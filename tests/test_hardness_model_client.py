import io
import http.client
import json
import urllib.error
from unittest.mock import patch

from agent.hardness.model_client import (
    DEFAULT_BASE_URL,
    DEFAULT_MODEL,
    DeepSeekClient,
    DeepSeekConfig,
    ModelResponse,
    completions_url,
    validate_base_url,
)
import pytest


def test_official_deepseek_base_url_is_default() -> None:
    config = DeepSeekConfig.from_environment(environ={})
    assert config.base_url == DEFAULT_BASE_URL == "https://api.deepseek.com"
    assert config.model == DEFAULT_MODEL == "deepseek-v4-flash"
    assert completions_url(config.base_url) == "https://api.deepseek.com/chat/completions"


def test_missing_key_does_not_make_network_request() -> None:
    response = DeepSeekClient(DeepSeekConfig(api_key=None)).complete_json(
        system="system", prompt="prompt"
    )
    assert response.called is False
    assert response.error == "missing DEEPSEEK_API_KEY"


def test_config_repr_does_not_expose_api_key() -> None:
    config = DeepSeekConfig(api_key="deepseek-secret")
    assert "deepseek-secret" not in repr(config)
    assert "deepseek-secret" not in str(config.to_public_dict())


def test_public_base_url_strips_credentials_query_and_fragment() -> None:
    config = DeepSeekConfig(
        api_key="secret",
        base_url="https://user:password@api.deepseek.com/v1?token=secret#fragment",
    )
    assert config.public_base_url == "https://api.deepseek.com/v1"


@pytest.mark.parametrize(
    "base_url",
    [
        "file:///tmp/fake-deepseek",
        "https://user:secret@api.deepseek.com",
        "https://api.deepseek.com?token=secret",
        "https://api.deepseek.com#secret",
    ],
)
def test_network_endpoint_rejects_non_http_or_embedded_secrets(base_url: str) -> None:
    with pytest.raises(ValueError):
        validate_base_url(base_url)


def test_http_error_redacts_api_key() -> None:
    error = urllib.error.HTTPError(
        url="https://api.deepseek.com/chat/completions",
        code=401,
        msg="Unauthorized",
        hdrs=None,
        fp=io.BytesIO(b'{"error":"deepseek-secret"}'),
    )
    client = DeepSeekClient(
        DeepSeekConfig(api_key="deepseek-secret", max_retries=0)
    )
    with patch("urllib.request.urlopen", side_effect=error):
        response = client.complete_json(system="system", prompt="prompt")
    assert response.ok is False
    assert response.error is not None
    assert "deepseek-secret" not in response.error
    assert "[REDACTED]" in response.error


def test_http_200_length_exhaustion_is_a_called_empty_response() -> None:
    class Response:
        status = 200

        def __enter__(self):
            return self

        def __exit__(self, *args: object) -> None:
            return None

        def read(self, limit: int) -> bytes:
            del limit
            return json.dumps(
                {
                    "choices": [
                        {
                            "message": {"content": ""},
                            "finish_reason": "length",
                        }
                    ],
                    "usage": {"completion_tokens": 4096},
                }
            ).encode()

    client = DeepSeekClient(DeepSeekConfig(api_key="test-key", max_retries=0))
    with patch("urllib.request.urlopen", return_value=Response()):
        response = client.complete_json(system="system", prompt="prompt")
    assert response.called is True
    assert response.ok is False
    assert response.status_code == 200
    assert response.finish_reason == "length"
    assert response.error == "empty assistant content (finish_reason=length)"


def test_http_200_empty_content_is_retried_before_failing_the_model_turn() -> None:
    class Response:
        status = 200

        def __init__(self, content: str):
            self.content = content

        def __enter__(self):
            return self

        def __exit__(self, *args: object) -> None:
            return None

        def read(self, limit: int) -> bytes:
            del limit
            return json.dumps(
                {
                    "choices": [
                        {
                            "message": {"content": self.content},
                            "finish_reason": "stop",
                        }
                    ],
                    "usage": {"total_tokens": 7},
                }
            ).encode()

    client = DeepSeekClient(DeepSeekConfig(api_key="test-key", max_retries=1))
    with patch(
        "urllib.request.urlopen",
        side_effect=[Response(""), Response('{"action":"search_problems"}')],
    ), patch("time.sleep"):
        response = client.complete_json(system="Return JSON.", prompt="prompt")
    assert response.ok is True
    assert response.attempts == 2
    assert response.content == '{"action":"search_problems"}'


def test_incomplete_http_body_becomes_an_auditable_failed_call() -> None:
    class Response:
        status = 200

        def __enter__(self):
            return self

        def __exit__(self, *args: object) -> None:
            return None

        def read(self, limit: int) -> bytes:
            del limit
            raise http.client.IncompleteRead(b"")

    client = DeepSeekClient(DeepSeekConfig(api_key="test-key", max_retries=0))
    with patch("urllib.request.urlopen", return_value=Response()):
        response = client.complete_json(system="system", prompt="prompt")
    assert response.called is True
    assert response.ok is False
    assert response.status_code is None
    assert response.attempts == 1
    assert response.error == "request failed: IncompleteRead(0 bytes read)"


def test_smoke_requires_nonce_echo_and_usage_without_starting_lean() -> None:
    client = DeepSeekClient(DeepSeekConfig(api_key="test-key"))

    def complete(*, system: str, prompt: str) -> ModelResponse:
        nonce = prompt.split('"nonce":"', 1)[1].split('"', 1)[0]
        return ModelResponse(
            called=True,
            ok=True,
            content=f'{{"ok":true,"nonce":"{nonce}"}}',
            error=None,
            status_code=200,
            duration_seconds=0.1,
            usage={"total_tokens": 7},
            attempts=1,
        )

    with patch.object(client, "complete_json", side_effect=complete):
        result = client.smoke()
    assert result.ok is True
    assert result.called is True
    assert result.usage == {"total_tokens": 7}
    assert result.to_dict()["lean_started"] is False
    assert "test-key" not in str(result.to_dict())
