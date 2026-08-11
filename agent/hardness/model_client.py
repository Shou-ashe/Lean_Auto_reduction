"""Minimal DeepSeek Chat Completions client with no proof authority."""

from __future__ import annotations

import json
import hashlib
import http.client
import os
import re
import secrets
import socket
import time
import urllib.error
import urllib.request
import urllib.parse
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Mapping


DEFAULT_BASE_URL = "https://api.deepseek.com"
DEFAULT_MODEL = "deepseek-v4-flash"
DEFAULT_MAX_TOKENS = 4096
MAX_RESPONSE_BYTES = 2_000_000
JSON_FENCE_RE = re.compile(r"```(?:json)?\s*(.*?)```", re.DOTALL | re.IGNORECASE)


def read_dotenv(path: Path) -> dict[str, str]:
    if not path.is_file():
        return {}
    values: dict[str, str] = {}
    for raw_line in path.read_text(encoding="utf-8").splitlines():
        line = raw_line.strip()
        if not line or line.startswith("#") or "=" not in line:
            continue
        key, _, value = line.partition("=")
        key = key.strip()
        value = value.strip()
        if len(value) >= 2 and value[0] == value[-1] and value[0] in {"'", '"'}:
            value = value[1:-1]
        if key:
            values[key] = value
    return values


def completions_url(base_url: str) -> str:
    base = (base_url or DEFAULT_BASE_URL).strip().rstrip("/")
    if base.endswith("/chat/completions"):
        return base
    return f"{base}/chat/completions"


def validate_base_url(base_url: str) -> str:
    """Validate the network endpoint without exposing credentials in errors."""

    parsed = urllib.parse.urlsplit(base_url)
    if parsed.scheme not in {"http", "https"} or not parsed.hostname:
        raise ValueError("DeepSeek base URL must be an absolute HTTP(S) URL")
    if parsed.username is not None or parsed.password is not None:
        raise ValueError("DeepSeek base URL may not contain credentials")
    if parsed.query or parsed.fragment:
        raise ValueError("DeepSeek base URL may not contain a query or fragment")
    return completions_url(base_url)


@dataclass(frozen=True)
class DeepSeekConfig:
    api_key: str | None = field(repr=False)
    base_url: str = DEFAULT_BASE_URL
    model: str = DEFAULT_MODEL
    timeout_seconds: int = 120
    temperature: float = 0.0
    max_tokens: int = DEFAULT_MAX_TOKENS
    max_retries: int = 2
    reasoning_effort: str | None = None

    @classmethod
    def from_environment(
        cls, *, env_file: Path | None = None, environ: Mapping[str, str] | None = None
    ) -> "DeepSeekConfig":
        environment = dict(os.environ if environ is None else environ)
        dotenv = read_dotenv(env_file) if env_file else {}
        def integer(name: str, default: int, *, allow_zero: bool = False) -> int:
            raw = environment.get(name) or dotenv.get(name)
            if raw is None:
                return default
            try:
                value = int(raw)
            except ValueError:
                return default
            minimum = 0 if allow_zero else 1
            return value if value >= minimum else default

        return cls(
            api_key=environment.get("DEEPSEEK_API_KEY") or dotenv.get("DEEPSEEK_API_KEY"),
            base_url=environment.get("DEEPSEEK_BASE_URL")
            or dotenv.get("DEEPSEEK_BASE_URL")
            or DEFAULT_BASE_URL,
            model=environment.get("DEEPSEEK_MODEL")
            or dotenv.get("DEEPSEEK_MODEL")
            or DEFAULT_MODEL,
            timeout_seconds=integer("DEEPSEEK_TIMEOUT_SECONDS", 120),
            max_tokens=integer("DEEPSEEK_MAX_TOKENS", DEFAULT_MAX_TOKENS),
            max_retries=integer("DEEPSEEK_MAX_RETRIES", 2, allow_zero=True),
            reasoning_effort=(
                environment.get("DEEPSEEK_REASONING_EFFORT")
                or dotenv.get("DEEPSEEK_REASONING_EFFORT")
                or None
            ),
        )

    @property
    def public_base_url(self) -> str:
        parsed = urllib.parse.urlsplit(self.base_url)
        hostname = parsed.hostname or ""
        port = f":{parsed.port}" if parsed.port is not None else ""
        path = parsed.path.rstrip("/")
        return urllib.parse.urlunsplit((parsed.scheme, hostname + port, path, "", ""))

    def to_public_dict(self) -> dict[str, Any]:
        return {
            "base_url": self.public_base_url,
            "model": self.model,
            "timeout_seconds": self.timeout_seconds,
            "temperature": self.temperature,
            "max_tokens": self.max_tokens,
            "max_retries": self.max_retries,
            "reasoning_effort": self.reasoning_effort,
            "api_key_configured": bool(self.api_key),
        }

    def redact(self, value: str) -> str:
        redacted = value
        sensitive_values = [self.api_key, self.base_url]
        parsed = urllib.parse.urlsplit(self.base_url)
        sensitive_values.extend((parsed.username, parsed.password, parsed.query, parsed.fragment))
        for sensitive in sensitive_values:
            if not sensitive:
                continue
            redacted = redacted.replace(sensitive, "[REDACTED]")
            encoded = urllib.parse.quote(sensitive, safe="")
            if encoded != sensitive:
                redacted = redacted.replace(encoded, "[REDACTED]")
        return redacted


@dataclass(frozen=True)
class ModelResponse:
    called: bool
    ok: bool
    content: str
    error: str | None
    status_code: int | None
    duration_seconds: float
    usage: dict[str, Any] | None
    attempts: int
    finish_reason: str | None = None


@dataclass(frozen=True)
class DeepSeekSmokeResult:
    ok: bool
    called: bool
    base_url: str
    model: str
    status_code: int | None
    duration_seconds: float
    usage: dict[str, Any] | None
    attempts: int
    response_sha256: str
    error: str | None = None
    schema_version: str = "hardness_deepseek_smoke_v1"

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema_version": self.schema_version,
            "ok": self.ok,
            "called": self.called,
            "base_url": self.base_url,
            "model": self.model,
            "status_code": self.status_code,
            "duration_seconds": self.duration_seconds,
            "usage": self.usage,
            "attempts": self.attempts,
            "response_sha256": self.response_sha256,
            "error": self.error,
            "lean_started": False,
        }


def extract_json_object(content: str) -> dict[str, Any] | None:
    candidates = [content.strip(), *(match.strip() for match in JSON_FENCE_RE.findall(content))]
    decoder = json.JSONDecoder()
    for candidate in candidates:
        if not candidate:
            continue
        try:
            value = json.loads(candidate)
            if isinstance(value, dict):
                return value
        except json.JSONDecodeError:
            pass
        for index, character in enumerate(candidate):
            if character != "{":
                continue
            try:
                value, _ = decoder.raw_decode(candidate[index:])
            except json.JSONDecodeError:
                continue
            if isinstance(value, dict):
                return value
    return None


class DeepSeekClient:
    def __init__(self, config: DeepSeekConfig):
        self.config = config

    def complete_json(self, *, system: str, prompt: str) -> ModelResponse:
        started = time.monotonic()
        if not self.config.api_key:
            return ModelResponse(
                called=False,
                ok=False,
                content="",
                error="missing DEEPSEEK_API_KEY",
                status_code=None,
                duration_seconds=0.0,
                usage=None,
                attempts=0,
            )
        try:
            endpoint = validate_base_url(self.config.base_url)
        except ValueError as error:
            return ModelResponse(
                called=False,
                ok=False,
                content="",
                error=str(error),
                status_code=None,
                duration_seconds=0.0,
                usage=None,
                attempts=0,
            )
        payload: dict[str, Any] = {
            "model": self.config.model,
            "messages": [
                {"role": "system", "content": system},
                {"role": "user", "content": prompt},
            ],
            "temperature": self.config.temperature,
            "stream": False,
            "response_format": {"type": "json_object"},
            "max_tokens": self.config.max_tokens,
        }
        if self.config.reasoning_effort:
            payload["reasoning_effort"] = self.config.reasoning_effort
        attempts = 0
        last_error: str | None = None
        last_status: int | None = None
        last_usage: dict[str, Any] | None = None
        last_finish_reason: str | None = None
        for attempt in range(self.config.max_retries + 1):
            attempts = attempt + 1
            request = urllib.request.Request(
                endpoint,
                data=json.dumps(payload, ensure_ascii=False).encode("utf-8"),
                headers={
                    "Authorization": f"Bearer {self.config.api_key}",
                    "Content-Type": "application/json",
                },
                method="POST",
            )
            try:
                with urllib.request.urlopen(
                    request, timeout=self.config.timeout_seconds
                ) as response:
                    raw_bytes = response.read(MAX_RESPONSE_BYTES + 1)
                    if len(raw_bytes) > MAX_RESPONSE_BYTES:
                        raise OSError("DeepSeek response exceeded the audit size limit")
                    raw = raw_bytes.decode("utf-8", errors="replace")
                    status_code = response.status
                parsed = json.loads(raw)
                choice = (parsed.get("choices") or [{}])[0]
                content = str(
                    ((choice.get("message") or {}).get("content")) or ""
                )
                finish_reason = str(choice.get("finish_reason") or "") or None
                usage = parsed.get("usage") if isinstance(parsed, dict) else None
                if content:
                    return ModelResponse(
                        called=True,
                        ok=True,
                        content=content,
                        error=None,
                        status_code=status_code,
                        duration_seconds=round(time.monotonic() - started, 3),
                        usage=usage,
                        attempts=attempts,
                        finish_reason=finish_reason,
                    )
                last_status = status_code
                last_usage = usage if isinstance(usage, dict) else None
                last_finish_reason = finish_reason
                last_error = "empty assistant content" + (
                    f" (finish_reason={finish_reason})" if finish_reason else ""
                )
            except urllib.error.HTTPError as error:
                last_status = error.code
                body = error.read().decode("utf-8", errors="replace")
                last_error = self.config.redact(f"HTTP {error.code}: {body[:1000]}")
                if error.code != 429 and not 500 <= error.code < 600:
                    break
            except (TimeoutError, socket.timeout) as error:
                last_error = f"timeout: {error}"
            except (
                urllib.error.URLError,
                json.JSONDecodeError,
                OSError,
                http.client.HTTPException,
            ) as error:
                last_error = self.config.redact(f"request failed: {error}")
            if last_error:
                last_error = self.config.redact(last_error)
            if attempt < self.config.max_retries:
                time.sleep(min(float(2**attempt), 8.0))
        return ModelResponse(
            called=True,
            ok=False,
            content="",
            error=last_error or "DeepSeek request failed",
            status_code=last_status,
            duration_seconds=round(time.monotonic() - started, 3),
            usage=last_usage,
            attempts=attempts,
            finish_reason=last_finish_reason,
        )

    def smoke(self) -> DeepSeekSmokeResult:
        """Make one tiny API call without starting Lean or exposing response text."""

        nonce = secrets.token_hex(12)
        response = self.complete_json(
            system="Return only the requested JSON object.",
            prompt=(
                "DeepSeek connectivity smoke. Return exactly "
                f'{{"ok":true,"nonce":"{nonce}"}}.'
            ),
        )
        payload = extract_json_object(response.content) if response.ok else None
        protocol_ok = bool(
            payload
            and payload.get("ok") is True
            and payload.get("nonce") == nonce
            and isinstance(response.usage, dict)
        )
        error = response.error
        if response.ok and not protocol_ok:
            error = "smoke response did not echo the nonce with usage"
        return DeepSeekSmokeResult(
            ok=protocol_ok,
            called=response.called,
            base_url=self.config.public_base_url,
            model=self.config.model,
            status_code=response.status_code,
            duration_seconds=response.duration_seconds,
            usage=response.usage,
            attempts=response.attempts,
            response_sha256=hashlib.sha256(response.content.encode("utf-8")).hexdigest(),
            error=error,
        )
