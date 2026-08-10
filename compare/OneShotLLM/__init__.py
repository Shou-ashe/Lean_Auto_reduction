"""Direct one-request LLM control arm for the hardness benchmark."""

from .client import OneShotLLMClient, OneShotResult

__all__ = ["OneShotLLMClient", "OneShotResult"]
