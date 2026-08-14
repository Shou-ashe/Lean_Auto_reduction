"""Helpers for stable ProofGuidance identifiers and serialization."""

from __future__ import annotations

from .models import ProofGuidance, stable_sha256


def guidance_id(*, goal_fingerprint: str, declaration: str, residuals: tuple[str, ...]) -> str:
    digest = stable_sha256(
        {
            "goal": goal_fingerprint,
            "declaration": declaration,
            "residuals": residuals,
        }
    )
    return f"guidance-{digest.removeprefix('sha256:')[:20]}"


def guidance_to_dict(guidance: ProofGuidance) -> dict[str, object]:
    from .models import _jsonable

    return _jsonable(guidance)


__all__ = ["guidance_id", "guidance_to_dict"]
