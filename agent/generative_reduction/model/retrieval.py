from __future__ import annotations

from pathlib import Path
from typing import Iterable


def public_source_excerpts(
    *, root: Path, paths: Iterable[Path], character_budget: int = 32_000
) -> dict[str, str]:
    excerpts: dict[str, str] = {}
    remaining = character_budget
    reference = (root.resolve() / "Lean" / "Reference").resolve()
    for path in paths:
        resolved = path.resolve()
        try:
            relative = resolved.relative_to(reference)
        except ValueError:
            continue
        if any(part in {"Oracles", "Oracle", "Gold", "HiddenTargets"} for part in relative.parts):
            continue
        text = resolved.read_text(encoding="utf-8")
        excerpt = text[:remaining]
        excerpts[str(relative)] = excerpt
        remaining -= len(excerpt)
        if remaining <= 0:
            break
    return excerpts


__all__ = ["public_source_excerpts"]
