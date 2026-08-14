from __future__ import annotations

import json
from pathlib import Path
from typing import Mapping, Any

from .models import GeneralNPHardResult


def write_json(path: Path, value: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )


def write_result(path: Path, result: GeneralNPHardResult) -> None:
    write_json(path, result.to_dict())


__all__ = ["write_json", "write_result"]
