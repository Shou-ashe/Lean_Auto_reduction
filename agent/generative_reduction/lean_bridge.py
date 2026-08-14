"""Read-only Lean probes and environment snapshots."""

from __future__ import annotations

from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Iterable

from agent.hardness.lean_runner import run_command, sha256_file

from .models import stable_sha256


@dataclass(frozen=True)
class EnvironmentSnapshot:
    lean_toolchain: str
    lake_manifest_sha256: str
    imported_modules: tuple[str, ...]
    import_closure_fingerprint: str
    axiom_policy: str
    snapshot_hash: str

    def to_dict(self) -> dict[str, object]:
        return asdict(self)


def snapshot_environment(
    *, root: Path, imported_modules: Iterable[str], axiom_policy: str
) -> EnvironmentSnapshot:
    root = root.resolve()
    modules = tuple(dict.fromkeys(imported_modules))
    toolchain = (root / "Lean" / "lean-toolchain").read_text(encoding="utf-8").strip()
    manifest_hash = sha256_file(root / "Lean" / "lake-manifest.json")
    closure = stable_sha256({"modules": modules, "toolchain": toolchain})
    snapshot_hash = stable_sha256(
        {
            "toolchain": toolchain,
            "manifest": manifest_hash,
            "closure": closure,
            "axiom_policy": axiom_policy,
        }
    )
    return EnvironmentSnapshot(
        lean_toolchain=toolchain,
        lake_manifest_sha256=manifest_hash,
        imported_modules=modules,
        import_closure_fingerprint=closure,
        axiom_policy=axiom_policy,
        snapshot_hash=snapshot_hash,
    )


def run_lean_file(
    *, root: Path, path: Path, timeout_seconds: int, output_limit: int = 16 * 1024 * 1024
):
    return run_command(
        ["lake", "env", "lean", str(path.resolve())],
        cwd=root.resolve() / "Lean",
        timeout_seconds=timeout_seconds,
        output_limit=output_limit,
    )


__all__ = ["EnvironmentSnapshot", "run_lean_file", "snapshot_environment"]
