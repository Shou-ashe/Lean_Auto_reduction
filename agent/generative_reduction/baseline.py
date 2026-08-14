"""Frozen hashes for the stable Boolean-CSP regression entry points."""

from __future__ import annotations

import hashlib
from pathlib import Path


STABLE_ENTRYPOINT_HASHES = {
    "scripts/prove_np_hard.py": (
        "976dd31924a95e5810841f15c68b7c52e0d9f9811f9ee73f3e88fb9635437de1"
    ),
    "agent/hardness/boolean_csp_np_hard_benchmark.py": (
        "0cc7ce55a68faa2b0680dc6229e0d929c6e6abe76fcfec41e7ef8028889ac460"
    ),
}


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def verify_stable_entrypoints(root: Path) -> dict[str, str]:
    actual = {
        relative: sha256_file(root.resolve() / relative)
        for relative in STABLE_ENTRYPOINT_HASHES
    }
    drifted = {
        relative: digest
        for relative, digest in actual.items()
        if digest != STABLE_ENTRYPOINT_HASHES[relative]
    }
    if drifted:
        raise RuntimeError(f"stable Boolean-CSP entrypoint drift: {sorted(drifted)}")
    return actual


__all__ = ["STABLE_ENTRYPOINT_HASHES", "sha256_file", "verify_stable_entrypoints"]
