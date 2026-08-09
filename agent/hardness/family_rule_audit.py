"""Static audit for benchmark-family literals in production routing code.

This audit is observational.  It does not grant proof authority; it makes the
Stage-F "Python family-specific rule count" reproducible instead of reporting
an asserted zero.
"""

from __future__ import annotations

import ast
import hashlib
import json
from collections import defaultdict
from collections.abc import Iterable, Mapping, Sequence
from pathlib import Path
from typing import Any


def _sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def _case_value(case: Any, name: str) -> Any:
    if isinstance(case, Mapping):
        return case.get(name)
    return getattr(case, name, None)


def build_family_markers(cases: Iterable[Any]) -> dict[str, tuple[str, ...]]:
    """Derive audit markers solely from explicit Stage-F suite metadata."""

    markers: dict[str, set[str]] = defaultdict(set)
    for case in cases:
        coverage = _case_value(case, "coverage")
        if not isinstance(coverage, Mapping):
            raise ValueError("family-rule audit requires case coverage metadata")
        family = coverage.get("study_family")
        if not isinstance(family, str) or not family:
            raise ValueError("family-rule audit requires an explicit study_family")
        values = (
            family,
            coverage.get("logical_source"),
            _case_value(case, "id"),
            _case_value(case, "module"),
            _case_value(case, "source"),
            _case_value(case, "target"),
            _case_value(case, "comparison_group_id"),
            _case_value(case, "matched_pair_id"),
        )
        for value in values:
            if isinstance(value, str) and len(value.strip()) >= 4:
                markers[family].add(value.strip())
    return {
        family: tuple(sorted(values, key=lambda value: (value.casefold(), value)))
        for family, values in sorted(markers.items())
    }


def audit_python_family_specific_rules(
    cases: Iterable[Any],
    *,
    routing_source_paths: Sequence[Path],
    benchmark_validation_paths: Sequence[Path] = (),
    display_root: Path | None = None,
) -> dict[str, Any]:
    """Count suite-derived family literals in executable Python string nodes.

    Production routing paths and benchmark-only validation paths are reported
    separately.  Only the former contributes to the Agent rule count.
    """

    materialized_cases = tuple(cases)
    markers = build_family_markers(materialized_cases)

    def display(path: Path) -> str:
        resolved = path.resolve()
        if display_root is not None:
            try:
                return str(resolved.relative_to(display_root.resolve()))
            except ValueError:
                pass
        return str(resolved)

    def scan(
        paths: Sequence[Path],
    ) -> tuple[list[dict[str, Any]], dict[str, list[dict[str, Any]]]]:
        files: list[dict[str, Any]] = []
        evidence: dict[str, list[dict[str, Any]]] = {
            family: [] for family in markers
        }
        for path in paths:
            source = path.read_bytes()
            text = source.decode("utf-8")
            tree = ast.parse(text, filename=str(path))
            files.append(
                {
                    "path": display(path),
                    "sha256": _sha256_bytes(source),
                }
            )
            for node in ast.walk(tree):
                if not isinstance(node, ast.Constant) or not isinstance(node.value, str):
                    continue
                literal = node.value
                folded = literal.casefold()
                for family, family_markers in markers.items():
                    matched = tuple(
                        marker
                        for marker in family_markers
                        if marker.casefold() in folded
                    )
                    if not matched:
                        continue
                    evidence[family].append(
                        {
                            "path": display(path),
                            "line": int(getattr(node, "lineno", 0)),
                            "literal_sha256": hashlib.sha256(
                                literal.encode("utf-8")
                            ).hexdigest(),
                            "matched_markers": list(matched),
                        }
                    )
        for family in evidence:
            evidence[family].sort(
                key=lambda row: (row["path"], row["line"], row["literal_sha256"])
            )
        return files, evidence

    routing_files, routing_evidence = scan(routing_source_paths)
    validation_files, validation_evidence = scan(benchmark_validation_paths)
    families: list[dict[str, Any]] = []
    for family, family_markers in markers.items():
        families.append(
            {
                "study_family": family,
                "marker_count": len(family_markers),
                "markers_sha256": hashlib.sha256(
                    json.dumps(
                        family_markers, ensure_ascii=False, separators=(",", ":")
                    ).encode("utf-8")
                ).hexdigest(),
                "python_family_specific_rule_count": len(
                    routing_evidence[family]
                ),
                "routing_evidence": routing_evidence[family],
                "benchmark_contract_marker_count": len(
                    validation_evidence[family]
                ),
                "benchmark_contract_evidence": validation_evidence[family],
            }
        )

    return {
        "schema_version": "hardness_python_family_rule_audit_v1",
        "method": (
            "AST string-literal containment against suite-derived study-family, "
            "logical-source, case, module, declaration, and comparison-group markers"
        ),
        "routing_scope": (
            "Only production prompt, catalog, retrieval, planning, model-client, and "
            "real-runner files contribute to python_family_specific_rule_count."
        ),
        "benchmark_validation_scope": (
            "Suite ABI constants are disclosed separately because they validate the "
            "experiment inventory and do not select a mathematical route."
        ),
        "audited_routing_files": routing_files,
        "audited_benchmark_validation_files": validation_files,
        "families": families,
        "python_family_specific_rule_count": sum(
            row["python_family_specific_rule_count"] for row in families
        ),
        "benchmark_contract_marker_count": sum(
            row["benchmark_contract_marker_count"] for row in families
        ),
    }
