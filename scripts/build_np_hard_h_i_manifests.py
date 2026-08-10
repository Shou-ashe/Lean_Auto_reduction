#!/usr/bin/env python3
"""Build the frozen, answer-free H-I target-hardness benchmark manifests.

The public suites contain only input identity and budget metadata.  Scoring
classes, expected outcomes, route lengths, difficulty levels, and target
matrix identities are written exclusively to the scorer-only oracle.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
HARDNESS = ROOT / "Benchmark" / "Hardness"
SUITES = HARDNESS / "Suites"
GATE_SUITES = ROOT / "Gate" / "Suites"
EVALUATION = HARDNESS / "Evaluation"

SUITE_SCHEMA = "hardness_np_hard_capability_suite_v1"
ORACLE_SCHEMA = "hardness_np_hard_capability_oracle_v1"
MANIFEST_SCHEMA = "hardness_np_hard_capability_manifest_v1"
EDGE_SUITE_SCHEMA = "hardness_exact_reduction_edge_input_suite_v1"
EDGE_ORACLE_SCHEMA = "hardness_exact_reduction_edge_oracle_v1"
EDGE_MANIFEST_SCHEMA = "hardness_exact_reduction_edge_manifest_v1"
ARCHIVE_SELECTION_SCHEMA = "hardness_np_hard_problem_archive_selection_v1"


def _case(
    case_id: str,
    module: str,
    problem: str,
    family: str,
    outcome_class: str,
    level: str,
    *,
    route_length: int | None = None,
    scored: bool = True,
    budget_profile: str = "formal-default",
    difficulty_axes: tuple[str, ...] = (),
) -> dict[str, Any]:
    tier = {
        "existing-route": "C0-existing",
        "first-authoring": "C0-authoring",
        "safety": "C0-safety",
        "frontier": "F0-frontier",
    }[outcome_class]
    return {
        "case_id": case_id,
        "module": module,
        "problem": problem,
        "family": family,
        "budget_profile": budget_profile,
        "_oracle": {
            "tier": tier,
            "outcome_class": outcome_class,
            "level": level,
            "level_bucket": level.split("-")[0],
            "scored": scored,
            "requires_model": outcome_class in {"first-authoring", "frontier"},
            "expected_public_status": (
                "BLOCKED_NOT_TARGET" if outcome_class == "safety" else "VERIFIED"
            ),
            "expected_failure_codes": (
                ["auxiliary_or_non_target"] if outcome_class == "safety" else []
            ),
            "route_length": route_length,
            "difficulty_axes": list(difficulty_axes),
        },
    }


SPLITS: dict[str, tuple[dict[str, Any], ...]] = {
    "dev": (
        _case("cdev-er-01-three-sat-seed", "ComplexityReduction.Problems.Karp21.Satisfiability", "ComplexityReduction.Problems.Karp21.Satisfiability.threeSATStructuredProblem", "sat-csp", "existing-route", "L1", route_length=0, difficulty_axes=("reflexive",)),
        _case("cdev-er-02-clique-direct", "ComplexityReduction.Problems.Karp21.GraphAtoms", "ComplexityReduction.Problems.Karp21.GraphAtoms.cliqueStructuredProblem", "graph", "existing-route", "L1", route_length=1, difficulty_axes=("direct-route",)),
        _case("cdev-er-03-vertex-cover-two-hop", "ComplexityReduction.Problems.Karp21.GraphAtoms", "ComplexityReduction.Problems.Karp21.GraphAtoms.vertexCoverStructuredProblem", "graph", "existing-route", "L2", route_length=2, difficulty_axes=("route-composition",)),
        _case("cdev-er-04-directed-hamiltonian-three-hop", "ComplexityReduction.Presentation.DirectedHamiltonianCircuit", "ComplexityReduction.Presentation.DirectedHamiltonianCircuit.structuredProblem", "graph", "existing-route", "L2", route_length=3, difficulty_axes=("route-composition",)),
        _case("cdev-au-01-tagged-three-sat-adapter", "ComplexityReduction.Routes.ThreeSATToClique.IngressAdapters", "ComplexityReduction.Routes.ThreeSATToClique.IngressAdapters.taggedThreeSATProblem", "sat-csp", "first-authoring", "L3", difficulty_axes=("representation-adapter", "semantic-iff")),
        _case("cdev-au-02-role-graph-eon-adapter", "ComplexityReduction.Presentation.RoleGraph", "ComplexityReduction.Presentation.RoleGraph.exactlyOneNeighborPresentedProblem", "graph", "first-authoring", "L3-L4", difficulty_axes=("representation-adapter", "predicate-identity", "semantic-iff")),
        _case("cdev-sf-01-graph-ir-wellformed-internal", "ComplexityReduction.Domain.Core.GraphIR", "ComplexityReduction.Domain.GraphIR.wellFormedProblem", "graph", "safety", "L0-L6", difficulty_axes=("internal-helper", "scope-policy")),
        _case("cdev-sf-02-modified-exact-cover-internal", "ComplexityReduction.Domain.ModifiedExactCoverInput", "ComplexityReduction.Domain.ModifiedExactCoverInput.modifiedProblem", "set-system", "safety", "L0-L6", difficulty_axes=("internal-helper", "scope-policy")),
    ),
    "validation": (
        _case("cval-er-01-zero-one-ip-direct", "ComplexityReduction.Presentation.ZeroOneIP", "ComplexityReduction.Presentation.ZeroOneIP.structuredProblem", "numeric", "existing-route", "L1", route_length=1, difficulty_axes=("direct-route", "numeric")),
        _case("cval-er-02-exact-cover-two-hop", "ComplexityReduction.Presentation.SetSystem", "ComplexityReduction.Presentation.SetSystem.exactCoverStructuredProblem", "set-system", "existing-route", "L2", route_length=2, difficulty_axes=("route-composition", "representation-adapter")),
        _case("cval-er-03-knapsack-binary-three-hop", "ComplexityReduction.Presentation.KnapsackBinary", "ComplexityReduction.Presentation.KnapsackBinary.structuredProblem", "numeric", "existing-route", "L2", route_length=3, difficulty_axes=("route-composition", "binary-encoding")),
        _case("cval-er-04-job-sequencing-binary-four-hop", "ComplexityReduction.Presentation.JobSequencingBinary", "ComplexityReduction.Presentation.JobSequencingBinary.binaryStructuredProblem", "numeric", "existing-route", "L2", route_length=4, difficulty_axes=("long-route", "binary-encoding")),
        _case("cval-au-01-knapsack-native-bridge", "ComplexityReduction.Presentation.Knapsack", "ComplexityReduction.Presentation.Knapsack.structuredProblem", "numeric", "first-authoring", "L4", difficulty_axes=("representation-adapter", "parameter-transform", "polynomial-bound")),
        _case("cval-au-02-partition-native-bridge", "ComplexityReduction.Presentation.Partition", "ComplexityReduction.Presentation.Partition.structuredProblem", "numeric", "first-authoring", "L4", difficulty_axes=("representation-adapter", "parameter-transform", "polynomial-bound")),
        _case("cval-sf-01-role-graph-ir-internal", "ComplexityReduction.Domain.Core.RoleGraphIR", "ComplexityReduction.Domain.RoleGraphIR.roleAssignedGraphProblem", "graph", "safety", "L0-L6", difficulty_axes=("internal-helper", "scope-policy")),
        _case("cval-sf-02-graph-wellformed-policy", "ComplexityReduction.Presentation.Graph", "ComplexityReduction.Presentation.Graph.wellFormedProblem", "graph", "safety", "L0-L6", difficulty_axes=("well-formedness", "scope-policy")),
    ),
    "heldout": (
        _case("chld-er-01-chromatic-number", "ComplexityReduction.Presentation.ChromaticNumber", "ComplexityReduction.Presentation.ChromaticNumber.structuredProblem", "other", "existing-route", "L1", route_length=1, difficulty_axes=("family-heldout", "direct-route")),
        _case("chld-er-02-node-deletion-bipartite", "ComplexityReduction.Presentation.NodeDeletionBipartite", "ComplexityReduction.Presentation.NodeDeletionBipartite.presentedProblem", "other", "existing-route", "L2", route_length=2, difficulty_axes=("family-heldout", "route-composition")),
        _case("chld-er-03-partition-binary-long", "ComplexityReduction.Presentation.PartitionBinary", "ComplexityReduction.Presentation.PartitionBinary.structuredProblem", "numeric", "existing-route", "L2", route_length=4, difficulty_axes=("long-route", "binary-encoding")),
        _case("chld-er-04-two-disjoint-paths-max-route", "ComplexityReduction.Presentation.TwoDisjointBoundedPaths", "ComplexityReduction.Presentation.TwoDisjointBoundedPaths.presentedProblem", "graph", "existing-route", "L2", route_length=5, difficulty_axes=("maximum-route", "route-composition")),
        _case("chld-au-01-feedback-node-set", "ComplexityReduction.Presentation.FeedbackNodeSet", "ComplexityReduction.Presentation.FeedbackNodeSet.structuredProblem", "graph", "first-authoring", "L5", difficulty_axes=("new-gadget", "mapping-invariant", "semantic-iff", "polynomial-bound")),
        _case("chld-au-02-job-sequencing-native", "ComplexityReduction.Presentation.JobSequencing", "ComplexityReduction.Presentation.JobSequencing.structuredProblem", "numeric", "first-authoring", "L4", difficulty_axes=("parameter-transform", "executable-coherence", "polynomial-bound")),
        _case("chld-au-03-max-cut-structured", "ComplexityReduction.Presentation.MaxCut", "ComplexityReduction.Presentation.MaxCut.structuredProblem", "graph", "first-authoring", "L5", difficulty_axes=("new-gadget", "threshold-transform", "semantic-iff", "polynomial-bound")),
        _case("chld-au-04-max-cut-binary", "ComplexityReduction.Presentation.MaxCutBinary", "ComplexityReduction.Presentation.MaxCutBinary.binaryStructuredProblem", "graph", "first-authoring", "L4-L5", difficulty_axes=("binary-encoding", "executable-coherence", "polynomial-bound")),
        _case("chld-au-05-seeing-set", "ComplexityReduction.Presentation.SeeingSet", "ComplexityReduction.Presentation.SeeingSet.presentedProblem", "set-system", "first-authoring", "L4", difficulty_axes=("program-composition", "mapping-invariant")),
        _case("chld-au-06-hitting-set", "ComplexityReduction.Presentation.SetSystem", "ComplexityReduction.Presentation.SetSystem.hittingSetStructuredProblem", "set-system", "first-authoring", "L4", difficulty_axes=("hub-selection", "set-duality", "semantic-iff")),
        _case("chld-au-07-set-covering", "ComplexityReduction.Presentation.SetSystem", "ComplexityReduction.Presentation.SetSystem.setCoveringStructuredProblem", "set-system", "first-authoring", "L4", difficulty_axes=("directionality", "new-ingress", "semantic-iff")),
        _case("chld-au-08-set-packing", "ComplexityReduction.Presentation.SetSystem", "ComplexityReduction.Presentation.SetSystem.setPackingStructuredProblem", "set-system", "first-authoring", "L5", difficulty_axes=("new-gadget", "parameter-transform", "semantic-iff", "polynomial-bound")),
        _case("chld-sf-01-role-graph-wellformed", "ComplexityReduction.Presentation.RoleGraph", "ComplexityReduction.Presentation.RoleGraph.wellFormedPresentedProblem", "graph", "safety", "L0-L6", difficulty_axes=("shared-representation", "predicate-identity", "scope-policy")),
        _case("chld-sf-02-set-system-wellformed", "ComplexityReduction.Presentation.SetSystem", "ComplexityReduction.Presentation.SetSystem.wellFormedProblem", "set-system", "safety", "L0-L6", difficulty_axes=("shared-representation", "predicate-identity", "scope-policy")),
        _case("chld-sf-03-graph-atoms-wellformed", "ComplexityReduction.Problems.Karp21.GraphAtoms", "ComplexityReduction.Problems.Karp21.GraphAtoms.graphWellFormedProblem", "graph", "safety", "L0-L6", difficulty_axes=("shared-module", "predicate-identity", "scope-policy")),
        _case("chld-sf-04-two-cnf-tractable", "ComplexityReduction.Problems.Karp21.SATTractable", "ComplexityReduction.Problems.Karp21.SATTractable.twoCNFStructuredProblem", "sat-csp", "safety", "L0-L6", difficulty_axes=("tractable-class", "scope-policy")),
    ),
    "frontier": (
        _case("frontier-01-feedback-arc-set", "ComplexityReduction.Presentation.FeedbackArcSet", "ComplexityReduction.Presentation.FeedbackArcSet.structuredProblem", "graph", "frontier", "L5-L6", scored=False, budget_profile="frontier-default", difficulty_axes=("new-gadget", "mapping-invariant", "polynomial-bound", "formal-prerequisite")),
        _case("frontier-02-three-dimensional-matching", "ComplexityReduction.Presentation.ThreeDimensionalMatching", "ComplexityReduction.Presentation.ThreeDimensionalMatching.structuredProblem", "other", "frontier", "L5-L6", scored=False, budget_profile="frontier-default", difficulty_axes=("family-heldout", "new-gadget", "semantic-iff", "formal-prerequisite")),
    ),
}


EDGE_AUDITS = (
    "kernel",
    "replay",
    "axiom",
    "endpoint",
    "dependency",
    "program_direct_tm_coherence",
    "semantic_iff",
    "polynomial_bound",
)


def _edge(
    case_id: str,
    archive_id: str,
    module: str,
    source: str,
    target: str,
    statement: str,
    *,
    status: str,
    allow_composition: bool,
    require_new_primitive: bool,
    existing_route: str | None = None,
    forbidden_route_imports: tuple[str, ...] = (),
) -> dict[str, Any]:
    return {
        "case_id": case_id,
        "module": module,
        "source": source,
        "target": target,
        "statement": statement,
        "budget_profile": "formal-default",
        "_oracle": {
            "archive_id": archive_id,
            "canonical_direction": {"source": source, "target": target},
            "status": status,
            "allow_composition": allow_composition,
            "require_new_primitive": require_new_primitive,
            "forbidden_route_imports": list(forbidden_route_imports),
            "required_audits": list(EDGE_AUDITS),
            "existing_route": existing_route,
        },
    }


EDGE_DEV_MODULE = "Benchmark.Hardness.Inputs.ExactReductionEdgeV1.DevEndpoints"
EDGE_VALIDATION_MODULE = "Benchmark.Hardness.Inputs.ExactReductionEdgeV1.ValidationEndpoints"
EDGE_HELDOUT_MODULE = "Benchmark.Hardness.Inputs.ExactReductionEdgeV1.HeldoutEndpoints"

THREE_SAT = "ComplexityReduction.Problems.Karp21.Satisfiability.threeSATStructuredProblem"
CLIQUE = "ComplexityReduction.Problems.Karp21.GraphAtoms.cliqueStructuredProblem"
VERTEX_COVER = "ComplexityReduction.Problems.Karp21.GraphAtoms.vertexCoverStructuredProblem"
ZERO_ONE_IP = "ComplexityReduction.Presentation.ZeroOneIP.structuredProblem"
CHROMATIC = "ComplexityReduction.Presentation.ChromaticNumber.structuredProblem"
CLIQUE_COVER = "ComplexityReduction.Presentation.CliqueCover.structuredProblem"
SET_COVER = "ComplexityReduction.Presentation.SetSystem.setCoveringStructuredProblem"
HITTING_SET = "ComplexityReduction.Presentation.SetSystem.hittingSetStructuredProblem"
SET_PACKING = "ComplexityReduction.Presentation.SetSystem.setPackingStructuredProblem"
EXACT_COVER = "ComplexityReduction.Presentation.SetSystem.exactCoverStructuredProblem"
UHC = "ComplexityReduction.Presentation.UndirectedHamiltonianCircuit.structuredProblem"
DHC = "ComplexityReduction.Presentation.DirectedHamiltonianCircuit.structuredProblem"
PARTITION = "ComplexityReduction.Presentation.Partition.structuredProblem"
KNAPSACK = "ComplexityReduction.Presentation.Knapsack.structuredProblem"


EDGE_SPLITS: dict[str, tuple[dict[str, Any], ...]] = {
    "dev": (
        _edge("edge-dev-01-three-sat-to-clique", "05-007", EDGE_DEV_MODULE, THREE_SAT, CLIQUE, "Construct a certified reduction from structured 3SAT to structured Clique.", status="ready", allow_composition=True, require_new_primitive=False, existing_route="ComplexityReduction.Routes.ThreeSATToClique.finalRoute"),
        _edge("edge-dev-02-three-sat-to-zero-one-ip", "06-008", EDGE_DEV_MODULE, THREE_SAT, ZERO_ONE_IP, "Construct a certified reduction from structured 3SAT to structured zero-one integer programming.", status="ready", allow_composition=True, require_new_primitive=False, existing_route="ComplexityReduction.Routes.ThreeSATToZeroOneIP.finalRoute"),
        _edge("edge-dev-03-three-sat-to-chromatic", "05-009", EDGE_DEV_MODULE, THREE_SAT, CHROMATIC, "Construct a certified reduction from structured 3SAT to structured Chromatic Number.", status="ready", allow_composition=True, require_new_primitive=False, existing_route="ComplexityReduction.Routes.ThreeSATToChromaticNumber.finalRoute"),
        _edge("edge-dev-04-chromatic-to-clique-cover", "06-028", EDGE_DEV_MODULE, CHROMATIC, CLIQUE_COVER, "Construct a certified reduction from structured Chromatic Number to structured Clique Cover.", status="ready", allow_composition=True, require_new_primitive=False, existing_route="ComplexityReduction.Routes.ChromaticNumberToCliqueCover.finalRoute"),
        _edge("edge-dev-05-set-cover-to-hitting-set", "03-004d", EDGE_DEV_MODULE, SET_COVER, HITTING_SET, "Construct a certified reduction from structured Set Covering to structured Hitting Set.", status="ready", allow_composition=True, require_new_primitive=False, existing_route="ComplexityReduction.Routes.SetCoveringToHittingSet.certifiedReduction"),
        _edge("edge-dev-06-undirected-to-directed-hc", "02-002", EDGE_DEV_MODULE, UHC, DHC, "Construct a certified reduction from structured Undirected Hamiltonian Circuit to structured Directed Hamiltonian Circuit.", status="ready", allow_composition=False, require_new_primitive=True, forbidden_route_imports=("ComplexityReduction.Routes.DirectedHamiltonianCircuitToUndirectedHamiltonianCircuit.Unified",)),
    ),
    "validation": (
        _edge("edge-val-01-vertex-cover-to-set-cover", "02-007", EDGE_VALIDATION_MODULE, VERTEX_COVER, SET_COVER, "Construct a certified reduction from structured Vertex Cover to structured Set Covering.", status="ready", allow_composition=False, require_new_primitive=True, forbidden_route_imports=("ComplexityReduction.Routes.VertexCoverToSetCovering",)),
        _edge("edge-val-02-clique-to-half-clique", "01-004", EDGE_VALIDATION_MODULE, CLIQUE, "ComplexityReduction.Presentation.HalfClique.structuredProblem", "Construct a certified reduction from structured Clique to structured Half Clique.", status="blocked_endpoint_formalization", allow_composition=False, require_new_primitive=True),
        _edge("edge-val-03-three-sat-to-double-sat", "01-001", EDGE_VALIDATION_MODULE, THREE_SAT, "ComplexityReduction.Presentation.DoubleThreeSAT.structuredProblem", "Construct a certified reduction from structured 3SAT to structured Double 3SAT.", status="blocked_endpoint_formalization", allow_composition=False, require_new_primitive=True),
        _edge("edge-val-04-three-sat-to-nae-three-sat", "02-004", EDGE_VALIDATION_MODULE, THREE_SAT, "ComplexityReduction.Presentation.NAEThreeSAT.structuredProblem", "Construct a certified reduction from structured 3SAT to structured Not-All-Equal 3SAT.", status="blocked_endpoint_formalization", allow_composition=False, require_new_primitive=True),
        _edge("edge-val-05-subset-sum-to-knapsack", "01-005", EDGE_VALIDATION_MODULE, "ComplexityReduction.Presentation.SubsetSum.structuredProblem", KNAPSACK, "Construct a certified reduction from structured Subset Sum to structured Knapsack.", status="blocked_endpoint_formalization", allow_composition=False, require_new_primitive=True),
        _edge("edge-val-06-clique-to-independent-set", "06-017", EDGE_VALIDATION_MODULE, CLIQUE, "ComplexityReduction.Presentation.IndependentSet.structuredProblem", "Construct a certified reduction from structured Clique to structured Independent Set.", status="blocked_endpoint_formalization", allow_composition=False, require_new_primitive=True),
    ),
    "heldout": (
        _edge("edge-held-01-vertex-cover-to-dominating-set", "05-008", EDGE_HELDOUT_MODULE, VERTEX_COVER, "ComplexityReduction.Presentation.DominatingSet.structuredProblem", "Construct a certified reduction from structured Vertex Cover to structured Dominating Set.", status="blocked_endpoint_formalization", allow_composition=False, require_new_primitive=True),
        _edge("edge-held-02-clique-to-dense-subgraph", "02-006", EDGE_HELDOUT_MODULE, CLIQUE, "ComplexityReduction.Presentation.DenseSubgraph.structuredProblem", "Construct a certified reduction from structured Clique to structured Dense Subgraph.", status="blocked_endpoint_formalization", allow_composition=False, require_new_primitive=True),
        _edge("edge-held-03-independent-set-to-vertex-cover", "06-018", EDGE_HELDOUT_MODULE, "ComplexityReduction.Presentation.IndependentSet.structuredProblem", VERTEX_COVER, "Construct a certified reduction from structured Independent Set to structured Vertex Cover.", status="blocked_endpoint_formalization", allow_composition=False, require_new_primitive=True),
        _edge("edge-held-04-independent-set-to-set-packing", "06-020", EDGE_HELDOUT_MODULE, "ComplexityReduction.Presentation.IndependentSet.structuredProblem", SET_PACKING, "Construct a certified reduction from structured Independent Set to structured Set Packing.", status="blocked_endpoint_formalization", allow_composition=False, require_new_primitive=True),
        _edge("edge-held-05-nae-three-sat-to-set-splitting", "02-005", EDGE_HELDOUT_MODULE, "ComplexityReduction.Presentation.NAEThreeSAT.structuredProblem", "ComplexityReduction.Presentation.SetSplitting.structuredProblem", "Construct a certified reduction from structured Not-All-Equal 3SAT to structured Set Splitting.", status="blocked_endpoint_formalization", allow_composition=False, require_new_primitive=True),
        _edge("edge-held-06-three-sat-to-one-in-three-sat", "06-007", EDGE_HELDOUT_MODULE, THREE_SAT, "ComplexityReduction.Presentation.OneInThreeSAT.structuredProblem", "Construct a certified reduction from structured 3SAT to structured One-In-Three 3SAT.", status="blocked_endpoint_formalization", allow_composition=False, require_new_primitive=True),
        _edge("edge-held-07-one-in-three-to-exact-cover", "06-013", EDGE_HELDOUT_MODULE, "ComplexityReduction.Presentation.OneInThreeSAT.structuredProblem", EXACT_COVER, "Construct a certified reduction from structured One-In-Three 3SAT to structured Exact Cover.", status="blocked_endpoint_formalization", allow_composition=False, require_new_primitive=True),
        _edge("edge-held-08-nae-three-sat-to-chromatic", "06-027", EDGE_HELDOUT_MODULE, "ComplexityReduction.Presentation.NAEThreeSAT.structuredProblem", CHROMATIC, "Construct a certified reduction from structured Not-All-Equal 3SAT to structured Chromatic Number.", status="blocked_endpoint_formalization", allow_composition=False, require_new_primitive=True),
        _edge("edge-held-09-exact-cover-three-to-four", "03-006", EDGE_HELDOUT_MODULE, "ComplexityReduction.Presentation.ExactCoverBy3.structuredProblem", "ComplexityReduction.Presentation.ExactCoverBy4.structuredProblem", "Construct a certified reduction from structured Exact Cover by 3-Sets to structured Exact Cover by 4-Sets.", status="blocked_endpoint_formalization", allow_composition=False, require_new_primitive=True),
        _edge("edge-held-10-subset-sum-to-partition", "03-015", EDGE_HELDOUT_MODULE, "ComplexityReduction.Presentation.SubsetSum.structuredProblem", PARTITION, "Construct a certified reduction from structured Subset Sum to structured Partition.", status="blocked_endpoint_formalization", allow_composition=False, require_new_primitive=True),
        _edge("edge-held-11-hamiltonian-cycle-to-tsp", "02-008", EDGE_HELDOUT_MODULE, UHC, "ComplexityReduction.Presentation.TSP.structuredProblem", "Construct a certified reduction from structured Undirected Hamiltonian Circuit to structured Traveling Salesperson.", status="blocked_endpoint_formalization", allow_composition=False, require_new_primitive=True),
        _edge("edge-held-12-hamiltonian-cycle-to-path", "03-013c", EDGE_HELDOUT_MODULE, UHC, "ComplexityReduction.Presentation.HamiltonianPath.structuredProblem", "Construct a certified reduction from structured Undirected Hamiltonian Circuit to structured Hamiltonian Path.", status="blocked_endpoint_formalization", allow_composition=False, require_new_primitive=True),
    ),
}


R1_PUBLIC_CASES = (
    {"case_id": "r1-pub-01-graph-coloring-ir", "module": "ComplexityReduction.Domain.Core.GraphColoringIR", "problem": "ComplexityReduction.Domain.GraphColoringIR.chromaticNumberProblem", "family": "graph"},
    {"case_id": "r1-pub-02-incidence-ir-exact-cover", "module": "ComplexityReduction.Domain.Core.IncidenceIR", "problem": "ComplexityReduction.Domain.IncidenceIR.exactCoverProblem", "family": "set-system"},
    {"case_id": "r1-pub-03-clique-cover", "module": "ComplexityReduction.Presentation.CliqueCover", "problem": "ComplexityReduction.Presentation.CliqueCover.structuredProblem", "family": "graph"},
    {"case_id": "r1-pub-04-exactly-one-neighbor", "module": "ComplexityReduction.Presentation.ExactlyOneNeighbor", "problem": "ComplexityReduction.Presentation.ExactlyOneNeighbor.presentedProblem", "family": "graph"},
    {"case_id": "r1-pub-05-most-neighbors", "module": "ComplexityReduction.Presentation.MostNeighbors", "problem": "ComplexityReduction.Presentation.MostNeighbors.presentedProblem", "family": "graph"},
    {"case_id": "r1-pub-06-steiner-tree", "module": "ComplexityReduction.Presentation.SteinerTree", "problem": "ComplexityReduction.Presentation.SteinerTree.structuredProblem", "family": "graph"},
    {"case_id": "r1-pub-07-three-sat-like", "module": "ComplexityReduction.Presentation.ThreeSATLike", "problem": "ComplexityReduction.Presentation.ThreeSATLike.presentedProblem", "family": "sat-csp"},
    {"case_id": "r1-pub-08-undirected-hamiltonian", "module": "ComplexityReduction.Presentation.UndirectedHamiltonianCircuit", "problem": "ComplexityReduction.Presentation.UndirectedHamiltonianCircuit.structuredProblem", "family": "graph"},
    {"case_id": "r1-pub-09-zero-one-ip-binary", "module": "ComplexityReduction.Presentation.ZeroOneIPBinary", "problem": "ComplexityReduction.Presentation.ZeroOneIPBinary.binaryStructuredProblem", "family": "numeric"},
    {"case_id": "r1-pub-10-cnf-sat", "module": "ComplexityReduction.Problems.Karp21.Satisfiability", "problem": "ComplexityReduction.Problems.Karp21.Satisfiability.cnfSATStructuredProblem", "family": "sat-csp"},
)


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _write(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(
        json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    temporary.replace(path)


def _build_exact_edge() -> dict[str, Any]:
    split_refs: dict[str, dict[str, str]] = {}
    oracle_cases: list[dict[str, Any]] = []
    directions: set[tuple[str, str]] = set()
    case_ids: set[str] = set()
    for split, cases in EDGE_SPLITS.items():
        public_cases: list[dict[str, Any]] = []
        for frozen in cases:
            if frozen["case_id"] in case_ids:
                raise ValueError(f"duplicate exact-edge case ID: {frozen['case_id']}")
            case_ids.add(frozen["case_id"])
            direction = (frozen["source"], frozen["target"])
            if direction in directions:
                raise ValueError(f"duplicate exact-edge direction: {direction}")
            directions.add(direction)
            public_cases.append(
                {
                    key: frozen[key]
                    for key in (
                        "case_id",
                        "module",
                        "source",
                        "target",
                        "statement",
                        "budget_profile",
                    )
                }
            )
            oracle_cases.append(
                {"case_id": frozen["case_id"], "split": split, **frozen["_oracle"]}
            )
        suite_path = SUITES / f"exact_reduction_edge_{split}_v1.json"
        _write(
            suite_path,
            {
                "schema_version": EDGE_SUITE_SCHEMA,
                "split": split,
                "cases": public_cases,
            },
        )
        split_refs[split] = {
            "suite": str(suite_path.relative_to(HARDNESS)),
            "sha256": "sha256:" + _sha256(suite_path),
        }
    if len(directions) != 24:
        raise ValueError(f"expected 24 exact-edge directions, found {len(directions)}")
    oracle_path = EVALUATION / "exact_reduction_edge_oracle_v1.json"
    _write(
        oracle_path,
        {"schema_version": EDGE_ORACLE_SCHEMA, "cases": oracle_cases},
    )
    manifest_path = HARDNESS / "EXACT_REDUCTION_EDGE_MANIFEST.json"
    _write(
        manifest_path,
        {
            "schema_version": EDGE_MANIFEST_SCHEMA,
            "benchmark_id": "exact-reduction-edge-v1",
            "splits": split_refs,
            "budget_profiles": {
                "formal-default": {
                    "authoring_mode": "model-auto",
                    "authoring_attempt_budget": 4,
                    "lean_timeout_seconds": 600,
                }
            },
            "execution": {
                "max_jobs": 4,
                "isolate_workspace": True,
                "runtime_prebuilt": True,
            },
            "scoring": {
                "oracle_sha256": "sha256:" + _sha256(oracle_path),
            },
        },
    )
    return {
        "manifest": str(manifest_path.relative_to(ROOT)),
        "manifest_sha256": _sha256(manifest_path),
        "oracle": str(oracle_path.relative_to(ROOT)),
        "oracle_sha256": _sha256(oracle_path),
        "suite_counts": {name: len(cases) for name, cases in EDGE_SPLITS.items()},
        "ready_count": sum(
            case["_oracle"]["status"] == "ready"
            for cases in EDGE_SPLITS.values()
            for case in cases
        ),
    }


def _build_archive_selection() -> dict[str, Any]:
    """Write scorer-only readiness annotations for the frozen 24 directions."""

    entries: list[dict[str, Any]] = []
    for split, cases in EDGE_SPLITS.items():
        for frozen in cases:
            oracle = frozen["_oracle"]
            status = oracle["status"]
            if status not in {
                "ready",
                "blocked_endpoint_formalization",
                "quarantined_source_error",
            }:
                raise ValueError(
                    f"unsupported archive selection status for {frozen['case_id']}: {status}"
                )
            existing_route = oracle["existing_route"]
            if status != "ready":
                cost = "endpoint-formalization-required"
                reason = (
                    "Frozen exact-edge candidate; excluded from the scored denominator "
                    "until both PresentedProblem endpoints pass independent formalization audits."
                )
            elif oracle["require_new_primitive"]:
                cost = "new-primitive-high"
                reason = (
                    "Both endpoints are formalized; the frozen direction requires a new direct "
                    "program/gadget and all exact-edge audits."
                )
            elif existing_route is not None:
                cost = "existing-edge-reconstruction"
                reason = (
                    "Both endpoints and a public forward edge are formalized; retained as an "
                    "exact-edge reconstruction control."
                )
            else:
                cost = "formal-prerequisite-review"
                reason = "Both endpoints are formalized; construction prerequisites need review."
            if frozen["case_id"] == "edge-dev-05-set-cover-to-hitting-set":
                reason += (
                    " The archive metadata source label is corrected to Set Covering from the "
                    "answer-free statement before scoring."
                )
            if frozen["case_id"] == "edge-dev-04-chromatic-to-clique-cover":
                reason += (
                    " The public benchmark is explicitly a generalized Chromatic Number edge, "
                    "not the archive's fixed three-colorability identity."
                )
            entries.append(
                {
                    "archive_id": oracle["archive_id"],
                    "case_id": frozen["case_id"],
                    "split": split,
                    "status": status,
                    "canonical_source": frozen["source"],
                    "canonical_target": frozen["target"],
                    "endpoint_readiness": status,
                    "formalization_cost": cost,
                    "selection_reason": reason,
                }
            )
    if len(entries) != 24 or len({entry["archive_id"] for entry in entries}) != 24:
        raise ValueError("archive selection must contain 24 unique archive IDs")
    pdf_only_sources = [
        {
            "source_member": f"problems/{number:02d}.pdf",
            "status": "unstructured_pdf_only",
            "endpoint_readiness": "unassessed_answer_free_problemization",
            "formalization_cost": "unknown_until_problemization",
            "selection_reason": (
                "Scorer-only provenance source; it remains outside every capability "
                "denominator until an independently rewritten answer-free case and its "
                "endpoints pass formalization audits."
            ),
            "capability_weight": 0,
        }
        for number in range(8, 15)
    ]
    pdf_candidate_specs = (
        ("pdf08-ex07-three-color-to-twelve-color", ("08",), "3-COLOR", "12-COLOR", "target_endpoint_missing", "high"),
        ("pdf08-ex09-five-color-to-careful-five-color", ("08",), "5-COLOR", "CAREFUL-5-COLOR", "source_and_target_endpoints_missing", "very_high"),
        ("pdf08-ex10c-hamiltonian-path-to-leaf-bounded-spanning-tree", ("08",), "HAMILTONIAN PATH", "SPANNING TREE WITH AT MOST 42 LEAVES", "source_and_target_endpoints_missing", "very_high"),
        ("pdf08-ex15a-hamiltonian-path-to-tonian-path", ("08",), "HAMILTONIAN PATH", "TONIAN PATH", "source_and_target_endpoints_missing", "high"),
        ("pdf08-ex15b-tonian-path-to-tonian-cycle", ("08",), "TONIAN PATH", "TONIAN CYCLE", "source_and_target_endpoints_missing", "high"),
        ("pdf08-ex16b-hamiltonian-cycle-to-double-hamiltonian-circuit", ("08",), "HAMILTONIAN CYCLE", "DOUBLE-HAMILTONIAN CIRCUIT", "target_endpoint_missing", "very_high"),
        ("pdf08-ex17-hamiltonian-cycle-to-heavy-hamiltonian-cycle", ("08",), "HAMILTONIAN CYCLE", "HEAVY HAMILTONIAN CYCLE", "target_endpoint_missing", "high"),
        ("pdf08-ex20-three-color-to-three-way-mumbletypeg", ("08",), "3-COLOR", "THREE-WAY MUMBLETYPEG", "endpoints_ready_pending_identity_audit", "high"),
        ("pdf10-thm15-nae-three-sat-to-max-cut", ("10", "14"), "NAE-3SAT", "MAX CUT", "source_endpoint_missing", "high"),
        ("pdf10-thm17-vertex-cover-to-undirected-hamiltonian-cycle", ("10",), "VERTEX COVER", "UNDIRECTED HAMILTONIAN CYCLE", "endpoints_ready_pending_identity_audit", "very_high"),
        ("pdf10-cor22-hamiltonian-cycle-to-longest-circuit", ("10",), "HAMILTONIAN CYCLE", "LONGEST CIRCUIT", "target_endpoint_missing", "high"),
        ("pdf10-ex08-dominating-set-to-k-center", ("10",), "DOMINATING SET", "K-CENTER", "source_and_target_endpoints_missing", "very_high"),
        ("pdf11-sat-to-exact-cover", ("11",), "SAT", "EXACT COVER", "endpoints_ready_pending_identity_audit", "very_high"),
        ("pdf11-exact-cover-to-directed-hamiltonian-cycle", ("11",), "EXACT COVER", "DIRECTED HAMILTONIAN CYCLE", "endpoints_ready_pending_identity_audit", "very_high"),
        ("pdf11-exact-cover-to-subset-sum", ("11",), "EXACT COVER", "SUBSET SUM", "target_endpoint_missing", "high"),
        ("pdf12-three-partition-to-minimum-makespan", ("12",), "3-PARTITION", "MINIMUM MAKESPAN SCHEDULING", "source_and_target_endpoints_missing", "very_high"),
    )
    pdf_only_candidates = [
        {
            "candidate_id": candidate_id,
            "source_members": [f"problems/{number}.pdf" for number in source_numbers],
            "canonical_source_label": source,
            "canonical_target_label": target,
            "split": "frontier" if cost == "very_high" else "reserve",
            "status": (
                "blocked_answer_free_problemization"
                if readiness == "endpoints_ready_pending_identity_audit"
                else "blocked_endpoint_formalization"
            ),
            "endpoint_readiness": readiness,
            "formalization_cost": cost,
            "selection_reason": (
                "Scorer-only PDF candidate; capability weight remains zero until "
                "independent answer-free problemization, endpoint/identity audits, and "
                "formal construction prerequisites are complete."
            ),
            "capability_weight": 0,
        }
        for candidate_id, source_numbers, source, target, readiness, cost in pdf_candidate_specs
    ]
    path = EVALUATION / "np_hard_problem_archive_selection_v1.json"
    _write(
        path,
        {
            "schema_version": ARCHIVE_SELECTION_SCHEMA,
            "entries": entries,
            "pdf_only_sources": pdf_only_sources,
            "pdf_only_candidates": pdf_only_candidates,
        },
    )
    return {
        "selection": str(path.relative_to(ROOT)),
        "sha256": _sha256(path),
        "entry_count": len(entries),
        "pdf_only_source_count": len(pdf_only_sources),
        "pdf_only_candidate_count": len(pdf_only_candidates),
        "status_counts": {
            status: sum(entry["status"] == status for entry in entries)
            for status in sorted({entry["status"] for entry in entries})
        },
    }


def _build_r1_public_suite() -> dict[str, Any]:
    path = GATE_SUITES / "np_hard_public_r1_coverage_v1.json"
    _write(
        path,
        {
            "schema_version": "hardness_np_hard_public_r1_coverage_suite_v1",
            "suite_id": "public-existing-route-coverage-v1",
            "cases": list(R1_PUBLIC_CASES),
        },
    )
    return {
        "suite": str(path.relative_to(ROOT)),
        "sha256": _sha256(path),
        "case_count": len(R1_PUBLIC_CASES),
    }


def main() -> int:
    matrix_path = ROOT / "Gate/NP_HARD_TARGET_MATRIX.json"
    scope_policy_path = ROOT / "agent/hardness/data/np_hard_scope_policy.json"
    matrix = json.loads(matrix_path.read_text(encoding="utf-8"))
    by_problem = {row["canonical_declaration"]: row for row in matrix["identities"]}
    suite_refs: dict[str, dict[str, str]] = {}
    oracle_cases: list[dict[str, Any]] = []
    seen_identity: dict[str, str] = {}

    for split, cases in SPLITS.items():
        public_cases: list[dict[str, Any]] = []
        for frozen in cases:
            row = by_problem.get(frozen["problem"])
            if row is None:
                raise ValueError(f"capability problem missing from target matrix: {frozen['problem']}")
            identity = row["identity_id"]
            previous = seen_identity.get(identity)
            if previous is not None:
                raise ValueError(
                    f"canonical identity appears in both {previous} and {frozen['case_id']}"
                )
            seen_identity[identity] = frozen["case_id"]
            public_cases.append({key: frozen[key] for key in ("case_id", "module", "problem", "family", "budget_profile")})
            oracle_cases.append(
                {
                    "case_id": frozen["case_id"],
                    "split": split,
                    "family": frozen["family"],
                    "canonical_identity": identity,
                    "canonical_problem": row["canonical_declaration"],
                    "matrix_disposition": row["disposition"],
                    **frozen["_oracle"],
                }
            )
        suite_path = GATE_SUITES / f"np_hard_capability_{split}_v1.json"
        _write(
            suite_path,
            {
                "schema_version": SUITE_SCHEMA,
                "suite_id": f"np-hard-capability-{split}-v1",
                "split": split,
                "cases": public_cases,
            },
        )
        suite_refs[split] = {
            "file": str(suite_path.relative_to(ROOT)),
            "sha256": _sha256(suite_path),
        }

    if len(seen_identity) != 34:
        raise ValueError(f"expected 34 C0/F0 identities, found {len(seen_identity)}")
    r1_identity_ids = {
        by_problem[case["problem"]]["identity_id"] for case in R1_PUBLIC_CASES
    }
    if len(r1_identity_ids) != 10:
        raise ValueError("R1 public coverage must contain 10 unique canonical identities")
    if r1_identity_ids.intersection(seen_identity):
        raise ValueError("R1 public coverage overlaps C0/F0 canonical identities")
    matrix_identity_ids = {row["identity_id"] for row in matrix["identities"]}
    if r1_identity_ids.union(seen_identity) != matrix_identity_ids:
        raise ValueError("C0/F0/R1 assignments do not partition all 44 identities")
    if any(
        by_problem[case["problem"]].get("has_forward_route") is not True
        for case in R1_PUBLIC_CASES
    ):
        raise ValueError("R1 public coverage contains an identity without a forward route")
    oracle_path = EVALUATION / "np_hard_capability_oracle_v1.json"
    _write(
        oracle_path,
        {
            "schema_version": ORACLE_SCHEMA,
            "benchmark_id": "np-hard-capability-v1",
            "cases": oracle_cases,
        },
    )
    manifest_path = ROOT / "Archive/CAPABILITY_MANIFEST.json"
    _write(
        manifest_path,
        {
            "schema_version": MANIFEST_SCHEMA,
            "benchmark_id": "np-hard-capability-v1",
            "objective": "target-hardness",
            "final_lean_type": "ComplexityReduction.Certificate.NativeTMNPHard input",
            "suites": suite_refs,
            "oracle": {
                "file": str(oracle_path.relative_to(ROOT)),
                "sha256": _sha256(oracle_path),
                "runner_access": "forbidden",
            },
            "target_matrix": {
                "file": str(matrix_path.relative_to(ROOT)),
                "sha256": _sha256(matrix_path),
            },
            "scope_policy": {
                "file": str(scope_policy_path.relative_to(ROOT)),
                "sha256": _sha256(scope_policy_path),
            },
            "required_model_profile": {
                "provider": "DeepSeek",
                "base_url": "https://api.deepseek.com",
                "model": "deepseek-v4-flash",
                "reasoning_effort": "low",
                "temperature": 0.0,
                "max_tokens": 16000,
                "timeout_seconds": 300,
                "max_retries": 0,
            },
            "budget_profiles": {
                "formal-default": {
                    "attempt_budget": 4,
                    "call_budget": "typed-dag-auto",
                    "lean_timeout_seconds": 600,
                },
                "frontier-default": {
                    "attempt_budget": 4,
                    "call_budget": "typed-dag-auto",
                    "lean_timeout_seconds": 600,
                },
            },
            "split_policy": {
                "canonical_identity_disjoint": True,
                "family_heldout": ["other"],
                "capability_node_heldout": ["new-gadget", "polynomial-bound"],
                "counts": {"dev": 8, "validation": 8, "heldout": 16, "frontier": 2},
            },
            "reserve_policy": {
                "promote_threshold": 0.9,
                "promote_consecutive_versions": 2,
                "intermediate_case_threshold": 0.1,
            },
            "public_suite_case_fields": ["case_id", "module", "problem", "family", "budget_profile"],
            "forbidden_runner_paths": [
                "ACTIVE_AGENT_IMPROVEMENT_PLAN.md",
                "Benchmark/Hardness/Evaluation",
                "problems.7z",
                "problems",
                "problems.json",
                "problems_clean.json",
            ],
        },
    )
    exact_edge = _build_exact_edge()
    archive_selection = _build_archive_selection()
    r1_public = _build_r1_public_suite()
    print(
        json.dumps(
            {
                "manifest": str(manifest_path.relative_to(ROOT)),
                "manifest_sha256": _sha256(manifest_path),
                "suite_counts": {name: len(cases) for name, cases in SPLITS.items()},
                "oracle_sha256": _sha256(oracle_path),
                "exact_edge": exact_edge,
                "archive_selection": archive_selection,
                "r1_public": r1_public,
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
