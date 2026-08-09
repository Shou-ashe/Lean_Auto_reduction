import itertools
import unittest

from agent.hardness.artifact import (
    CoreGeneralizationArtifactCase,
    build_core_generalization_batch_artifact_source,
)
from agent.hardness.benchmark import OBJECTIVES
from agent.hardness.boolean_csp_classes import (
    BooleanCSPContractError,
    BooleanCSPProblemClass,
    BooleanRelation,
    Gamma,
    GammaClassificationRegistry,
    RegisteredComplexity,
    SchaeferClass,
)
from agent.hardness.in_p import (
    BooleanCSPInstance,
    CSPConstraint,
    InPCertificate,
    InPContractError,
    PolynomialTimeBound,
    PredicateEquivalence,
    horn_unit_propagation,
    validate_in_p_certificate,
)
from agent.hardness.stage_q_artifact import (
    StageQInPArtifactCase,
    build_stage_q_in_p_batch_artifact_source,
)
from agent.hardness.stage_q_contract import (
    StageQContractError,
    StageQRequest,
    close_prove_in_p,
)


class BooleanCSPClassTests(unittest.TestCase):
    def test_gamma_fingerprint_is_order_and_duplicate_independent(self) -> None:
        equality = BooleanRelation.from_rows(2, ((False, False), (True, True)))
        implication = BooleanRelation.from_rows(
            2, ((False, False), (False, True), (True, True))
        )
        first = Gamma.finite((equality, implication, equality))
        second = Gamma.finite((implication, equality))
        self.assertEqual(first.relations, second.relations)
        self.assertEqual(first.fingerprint, second.fingerprint)

    def test_schaefer_class_decider_uses_polymorphism_closure(self) -> None:
        implication = BooleanRelation.from_rows(
            2, ((False, False), (False, True), (True, True))
        )
        xor_even = BooleanRelation.from_rows(
            3,
            tuple(
                row
                for row in itertools.product((False, True), repeat=3)
                if sum(row) % 2 == 0
            ),
        )
        nae = BooleanRelation.from_rows(
            3,
            tuple(
                row
                for row in itertools.product((False, True), repeat=3)
                if len(set(row)) > 1
            ),
        )
        self.assertTrue(Gamma.finite((implication,)).classify().contains(SchaeferClass.HORN))
        self.assertTrue(Gamma.finite((xor_even,)).classify().contains(SchaeferClass.AFFINE))
        self.assertFalse(Gamma.finite((nae,)).classify().tractable)

    def test_infinite_gamma_and_single_instance_are_rejected(self) -> None:
        relation = BooleanRelation.from_rows(1, ((False,),))
        with self.assertRaisesRegex(BooleanCSPContractError, "infinite_gamma"):
            Gamma.finite(relation for _ in range(1))
        registry = GammaClassificationRegistry()
        with self.assertRaisesRegex(BooleanCSPContractError, "single_instance_disguised"):
            registry.register(  # type: ignore[arg-type]
                object(), RegisteredComplexity.P, evidence_id="proof"
            )

    def test_registry_rejects_p_npc_double_registration(self) -> None:
        nae = BooleanRelation.from_rows(
            3,
            tuple(
                row
                for row in itertools.product((False, True), repeat=3)
                if len(set(row)) > 1
            ),
        )
        problem = BooleanCSPProblemClass("nae-3", Gamma.finite((nae,)))
        registry = GammaClassificationRegistry()
        registry.register(problem, RegisteredComplexity.P, evidence_id="p-proof")
        with self.assertRaisesRegex(BooleanCSPContractError, "p_npc_double_registration"):
            registry.register(problem, RegisteredComplexity.NPC, evidence_id="hardness-proof")

    def test_tractable_gamma_cannot_be_registered_npc(self) -> None:
        all_true = BooleanRelation.from_rows(1, ((True,),))
        problem = BooleanCSPProblemClass("unit-true", Gamma.finite((all_true,)))
        with self.assertRaisesRegex(BooleanCSPContractError, "tractable_gamma_registered_npc"):
            GammaClassificationRegistry().register(
                problem, RegisteredComplexity.NPC, evidence_id="bad"
            )

    def test_nested_structural_parameters_cannot_mutate_class_identity(self) -> None:
        relation = BooleanRelation.from_rows(1, ((True,),))
        supplied = {"occurrence": {"bounds": [3, 4]}}
        problem = BooleanCSPProblemClass("bounded", Gamma.finite((relation,)), supplied)
        fingerprint = problem.fingerprint
        supplied["occurrence"]["bounds"].append(5)
        self.assertEqual(problem.fingerprint, fingerprint)
        with self.assertRaises(TypeError):
            problem.structural_constraints["occurrence"]["new"] = True


class HornAlgorithmTests(unittest.TestCase):
    def test_forward_chaining_matches_bruteforce_on_small_horn_instances(self) -> None:
        implication = BooleanRelation.from_rows(
            2, ((False, False), (False, True), (True, True))
        )
        force_true = BooleanRelation.from_rows(1, ((True,),))
        force_false = BooleanRelation.from_rows(1, ((False,),))
        gamma = Gamma.finite((implication, force_true, force_false))
        atoms = (
            CSPConstraint(implication, (0, 1)),
            CSPConstraint(implication, (1, 0)),
            CSPConstraint(force_true, (0,)),
            CSPConstraint(force_true, (1,)),
            CSPConstraint(force_false, (0,)),
            CSPConstraint(force_false, (1,)),
        )
        for size in range(4):
            for constraints in itertools.combinations_with_replacement(atoms, size):
                instance = BooleanCSPInstance(gamma, tuple(constraints))
                expected = any(
                    instance.satisfies({0: left, 1: right})
                    for left, right in itertools.product((False, True), repeat=2)
                )
                self.assertEqual(horn_unit_propagation(instance), expected, constraints)

    def test_horn_solver_rejects_non_horn_gamma(self) -> None:
        one_in_three = BooleanRelation.from_rows(
            3,
            tuple(row for row in itertools.product((False, True), repeat=3) if sum(row) == 1),
        )
        instance = BooleanCSPInstance(Gamma.finite((one_in_three,)), ())
        with self.assertRaisesRegex(InPContractError, "class_mismatch"):
            horn_unit_propagation(instance)


class InPCertificateTests(unittest.TestCase):
    def test_prove_in_p_artifact_uses_versioned_protocol(self) -> None:
        source = build_stage_q_in_p_batch_artifact_source(
            (
                StageQInPArtifactCase(
                    case_id="stage-q-p",
                    input_module="Example.Input",
                    source_declaration="Example.problem",
                    membership_lean_term="Example.problemInP",
                ),
            )
        )
        self.assertIn("import ComplexityReduction.Protocol.InP", source)
        self.assertIn("TypedInPRequestV1", source)
        self.assertIn("TypedInPResultV1.proveInP", source)
        self.assertIn("Certificate.NativeTMInP Example.problem", source)
        self.assertNotIn("objective := .proveInNP", source)

    def test_frozen_reduction_abi_does_not_accept_prove_in_p(self) -> None:
        self.assertNotIn("prove_in_p", OBJECTIVES)
        with self.assertRaisesRegex(ValueError, "unsupported objective prove_in_p"):
            build_core_generalization_batch_artifact_source(
                (
                    CoreGeneralizationArtifactCase(
                        case_id="must-stay-versioned",
                        input_module="Example.Input",
                        objective="prove_in_p",
                        source_declaration="Example.problem",
                        proof_term="Example.problemInP",
                    ),
                )
            )

    def test_certificate_gate_checks_exact_bindings_and_predicate(self) -> None:
        fingerprint = "sha256:" + "1" * 64
        certificate = InPCertificate(
            problem_fingerprint=fingerprint,
            algorithm_id="even",
            algorithm=lambda value: value % 2 == 0,
            equivalence=PredicateEquivalence(fingerprint, "even", "Example.even_correct"),
            polytime=PolynomialTimeBound(1, 1, 1, "Example.even_polytime"),
        )
        receipt = validate_in_p_certificate(
            certificate,
            predicate=lambda value: value % 2 == 0,
            validation_instances=tuple(range(12)),
        )
        self.assertEqual(receipt.checked_instances, 12)

        with self.assertRaisesRegex(InPContractError, "predicate_mismatch"):
            validate_in_p_certificate(
                certificate,
                predicate=lambda _value: True,
                validation_instances=(1,),
            )

    def test_certificate_rejects_missing_or_cross_bound_evidence(self) -> None:
        fingerprint = "sha256:" + "2" * 64
        with self.assertRaisesRegex(InPContractError, "algorithm_mismatch"):
            InPCertificate(
                problem_fingerprint=fingerprint,
                algorithm_id="first",
                algorithm=lambda _value: True,
                equivalence=PredicateEquivalence(fingerprint, "second", "wrong"),
                polytime=PolynomialTimeBound(0, 0, 1, "constant"),
            )
        with self.assertRaisesRegex(InPContractError, "missing_polytime"):
            PolynomialTimeBound(1, 1, 0, "")
        with self.assertRaisesRegex(InPContractError, "invalid_fingerprint"):
            InPCertificate(
                problem_fingerprint="sha256:not-a-digest",
                algorithm_id="bad",
                algorithm=lambda _value: True,
                equivalence=PredicateEquivalence(
                    "sha256:" + "0" * 64, "bad", "wrong-fingerprint"
                ),
                polytime=PolynomialTimeBound(0, 0, 1, "constant"),
            )

    def test_stage_q_finish_is_bound_to_the_exact_class(self) -> None:
        fingerprint = "sha256:" + "3" * 64
        request = StageQRequest(fingerprint, "Example.problem")
        certificate = InPCertificate(
            problem_fingerprint=fingerprint,
            algorithm_id="always",
            algorithm=lambda _value: True,
            equivalence=PredicateEquivalence(
                fingerprint, "always", "Example.always_correct"
            ),
            polytime=PolynomialTimeBound(0, 0, 1, "Example.always_polytime"),
        )
        payload = close_prove_in_p(
            request,
            certificate,
            predicate=lambda _value: True,
            validation_instances=(0, 1),
            algorithm_lean_term="Example.problemInP",
        )
        self.assertEqual(payload.request, request)
        self.assertEqual(payload.receipt.problem_fingerprint, fingerprint)

        changed = StageQRequest("sha256:" + "4" * 64, "Example.problem")
        with self.assertRaisesRegex(StageQContractError, "exact_task_binding"):
            request.assert_same(changed)
        with self.assertRaisesRegex(StageQContractError, "class_fingerprint_mismatch"):
            close_prove_in_p(
                changed,
                certificate,
                predicate=lambda _value: True,
                validation_instances=(0,),
                algorithm_lean_term="Example.problemInP",
            )


if __name__ == "__main__":
    unittest.main()
