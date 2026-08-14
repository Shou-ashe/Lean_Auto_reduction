"""NP-hard-first research orchestrator.

The closed resolver remains the first fast path.  Its no-path result opens a
typed theorem search instead of immediately selecting a fixed authoring DAG.
"""

from __future__ import annotations

import json
import secrets
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from agent.hardness.model_client import DeepSeekClient, DeepSeekConfig
from agent.hardness.np_hard import (
    build_np_hard_probe_source,
    parse_np_hard_probe_output,
)
from agent.hardness.np_hard_input import (
    certify_np_hard_input,
    resolve_np_hard_input_reference,
)
from agent.hardness.np_hard_production import public_np_hard_status
from agent.hardness.lean_runner import build_module_command, run_command, sha256_file
from agent.hardness.state import JobStore

from .model_planner import choose_candidate, confirm_existing_route
from .models import ProofStep, ReductionResult, RootGoal, SearchBudget, SearchTrace
from .premise_solvers import plans_for
from .profiles import get_profile
from .theorem_index import project_module_catalog, query_theorem_index
from .verifier import (
    build_direct_artifact_source,
    build_theorem_artifact_source,
    verify_artifact,
)


@dataclass(frozen=True)
class ReductionOrchestratorConfig:
    root: Path
    input_module: str
    problem_declaration: str
    output_dir: Path
    profile: str = "research"
    lean_timeout_seconds: int = 600
    budget: SearchBudget = SearchBudget()
    model_policy: str = "auto"
    deepseek: DeepSeekConfig | None = None
    runtime_prebuilt: bool = False


class ReductionOrchestrator:
    def __init__(self, config: ReductionOrchestratorConfig):
        self.config = config
        self.root = config.root.resolve()
        self.output_dir = config.output_dir.resolve()
        self.profile = get_profile(config.profile)
        config.budget.validate()
        if config.model_policy not in {"disabled", "auto", "required"}:
            raise ValueError("unsupported model policy")

    @staticmethod
    def _command(command) -> dict[str, Any]:
        return command.to_dict()

    def _write_report(self, store: JobStore, result: ReductionResult) -> ReductionResult:
        store.write_json("report.json", result.to_dict())
        return result

    def _model_failure(
        self,
        *,
        store: JobStore,
        trace: SearchTrace,
        root_goal: RootGoal,
        identity: dict[str, Any],
        deterministic_result: dict[str, Any] | None,
        code: str,
        explanation: str | None,
    ) -> ReductionResult:
        return self._write_report(
            store,
            ReductionResult(
                status="FAILED",
                profile=self.profile.name,
                root_goal=root_goal,
                output_dir=str(self.output_dir),
                failure_code=code,
                explanation=explanation,
                proof_tree=tuple(trace.steps),
                commands=tuple(trace.commands),
                model_calls=tuple(trace.model_calls),
                input_identity=identity,
                deterministic_result=deterministic_result,
            ),
        )

    def _required_model_client(self) -> DeepSeekClient | None:
        if self.config.model_policy != "required":
            return None
        if self.config.deepseek is None or self.config.budget.max_model_calls < 1:
            return None
        return DeepSeekClient(self.config.deepseek)

    def run(self) -> ReductionResult:
        store = JobStore(self.output_dir)
        trace = SearchTrace()
        with store.exclusive_run():
            reference = resolve_np_hard_input_reference(
                root=self.root,
                input_module=self.config.input_module,
                requested_term=self.config.problem_declaration,
                timeout_seconds=self.config.lean_timeout_seconds,
            )
            toolchain = (self.root / "Lean" / "lean-toolchain").read_text(
                encoding="utf-8"
            ).strip()
            identity, input_command = certify_np_hard_input(
                root=self.root,
                reference=reference,
                certificate_path=store.path("InputNormalization.lean"),
                toolchain=toolchain,
                lake_manifest_sha256=sha256_file(
                    self.root / "Lean" / "lake-manifest.json"
                ),
                timeout_seconds=self.config.lean_timeout_seconds,
            )
            trace.commands.append(self._command(input_command))
            root_goal = RootGoal.for_problem(
                input_module=reference.input_module,
                problem_declaration=reference.problem_declaration,
                endpoint_fingerprint=identity.normalized_problem_node,
            )
            store.write_json(
                "request.json",
                {
                    "schema_version": "np_hard_reduction_request_v1",
                    "profile": self.profile.name,
                    "root_goal": root_goal.__dict__,
                    "budget": self.config.budget.__dict__,
                    "model_policy": self.config.model_policy,
                },
            )

            if not self.config.runtime_prebuilt:
                build = run_command(
                    build_module_command([reference.input_module]),
                    cwd=self.root / "Lean",
                    timeout_seconds=self.config.lean_timeout_seconds,
                    output_limit=16 * 1024 * 1024,
                )
                trace.commands.append(self._command(build))
                if not build.ok:
                    return self._write_report(
                        store,
                        ReductionResult(
                            status="FAILED",
                            profile=self.profile.name,
                            root_goal=root_goal,
                            output_dir=str(self.output_dir),
                            failure_code="lean_infrastructure_error",
                            explanation=build.stderr or build.stdout,
                            proof_tree=tuple(trace.steps),
                            commands=tuple(trace.commands),
                            input_identity=identity.to_dict(),
                        ),
                    )

            fast_nonce = secrets.token_hex(16)
            fast_probe_path = store.write_text(
                "FastPathProbe.lean",
                build_np_hard_probe_source(
                    input_module=reference.input_module,
                    problem_declaration=reference.problem_declaration,
                    nonce=fast_nonce,
                ),
            )
            fast_command = run_command(
                ["lake", "env", "lean", str(fast_probe_path)],
                cwd=self.root / "Lean",
                timeout_seconds=self.config.lean_timeout_seconds,
                output_limit=16 * 1024 * 1024,
            )
            trace.commands.append(self._command(fast_command))
            if not fast_command.ok:
                return self._write_report(
                    store,
                    ReductionResult(
                        status="FAILED",
                        profile=self.profile.name,
                        root_goal=root_goal,
                        output_dir=str(self.output_dir),
                        failure_code="lean_infrastructure_error",
                        explanation=fast_command.stderr or fast_command.stdout,
                        proof_tree=tuple(trace.steps),
                        commands=tuple(trace.commands),
                        input_identity=identity.to_dict(),
                    ),
                )
            deterministic = parse_np_hard_probe_output(
                stdout=fast_command.stdout,
                stderr=fast_command.stderr,
                nonce=fast_nonce,
                problem_declaration=reference.problem_declaration,
            )
            deterministic_payload = deterministic.to_dict()
            trace.steps.append(
                ProofStep(
                    action="resolver-fast-path",
                    goal=root_goal.proposition,
                    status=("verified" if deterministic.resolution is not None else "continued"),
                )
            )
            if deterministic.resolution is not None:
                if self.config.model_policy == "required":
                    model = self._required_model_client()
                    if model is None:
                        return self._model_failure(
                            store=store,
                            trace=trace,
                            root_goal=root_goal,
                            identity=identity.to_dict(),
                            deterministic_result=deterministic_payload,
                            code="model_provider_unavailable",
                            explanation="model-required needs a configured model and positive call budget",
                        )
                    record = confirm_existing_route(
                        model=model,
                        goal=root_goal.proposition,
                        resolver_result=deterministic.resolution.to_dict(),
                    )
                    trace.model_calls.append(record)
                    if not record.called or record.status_code != 200:
                        return self._model_failure(
                            store=store,
                            trace=trace,
                            root_goal=root_goal,
                            identity=identity.to_dict(),
                            deterministic_result=deterministic_payload,
                            code=(
                                "model_provider_unavailable"
                            ),
                            explanation=record.error,
                        )
                artifact_path = store.write_text(
                    "Artifact.lean",
                    build_direct_artifact_source(
                        input_module=reference.input_module,
                        problem_declaration=reference.problem_declaration,
                    ),
                )
                check, replay, digest = verify_artifact(
                    root=self.root,
                    artifact_path=artifact_path,
                    timeout_seconds=self.config.lean_timeout_seconds,
                    replay=self.profile.independent_replay,
                )
                trace.commands.append(self._command(check))
                if replay is not None:
                    trace.commands.append(self._command(replay))
                status = "VERIFIED" if check.ok and (replay is None or replay.ok) else "FAILED"
                result = ReductionResult(
                    status=status,
                    profile=self.profile.name,
                    root_goal=root_goal,
                    output_dir=str(self.output_dir),
                    failure_code=None if status == "VERIFIED" else "final_lean_failed",
                    artifact_file=str(artifact_path),
                    artifact_sha256=digest,
                    proof_tree=tuple(trace.steps),
                    commands=tuple(trace.commands),
                    input_identity=identity.to_dict(),
                    deterministic_result=deterministic_payload,
                    model_calls=tuple(trace.model_calls),
                    exact_type_verified=check.ok,
                    kernel_verified=check.ok,
                    axiom_audit_passed=check.ok,
                    independent_replay_passed=(replay.ok if replay is not None else check.ok),
                    endpoint_equality_audit_passed=check.ok,
                )
                return self._write_report(store, result)

            modules = project_module_catalog(self.root)
            candidates, index_command = query_theorem_index(
                root=self.root,
                input_module=reference.input_module,
                problem_declaration=reference.problem_declaration,
                modules=modules,
                output_path=store.path("TheoremIndexProbe.lean"),
                timeout_seconds=self.config.lean_timeout_seconds,
            )
            trace.commands.append(self._command(index_command))
            trace.candidates.extend(candidates)
            store.write_json(
                "theorem-index.json",
                {"modules": list(modules), "candidates": [candidate.__dict__ for candidate in candidates]},
            )

            deterministic_candidates = [
                candidate
                for candidate in candidates[: self.config.budget.max_candidates_per_goal]
                if len(plans_for(candidate)) == candidate.premise_count
            ]
            deterministic_candidates.sort(
                key=lambda candidate: (
                    0 if candidate.is_schaefer_schema else 1,
                    candidate.premise_count,
                    candidate.declaration,
                )
            )
            failures: list[dict[str, Any]] = []
            selected = None
            selected_plans = ()
            selected_check = None
            selected_digest = None
            checks = 0
            candidate_order = list(deterministic_candidates)

            if self.config.model_policy == "required":
                model = self._required_model_client()
                if model is None:
                    return self._model_failure(
                        store=store,
                        trace=trace,
                        root_goal=root_goal,
                        identity=identity.to_dict(),
                        deterministic_result=deterministic_payload,
                        code="model_provider_unavailable",
                        explanation="model-required needs a configured model and positive call budget",
                    )
                planning_candidates = tuple(candidate_order) or candidates
                proposed, record = choose_candidate(
                    model=model,
                    goal=root_goal.proposition,
                    candidates=planning_candidates,
                    failures=(),
                )
                trace.model_calls.append(record)
                if not record.called or record.status_code != 200:
                    return self._model_failure(
                        store=store,
                        trace=trace,
                        root_goal=root_goal,
                        identity=identity.to_dict(),
                        deterministic_result=deterministic_payload,
                        code=(
                            "model_provider_unavailable"
                        ),
                        explanation=record.error,
                    )
                if proposed is not None and len(plans_for(proposed)) == proposed.premise_count:
                    candidate_order = [
                        proposed,
                        *(candidate for candidate in candidate_order if candidate != proposed),
                    ]

            for candidate in candidate_order:
                if checks >= self.config.budget.max_lean_checks:
                    break
                plans = plans_for(candidate)
                source = build_theorem_artifact_source(
                    input_module=reference.input_module,
                    problem_declaration=reference.problem_declaration,
                    candidate=candidate,
                    premise_plans=plans,
                )
                candidate_path = store.write_text("Artifact.lean", source)
                check, _, digest = verify_artifact(
                    root=self.root,
                    artifact_path=candidate_path,
                    timeout_seconds=self.config.lean_timeout_seconds,
                    replay=False,
                )
                checks += 1
                trace.commands.append(self._command(check))
                if check.ok:
                    selected = candidate
                    selected_plans = plans
                    selected_check = check
                    selected_digest = digest
                    break
                failures.append(
                    {
                        "declaration": candidate.declaration,
                        "diagnostic": (check.stderr or check.stdout)[-4000:],
                    }
                )

            if selected is None and self.config.model_policy == "auto" and candidates:
                if len(trace.model_calls) < self.config.budget.max_model_calls:
                    config = self.config.deepseek
                    if config is not None:
                        proposed, record = choose_candidate(
                            model=DeepSeekClient(config),
                            goal=root_goal.proposition,
                            candidates=candidates,
                            failures=tuple(failures),
                        )
                        trace.model_calls.append(record)
                        if proposed is not None:
                            plans = plans_for(proposed)
                            if len(plans) == proposed.premise_count:
                                source = build_theorem_artifact_source(
                                    input_module=reference.input_module,
                                    problem_declaration=reference.problem_declaration,
                                    candidate=proposed,
                                    premise_plans=plans,
                                )
                                candidate_path = store.write_text(
                                    "Artifact.lean", source
                                )
                                check, _, digest = verify_artifact(
                                    root=self.root,
                                    artifact_path=candidate_path,
                                    timeout_seconds=self.config.lean_timeout_seconds,
                                    replay=False,
                                )
                                trace.commands.append(self._command(check))
                                if check.ok:
                                    selected, selected_plans = proposed, plans
                                    selected_check = check
                                    selected_digest = digest
                                else:
                                    failures.append(
                                        {
                                            "declaration": proposed.declaration,
                                            "diagnostic": (check.stderr or check.stdout)[-4000:],
                                        }
                                    )

            if selected is None:
                status = "FAILED" if self.config.model_policy == "required" else "BLOCKED"
                result = ReductionResult(
                    status=status,
                    profile=self.profile.name,
                    root_goal=root_goal,
                    output_dir=str(self.output_dir),
                    failure_code="no_verified_theorem_route",
                    explanation=json.dumps(failures[-3:], ensure_ascii=False),
                    theorem_candidates=tuple(candidates),
                    proof_tree=tuple(trace.steps),
                    commands=tuple(trace.commands),
                    model_calls=tuple(trace.model_calls),
                    input_identity=identity.to_dict(),
                    deterministic_result=deterministic_payload,
                )
                return self._write_report(store, result)

            artifact_path = store.path("Artifact.lean")
            assert selected_check is not None
            final_check = selected_check
            digest = selected_digest
            replay = None
            if self.profile.independent_replay:
                replay, _, _ = verify_artifact(
                    root=self.root,
                    artifact_path=artifact_path,
                    timeout_seconds=self.config.lean_timeout_seconds,
                    replay=False,
                )
                trace.commands.append(self._command(replay))
            trace.steps.append(
                ProofStep(
                    action="apply-theorem",
                    goal=root_goal.proposition,
                    declaration=selected.declaration,
                )
            )
            for premise, plan in zip(selected.premises, selected_plans, strict=True):
                trace.steps.append(
                    ProofStep(
                        action="solve-premise",
                        goal=premise,
                        solver=plan.solver,
                    )
                )
            verified = final_check.ok and (replay is None or replay.ok)
            result = ReductionResult(
                status="VERIFIED" if verified else "FAILED",
                profile=self.profile.name,
                root_goal=root_goal,
                output_dir=str(self.output_dir),
                failure_code=None if verified else "final_lean_failed",
                explanation=None if verified else (final_check.stderr or final_check.stdout),
                artifact_file=str(artifact_path),
                artifact_sha256=digest,
                theorem_candidates=tuple(candidates),
                selected_theorem=selected.declaration,
                selected_theorem_module=selected.module,
                proof_tree=tuple(trace.steps),
                commands=tuple(trace.commands),
                model_calls=tuple(trace.model_calls),
                input_identity=identity.to_dict(),
                deterministic_result=deterministic_payload,
                exact_type_verified=final_check.ok,
                kernel_verified=final_check.ok,
                axiom_audit_passed=final_check.ok,
                independent_replay_passed=(replay.ok if replay is not None else final_check.ok),
                endpoint_equality_audit_passed=final_check.ok,
            )
            return self._write_report(store, result)


def public_status(result: ReductionResult) -> str:
    return public_np_hard_status(
        internal_status=result.status,
        failure_code=result.failure_code,
        model_calls=result.model_call_count,
    )
