# ComplexityReduction Hardness Agent

The current implementation provides Phases 0--6 and the first Phase 7 model-authoring
vertical slice from
`HARDNESS_AGENT_IMPLEMENTATION_PLAN.md`:

- deterministic exact-input `probe -> route -> artifact -> verified` resolution;
- a checked job-local Native Cook--Levin root and production suffix composition;
- Lean-side typed gap classification with exact endpoints, stable content-addressed `GapIR`,
  deterministic blocker replay, and one-capability authoring task packets;
- deterministic closure of `unresolvedFamilyPremise`, `lawfulPresentation`, and existing-
  executable `primitive` blockers through fenced, job-local Lean candidates;
- exact bundle validation for a lawful structural-certificate primary capability or a
  `Program.Primitive` primary capability together with the derived `CertifiedReduction` route
  consumed by the resolver;
- seven independently compiled program-indexed authoring checkpoints:
  `executable`, `executable_direct_tm`, `primitive`, `program`, `semantic_proof`, `direct_tm`, and
  `certified_reduction`;
- exact same-index bundle validation across the executable, primitive, program, semantic proof,
  dependent direct-TM evidence, and final route; second-program proofs and cost-only facades are
  rejected;
- typed exact `proveInNP` and `proveNPComplete` resolution, with observational evidence kinds kept
  distinct as `native_membership`, `registered_completeness`, and `transported_completeness`;
- four independently compiled native-membership checkpoints: `verifier`,
  `witness_presentation`, `discipline`, and `native_membership`, followed by a dedicated Lean bundle
  validator and a fresh registry reconstruction;
- exact registered native completeness and forward-only complete-hub-to-target transport; the
  transported lane requires exact target `NativeTMInNP`, so backend membership and a reversed
  target-to-hub route cannot establish completeness;
- an independent standard-axiom audit of the extracted membership or completeness artifact;
- declaration-level dependency isolation: executable, direct-TM, and semantic template components
  are observed as separate global declarations, so a poisoned semantic theorem fails only its own
  checkpoint;
- a fresh capability scan, final resolver reconstruction, the standard-axiom gate, and
  deterministic replay after every accepted candidate;
- explicit `--resume` auditing: a previously verified candidate that is missing or changed is
  never silently regenerated or recovered from a stale `.olean`; for staged candidates integrity
  is checked over the complete ordered source bundle and the exact typed blocker is reconstructed
  instead.

`GapIR`, task packets, route JSON, and model output remain observational. They are never consumed
by `by_hardness_resolver` and cannot turn a blocked request into a certificate.

Configure DeepSeek through a local `.env` file. The key is read at runtime and is never emitted in
the Lean artifact or JSON report:

```text
DEEPSEEK_BASE_URL=https://api.deepseek.com
DEEPSEEK_API_KEY=your-key
DEEPSEEK_MODEL=deepseek-v4-flash
DEEPSEEK_TIMEOUT_SECONDS=300
DEEPSEEK_MAX_TOKENS=16000
DEEPSEEK_MAX_RETRIES=0
DEEPSEEK_REASONING_EFFORT=low
```

Copy `.env.example` to `.env` and fill in `DEEPSEEK_API_KEY`. The repository intentionally does not
contain a real key. `https://api.deepseek.com` is DeepSeek's official OpenAI-compatible base URL.

## Native NP-hard production entrypoint

`scripts/prove_np_hard.py` proves NP-hardness only. It does not claim NP membership or
NP-completeness, and it does not claim that every problem in the library is NP-hard. The input must
be an existing Lean `PresentedProblem`, a registered stable ID/alias, or a bare
`LawfulEncodedType` that Lean can resolve to exactly one existing lawful presentation.

```bash
python3 scripts/prove_np_hard.py \
  --problem ComplexityReduction.Problems.Karp21.GraphAtoms.vertexCoverStructuredProblem
```

The shortest command auto-discovers the owning public module. An explicit
`--module` remains available as an import-closure override and is checked against the requested
declaration. Production precedence is explicit CLI option, then process environment/`.env`, then
the accepted defaults: `deepseek-v4-flash`, low reasoning, 300 seconds, 16000 output tokens, zero
SDK retries, and temperature zero. The model-call budget is derived from the typed DAG as
`gap nodes × per-node attempt budget`; an undersized explicit budget fails closed.

The CLI reports the requested term, resolved encoding, canonical `PresentedProblem`, and the
Lean-checked normalization certificate. Existing routes make zero model calls. Model authoring is
allowed only after deterministic analysis produces a typed gap DAG, and every accepted artifact is
checked at the exact canonical endpoint by Lean, independent replay, and the standard-axiom gate.
It also writes a redacted `preflight.json` and emits one of the stable machine statuses
`VERIFIED`, `BLOCKED_NOT_TARGET`, `BLOCKED_MISSING_PREREQUISITE`, `FAILED_MODEL`, `FAILED_LEAN`,
or `INPUT_ERROR`.

Formal qualification can explicitly exercise authoring on a public `ComplexityReduction.*`
problem even when a deterministic route already exists. This does not change the default fast
path: without the qualification-only flag, existing routes still make zero model calls.

```bash
python3 scripts/prove_np_hard.py \
  --problem ComplexityReduction.Problems.Karp21.GraphAtoms.vertexCoverStructuredProblem \
  --qualification-authoring
```

`--qualification-authoring` implies the accepted formal profile and `model-required`; it is
rejected outside formal qualification and records the override in the redacted preflight.

Stable input-boundary failures include:

- `missing_lawful_presentation`: a bare encoding has no existing presentation in its import closure;
- `ambiguous_lawful_presentation`: multiple non-definitionally-equal presentations exist;
- `input_problem_not_found`: the declaration is absent or escapes the supplied module closure;
- `candidate_dependency_stale`: a source/toolchain/manifest change invalidated the normalization identity;
- `wrong_direction_only`: the library contains only a reverse reduction, which cannot prove NP-hardness.

Generate the auditable public-library inventory and run the answer-free H-E production-input suite
with:

```bash
python3 scripts/run_np_hard_h_e_inventory.py

DEEPSEEK_REASONING_EFFORT=low \
python3 scripts/run_np_hard_h_e_heldout.py \
  --output-root tmp/np-hard-h-e-heldout \
  --model deepseek-v4-flash \
  --model-max-tokens 16000
```

Qualify every existing-route public identity (one production proof per canonical identity, with
separate alias normalization checks) using:

```bash
python3 scripts/run_np_hard_h_h_existing_routes.py \
  --output-root tmp/np-hard-h-h-existing-routes
```

The qualification report is identity-level and requires all 22 current forward-route identities,
zero model calls, exact endpoint equality, shortest forward route agreement, independent replay,
and the standard-axiom audit. Its answer-free organic held-out subset contains 12 public inputs,
five families, and route lengths zero through five.

Run the formal three-round release stability gate with four isolated cases in parallel inside each
round:

```bash
python3 scripts/run_np_hard_release_stability.py \
  --output-root tmp/np-hard-release-stability \
  --jobs 4
```

The three rounds remain sequential so they are independent stability repetitions. Each round runs
its 12 cases with bounded case-level parallelism, preserves one fresh output directory per case,
and records configured jobs, observed maximum concurrency, and final active-task count in the
round and aggregate reports. Formal qualification requires at least two case workers; `--jobs 1`
is available only for debugging and cannot produce a passing formal aggregate.

The legacy resolver and model-authoring lanes remain deterministic about route selection: their
DeepSeek use starts only after Lean reports an exact typed gap and fixes a single editable proof
fence. The newer input-grounding research lane is intentionally separate. There, DeepSeek receives
only bounded Lean observations, catalog architecture, and on-demand query results; it chooses the
problem match, directed route, and complete `CertifiedPath` term. The Agent checks retrieval
provenance and endpoint direction without choosing a hidden route, and Lean runs once after all
model tasks finish.

The existing `complexity_reduction_ir_*` attributes remain a compatibility ABI because they are
already used across the production registry. New runtime modules, commands, and tactics use the
canonical `ComplexityReduction.Agent.Hardness` names; attributes still grant no capability without
type-directed registry validation.

```bash
python3 scripts/run_hardness_agent.py \
  --module Benchmark.Hardness.Inputs.Smoke.ExistingRoute \
  --source Benchmark.Hardness.Inputs.Smoke.ExistingRoute.source \
  --objective reduce-to-known-np \
  --planner deterministic
```

Run the complete deterministic Phase 6 inventory with:

```bash
python3 scripts/run_hardness_benchmark.py --agent-phase 6 --planner deterministic
```

Run the active matched flat-vs-IR feasibility slice with:

```bash
python3 scripts/run_hardness_benchmark.py \
  --suite ir-feasibility \
  --planner deterministic
```

Run the Phase 6 membership and completeness suites independently with:

```bash
python3 scripts/run_hardness_benchmark.py \
  --suite membership \
  --agent-phase 6 \
  --planner deterministic \
  --lean-timeout 1200

python3 scripts/run_hardness_benchmark.py \
  --suite completeness \
  --agent-phase 6 \
  --planner deterministic \
  --lean-timeout 600
```

Before the IR-feasibility slice was added, the Phase 6 baseline contained 32 runnable cases. The
active manifest now contains 44 Phase 6 cases and 45 Phase 7 cases. The IR-feasibility suite now
contains 6 logical matched pairs / 12 executions across Graph, Clause/CSP, and Incidence families;
their shared route audit and kernel regression pass, while the full 12-case per-process Agent run
is still pending. The dedicated membership suite passed 3/3 and the dedicated completeness suite
passed 5/5, with zero model calls. These are distinct runs; no combined full-inventory result is
claimed without executing it.

Phase 7 adds a separate hidden-gold semantic-proof benchmark, a one-region JSON patch protocol,
bounded compile/diagnostics retries, and an API-only smoke command. On 2026-07-29, a genuine
`deepseek-v4-flash` `model-required` run reached final `VERIFIED`: three HTTP 200 model calls used
12,297 total tokens, the third fenced proof body compiled, the complete seven-stage reduction
bundle passed fresh registry resolution and the standard-axiom gate, and an independent replay
produced artifact SHA-256
`17d33d96b0cc5befb319d40e0f57fc2d5940dd56ac6db1c23f7787ea19c468bb`. The full Python regression
then passed 106/106. A separate genuine `model-auto` run also reached `VERIFIED` without a
deterministic fallback: its fourth and final bounded call closed the semantic proof, using 15,942
total tokens and producing the same final artifact hash. Phase 7 remains in progress until at
least two additional comparable isolated runs per policy and the official trial aggregate
complete the required three-repeat stability evidence.

These results are reported in the `model_synthesis` lane and are never mixed with existing-route
or deterministic-fixture rates:

```bash
python3 scripts/run_deepseek_smoke.py --env-file .env

python3 scripts/run_hardness_benchmark.py \
  --suite model-authoring \
  --agent-phase 7 \
  --planner deterministic \
  --authoring model-required \
  --env-file .env

python3 scripts/run_hardness_model_trials.py \
  --repetitions 3 \
  --env-file .env
```

The trial runner executes `model-auto` and `model-required` in separate output trees and writes a
stability summary without copying raw model text or secrets into the aggregate report.

## Fixed-target input grounding

The active 24-case suite tests six logical source problems in direct, `abbrev`, and reducible-`def`
forms, plus six negative inputs. It does not place a source node, family label, matched problem, or
gold route in the model prompt. Build the fingerprint-bound catalogs and observations first, then
run the offline protocol regression or the genuine DeepSeek benchmark:

```bash
python3 scripts/run_input_grounding_offline_benchmark.py \
  --output-root .reduction-agent/input-grounding-offline-fresh

python3 scripts/run_deepseek_input_grounding_benchmark.py \
  --output-root .reduction-agent/deepseek-input-grounding-fresh \
  --canonical-report Benchmark/Hardness/INPUT_GROUNDING_REPORT.json \
  --run-label input-grounding-full
```

Every output root must be empty. `--resume-report` is optional and replays prior raw responses only
when the current prompt hashes, observation IDs, catalog IDs, and protocol outcomes all still
match; stability runs omit it. Each transcript preserves raw prompts and responses, HTTP status and
attempt counts, token/cache usage, query results, the model's original Lean term, and the final
HardnessPlan. API keys are never written.

On 2026-07-30, the post-fix baseline and three fresh `deepseek-v4-flash` stability runs all passed:
72/72 positive executions passed the protocol and final Lean check, 24/24 negatives were correctly
rejected, 251/251 API turns succeeded, and each run used exactly one final Lean process. No model
term was rewritten, no hidden route fixture or family-specific Agent rule was used, and no answer
field leaked into a prompt. See
`Benchmark/Hardness/INPUT_GROUNDING_STABILITY_SUMMARY.json` and the four reports it references.

## Open-target selection

The Stage G contract is the separate seven-case suite
`Benchmark/Hardness/Suites/open_target.json`. It reuses the six direct input-grounding sources but
removes the fixed target: each request exposes only the Native hardness requirement, allowed Lean
certificate classes, direction, and route/dependency limits. The suite contains three positive and
four negative cases and is checked by `agent.hardness.open_target.validate_open_target_suite`.
Neither its prompt contract nor its coverage metadata contains a preferred target, acceptable-target
list, or gold route; any policy-compliant reachable target whose final Lean artifact passes is valid.

## Predicate input grounding

Stage H extends the open-target lane from a bundled `PresentedProblem` declaration to a closed,
monomorphic unary predicate `α → Prop`. Lean exports the predicate/domain nodes and nonce-bound
`isDefEq` matches against existing `PresentedProblem.accepts` projections. Python may select only a
Lean-confirmed unique codec group; carrier equality, name similarity, or route quality cannot choose
a presentation. The resulting `CertifiedPath` starts at the selected existing `PresentedProblem`,
while the final batch artifact separately audits the real predicate-to-`accepts` grounding.

Build fresh snapshots, run the prompt-only full suite, and run the genuine DeepSeek suite with:

```bash
python3 scripts/build_predicate_input_snapshots.py \
  --output-root .reduction-agent/stage-h-snapshots-fresh

python3 scripts/run_predicate_input_offline_benchmark.py \
  --snapshots-root .reduction-agent/stage-h-snapshots-fresh \
  --output-root .reduction-agent/predicate-input-offline-fresh

python3 scripts/run_deepseek_predicate_input_benchmark.py \
  --snapshots-root .reduction-agent/stage-h-snapshots-fresh \
  --output-root .reduction-agent/deepseek-predicate-input-fresh \
  --canonical-report Benchmark/Hardness/PREDICATE_INPUT_REPORT.json \
  --run-label stage-h-full-real-deepseek
```

On 2026-07-31, the fresh eight-case `deepseek-v4-flash` run reached `VERIFIED`: all 8/8 protocol
outcomes matched Expected, all 4/4 positive paths and predicate groundings passed one combined Lean
process, and all 4/4 negatives returned their required stable blocker. Seven model-eligible cases
used 22 model turns and 23 real HTTP attempts; the closed `Prop` case made zero model calls. The run
used no resume/replay, rewrote no model term, leaked no prompt oracle, introduced no family-specific
Python routing rule, and audited four grounding theorems through one `assert_standard_axioms` gate.
See `Benchmark/Hardness/PREDICATE_INPUT_REPORT.json`.

## Long-route frontier efficiency

Stage I adds the independent eight-case long-route workload for Tagged 3SAT and Set Covering, with
four positive PresentedProblem/predicate cases and four target, direction, and presentation
blockers. Stage J keeps that public workload but uses new case IDs and a separate contract to test
bounded frontier navigation. `frontier_guidance` contains only already retrieved endpoint node IDs,
public outgoing counts, and source-only query templates; it contains no declaration, target,
evidence, or route selector. Auditable `finish_now` and `stop_now` hints do not relax the existing
finish/stop validation.

Build fresh snapshots, run the prompt-only full suite, and run the genuine DeepSeek suite with:

```bash
python3 scripts/build_frontier_efficiency_snapshots.py \
  --output-root .reduction-agent/frontier-efficiency-snapshots-fresh

python3 scripts/run_frontier_efficiency_offline_benchmark.py \
  --snapshots-root .reduction-agent/frontier-efficiency-snapshots-fresh \
  --output-root .reduction-agent/frontier-efficiency-offline-fresh \
  --report Benchmark/Hardness/FRONTIER_EFFICIENCY_OFFLINE_REPORT.json

python3 scripts/run_deepseek_frontier_efficiency_benchmark.py \
  --snapshots-root .reduction-agent/frontier-efficiency-snapshots-fresh \
  --output-root .reduction-agent/deepseek-frontier-efficiency-fresh \
  --canonical-report Benchmark/Hardness/FRONTIER_EFFICIENCY_REPORT.json \
  --model-max-tokens 32768 \
  --model-timeout 900 \
  --lean-timeout 1200
```

On 2026-08-02, the fresh `deepseek-v4-flash` run reached `VERIFIED`: all 8/8 protocol outcomes
matched Expected, all 4/4 positive paths passed one combined Lean process, and all 4/4 negatives
returned their required stable blocker. Against the same-fingerprint Stage I prompt-compaction
baseline, model turns fell from 66 to 48, reduction searches from 27 to 16, protocol feedback from
11 to 8, and total tokens from 789348 to 485829. The run used no resume/replay, repeated no
reduction query, ignored no terminal guidance, rewrote no model term, and retained zero
family-specific Python or system-prompt routing rules. See
`Benchmark/Hardness/FRONTIER_EFFICIENCY_REPORT.json`.

### Four-case parallel execution

The shared Stage I/Frontier DeepSeek runner accepts `--jobs 1..4`; its default remains 1 for
backward compatibility. Parallelism is between independent cases only. Model rounds inside one
case remain sequential, each worker owns its DeepSeek client and artifact paths, and the main
thread restores suite order before building the combined artifact. Lean starts only after every
case task has finished and still runs exactly once.

Run the Stage K four-way contract with:

```bash
python3 scripts/run_deepseek_frontier_efficiency_parallel_benchmark.py \
  --snapshots-root .reduction-agent/frontier-efficiency-snapshots-fresh \
  --output-root .reduction-agent/deepseek-frontier-efficiency-parallel-fresh \
  --canonical-report Benchmark/Hardness/FRONTIER_EFFICIENCY_PARALLEL_REPORT.json \
  --model-max-tokens 32768 \
  --model-timeout 900 \
  --lean-timeout 1200
```

On 2026-08-02, a fresh eight-case `deepseek-v4-flash` run reached `VERIFIED`: all 8/8 outcomes
matched Expected, all 4/4 positives passed the one combined Lean process, and all 4/4 negatives
returned their required blocker. The audit recorded eight tasks started/completed, zero active at
the final gate, and an observed maximum concurrency of 4. It used 46 real HTTP requests and
490334 tokens. Against the same-fingerprint Stage J sequential run, wall time fell from 1639.614
seconds to 760.583 seconds (-53.61%, 2.16x speedup). Tokens changed from 485829 to 490334 (+0.93%),
so this stage claims latency reduction, not token reduction. See
`Benchmark/Hardness/FRONTIER_EFFICIENCY_PARALLEL_REPORT.json`.
