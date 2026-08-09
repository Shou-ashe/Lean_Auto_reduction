# Lean Auto Reduction Benchmark

> 关于「一次归约 LLM 需要输出哪些文件、含哪些内容（语义等价/包含、多项式时间证明、
> 路径组合）」的完整输出契约，见 [`CERTIFICATE_OUTPUT_CONTRACT.md`](CERTIFICATE_OUTPUT_CONTRACT.md)。

`Benchmark/MANIFEST.yaml` is the benchmark entry point. It lists one
problem-only decision-problem sample file per benchmark sample:

```yaml
usable_sample_files:
  - Samples/L0/clique.yaml
  - Samples/L2/numeric_subset_tradeoff_route.yaml
```

Each `Benchmark/Samples/L0|L1|L2|L3|L4|L5|L6|L7|L8|L9|L10|L11|L12|L13|L14|L15/*.yaml`
file contains exactly one sample.

Public Lean proposition samples give:

- `id`
- `name`
- `input_language`
- `problem_family`
- `problem_statement`
- `certificate_contract: lean_proposition`
- `lean_preamble`
- `lean_target_name`
- `lean_target_type`
- optional difficulty metadata for report grouping

The public Lean proposition fields state the formal decision problem and target
complexity proposition. They are not a gold proof and do not prescribe route
targets, intermediate declarations, membership terms, or a truth label.
Opencode must choose the proof route and close the target theorem itself.

Legacy hidden-target samples still use natural-language fields plus optional
`route_target_policy`, but the current manifest uses the public Lean proposition
channel for every active level L0-L15.

When `--opencode-usable-samples` is enabled, the runner creates a run-local
private report directory under `.reduction-agent/runs/<run-id>/`. By default it
also creates an isolated public opencode workspace under
`.reduction-agent/opencode_public_workspaces/<run-id>/` and runs opencode from
that public copy rather than from the real repository.

The public workspace excludes benchmark oracle data and run-private artifacts:

- `Benchmark/HiddenTargets`
- `Benchmark/GoldProofs`
- `.reduction-agent`
- `.lake`
- opencode cache/data directories

The public copy keeps the local `Reference/ComplexityReduction` source tree and
rewrites Lake dependency paths to absolute paths. If the real repository already
has built `ComplexityReduction` oleans, the public workspace copies that trusted
library's Lean artifacts into its own `.lake/build/lib/lean/` directory,
including both the `ComplexityReduction/` submodule artifact tree and the
top-level `ComplexityReduction.olean/.ilean` root module artifacts. The copied
trusted artifact snapshot is read-only, so parallel opencode jobs sharing the
same public workspace cannot delete or rewrite each other's copied Lean
dependencies during scratch `lake` checks. The public workspace does not symlink
the real build cache and does not copy `Benchmark` build artifacts, so hidden
targets and gold proofs are not exposed through `.lake`.

Use `--opencode-public-root` to choose the base directory for public workspaces.
Use `--disable-opencode-oracle-isolation` only for debugging regressions in
opencode workspace permissions.

For legacy hidden-target samples, opencode writes only:

- `ProblemCertificate.lean`
- `NPMembershipCertificate.lean`

For public Lean proposition samples, opencode writes only:

- `ProofCertificate.lean`

under the public run's `usable_sample_certificates/<sample>/` directory. After
each opencode call, the runner synchronizes only those certificate files back to
the private report directory and performs Lean validation from the real
repository. Hidden targets, gold proofs, generated validators, and private
report paths are not included in prompts.

Gold proofs are optional per-sample sanity checks stored under:

```text
Benchmark/GoldProofs/Lx/<sample-id>.lean
```

For legacy hidden-target samples, each gold file imports the corresponding
hidden target and defines:

```lean
namespace BenchmarkGoldProof

noncomputable section

def goldCertificate : BenchmarkHiddenSample.sampleClaim := ...

end

end BenchmarkGoldProof
```

Passing `--require-gold-proofs` requires every evaluated sample to have a gold
file that compiles before the sample can count as verified. This checks that the
benchmark target itself is closed over `mathlib + ComplexityReduction`; it does
not reveal the proof to opencode. For public Lean proposition samples, the gold
file is a standalone Lean file that explicitly states and proves the same public
target proposition.

To run only selected benchmark levels, use `--levels` or the equivalent
`--benchmark-levels` flag. The flag accepts comma-separated values and may be
repeated:

```bash
python3 scripts/run_benchmark.py --levels L4,L5 ...
python3 scripts/run_benchmark.py --levels L0 --levels L3 --levels L8 ...
python3 scripts/run_benchmark.py --levels L9 ...
python3 scripts/run_benchmark.py --levels L10 ...
python3 scripts/run_benchmark.py --levels L11 ...
python3 scripts/run_benchmark.py --levels L12 ...
python3 scripts/run_benchmark.py --levels L13 ...
python3 scripts/run_benchmark.py --levels L14 ...
python3 scripts/run_benchmark.py --levels L15 ...
```

Passing bare digits is also accepted (`--levels 4,14` means `L4,L14`). Without
this flag, the runner uses every level present in the manifest.

The current manifest has sixteen active layers:

- `L0`: public Lean proposition samples for standard named decision problems.
- `L1`: public Lean proposition samples for structured/binary-structured
  encoded variants. These now require checked-suffix TM verifier evidence plus
  direct `TMInNP` evidence, rather than a generic `InNPEnc` wrapper.
- `L2`: public Lean proposition samples requiring a fixed one-hop
  `KarpReductionM` route certificate, route-target NP membership, and final
  source membership.
- `L3`: public Lean proposition samples for interface variants of local
  decision problems. These expose a public `referenceProblem` and require an
  existential `ProblemEquivM` adapter, the induced reducibility evidence,
  reference membership, and final membership.
- `L4`: public Lean proposition samples requiring two fixed route targets, both
  edge certificates, a composed `PolyReducibleM`, target membership, and final
  source membership. The active set keeps cross-family representatives rather
  than every same-shape two-hop route.
- `L5`: public Lean proposition samples for ignored-field and interface-wrapper
  encodings. These require a fixed normalization target, a `ProblemEquivM`
  bridge, a route from the normalized problem, a lifted route, and final
  membership. The active set keeps one hard representative per bridge shape
  rather than horizontally enumerating equivalent projection examples.
- `L6`: public Lean proposition samples for textbook-style source problems and
  wrapped interfaces. These require a fixed textbook target, a direct adapter
  `KarpReductionM`, a reducibility wrapper, target membership, and final source
  membership. Duplicate same-shape textbook adapters are pruned.
- `L7`: public Lean proposition samples for Schaefer hard-side CSP
  propositions. These now require an explicit `HardRelationCertificate` plus
  the NP-completeness proposition.
- `L8`: public Lean proposition local-adapter authoring samples. These require
  a semantic adapter proof, a costed adapter reduction, a reducibility wrapper,
  target NP-membership evidence, and the final NP-membership proof.
- `L9`: public Lean proposition open-synthesis samples. These require the
  candidate to normalize a public interface, choose route targets, compose two
  local Karp reduction edges, and close source membership without the benchmark
  prescribing the intermediate or final target.
- `L10`: public Lean proposition three-hop open-synthesis samples. These extend
  L9 by requiring a public normalization bridge, three local Karp reduction
  edges, a composed reducibility certificate, target membership, and final source
  membership while leaving all route targets open.
- `L11`: public Lean proposition composed-gadget samples. These require a
  normalization bridge from a wrapped CSP source, one public source-CSP-to-3SAT
  Karp reduction, one public 3SAT-to-target-CSP gadget reduction, composed
  reducibility, target membership, and final source membership. The 3SAT pivot
  and CSP target are fixed in the public target type so candidates must compose
  existing gadget reductions instead of choosing an unrelated graph route.
- `L12`: public Lean proposition mixed gadget-route samples. These require a
  normalization bridge from a wrapped CSP source, a fixed source-CSP-to-3SAT
  gadget edge, a fixed final graph or numeric target, then an intermediate
  non-CSP public Karp route target chosen from descriptors. This layer checks
  whether candidates can splice CSP gadget synthesis into the ordinary Karp21
  route graph.
- `L13`: public Lean proposition stacked-bridge mixed-route samples. These
  require two explicit `ProblemEquivM` normalization bridges before the same
  CSP-gadget-to-Karp21 route tail shape used by L12. This layer checks whether
  candidates can compose adapter/bridge evidence before choosing and packaging
  the public route.
- `L14`: public Lean proposition forked mixed-route samples. These require one
  normalization bridge and one CSP-to-3SAT gadget edge, then two independent
  public Karp21 route tails from the shared 3SAT pivot to graph and numeric
  targets. This layer checks whether candidates can assemble multiple route
  products in one certificate rather than solving only a single chain.
- `L15`: public Lean proposition stacked-bridge forked mixed-route samples.
  These compose two public normalization bridges before the same dual-tail
  route product shape used by L14, checking whether bridge composition and
  multi-target route assembly still work together.

The former L9 public-proposition smoke layer was removed in
`opencode_decision_problem_v0.12.0` because it duplicated L0/L7/L8 coverage.
`opencode_decision_problem_v0.13.1` carries L9 as an open route-synthesis
challenge layer. `opencode_decision_problem_v0.14.0` adds L10 as a three-hop
open route-composition challenge layer, and `opencode_decision_problem_v0.14.1`
adds a source audit so identity-route shortcuts do not count as completed L10
certificates. Since `opencode_decision_problem_v0.14.2`, that audit is driven
by the public target contract rather than by a level name: the required public
route theorem mention count is the number of public route `KarpReductionM`
witnesses in the sample's `lean_target_type`; local adapter reduction witnesses
are not counted as public route edges.
`opencode_decision_problem_v0.15.0` adds L11 as a composed CSP gadget synthesis
layer over the same non-invasive descriptor, retrieval, and audit route.
`opencode_decision_problem_v0.15.1` expands L11 to eight samples covering the
current 4x2 source-CSP/target-CSP gadget matrix.
`opencode_decision_problem_v0.16.0` adds L12 mixed gadget-route synthesis,
where the candidate must normalize a wrapped CSP source, use the CSP-to-3SAT
gadget, then continue through ordinary Karp21 route descriptors.
`opencode_decision_problem_v0.17.0` adds L13 stacked-bridge mixed-route
synthesis, where the candidate must compose two normalization bridges before
the CSP gadget and ordinary Karp21 route tail.
`opencode_decision_problem_v0.18.0` adds L14 forked mixed-route synthesis,
where the candidate must construct two independent route tails from one shared
3SAT pivot in the same certificate.
`opencode_decision_problem_v0.19.0` adds L15 stacked-bridge forked mixed-route
synthesis and expands L14 with alternate graph-tail coverage through
Chromatic Number and Clique Cover.

The 2026-06-07 hard extension keeps the same runner structure but adds harder
L4/L5/L6/L7/L8 samples:

- L4 hard samples require public proposition two-hop routes such as
  CNF Satisfiability -> 3SAT -> 0-1 Integer Programming and
  Vertex Cover -> Feedback Node Set -> Feedback Arc Set. The public target
  itself checks both route edges and the composed reducibility certificate.
- L5 hard samples require non-identity encoding bridges before the route:
  right projection, nested-left projection, nested-right projection, and
  sandwiched projection over ignored audit fields. The manifest keeps one hard
  representative for each shape so this layer tests bridge authoring without
  re-running equivalent horizontal variants.
- L6 hard samples combine ignored-field or nested-wrapper interfaces with
  textbook-adapter obligations. They require a single costed Karp reduction from
  the public interface problem to the textbook target, so opencode must compose
  generic projection maps with local textbook reductions rather than only
  calling the target membership theorem.
- L7 samples exercise the local Schaefer hard-side API through public
  `HardRelationCertificate` obligations and proposition-level validation.
- L8 samples force candidate-local adapter proof authoring for ignored-field
  and nested-wrapper interfaces before using local target membership evidence.
- L9 samples combine bridge authoring and open multi-hop route synthesis. The
  starter set covers tagged 3-SAT, tagged Clique, nested Vertex Cover, and
  sandwiched Set Covering interfaces before the candidate chooses a two-hop
  route through public Karp21 targets.
- L10 samples increase the open-route depth to three Karp edges and cover
  CNF-to-graph, SAT-to-set, graph-to-set, set-to-numeric, and numeric-to-graph
  route families.
- L11 samples force candidates to synthesize a new CSP gadget route by composing
  an existing source-CSP-to-3SAT reduction with an existing 3SAT-to-target-CSP
  hard-side gadget reduction. The expanded L11 matrix covers one-in-three,
  NAE-3SAT, 3SAT-like, and Horn-3 sources against one-in-three and NAE-3SAT
  targets.
- L12 samples force candidates to splice CSP gadget routes into ordinary
  Karp21 graph or numeric tails, such as CSP -> 3SAT -> Clique -> Vertex Cover
  and CSP -> 3SAT -> 0-1 Integer Programming -> Knapsack.
- L13 samples force candidates to compose two representation bridges before
  the same mixed gadget-route tail, covering stacked wrapper normalization.
- L14 samples force candidates to build two independent Karp21 route tails from
  the same normalized CSP-to-3SAT pivot, covering forked route assembly.
- L15 samples force candidates to compose stacked representation bridges before
  assembling those same independent graph and numeric route products.
- Since `opencode_decision_problem_v0.13.1`, all active levels L0-L15 use the
  public Lean proposition channel. The older two-file legacy path remains only
  for archived reports and manually constructed compatibility samples.

## Example

```yaml
schema_version: opencode_decision_problem_sample_file_v1
id: clique
name: clique_problem
input_language: clique
problem_family: graph
problem_statement: "Given an undirected graph G and an integer k, decide whether G contains a clique of size at least k."
difficulty: easy
difficulty_tags: [graph, subset_witness, cardinality_bound]
```

The runner gives opencode the problem statement in two stages. In the first
stage, opencode writes:

- `ProblemCertificate.lean`

`ProblemCertificate.lean` must define top-level `problem`. The runner then
builds a hidden problem-binding validator and checks:

```lean
#check (show problem = BenchmarkHiddenSample.sampleProblem from rfl)
```

When this check passes, the runner stores a run-local snapshot of the validated
`ProblemCertificate.lean`. Later membership validation uses that snapshot as the
fixed problem binding. If opencode later edits the artifact copy of
`ProblemCertificate.lean`, the report records that mutation as a diagnostic
instead of treating it as a proof failure.

Only if that Lean check passes does the runner call opencode a second time. In
the second stage, opencode uses the already validated `problem` declaration and
writes:

- `NPMembershipCertificate.lean`

For the default `certificate_contract: np_membership` mode,
`NPMembershipCertificate.lean` must define top-level
`npMembershipCertificate`. The runner keeps this prompt as a minimal certificate
ABI. It does not add sample-specific theorem names, route answers, local problem
symbols, or a growing list of corrective Lean style hints. Lean authoring
mistakes such as unavailable imports, duplicate declarations, namespace-wrapped
required names, or namespace/type-resolution mismatches are reported as
diagnostics after the candidate is validated.

For future proposition-level samples, the sample file may set:

```yaml
certificate_contract: proposition
```

In that mode `NPMembershipCertificate.lean` may define:

```lean
def propositionCertificate : BenchmarkHiddenSample.sampleClaim := ...
```

or use the legacy `npMembershipCertificate` name. The hidden validator checks
`propositionCertificate` first when present. This ABI is for samples whose
hidden `sampleClaim` is an arbitrary complexity proposition, not necessarily a
plain `InNPEnc` membership claim.

For the public Lean proposition channel, the sample file sets:

```yaml
certificate_contract: lean_proposition
```

and provides:

```yaml
lean_preamble: |
  import ComplexityReduction

  noncomputable section

  abbrev problem : ComplexityReduction.EncodedDecisionProblem := ...
lean_target_name: targetClaim
lean_target_type: |
  ComplexityReduction.InNPEnc
    ComplexityReduction.CostedPolyTimeModel
    problem
```

In this mode there is no hidden problem-binding target. Opencode receives the
public Lean preamble and the exact theorem type, then writes
`ProofCertificate.lean`. The proof file may define any helper declarations and
choose any route through the declaration catalog. The validator concatenates the
public preamble with the proof file and checks:

```lean
#check (targetClaim : <public target type>)
```

Since `opencode_decision_problem_v0.13.1`, this is the main benchmark path for
all active levels; in `opencode_decision_problem_v0.19.0` that covers L0-L15.
The older two-file ABI described below is retained for
archived reports and manual compatibility samples only.

For final validation, the runner inlines the validated `ProblemCertificate.lean`
before `NPMembershipCertificate.lean`. The top-level `problem` is the primary
ABI. The generated validator also provides a generic companion-file alias:

```lean
namespace ProblemCertificate
abbrev problem : ComplexityReduction.EncodedDecisionProblem := _root_.problem
end ProblemCertificate
```

This lets a membership certificate refer either to `problem` directly or to
`ProblemCertificate.problem`, without adding a sample-specific template.

For public-proposition `L2` route-composition samples, opencode still writes
only `ProofCertificate.lean`. The public target has the shape:

```lean
∃ routeTarget : ComplexityReduction.EncodedDecisionProblem,
  routeTarget = <public route target> ∧
    ∃ reductionCertificate :
      ComplexityReduction.KarpReductionM
        ComplexityReduction.CostedPolyTimeModel problem routeTarget,
      ComplexityReduction.InNPEnc
        ComplexityReduction.CostedPolyTimeModel routeTarget ∧
        ComplexityReduction.InNPEnc
          ComplexityReduction.CostedPolyTimeModel problem
```

The sample does not provide theorem names or proof terms. The target route is
part of the Lean proposition being proved, so Lean validation rejects direct
membership proofs that omit the route certificate.

For current public-proposition `L3` interface-adapter samples, opencode still
writes only `ProofCertificate.lean`. The public target has the shape:

```lean
∃ e : ComplexityReduction.ProblemEquivM
    ComplexityReduction.CostedPolyTimeModel problem referenceProblem,
  ∃ h : ComplexityReduction.PolyReducibleM
      ComplexityReduction.CostedPolyTimeModel problem referenceProblem,
    h = ComplexityReduction.ProblemEquivM.toReducible e ∧
      ComplexityReduction.InNPEnc
        ComplexityReduction.CostedPolyTimeModel referenceProblem ∧
        ComplexityReduction.InNPEnc
          ComplexityReduction.CostedPolyTimeModel problem
```

This layer is intended to expose failures that pure theorem lookup cannot:
opencode has to write the small interface proof, unfold or repair reference
definitions as needed, use the equivalence-induced reduction, and then call
the local membership theorem.

For public-proposition `L4` multi-hop route samples, opencode writes only
`ProofCertificate.lean`. The public target has the shape:

```lean
∃ routeTarget1 : ComplexityReduction.EncodedDecisionProblem,
  routeTarget1 = <public first route target> ∧
    ∃ routeTarget2 : ComplexityReduction.EncodedDecisionProblem,
      routeTarget2 = <public second route target> ∧
        ∃ reductionStep1 :
          ComplexityReduction.KarpReductionM
            ComplexityReduction.CostedPolyTimeModel problem routeTarget1,
          ∃ reductionStep2 :
            ComplexityReduction.KarpReductionM
              ComplexityReduction.CostedPolyTimeModel routeTarget1 routeTarget2,
            ∃ composedReduction :
              ComplexityReduction.PolyReducibleM
                ComplexityReduction.CostedPolyTimeModel problem routeTarget2,
              ComplexityReduction.InNPEnc
                ComplexityReduction.CostedPolyTimeModel routeTarget2 ∧
                ComplexityReduction.InNPEnc
                  ComplexityReduction.CostedPolyTimeModel problem
```

For public-proposition `L5` encoding-bridge samples, opencode writes only
`ProofCertificate.lean`. The public target has the shape:

```lean
∃ normalizedProblem : ComplexityReduction.EncodedDecisionProblem,
  normalizedProblem = <public normalized problem> ∧
    ∃ encodingBridgeCertificate :
      ComplexityReduction.ProblemEquivM
        ComplexityReduction.CostedPolyTimeModel problem normalizedProblem,
      ∃ normalizedRouteTarget : ComplexityReduction.EncodedDecisionProblem,
        normalizedRouteTarget = <public normalized route target> ∧
          ∃ normalizedReductionCertificate :
            ComplexityReduction.KarpReductionM
              ComplexityReduction.CostedPolyTimeModel
              normalizedProblem normalizedRouteTarget,
            ∃ liftedReductionCertificate :
              ComplexityReduction.PolyReducibleM
                ComplexityReduction.CostedPolyTimeModel problem normalizedRouteTarget,
              ComplexityReduction.InNPEnc
                ComplexityReduction.CostedPolyTimeModel normalizedRouteTarget ∧
                ComplexityReduction.InNPEnc
                  ComplexityReduction.CostedPolyTimeModel problem
```

For public-proposition `L6` textbook-adapter samples, opencode writes only
`ProofCertificate.lean`. The public target has the shape:

```lean
∃ textbookTarget : ComplexityReduction.EncodedDecisionProblem,
  textbookTarget = <public textbook target> ∧
    ∃ textbookReductionCertificate :
      ComplexityReduction.KarpReductionM
        ComplexityReduction.CostedPolyTimeModel problem textbookTarget,
      ∃ textbookRouteCertificate :
        ComplexityReduction.PolyReducibleM
          ComplexityReduction.CostedPolyTimeModel problem textbookTarget,
        ComplexityReduction.InNPEnc
          ComplexityReduction.CostedPolyTimeModel textbookTarget ∧
          ComplexityReduction.InNPEnc
            ComplexityReduction.CostedPolyTimeModel problem
```

For public-proposition `L7` Schaefer hard-side samples, opencode writes only
`ProofCertificate.lean`. The public target has the shape:

```lean
∃ hardCertificate :
  ComplexityReduction.Schaefer.Hardness.HardRelationCertificate cspLanguage,
  ComplexityReduction.NPCompleteEnc
    ComplexityReduction.CostedPolyTimeModel problem
```

For public-proposition `L8` local-adapter samples, opencode writes only
`ProofCertificate.lean`. The public target has the shape:

```lean
(∀ x : problem.Instance.Carrier,
    problem.isYes x ↔ localAdapterTarget.isYes (<public projection of x>)) ∧
  ∃ localAdapterReduction :
    ComplexityReduction.KarpReductionM
      ComplexityReduction.CostedPolyTimeModel
      problem
      localAdapterTarget,
    ComplexityReduction.PolyReducibleM
      ComplexityReduction.CostedPolyTimeModel
      problem
      localAdapterTarget ∧
    ComplexityReduction.InNPEnc
      ComplexityReduction.CostedPolyTimeModel
      localAdapterTarget ∧
    ComplexityReduction.InNPEnc
      ComplexityReduction.CostedPolyTimeModel
      problem
```

For public-proposition `L9` open-synthesis samples, opencode writes only
`ProofCertificate.lean`. The public target has the shape:

```lean
∃ normalizedProblem : ComplexityReduction.EncodedDecisionProblem,
  ∃ routeTarget1 : ComplexityReduction.EncodedDecisionProblem,
    ∃ routeTarget2 : ComplexityReduction.EncodedDecisionProblem,
      ∃ _encodingBridge :
        ComplexityReduction.ProblemEquivM
          ComplexityReduction.CostedPolyTimeModel
          problem
          normalizedProblem,
        ∃ _reductionStep1 :
          ComplexityReduction.KarpReductionM
            ComplexityReduction.CostedPolyTimeModel
            normalizedProblem
            routeTarget1,
          ∃ _reductionStep2 :
            ComplexityReduction.KarpReductionM
              ComplexityReduction.CostedPolyTimeModel
              routeTarget1
              routeTarget2,
            ComplexityReduction.PolyReducibleM
              ComplexityReduction.CostedPolyTimeModel
              problem
              routeTarget2 ∧
            ComplexityReduction.InNPEnc
              ComplexityReduction.CostedPolyTimeModel
              routeTarget2 ∧
            ComplexityReduction.InNPEnc
              ComplexityReduction.CostedPolyTimeModel
              problem
```

The runner treats this as both an encoding-bridge obligation and a multi-hop
route obligation. The target deliberately does not name the chosen Karp21 route
targets; those choices are part of the candidate proof.

For public-proposition `L10` open-synthesis samples, opencode writes only
`ProofCertificate.lean`. The public target has the same normalized-source shape
as L9 but requires three route edges:

```lean
∃ normalizedProblem : ComplexityReduction.EncodedDecisionProblem,
  ∃ routeTarget1 : ComplexityReduction.EncodedDecisionProblem,
    ∃ routeTarget2 : ComplexityReduction.EncodedDecisionProblem,
      ∃ routeTarget3 : ComplexityReduction.EncodedDecisionProblem,
        ∃ _encodingBridge :
          ComplexityReduction.ProblemEquivM
            ComplexityReduction.CostedPolyTimeModel
            problem
            normalizedProblem,
          ∃ _reductionStep1 :
            ComplexityReduction.KarpReductionM
              ComplexityReduction.CostedPolyTimeModel
              normalizedProblem
              routeTarget1,
            ∃ _reductionStep2 :
              ComplexityReduction.KarpReductionM
                ComplexityReduction.CostedPolyTimeModel
                routeTarget1
                routeTarget2,
              ∃ _reductionStep3 :
                ComplexityReduction.KarpReductionM
                  ComplexityReduction.CostedPolyTimeModel
                  routeTarget2
                  routeTarget3,
                ComplexityReduction.PolyReducibleM
                  ComplexityReduction.CostedPolyTimeModel
                  problem
                  routeTarget3 ∧
                ComplexityReduction.InNPEnc
                  ComplexityReduction.CostedPolyTimeModel
                  routeTarget3 ∧
                ComplexityReduction.InNPEnc
                  ComplexityReduction.CostedPolyTimeModel
                  problem
```

The runner classifies L10 as both an encoding-bridge obligation and a multi-hop
route obligation. L10 does not add a runner ABI or sample-specific prompt rule;
the route choices remain part of the candidate proof. Public route-source audit
is target-contract driven: when a public Lean proposition target contains
explicit public route `KarpReductionM` witnesses, the proof file must mention at
least that many public Karp route theorem symbols. Local adapter reduction
witnesses are not counted as public route edges. This rejects candidates that
satisfy the existential target by setting route targets equal and filling route
steps with identity/refl reductions.

For public-proposition `L12` mixed gadget-route samples, opencode also writes
only `ProofCertificate.lean`. The public target fixes the CSP-to-3SAT gadget
pivot and the final graph/numeric target, but leaves the middle Karp21 route
target open:

```lean
∃ normalizedProblem : ComplexityReduction.EncodedDecisionProblem,
  ∃ routeTarget2 : ComplexityReduction.EncodedDecisionProblem,
    ∃ _encodingBridge :
      ComplexityReduction.ProblemEquivM
        ComplexityReduction.CostedPolyTimeModel
        problem
        normalizedProblem,
      ∃ _sourceToSatGadget :
        ComplexityReduction.KarpReductionM
          ComplexityReduction.CostedPolyTimeModel
          normalizedProblem
          ComplexityReduction.SAT.threeSATDecisionProblem,
        ∃ _satToIntermediateRoute :
          ComplexityReduction.KarpReductionM
            ComplexityReduction.CostedPolyTimeModel
            ComplexityReduction.SAT.threeSATDecisionProblem
            routeTarget2,
          ∃ _intermediateToFinalRoute :
            ComplexityReduction.KarpReductionM
              ComplexityReduction.CostedPolyTimeModel
              routeTarget2
              targetProblem,
            ComplexityReduction.PolyReducibleM
              ComplexityReduction.CostedPolyTimeModel
              problem
              targetProblem ∧
            ComplexityReduction.InNPEnc
              ComplexityReduction.CostedPolyTimeModel
              targetProblem ∧
            ComplexityReduction.InNPEnc
              ComplexityReduction.CostedPolyTimeModel
              problem
```

The runner classifies L12 as both an encoding-bridge obligation and a multi-hop
route obligation. L12 adds coverage, not a new ABI: descriptor retrieval,
route-source audit, pass@k, and Lean validation are the same mechanisms used by
L9-L15.

For public-proposition `L13` stacked-bridge mixed-route samples, opencode still
writes only `ProofCertificate.lean`. The public target asks for two
normalization bridges before the normalized source enters the fixed 3SAT pivot
and an open Karp21 tail:

```lean
∃ bridgeProblem : ComplexityReduction.EncodedDecisionProblem,
  ∃ normalizedProblem : ComplexityReduction.EncodedDecisionProblem,
    ∃ routeTarget2 : ComplexityReduction.EncodedDecisionProblem,
      ∃ _outerBridge :
        ComplexityReduction.ProblemEquivM
          ComplexityReduction.CostedPolyTimeModel
          problem
          bridgeProblem,
        ∃ _innerBridge :
          ComplexityReduction.ProblemEquivM
            ComplexityReduction.CostedPolyTimeModel
            bridgeProblem
            normalizedProblem,
          ∃ _sourceToSatGadget :
            ComplexityReduction.KarpReductionM
              ComplexityReduction.CostedPolyTimeModel
              normalizedProblem
              ComplexityReduction.SAT.threeSATDecisionProblem,
            ∃ _satToIntermediateRoute :
              ComplexityReduction.KarpReductionM
                ComplexityReduction.CostedPolyTimeModel
                ComplexityReduction.SAT.threeSATDecisionProblem
                routeTarget2,
              ∃ _intermediateToFinalRoute :
                ComplexityReduction.KarpReductionM
                  ComplexityReduction.CostedPolyTimeModel
                  routeTarget2
                  targetProblem,
                ComplexityReduction.PolyReducibleM
                  ComplexityReduction.CostedPolyTimeModel
                  problem
                  targetProblem ∧
                ComplexityReduction.InNPEnc
                  ComplexityReduction.CostedPolyTimeModel
                  targetProblem ∧
                ComplexityReduction.InNPEnc
                  ComplexityReduction.CostedPolyTimeModel
                  problem
```

The runner classifies L13 as both an encoding-bridge obligation and a multi-hop
route obligation. It uses the same descriptor retrieval, route-source audit,
pass@k, and Lean validation path as L9-L12.

For public-proposition `L14` forked mixed-route samples, opencode still writes
only `ProofCertificate.lean`. The public target asks for one normalization
bridge, one source-CSP-to-3SAT gadget edge, and two independent Karp21 tails:

```lean
∃ normalizedProblem : ComplexityReduction.EncodedDecisionProblem,
  ∃ graphRouteTarget : ComplexityReduction.EncodedDecisionProblem,
    ∃ numericRouteTarget : ComplexityReduction.EncodedDecisionProblem,
      ∃ _encodingBridge :
        ComplexityReduction.ProblemEquivM
          ComplexityReduction.CostedPolyTimeModel
          problem
          normalizedProblem,
        ∃ _sourceToSatGadget :
          ComplexityReduction.KarpReductionM
            ComplexityReduction.CostedPolyTimeModel
            normalizedProblem
            ComplexityReduction.SAT.threeSATDecisionProblem,
          ∃ _satToGraphRoute :
            ComplexityReduction.KarpReductionM
              ComplexityReduction.CostedPolyTimeModel
              ComplexityReduction.SAT.threeSATDecisionProblem
              graphRouteTarget,
            ∃ _graphToFinalRoute :
              ComplexityReduction.KarpReductionM
                ComplexityReduction.CostedPolyTimeModel
                graphRouteTarget
                graphTargetProblem,
              ∃ _satToNumericRoute :
                ComplexityReduction.KarpReductionM
                  ComplexityReduction.CostedPolyTimeModel
                  ComplexityReduction.SAT.threeSATDecisionProblem
                  numericRouteTarget,
                ∃ _numericToFinalRoute :
                  ComplexityReduction.KarpReductionM
                    ComplexityReduction.CostedPolyTimeModel
                    numericRouteTarget
                    numericTargetProblem,
                  ComplexityReduction.PolyReducibleM
                    ComplexityReduction.CostedPolyTimeModel
                    problem
                    graphTargetProblem ∧
                  ComplexityReduction.PolyReducibleM
                    ComplexityReduction.CostedPolyTimeModel
                    problem
                    numericTargetProblem ∧
                  ComplexityReduction.InNPEnc
                    ComplexityReduction.CostedPolyTimeModel
                    graphTargetProblem ∧
                  ComplexityReduction.InNPEnc
                    ComplexityReduction.CostedPolyTimeModel
                    numericTargetProblem ∧
                  ComplexityReduction.InNPEnc
                    ComplexityReduction.CostedPolyTimeModel
                    problem
```

The runner classifies L14 as both an encoding-bridge obligation and a multi-hop
route obligation. Its route-source audit is still inferred from the public
target contract, so the benchmark does not add an L14-specific prompt rule.

For public-proposition `L15` stacked forked-route samples, opencode again writes
only `ProofCertificate.lean`. The public target adds an outer and inner
`ProblemEquivM` bridge before the L14-style fork:

```lean
∃ bridgeProblem : ComplexityReduction.EncodedDecisionProblem,
  ∃ normalizedProblem : ComplexityReduction.EncodedDecisionProblem,
    ∃ graphRouteTarget : ComplexityReduction.EncodedDecisionProblem,
      ∃ numericRouteTarget : ComplexityReduction.EncodedDecisionProblem,
        ∃ _outerBridge :
          ComplexityReduction.ProblemEquivM
            ComplexityReduction.CostedPolyTimeModel
            problem
            bridgeProblem,
          ∃ _innerBridge :
            ComplexityReduction.ProblemEquivM
              ComplexityReduction.CostedPolyTimeModel
              bridgeProblem
              normalizedProblem,
            ∃ _sourceToSatGadget :
              ComplexityReduction.KarpReductionM
                ComplexityReduction.CostedPolyTimeModel
                normalizedProblem
                ComplexityReduction.SAT.threeSATDecisionProblem,
              ∃ _satToGraphRoute :
                ComplexityReduction.KarpReductionM
                  ComplexityReduction.CostedPolyTimeModel
                  ComplexityReduction.SAT.threeSATDecisionProblem
                  graphRouteTarget,
                ∃ _graphToFinalRoute :
                  ComplexityReduction.KarpReductionM
                    ComplexityReduction.CostedPolyTimeModel
                    graphRouteTarget
                    graphTargetProblem,
                  ∃ _satToNumericRoute :
                    ComplexityReduction.KarpReductionM
                      ComplexityReduction.CostedPolyTimeModel
                      ComplexityReduction.SAT.threeSATDecisionProblem
                      numericRouteTarget,
                    ∃ _numericToFinalRoute :
                      ComplexityReduction.KarpReductionM
                        ComplexityReduction.CostedPolyTimeModel
                        numericRouteTarget
                        numericTargetProblem,
                      ComplexityReduction.PolyReducibleM
                        ComplexityReduction.CostedPolyTimeModel
                        problem
                        graphTargetProblem ∧
                      ComplexityReduction.PolyReducibleM
                        ComplexityReduction.CostedPolyTimeModel
                        problem
                        numericTargetProblem ∧
                      ComplexityReduction.InNPEnc
                        ComplexityReduction.CostedPolyTimeModel
                        graphTargetProblem ∧
                      ComplexityReduction.InNPEnc
                        ComplexityReduction.CostedPolyTimeModel
                        numericTargetProblem ∧
                      ComplexityReduction.InNPEnc
                        ComplexityReduction.CostedPolyTimeModel
                        problem
```

The runner classifies L15 through the same target-contract analysis as L13 and
L14: it has encoding-bridge and multi-hop route obligations, and the route-source
audit requires five public Karp-reduction theorem mentions because the target
contains five public `KarpReductionM` witnesses.

## Hidden Lean Target

The legacy two-file validator accepts a hidden Lean target file for each legacy
sample. Public Lean proposition samples do not use hidden targets for proof
validation. The local repository still retains
`Benchmark/HiddenTargets/L0|L1|L2|L3|L4|L5|L6|L7|L8/<sample-id>.lean` for older
reports and development oracle checks; each legacy target defines:

```lean
namespace BenchmarkHiddenSample

abbrev sampleProblem : ComplexityReduction.EncodedDecisionProblem := ...
abbrev sampleClaim : Prop :=
  ComplexityReduction.InNPEnc ComplexityReduction.CostedPolyTimeModel sampleProblem

end BenchmarkHiddenSample
```

An `L2` hidden target additionally defines:

```lean
abbrev sampleRouteTarget : ComplexityReduction.EncodedDecisionProblem := ...
abbrev sampleReductionClaim : Type :=
  ComplexityReduction.KarpReductionM
    ComplexityReduction.CostedPolyTimeModel
    sampleProblem
    sampleRouteTarget
abbrev sampleRouteMembershipClaim : Prop :=
  ComplexityReduction.InNPEnc
    ComplexityReduction.CostedPolyTimeModel
    sampleRouteTarget
```

These declarations are not written to the opencode prompt.

An `L3` hidden target additionally defines:

```lean
abbrev sampleReferenceProblem : ComplexityReduction.EncodedDecisionProblem := ...
abbrev sampleInterfaceEquivalenceClaim : Type :=
  ComplexityReduction.ProblemEquivM
    ComplexityReduction.CostedPolyTimeModel
    sampleProblem
    sampleReferenceProblem
abbrev sampleInterfaceReductionClaim : Type :=
  ComplexityReduction.KarpReductionM
    ComplexityReduction.CostedPolyTimeModel
    sampleProblem
    sampleReferenceProblem
abbrev sampleReferenceMembershipClaim : Prop :=
  ComplexityReduction.InNPEnc
    ComplexityReduction.CostedPolyTimeModel
    sampleReferenceProblem
```

These declarations also stay hidden. They validate the adapter proof after
opencode returns; they are not templates and are not included in the prompt.

An `L4` hidden target additionally defines:

```lean
abbrev sampleRouteTarget1 : ComplexityReduction.EncodedDecisionProblem := ...
abbrev sampleRouteTarget2 : ComplexityReduction.EncodedDecisionProblem := ...
abbrev sampleReductionStep1Claim : Type := ...
abbrev sampleReductionStep2Claim : Type := ...
abbrev sampleComposedReductionClaim : Prop := ...
abbrev sampleRouteTarget2MembershipClaim : Prop := ...
```

An `L5` hidden target additionally defines:

```lean
abbrev sampleNormalizedProblem : ComplexityReduction.EncodedDecisionProblem := ...
abbrev sampleEncodingBridgeClaim : Type := ...
abbrev sampleNormalizedRouteTarget : ComplexityReduction.EncodedDecisionProblem := ...
abbrev sampleNormalizedReductionClaim : Type := ...
abbrev sampleLiftedReductionClaim : Prop := ...
abbrev sampleNormalizedRouteTargetMembershipClaim : Prop := ...
```

An `L6` hidden target additionally defines:

```lean
abbrev sampleTextbookTarget : ComplexityReduction.EncodedDecisionProblem := ...
abbrev sampleTextbookReductionClaim : Type := ...
abbrev sampleTextbookRouteClaim : Prop := ...
abbrev sampleTextbookTargetMembershipClaim : Prop := ...
```

An `L7` hidden target additionally defines:

```lean
abbrev sampleCspLanguage : ComplexityReduction.CSP.BoolLanguage := ...
abbrev sampleSchaeferHardCertificateClaim : Type 1 := ...
abbrev sampleSchaeferCompletenessClaim : Prop := ...
```

An `L8` hidden target additionally defines:

```lean
abbrev sampleLocalAdapterTarget : ComplexityReduction.EncodedDecisionProblem := ...
abbrev sampleLocalAdapterClaim : Prop := ...
abbrev sampleLocalAdapterReductionClaim : Type := ...
abbrev sampleLocalAdapterRouteClaim : Prop := ...
abbrev sampleLocalAdapterTargetMembershipClaim : Prop := ...
```

These declarations are also hidden in the legacy validator. They are not sample
templates and are not included in the prompt. Public Lean proposition samples
encode the corresponding obligations directly in `lean_target_type` instead of
using these hidden declarations.

The target root is not written to the opencode prompt or to
`usable_sample_inputs/*.json`. For a strict non-leaking benchmark, pass
`--hidden-target-root` pointing to a directory outside the opencode-readable
workspace.

After opencode returns, the runner generates a run-local `CombinedValidator.lean`:

```lean
/- hidden target generated by the runner -/
abbrev sampleProblem : ComplexityReduction.EncodedDecisionProblem := ...
abbrev sampleClaim : Prop :=
  ComplexityReduction.InNPEnc ComplexityReduction.CostedPolyTimeModel sampleProblem

/- opencode ProblemCertificate.lean -/
abbrev problem : ComplexityReduction.EncodedDecisionProblem := ...

/- opencode NPMembershipCertificate.lean -/
theorem npMembershipCertificate : ... := ...

#check (show problem = sampleProblem from rfl)
#check (npMembershipCertificate : sampleClaim)

/- L2 only. -/
#check (show routeTarget = sampleRouteTarget from rfl)
#check (reductionCertificate : sampleReductionClaim)
#check (routeTargetInNP : sampleRouteMembershipClaim)

/- L3 only. -/
#check (show referenceProblem = sampleReferenceProblem from rfl)
#check (interfaceEquivalenceCertificate : sampleInterfaceEquivalenceClaim)
#check (interfaceReductionCertificate : sampleInterfaceReductionClaim)
#check (referenceMembershipCertificate : sampleReferenceMembershipClaim)
```

This prevents a certificate for an unrelated problem from passing the sample.

## Pass Metric

The primary benchmark verdict is:

```text
primary_verdict.complete_verifiable_proof
```

It is true only when every manifest sample has:

- the two required Lean source files present and nonempty
- no `sorry`, `admit`, or new top-level `axiom`
- top-level `problem` and top-level `npMembershipCertificate`
- a generated `ProblemBindingValidator.lean` that compiles with `lake env lean`
- `problem` definitionally equal to the hidden `sampleProblem` before the
  membership stage runs
- a run-local snapshot of that validated problem binding used for final
  membership validation
- a generated `CombinedValidator.lean` that compiles with `lake env lean`
- `npMembershipCertificate` checking against the hidden `sampleClaim`
- for L2 samples only, `routeTarget`, `reductionCertificate`, and
  `routeTargetInNP` checking against the hidden route claims
- for L3 samples only, `referenceProblem`,
  `interfaceEquivalenceCertificate`, `interfaceReductionCertificate`, and
  `referenceMembershipCertificate` checking against the hidden adapter claims

Extra artifact files in the certificate directory are recorded in
`extra_artifact_files` but do not decide proof validity.

The terminal prints the count form, not a rate:

```text
usable_samples_proved: <proved>/<samples>
usable_problem_languages_proved: <proved languages>/<input languages>
```

## Commands

Short schema/report dry run without opencode:

```bash
python3 scripts/run_benchmark.py --jobs 4
```

Real benchmark with opencode:

```bash
python3 scripts/run_benchmark.py \
  --opencode-usable-samples \
  --require-opencode \
  --jobs 2 \
  --hidden-target-root Benchmark/HiddenTargets \
  --opencode-timeout 1200 \
  --usable-sample-timeout 120 \
  --retrieval-precheck-limit 6 \
  --retrieval-precheck-timeout 60 \
  --opencode-repair-rounds 1
```

`--jobs` controls how many samples are processed concurrently. The default is
`1`, preserving the previous serial behavior. The hard cap is `5`; larger values
are rejected by the runner. With `--opencode-usable-samples`,
each sample can call opencode twice: once for problem binding and once for
NP-membership certification. The second call is skipped when the first Lean
binding check fails.

By default, each failed stage gets one generic repair round. The runner gives
opencode compact Lean/lake validation feedback and asks it to repair the
certificate files. The repair prompt does not include hidden target source
files or route answers.

Disable repair when measuring a no-repair baseline:

```bash
python3 scripts/run_benchmark.py \
  --opencode-usable-samples \
  --require-opencode \
  --jobs 2 \
  --hidden-target-root Benchmark/HiddenTargets \
  --opencode-timeout 1200 \
  --usable-sample-timeout 120 \
  --opencode-repair-rounds 0
```
