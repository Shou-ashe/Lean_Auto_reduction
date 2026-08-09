# Hardness benchmark 迁移状态

> 日期：2026-07-28  
> 设计依据：`HARDNESS_AGENT_BENCHMARK_DESIGN_AND_MIGRATION_PLAN.md`  
> 当前 Agent：Phase 0--5 完成；M5 已达成

## 已完成范围

- B0：旧 schema 隔离、v2 manifest/suite loader、inventory、oracle quarantine；
- B1：旧 V2 `ThreeSAT` 拆分、Tagged ThreeSAT port、Knapsack exact ABI；
- B2 首个代表：旧 L2 `graph_coloring_route` 已迁移到 current exact endpoints；
- trusted `Certificate.NativeCookLevin`：canonical structured 3SAT、`reduceOfCapability`、
  `reduce`、native completeness 与 standard axiom gate；
- job-local attributed Cook--Levin root 在 Probe、revalidation 与 Artifact 中重新构造；
- fixed structured-3SAT root 与 root + production Clique suffix 两条 Phase 2 正例；
- Lean-side typed gap classifier：`lawfulPresentation`、`primitive`、`nativeMembership`、
  `verifierEncodingDiscipline` 与保守 `noRegistryPath`；
- `hardness_gap_ir_v1`、内容寻址稳定 `gap_id`、同环境 blocker replay 与单 capability
  `hardness_authoring_task_v1`；
- `unresolvedFamilyPremise` 的 deterministic/template closed-family authoring：固定 skeleton、
  editable-file boundary、attempt budget、source hash fence、candidate 编译与
  canonical-head/exact-endpoint validation；
- `lawfulPresentation` 固定 skeleton：closed structural origin、executable、alphabet equivalence、
  encoding coherence 与 semantic correctness；primary capability 必须是 exact canonical
  `StructuralRepresentationCertificate`，并同时验证 derived `CertifiedReduction` route；
- 已有 executable 的 `primitive` admission：dependent `TMPolyTimeMap` 与 semantic correctness 固定在
  同一个 executable；primary capability 必须是 exact canonical `Program.Primitive`，derived route
  必须实际使用该 primitive；
- 真正的新 program-indexed reduction authoring：固定七阶段
  `executable -> executable_direct_tm -> primitive -> program -> semantic_proof -> direct_tm ->
  certified_reduction`，每阶段独立 `.lean/.olean`、source fence、compile diagnostics、standard-axiom
  gate 与 checkpoint；
- program-indexed template observation 输出 executable、dependent executable direct-TM、semantic
  theorem 三个独立 global declaration handle；generated stage 不引用 marker value，poisoned semantic
  dependency 因而只在 `semantic_proof` checkpoint 被拒绝；
- dedicated program-indexed bundle validation 强制 primitive/executable、program/primitive、
  semantic/program、direct-TM/program 和 route/program 使用相同索引，拒绝第二个 map 的 proof/route
  以及 cost-only direct-TM facade；
- bounded retry 前清除全部七阶段源码和 `.olean`；resume checkpoint 使用 ordered stage-bundle hash，
  任一阶段缺失或改变都恢复当前 Lean environment 中的原 typed blocker；
- lawful/primitive template observation 只接受 exact role/source/target，并绑定 Probe nonce 与
  registry fingerprint；错误 role、错误 structural representation、错误 primitive endpoint 均拒绝；
- candidate 仅进入 job-local import，成功后重新 Probe、registry revalidation、final resolver、
  standard axiom gate 与 deterministic Artifact replay；
- 显式 `--resume` 只读取旧 report 的最小 content-addressed checkpoint；candidate 缺失或改变时不
  重新 author、不复用 stale `.olean`，而是由当前 Lean environment 恢复原 typed blocker；
- GapIR 不进入 final resolver，Artifact emitter 也显式拒绝把 GapIR 当作 route；
- wrong-membership、backend-only、missing-discipline、no-route、representation mismatch、
  missing primitive 与 missing native membership 七类负例；
- poisoned root 的非标准公理拒绝回归；
- suite/phase/disabled 调度、group 汇总、分项指标、一次统一 preflight 和隔离 case 并行；
- preflight 同时构建 Runtime 与全部选中 input modules，避免 source hash 对应到陈旧 `.olean`；
- current Lean regression aggregate；
- 110 个旧 case 的逐项迁移处置台账与源文件 SHA-256。

## 当前正式用例结果

Phase 4 完整 inventory 执行命令：

```bash
python3 scripts/run_hardness_benchmark.py \
  --manifest Benchmark/Hardness/MANIFEST.json \
  --agent-phase 4 \
  --planner deterministic \
  --jobs 3 \
  --lean-timeout 600
```

Phase 5 isolation suite 执行命令：

```bash
python3 scripts/run_hardness_benchmark.py \
  --suite phase5-authoring \
  --agent-phase 5 \
  --planner deterministic \
  --jobs 3 \
  --lean-timeout 600
```

下表合并展示上述两次实际运行的 case 结果；本轮没有执行单一的 Phase 5 全量 24-case run。

| case | expected | actual | atoms / gap | 结果 |
| --- | --- | --- | --- | --- |
| `existing-route` | VERIFIED | VERIFIED | 1 atom | PASS |
| `three-sat-refl` | VERIFIED | VERIFIED | 0 atoms | PASS |
| `no-route` | BLOCKED / `no_registry_path` | same | `noRegistryPath` | PASS |
| `three-sat-explicit-suffix` | VERIFIED | VERIFIED | 1 atom | PASS |
| `tagged-three-sat-normalization` | VERIFIED | VERIFIED | 1 atom | PASS |
| `graph-coloring-route` | VERIFIED | VERIFIED | 1 atom | PASS |
| `knapsack-native-cook-levin` | VERIFIED | VERIFIED | 1 atom | PASS |
| `knapsack-native-cook-levin-clique` | VERIFIED | VERIFIED | 2 atoms | PASS |
| `wrong-membership-endpoint` | FAILED / `input_declaration_rejected` | same | — | PASS |
| `backend-only-membership` | FAILED / `input_declaration_rejected` | same | — | PASS |
| `missing-verifier-discipline` | FAILED / `input_declaration_rejected` | same | — | PASS |
| `representation-mismatch-gap` | BLOCKED / `missing_lawful_presentation` | same | `lawfulPresentation` | PASS |
| `missing-primitive-gap` | BLOCKED / `missing_primitive` | same | `primitive` | PASS |
| `missing-native-membership-gap` | BLOCKED / `missing_native_membership` | same | `nativeMembership` | PASS |
| `closed-family-template-authoring` | VERIFIED after `unresolved_family_premise` | VERIFIED | 1 authored `sharedGadget` atom | PASS |
| `closed-family-candidate-absent` | BLOCKED / `unresolved_family_premise` | same after resume | candidate `missing` | PASS |
| `lawful-presentation-template-authoring` | VERIFIED after `missing_lawful_presentation` | VERIFIED | structural certificate + 1 derived route atom | PASS |
| `lawful-presentation-candidate-absent` | BLOCKED / `missing_lawful_presentation` | same after resume | candidate `missing` | PASS |
| `primitive-admission-template-authoring` | VERIFIED after `missing_primitive` | VERIFIED | `Program.Primitive` + 1 derived route atom | PASS |
| `primitive-admission-candidate-absent` | BLOCKED / `missing_primitive` | same after resume | candidate `missing` | PASS |
| `program-indexed-reduction-authoring` | VERIFIED after `missing_semantic_proof` | VERIFIED | seven checkpoints + 1 authored route atom | PASS |
| `program-indexed-candidate-absent` | BLOCKED / `missing_semantic_proof` | same after resume | bundle candidate `missing` | PASS |
| `missing-direct-tm-authoring-blocker` | BLOCKED / `missing_direct_tm` | same | `directTM`, 0 attempts | PASS |
| `program-indexed-retry-isolation` | VERIFIED after first rejected attempt | VERIFIED | attempt 1 fails only at `semantic_proof`; attempt 2 seven checkpoints | PASS |

实际报告：

- Phase 4 完整 inventory：`/tmp/hardness-phase4-full-lawful-primitive/report.json`；
- Phase 5 isolation suite：`/tmp/hardness-phase5-isolated.CWCjPa/report.json`。

Phase 5 进程启动后才修正 `full_reduction_authored_rate` 的分母，因此上述 raw report 保留了旧口径的
`0.666667`；使用当前 scorer 对同一组不可变 result rows 重新汇总后，六项指标均为 `1.0`。4/4 case
outcome、Lean artifacts 和全部 coverage assertion 未发生变化。

汇总：

- current runnable inventory：24，skipped 0；
- Phase 4 完整 outcome：20/20；新增 Phase 5 isolation outcome：4/4；不宣称未实际执行的单次 24/24；
- 两次运行合计 positive final verified：12/12；negative outcome accuracy：12/12；
- typed blocked replay：9/9（Phase 4 的 7 个，加 Phase 5 direct-TM blocker 与 candidate-absence resume）；
- full reduction authored：5/5 预期 `VERIFIED` 的 authoring case；预期保持 blocked 的 direct-TM 负例
  不进入该指标分母；
- axiom-clean verified：12/12；deterministic Artifact replay：12/12；
- model calls：0，最终验证完全使用 deterministic planner；
- Phase 4 三组 isolation 均为 2/2；Phase 5 program-indexed isolation 为 2/2、direct-TM blocker 为
  1/1、retry isolation 为 1/1；
- retry audit：attempt 1 的 accepted stages 精确为 executable、executable-direct-TM、primitive、
  program，随后 semantic 失败；attempt 2 七阶段全部 accepted；
- resume audit：四组均满足 `resumed_from_status = VERIFIED`、
  `resume_candidate_integrity = missing`、resume authoring attempts = 0。

## 回归结果

```text
lake build ComplexityReduction.Agent.Hardness.Regression
           Benchmark.Hardness.Regression          PASS
lake env lean Reference/ComplexityReduction/Agent/Hardness/Regression.lean
                                                  PASS
lake build Benchmark.Hardness.Regression        PASS
lake env lean Reference/Benchmark/Hardness/Regression.lean
                                                  PASS
python3 -m pytest -q                             70 passed
```

`Agent.Hardness.Regression.Authoring` 同时确认 parameterized-family matcher 只接受全局 declaration
handle，并拒绝 wrong-endpoint family candidate、错误 role 的 exact template、错误 structural
representation 和错误 primitive endpoint；新增 route 还必须重新进入 resolver。benchmark 的三组
authoring isolation 覆盖实际 blocker → candidate → `VERIFIED`，以及移走 candidate 与 `.olean` 后对
同一 content-addressed job resume 并恢复原 blocker。

`Agent.Hardness.Regression.ProgramIndexedAuthoring` 进一步验证七阶段 clean bundle，并分别拒绝 semantic
proof、direct-TM evidence 和 final route 指向第二个 program，以及把 cost-only evidence 伪装为 direct-TM
checkpoint。Phase 5 retry benchmark 用 `native_decide` 依赖污染第一个 semantic component，确认该依赖
不会污染 executable、executable-direct-TM、primitive 或 program checkpoint，并且 retry 清理不会把旧
源码或 `.olean` 带入第二次 attempt。

`GapClassifier` 回归使用真正只有 backend verifier、没有 exact native discipline 的 CNF endpoint，
避免用一个在当前 aggregate 中已具备 definitionally equal discipline 的 ThreeSAT endpoint 制造不一致
failure。`NativeCookLevinAxiomGate` 仍使用仅限 regression 的 poisoned membership，确认 job-local root
只要传递依赖非标准公理就会被 `assert_standard_axioms` 拒绝；该 axiom 不存在于 public benchmark
input 或 production runtime 中。

统一 preflight 现在执行 `lake build Runtime <selected-input-modules...>`。这是 correctness 要求：
`lake env lean Generated.lean` 会消费已有 `.olean`，不会因为 imported local source 改变而自行重建；
因此只构建 Runtime 可能让新 source hash 的 job 实际读取旧 input declarations。当前 runner 会先去重并
构建所有选中 input modules，再启动并行 case。

## 原 benchmark 的处理

下列原活动路径已删除：

```text
Benchmark/MANIFEST.yaml
Benchmark/Samples/
Benchmark/HiddenTargets/
Benchmark/GoldProofs/
Benchmark/V2Hardness/
```

按照迁移计划 B0，它们的唯一迁移来源被移动到 `Benchmark/Hardness/Legacy/`，而不是继续作为 active
benchmark。current runner 不会加载该目录，旧 JSON/YAML schema 均返回
`unsupported_legacy_benchmark`。模型 workspace、candidate imports、production aggregate 和当前通过率
全部排除 `Legacy/`。

之所以暂不物理删除 `Legacy/` 归档，是因为 ledger 中仍有 101 个 `deferred` case；直接删除会丢失
后续 B2--B4 port 所需的唯一题面/oracle 来源，并违反设计文档的迁移完整性约束。当前处置统计为：

```text
migrated   8
split      1
deferred 101
deprecated 0
total    110
```

每个 deferred case 已有目标 lane、最低 Agent phase、迁移原因、样例 SHA-256 及全部 oracle 文件记录。

## Stage N-C 完成状态

Phase 5/M5 typed authoring 与 Stage N-A、N-B、N-C 均已完成。N-C 已为
`fall2014-most-neighbors` 与 `uiuc2020-two-disjoint-bounded-paths` 建立 exact、可导入、无 oracle
public `PresentedProblem` 和独立 formalization validation，补齐 external-neighborhood 与 pair-of-path
witness 所需的通用 checker/gadget capability，并把正式 Quals primary 扩展到 5/5。

官方全新真实 DeepSeek 12-case run 为 `VERIFIED`：formalization 5/5、primary 5/5、adversarial 7/7、
protocol 12/12、18/18 gates、5 次 HTTP 200，最终 Lean 与独立 release replay 均退出码 0。其后
三次完全独立、无 resume/replay 的 full run 也全部维持 5/5 与 7/7，合计 15 次真实 HTTP 200、
0 replay、52,940 tokens；三轮最终 artifact SHA-256 均为
`295b3f984b95b21fc032121614706f2719fd93abadd63903d6ad89bf47d56d49`。稳定性规范报告为
`QUALS_COMPLETENESS_N_C_STABILITY_AGGREGATE.json`，SHA-256
`a82380344141b579936fe93f407cb624621057f3d82a6967033974e5bb6a30a2`。

五道旧 Quals 现均在 migration ledger 中逐题映射到 exact active case；后续迁移其余 deferred case
必须另立 benchmark contract。当前 task packet、template observation 与 GapIR 仍只用于调度和审计，
不会自行授予 capability。

每个任务仍只闭合一个 capability，并要求固定 statement/header、editable-file allowlist、attempt
budget、per-file diagnostics、canonical-head validation、job-local import、重新 scan 与 final resolve。
验收 benchmark 必须展示 blocker → verified；删除 candidate 后恢复原 blocker；endpoint 不匹配的
candidate 必须 validation 失败。只有具备 current exact type、稳定 typed blocker、gold sanity、final
resolver、axiom gate 和 replay 的 legacy case，才能把 ledger 状态从 `deferred` 改为 `migrated` 或
`split`。
