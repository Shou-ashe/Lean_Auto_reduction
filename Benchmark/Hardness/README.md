# Hardness Agent Benchmark

这是 `HARDNESS_AGENT_IMPLEMENTATION_PLAN.md` 对应的当前正式 benchmark。正式入口只有：

- `MANIFEST.json`：`hardness_benchmark_v2` 顶层清单；
- `Suites/*.json`：`hardness_benchmark_suite_v1` case 清单；
- `Lean/Reference/Benchmark/Hardness/Inputs/`：可由当前 Lake source root 导入的 Lean 题面。

`Expected/`、tag、route 数量和迁移 provenance 都是非权威评分元数据。case 是否成功仍只由
`HardnessAgent` 生成的 `Artifact.lean` 在当前环境中经 `by_hardness_resolver`、kernel、exact request
type、standard axiom gate 和 deterministic replay 决定。

## NP-hard 正式入口与 H-E 覆盖

`scripts/prove_np_hard.py` 只证明精确端点的 `NativeTMNPHard input`，不证明 membership 或
NP-complete，也不声称库内所有问题必然 NP-hard。完整 `PresentedProblem` 不需要 registry 登记；
stable ID、alias、wrapper 与裸 `LawfulEncodedType` 都必须生成 Lean 编译通过的 normalization
certificate。裸 encoding 无 presentation 或有多个不等价 presentation 时分别稳定阻塞为
`missing_lawful_presentation` / `ambiguous_lawful_presentation`，且模型调用保持零。

- `Suites/np_hard_h_e_heldout_inputs.json` 只含 module/problem/family 输入，不含 expected、gold、
  gap node、task class 或 authoring policy；
- `Evaluation/np_hard_h_e_heldout_oracle.json` 仅供运行结束后的评分，绝不传给 production
  orchestrator 或模型；
- `NP_HARD_H_E_INVENTORY.json` 由 Lean 对公开 ComplexityReduction 模块统一导出
  `PresentedProblem`、directed connection 和 hardness target 目录，再由 Python 计算内容哈希与
  正向可达性；hidden/gold namespace 不进入导入闭包。

H-E suite 要求 8 个互异正例、至少 4 个 family，并覆盖已有路径、单缺口、多缺口、程序组合和
程序合成；reverse-only、无 presentation、歧义 presentation 与错误端点 mutation 构成 4 个负例。
所有 authoring 正例使用本轮真实 `deepseek-v4-flash` 调用，已有路径和结构性负例必须为零调用。

## 当前 Agent phase

当前实现覆盖 Agent Phase 0--6，并已进入 Phase 7：完成了首个独立的 DeepSeek
model-authoring vertical slice，且已有一次真实 `deepseek-v4-flash` 隐藏 gold 样例到达最终
`VERIFIED`。Phase 4 的三个低风险 authoring、Phase 5 的完整
program-indexed reduction、Phase 6 的 membership/completeness lanes 继续作为无模型可信基线。
除 Phase 1 的既有 registry 路线和 Phase 2 checked Cook--Levin lane 外，失败路径由 Lean 侧
classifier 投影为 `hardness_gap_ir_v1`。Gap 保留 closed
`MissingCapabilityReason`、exact source/target declaration handle、component role、expected capability
head 和当前 registry fingerprint；runner 只据此生成稳定 `gap_id` 与单 capability
`hardness_authoring_task_v1`，不会从字符串自行猜 reason。

每个 blocked job 会用相同 Probe 再运行一次，只有 registry fingerprint 与 `gap_id` 均稳定才写入
最终 `BLOCKED`。`gap.json`、task packet 和 manifest 均不进入 Artifact，也不能被 Artifact emitter
当成 route 使用。

Phase 2 中 exact `NativeTMInNP source` 仍会在每个
job 的 Probe 与 Artifact 中安装一个由库内 `Certificate.NativeCookLevin.reduce` 构造的 checked root。
`knapsack-native-cook-levin` 固定目标为 canonical structured 3SAT，
`knapsack-native-cook-levin-clique` 固定目标为 structured Clique，分别强制覆盖 root 与 root+production
suffix；二者在 `--agent-phase 1` 下 phase-gated，在 Phase 2 下进入正式分母。

`gaps` suite 覆盖 representation mismatch、missing primitive 和 missing native membership；
`authoring` suite 包含三组同 job isolation case：

- closed-family：闭合 `unresolvedFamilyPremise`，生成 exact `CertifiedReduction`；
- lawful-presentation：生成 canonical `StructuralRepresentationCertificate` primary capability 和
  经验证的 derived `CertifiedReduction` route；
- primitive-admission：为已有 executable + dependent `TMPolyTimeMap` 生成 canonical
  `Program.Primitive` primary capability 和经验证的 derived route。

每组正例都经过 fenced job-local candidate、重新 Probe、bundle validation、registry revalidation、
final resolver、axiom gate 和 deterministic replay 后到达 `VERIFIED`。对应 candidate-absent case
随后移走 candidate 及 `.olean`，显式 resume 同一 job，并要求恢复原 typed blocker。resume 不会重新
author，也不会信任旧 report 中的路径、声明或 stale compiled output。

`phase5-authoring` suite 新增四个 case：

- `program-indexed-reduction-authoring`：从 `missing_semantic_proof` 经七阶段 bundle 到
  `VERIFIED`；
- `program-indexed-candidate-absent`：删除最终 candidate 后 resume，恢复同一个
  `missing_semantic_proof` blocker；
- `missing-direct-tm-authoring-blocker`：没有 exact dependent `TMPolyTimeMap` 时保持
  `BLOCKED / missing_direct_tm`，不接受 cost-only facade；
- `program-indexed-retry-isolation`：第一次 attempt 的前四阶段通过、`semantic_proof` 因非标准公理
  精确失败；清除全 bundle 源码和 `.olean` 后，第二次 attempt 七阶段全部通过。

七阶段分别是 `executable`、`executable_direct_tm`、`primitive`、`program`、`semantic_proof`、
`direct_tm` 和 `certified_reduction`。每阶段有独立源码 fence、compile command、axiom gate 与
checkpoint；bundle validator 还要求 primitive 使用同一 executable、program 使用同一 primitive，
semantic/direct-TM/route 使用同一 program。template marker 只用于观察，generated stage 直接引用三个
独立 component declaration，避免 poisoned semantic theorem 污染 executable checkpoint。

`membership` suite 新增三个 case：exact registered membership 得到零原子
`native_membership`；backend-only `TMInNP` 保持 `BLOCKED / missing_native_membership`；
deterministic authoring 从 `missing_verifier_program` 经 `verifier`、`witness_presentation`、
`discipline`、`native_membership` 四阶段 bundle 到达 `VERIFIED`。四阶段均有独立 fence、编译与
standard-axiom gate，随后还必须通过 dedicated bundle validator、post-authoring Probe、registry
revalidation、最终 Artifact 与 deterministic replay。

`completeness` suite 新增五个 case：exact registered structured 3SAT 得到
`registered_completeness`；structured 3SAT 经唯一的
`ComplexityReduction.Routes.ThreeSATToClique.sharedGadget` 前向原子和 exact Clique membership 得到
`transported_completeness`；缺 target membership、只有 target-to-3SAT 反向路径、以及只有 backend
completeness 的三个负例分别保持 typed blocker。completeness Artifact 对提取出的
`NativeTMNPComplete` 执行独立 axiom gate。

加入 IR feasibility slice 之前的 Phase 6 baseline 有 32 个 runnable case；当前 active manifest
包含 44 个 Phase 6 case 和 45 个 Phase 7 case。IR feasibility suite 已扩展到 Graph、Clause/CSP、
Incidence 三个 family，共 6 个 logical matched pair / 12 个 execution；共享 resolver 路径审计与
集中 kernel regression 已通过，完整 12-case Agent 多进程运行仍待执行。历史 membership suite
实测 3/3、completeness suite 实测 5/5，模型调用均为 0；这些是独立执行，本文不把它们表述成
一次未实际运行的全量结果。

首个 matched flat/IR run 的机器可读快照见
[`IR_FEASIBILITY_BASELINE.json`](IR_FEASIBILITY_BASELINE.json)。该快照只覆盖 registered、
type-validated edge；其中出现的负 compression 值是后续 family-aware slicing 与 flat matrix
补全工作的基线，不是 IR hypothesis 的最终结论。

当前扩展后的配对、实际 declaration 路径、不可用配对与验证状态见
[`IR_FEASIBILITY_COVERAGE.json`](IR_FEASIBILITY_COVERAGE.json)。该文件明确记录本轮没有修改
Lean 数学库，也没有创建 benchmark-local reduction facade。

## 运行

```bash
python3 scripts/run_hardness_benchmark.py --list --agent-phase 6

python3 scripts/run_hardness_benchmark.py \
  --suite ir-feasibility \
  --planner deterministic

python3 scripts/run_hardness_benchmark.py \
  --manifest Benchmark/Hardness/MANIFEST.json \
  --agent-phase 6 \
  --planner deterministic \
  --jobs 4 \
  --lean-timeout 600

python3 scripts/run_hardness_benchmark.py \
  --suite membership \
  --agent-phase 6 \
  --planner deterministic \
  --jobs 2 \
  --lean-timeout 1200

python3 scripts/run_hardness_benchmark.py \
  --suite completeness \
  --agent-phase 6 \
  --planner deterministic \
  --jobs 2 \
  --lean-timeout 600

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

`--suite` 与 `--case` 可重复。`--agent-phase` 控制 phase gate，但显式 disabled 的未实现 case 不会因为
增大该参数而被错误启用。`--list` 会进行完整 schema、路径、重复 ID、public-module 和 oracle-reference
校验，但不调用 Lean 或模型。正式执行只做一次统一 preflight：先构建 Runtime 与全部选中 input
modules，防止 generated Lean 文件读到陈旧 `.olean`，随后才启动并行 case。`--jobs` 只并行彼此隔离
的 case，不会省略任何 case 内的 input gate、probe、registry revalidation、artifact、axiom gate 或
replay。

汇总报告区分：

- `case_outcome_accuracy`；
- `positive_final_verified_rate`；
- `negative_block_accuracy`；
- `full_reduction_authored_rate`；
- `native_membership_rate`；
- `native_completeness_rate`；
- `axiom_clean_rate`；
- `deterministic_replay_rate`；
- disabled/phase-gated skipped cases。

`full_reduction_authored_rate` 的分母只包含“预期最终 `VERIFIED` 且要求新 reduction authoring”的
case；预期保持 typed blocker 的 Phase 5 负例由 `negative_block_accuracy` 计分，不会错误拉低
authoring 成功率。

Phase 7 的模型生成 case 只进入 `model_synthesis` lane。route search 始终 deterministic；已有闭合
路线在任何 authoring policy 下都必须保持 `model_called = false`。DeepSeek 只能返回当前 task 的单个
editable proof body，runner 会保存 prompt/response hash、usage、patch、逐次 diagnostics 和编译记录，
并在 fresh probe、ClosedResolver、axiom gate 与无模型 replay 后才允许 `VERIFIED`。

2026-07-29 的真实 `model-required` 实测中，`deepseek-v4-flash` 发生 3 次 HTTP 200
调用，总 usage 为 12,297 tokens；前两次证明被 Lean 诊断拒绝，第三次受 fence
约束的 proof body 通过。未变的前缀 checkpoint 在重试中均实际复用，完整七阶段
bundle、fresh registry scan、ClosedResolver、standard-axiom gate 和 deterministic replay 全部
通过，artifact SHA-256 为
`17d33d96b0cc5befb319d40e0f57fc2d5940dd56ac6db1c23f7787ea19c468bb`。随后 Python 回归为
106/106。另一次完全隔离的真实 `model-auto` 运行也在没有 deterministic fallback
的情况下到达 `VERIFIED`：第 4/4 次有界修复闭合 semantic proof，共使用 15,942
tokens，最终 artifact hash 与上述运行相同。两次端到端运行分别约 44 和 63 分钟，
而每次模型网络时间都不到一分钟；当前主要性能瓶颈是 mounted workspace 上的
Lean 冷启动。两种 policy 都至少还需要各 2 次同配置隔离运行，并生成正式 trial
aggregate，才满足各三次的发布稳定性要求。

`run_hardness_model_trials.py` 默认把 `model-auto` 和 `model-required` 各独立运行三次，并汇总
outcome accuracy、capability closure、真实 call/token/time 与稳定性；它不会把这些结果并入
existing-route 或 deterministic-fixture lane。

## 旧 benchmark

旧 Opencode 与旧 V2 schema 不再是可执行入口。迁移来源按 B0 规则隔离在 `Legacy/`，逐项处置记录在
`MIGRATION_LEDGER.json`，本轮实现与实测结果见 `MIGRATION_STATUS.md`。runner 会以
`unsupported_legacy_benchmark` 明确拒绝旧 schema；legacy
通过率不得和当前 exact-presentation benchmark 合并。

`Legacy/`、`Expected/`、GoldProofs 与 HiddenTargets 不得进入模型 workspace，也不得被 candidate
import。它们不属于 production aggregate。
