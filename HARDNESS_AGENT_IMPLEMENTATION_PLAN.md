# ComplexityReduction Hardness Agent 详细实施计划

> 状态：实施中；Phase 0--6 已完成确定性可信基础设施；Phase 7 首个隐藏 gold
> semantic-proof model-authoring vertical slice已由真实 DeepSeek 生成并最终 `VERIFIED`，
> 三次稳定性评测、Lean 冷启动优化与更广 capability authoring 仍待完成
>
> 日期：2026-07-27
>
> 实施进度更新：2026-07-29
>
> 参考设计：`../LeanAutoReduction/V2_HARDNESS_AGENT_DESIGN.md`
>
> 当前可信库：`Lean/Reference/ComplexityReduction/`

## 1. 文档目的

本文将已有 hardness agent 设计细化为可逐阶段交付的工程计划。面向用户的产品目标是：
输入一个已经形式化的 Lean 题面，agent 输出完整的归约定义、正确性证明、复杂度证明以及
可独立检查的 Lean 源码。LLM 负责生成和修复这些源码，但不能自行宣称归约成立；证明权限
始终由 Lean kernel 掌握：

1. Lean 负责精确输入 elaboration、能力识别、端点连接、证书组合和最终 kernel 检查；
2. 确定性 runner 负责已有 registry 路线的图搜索、任务状态、缓存、命令执行和审计记录；
3. 已有闭合路线完全由确定性算法选择和组合，不调用 LLM；
4. 只有在 Lean 给出 exact typed missing capability 后，模型才生成或修复 job-local Lean 源码；
5. 任意模型输出只有通过 Lean 类型检查、registry validation、resolver 和 axiom gate 后，
   才能进入最终 artifact。

这里必须严格区分两类工作：

- **route reuse**：registry 中已经存在所需证书边。它是有限的图搜索问题，应使用
  BFS/Dijkstra/稳定 cost ordering 直接求解，LLM 不参与；
- **reduction authoring**：registry 中不存在闭合路线。Lean 只固定题面、端点和缺失 capability
  的类型，DeepSeek 负责生成新的 reduction/program/proof 源码，再由 Lean 验证。

本文后续所称“分阶段”或“局部 capability”只描述内部编译与验证单元，不表示最终只向用户
返回局部结果。一个端到端任务可以依次生成多个 capability，最终必须输出完整、可编译的
reduction bundle 和 `Artifact.lean`。

本文同时处理当前代码已经从 `ComplexityReduction_IR.V2` 重命名为
`ComplexityReduction` 后产生的运行时迁移问题。

Phase 4 的三个低风险 deterministic/template authoring lane 已全部打通：closed parameterized
family、`lawfulPresentation` 固定 skeleton，以及已有 executable + dependent `TMPolyTimeMap` 的
`primitive` admission。Phase 5 在同一可信边界上实现了完整的 program-indexed authoring 管线：
`executable -> executable_direct_tm -> primitive -> program -> semantic_proof -> direct_tm ->
certified_reduction` 七个阶段分别拥有独立源码 fence、`.lean/.olean`、standard-axiom gate 和
checkpoint。Phase 4--6 的通过结果来自确定性模板，模型调用均为 0；它们证明的是 authoring
基础设施和可信边界，而不是 LLM 已经能够从题面独立写出归约。

Phase 5 的 template observation 只暴露三个相互独立的全局组件声明：executable、该 executable 的
dependent direct-TM evidence，以及 semantic theorem。生成阶段不会引用承载 observation 的 marker，
因此一个带非标准公理的 semantic theorem 只会污染并拒绝 `semantic_proof` checkpoint，不会错误污染
前面的 executable 或 primitive。最终 bundle validator 强制 executable、primitive、program、semantic、
direct-TM 和 route 使用同一索引，拒绝第二个 program 的 proof/route，也拒绝只有 cost facade、没有真实
`TMPolyTimeMap` head 的证据。

Phase 6 闭合了 exact `proveInNP` 与 `proveNPComplete`。resolver 只从 validated exact
`NativeTMInNP` 或 `NativeTMNPComplete` 构造 typed result，并把
`native_membership`、`registered_completeness`、`transported_completeness` 三类证据严格分开。
completeness transport 的唯一方向是 native-complete hub 到 target，且 target 必须另有 exact native
membership；backend membership/completeness 和 target-to-hub 反向路径均 fail closed。

membership authoring 固定为 `verifier -> witness_presentation -> discipline -> native_membership`
四阶段 job-local bundle，每阶段独立编译和 axiom gate，之后再经 dedicated bundle validator、fresh
Probe、registry revalidation、最终 Artifact 与 replay。Phase 6 membership suite 实测 3/3，
completeness suite 实测 5/5，模型调用均为 0。当前 inventory 有 32 个 runnable case；这两次是独立
suite 执行，本轮没有把它们表述成一次未实际运行的 32/32 全量结果。

## 2. 当前基线与已解决的历史阻断项

### 2.1 当前基线

- Lake 中只有一个本地 Lean 库：`ComplexityReduction`；
- 源码根为 `Lean/Reference/ComplexityReduction/`；
- 已有精确 `PresentedProblem`、`CertifiedReduction`、`CertifiedPath`、
  `NativeTMInNP` 和 `NativeTMNPComplete`；
- 已有 attribute discovery、type-directed registry validation 和 graph export；
- 已有 `TypedAutoReductionRequest`、`TypedAutoReductionResult` 和
  `ClosedResolver`；
- 已有 `MissingCapabilityReason`、`ComponentRequest` 与 fail-closed component
  composition；
- 完整 `lake build ComplexityReduction` 当前通过。

### 2.2 Phase 0 原始阻断项（均已解决）

1. `Protocol/ClosedResolver.lean` 的 `productionAggregateModule` 曾拼接旧模块名
   `ComplexityReduction_IR.V2.Registry.Aggregate`；实际执行时会误报
   `aggregateNotImported`。
2. 旧 `atomicFirst` 在全图中只要发现任意 atomic edge，就会全局丢弃所有
   `finalComposition` edge；这不是逐端点 fallback，可能错误删除必要路线。
3. 旧 `resolvePath` 未优先处理 `source` 与 `target` definitionally equal 的情况，
   因而不能稳定生成 `CertifiedPath.refl`。
4. 相邻工程的 agent runtime、runner、测试和文档曾使用
   `ComplexityReduction_IR.V2`、`#v2_hardness_probe`、
   `by_v2_hardness_resolver` 等旧名称。
5. 旧 runner 曾把输入 Lean 文件全文拼进 `Probe.lean` 和 `Artifact.lean`，而不是
   导入一个模块；这会破坏模块边界，并允许输入命令干扰 probe 输出。
6. probe 的 pretty-printed endpoint 曾被 runner 再次当作 Lean term 写入 artifact；
   pretty string 应只用于显示，不能成为自动目标的稳定句柄。
7. 旧 `route_id = route-{target_index}` 假设每个 target 只有一条候选路线；扩展多路线后
   会发生 ID 冲突。
8. request 协议已声明 `proveInNP` 和 `proveNPComplete`，但当时 closed resolver 尚未真正
   闭合这两个分支。

这些项目已经在 Phase 0--6 中解决，并作为回归不变量保留；后续不得因接入模型而重新引入。

## 3. 范围

### 3.1 本计划覆盖

- 精确 `PresentedProblem` 输入；
- polynomial-time many-one reduction；
- 已有 registry 路径复用；
- exact `NativeTMInNP` 驱动的 checked Cook-Levin 根；
- `reduceTo`、`reduceToKnownNP`、`proveInNP`、`proveNPComplete`；
- typed missing capability 诊断；
- 局部 presentation、primitive、semantic proof、direct-TM、verifier 和
  parameterized-family authoring；
- deterministic registry resolver 与 typed gap planner；
- DeepSeek 驱动的分阶段 Lean authoring、编译诊断反馈和完整 reduction bundle 输出；
- 可恢复 job、审计报告、负例测试和标准公理 gate。

### 3.2 暂不覆盖

- 从任意自然语言自动形式化一个新 NP 问题；
- 从裸 `DecisionProblem` 猜测编码；
- 从 backend `TMInNP` 自动伪造 native verifier discipline；
- logspace、parsimonious、counting、approximation 或 randomized reduction；
- 允许模型直接指定可信 theorem name 或 route atom；
- 将 JSON、日志、hash 或模型响应反序列化为 Lean certificate；
- 在最终 artifact 中容忍 `sorryAx`、自定义 axiom 或未审计 unsafe 证明入口。

## 4. 核心不变量

以下不变量在所有阶段保持成立：

1. **Exact endpoint**：source 和 target 始终是 elaborated `PresentedProblem`，端点连接
   只使用受控 `whnf` 与 kernel definitional equality。
2. **Exact presentation**：`.fromPresented source` 只接受 `.exactUser`；representation
   mismatch 必须由显式、已认证的 adapter 或 presentation-change certificate 处理。
3. **Program-indexed certificate**：`CertifiedReduction` 的函数、语义证明和复杂度证明
   必须索引到同一个 `PolyProg`。
4. **Type-directed registry**：attribute 只确定扫描范围；能力只来自声明的 elaborated type。
5. **Closed final resolution**：最终 artifact 不接收 runner 选出的 theorem list；resolver
   必须在当前 environment 中重新发现、验证并组合原子。
6. **Observational metadata only**：GoalIR、HardnessPlan、fingerprint、route ID、日志和模型响应
   永远不授予 Lean 能力。
7. **Fail closed**：缺少 presentation、primitive、semantic proof、direct-TM、discipline、
   membership 或 completeness 时返回 typed blocker，不降级到 backend 或字符串证据。
8. **Revalidation**：缓存命中不能直接恢复 `verified`；最终 request 必须重新 elaboration、
   resolution 和 axiom audit。
9. **Reuse/authoring separation**：已有闭合路线不得触发模型调用；模型不能选择 route ID、
   theorem name 或 registry atom，只能编辑当前 typed task 允许的候选源码。

## 5. 目标架构

```text
输入模块 + source declaration + objective
                  |
          Lean Input Gate
                  |
       Capability Snapshot / Registry Graph
                  |
       Deterministic ClosedResolver
                  |
       +----------+---------------------------+
       |                                      |
已有闭合路线或 Cook-Levin 根              Exact typed gap
       |                                      |
       |                           固定 skeleton / editable fence
       |                                      |
       |                            DeepSeek 生成或修复 Lean 源码
       |                                      |
       |                            Candidate compile + validation
       |                                      |
       +------------------ Fresh registry scan
                          |
               Final Resolver + Axiom Gate
                          |
          完整 reduction bundle + Artifact.lean
                          |
                      report.json
```

### 5.1 Lean 可信层

Lean 可信层拥有：

- 输入声明的精确类型检查；
- registry candidate validation；
- exact endpoint equality；
- route search 所使用的已验证 graph；
- Cook-Levin reduction theorem；
- candidate capability 的重新分类；
- `TypedAutoReductionResult request` 的构造；
- `sorryAx` 与标准公理 allowlist gate。

### 5.2 Runner 非可信层

Runner 只拥有：

- job ID、状态迁移和文件布局；
- 调用 `lake env lean`、测试和静态扫描；
- 解析 observational probe output；
- 确定性 registry 图搜索、路线选择和 gap 调度；
- 只针对 typed authoring task 的模型 API 调用、预算和重试；
- 生成固定模板；
- 保存报告和日志。

Runner 可以使任务失败、超时或漏掉一个可行候选，但不能产生 Lean 可接受的错误证书。

## 6. 建议目录结构

保持单一 `ComplexityReduction` Lean 库，不新增第二个可信库 target：

```text
Lean/Reference/ComplexityReduction/
  Agent/
    Hardness/
      InputGate.lean
      Probe.lean
      Gap.lean
      Resolver.lean
      Runtime.lean
      Regression.lean
  Certificate/
    NativeCookLevin.lean
    CompletenessTransport.lean
  Protocol/
    ClosedResolver.lean
    MissingCapability.lean
    Request.lean
    Result.lean
  Registry/
    Aggregate.lean
    Export.lean
    Graph.lean

agent/
  hardness/
    __init__.py
    models.py
    state.py
    lean_runner.py
    probe.py
    planner.py
    authoring.py
    emitter.py
    report.py
    model_client.py

scripts/
  run_hardness_agent.py
  run_hardness_benchmark.py

tests/
  test_hardness_models.py
  test_hardness_probe.py
  test_hardness_planner.py
  test_hardness_state.py
  test_hardness_emitter.py
  test_hardness_negative.py

Benchmark/Hardness/
  Inputs/
  Expected/
  MANIFEST.json
```

`NativeCookLevin.lean` 放在 `Certificate` 而不是 `Agent` 下，因为它是可复用数学能力，
不应与外层编排实现绑定。`Agent/Hardness` 只保留 environment inspection、probe、gap
classification 和最终 elaborator。

## 7. 输入 ABI

### 7.1 CLI

Phase 7 完成后的目标 CLI 为：

```bash
python3 scripts/run_hardness_agent.py \
  --module Benchmark.Hardness.Inputs.KnapsackNativeNP \
  --source Benchmark.Hardness.Inputs.KnapsackNativeNP.source \
  --membership Benchmark.Hardness.Inputs.KnapsackNativeNP.membership \
  --objective reduce-to-known-np \
  --planner deterministic \
  --authoring model-required \
  --output-dir .reduction-agent/jobs/knapsack
```

规则：

- `--module` 必须是可由当前 Lake environment 导入的模块名；
- `--source`、`--membership` 和可选 `--target` 第一版只接受 fully-qualified declaration
  name，不接受任意 Lean term；
- runner 只生成 `import <module>`，不复制输入源码；
- source declaration 必须闭合并具有精确 `PresentedProblem` 类型；
- membership 若提供，必须具有精确 `NativeTMInNP source` 类型；
- target 若提供，必须能绑定到 validated `PresentedProblem` declaration；
- `--planner` 只负责已有 registry 路线，目标接口只保留 `deterministic`；现有
  `auto`/`model-required` route-reranking 取值属于待删除的过渡兼容接口；
- `--authoring` 独立控制缺口补齐，目标取值为 `disabled`、`deterministic-template`、
  `model-auto`、`model-required`；`model-required` 只表示出现 typed gap 时必须调用模型，
  不表示已有闭合路线也要调用模型；
- 所有名称由 Lean 再次解析，runner 的正则检查只用于阻止语法注入，不用于授予能力。

### 7.2 Objective

CLI objective 与 Lean request 一一映射：

```text
reduce-to             -> AutoReductionRequest.reduceTo
reduce-to-known-np    -> AutoReductionRequest.reduceToKnownNP
prove-in-np           -> AutoReductionRequest.proveInNP
prove-np-complete     -> AutoReductionRequest.proveNPComplete
```

不得把一种 objective 的成功结果复用为另一种 objective，除非 Lean 中存在显式 transport
定理并构造了后者的精确结果类型。

## 8. Job 数据模型

所有 JSON 结构带独立 schema version。它们只用于调度和审计。

### 8.1 GoalIR

```json
{
  "schema_version": "hardness_goal_ir_v1",
  "job_id": "sha256:...",
  "input_module": "Benchmark.Hardness.Inputs.KnapsackNativeNP",
  "source_declaration": "...source",
  "membership_declaration": "...membership",
  "target_declaration": null,
  "objective": "reduce_to_known_np",
  "presentation_policy": "exact_user",
  "computation_policy": "polyprog_compiled_direct_tm",
  "toolchain": "leanprover/lean4:v4.29.0",
  "input_sha256": "...",
  "lake_manifest_sha256": "..."
}
```

### 8.2 CapabilitySnapshot

记录同一次 Lean scan 的观察结果：

- elaborated source 显示值；
- exact source declaration；
- membership 是否通过精确类型检查；
- registry fingerprint；
- validated targets；
- validated edges；
- parameterized families；
- reachable routes；
- typed blockers。

Snapshot 中的 endpoint pretty string 只显示，不作为下一次 Lean 输入。自动 target 必须使用
validated presented-problem declaration handle。

### 8.3 RouteIR

```json
{
  "schema_version": "hardness_route_ir_v1",
  "route_id": "sha256:<target+atoms+registry>",
  "target_declaration": "ComplexityReduction.Presentation....problem",
  "membership_declaration": "ComplexityReduction.Problems....nativeTMInNP",
  "atoms": ["...edge1", "...edge2"],
  "roles": ["ingress", "egress"],
  "cost": {
    "new_capabilities": 0,
    "final_composition_edges": 0,
    "atom_count": 2
  }
}
```

### 8.4 GapIR

GapIR 是 `MissingCapabilityReason` 的非可信镜像，同时携带 Lean 输出的稳定 declaration
handle：

```json
{
  "schema_version": "hardness_gap_ir_v1",
  "gap_id": "sha256:...",
  "reason": "primitive",
  "role": "sharedGadget",
  "source_declaration": "...",
  "target_declaration": "...",
  "expected_capability_head": "ComplexityReduction.Program.Primitive",
  "producer": "lean_gap_classifier"
}
```

Runner 不能自行把 `noRegistryPath` 猜成 `primitive`；细分必须来自 Lean-side gap
classification，或者以 `unknown` 保持 blocked。

### 8.5 Attempt 与 VerificationReceipt

每次 authoring 尝试记录：

- attempt number；
- task packet hash；
- 模型及参数；
- 输入上下文文件列表；
- 生成或修改的候选文件；
- Lean diagnostics；
- timeout 与 token 使用；
- static scan 结果；
- candidate validation 结果。

`VerificationReceipt` 只在最终重新编译后生成，记录 artifact hash、当前 registry
fingerprint、Lean 命令、退出码和 axiom gate 结果。它仍是审计信息，不是证明。

## 9. Job ID 与可恢复状态机

### 9.1 Job ID

Job ID 由以下内容的 canonical JSON 计算 SHA-256：

- input module 与输入文件 hash；
- source、membership、target declaration name；
- objective 与 trust policy；
- `lean-toolchain` 内容；
- `lake-manifest.json` hash；
- agent schema major version。

API key、时间戳和模型响应不进入 job ID。

### 9.2 状态

```text
RECEIVED
INPUT_VALIDATED
CAPABILITIES_SCANNED
PLAN_SELECTED
AUTHORING
CANDIDATE_COMPILED
REGISTRY_REVALIDATED
FINAL_RESOLVED
AXIOM_AUDITED
VERIFIED

终止状态：BLOCKED | FAILED | CANCELLED
```

### 9.3 状态转换规则

- 每个转换必须是幂等的；
- 转换前检查所依赖文件 hash；
- registry fingerprint 改变时，从 `CAPABILITIES_SCANNED` 重跑；
- candidate 文件改变时，从 `CANDIDATE_COMPILED` 重跑；
- `VERIFIED` 在 resume 时必须重新执行 final artifact compile；
- `BLOCKED` 表示已得到稳定 typed blocker，且当前策略无可执行 authoring lane；
- `FAILED` 表示基础设施、语法、timeout 或内部 invariant 失败；
- 状态历史追加写入 `events.jsonl`，`report.json` 是历史的当前投影。

## 10. Lean 侧详细设计

### 10.1 InputGate

`Agent/Hardness/InputGate.lean` 负责：

1. 在已导入 input module 的 environment 中查找 source declaration；
2. 检查声明闭合且类型 definitionally equal 于 `PresentedProblem`；
3. 若提供 membership，检查其类型为 exact `NativeTMInNP source`；
4. 若提供 target，检查其是 validated presented-problem declaration；
5. 拒绝 open metavariable、未实例化参数和 universe hole；
6. 返回 MetaM 内部的 typed handles，probe 只输出其非权威投影。

### 10.2 Probe 输出

短期可继续使用单行 marker，但必须增加：

- schema version；
- job nonce；
- record kind；
- stable declaration name；
- route ID；
- registry fingerprint。

runner 只解析包含本 job nonce 的记录，避免 input 模块伪造同名日志干扰排序。中期应改成
Lean executable 或结构化 JSON command output，取消对普通 diagnostic 文本的宽松扫描。

### 10.3 Registry target handle

自动 target 不使用 pretty endpoint。对每个 `NativeTMInNP target`：

1. 从 validated `typed_problem` candidates 中寻找一个声明，其值与 target endpoint defeq；
2. 若有多个，按 declaration name 稳定排序并选择 canonical handle；
3. 若没有可重新 elaboration 的 problem declaration，target 仅可显示，不进入自动候选；
4. final artifact 使用该 problem declaration name 构造 request；
5. resolver 仍重新检查它与 membership endpoint defeq。

### 10.4 Path search

先实现正确性，再优化规模：

1. 检查 `controlledDefEq source target`，成立时返回 `CertifiedPath.refl`；
2. 保留所有 validated reduction edge；
3. 不再通过 `atomicFirst` 全局删除 convenience edge；
4. 使用稳定优先队列搜索，cost 按字典序比较：
   `newCapabilities`、`finalCompositionPenalty`、`atomCount`、`declarationNames`；
5. 对相同 defeq endpoint pair，有 component atom 时优先，但仍保留 final composition fallback；
6. 每个选中 atom 在构造 `CertifiedPath` 前再次通过 attributed declaration validation；
7. result term 构造后检查实际 `CertifiedPath source target` 类型。

图较小时可使用简单 list frontier。只有 benchmark 证明性能不足后，才引入基于 whnf/hash 的
候选 bucket；hash 只能缩小候选范围，最终仍用 `isDefEq`。

### 10.5 Native Cook-Levin

将 checked Cook-Levin 根移动到 `Certificate/NativeCookLevin.lean`：

- `reduceOfCapability`；
- `reduce`；
- canonical structured 3SAT target；
- structured 3SAT native completeness；
- 标准公理 gate。

Agent runtime 只调用这些库声明，不拥有独立的 map、correctness 或 TM witness。

### 10.6 Exact request resolver

按以下顺序实现 request lanes：

1. `reduceTo`：exact source match + closed path；
2. `reduceToKnownNP`：closed path + exact target `NativeTMInNP`；
3. `proveInNP`：从 registry 重新取得 exact `NativeTMInNP problem`；
4. `proveNPComplete`：
   - 优先使用 exact registered `NativeTMNPComplete problem`；
   - 否则取得 exact target membership；
   - 取得 canonical complete hub 到 target 的 certified path；
   - 使用库内 completeness transport 定理构造 exact `NativeTMNPComplete target`。

`proveNPComplete` 不允许仅凭 `3SAT <= target` 得出 completeness；必须同时取得 target
native membership，并使用已验证的 canonical hardness root。

### 10.7 Gap classifier

`Agent/Hardness/Gap.lean` 把失败细分为现有闭集：

```text
lawfulPresentation
primitive
semanticProof
executableRelationContract
directTM
verifierEncodingDiscipline
verifierProgram
witnessLawfulPresentation
unresolvedFamilyPremise
noRegistryPath
nativeMembership
nativeCompleteness
```

要求：

- blocker 保留 exact typed endpoint；
- 字符串只由 blocker 投影，不反向构造 blocker；
- 无法可靠判断更细原因时返回 `noRegistryPath`，不由 runner 猜测；
- authoring 成功后必须重新 scan，不能在原 blocker 上直接翻转状态。

## 11. Deterministic registry resolver 与 authoring 入口

### 11.1 已有闭合路线的优先级

默认顺序：

1. source = target 的 reflexive path；
2. 纯 registry atomic route；
3. Cook-Levin root + registry suffix；
4. 包含 validated final-composition fallback 的 route。

需要闭合 parameterized-family premise 或生成新 capability 的情况不是“已有路线”，必须进入
typed gap/authoring 分支。即使 registry 图很大，也应使用确定性图算法搜索，而不是让模型从
route ID 列表中猜测。

### 11.2 稳定 tie-break

同一成本使用以下稳定顺序：

1. target declaration name；
2. atom declaration name list；
3. role list；
4. route content hash。

不要使用 environment iteration 顺序或 pretty endpoint 作为最终 tie-break。

### 11.3 已有路线禁止模型调用

- registry 中存在闭合路线时，resolver 直接选择稳定最小 cost 路线；
- 不生成供模型选择的 route allowlist，不调用 DeepSeek，也不产生模型费用；
- `route_id` 只用于缓存、审计和 deterministic replay，不是模型决策接口；
- 如需面向用户生成路线解释，应在 artifact 已验证后作为独立、非阻塞的展示功能实现，
  不得进入求证主路径。

### 11.4 Authoring 触发条件

只有同时满足以下条件才允许调用模型：

1. exact input gate 已通过；
2. 当前 registry 中没有可闭合 request 的路线或 exact evidence；
3. Lean-side classifier 已产生可执行的 typed gap；
4. runner 已为该 gap 生成固定 expected type、skeleton 和 editable-file fence；
5. authoring policy 为 `model-auto` 或 `model-required`，且仍有 attempt budget。

若只能得到 `noRegistryPath` 而无法形成安全的 capability skeleton，任务保持 `BLOCKED`；不得把
整张 route graph 交给模型，让模型自行发明 theorem name 或声明某条路线存在。

| 当前状态 | 系统动作 | 调用 DeepSeek |
| --- | --- | --- |
| registry 已有闭合路线 | 确定性搜索、组合、final verify | 否 |
| 无闭合路线，有 typed gap，`authoring=disabled` | 保留 exact blocker | 否 |
| 无闭合路线，有 typed gap，`authoring=deterministic-template` | 运行受控 fixture/skeleton | 否 |
| 无闭合路线，有 typed gap，`authoring=model-auto/model-required` | 生成或修复候选 Lean 源码 | 是 |
| 只有不可安全细分的 `noRegistryPath` | `BLOCKED`，等待新增 classifier/skeleton | 否 |

## 12. Authoring 子系统

### 12.1 产品输出与内部任务的关系

用户请求的是完整归约与完整 Lean 代码。runner 可以为安全和诊断把它确定性拆为
`executable -> primitive -> program -> semantic_proof -> direct_tm -> certified_reduction`
等 typed task，但这些 task 共同属于同一个 end-to-end authoring job。成功时必须交付：

- 所有新生成的 job-local `.lean` 源文件；
- 最终 reduction function/program；
- 语义正确性与复杂度证据；
- 完整 `CertifiedReduction`/membership/completeness artifact（按 objective）；
- 可复现的编译命令、diagnostics、axiom audit 与 `report.json`。

内部“局部候选”是验证粒度，不是缩减产品目标。

### 12.2 AuthoringTask

每个任务只要求一个 capability：

```json
{
  "schema_version": "hardness_authoring_task_v1",
  "task_id": "sha256:...",
  "gap_reason": "semanticProof",
  "expected_type": "...",
  "source_declaration": "...",
  "target_declaration": "...",
  "role": "sharedGadget",
  "candidate_module": "Generated.Job123.SemanticProof",
  "allowed_imports": ["ComplexityReduction.Domain...."],
  "editable_files": ["work/Generated/Job123/SemanticProof.lean"],
  "attempt_budget": 4
}
```

`expected_type` 用于显示；真正 expected type 由生成的 Lean skeleton 固定。

### 12.3 上下文最小化

每次模型调用只提供：

- 目标文件；
- 当前 Lean diagnostics；
- exact declaration signatures；
- 至多若干直接相关实现；
- 可用 helper lemma 搜索结果；
- 禁止修改的 statement/header fence；
- 剩余尝试预算。

不把整个 687 文件库直接塞入 prompt。

### 12.4 Capability-specific skeleton

#### lawfulPresentation

- 固定 semantic problem 与 carrier；
- 要求明确 lawful representation；
- 要求 encoding fidelity/coherence；
- 禁止只用 carrier equivalence 或 metadata 声明相同 presentation。

当前实现使用 `LawfulPresentationTemplate` 固定 exact role/source/target，并同时固定 structural
origin、executable、alphabet equivalence、encoding coherence 与 semantic correctness。生成 bundle
必须提供 exact structural certificate 作为 primary capability，并由同一 template 派生
`CertifiedReduction` route；validator 同时检查两个声明，错误 role、错误 representation index 或
错误 route endpoint 均拒绝。

#### primitive

- 固定 source/target lawful representations；
- 先定义纯函数；
- 再构造 exact `Program.Primitive`；
- direct-TM witness 缺失时保持 `.directTM` blocker，不能用裸 cost map 替代。

当前实现使用 `PrimitiveAdmissionTemplate` 固定 exact role/source/target、已有 executable、依赖于该
executable 的 `TMPolyTimeMap` 与 semantic correctness。生成 bundle 的 primary capability 必须是该
exact executable 的 `Program.Primitive`；derived route 通过显式 `primitive.run = template.run` 将语义
证明重新索引到同一 executable。错误 endpoint、第二个 map 或 cost-only facade 均不能通过 bundle
validation。

#### semanticProof

- statement 固定为同一 program 的接受性等价；
- 模型只能修改 proof body；
- 禁止定义第二个 map 绕过 program index。

#### verifierProgram

- 固定 problem、witness representation 和 checker input shape；
- checker 必须进入 `CertifiedVerifier`；
- 后续 discipline 必须索引到同一个 verifier。

#### verifierEncodingDiscipline

- 必须提供 checked parse/decode/suffix validity；
- backend `TMInNP`、裸 injectivity 或 decoder 名称不能满足任务。

#### unresolvedFamilyPremise

- 只实例化已注册 parameterized family；
- premises 必须是闭合 Lean term；
- 实例化结果重新按普通 certificate candidate 验证。

### 12.5 尝试循环

每个 task 的 bounded loop：

1. 生成固定 skeleton；
2. 编译目标文件；
3. 收集首批 diagnostics；
4. 搜索局部/mathlib lemma；
5. 模型只对当前 editable files 提交源码或 patch；
6. 重新编译该文件；
7. 成功后运行 candidate type validation；
8. 失败则记录 attempt，并在预算内继续；
9. 预算耗尽后返回原 exact blocker 与 diagnostics summary。

不得在同一 attempt 中同时改 request、target、多个无关 route module 和 registry aggregate。
多阶段完整归约由 runner 按 typed dependency 顺序逐个推进，而不是由模型越权同时修改整个库。

## 13. 生成文件与隔离

每个 job 使用内容寻址目录：

```text
.reduction-agent/jobs/<job-id>/
  Goal.lean
  Probe.lean
  Artifact.lean
  report.json
  events.jsonl
  commands/
  model/
  work/
    Generated/<job-id>/...
  receipts/
```

规则：

- job 默认不修改 production library；
- candidate 模块从 job workspace 编译并被 final Artifact 显式导入；
- 只有人工确认或单独 promotion 命令才能把成功 candidate 移入 production registry；
- 并发 job 不共享可写 candidate 文件；
- API key 不进入目录、日志或 report；
- report 中命令输出需要长度限制，但原始完整日志可单独保存。

## 14. 验证关卡

### 14.1 每个候选文件

1. `lake env lean <candidate-file>`；
2. 目标 capability 的 exact type check；
3. 禁止 `sorry`、`admit`、`sorryAx`、新 `axiom`；
4. 禁止修改 statement/header fence；
5. candidate attribute discovery 后重新执行 type-directed validation。

### 14.2 最终 artifact

1. 重新 import input module、runtime、aggregate 和 candidate modules；
2. 重新 elaboration exact source、membership、target 与 request；
3. ClosedResolver 重新搜索并验证 path；
4. 结果必须具有精确 `TypedAutoReductionResult request` 类型；
5. 对本地 Cook-Levin root、新 candidate 和 final result 执行标准公理 gate；
6. 独立 sorry scan；
7. 保存 artifact hash 和当前 registry fingerprint；
8. 在不再次调用模型的情况下重新运行 final resolution，确认路线、类型与输出稳定。

### 14.3 Definition of verified

只有同时满足以下条件才设置 `status = verified`：

- final Lean command exit code 为 0；
- exact request type check 通过；
- standard axiom gate 通过；
- sorry scan 通过；
- final resolver 没有消费 JSON route 或模型 theorem name；
- report 的 artifact hash 与磁盘文件一致。

## 15. 失败分类

### 15.1 Blocked

表示可信层给出了稳定缺口，但当前策略无法补齐：

- `missing_lawful_presentation`；
- `missing_primitive`；
- `missing_semantic_proof`；
- `missing_direct_tm`；
- `missing_verifier_program`；
- `missing_verifier_discipline`；
- `missing_native_membership`；
- `missing_native_completeness`；
- `unresolved_family_premise`；
- `no_registry_path`；
- `authoring_budget_exhausted`；
- `required_model_unavailable`。

### 15.2 Failed

表示基础设施或输入错误：

- module/source/membership declaration 不存在；
- 输入声明类型不符或不闭合；
- aggregate 未导入；
- generated source 语法错误；
- Lean timeout/crash；
- schema/version 不兼容；
- event log 或文件 hash invariant 失败；
- final resolver 与 probe snapshot 不一致且重试后仍失败。

每个 failure 包含 `phase`、`code`、`retryable`、`evidence` 和建议的下一步，但建议
不自动扩大权限。

## 16. 测试矩阵

### 16.1 正例

1. source 已有一条 registry 路线；
2. source = target，生成 reflexive path；
3. source 有 native membership，经 Cook-Levin 到 structured 3SAT；
4. Cook-Levin root 再组合 production suffix；
5. 多条路线稳定选择最小 cost；
6. final-composition edge 仅在同端点无 atomic route 时作为 fallback；
7. exact target 已有 native membership；
8. `proveInNP` 取得 exact membership；
9. `proveNPComplete` 直接取得 exact completeness；
10. `proveNPComplete` 通过 canonical root + path + target membership transport；
11. parameterized family premises 被闭合并形成新 validated edge；
12. 已有闭合路线在任何 authoring policy 下均不调用模型；
13. 一个 bounded model authoring task 生成新候选、进入临时 registry 并完成 final resolution；
14. 一个隐藏 gold proof、registry 中无现成路线的样例输出完整 reduction bundle 与 Lean artifact。

### 16.2 负例

1. carrier 相同但 representation 不同；
2. source term 正确但 membership 属于另一个 defeq 不成立的 presentation；
3. attribute 标记在错误类型声明上；
4. theorem name 或 JSON 声称存在 edge，但 registry 无对应 capability；
5. backend `TMInNP` 试图进入 native Cook-Levin lane；
6. verifier 存在但缺 encoding discipline；
7. target 有 route 但无 native membership；
8. input module 输出伪造 probe marker；
9. 模型发明不存在的 theorem/helper declaration；
10. 模型尝试修改固定 statement、endpoint、request 或 editable-file fence 外文件；
11. probe 后 registry 改变；
12. probe 后 input 文件改变；
13. candidate 含 `sorry`、新 axiom 或错误 endpoint；
14. candidate 编译通过但未通过 registry canonical-head classification；
15. final artifact 类型与原 request 不一致；
16. DeepSeek/API timeout；
17. deterministic replay 产生不同 route ID；
18. 两个并发 job 尝试写同一 candidate 路径。

### 16.3 回归命令

计划中的最终回归入口：

```bash
cd Lean
lake build ComplexityReduction
lake env lean Reference/ComplexityReduction/Agent/Hardness/Regression.lean

cd ..
python3 -m pytest -q tests
python3 scripts/run_hardness_benchmark.py \
  --manifest Benchmark/Hardness/MANIFEST.json \
  --planner deterministic \
  --authoring disabled
```

模型 authoring benchmark 必须作为独立 suite 运行并单独报告，不得把确定性 existing-route
通过率与 LLM synthesis 通过率混为一个数字。API/key/model 连通性另设不启动 Lean 的最小 smoke；
它不能替代端到端 Lean authoring benchmark。

## 17. 分阶段实施

### Phase 0：命名与 resolver 稳定化

目标：在当前 `ComplexityReduction` 架构下恢复可运行的 deterministic closed resolver。

任务：

- 修复 `productionAggregateModule`；
- 添加 `source = target` 的 refl 分支；
- 用带 penalty 的完整 edge search 替换全局 `atomicFirst` 过滤；
- 添加 aggregate 缺失、refl、atomic/final fallback 回归；
- 将 runtime import、command、tactic 和测试从旧 V2 namespace 迁移；
- 决定 attribute 名迁移策略：默认建立新 canonical 名，只有明确外部兼容需求时保留旧 alias；
- 保证 `lake build ComplexityReduction` 与 resolver regression 通过。

验收：

- current aggregate 可被实际 runtime 检测；
- refl path 原子数为 0；
- final-composition edge 不再被无关 atomic edge 全局删除；
- 非 Legacy 主源码与新 agent 源码中无 `ComplexityReduction_IR.V2`。

### Phase 1：无模型 deterministic MVP

目标：完成 input module -> probe -> route -> artifact -> verified 的纯确定性闭环。

任务：

- 实现 declaration-name-only InputGate；
- 禁止 raw input source 拼接；
- 为 native target 建立 stable presented-problem handle；
- 定义 versioned probe records；
- 定义 GoalIR、RouteIR、CommandResult、AgentResult；
- 实现 content-addressed job 目录和状态机；
- 实现固定 Artifact emitter；
- 实现 report、events 和 resume；
- 覆盖已有路线、refl、目标不可达和 stale snapshot 测试。

验收：

- 完全离线执行；
- 相同输入连续运行产生相同 route ID 和等价 Artifact；
- runner 报告 route 不能使错误 artifact 通过 final resolver；
- resume 后仍重新编译 final artifact。

### Phase 2：Native Cook-Levin lane

目标：exact `NativeTMInNP source` 可进入 canonical structured 3SAT 并继续搜索。

任务：

- 将 Cook-Levin root 移入 `Certificate/NativeCookLevin.lean`；
- 固定 exact source/membership type check；
- 生成 job-local attributed ingress edge；
- structured 3SAT 可直接成为 target；
- 支持 structured 3SAT 后缀路线；
- 对 root 与 final result 执行标准公理 gate；
- 增加 wrong-membership、backend-only 和 missing-discipline 负例。

验收：

- exact native source 到 structured 3SAT 通过；
- root + 至少一条 production suffix 通过；
- backend-only membership fail closed；
- `sorryAx` 进入 root 传递依赖时 artifact 失败。

### Phase 3：Typed blocker 与 gap planning

目标：失败从字符串升级为可调度但不授予能力的 typed gap。

任务：

- 实现 Lean-side Gap classifier；
- 将 `ClosedResolver.Failure` 与 `MissingCapabilityReason` 建立明确映射；
- 输出 GapIR；
- 实现 blocker 的稳定状态和 resume 行为；
- 生成只包含 exact endpoint、role 和 expected capability 的 task packet；
- 无法细分时保留 `noRegistryPath`。

验收：

- representation mismatch、missing primitive、missing membership 可区分；
- runner 无法通过修改 GapIR 把 blocked 任务变成 success；
- 同一 environment 下 gap ID 稳定。

### Phase 4：低风险 authoring vertical slices（已完成）

目标：打通 authoring 基础设施，先处理低风险的 closed family/presentation 任务。

优先顺序：

1. `unresolvedFamilyPremise`：闭合已有 parameterized family；
2. `lawfulPresentation`：补精确结构化 presentation；
3. 已有 executable 的 `primitive` admission。

任务：

- 实现 AuthoringTask、attempt budget 和 editable-file boundary；
- 生成固定 Lean skeleton；
- 接入 per-file Lean diagnostics；
- 成功后运行 static scan 与 canonical-head validation；
- 将 candidate module 加入 job-local final import；
- 重新 scan 和 final resolve；
- 暂时使用 deterministic/template author，不要求模型。

验收：

- 至少一个 benchmark 从 typed blocker 经局部 candidate 变为 verified；
- candidate 不修改 production library；
- 删除 candidate 后 resume 回到原 blocker；
- candidate endpoint 不匹配时 validation 失败。

完成结果（2026-07-28）：

- `unresolvedFamilyPremise`、`lawfulPresentation`、已有 executable 的 `primitive` admission 三条 lane
  均已实现 deterministic skeleton；
- Probe 只输出与 gap role/source/target 精确匹配、且绑定 nonce 与 registry fingerprint 的 template
  observation；
- lawful bundle 验证 exact structural certificate + derived route，primitive bundle 验证 exact
  `Program.Primitive` + 使用该 primitive 的 derived route；
- 三个正例均从原 blocker 到达 `VERIFIED`，三个 candidate-absent resume 均恢复原 blocker；
- authoring suite 6/6、Phase 4 全量 benchmark 20/20、模型调用 0。

### Phase 5：program-indexed reduction authoring 管线（确定性模板，已完成）

目标：支持 `primitive -> semantic proof -> directTM -> CertifiedReduction` 的分步构造，
建立未来模型 authoring 所需的类型边界、文件隔离和验证关卡。本阶段不以 LLM 生成能力为验收目标。

任务：

- 为每种 capability 建独立 skeleton；
- 固定 statement/header，并预留未来模型只能修改 proof body 或指定定义区的 fence；
- 建立 helper lemma search 与 diagnostics feedback；
- 每阶段单独 checkpoint；
- 语义 proof 强制引用同一个 program；
- direct-TM 缺失时不接受 cost-only facade；
- 最终 certificate 加 attribute 后重新验证；
- 增加 bounded retry、timeout 和 budget exhaustion。

验收：

- 一个小型新 map 能完成完整 program-indexed certificate；
- 换用第二个 map 的语义证明无法通过类型；
- 缺 direct-TM 时保持 typed blocked；
- authoring 失败不会污染 registry 或后续 job。

完成结果（2026-07-28）：

- 新增 canonical 七阶段 bundle：`executable`、`executable_direct_tm`、`primitive`、`program`、
  `semantic_proof`、`direct_tm`、`certified_reduction`；每阶段独立编译、记录 source/fence hash、
  保存 diagnostics、执行 standard-axiom gate，并写入独立 checkpoint；
- Probe 观察 `ProgramIndexedReductionTemplate` 时输出三个独立 component declaration handle；
  generated stage 只引用自己需要的 component，从声明依赖层面隔离 executable/direct-TM/semantic；
- dedicated Lean bundle validator 检查 exact source/target、canonical head、primitive 对 executable 的
  绑定、program 对 primitive 的绑定，以及 semantic/direct-TM/route 对同一 program 的绑定；
- program direct-TM checkpoint 的 head 必须是 dependent `TMPolyTimeMap`，cost-only facade 无法通过；
- deterministic candidate 按稳定 observation 顺序 bounded retry；每次 retry 前清除该 bundle 全部阶段
  源码和 `.olean`，前一 attempt 的 diagnostics 与逐阶段结果保留在审计记录中；
- resume integrity 从单文件 hash 升级为有序 stage-bundle hash；任一阶段缺失或改变都会由当前 Lean
  environment 恢复原 typed blocker，而不会复用 stale `.olean` 或静默重新 author；
- `program-indexed-reduction-authoring` 从 `missing_semantic_proof` 到达 `VERIFIED`，最终 route 恰为
  1 atom；`program-indexed-retry-isolation` 第一次只在 `semantic_proof` gate 失败，第二次七阶段通过；
- `missing-direct-tm-authoring-blocker` 保持 `BLOCKED / missing_direct_tm`，candidate-absent resume 保持
  `BLOCKED / missing_semantic_proof`；Phase 5 isolation suite 4/4、模型调用 0；
- Python regression 为 70/70，Lean aggregate regression 继续覆盖 wrong-program semantic/direct-TM/route、
  cost-only facade 和 poisoned semantic dependency isolation。

因此，“Phase 5 已完成”只表示完整 reduction bundle 可以由受控 authoring 管线构造并验证，
不表示 DeepSeek 已经能够从未知题面生成该 bundle。

### Phase 6：Membership 与 completeness lanes（已完成）

目标：闭合 `proveInNP` 与 `proveNPComplete`。

任务：

- resolver 支持 exact `proveInNP`；
- 新增 `CompletenessTransport.lean`；
- 支持 exact registered completeness；
- 支持 canonical complete hub -> target path + target membership transport；
- 增加 verifierProgram、witnessPresentation、discipline authoring skeleton；
- 对 completeness result 执行独立 axiom gate。

验收：

- 三种结果严格区分：只有 reduction、reduction+membership、native completeness；
- 没有 target membership 时不能得到 completeness；
- 方向错误的 `target -> 3SAT` 不能证明 target hardness。

完成结果（2026-07-28）：

- `TypedAutoReductionResult` 为 `proveInNP` 与 `proveNPComplete` 保留 exact typed evidence，runner 通过
  `#hardness_probe_in_np` 与 `#hardness_probe_np_complete` 观察同一次 Lean-side resolution；
- closed resolver 支持 exact registered native membership、exact registered native completeness，
  以及 canonical native-complete hub 经 validated forward path 到 exact native-NP target 的 completeness
  transport；结果 kind 分别为 `native_membership`、`registered_completeness`、
  `transported_completeness`；
- 新增 `Certificate/CompletenessTransport.lean`，构造器签名只接受 `hub -> target` 的
  `CertifiedPath` 和 target `NativeTMInNP`，反向路径在类型层面无法进入；
- membership deterministic authoring 固定四阶段 bundle，并由 dedicated Lean validator 检查 exact
  problem、canonical capability head、witness presentation 与 discipline 的同 verifier 索引；
- completeness 结果对提取出的 `NativeTMNPComplete` 运行独立 standard-axiom gate；带自定义 axiom 的
  completeness artifact 被回归测试明确拒绝；
- Phase 6 Lean regression 覆盖 exact membership/completeness、3SAT-to-Clique 单原子 transport、缺
  target membership、错误方向、backend completeness 隔离和 poisoned completeness axiom gate；
- membership suite 3/3、completeness suite 5/5，`case_outcome_accuracy`、相应 native rate、正负例
  准确率、axiom clean 与 deterministic replay 均为 1.0，模型调用 0；
- Python regression 更新为 78/78；Phase 6 input modules、aggregate regression 与全量 Lake build
  均通过。

### Phase 7：DeepSeek Lean authoring 与端到端归约生成（必需，实施中）

目标：在 Phase 0--6 的可信边界内，实现“输入 Lean 题面，输出完整归约与 Lean 代码”的
用户目标。模型负责创造缺失源码，Lean 负责验证；已有路线复用仍保持纯确定性。

截至 2026-07-29，route reranking 已从核心 planner 删除；DeepSeek API-only smoke、
`hardness_model_patch_v1` 单区域协议、diagnostics bounded retry、七阶段 program-indexed bundle、
隐藏 gold `model-authoring` suite、分 lane 指标、三次稳定性 trial runner 和并发 job lock 已落地。
API-only smoke 已真实返回 HTTP 200 与 usage；首个真实 `deepseek-v4-flash`
`model-required` 隐藏样例在 3 次受限模型调用后由 Lean 接受，完整 bundle、fresh scan、
ClosedResolver、standard-axiom gate 和 deterministic replay 全部通过，最终状态为
`VERIFIED`。该运行使用 12,297 tokens，artifact SHA-256 为
`17d33d96b0cc5befb319d40e0f57fc2d5940dd56ac6db1c23f7787ea19c468bb`，随后 Python 回归
106/106 通过。随后的独立 `model-auto` 运行也在无 deterministic fallback 的情况下到达
`VERIFIED`：第 4/4 次受限修复被 Lean 接受，总 usage 为 15,942 tokens，并产生相同
artifact hash。Phase 7 仍需两种 policy 至少各补 2 次同配置隔离运行并生成正式 trial
aggregate，才形成各三次的稳定性证据；
当前单次端到端耗时约 44--63 分钟，主要瓶颈是 Lean 冷启动而非模型 API。

任务：

- 删除核心流程中的 route reranking；废弃 `--planner auto/model-required` 的模型选路语义；
- 将已有路线策略与 authoring 策略分离：route 始终 deterministic，模型模式只由
  `--authoring model-auto|model-required` 控制；
- 增加不启动 Lean 的 DeepSeek API smoke，验证官方 base URL、local key、
  `deepseek-v4-flash`、HTTP 状态和 usage，但绝不输出 key；
- exact typed gap 出现后，由 runner 确定性选择下一个 task；模型不得选择 task ID 或 route ID；
- 为 DeepSeek 提供题面、固定 skeleton、exact signatures、相关 helper、当前 diagnostics 和剩余预算；
- LeanAuthor 只能修改 task 的 editable files/regions，并将模型响应落为可审计 patch；
- 实现 `生成 -> 单文件编译 -> diagnostics 回传 -> 修正` 的 bounded loop；
- 按 typed dependency 顺序支持多阶段 bundle，使一次 end-to-end job 最终输出完整 reduction；
- 每个成功 stage 重新做 exact type validation、canonical-head classification 和 axiom gate；
- 最终 fresh scan、ClosedResolver、Artifact compile 和无模型 replay 不信任任何模型声明；
- 记录模型、base URL（不含 key）、token、响应 hash、attempt、diagnostics 和费用信息；
- API failure 时，`model-auto` 只在存在受控 deterministic template 时回退，否则保持原 blocker；
  `model-required` 返回 `required_model_unavailable` 或 `authoring_budget_exhausted`；
- 复用 Lake build 与 Lean environment，避免每个 stage/API 调用前重复冷加载整个库；
- 增加 prompt injection、虚构 theorem、越权文件、改写 endpoint、`sorry`/axiom 和 stale candidate 测试；
- 建立隐藏 gold proof 且 production registry 无现成路线的独立 model-authoring benchmark suite；
- 对模型关闭时继续运行完整 Phase 1--6 deterministic benchmark。

验收：

- existing-route/refl/Cook-Levin 闭合样例全部 `model_called = false`；
- API smoke 在不运行 Lean 的情况下确认 `deepseek-v4-flash` 的真实调用和 usage；
- 至少一个 registry 中无现成路线、gold proof 对 agent 隐藏的样例，由 DeepSeek 实际生成新的
  Lean 源码并最终 `VERIFIED`；
- 成功报告包含完整 reduction bundle，而不只是 route ID 或自然语言方案；
- 生成源码不导入 gold proof，不含 `sorry`/新 axiom，并通过 exact request 与 standard-axiom gate；
- 编译错误能够反馈给模型并在 bounded retry 内形成可审计修正；
- 关闭模型不影响 Phase 1--6 已有确定性能力；
- 任意非法模型响应最多导致 fallback、blocked 或 failed；
- 模型无法改变 final request 或绕过 Lean validation。

## 18. 里程碑

### M1：可信路线复用可运行

- Phase 0-1 完成；
- deterministic existing-route benchmark 通过；
- 无旧 V2 runtime 名称；
- report 与 resume 可用。

### M2：任意 exact native-NP source 可接 canonical 3SAT

- Phase 2 完成；
- Cook-Levin root 与 suffix composition 通过；
- standard axiom gate 通过。

### M3：失败可被精确调度

- Phase 3 完成；
- blocker 不再只有自由文本；
- authoring task 可稳定复现。

### M4：首个局部能力自动补齐（已达成，2026-07-28）

- Phase 4 完成；
- job-local candidate 从 blocker 推进到 verified；
- promotion 仍需独立操作。

### M5：program-indexed authoring 基础设施（已达成，2026-07-28）

- Phase 5 完成；
- program、semantic proof、direct-TM 和 certificate 可由确定性 fixture 分阶段闭合；
- 不声称已经完成 LLM synthesis。

### M6：exact hardness/membership/completeness 可信闭环（已达成，2026-07-28）

- Phase 6 完成；
- `reduceTo`、`reduceToKnownNP`、`proveInNP`、`proveNPComplete` 全覆盖；
- deterministic resolver、authoring fixture 和 axiom audit 全覆盖。

### M7：LLM 端到端归约生成（进行中）

- Phase 7 完成；
- DeepSeek 能从 typed gap 生成并修复完整 reduction bundle；
- 已有路线不调用模型，未知路线才进入 authoring；
- 模型不在可信计算基中，真实隐藏样例通过最终 Lean 验证。

## 19. 风险与控制

### 19.1 Registry import 闭包遗漏

风险：合法声明未进入 aggregate，agent 误判缺失。

控制：aggregate 作为显式环境前提；报告未扫描模块；为 promotion 提供检查命令；不把未导入
候选自动视为可信。

### 19.2 Definitional equality 性能

风险：大图上逐边 `whnf + isDefEq` 成本高。

控制：先保持正确性；记录扫描和比较次数；需要时增加非权威 hash bucket，但最终连接仍走
`isDefEq`。

### 19.3 Pretty term 不可重放

风险：probe 字符串无法在 artifact 中重新 elaboration。

控制：只输出/消费 stable declaration handles；pretty term 仅显示。

### 19.4 Authoring 修改范围扩大

风险：模型为解决一个 gap 修改 request 或无关库文件。

控制：固定 editable-file allowlist、header fence、patch 审计和 job-local workspace。

### 19.5 编译通过但信任策略失败

风险：candidate 使用 `sorryAx`、额外 axiom 或 backend-only shortcut。

控制：static scan + canonical type validation + final standard axiom gate；三者缺一不可。

### 19.6 缓存陈旧

风险：input、registry 或 toolchain 改变后复用旧 verified 结论。

控制：content-addressed job、dependency hashes、fingerprint invalidation 和 final replay。

### 19.7 模型调用投入产出低

风险：在已知路线排序上消耗模型预算但没有提升能力。

控制：禁止已知路线调用模型；route search 永远 deterministic。模型预算只用于 exact typed gap
对应的 Lean 源码生成和 diagnostics 修正。

### 19.8 把确定性 fixture 通过率误报为模型能力

风险：Phase 4--6 的 deterministic-template benchmark 全部通过，但真实 DeepSeek 从未生成源码，
却被表述为 agent 已具备 LLM reduction synthesis。

控制：报告强制区分 `deterministic_fixture`、`model_generated` 和 `existing_route`；分别报告
`model_called`、真实 token usage、生成文件来源与 suite 通过率。没有真实 API 调用和隐藏 gold
样例时，不得声称 LLM authoring 已完成。

## 20. 下一批实施任务（Phase 7）

建议按以下顺序实施：

1. 移除模型 route reranking，把 existing-route 分支固定为 deterministic 且断言
   `model_called = false`；
2. 拆分 CLI/config：保留 deterministic route policy，新增独立
   `model-auto`/`model-required` authoring policy；
3. 实现不经过 Lean 的 DeepSeek `deepseek-v4-flash` API smoke；
4. 定义模型 authoring 请求/响应协议，使响应只能映射到当前 editable file/region；
5. 先在一个 `missing_semantic_proof` 隐藏 gold 样例上打通真实
   `prompt -> patch -> compile -> diagnostics -> retry`；
6. 扩展到七阶段 program-indexed bundle，最终输出完整 `CertifiedReduction`；
7. 再接 membership/completeness 的 verifier bundle authoring；
8. 建立独立 model-authoring benchmark 与指标，禁止混入 deterministic suite 通过率；
9. 优化 Lean 冷启动：统一 preflight、复用 build 产物，并评估 persistent environment/单进程多阶段；
10. 完成越权、虚构声明、prompt injection、API timeout、budget exhaustion 和 axiom poisoning 回归；
11. 在真实 DeepSeek 环境运行隐藏样例，并保存不含 secret 的完整审计报告。

本阶段不引入通用多-agent 协作、数据库或分布式队列；先证明单模型、单 job 能可靠生成并验证
完整归约。

## 21. 完成标准

整个计划完成时，应满足：

- 单一 `ComplexityReduction` Lean 库包含所有可信定义和 agent runtime；
- 现有路线和 Cook-Levin 路线可在无模型环境确定性完成；
- 现有闭合路线永不为 route selection 调用模型；
- 四种 request objective 都有 exact resolver lane；
- 无路线时能产生 exact typed blocker；
- typed gap 能触发 DeepSeek 在 job-local editable files 中生成和修复源码；
- 至少一个隐藏 gold、registry 无现成路线的样例由真实模型生成完整 reduction bundle 并通过；
- 模型不能选择 route ID、theorem name 或授予 capability，只能修改允许的候选文件；
- 最终 artifact 始终由当前 Lean environment 重新构造；
- 所有成功 artifact 通过 kernel、exact request type、sorry scan 和 standard axiom gate；
- benchmark 分别报告 existing-route、deterministic fixture 和 model synthesis，通过率不得混算；
- API smoke 与端到端 Lean benchmark 分离，二者都必须有真实运行证据；
- benchmark 同时包含 representation、membership、registry、模型越权和 stale-cache 负例；
- JSON、fingerprint、日志、模型响应和 runner 均不属于证明可信计算基。
