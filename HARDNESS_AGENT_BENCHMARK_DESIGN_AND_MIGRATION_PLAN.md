# ComplexityReduction Hardness Agent Benchmark 设计与迁移计划

> 状态：迁移主体已完成；Phase 0--6 确定性 benchmark 已落地；Phase 7 进入架构拆分修订。
> 已完成的七阶段 model-authoring 实验保留为可选能力证据，不再作为默认 hardness reducer
> 的运行路径；后续先完成 Core Reducer、Optional Authoring、Benchmark/Release Audit 三层分离。
>
> 日期：2026-07-29
>
> 本次修订：2026-07-29，按“优先直接引用库中已有定理”的产品目标收缩默认运行链。
>
> 关联实现计划：`HARDNESS_AGENT_IMPLEMENTATION_PLAN.md`（待下一步同步；与本次三层拆分冲突时，
> 以本文第 1--15 节和 B5 修订为准）
>
> 当前正式 benchmark 根：`Benchmark/Hardness/`

## 1. 文档目的

本文定义 hardness agent 的端到端 benchmark，并给出从 `../LeanAutoReduction/Benchmark/`
迁移而来的旧 benchmark 的系统改造计划。

产品层默认目标是一个**库复用优先的自动 hardness 归约器**：

```text
输入一个可导入的 Lean 题面模块
        |
        v
从预构建 typed declaration index 检索库中已有 theorem/capability
        |
        v
直接匹配、插入 adapter 或确定性组合多跳 reduction
        |
        v
生成最小 Artifact.lean，显式 import 并引用已选库定理
        |
        v
一次 Lean kernel 编译 + exact request type + final standard axiom gate
```

默认 Core Reducer 不负责发明新的 reduction。若库中没有可用定理或可组合路线，它必须返回
精确 typed blocker；只有用户显式选择新边创作模式时，才进入 authoring 子系统。

本计划把原先混合在同一 runner 中的职责拆为三层：

| 层 | 默认启用 | 职责 | 正常 Lean 进程预算 |
| --- | --- | --- | --- |
| **Core Reducer** | 是 | 库定理索引、typed retrieval、直接引用、adapter 与多跳组合、最终编译 | 共享 preflight 后每 case 1 次 |
| **Optional Authoring** | 否 | 无库路线时显式创作一条新 capability；可使用 deterministic template 或模型 | 按 authoring task 单独统计 |
| **Benchmark/Release Audit** | 否 | hidden gold、oracle isolation、fresh scan、stale-cache、独立 replay 与发布收据 | Core 结果上额外 1 次 replay，安全负例除外 |

Core Reducer 允许最终 Lean 源码显式引用 typed index 选出的库 theorem name；这些名字只是
代码生成输入，只有最终 Lean elaboration/typecheck 成功才授予能力。禁止的仍是把未验证 JSON、
模型声称或不存在的 theorem name 当作证明。

Core、authoring 和 release audit 必须分开运行、分开计时、分开统计。模型不参与 Core route
选择，也不得因 Core 无路线而被隐式调用。

本文不把旧 benchmark 的通过记录视为新 Agent 的成绩。旧数据只有在完成类型、模块、manifest、
验证器和可信边界迁移后，才能进入正式评测。

## 2. 当前基线与审计结论

### 2.1 当前正式 benchmark

- 唯一正式入口为 `Benchmark/Hardness/MANIFEST.json`，schema 为 `hardness_benchmark_v2`；
- case 按 smoke、routes、Cook-Levin、gaps、authoring、Phase 5、membership、completeness、negative
  和 security suite 组织；
- Lean 输入模块位于 `Lean/Reference/Benchmark/Hardness/Inputs/`；
- 当前 inventory 有 32 个 runnable case；
- Phase 6 membership suite 已实测 3/3，completeness suite 已实测 5/5，模型调用均为 0；
- 上述是两次独立运行，不得表述为尚未实际执行的单次 32/32。

### 2.2 Legacy 数据状态

- 原 `Benchmark/MANIFEST.yaml`、`Benchmark/Samples/`、`Benchmark/HiddenTargets/`、
  `Benchmark/GoldProofs/` 和 `Benchmark/V2Hardness/` 活动路径已经删除；
- 110 个旧 case 的原始材料、SHA-256 与逐项处置保存在 `Benchmark/Hardness/Legacy/` 和
  `Benchmark/Hardness/MIGRATION_LEDGER.json`；
- legacy 文件只用于 provenance/oracle，不进入正式 manifest、模型 workspace 或通过率；
- 当前事实来源是 `Benchmark/Hardness/README.md`、manifest 与实际 `report.json`；
  `MIGRATION_STATUS.md` 及本文件后部的 L0--L15/B0--B4 内容保留为历史迁移记录，B5 已改为
  三层拆分、Core 快速路径和后续 model-synthesis 发布计划。

### 2.3 架构偏差与修订决策

现有实现把 benchmark 级别的防御和新能力 authoring 放进了普通 existing-route 路径，产生了
以下偏差：

1. discovery 主要依赖 attribute registry；库中已经存在但未注册为 canonical capability 的 theorem
   可能不可见；
2. 一旦 registry 无路线，runner 倾向进入多阶段 authoring，而不是先完成全库 typed retrieval；
3. `Goal`、`Probe`、revalidation、`Artifact` 和 replay 分别启动 Lean，导致普通库复用也承担
   发布级审计成本；
4. 七阶段 bundle 是“创作新 reduction”的内部协议，却被误当成自动 hardness reducer 的默认产品形态。

修订决策：Phase 7 后续首先实现库定理索引与 Core 快速路径；现有七阶段实现保留，但下沉为
显式 Optional Authoring。三次模型稳定性 trial 在三层边界落地前不作为 Core Reducer 发布门槛。

## 3. Benchmark 设计目标

### 3.1 Core Reducer 必须覆盖的产品能力

Core benchmark 必须优先覆盖：

1. exact Lean `PresentedProblem` 输入；
2. 预构建 typed declaration index 能发现库内直接 theorem、registered capability 及其 import；
3. source 与 target definitionally equal 的 reflexive path；
4. 已有直接 reduction theorem 的显式引用；
5. 已有多跳 route 的确定性搜索与 `trans` 组合；
6. presentation/encoding equivalence 与 adapter 的库内复用；
7. exact `NativeTMInNP source` 驱动的 checked Cook–Levin；
8. `reduceTo`、`reduceToKnownNP`、`proveInNP` 和 `proveNPComplete`；
9. 输出最小、可独立编译的 `Artifact.lean`；
10. 最终结果通过 exact type、kernel 与 standard axiom gate；
11. 库内无路线时返回稳定 typed blocker，不自动调用模型；
12. 共享 preflight 后普通 case 只启动一次 Lean 编译。

### 3.2 Optional Authoring 覆盖的能力

以下能力属于独立 opt-in authoring lane，不计入 Core Reducer 通过率：

1. presentation/encoding adapter 的新建；
2. executable primitive/program 的新建；
3. program-indexed semantic proof；
4. direct-TM/polytime evidence；
5. 新 `CertifiedReduction` 或 native membership bundle；
6. deterministic template authoring；
7. DeepSeek 对单个 typed gap 的 fenced patch 与 bounded repair。

Core 返回 blocker 后，只有显式 `author-new-edge` 策略才能进入本层；禁止 `auto` 隐式升级。

### 3.3 Benchmark/Release Audit 覆盖的能力

以下能力由严格评测 wrapper 负责，不进入普通 Core 每次运行：

- hidden gold 与 oracle isolation；
- baseline/final fresh scan；
- registry fingerprint 和 stale-cache 检查；
- candidate 删除、resume 与并发隔离；
- prompt injection 与非法模型响应；
- 独立 deterministic replay；
- 发布用 verification receipt 与重复稳定性 trial。

### 3.4 不作为 hardness benchmark 主任务的能力

以下能力应放在独立 formalization benchmark，而不是混入本 benchmark 的通过率：

- 从纯自然语言发明 source 的 Lean 定义；
- 从裸 `DecisionProblem` 猜测编码；
- 任意数学定理证明；
- logspace、counting、approximation、randomized 或 optimization reduction；
- 允许模型改变题面、objective 或 exact endpoint；
- 将一个 JSON route、theorem name 或模型结论当作证明。

自然语言描述可以作为辅助 metadata，但正式输入必须已经包含可 elaboration 的 Lean 声明。

## 4. 核心可信不变量

可信不变量按执行层作用，禁止把严格层要求无条件施加到 Core。

### 4.1 Core Reducer 不变量

1. **Formal input only**：正式题面是 importable Lean module。
2. **Exact endpoint**：source/target 是闭合 `PresentedProblem` declaration，连接只依赖受控
   definitional equality。
3. **Typed index, kernel authority**：declaration index 只负责搜索；最终 import、theorem name、
   参数和组合项必须由 Lean elaboration/typecheck 确认。
4. **Library reference allowed**：Artifact 可以显式引用 index 选出的库定理，不要求它先被包装成
   job-local 七阶段 capability。
5. **Deterministic route**：相同 index、goal 和 cost policy 产生相同直接/多跳路线。
6. **Fail closed**：没有可编译路线时返回 typed blocker，不隐式调用模型。
7. **Minimal final verification**：成功只要求最终 Artifact 通过 exact type、kernel 和传递性
   standard axiom gate。
8. **No oracle dependency**：Core artifact 不得 import benchmark Gold/HiddenTargets。

### 4.2 Optional Authoring 不变量

1. 只有显式策略才能从 Core blocker 进入 authoring；
2. 一次 task 只闭合一个 typed gap；
3. 模型只能修改 fenced editable body，不能改变 request 或 endpoint；
4. 新 program、semantic proof、direct-TM 和 reduction 必须保持依赖索引一致；
5. 新 capability 必须先通过 candidate/bundle validation，再交回 Core 生成最终 Artifact。

### 4.3 Benchmark/Release Audit 不变量

1. expected、route ID、fingerprint、token usage 和日志不授予 Lean 能力；
2. model workspace 隔离 oracle；
3. strict profile 对 cache、input、candidate 和 registry 做 fresh revalidation；
4. release case 独立 replay 最终 Artifact；
5. Core、authoring、release 指标和进程时间禁止混算。

## 5. Benchmark 总体架构

### 5.1 Core Reducer 默认路径

```text
Public Lean Module + Goal
            |
   Prebuilt Typed Declaration Index
            |
 Direct Match / Adapter / Multi-hop Search
            |
       +----+----+
       |         |
    Route       Typed blocker
       |         |
       v         +--> stop; no model call
 Minimal Artifact Emitter
       |
 One Lean Compile + Final Axiom Gate
       |
 Core Result + Route Report
```

typed declaration index 应离线或在共享 preflight 中构建，记录 declaration name、elaborated type、
canonical head、source/target endpoint、import module 和依赖 hash。它不是证明；最终 Artifact 的
Lean 编译才是权威。

### 5.2 Optional Authoring 扩展路径

```text
Core typed blocker + explicit author-new-edge
                 |
       One typed AuthoringTask
                 |
 deterministic template or fenced model patch
                 |
 candidate compile / bundle validation
                 |
 validated job-local capability
                 |
 return to Core route search and final Artifact compile
```

七阶段 program-indexed bundle 仅属于本路径。它不得成为直接 theorem reuse、registered route 或
multi-hop composition 的前置条件。

### 5.3 Benchmark/Release Audit 包装路径

```text
Shared preflight
      |
Run Core or Explicit Authoring
      |
Fresh scan / fingerprint / oracle checks
      |
Independent Artifact replay
      |
Strict report and verification receipt
```

benchmark runner 负责 case 调度、隔离、预算、严格 profile 和报告；它不能改变 Core 的默认语义。
普通开发与库复用评测使用 `core` profile，发布、安全和 model-synthesis 使用 `strict-release`。

## 6. 建议目录结构

```text
agent/hardness/
  core/
    declaration_index.py
    retrieval.py
    route_search.py
    artifact_emitter.py
  authoring/
    tasks.py
    checkpoints.py
    model_protocol.py
  audit/
    revalidation.py
    replay.py
    receipts.py

Benchmark/Hardness/
  README.md
  MANIFEST.json
  Suites/
    smoke.json                # core_reuse
    routes.json               # core_reuse
    cook_levin.json           # core_reuse
    membership.json           # core_reuse 或显式 authoring case
    completeness.json         # core_reuse
    authoring.json            # optional_authoring
    model_authoring.json      # optional_authoring + strict-release
    negative.json             # core 或 authoring 负例
    security.json             # strict-release
  Expected/
    <case-id>.json
  Legacy/
    Opencode/
      MANIFEST.yaml
      Samples/
      HiddenTargets/
      GoldProofs/
    V2Hardness/
      MANIFEST.json
      Inputs/

Lean/Reference/Benchmark/Hardness/
  Inputs/
    Smoke/
    Routes/
    CookLevin/
    Authoring/
    Membership/
    Completeness/
    Negative/
    Security/
  Oracles/
    Gold/                  # 不进入模型 workspace，不进入 production aggregate
  Regression.lean
```

规则：

- `agent/hardness/core/` 不得 import model client、authoring checkpoint 或 oracle 代码；
- authoring 只能消费 Core 返回的 typed blocker，不得改变 Core goal；
- audit 只能包装 Core/authoring 结果，不得成为普通 Core 成功的前置条件；
- 当前可执行 benchmark 只从 `Benchmark/Hardness/MANIFEST.json` 和 `Suites/*.json` 读取；
- 每个 case 必须声明 `execution_layer`，取值为 `core_reuse`、`optional_authoring` 或
  `release_audit`；
- legacy 数据必须显式放入 `Legacy/`，防止 runner 误把旧 schema 当作当前 case；
- 正式 Lean 输入必须位于当前 Lake 的 `Reference` source root；
- `Expected/*.json` 只存非权威预期状态、gap class 和 coverage metadata；
- Gold Lean proof 只用于 benchmark target sanity，不进入 Agent prompt 或 candidate import path；
- job 输出继续写入 `.reduction-agent/`，不修改 production registry。

## 7. Lean 题面 ABI

### 7.1 固定 target 的 reduction case

```lean
import ComplexityReduction.Agent.Hardness.Runtime

namespace Benchmark.Hardness.Inputs.Example

def source : ComplexityReduction.Encoding.PresentedProblem :=
  ...

@[complexity_reduction_ir_typed_problem]
def target : ComplexityReduction.Encoding.PresentedProblem :=
  ...

end Benchmark.Hardness.Inputs.Example
```

Manifest 使用 fully-qualified declaration name：

```text
module = Benchmark.Hardness.Inputs.Example
source = Benchmark.Hardness.Inputs.Example.source
target = Benchmark.Hardness.Inputs.Example.target
objective = reduce_to
```

### 7.2 开放 native-NP target case

```lean
namespace Benchmark.Hardness.Inputs.ExampleNative

def source : ComplexityReduction.Encoding.PresentedProblem :=
  ...

theorem membership :
    ComplexityReduction.Certificate.NativeTMInNP source :=
  ...

end Benchmark.Hardness.Inputs.ExampleNative
```

Manifest 设置 `objective = reduce_to_known_np`，target 可以为空，由 typed index 与 deterministic
route search 从 validated native targets 中选择 stable presented-problem handle。

### 7.3 Authoring case

Authoring case 是 Core blocker 的**显式后续运行**，不能作为普通 case 的自动 fallback。公共题面
只声明 source、可选 target 和已经允许使用的局部 helper，不能预先暴露完整 reduction theorem
或 gold proof。Core run 必须先产生稳定 typed blocker，例如：

```text
missing_lawful_presentation
missing_primitive
missing_semantic_proof
missing_direct_tm
missing_native_membership
```

随后独立 `optional_authoring` run 才能在 job-local `Generated` 模块中闭合 blocker，并把通过
candidate/bundle validation 的新能力交回 Core emitter。authoring 成功率与 Core 库复用成功率
分开统计。

### 7.4 Completeness case

Completeness case 使用 `objective = prove_np_complete`。输入必须明确 exact problem，并根据 case
类型提供或隐藏以下能力：

- exact library/registered `NativeTMNPComplete problem`；或
- target native membership；
- canonical complete hub 到 target 的 certified path；
- completeness transport 所需的库内定理。

不允许仅凭方向错误的 reduction 或裸 `NPCompleteEnc` 通过。

## 8. Manifest v2 设计

`hardness_benchmark_v2` 增加执行层和验证 profile，默认 case 必须是 Core 库复用：

```json
{
  "schema_version": "hardness_benchmark_v2",
  "suite_id": "hardness-core-routes",
  "cases": [
    {
      "id": "three-sat-to-clique-library-route",
      "execution_layer": "core_reuse",
      "verification_profile": "core",
      "module": "Benchmark.Hardness.Inputs.Routes.ThreeSATExplicitSuffix",
      "source": "Benchmark.Hardness.Inputs.Routes.ThreeSATExplicitSuffix.source",
      "membership": null,
      "target": "ComplexityReduction.Problems.Karp21.GraphAtoms.cliqueStructuredProblem",
      "objective": "reduce_to",
      "target_policy": "fixed",
      "planner": "deterministic",
      "min_agent_phase": 1,
      "authoring_policy": {"enabled": false, "mode": "disabled"},
      "expected": {
        "final_status": "VERIFIED"
      },
      "coverage": {
        "required_resolution_source": "library",
        "forbid_model_call": true,
        "maximum_core_lean_processes": 1
      },
      "resources": {
        "lean_timeout_seconds": 300
      },
      "tags": ["core", "library-reuse", "route"]
    }
  ]
}
```

显式 authoring case 必须改用：

```json
{
  "execution_layer": "optional_authoring",
  "verification_profile": "strict-release",
  "authoring_policy": {
    "enabled": true,
    "mode": "model-required",
    "attempt_budget": 4
  }
}
```

约束：

- `core_reuse` 必须设置 `authoring_policy.enabled = false`；
- `optional_authoring` 必须有稳定 baseline blocker，并显式声明允许的 gap；
- `release_audit` 只包装已有 Core/authoring case，不创建新的数学能力；
- `planner = auto` 不再表示“无路线则调用模型”，Core route policy 只保留 deterministic；
- `verification_profile = core` 不要求 fresh scan/replay；`strict-release` 才要求完整审计。

### 8.1 权威与非权威字段

以下字段只用于编排和评分，不进入 proof：

- `execution_layer` 与 `verification_profile`；
- `expected`；
- `coverage`；
- `tags`；
- `legacy_provenance`；
- token/time budget；
- route count/atom count；
- model reason。

真正的 expected type 由输入 declaration 和最终 Artifact 固定。typed index 提供的 theorem name、
import 和 route plan 可以写入生成源码，但必须由 Lean 重新 elaboration；manifest 中的 expected
字段不能使其通过。

### 8.2 Route 预期

默认不在 manifest 的 expected 中写死 route ID 或 theorem name，因为库演化会改变最优路径。
runner 必须在 `route.json` 中记录本次实际引用的 theorem declarations、imports、直接/多跳分类和
index hash。允许的 route coverage 约束包括：

- fixed exact target declaration；
- resolution source 为 direct theorem、adapter、registered edge 或 multihop；
- Core artifact 确实显式引用库 declaration；
- final-composition penalty 上限；
- atom count 上限或下限，但 reflexive case 必须允许 0。

仅 `optional_authoring` 允许增加以下 coverage：

- 必须闭合某种 typed gap；
- baseline 无路线、candidate 后有路线；
- 必须产生新的 validated capability head。

所有约束只影响 benchmark outcome；最终能力只由 Artifact 中实际 elaborated 的 Lean term 授予。

## 9. 分层输出契约

### 9.1 Core Reducer 最小交付

每个 Core job 只要求保存：

```text
.reduction-agent/jobs/<job-id>/
  Artifact.lean
  goal.json
  route.json
  report.json
  commands/
  index/
    metadata.json
```

`route.json` 记录实际引用的 library declarations、import modules、route cost、index hash 和
direct/adapter/multihop 分类。Core 不要求生成 `Probe.lean`、stage modules、candidate snapshot 或
receipt。

### 9.2 Optional Authoring 完整交付

成功 authoring job 在 Core 文件之外保存：

```text
.reduction-agent/jobs/<job-id>/
  gap.json
  authoring-task.json
  events.jsonl
  model/
  work/
    Generated/<job-id>/
      Presentation.lean
      Program.lean
      Semantics.lean
      DirectTM.lean
      Reduction.lean
      Membership.lean
      Completeness.lean
```

不存在的能力文件可以省略。七阶段 reduction 或四阶段 membership bundle 只在本层生成；新能力
通过验证后，仍由 Core 生成最小最终 Artifact。

### 9.3 模型可编辑范围

- 模型只能修改当前 AuthoringTask 的 `editable_files`；
- fixed header、namespace、source/target declaration 和 expected type 不可修改；
- 模型不能编辑 `Goal.lean`、`Probe.lean`、`Artifact.lean`、manifest 或 report；
- 模型不能新增对 `Benchmark.Hardness.Expected`、Gold、HiddenTargets 或 job 外 generated 文件的
  import；
- 一个 task 不得同时修改 presentation、program、semantics、direct-TM 和 final request。

### 9.4 Final Artifact

`Artifact.lean` 由 Core 固定 emitter 生成。它可以显式 import 并引用 typed index 选择的库定理，
示意形态为：

```lean
import Benchmark.Hardness.Inputs.Example
import ComplexityReduction.SomeLibraryModule

def request : ComplexityReduction.Protocol.TypedAutoReductionRequest :=
  ...

noncomputable def selectedReduction :
    ComplexityReduction.Certificate.CertifiedReduction source target :=
  libraryReduction₁.trans libraryReduction₂

-- objective-specific fixed emitter constructs the exact request/result
noncomputable def result :
    ComplexityReduction.Protocol.TypedAutoReductionResult request :=
  ...

assert_standard_axioms selectedReduction, result
```

上述代码是结构示意，具体 result constructor 由 objective-specific emitter 决定。Core 不再强制
使用 `by_hardness_resolver` 重新扫描 registry；它可以直接消费已经由 typed index 选中、并将在
当前文件中由 Lean 检查的 library term。Artifact 仍不得引用模型返回但未被 index/Lean 验证的名字。

## 10. 验证关卡

### 10.1 Core profile

1. suite 级共享 preflight 构建 runtime、输入模块和 typed declaration index；
2. source/target/membership 只接受 fully-qualified declaration name；
3. index 搜索 direct theorem、adapter、registered capability 和 multihop path；
4. emitter 生成包含 exact input check、selected term、request/result 和 final axiom gate 的
   `Artifact.lean`；
5. 每个 case 执行一次 `lake env lean Artifact.lean`；
6. compile success、exact result type 和 final axiom gate 同时成立才是 Core `VERIFIED`；
7. 库无路线时输出 typed blocker，不生成 candidate、不调用模型；
8. index hash、输入 hash、selected declarations 和 imports 写入报告。

Core profile 不强制独立 `Goal.lean`、Probe、registry revalidation 或 replay。若 index dependency hash
不匹配，应在共享 preflight 重建 index，而不是为每个 case 启动多次 Lean。

### 10.2 Optional Authoring profile

1. `lake env lean <candidate>`；
2. static scan 禁止 `sorry`、`admit`、`sorryAx` 和新 `axiom`；
3. header fence hash 不变；
4. import allowlist 通过；
5. exact expected capability type check；
6. attribute discovery 后重新进行 canonical-head classification；
7. candidate endpoint 与题面 endpoint defeq；
8. capability 使用同一个 program/verifier index；
9. candidate 通过 standard axiom gate；
10. bundle validator 检查所有 dependent indices；
11. 验证后的 capability 交回 Core route search；
12. Core 再生成并编译一次最终 Artifact。

### 10.3 Strict-release profile

1. 校验 input、index、toolchain、manifest、candidate 和 Artifact hash；
2. fresh scan 验证 selected declarations 或新 candidate 仍存在且 endpoint/type 未变；
3. 重新 elaboration exact request；
4. 独立编译同一 `Artifact.lean`；
5. replay 后 result exact type 和 standard axiom gate 仍通过；
6. artifact hash 与 report 一致；
7. oracle exclusion、prompt/response 边界和 model usage 检查通过；
8. authoring case 可增加 candidate 删除/resume 与 stale-cache 负例；
9. 生成发布用 verification receipt。

### 10.4 进程预算

- Core：共享 preflight 不计入单 case；每个 direct/adapter/multihop case 最多 1 个 Lean 进程；
- Strict release：在 Core 基础上最多增加 1 个独立 replay；
- Optional authoring：候选编译单独计数，不得并入 Core latency；
- 安全负例和故障注入可以超出预算，但报告必须给出原因；
- 超预算不是证明失败，但属于 runner 性能回归。

## 11. Oracle 与数据泄露隔离

迁移 benchmark 将 GoldProofs 和 HiddenTargets 放在同一仓库中。Core 始终禁止 oracle import；
涉及模型或 strict-release 的运行还必须实施 workspace 级显式隔离：

1. model workspace 不复制 `Expected/`、Gold、HiddenTargets 或 legacy proof；
2. 不复制这些模块的 `.olean`/`.ilean`；
3. candidate import scanner 拒绝任何 oracle module；
4. prompt 只包含公共 case module、exact signatures、当前 diagnostics 和允许的 helper；
5. gold proof 只由独立 sanity runner 编译；
6. gold proof 的成功不能直接使 Agent case 通过；
7. report 记录 public workspace hash 和排除目录；
8. DeepSeek Key 只来自本地 `.env`，不进入 workspace、prompt、response log 或 report；
9. prompt injection 样例必须证明模型无法读取或 import oracle；
10. promotion production candidate 必须是独立人工操作，不属于 benchmark job。

## 12. Benchmark 分类与层级

case 先按执行层分类，再使用能力 lane；旧 L0–L15 只保留为 provenance/difficulty metadata：

| execution layer | lane | 目标 | 预期 final |
| --- | --- | --- | --- |
| `core_reuse` | `core.refl` | defeq source/target | verified, 0 atoms |
| `core_reuse` | `core.direct_theorem` | index 找到库内精确 theorem 并直接引用 | verified |
| `core_reuse` | `core.registered_route` | 已注册单跳 capability | verified |
| `core_reuse` | `core.adapter` | 复用库内 presentation/equivalence adapter | verified |
| `core_reuse` | `core.multihop` | 多跳已有路线 | verified |
| `core_reuse` | `core.cook_levin` | exact native membership | verified |
| `core_reuse` | `core.membership` | `proveInNP` | verified 或 typed blocked |
| `core_reuse` | `core.completeness` | `proveNPComplete` | verified 或 typed blocked |
| `optional_authoring` | `authoring.presentation` | 新建 lawful presentation/adapter | verified after candidate |
| `optional_authoring` | `authoring.program` | primitive/program/semantic/direct-TM | verified after candidate |
| `optional_authoring` | `authoring.reduction` | 完整新 reduction | verified after candidate |
| `optional_authoring` | `authoring.membership` | 新建 native membership bundle | verified after candidate |
| `release_audit` | `audit.stale` | input/index/candidate 改变 | expected failed |
| `release_audit` | `audit.replay` | 独立重放 | verified |
| `release_audit` | `security.model` | prompt injection/oracle/非法响应 | expected blocked/failed |

Core 的 `VERIFIED` 不能依赖 Optional Authoring；authoring 和 audit 也不能反向抬高 Core 通过率。

## 13. 指标与通过率

### 13.1 Core Reducer 一级指标

- `core_library_route_verified_rate`：库中存在直接或可组合路线的 Core case 最终通过率；
- `direct_theorem_reuse_rate`：有精确库 theorem 的 case 确实直接引用该类 declaration 的比例；
- `multihop_route_closure_rate`：需要两跳以上组合的 Core case 通过率；
- `core_typed_blocker_accuracy`：库中确无路线时稳定返回正确 blocker 的比例；
- `core_axiom_clean_rate`：Core verified artifact 通过 final axiom gate 的比例；
- `core_zero_model_call_rate`：Core case 中模型调用为 0 的比例，目标必须为 1.0。

### 13.2 Optional Authoring 指标

- `authoring_case_outcome_accuracy`；
- `full_reduction_authored_rate`；
- lawful presentation、primitive、semantic proof、direct-TM closure rate；
- verifier program/discipline、native membership closure rate；
- model patch protocol acceptance、first-pass compile 和 bounded repair rate；
- authoring budget exhaustion rate。

### 13.3 Benchmark/Release Audit 指标

- `strict_replay_rate`；
- stale-cache/input/index detection accuracy；
- oracle isolation 和 prompt injection block accuracy；
- verification receipt completeness；
- repeated trial stability。

### 13.4 效率指标

- wall-clock time；
- Lean command time；
- Core 单 case Lean process count，目标为 1；
- strict-release 额外 replay process count，目标为 1；
- declaration index build/update time 与 hit rate；
- selected route cost；
- direct theorem、adapter、registered edge、multihop 的命中分布；
- authoring model calls/attempts 与 token usage；
- authoring candidate compile time；
- audit revalidation/replay time；
- candidate LOC 与修改文件数；
- `/mnt/*` 与 Linux ext4 环境的 I/O 基准差异。

所有时间必须按 Core、authoring、audit 三层分别报告，不得用 authoring/replay 时间描述 Core latency。

### 13.5 禁止误计为成功的情况

- 只证明 backend `InNPEnc`/`TMInNP`；
- Core route 只存在于 JSON/index，但 Artifact 未显式引用或 Lean 未编译；
- Core 无路线后隐式调用模型并把结果计入 Core success；
- authoring case 使用已有 identity/refl route 绕过要求的新 reduction；
- authoring case 只调用已有 membership theorem，没有生成要求的 capability；
- report 写 `VERIFIED` 但 Artifact 未编译；
- candidate 含 `sorryAx` 或额外 axiom；
- import GoldProof/HiddenTargets；
- theorem name 只存在于 report，未进入可重放 Lean 源码；
- direction 错误的 reduction；
- semantic proof 与 direct-TM 使用不同程序。

## 14. 正例矩阵

### 14.1 Core Reducer 正例

1. exact refl；
2. 库内精确 theorem 未带 registry attribute，但 typed index 能发现并直接引用；
3. 单原子 registered route；
4. 多原子 library/registry 混合路线；
5. 库内 presentation/equivalence adapter；
6. atomic route 优于高 cost fallback；
7. exact native membership 经 Cook–Levin 到 structured 3SAT；
8. Cook–Levin root + production suffix；
9. exact `proveInNP`；
10. exact library/registered `proveNPComplete`；
11. completeness transport；
12. 所有 Core 正例模型调用为 0，且单 case Lean process count 不超过 1。

### 14.2 Optional Authoring 正例

1. lawful presentation authoring；
2. primitive/program authoring；
3. semantic proof authoring；
4. direct-TM authoring；
5. 完整 program-indexed new reduction；
6. verifier program + discipline + membership；
7. DeepSeek bounded repair；
8. hidden gold、无现成 route 的完整 reduction bundle。

### 14.3 Strict-release 正例

1. Core Artifact 独立 replay；
2. authoring Artifact 独立 replay；
3. index/cache 未变化时 hash 一致；
4. deterministic fixture 与 model-generated candidate 分开标记和计分。

## 15. 负例矩阵

### 15.1 Core Reducer 负例

1. carrier 相同但 presentation 不同；
2. wrong exact membership endpoint；
3. backend-only membership；
4. declaration index 中 theorem type 与当前 library 不一致；
5. index 命中不存在或不可 import 的 theorem；
6. source/target direction 错误；
7. target 有 reduction 但无所需 native membership；
8. route 只记录在 JSON 而未写入 Artifact；
9. library 无路线时错误启动模型；
10. Artifact request 与原 request 不同。

### 15.2 Optional Authoring 负例

1. verifier 无 checked discipline；
2. model 发明不存在的 theorem/helper declaration；
3. model 试图改变 target/objective、fixed header 或 endpoint；
4. model import GoldProof；
5. model 输出 `sorry`、`axiom` 或 unsafe shortcut；
6. semantic proof 与 direct-TM 使用不同 program；
7. candidate endpoint 不匹配；
8. bundle/canonical-head validation 失败；
9. API timeout/429/5xx、非 JSON 或 prompt injection；
10. authoring budget exhausted。

### 15.3 Strict-release 负例

1. index、input、candidate 或 registry 在 Core 后改变；
2. replay Artifact hash 或结果改变；
3. 两个 job 写同一 candidate 路径；
4. 删除 candidate 后错误复用 verified cache；
5. oracle `.lean`、`.olean` 或 prompt 内容泄漏。

## 16. `Benchmark/V2Hardness` 历史迁移方案

本节及第 17 节记录历史 case 的来源与数学覆盖点。所有迁移目标均受第 1--15 节的新执行层规则
约束：先建立 `core_reuse` case；只有库内确无可用路线时，才另建 `optional_authoring` variant；
fresh replay 与 oracle 检查归入 `release_audit`。

### 16.1 共通修改

1. 将旧输入移动/重写到 `Lean/Reference/Benchmark/Hardness/Inputs/`；
2. `ComplexityReduction_IR.V2` 改为 canonical `ComplexityReduction`；
3. 使用当前 `PresentedProblem`、`NativeTMInNP` 和 current declaration names；
4. raw `input` path 改成 importable `module`；
5. manifest schema 改为 `hardness_benchmark_v2`；
6. 添加 `objective`、`expected`、`target_policy`、phase/tag/resource 字段；
7. 删除 `minimum_route_atoms = 1` 作为通用成功判据；
8. `#v2_hardness_probe` 改为当前 nonce-bound probe；
9. `by_v2_hardness_resolver` 改为 `by_hardness_resolver`；
10. `assert_v2_standard_axioms` 改为 `assert_standard_axioms`；
11. README 中旧 scripts、旧 design doc 和 `deepseek-chat` 全部更新；
12. 不再复制 input source 到 Probe/Artifact。

### 16.2 `three_sat_to_known_np`

旧 case 要求至少一个 atom，但当前 planner 正确优先 refl。迁移时拆成两个 case：

1. `three-sat-refl`
   - source 为 canonical structured 3SAT；
   - objective 为 `reduce_to_known_np`；
   - 允许/要求 selected path 为 0 atoms；
   - 覆盖 defeq refl。
2. `three-sat-explicit-suffix`
   - fixed target 为一个不同的 validated native-NP target；
   - objective 为 `reduce_to_known_np`；
   - 要求至少一个 validated atom；
   - 不写死 theorem name。

### 16.3 `tagged_three_sat_normalization`

- 迁移为 exact tagged `PresentedProblem`；
- baseline 应发现 registered ingress normalization；
- 可设置 fixed structured 3SAT target，避免 registry 演化导致 case 失去覆盖点；
- 增加 presentation mismatch 负例；
- 后续增加一个删除 ingress 后的 authoring variant，要求 Agent job-local 补 adapter。

### 16.4 `native_np_via_checked_cook_levin`

- 依赖 Agent Phase 2；
- source 为 current structured Knapsack `PresentedProblem`；
- membership 必须 exact `NativeTMInNP source`；
- baseline 不注册 source 到 3SAT edge；
- Agent 通过库内 `NativeCookLevin` 生成 job-local ingress edge；
- 至少测试 direct 3SAT target 与 3SAT suffix 两种 case；
- 添加 wrong membership、backend-only、missing discipline 和 axiom failure 负例。

## 17. Opencode L0–L15 迁移映射

旧 level 不直接复制 proof target，而是先转换为 Core library-reuse lane；确需创造新 capability 的
覆盖点再拆出独立 authoring case。下文中的“authoring”描述均不代表 Core 自动 fallback。

### 17.1 L0：标准问题 membership（25 例）

迁移目标：`membership.native`。

- 为每个问题建立 exact `PresentedProblem` module；
- 优先复用 current native verifier/membership；
- objective 改为 `prove_in_np`；
- 没有 native membership 的问题应先成为 expected blocker，而不是用旧 `InNPEnc` 通过；
- direct library membership case 与 authoring verifier case 分开统计。

### 17.2 L1：structured/binary structured membership（10 例）

迁移目标：`membership.native` 和 verifier discipline。

- 保留 structured encoding 难度；
- 明确 witness presentation、verifier program、checked decoder discipline 和 direct-TM；
- backend `TMInNP` 只作为 negative evidence；
- 增加 representation mismatch 与 wrong discipline negative case。

### 17.3 L2：一跳 route composition（5 例）

迁移目标：`route.single-hop`。

- 旧 `KarpReductionM` 替换为 `CertifiedReduction`；
- source/target 改为 exact `PresentedProblem`；
- fixed target 写入 manifest declaration handle；
- objective 为 `reduce_to` 或 `reduce_to_known_np`；
- route theorem name 不写入 expected；
- target membership 由 current registry exact discovery。

### 17.4 L3：interface adapter（5 例）

迁移目标：`gap.presentation`/`gap.primitive`。

- 先构造 exact wrapped source presentation；
- baseline 产生 lawful presentation、presentation change 或 primitive blocker；
- Agent 只在 job-local module 中补 adapter；
- final result 必须由 resolver 使用新 candidate；
- identity shortcut 必须被 hidden coverage check 拒绝。

### 17.5 L4：两跳 route（6 例）

迁移目标：`route.multihop`。

- 使用 current registry atomic edges；
- 测试 path composition、stable cost 和 final-composition fallback；
- expected 不固定 atom names，但可固定 source/target 与最大 penalty；
- 增加缺中间 edge 的 expected blocker variant。

### 17.6 L5：encoding bridge（4 例）

迁移目标：`gap.presentation` 和 `Certificate.PresentationChange`/`Equiv`。

- 忽略字段、nested projection 和 sandwiched encoding 必须有显式 certified bridge；
- 不接受 carrier equality metadata 替代 presentation certificate；
- bridge 与 route 分成两个 AuthoringTask；
- final artifact 组合 bridge 与 route。

### 17.7 L6：textbook adapter（6 例）

迁移目标：`authoring.reduction`。

- 将旧 costed map 拆为 pure function、`Program.Primitive`、semantic proof、direct-TM 和
  `CertifiedReduction`；
- 每种 capability 独立 checkpoint；
- 缺 direct-TM 时保持 blocker；
- 成功后重新 registry classification。

### 17.8 L7：Schaefer hard-side（3 例）

迁移目标：`completeness.native`。

- 旧 `NPCompleteEnc` 替换为 exact `NativeTMNPComplete`；
- 要求 target native membership；
- hardness root 和方向必须明确；
- objective 为 `prove_np_complete`；
- 增加只有 hardness 无 membership、方向相反和 backend-only negative case。

### 17.9 L8：local adapter authoring（4 例）

迁移目标：Phase 4/5 authoring vertical slice。

- 保留局部 projection/adapter 难度；
- 不再一次输出完整 membership proof；
- 拆为 presentation、primitive、semantics、direct-TM、certificate task；
- Agent 最终仍交付全部 Lean 文件和 verified artifact。

### 17.10 L9：开放两跳 synthesis（4 例）

迁移目标：adapter authoring + open validated target selection。

- source normalization 先闭合；
- route target 与已有多跳 path 由 deterministic resolver 决定；
- 模型不选择 route ID 或 theorem name；
- 若 registry 已有路线，必须 deterministic reuse 且 `model_called = false`；
- 若无路线，Lean 产生 typed task，模型分阶段生成受 fence 约束的源码，最终仍交付完整 bundle。

### 17.11 L10：开放三跳 synthesis（6 例）

迁移目标：稳定多跳 path search，以及缺失单边时的 typed authoring。

- 不要求模型手写三个 theorem application；
- Lean resolver 负责发现和组合已有 edges；
- benchmark 测试 planner cost、route stability 和 registry evolution；
- authoring variant 隐藏一个 edge capability，要求模型生成新源码补齐；route search 本身不调用模型。

### 17.12 L11：composed CSP gadget（8 例）

迁移目标：Phase 5 gadget authoring。

- source-CSP-to-3SAT 与 3SAT-to-target-CSP 分成 validated atoms；
- 若两者均已存在，测试 closed composition；
- 若缺一个 gadget，只 author 一个 typed local reduction；
- program、semantic proof 和 direct-TM 必须同索引；
- final resolver 组合，而不是模型提交整条 proof term。

### 17.13 L12：mixed gadget-route（4 例）

迁移目标：gadget candidate + production suffix。

- Agent author 局部 CSP gadget；
- ordinary Karp21 suffix 由 registry resolver 复用；
- fixed final target 保持 exact declaration；
- 测试 candidate 后 registry revalidation。

### 17.14 L13：stacked bridge mixed route（4 例）

迁移目标：多个顺序 typed gap。

- 两个 presentation bridge 分成两个任务；
- gadget 为第三任务；
- suffix 由 resolver 完成；
- 每步 checkpoint 和 resume；
- 任一步删除后必须回到对应 blocker。

### 17.15 L14：forked dual-tail route（6 例）

迁移目标：同一 source 到两个 target 的独立 request 或 suite-level product。

- 当前 `TypedAutoReductionResult` 一次只对应一个 request；
- 不把两个结果塞进一个非标准 proof target；
- 将每个旧样例拆为 graph-target 与 numeric-target 两个 case，并用 suite group 关联；
- 可增加一个 meta-case 检查两个 artifact 都 verified，但 meta-case 不授予 Lean 能力。

### 17.16 L15：stacked bridge + forked route（2 例）

迁移目标：最高难度 suite group。

- 先拆成 bridge A、bridge B、graph tail、numeric tail 四个可恢复 job/case；
- 再增加 end-to-end grouped benchmark；
- 只有四个 exact artifact 均 verified 时 group success；
- 不允许一个大 existential theorem 绕过 current request ABI。

### 17.17 Quals（5 例）

迁移目标：单独的 `quals-completeness` suite。

- 将题目形式化结果固定为 exact `PresentedProblem`；
- 若需要从自然语言创建该 presentation，放入独立 formalization benchmark，不计 hardness Agent
  通过率；
- hardness suite 只从已确认的 Lean presentation 开始；
- objective 根据题意使用 `reduce_to` 或 `prove_np_complete`；
- 需要 hidden gold sanity 和标准公理 gate。

## 18. HiddenTargets 与 GoldProofs 修改计划

### 18.1 HiddenTargets

旧 HiddenTargets 不再作为候选可以 import 的 Lean module。迁移后拆为：

- public input module：source/target declaration；
- private expected JSON：expected baseline gap、final status、coverage；
- 可选 private Lean oracle：只做 benchmark sanity，不进入 Agent environment。

如果 hidden module 必须 elaboration，它应在独立 Lake target 或隔离 workspace 中编译，不能进入
production aggregate 或 model-visible olean cache。

### 18.2 GoldProofs

每个迁移后的 gold proof 必须：

1. 改为 current `PresentedProblem`/certificate types；
2. 不使用 Legacy backend shortcut；
3. 不含 `sorry`/axiom；
4. 执行 `assert_standard_axioms`；
5. 通过 exact endpoint check；
6. 不被正式 candidate import；
7. 只证明 benchmark target 非空且设计可解；
8. 不决定 Agent 是否通过。

Gold proof 缺失不一定阻止普通 case 运行，但 release benchmark 必须为所有预期可解的 authoring
case 提供 gold sanity 或独立人工验证记录。

## 19. Runner 与测试修改计划

### 19.1 Runner

Runner 拆为三个明确入口/模块：

1. **Core Reducer**
   - 默认 CLI mode 为 `reuse`；
   - 在共享 preflight 构建或加载 typed declaration index；
   - 搜索 direct theorem、adapter、registered edge 与 multihop；
   - 每个 case 只生成并编译一个最终 Artifact；
   - 无路线时返回 typed blocker，绝不自动调用模型。
2. **Optional Authoring**
   - 只接受显式 `author-new-edge`；
   - 消费 Core blocker 和固定 endpoint；
   - authoring policy 支持 `deterministic-template`、`model-auto`、`model-required`，但
     `model-auto` 只在本入口内部表示模型失败后的受控模板 fallback；
   - 成功 candidate 交回 Core emitter，不能自行改写 final request。
3. **Benchmark/Release Audit**
   - `scripts/run_hardness_benchmark.py` 负责 suite files、schema、case 并行和共享 preflight；
   - 支持 `verification_profile = core|strict-release`；
   - strict profile 才执行 fresh scan、stale check、oracle exclusion、resume/replay 和 receipt；
   - report 按 Core、authoring、audit 分项输出通过率、进程数和耗时。

兼容迁移期间可以保留旧 `--authoring` 参数，但在 `core_reuse` case 上任何非 disabled 值都应被
schema 拒绝，而不是静默忽略或自动升级。

### 19.2 Python 测试

新增：

```text
tests/test_hardness_core_declaration_index.py
tests/test_hardness_core_direct_theorem.py
tests/test_hardness_core_multihop.py
tests/test_hardness_core_process_budget.py
tests/test_hardness_execution_layer_schema.py
tests/test_hardness_benchmark_schema.py
tests/test_hardness_benchmark_inventory.py
tests/test_hardness_benchmark_outcomes.py
tests/test_hardness_benchmark_oracle_isolation.py
tests/test_hardness_benchmark_grouping.py
tests/test_hardness_benchmark_metrics.py
tests/test_hardness_benchmark_negative.py
tests/test_hardness_legacy_quarantine.py
```

### 19.3 Lean regression

新增：

```text
Lean/Reference/Benchmark/Hardness/Regression.lean
Lean/Reference/Benchmark/Hardness/Regression/Refl.lean
Lean/Reference/Benchmark/Hardness/Regression/DirectLibraryTheorem.lean
Lean/Reference/Benchmark/Hardness/Regression/LibraryAdapter.lean
Lean/Reference/Benchmark/Hardness/Regression/MixedMultihop.lean
Lean/Reference/Benchmark/Hardness/Regression/RouteFallback.lean
Lean/Reference/Benchmark/Hardness/Regression/InputMismatch.lean
Lean/Reference/Benchmark/Hardness/Regression/MembershipMismatch.lean
Lean/Reference/Benchmark/Hardness/Regression/AxiomGate.lean
```

## 20. 分阶段迁移

### Benchmark Phase B0：隔离与 schema 基线

任务：

- 将旧数据移动到 `Benchmark/Hardness/Legacy/`；
- 保留 legacy provenance 与 changelog；
- 当前 runner 对 legacy schema 明确报 `unsupported_legacy_benchmark`；
- 建立 `hardness_benchmark_v2` schema validator；
- 建立 inventory test；
- 文档说明旧通过率不能与新成绩比较。

验收：

- 当前 smoke 3/3 不受影响；
- legacy 文件不会被 current runner 自动发现；
- 107 样例、68 hidden、39 gold、3 V2 inventory 均可追踪；
- 无 oracle 进入 model workspace。

### Benchmark Phase B1：迁移 V2Hardness 三例

任务：

- port namespace/import/input ABI；
- 拆分 ThreeSAT refl 与 explicit suffix；
- port tagged normalization；
- Knapsack case 先标 `min_agent_phase = 2`；
- 添加 wrong membership/backend-only negative case；
- 更新 README 和运行命令。

验收：

- Phase 1 可运行 case 全部 outcome match；
- Phase 2 未实现时 Knapsack 明确 disabled，不伪报失败；
- Phase 2 完成后 Cook–Levin positive/negative 均通过。

### Benchmark Phase B2：代表性 vertical slice

从旧 L0–L8 每类先选 1–2 个代表，共约 12–16 个 case：

- L0 membership；
- L1 structured verifier；
- L2 one-hop route；
- L3 interface adapter；
- L4 multi-hop；
- L5 presentation bridge；
- L6 full reduction authoring；
- L7 completeness；
- L8 local adapter；
- 每类至少一个 negative variant。

验收：

- 所有 case 使用 current exact types；
- baseline blocker 稳定；
- final artifact 与 gold sanity 均通过；
- 删除 candidate 后 resume 回到 blocker；
- 模型关闭时已有路线 case 仍通过。

### Benchmark Phase B3：扩展 L0–L8

任务：

- 完成全部标准 membership、structured membership、route、bridge、textbook 和 Schaefer case；
- 补齐 native membership/completeness；
- 为所有 expected-solvable authoring case提供 gold sanity；
- 统一 metrics/tag/provenance。

验收：

- 不再出现旧 `EncodedDecisionProblem`/`KarpReductionM` 作为正式 case target；
- 不再出现旧 namespace/import；
- 所有成功 case 通过 axiom gate；
- 所有负例按精确 failure code 分类。

### Benchmark Phase B4：迁移 L9–L15

任务：

- port open route、three-hop、gadget、mixed、stacked 和 forked cases；
- 大 existential theorem 拆成多个 typed request/capability task；
- grouped metric 只做汇总；
- authoring task 一次一个 capability；
- 加入 checkpoint/resume 和 budget exhaustion。

验收：

- 至少一个完整新 reduction 从 presentation 到 direct-TM 全自动 verified；
- multi-hop 路线由 resolver 组合，不由模型列 theorem；
- forked case 的每个 target 有独立 exact artifact；
- oracle isolation 与 prompt injection 测试通过。

### Benchmark Phase B5：三层拆分与 Phase 7 发布（重新规划，进行中）

2026-07-29 已完成的 model-authoring 实验保留为 Optional Authoring 能力证据：
`model-required` 第 3 次 fenced proof-body 修复通过，`model-auto` 第 4 次通过，最终 artifact
hash 均为 `17d33d96b0cc5befb319d40e0f57fc2d5940dd56ac6db1c23f7787ea19c468bb`。
两次端到端耗时约 44--63 分钟，而模型网络时间均不到一分钟。这些数据不再作为 Core latency
或 Core 发布门槛；它们证明七阶段 authoring 与 strict audit 必须从默认 reducer 中拆出。

#### B5.1：Typed declaration index 与库定理直引

任务：

- 从当前 Lean environment 导出可复用 theorem/capability 的 declaration、type、canonical head、
  endpoint、import module 和 dependency hash；
- 同时索引未带 registry attribute、但类型可归一为所需 reduction/membership/completeness 的库定理；
- 实现 direct theorem、adapter、registered edge 和 multihop 的统一 costed search；
- route report 记录实际引用的 theorem names，但 final authority 仍是 Lean compile。

验收：

- 至少一个“库中存在但未注册 attribute”的 reduction 被 Core 发现并直接引用；
- index stale 时在共享 preflight 重建；
- Core 无路线时只返回 blocker，模型调用为 0。

#### B5.2：Core 单 Artifact 快速路径

任务：

- 将 input exact check、selected route term、request/result 和 axiom gate 合并进一个 Artifact；
- existing-route、direct theorem、adapter 和 multihop case 不再生成独立 Goal/Probe/revalidation 文件；
- suite 级 preflight 只执行一次。

验收：

- 共享 preflight 后每个 Core case 最多启动 1 个 Lean 进程；
- Core Artifact 可独立编译；
- 关闭/删除 authoring 与 model client 不影响 Core suite。

#### B5.3：Optional Authoring 抽离

任务：

- 七阶段 reduction、四阶段 membership、checkpoint、fenced model patch 移入独立 authoring 模块；
- 只有 `execution_layer = optional_authoring` 且策略显式启用时才可进入；
- candidate 验证后返回 Core，由 Core 生成最终 Artifact。

验收：

- Core case 无法通过配置误入 authoring；
- authoring 进程数、模型时间和成功率单独报告；
- deterministic fixture 与 model synthesis 不混算。

#### B5.4：Strict-release audit 包装层

任务：

- fresh scan、fingerprint、stale-cache、oracle isolation、resume 和 replay 移入 audit 模块；
- `verification_profile = core` 默认关闭这些重复步骤；
- `strict-release` 在 Core/authoring 结果上增加独立 replay 和 receipt。

验收：

- strict profile 不改变 Core 选择的数学路线；
- Core latency 报告不包含 audit 时间；
- release/security suite 继续覆盖原有可信边界。

#### B5.5：模型稳定性评测与发布

三层拆分完成后再恢复：

- API-only smoke；
- `model-auto`、`model-required` 各三次隔离 trial；
- token/time/attempt/capability closure 与稳定性汇总；
- public manifest、runner version、toolchain/index hash 和结果摘要。

本阶段只决定 Optional Authoring 的发布状态，不阻塞 Core Reducer 的库复用版本发布。

## 21. 历史首批迁移清单

以下清单记录 B0--B4 的历史实施顺序，不再决定 Phase 7 默认运行链：

1. legacy 目录隔离；
2. v2 schema 与 inventory test；
3. port `ThreeSAT` 为 refl + explicit suffix；
4. port `TaggedThreeSAT` normalization；
5. 为 Knapsack Cook–Levin 建 disabled/phase gate；
6. 从 L2 迁移一个 existing route case；
7. 从 L3/L8 迁移一个 presentation/adapter case；
8. 从 L6 迁移一个完整 reduction authoring case；
9. 从 L7 迁移一个 completeness case；
10. 为上述每类增加至少一个 negative case；
11. 建立 Gold oracle isolation；
12. 扩展 benchmark runner 分项指标；
13. deterministic 重放；
14. 最后启用 DeepSeek V4 Flash authoring 对照实验。

后续 case 必须先迁移为 `core_reuse`；只有确认库中确无路线且 benchmark 明确要求新能力时，才增加
独立 `optional_authoring` variant。strict replay 不再是批量迁移 Core case 的前置条件。

## 22. 回归命令目标

B5 三层拆分完成后的目标入口应为：

```bash
cd Lean
lake build ComplexityReduction Benchmark
lake env lean Reference/ComplexityReduction/Agent/Hardness/Regression.lean
lake env lean Reference/Benchmark/Hardness/Regression.lean

cd ..
python3 -m pytest -q tests

# 默认产品路径：只复用库定理，不启动模型，不执行重复 replay
python3 scripts/run_hardness_benchmark.py \
  --manifest Benchmark/Hardness/MANIFEST.json \
  --execution-layer core_reuse \
  --verification-profile core \
  --planner deterministic

# 显式新边创作：与 Core 指标和耗时分开
python3 scripts/run_hardness_benchmark.py \
  --manifest Benchmark/Hardness/MANIFEST.json \
  --execution-layer optional_authoring \
  --suite model-authoring \
  --planner deterministic \
  --authoring model-required \
  --verification-profile strict-release \
  --env-file .env

# 发布/安全审计：包装既有结果，增加 fresh checks 和独立 replay
python3 scripts/run_hardness_benchmark.py \
  --manifest Benchmark/Hardness/MANIFEST.json \
  --execution-layer release_audit \
  --verification-profile strict-release
```

上述新参数属于本计划的目标接口，在 runner 实现前不得写入当前用户文档为已可用命令。发布前应
随机抽取 Core 与 authoring verified job，独立重新编译其 `Artifact.lean`；generated modules 仅在
authoring case 中存在。

## 23. 风险与控制

### 23.1 旧 theorem proof 被机械包装成新 case

风险：表面替换 namespace，实际仍依赖 backend membership 或旧 cost model。

控制：正式 target 必须使用 current canonical heads；schema/inventory test 禁止旧类型；每个 case
必须记录 exact source/target 和 phase lane。

### 23.2 Benchmark 泄露 gold route

风险：模型从 source tree、olean、prompt 或 helper retrieval 读到 GoldProof。

控制：独立 public workspace、禁止 oracle import、不复制 oracle olean、prompt 文件清单审计。

### 23.3 编译通过但没有创作新 reduction

风险：identity route、已有 theorem 或 membership shortcut 使 case 虚假通过。

控制：baseline snapshot、required gap closure、candidate exact capability validation、固定 target、
hidden coverage check 和 final revalidation。

### 23.4 多目标旧 case 与当前 request ABI 不一致

风险：为了保留旧 existential target，绕过 `TypedAutoReductionRequest`。

控制：每个 target 独立 case/artifact，group 只做非权威汇总。

### 23.5 Registry 演化导致 route 期望脆弱

风险：写死 theorem name、atom count 或 route ID 后，library/index/registry 中出现合法更优路线使
benchmark 失败。

控制：固定 exact endpoint 和 resolution class；实际 theorem names 只记录在本次 route report；除
特定 coverage case 外不在 expected 中写死 atom names。

### 23.6 Benchmark 难度与 Agent phase 不匹配

风险：未实现的 Phase 5/6 case 被统计为模型失败。

控制：`min_agent_phase`、disabled reason、分 suite 报告；只有 enabled case 进入当前通过率。

### 23.7 库中已有 theorem 但 Core 无法发现

风险：只扫描 attribute registry，导致已有 Lean theorem 被误判为 typed gap，并错误进入 authoring。

控制：建立全库 typed declaration index；加入未注册 direct theorem、adapter 和 import discovery 回归；
Core blocker 报告必须区分 `index_no_match` 与 `candidate_failed_to_compile`。

### 23.8 Strict audit 再次渗入 Core 默认路径

风险：为追求发布可信性，又把 Probe、fresh scan、fingerprint 和 replay 变成每个普通 case 的强制
步骤，重新造成多进程冷启动。

控制：schema 强制区分 `verification_profile`；Core process-budget 测试要求共享 preflight 后最多
1 个 Lean 进程；audit 时间不得计入 Core latency。

### 23.9 直接引用 theorem name 产生 stale 或伪造路线

风险：index/report 中的 declaration 已删除、类型改变、import 不完整或由模型伪造。

控制：index 绑定 dependency hash；Artifact 显式 import 和引用；最终 Lean elaboration、exact type 与
axiom gate 是唯一权威。模型输出不能直接修改 Core route plan。

## 24. 完成标准

本次架构拆分与 benchmark 迁移完成时应满足：

### 24.1 Core Reducer

- 默认入口只做库定理检索、adapter/multihop 组合和最终 Artifact 编译；
- typed declaration index 能发现 registered capability 和未注册但类型匹配的库 theorem；
- Artifact 显式 import 并引用实际选中的 library declarations；
- 每个 Core case 从 exact `PresentedProblem` 开始，membership/completeness 使用 native exact types；
- 库无路线时返回 typed blocker，模型调用严格为 0；
- 共享 preflight 后 direct/adapter/multihop case 最多启动 1 个 Lean 进程；
- Core verified 只依赖 kernel、exact request type 和 final standard axiom gate；
- 删除 authoring/model/audit 模块后 Core suite 仍可独立运行。

### 24.2 Optional Authoring

- 只有显式 `optional_authoring` case 可以创建 job-local capability；
- 新 reduction case 强制 program、semantics 和 direct-TM 同索引；
- 七阶段 reduction、membership bundle、checkpoint 与模型 patch 不出现在 Core 默认路径；
- candidate 通过专用 validator 后交回 Core 生成最终 Artifact；
- DeepSeek 只能修改当前 typed task 的 editable body，不能改变 goal、endpoint 或 Core route plan；
- model synthesis 与 deterministic fixture、Core reuse 分开计分和计时。

### 24.3 Benchmark/Release Audit

- strict-release 才执行 fresh scan、fingerprint、stale-cache、oracle isolation、receipt 和 replay；
- strict audit 不改变 Core 数学路线，也不计入 Core latency；
- GoldProof/HiddenTargets 不进入 Core、candidate 或模型 workspace；
- verified release case 可由公开输入、Artifact 和必要 authoring source 独立重放；
- positive、negative、blocked、failed 以及三层指标分开统计。

### 24.4 迁移与文档

- 当前正式 manifest 中无旧 V2 namespace、旧 input-file ABI 或旧 runner command；
- 所有正式 Lean 输入均位于当前 Lake module root；
- 每个 case 明确声明 `execution_layer` 和 `verification_profile`；
- 旧 107+3 样例全部有明确状态：已迁移、暂缓、拆分或废弃；
- legacy 通过率不与新 benchmark 通过率混合；
- benchmark 报告能够分别回答：Core 能否自动复用库定理、authoring 能否创建新能力、严格审计是否
  可重放且无泄漏。
