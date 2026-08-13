# Complexity Reduction Agent：NP-hard-first 通用自动归约 Agent 核心重构计划

> 状态：Active
>
> 更新日期：2026-08-13
>
> 当前唯一优先主线：最大限度复用 ComplexityReduction 的原生证书、路径、transport 与程序复杂度抽象，先构建一个能够自动产出 `NativeTMNPHard target` 的通用归约 Agent；一般定理搜索、前提求解和新归约创作都服务于这一 NP-hard 闭环。

## 0. 战略重置

此前活动计划以冻结 benchmark、exact-edge 审查、逐节点模型调用记录和发布级复现为中心。这些工作可以继续作为独立评测或发布工具存在，但不再决定核心 Agent 的架构，也不再是默认求证路径的前置义务。

从本计划开始，项目的第一产品目标不是“严格执行一套预先冻结的 benchmark 协议”，也不是“证明任意 Lean 命题”，而是：

> 给定一个精确的 `PresentedProblem target`，Agent 自动构造并验证 `NativeTMNPHard target`：优先复用已有 hardness/completeness 证据、`CertifiedReduction`、`CertifiedPath`、presentation transport 和一般 hardness theorem；递归解决这些规则产生的前提；若复用路径均失败，再从合适的 hard/complete hub 到目标自主定义并验证新的 `CertifiedReduction`。

核心成功标准不是命中预先指定的路线，而是最终产生一个精确类型为 `NativeTMNPHard target`、可被 Lean kernel 接受的证明项。`CertifiedReduction`、`CertifiedPath`、性质证明和程序复杂度证明是这一根目标的内部证明对象，而不是当前范围内彼此独立的产品线。

本计划取代本文件此前全部 exact-edge 优先事项、冻结 case 实施表、模型 ledger 门槛和 benchmark 发布目标。旧报告与 benchmark 数据仍可用于回归和对照，但不得反向限制通用 Agent 的证明搜索能力。

## 1. 产品目标与非目标

### 1.1 第一且当前唯一产品目标：自动证明 `NativeTMNPHard`

当前产品入口只承诺处理以下根目标：

```lean
ComplexityReduction.Certificate.NativeTMNPHard target
```

调用方可以通过精确 goal expression、目标 declaration，或现有 `TypedNPHardRequestV1` 提交任务。搜索内部可以并且必须处理下列中间目标：

- `NativeTMNPHard hub`；
- `NativeTMNPComplete hub`，仅用于投影 hardness；
- `CertifiedReduction source target`；
- `CertifiedPath source target`；
- `CertifiedEquiv source target`；
- `CertifiedPresentationChange source target`；
- 一般 hardness theorem 的性质前提；
- 新 reduction constructor 暴露出的程序、语义和复杂度义务；
- 这些目标递归产生的局部辅助命题。

典型辅助命题包括：

- 两个 presentation 或 representation 的一致性；
- 某个关系、语言或实例满足结构性质；
- 某个函数是多项式时间映射；
- 某个程序运行结果与数学构造一致；
- 某个有限对象非空、可判定或不属于某个分类；
- 某个 reduction 的语义等价；
- 某个一般定理的依赖前提。

`NativeTMInNP target`、`NativeTMNPComplete target` 和任意一般 `Prop` 的独立自动证明不属于当前交付范围。它们只有在闭合 NP-hard 根目标所需时才进入搜索。待 NP-hard Agent 稳定后，再评估是否提升为新的产品目标。

Agent 不得把 NP-hard 目标预先压缩成有限种 benchmark task class。目标类型、ComplexityReduction 的证书构造和当前 Lean 环境决定可用推理规则，Python 枚举值不得成为系统能力边界。

默认不得把 `NativeTMNPHard target` 直接展开为

```lean
∀ source, NativeTMInNP source → Nonempty (CertifiedReduction source target)
```

并从零证明该全称命题。正常路线必须通过库中已经封装好的 hardness/completeness、path transport 或一般 hardness theorem 闭合。只有库 theorem 本身要求展开，或最终 synthesis 明确构造了同等强度的通用证据时，才允许受控展开。

### 1.2 扩展性目标：无需修改 planner 即可吸收新定理

扩展性的核心验收条件是：

> 向 Lean 库新增一个结论能够与 `NativeTMNPHard target` 或其可达内部子目标统一的一般定理后，在不修改 Python planner、不增加 relation 名称特判、不增加 benchmark case ID 和不注册专用 scaffold 的情况下，Agent 能发现该定理、生成它的前提子目标并尝试完成证明。

例如，当库中存在闭合的 Schaefer hardness 定理时：

```lean
theorem nPHard_of_not_schaefer_tractable
    (Γ : Gamma)
    (nonempty : ∀ symbol, (Γ.relationOf symbol).Nonempty)
    (hardSide : ¬ Γ.IsSchaeferTractable) :
    NativeTMNPHard (cspOf Γ)
```

Agent 应通过结论统一自动发现它，而不是在 Python 中检查 `NAE3`、`NAE4`、`EXACTLY-t-OF-k` 或特定源文件字符串。

### 1.3 规划目标：开放式路线提出，封闭式最终验证

模型可以：

- 提议使用哪个定理；
- 提议定理参数如何实例化；
- 提议新的辅助 lemma；
- 改变上一轮失败的数学路线；
- 选择直接定理、归约组合、反射证明或新归约创作；
- 在受控工作区内生成完整候选 Lean 源码。

模型、Python planner、JSON、缓存、日志和 benchmark metadata 都不能直接授予数学能力。唯一的最终正确性依据是：

1. 候选源码能够在目标 Lean 环境中 elaboration；
2. 最终声明具有用户请求的精确类型；
3. Lean kernel 接受完整证明项；
4. 默认策略下不存在 `sorry`、`admit`、`sorryAx` 或未经允许的新公理。

“允许模型提出路线”和“信任模型提出的路线”必须严格区分。前者是通用智能所必需的，后者仍然禁止。

### 1.4 非目标

核心 Agent 不再以以下事项作为默认产品目标：

- 命中隐藏 oracle 中的 gold route；
- 保证模型调用次数大于零；
- 强制为已有定理重新创作一条新归约；
- 为每道 benchmark 维护固定 DAG；
- 逐节点保存发布级 hash receipt；
- 在普通求证中执行独立 replay、fresh scan、mutation scorer 或 oracle isolation；
- 因 benchmark construction policy 禁止一条数学上合法且 Lean 可验证的更优路线；
- 把当前项目扩张成可证明任意 Lean `Prop` 的通用 theorem prover；
- 在 NP-hard MVP 之前并列实现自动 membership、NP-completeness 和其他复杂性类别；
- 绕开 ComplexityReduction 的 `CertifiedReduction`/`CertifiedPath` 体系，建立一套平行且不兼容的归约证书。

其中审查、复现和计分需求只能存在于显式选择的 benchmark 或 strict-release profile；扩大到其他复杂性目标则属于 NP-hard MVP 完成后的独立路线图，不自动进入当前范围。

## 2. 核心可信边界

### 2.1 默认保留的正确性义务

默认 `research` profile 只保留以下硬边界：

1. **精确目标类型**：最终声明必须与用户请求的 Lean 类型通过 elaboration 和 definitional equality 对齐。
2. **Kernel 验证**：最终 artifact 必须由 Lean kernel 接受。
3. **无占位证明**：禁止 `sorry`、`admit`、`sorryAx` 及等价绕过。
4. **公理策略**：默认只允许项目明确配置的基础公理集合；新增领域公理必须显式授权，不能由模型自行声明。
5. **程序与证明同索引**：`CertifiedReduction`、`TMPolyTimeMap`、`PolyProg` 等现有依赖类型约束必须继续保证构造、复杂度和语义证明指向同一程序。
6. **资源边界**：搜索深度、状态数、Lean 检查次数、模型调用数和运行时间必须有界。
7. **工作区安全**：模型只能修改当前任务允许的候选文件，不能覆盖用户源码或扩大任务授权范围。

### 2.2 从核心路径删除的审查义务

以下逻辑必须从默认 orchestrator 中移除：

- benchmark registry 与 suite hash 前置校验；
- oracle、gold、split 和 statement hash 对求证路线的约束；
- route ID 冻结与 shortest-route 审查；
- “模型不得选择 theorem name 或 route”的限制；
- 固定 task class 后禁止改变数学策略；
- 每个节点的 dependency receipt、publication manifest 和 token ledger 验收；
- candidate deletion audit、stale checkpoint audit 和 scorer mutation；
- 默认 independent replay；
- 为 benchmark directness 而禁止合法 composition；
- 为保证 `model_calls > 0` 而绕开已有通用定理；
- 将标准公理审查、endpoint equality、fresh scan 分散执行多次。

默认路径只在最终 artifact 上进行一次必要验证。重复验证和发布证据收集移动到可选 profile。

### 2.3 三种运行 profile

| Profile | 默认 | 用途 | 验证范围 |
|---|---:|---|---|
| `research` | 是 | 日常自动证明与库开发 | 精确类型、kernel、占位/公理策略、基本资源边界 |
| `strict-release` | 否 | 发布候选和高可信复现 | 在 `research` 成功结果上增加 clean replay、依赖 hash、完整 axiom provenance |
| `benchmark` | 否 | 冻结实验与论文评分 | 显式 suite、oracle 隔离、construction policy、计分与 mutation |

三个 profile 必须共享同一个核心证明搜索器。`strict-release` 和 `benchmark` 只能包装或拒绝核心结果，不能修改核心搜索器对数学路线的理解，也不能把 benchmark case 信息注入核心 theorem planner。

## 3. 当前架构的根本缺口

### 3.1 只会搜索闭合边，不会应用带前提的定理

当前 resolver 主要处理：

```text
hardness seed ── CertifiedReduction ──> target
```

这相当于在闭合 capability 图上做路径搜索。一般定理则具有：

```text
premise₁ → premise₂ → ... → target
```

甚至包含依赖参数、类型类前提和 existential witness。当前系统没有将 theorem telescope 展开为可递归求解的子目标，因此无法自然应用 Schaefer dichotomy、参数化 family theorem 或其他数学分类定理。

### 3.2 theorem discovery 受 registry 和 attribute 限制

库中未注册为 canonical capability、但具有正确 Lean 类型的 theorem 可能对 planner 不可见。核心系统必须从 elaborated environment 构建 typed theorem index，而不是把 attribute registry 当作知识边界。

Attribute 可以继续提供：

- 搜索优先级；
- theorem 角色提示；
- 不透明或不推荐标记；
- 人工分类 metadata。

但 theorem 是否可应用必须由其 elaborated type 和 Lean 统一结果决定。

### 3.3 固定 DAG 把安全策略变成能力边界

当前 planner 在模型调用前就固定 task class、节点集合、allowed imports 和 allowed primitives。模型只能填写选定路线中的局部 body，不能提出另一条通用定理路线。

这种机制可以保留为某些高风险 synthesis action 的文件编辑约束，但不能继续支配 theorem reuse 和高层规划。

### 3.4 case-specific scaffold 代替了数学抽象

Boolean CSP 当前通过 relation 源码字符串选择 NAE3/4/5 scaffold。该策略必须从核心 planner 中删除。类似的按 case、arity、文件名或 benchmark family 分支都视为架构债务。

### 3.5 审查、benchmark 与求证核心混合

当前系统把 route discovery、authoring、oracle isolation、checkpoint、replay 和 scoring 混在同一运行链，导致：

- 普通 theorem reuse 承担发布级成本；
- planner 为满足审查协议而拒绝探索；
- benchmark 的 direct-new 要求污染产品行为；
- 新数学定理无法自然改变求解策略。

本计划要求先拆出独立核心，再决定旧审查代码是保留为可选工具还是删除。

## 4. NP-hard-first 目标架构

```text
精确目标：NativeTMNPHard target
      │
      ▼
Goal Intake / PresentedProblem 与 endpoint normalization
      │
      ▼
ComplexityReduction NP-hard Rule Kernel
      │
      ├── 现有 NPHardResolver fast path
      ├── exact registered hardness / completeness projection
      ├── NativeTMNPHard.alongPath / ofCompleteAlongPath
      ├── CertifiedReduction.comp / CertifiedPath
      ├── CertifiedEquiv / CertifiedPresentationChange
      └── hardness theorem-schema application
      │
      ▼
Hybrid NP-hard Search
      │
      ├── 向后：从 NativeTMNPHard target 应用定理规则
      ├── 向前：从 hard/complete seed 搜索 certified path
      ├── 汇合：在 hub/path/reduction endpoint 处相遇
      └── 性质前提：Premise Solvers / bounded Lean automation
      │
      ├── 成功：重建完整 Lean proof term
      └── 复用失败：模型规划与新 CertifiedReduction synthesis
                    │
                    └── 从合适 hard/complete hub 到 target
      ▼
精确 NP-hard Artifact
      │
      ▼
一次最终 Lean elaboration + kernel check
      │
      ├── research：返回验证结果
      ├── strict-release：附加 replay/provenance
      └── benchmark：附加 suite/scorer
```

核心不是纯 backward reasoning，也不是当前 resolver 的纯 closed-edge forward search，而是二者的混合：

- 从 `NativeTMNPHard target` 向后寻找 conclusion 可统一的 theorem schema；
- 从已验证的 `NativeTMNPHard`/`NativeTMNPComplete` seed 沿 `CertifiedReduction` 图向前搜索；
- 在 theorem 产生的 hub、path 或 reduction endpoint 与 forward frontier 汇合；性质前提交给递归 theorem search 和 premise solvers；
- 只有无法通过现有证书代数闭合时，才创建新的归约程序和证书。

### 4.1 ComplexityReduction 原生 NP-hard Rule Kernel

第一版 planner 必须显式理解一小组稳定的、由库类型决定的证明规则。这些规则构成搜索语义的主干，不是 benchmark 特判：

| 优先级 | 规则 | 结果 |
|---:|---|---|
| R0 | local/exact registered hardness | 直接得到 `NativeTMNPHard target` |
| R1 | `NativeTMNPComplete.nativeHardness` | 从 exact complete endpoint 投影 hardness |
| R2 | `NativeTMNPHard.alongPath` | 从 `NativeTMNPHard hub` 与 `CertifiedPath hub target` transport |
| R3 | `NativeTMNPHard.ofCompleteAlongPath` | 从 `NativeTMNPComplete hub` 与路径得到 target hardness |
| R4 | `CertifiedPath.step/cons/append`、`CertifiedReduction.comp` | 构造和组合精确方向的路径 |
| R5 | `CertifiedEquiv`、`CertifiedPresentationChange` 的 forward/backward reduction | 解决 presentation 与 representation 差异 |
| R6 | conclusion 可统一的一般 hardness theorem | 产生待递归求解的性质或证书前提 |
| R7 | 新 `CertifiedReduction hub target` synthesis | 现有知识不足时扩展路径图 |

规则内核必须直接调用库中的 constructor/theorem，不得复制 `NativeTMNPHard`、`CertifiedReduction` 或 path composition 的语义到 Python。Python 只管理候选、预算和搜索状态；Lean 负责实例化并生成权威 proof term。

### 4.2 根目标规范形

每个任务在进入搜索后归一化为：

```text
RootGoal
  target        : exact PresentedProblem Expr
  proposition   : NativeTMNPHard target
  request?      : optional TypedNPHardRequestV1
  endpoint key  : Lean-side normalized fingerprint
```

如果输入目标不是 definitionally equal 于 `NativeTMNPHard target`，NP-hard MVP 必须明确拒绝并报告“不属于当前产品目标”，而不是悄悄切换成通用定理证明模式。

### 4.3 Proof reconstruction 是核心能力

搜索成功必须产生可重建的 Lean application tree，而不只是“找到一条路线”：

```text
NativeTMNPHard target
└── NativeTMNPHard.alongPath hubHardness path
    ├── hubHardness : NativeTMNPHard hub
    └── path : CertifiedPath hub target
        ├── edge₁ : CertifiedReduction hub middle
        └── edge₂ : CertifiedReduction middle target
```

每个 rule application 保存 declaration、显式参数、子证明引用和目标 fingerprint。最终统一在 job-local Lean module 中重建完整 declaration，再进行一次根级 elaboration 与 kernel 验证。证明树 JSON 仅用于调试，不得替代 Lean artifact。

如果调用方使用 `TypedNPHardRequestV1`，最终还必须复用协议层：

- exact hardness 使用 `TypedNPHardResultV1.fromRegistered`；
- hub-to-target path 使用 `TypedNPHardResultV1.fromPath`；
- caller-facing theorem 通过 `extractNativeHardness` 得到。

一般 hardness theorem 得到的 exact target hardness 也可以进入 `fromRegistered` 这一证据形态；无需为 theorem-schema 新建平行结果协议。

### 4.4 Hardness seed 与方向策略

默认可信 seed 集合来自当前 Lean 环境中已验证的 native hardness/completeness declarations，包括但不限于：

- `NativeCookLevin.canonicalThreeSATNativeCompleteness`；
- production registry 中通过类型和公理策略重新验证的 `NativeTMNPHard`；
- production registry 中通过验证的 `NativeTMNPComplete`。

对每个 seed，唯一默认归约方向是：

```text
hard/complete seed ── CertifiedPath ──> requested target
```

`target → seed` 不能证明 target NP-hard，只能作为错误方向诊断或在存在额外双向 equivalence 证据时使用。选择 synthesis hub 时，按“已有可复用路径长度、presentation 距离、可用 gadget/theorem、预期证明成本”排序；canonical structured 3SAT 始终是可解释的基础 completeness root，但不强制所有任务都从它直接起步。

### 4.5 Library-first 职责边界

为了确保项目扩展的是 ComplexityReduction，而不是在它旁边再造一个系统，职责必须固定为：

| 层 | 负责内容 |
|---|---|
| ComplexityReduction Lean 库 | 问题表示、`CertifiedReduction`、`CertifiedPath`、hardness/completeness、transport、presentation adapter、polytime combinator、可复用数学 theorem |
| Lean Agent meta 层 | theorem/module index、真实类型统一、前提提取、application skeleton、proof reconstruction、最终检查 |
| Python orchestration 层 | 搜索状态、排序、预算、回溯、模型调用、候选工作区和诊断汇总 |
| 模型 | 数学路线建议、helper lemma 和缺失 reduction 的候选实现 |

若同一种前提或归约模式在多个 family 中重复出现，应优先把它抽象为 ComplexityReduction 中的通用 theorem/combinator，再由索引自动吸收；不得用新的 Python family 分支长期填补库抽象缺口。

Agent 新生成的所有程序型归约必须最终落入 `CertifiedReduction` 或由它组成的 `CertifiedPath`。Python `Rule`、`Action`、JSON proof tree 和模型输出都只是控制数据，不是第二套数学证书。

## 5. NP-hard 相关的 Typed Theorem Index

### 5.1 索引范围

索引能力可以覆盖当前 Lean environment 中所有可见声明，但每个 NP-hard 任务必须按需检索，不能把“全库所有 theorem 平铺给搜索器”作为默认行为。

首层索引只检索 conclusion head 属于 NP-hard 闭环的声明：

- `NativeTMNPHard`；
- `NativeTMNPComplete`；
- `CertifiedReduction`；
- `CertifiedPath`；
- `CertifiedEquiv`；
- `CertifiedPresentationChange`。

当这些规则实例化产生新的前提后，才按该前提的 conclusion head 递归扩大检索范围。索引总体应覆盖：

- 相关 `theorem`、`lemma`；
- 返回证书的 `def`；
- structure constructor；
- 已注册 reduction、hardness、membership 和 completeness capability；
- 未注册但结论类型匹配的声明；
- presentation adapter、equivalence 和 transport theorem；
- decidability/reflection theorem；
- polynomial-time combinator；
- 用户输入模块中的局部公共 theorem。

已有 registry/attribute 不再是知识边界，但继续作为高价值种子和排序提示。应优先查询：

1. 当前 `NPHardResolver` 已验证的 exact seed 与 forward path；
2. ComplexityReduction certificate/transport 模块中的原生规则；
3. 带 capability attribute 的候选；
4. 未注册、但 conclusion 可统一的声明。

这样既保留“新增 theorem 不改 Python 即可吸收”的开放性，也避免在每个 NP-hard 目标上退化为无方向的通用 Lean theorem search。

默认排除：

- private declaration；
- unsafe 或无法在当前信任策略下使用的声明；
- 明确标记为 benchmark oracle、gold、test poison 的模块；
- 结论不在 `Prop` 或不产生可用构造且无规则价值的声明；
- 依赖禁止公理且当前 profile 不允许的声明。

### 5.2 Index entry

每个声明至少记录：

```text
declaration name
owning module / required import
universe parameters
explicit and implicit binders
typeclass binders
propositional premises
data-producing premises
normalized conclusion
conclusion head constant
conclusion fingerprint
reducibility/opacity information
optional role attributes
known axiom basis or deferred-audit marker
dependency fingerprint
```

索引不得只保存 pretty-printed type 字符串。权威匹配必须在 Lean `MetaM` 中对 `Expr` 执行。

### 5.3 索引构建方式

新增 Lean 侧模块，建议位于：

```text
Lean/Reference/ComplexityReduction/Agent/Reduction/TheoremIndex.lean
Lean/Reference/ComplexityReduction/Agent/Reduction/GoalProbe.lean
Lean/Reference/ComplexityReduction/Agent/Reduction/RuleApplication.lean
```

Lean 侧负责：

- 枚举 environment declaration；
- 展开 theorem telescope；
- 对 conclusion 做受控 `whnf`；
- 计算结构化 fingerprint；
- 按 conclusion head 建倒排索引；
- 对给定目标执行真实 metavariable unification；
- 返回可重建的候选规则、参数赋值和前提类型。

Python 不重新实现 Lean unification，也不通过字符串替换构造类型。

索引分成两个层级：

1. **Environment index**：对当前已导入环境中的声明保存可直接用于 MetaM unification 的 typed entry；
2. **Project module catalog**：离线扫描 Lake 项目的公共 Lean 模块，记录模块名、导出的 declaration 名、轻量 conclusion fingerprint 和来源文件，用于发现尚未位于当前 import closure 的候选。

当 module catalog 命中潜在候选时，Agent 在临时 probe module 中增加对应 import，重新由 Lean 构建 environment entry 并执行真实 unification。catalog 中的字符串或离线 fingerprint 只能用于召回，不能授予 theorem 可用性。

只扫描当前 environment 而要求调用者预先知道并 import 正确 theorem 模块，不满足“全库定理发现”的扩展性目标。

### 5.4 增量与缓存

Index cache 绑定：

- Lean toolchain；
- lake manifest；
- import closure；
- declaration environment fingerprint。

缓存仅用于性能，不能直接授予 proof。最终候选仍需在当前环境重新 elaboration。开发环境变化时允许局部增量重建，而不是每个目标扫描全库。

### 5.5 索引验收

必须增加 synthetic regression：

1. 在测试 Lean 模块中新增一个未加 attribute、且初始输入模块未 import 的直接 `NativeTMNPHard` theorem；
2. 新增一个带两个前提、结论为 `NativeTMNPHard (P x)` 的一般 theorem；
3. 新增一个产生 `CertifiedReduction (A x) (B x)` 的 polymorphic/dependent theorem；
4. module catalog 找到所需 import，临时环境重新验证候选；
5. 不修改 Python planner；
6. Agent 自动发现并应用它们。

若必须增加 theorem name allowlist 或 Python 分支才能通过，则 typed theorem index 不算完成。

## 6. Lean 驱动的结论统一

### 6.1 统一输入

对每个开放目标，Lean 侧接收：

- 精确目标 `Expr`；
- local context；
- 当前允许的 transparency mode；
- profile 的公理和模块策略；
- 搜索预算。

### 6.2 统一过程

对于候选 theorem：

1. 创建 theorem universe metavariables；
2. 依次实例化非前提参数；
3. 将 theorem conclusion 与目标执行 `isDefEq`；
4. 收集成功统一产生的参数赋值；
5. 把尚未解决的显式前提和类型类前提转成子目标；
6. 生成可重建的 theorem application skeleton；
7. 返回候选成本和所有子目标的规范化 fingerprint。

统一失败必须提供结构化原因，例如：

- conclusion head 不匹配；
- endpoint 不可 definitionally equal；
- universe constraint 失败；
- implicit parameter 无法推断；
- typeclass 前提未解；
- theorem 依赖当前 profile 禁止的公理。

### 6.3 不跨进程持久化 Lean metavariable

Python 状态中不得保存不可重建的 Lean metavariable ID。持久状态保存：

- theorem declaration；
- 规范化目标；
- 已确定的显式参数表达式；
- 前提序号和精确类型；
- application skeleton 的内容 hash。

每次验证由 Lean 重新建立 metavariable context 并 elaboration。

### 6.4 直接 theorem 与 schema theorem

统一成功且无剩余前提时，候选是直接 theorem reuse。

统一成功但有剩余前提时，候选是 inference rule：

```text
subgoal₁ ... subgoalₙ
────────────────────── theorem application
original goal
```

两者必须进入同一个搜索器，不能继续把带前提 theorem 视为“没有闭合路线”。

## 7. Hybrid NP-hard 搜索器

### 7.1 核心状态

新增通用 Python package，建议使用：

```text
agent/reduction/
  models.py
  theorem_index.py
  lean_bridge.py
  proof_state.py
  search.py
  ranking.py
  premise_solvers.py
  model_planner.py
  synthesis.py
  verifier.py
  profiles.py
  orchestrator.py
```

一个 proof state 至少包含：

```text
root goal
open goals
local contexts
selected rule applications
completed proof fragments
known hard/complete seeds
forward reachable endpoints and certified paths
backward theorem obligations
frontier meeting points
imports
search cost
depth
Lean-check count
model-call count
cycle fingerprints
last diagnostics
```

### 7.2 默认 action 顺序

对根 NP-hard 目标先执行第 1 项；随后对每个开放目标按其类型执行其余可适用 action：

1. 调用现有 `NPHardResolver` fast path，尝试 exact hardness 或现有 seed-to-target path；若返回 no-path/aggregate-missing 等非成功结果，记录诊断并继续开放搜索，不得直接终止任务；
2. local hypothesis、已有闭合 hardness theorem 和 completeness projection；
3. `alongPath`/`ofCompleteAlongPath` 与已注册 reduction graph 的向前扩展；
4. 带前提的一般 hardness theorem 的向后实例化；
5. 在向前 endpoint 与向后所需 hub/reduction 之间做 meet-in-the-middle；
6. presentation/equivalence adapter；
7. typeclass、`simp`、有限 reflection 和专用 premise solver；
8. 有界 Lean tactic automation；
9. 模型路线规划、helper lemma proposal 与路线切换；
10. 从选定 hard/complete hub 到目标的新 `CertifiedReduction` synthesis。

此顺序是成本偏好，不是硬编码路线。搜索器必须保留多个候选，不能因第一个 theorem 产生困难前提就永久丢弃其他路线。

### 7.3 搜索算法

第一版本采用有界 best-first 或 beam search，但搜索节点同时包含 backward obligations 和 forward certified frontier：

- normalized goal fingerprint 做 cycle detection；
- endpoint fingerprint 对 forward reachable path 做去重；
- 以 `CertifiedPath` 类型方向检查所有 forward edge；
- backward 子目标出现 `NativeTMNPHard hub`、`NativeTMNPComplete hub`、`CertifiedReduction hub target` 或 `CertifiedPath hub target` 时，主动与 forward frontier 尝试汇合；
- 相同目标与相同 local context 做 memoization；
- 明显更差的重复状态做 subsumption；
- 每条 theorem application 计基础成本；
- 每个未解决前提增加估计成本；
- 模型调用和新源码 synthesis 具有更高成本；
- 禁止公理或 endpoint 不匹配的候选直接丢弃；
- 达到预算后返回最小、最具体的 blocker，而不是伪造成功。

搜索不得为了“通用”而忽略现有 reduction graph。它是 ComplexityReduction 已积累知识的高性能索引，应作为 NP-hard rule kernel 的一级能力；但它也不得继续成为唯一 planner。

### 7.4 默认预算

所有预算可配置，但必须有合理默认值：

```text
max_search_depth
max_expanded_states
max_candidates_per_goal
max_lean_checks
max_model_calls
max_synthesis_rounds
wall_clock_timeout
```

预算耗尽时报告：

- 最接近闭合的候选路线；
- 未解决子目标；
- 每个子目标尝试过的 solver；
- Lean 最后诊断；
- 是否存在需要新库定理的明确能力缺口。

### 7.5 路线可修改

模型或确定性搜索选择一条路线后，如果后续前提无法完成，系统必须能够回溯并选择另一条 theorem。当前“task class 一旦确定便不可改变”的限制必须删除。

## 8. 可插拔 Premise Solver

### 8.1 统一协议

每种 solver 实现统一接口：

```text
supports(goal, context) -> confidence
propose(goal, context, budget) -> candidate proof actions
check(candidate) -> Lean-verified result
```

Solver 只能提出候选，不能绕过最终 Lean 检查。

### 8.2 基础 solver

第一批必须实现：

1. **LocalContextSolver**
   - local hypothesis；
   - assumption；
   - constructor/projection；
   - equality substitution。

2. **DefinitionalSolver**
   - `rfl`；
   - controlled unfolding；
   - presentation abbreviation；
   - exact endpoint definitional equality。

3. **TypeclassSolver**
   - `synthInstance`；
   - decidability、finiteness、encoding instance。

4. **SimpSolver**
   - bounded `simp`；
   - theorem-supplied simp set；
   - 禁止无界展开大定义。

5. **FiniteReflectionSolver**
   - finite enumeration；
   - `decide`/`native_decide` 可用性探测；
   - 显式 counterexample/witness 证书；
   - 反射 theorem。

6. **ReductionGraphSolver**
   - 直接包装现有 `NPHardResolver`/closed resolver 的 seed 与 certified route 能力；
   - 同时提供根目标 fast path、forward frontier 和内部 premise solver 三种入口；
   - 可以解决 `CertifiedReduction A B` 或相应 transport 子目标。

7. **PolynomialCombinatorSolver**
   - 组合已有 `TMPolyTimeMap`、`Primitive`、`PolyProg`；
   - 解决标准 list/map/compose/transport 复杂度前提。

8. **LeanTacticSolver**
   - 有界运行 `aesop`、`omega`、`simp_all` 等；
   - 记录所用 tactic 和超时；
   - 最终保存 elaborated proof，而不是只保存 tactic 成功日志。

### 8.3 领域 solver 与核心解耦

允许增加 Boolean CSP、图论、数值编码等领域 solver，但必须满足：

- 通过类型或 typeclass capability 注册；
- 不检查 benchmark case ID；
- 不在核心搜索器中添加 relation 名称分支；
- 新 solver 插件删除后，通用 theorem search 仍可工作；
- solver 输出仍由 Lean 检查。

## 9. 模型在新架构中的职责

### 9.1 模型可见信息

模型 planner 可以看到：

- 当前精确目标和 local context；
- typed theorem index 返回的候选及其精确类型；
- 各候选统一后产生的子目标；
- 已尝试路线和 Lean 诊断；
- 相关公共源码；
- 剩余预算。

模型不需要接触：

- benchmark oracle；
- gold proof；
- scorer-only construction route；
- 未经请求的用户私有文件。

### 9.2 模型允许的规划输出

模型可以返回以下 action：

```text
apply_theorem
instantiate_argument
solve_premise_with_tactic
prove_helper_lemma
define_auxiliary_object
compose_reductions
switch_route
synthesize_reduction
request_more_relevant_source
```

每个 action 必须携带目标 fingerprint 和候选声明，不允许用自然语言声称目标已经证明。

### 9.3 模型的两类工作

模型调用分为：

1. **Strategy proposal**
   - 选择或组合数学路线；
   - 分析前提；
   - 提出辅助 lemma；
   - 可以在失败后改变路线。

2. **Lean implementation**
   - 为选定 action 生成 proof term、tactic block、definition 或 theorem body；
   - 接收 Lean diagnostics 修复；
   - 允许同时新增与当前路线直接相关的辅助声明。

不再要求所有问题都套用同一个 8 节点或 16 节点 DAG。

### 9.4 模型失败不污染可信状态

以下情况只产生被拒绝候选：

- theorem name 不存在；
- 类型无法统一；
- 使用错误 endpoint；
- 引入 forbidden axiom；
- 使用 `sorry`；
- proof 不编译；
- 复杂度 witness 指向不同程序。

搜索器随后可以修复、回溯或尝试其他路线。

## 10. 新归约 Synthesis Fallback

### 10.1 触发条件

只有以下路径都未闭合时才进入新归约创作：

- 直接 theorem；
- theorem schema；
- reduction graph composition；
- premise solvers；
- 模型辅助 theorem reuse。

进入 synthesis 不再要求 benchmark 显式声明 `direct_new_edge`。它是通用 Agent 在现有知识不足时的正常 fallback。

对 `NativeTMNPHard target` 根目标，synthesis 默认不是重证 `NativeTMNPHard` 的展开定义，而是：

1. 从已验证 hard/complete seeds 中选择合适 hub；
2. 生成 `CertifiedReduction hub target` 或多步 `CertifiedPath hub target`；
3. 使用 `NativeTMNPHard.alongPath` 或 `ofCompleteAlongPath` 组装最终 hardness；
4. 如目标只与某个已知 endpoint 存在 presentation 差异，优先合成/证明 adapter，而不是重写整个归约。

只有没有可用 hardness seed、且库中存在另一条足以构造通用 hardness 的数学定理时，才允许采用其他根级证明形态。

### 10.2 动态分解

Synthesis 根据目标类型动态生成 obligations。例如 `CertifiedReduction source target` 通常需要：

- instance transformation；
- target representation/encoding 对齐；
- direct-TM 或 polynomial program；
- forward semantics；
- reverse semantics；
- program/run coherence；
- certificate assembly。

但节点必须从目标 certificate 的实际 constructor 和缺失 metavariables 导出，而不是来自固定 Python 清单。若某个库 theorem 已经封装部分义务，搜索器应直接应用并减少剩余子目标。

### 10.3 辅助声明

模型可以在 job-local module 中创建：

- helper definitions；
- gadget；
- invariant；
- witness transformation；
- local semantic lemmas；
- local polynomial lemmas。

这些声明的依赖图由 Lean 类型自然形成。系统只需保证：

- 不覆盖库源码；
- 不逃出任务工作区；
- 无占位证明或禁止公理；
- 最终 root declaration 闭合。

### 10.4 成功后的能力复用

成功生成的新 theorem 默认只存在于当前 artifact。用户显式要求发布时，才：

- 移入正式库模块；
- 添加文档与测试；
- 可选添加 capability attribute；
- 更新 theorem index cache。

核心 Agent 不得自动修改全局 registry 或把一次未审阅 synthesis 永久加入库。

## 11. Boolean CSP：旗舰领域纵切，而非引擎前置条件

Boolean CSP 20 题是新架构的旗舰验收案例，但不作为确定性 NP-hard theorem/path reuse 引擎或最小新归约闭环的前置条件。通用搜索、规则内核和 proof reconstruction 必须先通过更小的 synthetic 与非 Boolean CSP theorem-schema 回归，避免 Schaefer 形式化规模掩盖 Agent 架构是否成立。

完成该纵切时，仍不得通过 case-specific planner 或 20 份专用 proof 绕过一般 theorem。

### 11.1 目标公共 theorem

最终必须提供无 caller-supplied reduction witness、无新增领域 axiom 的闭合接口：

```lean
theorem nPHard_of_not_schaefer_tractable
    (Γ : Gamma)
    (nonempty : ∀ symbol : Γ.Symbol, (Γ.relationOf symbol).Nonempty)
    (hardSide : ¬ Γ.IsSchaeferTractable) :
    NativeTMNPHard (cspOf Γ)
```

或者一个结论 definitionally equal、同样只要求有限语言性质前提的 theorem。

### 11.2 必须消除的公理缺口

当前以下内容不能继续作为最终证明基础：

- `oneInThreeCoreNPHard` axiom；
- `exactlyTwo3CoreNPHard` axiom；
- `interpretation_hardCore_of_not_schaefer_tractable` axiom。

需要完成：

1. Exact Cover 到 positive 1-IN-3 CSP 的完整 executable；
2. 该 executable 的 direct-TM / polynomial proof；
3. 正反向 satisfiability proof；
4. `oneInThreeCoreNPHard` 的真实 certificate；
5. exactly-one / exactly-two pp-interpretation 的通用 substitution TM；
6. `exactlyTwo3CoreNPHard` 的真实 transport；
7. Schaefer expressive-power case analysis中剩余的 bijunctive、affine 与 hard-core assembly；
8. 从所得 interpretation 自动获得 `TMPolyTimeMap` 的通用 compiler。

### 11.3 PP interpretation 的通用 polynomial compiler

当前 `LanguageInterpretation` 已表达有限 gadget substitution 的语义，但调用者仍需提供 `interpretTM`。应新增一般 theorem：

```lean
noncomputable def interpret_tmPolyTime
    (interpretation : LanguageInterpretation Γ' Γ) :
    TMPolyTimeMap
      (FiniteDomainCSPTable.encodedType Γ')
      (FiniteDomainCSPTable.encodedType Γ)
      (interpret interpretation)
```

若无法对任意 representation 直接成立，则应明确最小、可自动生成的固定 gadget size / encoding coherence 前提，并由 typeclass 或 reflection 自动求解。

这一步完成后，Schaefer theorem 才能真正把数学 expressive-power 结果转化为库要求的 executable hardness certificate。

### 11.4 六类反证的有限反射

新增通用 Boolean CSP reflection 层：

- relation 非空检查；
- zero-valid / one-valid；
- meet closure；
- join closure；
- majority closure；
- affine closure；
- 从六个 `false` 结果反射得到 `¬ Γ.IsSchaeferTractable`。

对于 closure 失败，应产生明确有限 witness：

```text
Horn:       accepted a, accepted b, rejected (a ∧ b)
Dual-Horn:  accepted a, accepted b, rejected (a ∨ b)
Bijunctive: accepted a, b, c, rejected majority(a,b,c)
Affine:     accepted a, b, c, rejected xor(a,b,c)
```

证明可以由 `decide`、反射 theorem 或生成的 witness lemma 完成，但必须最终由 kernel 检查，不得只相信 Python 真值表分类。

### 11.5 Agent 的预期搜索行为

输入：

```lean
NativeTMNPHard CaseXX.problem
```

预期自动过程：

1. unfolding/definitional solver 识别 `problem = cspOf gamma`；
2. theorem index 找到 Schaefer hardness theorem；
3. conclusion unification 实例化 `Γ := CaseXX.gamma`；
4. 产生 `nonempty` 与 `¬ IsSchaeferTractable` 两个子目标；
5. FiniteReflectionSolver 完成两个子目标；
6. application theorem 组装最终 proof；
7. Lean kernel 编译。

此过程不得依赖：

- case ID；
- split；
- relation 名称；
- arity；
- NAE scaffold；
- `EXACTLY-t-OF-k` 专用 Python 分支；
- hidden oracle。

### 11.6 Boolean CSP 验收

必须同时满足：

- 20/20 题通过最终 kernel 验证；
- 19 个 hard-side case 使用同一一般 theorem family；
- canonical case 可以继续走已有直接 endpoint；
- 默认不需要模型调用；
- 删除 NAE3/4/5 planner 特判后结果不退化；
- 添加至少 10 个运行时新生成、未出现在 benchmark 中的 finite Gamma，仍能自动分类并证明 hard-side 实例；
- 核心 Python 文件中搜索不到 20 个 case ID、relation 名称或 arity 匹配表。

如果只能通过为每种 relation 增加 scaffold，则本纵切失败。

## 12. Schaefer 之前的 NP-hard 通用性验收

这些回归属于通用引擎 MVP，必须先于 Schaefer 闭合完成。它们验证 Agent 的能力来自 ComplexityReduction 证书代数和 theorem schema，而不是 Boolean CSP 特化。

### 12.1 参数化 reduction theorem

测试一个 theorem：

```text
P x → CertifiedReduction (A x) (B x)
```

Agent 应自动实例化 `x`、递归证明 `P x`，并把所得 edge 与已知 hard seed 组合成目标 hardness。

### 12.2 Transport theorem

测试：

```text
PresentedEquivalent A B →
NativeTMNPHard A →
NativeTMNPHard B
```

Agent 应分别解决 equivalence 与 source hardness，而不是要求预注册一条闭合 edge。

### 12.3 多跳 certified route 与 presentation change

测试：

```text
NativeTMNPHard A
CertifiedReduction A B
CertifiedPresentationChange B C
────────────────────────────────
NativeTMNPHard C
```

Agent 应通过 `CertifiedPath`/`CertifiedReduction.comp` 和 presentation adapter 组装证明，且所有边方向精确。该测试不要求把 `NativeTMNPComplete C` 作为产品目标。

### 12.4 未注册 theorem 热插拔

在测试模块新增一个未注册 theorem 后：

- theorem index 自动发现；
- planner 无代码变化；
- 新 theorem 可以改变原目标的最佳路线；
- 删除 theorem 后系统恢复到其他路线或精确 blocker。

### 12.5 最小动态 synthesis

至少选择一个不依赖 Schaefer 的小型 target family：库中已有 hard seed，但没有 seed-to-target edge。Agent 必须动态创建一个新的 `CertifiedReduction hub target`，随后使用库的 hardness transport 得到 `NativeTMNPHard target`。验收重点是根证明结构和证书复用，不是 benchmark direct-edge policy。

## 13. 代码迁移方案

### 13.1 新增 NP-hard-first 通用核心

优先新增 `agent/reduction/`，避免继续把所有能力塞入 `agent/hardness/`。这里的“通用”指不依赖 problem family、relation 名称或 benchmark case 的 NP-hard 自动归约核心，不表示首版支持任意 Lean 根目标。该 package 不得 import benchmark runner、oracle loader 或 scorer。

建议模块职责：

| 文件 | 职责 |
|---|---|
| `models.py` | NP-hard RootGoal、Rule、SearchState、Action、Result schema |
| `lean_bridge.py` | 调用 Lean goal probe、unifier 和 candidate checker |
| `theorem_index.py` | typed index cache、查询与 import discovery |
| `proof_state.py` | open goals、proof fragments、回溯状态 |
| `search.py` | best-first/beam hybrid NP-hard search |
| `ranking.py` | 成本模型和候选排序 |
| `premise_solvers.py` | solver registry 与基础 solver |
| `model_planner.py` | 开放式 strategy proposal |
| `synthesis.py` | 动态新归约/辅助 lemma 创作 |
| `verifier.py` | 最终 artifact 与 kernel 验证 |
| `profiles.py` | research/strict-release/benchmark 分层 |
| `orchestrator.py` | 通用任务生命周期 |

### 13.2 Lean 侧通用模块

新增：

```text
ComplexityReduction.Agent.Reduction.TheoremIndex
ComplexityReduction.Agent.Reduction.GoalProbe
ComplexityReduction.Agent.Reduction.RuleApplication
ComplexityReduction.Agent.Reduction.Reflection
ComplexityReduction.Agent.Reduction.FinalCheck
```

现有 registry、resolver 和 authoring meta code 必须被这些模块复用，但不得成为唯一入口。尤其：

- `NPHardResolver.resolveNPHardRequestV1` 保留为 exact/closed-route fast path；
- `ClosedResolver` 的路径搜索暴露为 forward-frontier 服务；
- `TypedNPHardRequestV1`/`TypedNPHardResultV1` 保留为稳定 NP-hard 协议；
- 现有 authoring executor、candidate workspace、Lean diagnostics 和 artifact compiler 通过 adapter 接入 synthesis；
- 新 package 不得重新实现一套与这些类型不兼容的请求、路径或证书语义。

### 13.3 兼容现有 hardness CLI

现有 `scripts/prove_np_hard.py` 保留为薄适配器：

```text
parse NP-hard request
→ 构造精确 Lean goal
→ 调用 agent.reduction.orchestrator
→ 格式化 hardness-specific result
```

在 NP-hard MVP 内不新增任意 complexity goal 入口；直接扩展现有 `scripts/prove_np_hard.py`。它接受：

- input module；
- target problem declaration 或 `NativeTMNPHard target` goal expression；
- profile；
- search/model budgets；
- 输出目录。

benchmark runner 继续单独存在，但不得成为产品 CLI 的内部依赖。

### 13.4 旧代码的迁移原则

保留并复用：

- Lean input gate；
- exact endpoint normalization；
- certified reduction registry；
- TM/polytime combinators；
- model client；
- Lean diagnostic collection；
- candidate workspace sandbox；
- final artifact compiler。

重构为核心可组合服务：

- `NPHardResolver`，其失败转换为可继续搜索的结构化诊断；
- route graph search；
- authoring source discovery；
- semantic proof generator。

其中前两项是确定性高优先级能力，不得因“通用搜索”而被低优先级模型流程取代；后两项主要服务 synthesis fallback。

从核心删除：

- `_whole_reduction_authoring_seed_modules`；
- `_BOOLEAN_CSP_*_SCAFFOLD_*` planner maps；
- 通过 relation 源码字符串选择 task family；
- 默认固定 8/16 节点 whole-reduction DAG；
- `semantic_plan` 只能描述 NAE clause gadget 的固定 schema；
- benchmark policy 决定 theorem reuse 是否允许；
- final result 依赖 scorer 布尔值才能成为 verified。

旧 exact-edge、capability、frontier benchmark code 可以迁移到：

```text
agent/benchmark/
```

在核心迁移完成前允许保留兼容 wrapper，但新通用 package 不得反向 import 它们。

## 14. 实施任务与依赖顺序

### 固定 NP-hard 产品边界并切断 benchmark 对核心的控制

任务：

- 定义 `research`、`strict-release`、`benchmark` profiles；
- 建立只接受 `NativeTMNPHard target` 根目标的 orchestrator 空壳；
- 让现有 NP-hard CLI 能通过 `research` profile 调用新 orchestrator；
- 保留 `TypedNPHardRequestV1`/`TypedNPHardResultV1` 兼容层；
- 默认关闭 oracle、scorer、independent replay、route directness 和 publication receipt；
- 保留最终 kernel、exact type 和公理策略。

验收：

- 不提供任何 suite/manifest/oracle 仍能运行单个目标；
- 删除或禁用 benchmark package 后核心 smoke test 仍能运行；
- `research` 成功不依赖 scorer；
- 非 NP-hard 根目标得到明确的 unsupported-goal 结果；
- 旧 benchmark runner 仍可显式选择 `benchmark` profile。

### 建立 ComplexityReduction NP-hard Rule Kernel 与现有 fast path

任务：

- 将 `NPHardResolver` 接为根目标第一 fast path；
- 把 exact hardness、completeness projection、`alongPath`、`ofCompleteAlongPath`、path/reduction composition、equivalence/presentation adapter 编码为 typed rules；
- 暴露现有 closed resolver 的 seed、forward path 和 endpoint 查询；
- 实现每条规则的 Lean application 与根 proof reconstruction；
- 不复制库证书语义到 Python。

验收：

- exact registered hardness、complete-to-hardness、单边 path、多边 path 和 presentation transport 均能产生精确 `NativeTMNPHard target` artifact；
- 现有 resolver 能闭合的目标在新 orchestrator 中不退化；
- reverse-only edge 被类型方向拒绝；
- 最终 proof term 直接引用 ComplexityReduction 的原生 constructor/theorem。

### 建立按需 Typed Theorem Index、结论统一与规则实例化

任务：

- 实现 Lean environment declaration scan 和 conclusion-head 倒排索引；
- 建立 project module catalog，支持发现输入 import closure 之外的公共 theorem；
- 第一层只查询 NP-hard rule heads，随后按新 premise head 递归扩展；
- Lean MetaM unifier；
- dependent/implicit/typeclass binder 支持；
- rule application skeleton；
- premise extraction；
- 未注册 theorem 与 required import discovery；
- environment fingerprint 增量 cache；
- 结构化失败诊断。

验收：

- 零前提、单前提、多前提、dependent premise、universe-polymorphic theorem 均有回归；
- 未注册 hardness/reduction theorem 不修改 Python 即可被发现；
- 未预先 import 的 theorem 模块可被发现、加入临时 import 并由 Lean 重新验证；
- Python 不使用 pretty string 作为类型权威；
- 错误 endpoint 不会因字符串相似而匹配；
- 默认候选集不平铺无关的全库 theorem。

### 构建 Hybrid Search、proof reconstruction 与基础 Premise Solver

任务：

- proof state；
- backward theorem obligations + forward certified frontier 的 best-first/beam search；
- cycle detection、memoization、回溯；
- Local、Definitional、Typeclass、Simp、LeanTactic solver；
- reduction graph 的 fast path、frontier 与 premise-solver 三种接口；
- meet-in-the-middle；
- 完整 Lean application tree 重建。

验收：

- 两层和三层 theorem chaining；
- hard seed 前向路径与一般 theorem 后向前提能够汇合；
- 一个候选失败后自动换路线；
- 循环 theorem 不导致无限搜索；
- 预算耗尽产生精确 blocker；
- existing route 行为不退化；
- 所有成功都输出可单独编译的 `NativeTMNPHard target` declaration。

### 验收确定性 NP-hard theorem/path reuse 引擎

任务：

- 参数化 reduction theorem；
- property-premised hardness theorem；
- 多跳 path + presentation change；
- 未注册 theorem 热插拔；
- 错误方向、错误 endpoint 和困难前提下的回溯回归。

验收：

- 至少三种非 Boolean CSP theorem schema 自动闭合 NP-hard 根目标；
- 新 theorem 加入环境后不改 planner 即可改变可用路线；
- 核心 planner 中无 problem family/case ID 路由；
- 完成这些验收后，形成可交付的“通用 NP-hard theorem/path reuse 引擎”，但尚未满足自主创作新归约的完整 Agent MVP 定义。

### 接入开放式模型 Planner 并完成最小新归约纵切

任务：

- strategy action schema；
- theorem candidates 与子目标 prompt；
- route switching；
- helper lemma generation；
- Lean diagnostics feedback；
- 模型候选的逐 action 验证；
- 将现有 authoring executor 接成 `CertifiedReduction hub target` synthesis action；
- 完成一个不依赖 Schaefer 的最小“新 edge + hardness transport”案例。

验收：

- 模型可以选择未预写路线；
- 模型可以在路线失败后切换 theorem；
- hallucinated theorem 被拒绝但任务可以继续；
- 模型不能通过 JSON 状态伪造完成；
- 不再受固定 task class 限制；
- 一个此前没有 route 的 target 通过模型辅助构造 `CertifiedReduction hub target`，再由 `alongPath`/`ofCompleteAlongPath` 得到 exact hardness；
- 完成该纵切后，形成首个完整“通用 NP-hard 自动归约 Agent MVP”。

### 扩展多 family 动态 Reduction Synthesis

任务：

- 从目标 certificate constructor 推导缺失 obligations；
- 动态生成 job-local module；
- 支持 helper definitions 与多个相关 lemma；
- 组合现有 polytime/semantic theorem；
- 最终 root certificate assembly。

验收：

- 至少三个不同问题 family 的新归约创作；
- 每个任务的 obligation graph 可以不同；
- 不新增 Python family 分支也能处理新的 target presentation；
- synthesis 失败能够回到 theorem search 或报告具体缺口；
- 每个成功任务都以 `alongPath`/`ofCompleteAlongPath` 或等价的库 theorem 组装根 hardness。

### 完成 Schaefer/Boolean CSP 旗舰纵切

任务：

- Boolean CSP finite reflection；
- nonempty 与六类闭包 witness；
- 完成 hard-core certificates；
- 完成 PP interpretation polynomial compiler；
- 移除三个领域 axiom；
- 提供闭合 Schaefer hard-side theorem；
- 让 Agent 仅通过 theorem discovery、premise solving 和 kernel reconstruction 完成全部案例。

验收：

- 新 theorem 通过默认 axiom policy；
- Boolean CSP 20/20 通过；
- 额外随机/生成 Gamma 通过；
- planner 中无 Boolean relation、arity、case ID 或 scaffold 特判；
- Schaefer 相关工作不得回溯破坏已交付的通用 theorem/path reuse 引擎或最小 NP-hard Agent MVP。

### 清理旧封闭架构

只有 NP-hard rule kernel、typed theorem discovery、hybrid search、最小新归约、多 family synthesis 和 Boolean CSP 纵切均稳定后，才执行破坏兼容性的清理：

- 删除不再被兼容层使用的固定 Boolean CSP scaffold planner；
- 删除默认 whole-reduction 固定 DAG；
- 将 benchmark-only ledger/checkpoint/scorer 代码移出核心 package；
- 更新 README 和产品 CLI 文档；
- 将旧 exact-edge 活动报告标记为历史评测；
- 删除强制“唯一 benchmark runner 即唯一产品入口”的测试；
- 保留必要 benchmark regression，但与核心单测分开。

验收：

- `agent/reduction` 不 import `Benchmark`、`Evaluation` 或 scorer；
- 核心测试不加载 suite；
- 删除 benchmark 目录的副本后，NP-hard theorem-search 测试仍通过；
- 代码搜索不存在核心 planner 的 case ID/family name 路由表。

## 15. 测试体系

### 15.1 核心单元测试

新增：

```text
tests/test_np_hard_rule_kernel.py
tests/test_np_hard_theorem_index.py
tests/test_np_hard_goal_unification.py
tests/test_np_hard_hybrid_search.py
tests/test_np_hard_premise_solvers.py
tests/test_np_hard_search_backtracking.py
tests/test_np_hard_proof_reconstruction.py
tests/test_np_hard_model_planner.py
tests/test_np_hard_reduction_synthesis.py
tests/test_np_hard_profiles.py
```

### 15.2 Lean regression

新增 answer-independent synthetic modules，覆盖：

- exact hardness 与 completeness projection；
- 单跳/多跳 `CertifiedPath`；
- 未注册 hardness/reduction theorem；
- 多前提 hardness theorem；
- dependent theorem；
- theorem cycle；
- 两条可行路线；
- 一条错误近似 endpoint；
- 一条 reverse-only reduction；
- presentation/equivalence transport；
- typeclass premise；
- finite reflection；
- helper lemma synthesis；
- final exact `NativeTMNPHard target` artifact。

### 15.3 NP-hard MVP generalization regression

在 Boolean CSP 之前固定运行：

- direct theorem；
- existing seed-to-target path；
- 参数化 reduction theorem；
- property-premised hardness theorem；
- 多跳 path + presentation adapter；
- 未注册 theorem 热插拔；
- 新 edge synthesis 后 hardness transport。

CI 动态生成若干此前不存在的 theorem/endpoint，防止 planner 通过固定名称表过拟合。

### 15.4 Boolean CSP regression

重写现有 Boolean CSP 测试，使其检查：

- theorem index 发现 Schaefer theorem；
- planner 产生两个性质子目标；
- reflection 提供 witness；
- 20 题最终 proof 共享通用路径；
- 没有 scaffold 选择；
- 没有模型依赖；
- 无非标准 axiom。

测试不得只检查 20 个 endpoint 可以 import。

### 15.5 跨 family generalization regression

除运行时生成的有限 Gamma 外，至少选择图、集合系统、数值编码等三个非 Boolean CSP family，验证相同 NP-hard rule kernel 与搜索器，无 family-specific Python 分支。

### 15.6 Benchmark 测试降级

以下测试从核心发布门槛移到 benchmark profile：

- oracle isolation；
- exact-edge construction policy；
- model-call ledger；
- hidden route mutation；
- split freeze；
- scorer completion rate；
- publication receipt。

它们可以继续运行，但失败不代表通用 theorem search 核心不可用，除非失败暴露 kernel、类型或工作区安全问题。

## 16. 可观测指标

核心报告应关注能力，而不是审查流程数量：

- NP-hard root closure rate；
- existing resolver fast-path hit rate；
- certified forward path closure rate；
- direct theorem discovery rate；
- schema theorem application rate；
- 平均递归前提深度；
- forward/backward frontier meeting rate；
- deterministic solver closure rate；
- route backtracking 次数；
- model-assisted closure rate；
- synthesis fallback rate；
- 最终 kernel verification rate；
- 新 theorem 热插拔成功率；
- 未见 problem family 的迁移成功率；
- 搜索时间、Lean checks 和模型 token 成本。

对每次成功，报告实际证明树：

```text
root goal
  applied theorem
    premise 1 → solver / theorem
    premise 2 → solver / theorem
      nested premise ...
```

证明树是解释和调试信息，不是新的可信证书；最终 Lean declaration 仍是权威。

## 17. 风险与控制

### 17.1 搜索空间爆炸

控制：

- conclusion-head index；
- NP-hard rule heads 的按需首层检索；
- 先运行现有 resolver fast path；
- theorem role hint；
- 有界 best-first/beam；
- goal memoization；
- cycle detection；
- premise solvability estimate；
- 按成本和目标相关性逐步扩大候选；
- 明确预算。

### 17.2 退化成通用 Lean theorem prover

控制：

- 根目标只接受 `NativeTMNPHard target`；
- 任意 theorem search 只由 NP-hard proof tree 中实际出现的 premise 触发；
- ComplexityReduction 原生 rule kernel 始终优先于无角色 theorem；
- 不把 `NativeTMInNP`、`NativeTMNPComplete` 或任意 `Prop` 提升为并列产品目标；
- 确定性引擎验收和最小新归约验收都围绕 NP-hard artifact，而不是一般 theorem-proving benchmark。

### 17.3 一般 theorem 产生难以解决的前提

控制：

- 保留多条候选路线；
- 对前提运行快速 solvability probe；
- 支持回溯；
- 允许模型提出辅助 lemma；
- 报告最小 unresolved premise。

### 17.4 模型 hallucinate theorem 或错误路线

控制：

- theorem 必须由 environment resolve；
- 参数实例化由 Lean unification；
- proof body 必须 elaboration；
- 最终 kernel check；
- hallucination 仅损失预算，不产生错误证书。

### 17.5 按需索引与 module catalog 性能

控制：

- suite/workspace 级共享 index；
- environment fingerprint cache；
- conclusion-head 倒排；
- 增量更新；
- import closure 分区；
- 避免每个 goal 冷启动 Lake。

### 17.6 公理与不完整理论

控制：

- profile 明确公理策略；
- theorem index 标记 axiom basis；
- forbidden axiom candidate 不进入默认成功；
- 缺失形式化定理报告为 library gap；
- 不用 case-specific scaffold 掩盖一般 theorem 的公理缺口。

### 17.7 自动 tactic 不稳定或耗时

控制：

- 每个 tactic 独立 timeout；
- 固定 tactic 配置；
- tactic 成功后保存完整 proof artifact；
- 不把日志中的“success”当作证明。

### 17.8 benchmark 再次支配核心

控制：

- package 依赖测试禁止 `agent/reduction` import benchmark/scorer；
- 核心 API 不接受 oracle、case ID、split 或 construction policy；
- benchmark 只能调用核心公开 API；
- 活动计划和产品 README 将通用性指标置于 benchmark 分数之前。

## 18. 完成定义

本计划完成时，系统必须满足以下全部条件。

### 18.1 架构

- 存在独立、NP-hard-first 的 `agent/reduction` 通用核心；
- 根任务规范形是精确 `NativeTMNPHard target`；
- ComplexityReduction 原生 NP-hard rule kernel 是证明搜索主干；
- 现有 `NPHardResolver`/closed route search 被复用为 fast path 与 forward frontier；
- 按需 typed theorem index 可发现未注册 theorem；
- Lean MetaM 完成结论统一与前提提取；
- hybrid search 支持 forward/backward 汇合、递归、回溯与循环控制；
- route graph 是一级确定性能力，但不再是唯一 planner；
- 每个成功结果都能重建可独立编译的 Lean proof declaration；
- 模型可以提出并改变数学路线；
- synthesis obligation 由目标类型动态产生；
- benchmark/release audit 不在默认核心路径。

### 18.2 扩展性

- 新增一般 theorem 不需要修改 Python planner；
- 新增 problem family 不需要添加 case ID 或源码字符串分支；
- theorem 热插拔 regression 通过；
- 至少三种非 Boolean CSP theorem schema 自动应用成功；
- 至少三个不同 family 的新 reduction synthesis 成功；
- 新 family 的成功最终复用 `CertifiedReduction`、`CertifiedPath` 和 hardness transport，而不是平行证书体系。

### 18.3 Boolean CSP

- Schaefer hard-side theorem 无领域 axiom；
- 20/20 benchmark 目标通过；
- 额外未见 Gamma 通过；
- 无 NAE3/4/5 planner 特判；
- 无 EXACTLY family Python 路由表；
- 默认零模型调用即可完成有限分类和 theorem reuse。

### 18.4 正确性

- 最终目标类型精确为 `NativeTMNPHard target`；
- Lean kernel 接受；
- 无占位证明；
- 公理策略通过；
- certificate 的程序、复杂度和语义保持同索引；
- 错误候选、hallucinated theorem 和错误 endpoint 均不能产生成功结果。

### 18.5 独立性

- 核心运行不需要 benchmark manifest；
- 核心运行不需要 Evaluation oracle；
- 核心成功不需要 scorer；
- 关闭 model client 后仍可完成可确定性复用的目标；
- 删除 optional audit 组件不影响核心 theorem-search 测试。

### 18.6 可独立交付的能力边界

当 NP-hard rule kernel、按需 theorem discovery、hybrid search、前提求解和 proof reconstruction 全部通过验收时，“通用 NP-hard theorem/path reuse 引擎”即可独立交付。

在此基础上，再完成开放式模型规划以及至少一个“新 `CertifiedReduction` + hardness transport”纵切，才形成“通用 NP-hard 自动归约 Agent MVP”。该 MVP 的定义是：

- 能复用现有 hardness/completeness/path；
- 能自动应用未注册的一般 hardness/reduction theorem；
- 能递归解决定理前提并回溯；
- 能在至少一个新 target 上合成 edge 并 transport hardness；
- 最终输出 kernel 验证的 `NativeTMNPHard target`。

多 family synthesis、Schaefer/Boolean CSP 旗舰能力与旧架构清理是后续扩展任务。Boolean CSP 20/20 是完整计划的重要验收，但不再定义基础引擎是否成立。

## 19. 立即执行顺序

在本计划写入后，按以下顺序开展工作：

1. 冻结 `NativeTMNPHard target` 根目标和 `research` profile，切断 scorer/oracle 默认依赖；
2. 将现有 `NPHardResolver` 接入新 orchestrator 作为 fast path；
3. 实现 ComplexityReduction 原生 NP-hard rule kernel 与根 proof reconstruction；
4. 实现按需 typed theorem index、MetaM conclusion unification 和 premise extraction；
5. 实现 forward certified frontier + backward theorem obligations 的 hybrid search；
6. 完成 synthetic 未注册 theorem、参数化 reduction、property-premised hardness、多跳 adapter 回归；
7. 接入开放式模型 strategy planner、helper lemma generation 和旧 authoring executor adapter；
8. 完成一个不依赖 Schaefer 的“新 edge synthesis + hardness transport”纵切，交付 NP-hard Agent MVP；
9. 将 synthesis 扩展到多个 problem family；
10. 完成至少三个非 Boolean CSP family 的 synthesis/generalization 验收；
11. 闭合 Schaefer theorem、PP interpretation polynomial compiler 和有限反射；
12. 让 Boolean CSP 20 题通过同一一般 theorem 路线；
13. 清理固定 family planner、固定 DAG 和核心中的 benchmark 审查依赖；
14. 最后重新运行 benchmark，作为能力测量而不是架构驱动力。

在 NP-hard Agent MVP 交付前，不再增加新的 Boolean CSP case-specific scaffold。在 Schaefer/Boolean CSP 旗舰纵切完成前，不再以 exact-edge 分数、模型调用次数或审查 receipt 数量作为项目主进度指标。
