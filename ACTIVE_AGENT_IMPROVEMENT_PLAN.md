# 通用自动归约 Agent：结构化证明生成与 Strategy 控制实施计划

> 状态：Active
>
> 更新日期：2026-08-15
>
> 当前唯一实施主线：在已经接通的全局递归搜索、dependent binder、ApplicationFrame、失败回队、整树重建和最终 Lean 审计基础上，补齐“结构化构造、环境 grounding、可持续 repair、proof-producing finite synthesis”能力，并让 strategy 模型的返回值真正控制下一步 action 或 synthesis design。

## 0. 文档范围

此前计划聚焦于把一次性根目标求解改造成统一的 AND/OR 递归搜索。该部分已经在生产路径中接通，并通过 Boolean CSP 20 题测试验证了以下能力：

- theorem premise 可以递归进入同一个 GlobalProofFrontier；
- data binder 可以绑定并重新实例化 dependent sibling premises；
- theorem、reuse、synthesis action 失败后可以携带 failure memory 回队；
- source witness 可以回溯并切换；
- ApplicationFrame 可以表达多层 theorem application；
- 最终 artifact 继续经过独立 Lean elaboration、kernel、axiom 和 forbidden dependency 审计。

因此，本文件删除旧计划中已经完成或已经不再构成主要瓶颈的递归接线任务，不再把“接入 SearchCoordinator”“新增 ApplicationFrame”“迁移子目标 synthesis”等内容列为待办。

本文件只描述下一阶段尚未完成的能力建设。

## 1. 当前证据与问题定位

### 1.1 压力测试设置

权威压力测试报告：

    Reports/GENERAL_AGENT_BOOLEAN_CSP_NO_CANONICAL_INTERPRETATION_REAL_API_STRESS_REPORT.json

测试同时禁止：

- `ComplexityReduction.Domain.BooleanCSP.Hardness.NativeTMNPHard_of_notSchaeferTractable`；
- `ComplexityReduction.Domain.BooleanCSP.Hardness.NativeTMNPHard_of_notSchaeferTractable_with_oneInThree`；
- `ComplexityReduction.Domain.BooleanCSP.schaefer_dichotomy`；
- `ComplexityReduction.Domain.BooleanCSP.Hardness.CanonicalHardCores.oneInThreeInterpretation`；
- `ComplexityReduction.Domain.BooleanCSP.Hardness.CanonicalHardCores.naeInterpretation`。

结果：

- 20/20 case 完成；
- 4 个 VERIFIED；
- 16 个 BUDGET_EXHAUSTED；
- 272 次真实 DeepSeek API 调用；
- 272 次 HTTP 200；
- 236 次响应通过模型协议解析；
- 192 次 lean-authoring；
- 80 次 strategy-proposal；
- 1,574,554 total tokens；
- 132 个生成候选进入 Lean；
- 0 个生成 capability 通过 Lean；
- 0 个 forbidden declaration 直接或传递依赖。

### 1.2 已经工作的部分

16 个失败 case 均能走到正确的数学瓶颈：

    NativeTMNPHard target
      <- nPHard_of_interpretation_auto
         AND source : Gamma
         AND LanguageInterpretation source target
         AND NativeTMNPHard (cspOf source)

每个失败 case 都完成了：

1. 绑定 `oneInThreeCore`；
2. 闭合对应 source hardness；
3. 尝试构造 `LanguageInterpretation oneInThreeCore target`；
4. 失败后触发 `DATA_BINDING_REOPENED`；
5. 改为绑定 `nae3Core`；
6. 闭合对应 source hardness；
7. 尝试构造 `LanguageInterpretation nae3Core target`；
8. 最终耗尽 authoring budget。

这说明当前主要问题已经不是：

- 根目标不会递归分解；
- dependent binder 不会共享；
- theorem action 失败后不能回退；
- source hardness 找不到；
- dichotomy 路径没有被正确禁止。

### 1.3 当前主要瓶颈

当前主要瓶颈是：

> Agent 能找到应当构造的局部对象，但缺少把复杂 data-valued Lean goal 分解、ground、搜索、修复并最终变成 kernel-verified capability 的通用机制。

代表性目标包括：

    LanguageInterpretation source target

以及继续分解后的：

    (symbol : source.Symbol) →
      Gadget target (source.relationOf symbol)

`Gadget` 并不是一个可以靠名称猜出的简单对象。它包含：

- 一个目标语言公式；
- distinguished output variables；
- output injectivity；
- 对所有 Boolean tuple 的双向语义正确性证明。

模型当前常见失败：

- 35 次 typeclass/instance 相关错误；
- 27 次 unknown identifier；
- 26 次 unsolved goals；
- 14 次 type mismatch；
- 16 次响应达到 max tokens 后为空；
- 9 次 authoring JSON 缺少 implementation 或 reason；
- 6 次 strategy 响应违反 opaque action protocol；
- 3 次 authoring 响应无法提取单一 JSON object；
- 2 次 finish_reason=stop 但 assistant content 为空。

### 1.4 Strategy 当前没有真正参与决策

当前 recursive runtime 调用：

    _, record = propose_strategy(...)

strategy proposal 被解析和计费，但其 action、action_id 和 reason 没有用于选择下一步 action，也没有改变 synthesis design。

因此目前的 80 次 strategy 调用只产生：

- API 成本；
- token 成本；
- latency；
- report receipt；

但不产生任何 proof-search state transition。

这是本计划必须首先修复的明确缺陷。

### 1.5 Authoring repair 当前不是修复

同一 synthesis action 的后续尝试目前只收到：

- exact expected type；
- construction mode 标签；
- declaration 名称列表；
- 最近 4000 字符 Lean diagnostics。

它没有收到：

- 上一次实际 implementation；
- 上一次源码 hash；
- 错误位置对应的源码片段；
- 目标 head declaration 的结构定义；
- constructor 的完整类型；
- 候选 theorem 的完整类型；
- 相关 local definitions；
- 已经验证过的相邻示例。

因此每一次所谓 repair 实际上都是无状态重新生成。

### 1.6 Construction mode 当前只是标签

`intermediate-first`、`typed-witness`、`direct-authoring` 等 mode 当前主要用于：

- 生成不同 action_id；
- 写入 prompt；
- 改变 estimated_cost。

它们没有稳定对应不同的：

- 子目标分解；
- helper DAG；
- materialization schema；
- repair policy；
- proof-producing solver；
- budget allocation。

下一阶段必须把 mode 从提示词标签改成可执行的 SynthesisDesign。

## 2. 本轮目标

本轮目标是建立以下闭环：

1. 对当前 OpenGoal 先运行 deterministic exact closure；
2. 根据 Lean goal shape 产生结构化 introduction/constructor actions；
3. 召回 theorem、reuse、plugin 和 synthesis candidates；
4. 对真正存在多个可行选择的状态调用 strategy；
5. 将 strategy proposal 解析成一个可执行的 StrategyDecision；
6. StrategyDecision 必须实际选择 action、选择 design 或请求局部 backtrack；
7. 被选中的 action 必须出现在随后的 `ACTION_EXPANDED` 事件中；
8. data-valued 目标优先被结构化分解，而不是整体交给模型；
9. authoring 获得经过 Lean 提取的 environment context capsule；
10. 第一次 materialization 失败后，repair 必须基于上一版源码进行；
11. 对有限且可判定的 witness 目标，优先使用 proof-producing finite synthesis；
12. 生成 capability 通过局部 Lean 后立即回注当前 ProofState；
13. 最终 proof tree 继续经过独立重建和完整审计。

## 3. 非目标

本轮不做以下事情：

- 不把 Boolean CSP case ID 写入 generic core；
- 不按 `NAE4`、`exactly-k`、`OR3XOR2` 等 benchmark 名称分支；
- 不在 prompt 中硬编码 20 道题的答案；
- 不为被禁止 theorem 建 alias 或 wrapper；
- 不降低 forbidden declaration 审计；
- 不允许 Python 伪造 Lean proof receipt；
- 不把 LLM 判断作为 proof authority；
- 不通过增加 authoring 次数掩盖重复失败；
- 不重建一套与 GlobalProofFrontier 平行的独立 synthesis 搜索器；
- 不删除已经工作的 recursive theorem/binder/backtracking 机制；
- 不以“20/20 必须一次实现完成”为理由引入 benchmark 特判。

## 4. 通用性边界

### 4.1 Generic core 可以知道什么

Generic core 只允许依据以下信息做决策：

- Lean exact goal type；
- local context；
- goal head constant；
- theorem/constructor telescope；
- inductive/structure metadata；
- candidate exact types；
- residual obligations；
- failure fingerprints；
- generated capability receipts；
- provider capability metadata；
- budget 和历史成本；
- plugin 的 typed support score。

### 4.2 Domain plugin 可以知道什么

Domain plugin 可以理解一个领域中稳定、公开的形式化接口，例如：

- Boolean CSP 的 `Gamma`；
- `BooleanRelation`；
- `CSP.Formula`；
- `Gadget`；
- finite relation table reflection。

但 domain plugin 不得知道：

- benchmark case ID；
- train/dev/heldout split；
- 某个 case 的预制答案；
- 为通过测试而写死的 constraint 列表；
- oracle 文件内容。

### 4.3 最终可信边界

无论 capability 来自：

- theorem reuse；
- structural decomposition；
- deterministic solver；
- domain plugin；
- enumerative search；
- CEGIS；
- LLM authoring；

都必须满足：

1. 精确声明 expected Lean type；
2. 独立运行 Lean；
3. 通过标准公理检查；
4. 通过 placeholder/source fence；
5. 通过 forbidden direct/transitive dependency audit；
6. 只有成功后才能进入 ProofState。

## 5. 目标架构

目标求解顺序：

    OpenGoal
      -> ExactClosureProbe
      -> StructuralActionProvider
      -> ReuseActionProvider
      -> TheoremActionProvider
      -> Registered Solver/Plugin Providers
      -> SynthesisDesignProvider
      -> StrategyController
      -> Action Executor
      -> Lean verification
      -> close/decompose/repair/backtrack
      -> GlobalProofFrontier

模型调用原则：

    模型只在其输出能够改变下一步状态时调用。

具体含义：

- 唯一 exact-closed action 不调用 strategy；
- 只有一个可执行 action 时不调用 strategy；
- 所有 action 都已被 failure memory 排除时不调用 strategy；
- strategy proposal 必须映射到具体 action_id 或 design_id；
- 无法映射的 proposal 记录为 rejected，并走 deterministic fallback；
- 不允许出现“strategy 调用了，但 executor 完全忽略其结果”。

## 6. Strategy 控制面

### 6.1 新增内部数据结构

在 `agent/generative_reduction/models.py` 中增加：

    StrategyDecision
      decision_id
      goal_id
      state_fingerprint
      decision_kind
      selected_action_id
      selected_design_id
      requested_backtrack
      rationale
      confidence
      proposal_hash
      applicable

    StrategyEffectReceipt
      decision_id
      proposal_status
      proposed_action_id
      applied_action_id
      applied_design_id
      effect
      override_reason
      next_state_fingerprint

`effect` 至少包含：

- `selected-action`；
- `selected-design`；
- `backtracked-current-branch`；
- `deterministic-fallback-invalid-proposal`；
- `deterministic-fallback-stale-proposal`；
- `not-called-single-action`；
- `not-called-deterministic-closure`。

### 6.2 Strategy 何时调用

满足以下条件之一才调用 strategy：

1. 同一 goal 有至少两个仍可执行、未尝试且非 exact-closed 的 action；
2. 同一 synthesis contract 有至少两个语义不同、可执行的 SynthesisDesign；
3. 当前 action 已失败，且需要在“repair 当前 design”和“切换 design/action”之间选择；
4. 当前 branch 存在多个 data witness，deterministic constructibility score 无法明显区分；
5. 当前 state 的剩余预算不足以扩张所有高成本分支，需要做成本感知选择。

以下情况禁止调用：

- exact closure 已经通过 Lean；
- 只有一个可执行 action；
- strategy cache 中已有仍然适用的 decision；
- 当前 action set 与上次完全相同且没有新增 diagnostic/capability/budget 变化；
- model policy disabled；
- strategy budget 已耗尽。

### 6.3 Strategy 输入

strategy prompt 必须包含经过裁剪的可决策信息：

- exact goal；
- goal kind；
- local context 摘要；
- 每个 action 的：
  - action_id；
  - provider；
  - disposition；
  - declaration 或 design_id；
  - exact result type；
  - residual obligation exact types；
  - constructibility score；
  - estimated Lean/model cost；
  - cycle/progress risk；
  - prior failure code；
  - prior diagnostic fingerprint；
- 当前 branch 已验证 capabilities；
- 当前 data bindings；
- remaining budget；
- strategy 可执行的 decision schema。

不能只给 opaque action_id 和 residual count。模型至少需要知道不同 action 在数学上会产生什么 typed obligations。

### 6.4 Strategy 输出协议

新的输出协议只允许：

    {
      "decision": "select_action" | "select_design" | "backtrack",
      "action_id": "<supplied id or null>",
      "design_id": "<supplied id or null>",
      "confidence": 0.0,
      "reason": "..."
    }

约束：

- `select_action` 必须提供仍可执行的 action_id；
- `select_design` 必须提供属于当前 contract 的 design_id，并同时确定承载该 design 的 synthesis action；
- `backtrack` 只表示放弃当前 branch/state，不得直接产生顶层 BLOCKED；
- strategy 不再允许 `stop_with_blocker` 直接终止 job；
- strategy 不得发明 theorem、declaration、action 或 design。

### 6.5 Strategy 如何真正影响执行

`SearchCoordinator` 的选择顺序改为：

1. 收集全部 executable actions；
2. 执行 exact deterministic priority；
3. 如果需要 strategy，调用 `StrategyController.decide`；
4. 验证 decision 仍适用于当前 state；
5. 若 valid：
   - `select_action`：下一次 executor 必须扩张该 action_id；
   - `select_design`：将对应 design 注入 action metadata，并扩张承载该 design 的 action；
   - `backtrack`：淘汰当前 state，但保留其他 frontier states；
6. 若 invalid/stale：
   - 记录 rejected receipt；
   - 使用 deterministic ranking；
7. 写入 `STRATEGY_DECISION_APPLIED`；
8. 随后的 `ACTION_EXPANDED` 必须引用 receipt 中的 applied_action_id。

禁止继续出现：

    _, record = propose_strategy(...)

至少必须变成：

    proposal, record = propose_strategy(...)
    decision = validate_strategy_proposal(proposal, state, goal, actions, designs)
    selected = apply_strategy_decision(decision, deterministic_fallback)

### 6.6 Strategy cache

cache key 必须包含：

- state fingerprint；
- goal key；
- executable action IDs；
- design IDs；
- action failure fingerprints；
- generated capability fingerprint；
- binding fingerprint；
- remaining budget bucket；
- environment/context capsule hash。

以下变化必须使旧 decision 失效：

- action 已被尝试；
- 新 capability 注入；
- Lean diagnostic 更新；
- data binding 改变；
- design 状态改变；
- action set 改变；
- budget 跨过配置阈值。

### 6.7 Strategy 验收

- [ ] 两个 theorem action 中，mock strategy 选择第二个，随后第二个真实扩张；
- [ ] 两个 synthesis design 中，strategy 选择的 design 被 materialize；
- [ ] strategy 请求 backtrack 时只淘汰当前 state；
- [ ] invalid action_id 触发 deterministic fallback；
- [ ] stale decision 不会执行；
- [ ] 单一 action 不产生 strategy call；
- [ ] exact closure 不产生 strategy call；
- [ ] 每个真实 strategy call 都有 StrategyEffectReceipt；
- [ ] `unused_strategy_call_count = 0`；
- [ ] report 可以证明 proposed action 与 expanded action 的对应关系。

## 7. 通用 Lean 结构化分解

### 7.1 新增 StructuralActionProvider

新增：

    agent/generative_reduction/providers/structural.py

该 provider 不依赖 theorem index 中已经人工注册的 theorem，而是由 Lean environment 直接读取目标形状。

至少支持：

- dependent function / `∀` introduction；
- ordinary function introduction；
- `let` 展开；
- structure constructor；
- inductive constructor；
- `Exists`；
- `Nonempty`；
- `And`；
- `Or` 的分支候选；
- `Subtype`；
- `Sigma`；
- equality reflexivity；
- typeclass synthesis 作为独立 typed action。

### 7.2 Lean Structural Probe

新增 Lean probe，输出：

- goal head kind；
- target universe/sort；
- Pi binder 列表；
- constructor declarations；
- constructor telescope；
- constructor result与目标统一后的 binder assignments；
- 每个 constructor field 的 premise kind；
- field dependency slot IDs；
- application skeleton；
- progress receipt；
- import/module receipt。

不得由 Python 字符串解析 `#print` 猜 constructor telescope。

### 7.3 Function goal

对于：

    (symbol : source.Symbol) → Gadget target (source.relationOf symbol)

必须先产生结构 action：

    intro symbol

并创建带显式 local context 的 child goal：

    Gadget target (source.relationOf symbol)

`symbol` 作为稳定 binder slot 保存，resume 后必须能重新 elaboration。

### 7.4 Structure goal

对于：

    Gadget target relation

必须召回 `Gadget.mk`，并分解为：

- formula witness；
- outputs witness；
- outputs_injective proof；
- correct semantic proof。

这些字段通过 ApplicationFrame 共享同一个 formula 和 outputs binding。

### 7.5 Constructor ranking

默认排序：

1. exact constructor with zero residual；
2. field 数量少且 deterministic solver coverage 高；
3. 有现成 witness candidate；
4. finite/decidable fields；
5. 需要 synthesis 的 fields；
6. 可能重新产生 parent goal 的 projection/self-loop action。

projection 不能因为名称匹配而排在能够实际构造目标的 constructor 前面。

### 7.6 Progress 与循环

结构 action 的 progress fingerprint 包含：

- parent goal key；
- introduced binders；
- constructor declaration；
- instantiated field goal multiset；
- local context delta。

以下 action 必须被判定为 non-progress：

- projection 的 premise等价于 parent goal；
- constructor 分解后只产生同一个 parent goal；
- 没有新增 binder、field、binding 或 capability；
- 同一 structural frame 已在祖先路径出现。

### 7.7 Structural provider 验收

- [ ] 通用 `∀ x, T x` 目标被 intro；
- [ ] 通用二字段 structure 被分解；
- [ ] dependent structure fields 共享 witness；
- [ ] `Exists` witness 和 proof 形成两个 dependent slots；
- [ ] `Subtype` witness 和 property 正确重建；
- [ ] `Gadget` 通过 constructor 分解，不再只召回 `LanguageInterpretation.gadgetOf`；
- [ ] constructor action 不包含 Boolean CSP 名称判断；
- [ ] wrong constructor field 顺序被 Lean 拒绝；
- [ ] resume 后 local binder 和 field slots 保持稳定。

## 8. Environment Context Capsule

### 8.1 目标

authoring 模型不能只看到 declaration 名称。每次生成前必须由 Lean 产生一个可审计、可缓存、受 token budget 限制的上下文胶囊。

新增：

    ContextCapsule
      capsule_id
      exact_goal
      local_context
      goal_head
      goal_head_type
      goal_head_definition
      constructors
      candidate_signatures
      relevant_definitions
      relevant_lemmas
      verified_examples
      imports
      omitted_item_receipts
      token_estimate
      environment_fingerprint

### 8.2 必须包含

- exact goal；
- 完整 local context；
- goal head declaration 的完整类型；
- structure/inductive fields 与 constructor 类型；
- planner 推荐 declaration 的完整类型；
- reusable declaration 的完整类型；
- application skeleton；
- residual obligation exact types；
- diagnostics 中出现的 constant 的类型；
- 当前 generated capability 的签名；
- 最多若干个按 exact-type 相似度召回的已验证例子。

### 8.3 定义展开策略

按需展开，不全量发送源码：

1. 目标 head；
2. constructor/field 类型中直接出现的定义；
3. Lean diagnostic 中的 unknown/mismatch constant；
4. candidate theorem premise 中的关键 definition；
5. 经过 dependency distance 和 token budget 排序的 definitions。

每个展开项记录：

- declaration；
- module；
- type；
- value/body 是否包含；
- omission reason；
- source hash。

### 8.4 Token 预算

context capsule 使用独立预算：

- exact signatures 不得省略；
- definition body 可以裁剪；
- verified example 可以按相似度裁剪；
- diagnostics 只保留当前 declaration 相关窗口；
- 不把完整 theorem index 或完整模块源码塞进 prompt。

### 8.5 Capsule 缓存

cache key：

- goal key；
- local context fingerprint；
- candidate/action set；
- environment fingerprint；
- generated import fingerprint；
- diagnostic fingerprint；
- expansion policy version。

### 8.6 Capsule 验收

- [ ] 模型能看到 `Gadget.mk` 的完整字段类型；
- [ ] 模型能看到 `LanguageInterpretation.mk` 的完整类型；
- [ ] unknown identifier 后下一次 capsule 包含相关替代 declaration；
- [ ] capsule hash 写入每次 authoring receipt；
- [ ] prompt 不再只包含 reusable declaration 名称；
- [ ] capsule 不包含 API key、authorization header 或 oracle 内容；
- [ ] capsule 构造完全由类型和 dependency distance 驱动。

## 9. 可执行 SynthesisDesign

### 9.1 扩展 SynthesisDesign

`SynthesisDesign` 至少增加：

- parent_goal_id；
- design_kind；
- stage；
- staged_goal_ids；
- helper_declarations；
- constructor_skeleton；
- previous_implementation；
- previous_source_hash；
- diagnostic_history；
- diagnostic_fingerprints；
- candidate_source_hashes；
- counterexamples；
- context_capsule_id；
- strategy_decision_id；
- materialization_attempts；
- repair_attempts；
- status；
- terminal_reason。

### 9.2 Design kind

第一版支持：

- `constructor-first`；
- `helper-first`；
- `direct-authoring`；
- `finite-enumeration`；
- `cegis-witness`；
- `theorem-composition`。

旧 mode 映射：

- `typed-witness` → `constructor-first`；
- `intermediate-first` → `helper-first`；
- `direct-authoring` → `direct-authoring`。

映射后必须产生不同执行行为，不能只改变 prompt 字符串。

### 9.3 Constructor-first

- 先运行 StructuralActionProvider；
- 生成 constructor skeleton；
- 每个 field 进入普通 recursive search；
- 只对无法 deterministic close 的最小 field 调用模型或 plugin；
- parent object 由 Lean frame 重建。

### 9.4 Helper-first

- strategy 必须选择一个具体 helper design；
- helper 有精确 declaration name 和 exact type；
- helper 作为 child goal 进入同一 frontier；
- helper 通过 Lean 后回注 parent；
- 不允许模型返回没有 exact type 的自由文本“中间引理”。

### 9.5 Direct-authoring

只在以下条件下使用：

- structural decomposition 不可用；
- plugin 不支持；
- theorem/reuse alternatives 已尝试；
- strategy 明确选择或 deterministic ranking 认为成本最低；
- goal size 未超过配置阈值。

### 9.6 Design 状态转换

允许：

    planned
      -> context-ready
      -> materializing
      -> lean-failed
      -> repairing
      -> verified

以及：

    lean-failed
      -> abandoned
      -> switch-design

每次状态转换写入事件，不允许把多次无状态调用都记成同一个“synthesis action failed”。

## 10. 真正的 Authoring Repair

### 10.1 Initial authoring 与 repair 分离

新增两个协议：

    propose_initial_implementation(...)
    propose_repair(...)

初次生成输入：

- exact declaration；
- exact type；
- executable design；
- context capsule；
- forbidden declarations；
- source fence；
- required output schema。

repair 输入必须额外包含：

- 上一次 implementation 原文；
- base implementation/source hash；
- Lean error classification；
- 错误行和附近源码；
- normalized diagnostics；
- 本轮新增 context capsule items；
- 已失败 source hashes；
- 要求保留不相关正确部分。

### 10.2 Repair 输出

使用：

    {
      "base_sha256": "...",
      "implementation": "...",
      "changed_reason": "...",
      "addressed_diagnostic_codes": ["..."]
    }

要求：

- base_sha256 必须匹配当前 design 的上一版；
- implementation 必须是完整替换内容；
- 不接受无法安全定位的自由格式 patch；
- 不允许 imports、namespace、axiom、sorry/admit；
- 不允许 forbidden declaration。

### 10.3 Lean diagnostic 分类

新增稳定分类：

- `unknown_identifier`；
- `invalid_field_or_constructor`；
- `typeclass_synthesis_failed`；
- `type_mismatch`；
- `unsolved_goals`；
- `termination_or_recursion`；
- `forbidden_source`；
- `placeholder_or_axiom`；
- `timeout`；
- `parser_error`；
- `other_elaboration_error`。

分类影响下一步：

- unknown identifier → 扩充 declaration capsule；
- invalid constructor → 重新运行 structural probe；
- typeclass failure → 列出真实 instances 或禁止继续猜 instance；
- type mismatch → 提供 expected/actual type；
- unsolved goals → 将 residual goals 显式加入 repair；
- repeated same fingerprint → 切换 design，不再重复 authoring。

### 10.4 去重与停止

以下任一条件触发 design abandon：

- implementation hash 重复；
- source hash 重复；
- 同一 diagnostic fingerprint 连续出现达到阈值；
- 模型再次使用已明确不存在的 identifier；
- repair 没有修改错误区域；
- authoring fence 连续拒绝；
- 预计剩余 budget 不足以完成 Lean check 和 final audit。

### 10.5 模型协议可靠性

模型 client 优先使用 provider 支持的 structured schema；否则：

- 只提取一个顶层 JSON object；
- code 只放在 implementation 字段；
- 协议修复与数学 authoring 分离；
- schema repair 使用小 token budget；
- schema repair 不计为新的数学 design；
- finish_reason=length 时不得直接重试同样 prompt 和 max tokens。

### 10.6 文件命名与证据

generated attempt 文件名必须包含：

- design ID；
- attempt ordinal；
- implementation/source hash 前缀。

不得使用会在回队或 resume 后覆盖旧内容的固定路径。

每次尝试必须保留：

- prompt capsule hash；
- response hash；
- implementation hash；
- source hash；
- Lean command receipt；
- diagnostic classification；
- repair parent hash。

### 10.7 Repair 验收

- [ ] 第二次 authoring prompt 包含第一次 implementation；
- [ ] repair base hash 不匹配时拒绝；
- [ ] unknown identifier 触发 capsule expansion；
- [ ] 相同 implementation 不重复运行 Lean；
- [ ] 相同 diagnostic 超阈值后切换 design；
- [ ] attempt 文件不被后续回队覆盖；
- [ ] report 能重建完整 repair lineage；
- [ ] mock 模型修正单行类型错误后 capability 被注册。

## 11. Proof-producing Finite Synthesis

### 11.1 通用插件协议

新增通用接口：

    FiniteSynthesisPlugin
      supports(goal, context_capsule) -> SupportReceipt
      reify(goal, environment) -> ReifiedProblem
      propose_bounds(problem, budget) -> SearchBounds
      enumerate(problem, bounds) -> CandidateWitness stream
      check(problem, witness) -> CheckResult
      counterexample(problem, witness) -> Counterexample | None
      materialize(problem, witness, check_receipt) -> LeanCapabilitySource

`CheckResult` 必须区分：

- rejected by executable semantics；
- accepted by executable semantics but not yet certified；
- proof source materialized；
- Lean verified。

### 11.2 Generic core 与 plugin 的关系

Generic core 只负责：

- 根据 typed support receipt 注册 plugin action；
- 把 plugin action放入同一个 action bucket；
- 允许 strategy 在 plugin 与 model/theorem action之间选择；
- 管理 budget；
- 运行 Lean；
- 注册 capability；
- 记录 proof receipt。

Generic core 不理解具体 witness 编码。

### 11.3 Boolean CSP finite gadget adapter

在 Boolean CSP plugin 内实现：

- reify `Gamma` 的 finite relation table；
- reify目标 `BooleanRelation`；
- 生成 bounded `CSP.Formula Gamma`；
- 生成 output variable map；
- 检查 output injectivity；
- 枚举 output tuple 和 auxiliary assignments；
- 验证：

      relation.Holds tuple
        ↔ ∃ assignment,
            formula.Satisfies assignment ∧
            assignment(outputs) = tuple

- 生成对应 Lean `Gadget` declaration；
- 使用 reflection theorem 或可计算 certificate 证明 correct。

禁止：

- 按 Case02/Case05 等 ID 返回预制 formula；
- 读取 benchmark oracle；
- 调用两个被禁止的 canonical interpretation；
- 把 Python 枚举结果直接当 proof。

### 11.4 搜索方式

按成本递增枚举：

- constraint 数；
- auxiliary variable 数；
- variable repetition；
- relation symbol；
- argument projection/permutation；
- formula composition size。

先做 executable semantic filtering，再生成 Lean，避免每个明显错误候选都调用 Lean。

### 11.5 CEGIS

当完整枚举过大时：

1. strategy 或 model 提议 witness shape；
2. executable checker 返回反例 tuple/assignment；
3. counterexample 进入 design state；
4. 下一次 proposal 必须满足累计反例；
5. executable checker 全通过后 materialize Lean certificate；
6. Lean 最终验证。

模型只能提议 witness，不得声明 witness 正确。

### 11.6 从 Boolean CSP 推广

Boolean CSP adapter 是第一项验收实现，但接口应能进一步支持：

- 有限图 gadget；
- 有限自动机/转换表 witness；
- 小型 finite algebra operation；
- 有限 relation interpretation；
- bounded mapping/permutation witness。

因此插件入口应按：

- finite carrier receipt；
- decidable semantics receipt；
- witness grammar；
- certificate materializer；

建模，而不是按 benchmark 名称建模。

### 11.7 Finite synthesis 验收

- [ ] plugin supports 判断基于 exact type 和 environment；
- [ ] Case02 名称不出现在 generic core 或搜索器；
- [ ] 错误 gadget 被 executable checker 拒绝；
- [ ] executable accepted 但伪造 proof 被 Lean 拒绝；
- [ ] 正确小型 synthetic gadget 生成并注册 capability；
- [ ] counterexample 可以反馈给下一次 design；
- [ ] generated capability 不依赖五个 forbidden declarations；
- [ ] plugin action 可以被 strategy 真正选择；
- [ ] plugin 失败后 theorem/model alternatives 仍然存在。

## 12. Candidate Ranking 与搜索成本

### 12.1 Constructibility score

每个 action 增加通用 constructibility score，考虑：

- exact closed premise 数；
- structural decomposition 后 field 数；
- deterministic solver coverage；
- finite plugin support；
- unresolved data witness 数；
- semantic proof 数；
- prior diagnostic severity；
- cycle risk；
- historical success rate；
- estimated Lean checks；
- estimated model calls；
- expected context size。

### 12.2 Projection/self-loop 惩罚

如果 candidate：

- 由目标对象的 projection 得到；
- premise 与 parent goal 等价；
- 会重新要求同一 capability；
- 已在祖先 frame 中出现；

则必须降低优先级或直接标记 non-progress。

本规则是通用 goal-graph 规则，不写 `LanguageInterpretation.gadgetOf` 特判。

### 12.3 Provider 顺序

顺序不是硬门禁，但默认成本应体现：

1. exact Lean closure；
2. deterministic structural action；
3. verified reuse；
4. theorem with high closed-premise coverage；
5. proof-producing plugin；
6. bounded finite enumeration；
7. model-assisted CEGIS；
8. direct authoring。

strategy 可以在多个可行 action 中调整顺序，但不能选择已被 proof policy 禁止的 action。

### 12.4 Adaptive budget

新增或明确：

- max_strategy_calls_per_goal；
- max_context_expansions_per_design；
- max_repairs_per_design；
- max_duplicate_candidate_rejections；
- max_same_diagnostic_repetitions；
- max_finite_candidates；
- max_cegis_rounds；
- max_structural_depth；
- final_verification_reserved_lean_checks。

预算规则：

- strategy 调用必须对应一个可应用 decision；
- invalid protocol 不消耗数学 action attempt，但消耗模型预算；
- duplicate source 不消耗 Lean check；
- executable semantic reject 不消耗 Lean check；
- final artifact verification 始终保留预算；
- repeated finish_reason=length 必须缩小任务或切换 design；
- budget exhausted 必须报告正在阻塞的最小 capability。

## 13. 报告与可观测性

### 13.1 新增事件

- `STRUCTURAL_ACTION_DISCOVERED`；
- `STRUCTURAL_GOAL_DECOMPOSED`；
- `CONTEXT_CAPSULE_BUILT`；
- `CONTEXT_CAPSULE_EXPANDED`；
- `STRATEGY_DECISION_PROPOSED`；
- `STRATEGY_DECISION_APPLIED`；
- `STRATEGY_DECISION_REJECTED`；
- `SYNTHESIS_DESIGN_CREATED`；
- `SYNTHESIS_DESIGN_SELECTED`；
- `SYNTHESIS_DESIGN_SWITCHED`；
- `AUTHORING_INITIAL_PROPOSED`；
- `AUTHORING_REPAIR_PROPOSED`；
- `CANDIDATE_DEDUPLICATED`；
- `LEAN_DIAGNOSTIC_CLASSIFIED`；
- `FINITE_CANDIDATE_CHECKED`；
- `FINITE_COUNTEREXAMPLE_FOUND`；
- `FINITE_CERTIFICATE_MATERIALIZED`；
- `GENERATED_CAPABILITY_REGISTERED`。

### 13.2 新增报告字段

- strategy_call_count；
- strategy_valid_proposal_count；
- strategy_applied_decision_count；
- strategy_fallback_count；
- unused_strategy_call_count；
- strategy_effect_receipts；
- context_capsule_count；
- context_capsule_expansion_count；
- structural_action_count；
- constructor_decomposition_count；
- synthesis_design_count；
- design_switch_count；
- initial_authoring_count；
- repair_authoring_count；
- duplicate_candidate_count；
- repeated_diagnostic_count；
- generated_lean_check_count；
- generated_lean_success_count；
- finite_candidate_count；
- finite_counterexample_count；
- finite_certificate_count；
- capability_registration_count；
- capability_used_by_final_artifact_count。

### 13.3 强制一致性

报告必须验证：

    strategy_call_count
      = strategy_applied_decision_count
      + strategy_fallback_count
      + strategy_rejected_count

并要求：

    unused_strategy_call_count = 0

每个 applied strategy decision 必须能关联：

- 一个后续 expanded action；
- 一个 design selection；
- 或一个明确的 current-state backtrack。

## 14. 实施阶段

### 14.1 Phase 1：Strategy 真正接管 action/design 选择

修改：

- `agent/generative_reduction/model/strategy.py`；
- `agent/generative_reduction/model/protocol.py`；
- `agent/generative_reduction/models.py`；
- `agent/generative_reduction/search.py`；
- `agent/generative_reduction/recursive_runtime.py`；
- `agent/generative_reduction/reporting.py`；
- `tests/test_generative_reduction.py`。

任务：

- [ ] 定义 StrategyDecision 和 StrategyEffectReceipt；
- [ ] 收紧 strategy 输出 schema；
- [ ] strategy 输入加入 typed action consequences；
- [ ] SearchCoordinator 使用 proposal 选择 action；
- [ ] synthesis proposal 映射到具体 design；
- [ ] backtrack 只淘汰当前 branch；
- [ ] invalid/stale proposal deterministic fallback；
- [ ] 单 action与 exact closure 跳过 strategy；
- [ ] 增加 decision cache；
- [ ] 记录完整 effect receipt；
- [ ] 删除忽略 proposal 的调用方式。

阶段验收：

- `unused_strategy_call_count = 0`；
- mock strategy 选择的 action 与 `ACTION_EXPANDED` 一致；
- 真实 API 单例 report 可以证明 strategy 决策生效。

### 14.2 Phase 2：StructuralActionProvider

修改/新增：

- 新增 `agent/generative_reduction/providers/structural.py`；
- `agent/generative_reduction/capability_planner.py`；
- `agent/generative_reduction/proof_state.py`；
- `agent/generative_reduction/recursive_runtime.py`；
- `agent/generative_reduction/lean_bridge.py`；
- 新增或扩展 Lean structural probe；
- `tests/test_generative_reduction.py`。

任务：

- [ ] Pi/function intro；
- [ ] structure/inductive constructor discovery；
- [ ] dependent field frame；
- [ ] Exists/Nonempty/And/Or/Subtype/Sigma；
- [ ] structural progress fingerprint；
- [ ] projection/self-loop guard；
- [ ] constructor constructibility ranking；
- [ ] serialization/resume。

阶段验收：

- synthetic dependent structure 完整闭合；
- `Gadget` 被分解为字段目标；
- generic core 无 Boolean CSP 名称判断。

### 14.3 Phase 3：Context Capsule 与真 Repair

修改/新增：

- 新增 `agent/generative_reduction/context_capsule.py`；
- `agent/generative_reduction/model/authoring.py`；
- `agent/generative_reduction/model/protocol.py`；
- `agent/generative_reduction/synthesis/designs.py`；
- `agent/generative_reduction/synthesis/materialize.py`；
- `agent/generative_reduction/synthesis/repair.py`；
- `agent/generative_reduction/recursive_runtime.py`；
- Lean declaration/context probe；
- tests。

任务：

- [ ] 从 Lean 提取 exact signatures；
- [ ] constructor/field 定义进入 capsule；
- [ ] diagnostic-driven capsule expansion；
- [ ] previous implementation 进入 repair；
- [ ] base hash 校验；
- [ ] diagnostic 分类；
- [ ] candidate/source 去重；
- [ ] repair lineage；
- [ ] hash-based attempt filenames；
- [ ] schema repair 与数学 repair 分离。

阶段验收：

- unknown identifier repair 能看到真实 declaration；
- mock 两轮 repair 第二轮通过 Lean；
- attempt 文件和 report 可完整复现。

### 14.4 Phase 4：Executable SynthesisDesign

修改：

- `agent/generative_reduction/synthesis/designs.py`；
- `agent/generative_reduction/synthesis/actions.py`；
- `agent/generative_reduction/synthesis/intermediates.py`；
- `agent/generative_reduction/providers/synthesis.py`；
- `agent/generative_reduction/recursive_runtime.py`；
- tests。

任务：

- [ ] constructor-first 真正走 structural action；
- [ ] helper-first 创建 typed helper child goal；
- [ ] direct-authoring 保持最后 fallback；
- [ ] strategy 选择 design；
- [ ] design stage 持久化；
- [ ] design switch 保留 failure memory；
- [ ] 不同 design 使用不同预算策略。

阶段验收：

- 两个 design 产生不同 proof-state transitions；
- strategy 选择的 design 确实被执行；
- mode 不再只是 prompt 标签。

### 14.5 Phase 5：Proof-producing Finite Synthesis Plugin

修改/新增：

- 新增通用 finite synthesis protocol；
- 扩展 plugin registry；
- 扩展 `agent/generative_reduction/plugins/boolean_csp.py`；
- 新增 Lean finite gadget reflection/certificate 模块；
- `agent/generative_reduction/recursive_runtime.py`；
- tests。

任务：

- [ ] reify finite typed goal；
- [ ] bounded witness grammar；
- [ ] executable checker；
- [ ] counterexample receipt；
- [ ] Lean certificate materializer；
- [ ] plugin action provider；
- [ ] strategy 可选择 plugin action；
- [ ] plugin failure 后可回退。

阶段验收：

- synthetic finite gadget 自动生成；
- 错误 witness 被语义 checker 排除；
- 正确 witness 通过 Lean；
- 无 benchmark case ID 分支。

### 14.6 Phase 6：Case02 单例真实 API

目标：

    Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case02PositiveNAE4

Case02 只作为黑盒验收目标，不作为实现分支。

运行要求：

- 禁止五个声明；
- 使用真实 provider；
- 保存全部 strategy effect receipts；
- 保存 context capsule hashes；
- 保存 repair lineage；
- 保存 finite search/counterexample receipts；
- 最终 artifact 独立验证；
- final route audit 通过。

硬验收：

- [ ] strategy proposal 至少一次真实影响 action 或 design；
- [ ] `unused_strategy_call_count = 0`；
- [ ] 至少一个 data-valued goal 被 structural provider 分解；
- [ ] 至少一个 generated capability 通过 Lean；
- [ ] generated capability 被 parent frame 使用；
- [ ] Case02 VERIFIED；
- [ ] 0 forbidden dependency。

如果 Case02 未通过，blocker 必须定位为：

- finite search bound 不足；
- certificate materializer 缺失；
- context capsule 缺 declaration；
- repair 未收敛；
- strategy 选择错误且 deterministic alternatives 已真实尝试；
- 明确的库 theorem/certificate gap。

不得退回“模型没有写出整个 proof”这一笼统结论。

### 14.7 Phase 7：Boolean CSP 20 题真实 API 回归

输出建议：

    Reports/GENERAL_AGENT_BOOLEAN_CSP_STRUCTURED_SYNTHESIS_REAL_API_REPORT.json

固定比较基线：

    Reports/GENERAL_AGENT_BOOLEAN_CSP_NO_CANONICAL_INTERPRETATION_REAL_API_STRESS_REPORT.json

必须比较：

- VERIFIED 数；
- BUDGET_EXHAUSTED 数；
- total API calls；
- strategy calls；
- strategy applied decisions；
- unused strategy calls；
- authoring calls；
- repair calls；
- generated Lean checks；
- generated Lean success；
- finite candidate checks；
- registered capabilities；
- final-used capabilities；
- total tokens；
- wall time；
- forbidden dependency count。

架构验收：

- 20/20 case 有终态；
- 0 unused strategy calls；
- 0 ignored valid strategy proposals；
- 0 benchmark-specific generic-core branch；
- 所有 generated capability 有独立 Lean receipt；
- 所有 VERIFIED case 通过 route audit；
- 所有失败 case 定位到最小 capability/design/plugin gap。

能力验收：

- 至少一个此前 BUDGET_EXHAUSTED 的 case 变为 VERIFIED；
- 至少一个最终 proof 使用新生成 capability；
- generated Lean success count 大于 0；
- 20/20 VERIFIED 仍是后续产品目标，但不通过硬编码实现。

## 15. 测试矩阵

### 15.1 Python unit

- [ ] strategy 选择第二 action；
- [ ] strategy 选择 synthesis design；
- [ ] strategy backtrack；
- [ ] invalid/stale strategy fallback；
- [ ] single-action 不调用 strategy；
- [ ] strategy decision/effect accounting；
- [ ] structural Pi intro；
- [ ] structure constructor fields；
- [ ] dependent constructor slots；
- [ ] projection cycle pruning；
- [ ] context capsule cache；
- [ ] diagnostic-driven capsule expansion；
- [ ] repair base hash；
- [ ] implementation/source dedup；
- [ ] design stage transitions；
- [ ] plugin supports receipt；
- [ ] finite candidate budget；
- [ ] CEGIS counterexample accumulation。

### 15.2 Lean synthetic

- [ ] function-valued data goal；
- [ ] ordinary structure goal；
- [ ] dependent structure goal；
- [ ] Exists/Subtype/Sigma；
- [ ] constructor field顺序错误；
- [ ] wrong local binder dependency；
- [ ] generated helper exact closure；
- [ ] repair 后 declaration exact type；
- [ ] finite witness正确性 certificate；
- [ ] forged executable receipt 不能绕过 Lean；
- [ ] forbidden dependency transitive rejection。

### 15.3 Integration

- [ ] deterministic structural proof，model disabled；
- [ ] theorem + constructor混合递归；
- [ ] strategy 真实控制 theorem action；
- [ ] strategy 真实控制 synthesis design；
- [ ] initial authoring + repair；
- [ ] repeated diagnostic 触发 design switch；
- [ ] plugin success 回注 parent frame；
- [ ] plugin failure 后 model fallback；
- [ ] resume 后继续同一 design/repair lineage；
- [ ] final artifact 使用 generated capability；
- [ ] complete strategy accounting。

### 15.4 防退化

- [ ] 旧 fast path 不回归；
- [ ] theorem recursion 不回归；
- [ ] data binding backtrack 不回归；
- [ ] `DATA_BINDING_REOPEN_FAILED = 0`；
- [ ] 不恢复 root-only authoring；
- [ ] 不创建平行 synthesis frontier；
- [ ] 不降低 final Lean verification；
- [ ] 不降低 route audit；
- [ ] 不让 strategy 直接声明 proof 成功；
- [ ] 不让 strategy 直接产生顶层 BLOCKED；
- [ ] 不让 plugin executable check 替代 Lean proof；
- [ ] 不引入 case ID 或 benchmark名称分支。

## 16. 指标与完成标准

### 16.1 Strategy 指标

- `unused_strategy_call_count = 0`；
- 所有 valid strategy proposal 均 applied 或带明确 override reason；
- applied action 与后续 expanded action 一致；
- 单 action goal 的 strategy call 数为 0；
- exact closure goal 的 strategy call 数为 0。

### 16.2 Authoring 指标

- repair prompt 包含 previous implementation 的比例为 100%；
- duplicate implementation 不进入 Lean；
- generated attempt 文件无覆盖；
- unknown identifier 比压力基线显著下降；
- generated Lean success count 大于 0。

### 16.3 搜索指标

- constructor-capable goal 至少产生一个 structural action；
- projection/self-loop 不消耗全部 search budget；
- finite plugin support goal 不直接跳到 monolithic authoring；
- budget exhausted 时报告最小阻塞 goal/design。

### 16.4 最终完成标准

本计划完成必须同时满足：

1. strategy 返回值真实控制 action、design 或当前 branch backtrack；
2. 不存在只记录 strategy receipt 而忽略 proposal 的生产路径；
3. Generic core 可以分解 Pi、structure 和常见 dependent constructors；
4. authoring 使用 Lean environment context capsule；
5. repair 基于上一版源码而不是无状态重写；
6. SynthesisDesign 有真实状态转换和不同执行语义；
7. 至少一个 proof-producing finite plugin 可用；
8. 至少一个此前失败的 Boolean CSP case 使用新生成 capability 通过；
9. 完成 20 题真实 API 回归；
10. 所有成功 artifact 通过 kernel、axiom、endpoint 和 forbidden dependency 审计；
11. generic core 不包含 Boolean CSP case/name 特判；
12. 所有失败可以归因到明确 capability、design、plugin、library 或 budget gap。

## 17. 立即执行顺序

1. 修复 strategy proposal 被忽略的问题；
2. 增加 StrategyDecision、EffectReceipt 和报告一致性；
3. 增加 strategy-controlled action/design 单元测试；
4. 实现 StructuralActionProvider 和 Lean structural probe；
5. 让 `Gadget` 等 structure goal 进入 constructor frame；
6. 实现 ContextCapsule；
7. 分离 initial authoring 与 repair；
8. 加入 previous source、diagnostic 分类与去重；
9. 将 mode 改为可执行 SynthesisDesign；
10. 实现通用 finite synthesis protocol；
11. 实现 Boolean CSP finite gadget adapter；
12. 运行 synthetic finite witness 测试；
13. 运行 Case02 真实 API 单例；
14. 修复明确 capability gap；
15. 运行禁用五个声明的 Boolean CSP 20 题真实 API 全量回归。

本轮核心判据是：

> Strategy 的每一次真实调用都必须改变或明确尝试改变下一步 proof-search 行为；复杂 data goal 必须先经过类型驱动的结构化分解和可验证求解器，再把最小、grounded、可修复的局部缺口交给模型。
