# 通用 NP-hard Agent 递归调度与整树重建实施计划

> 状态：Active
>
> 更新日期：2026-08-14
>
> 当前唯一实施主线：在保持现有输入校验、环境冻结、typed index、Capability Planner、三类 Action Provider、预算、模型协议和最终 Lean 审计设计不变的前提下，接通全局 AND/OR 递归调度，使 theorem premise、data witness、局部生成 capability 和失败分支能够重新进入统一搜索。
>
> 本文件只记录尚未完成的工作。已经存在的 CLI、package、Lean probe、planner/provider/frontier 骨架、基础 route audit 和已经执行过的测试不再作为待办重复列出。

## 1. 本轮目标

给定已经通过 Input Gate 的根目标：

    ComplexityReduction.Certificate.NativeTMNPHard target

Agent 必须能够完成以下闭环：

1. 从 Global Proof Frontier 选择一个 ProofState；
2. 从该 state 选择一个当前可求解的 OpenGoal；
3. 对该子目标运行 Capability Planner；
4. 从 Reuse、Theorem、Synthesis 三类候选中扩张一个或多个 OR 分支；
5. theorem application 产生的全部前提作为 AND obligations 进入同一个 ProofState；
6. data binder 被具体实例化后，所有依赖它的 sibling obligations 自动得到同一实例；
7. 子目标失败只淘汰当前 action 或当前 branch，不直接终止整个 job；
8. 生成并通过 Lean 检查的新 capability 立即回注当前 branch，并触发相关子目标重新规划；
9. 所有 application frame 闭合后重建完整 Lean application tree；
10. 最终 artifact 独立 elaboration、kernel check、axiom check 和 forbidden-declaration 传递依赖审计通过。

本轮不以“Python 函数递归调用”为目标。递归语义由 ProofState 的 goal decomposition 表达，调度继续使用有界、可恢复、可回溯的迭代式全局 frontier。

## 2. 当前必须解决的行为缺口

当前实现的核心缺口不是缺少 planner 或 frontier 类型，而是生产控制流没有把它们接成闭环：

- orchestrator 在 INDEX_READY 后只对根目标规划一次；
- 根目标不能直接闭合时，控制流进入根目标整体 authoring，而不是递归处理 theorem premises；
- SearchCoordinator 尚未接入生产 orchestrator；
- SearchCoordinator 每轮只选择一个 action，该 action 没有产生 child state 时会直接丢弃当前 state；
- OpenGoal 已有 attempted_actions 字段，但 ProofState 没有对应的不可变更新接口；
- ProofState fingerprint 没有纳入 attempted actions 和 failure memory，失败状态重新入队时可能被 frontier 当成旧状态去重；
- decompose_goal 只复制 pretty-printed residual type，不能保存不同前提之间共享的 Lean binder；
- 带有 ?Γ' 等 unresolved metavariable 的文本被当成彼此独立的子目标，无法保证 source hardness 与 interpretation 使用同一个 Γ'；
- proof_skeleton 是平面 ProofStep 序列，不能证明全部 child proof term 已经正确填回 parent theorem telescope；
- reconstruction 只能处理单定理闭包或根目标整体 authored source，不能重建多层 application tree；
- 单次模型失败、Lean 失败或某个 theorem route 失败仍可能过早映射为 BLOCKED 或 FAILED_MODEL。

当前 dichotomy-free Boolean CSP 真实 API 基线为：

- 20 个 case 全量执行；
- 53 次真实模型调用，53 次 HTTP 200；
- 3 个 VERIFIED；
- 15 个 BLOCKED；
- 2 个 FAILED_MODEL；
- 0 个新 CertifiedReduction；
- 0 个 generated edge 被最终 artifact 使用。

代表性失败已经能选中 interpretation transport theorem，但没有继续递归完成以下共享前提：

    Γ' : Gamma
    LanguageInterpretation Γ' target
    NativeTMNPHard (cspOf Γ')

因此本轮优先修复控制流、依赖绑定和重建，不先扩大模型 prompt 或增加 Boolean CSP 专用结论。

## 3. 保持不变的边界

以下流程继续保留，不在本轮重写：

- scripts/prove_np_hard.py 的旧入口行为；
- agent/hardness/boolean_csp_np_hard_benchmark.py 的旧 benchmark 协议；
- scripts/prove_np_hard_general.py 的 request、strategy、profile 和 budget 接口；
- Input Gate、endpoint normalization 和 environment snapshot；
- closed resolver fast path；
- typed theorem index 的总体召回入口；
- ExactClosureProbe 先执行闭包检查、GuidedProofPlanner 再提供证明指导的职责划分；
- ReuseActionProvider、TheoremActionProvider、SynthesisActionProvider 三类来源；
- GlobalProofFrontier 与 ReadyActionBuckets 的总体设计；
- job-local generated module 边界；
- model strategy 与 authoring 调用分离；
- final Lean verification、标准公理检查和 forbidden-declaration 审计；
- proof_status、solution_classification、qualification_status 三类结果字段；
- Boolean CSP 领域信息不得进入 generic core 的原则。

本轮只允许为递归闭环扩展这些接口，不重新引入三套彼此独立的 proof pipeline。

## 4. 目标控制流

生产 orchestrator 的中段改为：

    INPUT_VALIDATED
      -> ENVIRONMENT_FROZEN
      -> FAST_PATH_CHECKED
      -> INDEX_READY
      -> SEARCHING
           -> pop ProofState
           -> select ready OpenGoal
           -> state-aware candidate lookup
           -> Capability Planner
           -> select unattempted action
           -> execute action
           -> push child/failure-memory states
           -> repeat
      -> PROOF_RECONSTRUCTED
      -> final Lean verification and route audit
      -> COMPLETED

局部 action 的结果只允许是：

- closed：关闭当前 goal 或 application slot；
- decomposed：创建 application frame，并激活当前已经具备依赖的 child goals；
- generated：注册一个 Lean 已验证 capability，然后关闭或继续分解当前 goal；
- failed-branch：记录失败并将仍有 alternative 的 state 重新入队；
- pruned-cycle：当前 action 无实质进展，淘汰该 action；
- budget-stop：由统一 BudgetTracker 终止搜索。

BLOCKED 只能在 GlobalProofFrontier 真正耗尽后产生，不能作为单个 action handler 的返回值直接结束 job。

## 5. ProofState 与依赖应用图

### 5.1 新增 ApplicationFrame

在 agent/generative_reduction/models.py 中增加可序列化、不可变的数据结构：

    BinderSlot
      slot_id
      ordinal
      binder_name
      binder_kind
      exact_type
      dependency_slot_ids
      bound_term
      bound_declaration
      provenance

    PremiseSlot
      slot_id
      ordinal
      premise_kind
      type_template_receipt
      dependency_slot_ids
      instantiated_exact_type
      child_goal_id
      proof_term
      declaration
      status

    ApplicationFrame
      frame_id
      parent_goal_id
      parent_exact_type
      action_id
      declaration
      guidance_id
      application_skeleton
      binder_slots
      premise_slots
      result_proof_term
      status
      lean_receipt_hash

frame status 至少包含：

- waiting-bindings；
- active；
- saturated；
- verified；
- failed。

### 5.2 OpenGoal 扩展

OpenGoal 增加：

- producer_frame_id；
- producer_slot_id；
- dependency_slot_ids；
- ready；
- attempted_actions；
- normalized_last_diagnostic_hash。

强制不变量：

1. 每个进入 open_goals 的 exact_type 必须可以在其显式 local context 下重新 elaboration；
2. open_goals 中不得保存跨进程不可恢复的 Lean metavariable ID；
3. 仍依赖未绑定 data slot 的 premise 不进入 open_goals，只保存在 ApplicationFrame 中；
4. 同一 goal 的 attempted_actions 只记录已经真实扩张过的 action；
5. 一个 child goal 只能填充一个明确的 frame slot。

### 5.3 ProofState 扩展

ProofState 增加：

- application_frames；
- generated_capabilities；
- verified_frame_fragments；
- root_fragment；
- normalized_failure_fingerprints。

新增不可变状态转换：

- mark_action_attempted(goal_id, action_id)；
- add_application_frame(goal_id, action, guidance, frame)；
- activate_ready_premises(frame_id)；
- bind_data_slot(frame_id, slot_id, fragment)；
- fill_premise_slot(frame_id, slot_id, fragment)；
- refresh_dependent_premises(frame_id, lean_instantiation_result)；
- verify_saturated_frame(frame_id, receipt)；
- fail_frame(frame_id, diagnostic)；
- add_generated_capability(fragment, module, source_hash)；
- remember_failure(action, diagnostic, blocker_code)；
- prune_non_progressing_action(goal_id, action_id, reason)。

ProofState.complete 改为同时满足：

- 没有 ready 或 dormant 的未闭合 obligation；
- 所有 application frame 均为 verified；
- root_fragment 已存在；
- root_fragment.exact_type 与 root_goal.exact_type 一致。

### 5.4 State fingerprint

ProofState fingerprint 必须包含：

- root exact type；
- 每个 open goal 的 GoalKey；
- 每个 open goal 的 attempted action IDs；
- application frame 的 declaration、slot 状态和 binder substitutions；
- generated capability 的 exact type、declaration、module 和 source hash；
- normalized failure fingerprint；
- verified fragment 的 exact type 与 proof term fingerprint。

不得把完整、非规范化 diagnostics 文本直接加入 fingerprint；只保存稳定 blocker code 和 diagnostic hash。

这个修改必须保证：

- action 失败后的 state 与失败前 state 不会被误去重；
- 两个使用不同 Γ' witness 的分支不会被合并；
- 两个只在物理 workspace 中存在、但 state import set 不同的分支不会互相污染；
- resume 后可以重新构造同一搜索状态。

## 6. Lean 侧依赖实例化

### 6.1 禁止 Python 替换 Lean metavariable 文本

Python 不得通过字符串替换把 ?Γ' 改成某个 declaration。Lean 负责 theorem telescope、implicit binder、universe 和 dependent premise 的重新实例化。

扩展以下 Lean 模块：

- Lean/Reference/ComplexityReduction/Agent/GenerativeReduction/RuleApplication.lean；
- Lean/Reference/ComplexityReduction/Agent/GenerativeReduction/TheoremIndex.lean；
- 必要时扩展 GuidedProofProbe.lean。

新增一个 typed rule instantiation probe，输入：

- candidate declaration；
- 当前 exact target goal；
- 已绑定 binder slot 的 ordinal 和 Lean term；
- local context receipt；
- transparency mode。

输出：

- stable binder slot IDs；
- 每个 binder 的类型和依赖 ordinal；
- 已由 target unification 决定的 binder assignments；
- 仍需搜索的 data binder；
- 每个 premise 的依赖 slot IDs；
- 当前已完全实例化且可独立 elaboration 的 premise exact type；
- 暂时 dormant 的 premise；
- 可重建 application skeleton；
- environment/import receipt。

stable slot ID 使用 theorem binder ordinal 和 frame ID，不保存 Lean internal metavariable ID。

### 6.2 Dependent premise 激活

以 interpretation transport 为例，第一次 probe 返回：

    b0 : Gamma
    p1 : LanguageInterpretation $b0 target    depends on b0
    p2 : NativeTMNPHard (cspOf $b0)          depends on b0

只有 b0 先进入 open_goals。

当 b0 被关闭为 KnownHardGamma 后，重新调用 Lean probe，得到：

    LanguageInterpretation KnownHardGamma target
    NativeTMNPHard (cspOf KnownHardGamma)

此时才创建 p1 和 p2 的 OpenGoal。

### 6.3 Data witness 搜索

data binder 与 proposition premise 使用同一个 typed candidate lookup，但排序需要增加通用 downstream lookahead：

- candidate term 是否精确具有 binder type；
- 绑定后可以直接闭合多少 sibling premises；
- 绑定后是否出现已知 hardness、path 或 exact theorem；
- 是否产生 forbidden dependency；
- 是否使 residual obligation 数量减少；
- 是否重复祖先 binding。

该 lookahead 必须基于 dependent premise 的类型覆盖率，不得写 Boolean CSP、Gamma 或 NAE 名称分支。

## 7. State-aware Candidate Lookup

修改 SearchCoordinator 的 CandidateLookup 协议：

    candidate_lookup(state, goal) -> Sequence[TheoremIndexEntry]

原因是每个 branch 的 generated modules、fragments、imports 和 failure memory 不同，candidate lookup 不能只依赖 OpenGoal。

实现要求：

1. 基础模块来自冻结的 environment snapshot；
2. branch-local 模块只取 state.generated_modules；
3. 对每个 exact child goal 调用 query_typed_goal_index；
4. 当前 state 的 verified fragments 同时进入 ExactClosureProbe；
5. forbidden declarations 在召回、规划、生成源码扫描和最终传递依赖审计四层过滤；
6. action_id 已在 goal.attempted_actions 中的 candidate 不再返回；
7. 失败 declaration、binding 和 guidance fingerprint 进入局部负缓存；
8. 新 capability 注入后只使相关 GoalKey 的 capability cache 失效；
9. 不把某个 branch 已生成但未导入的物理文件视为全局 capability。

缓存 key 至少包含：

- GoalKey；
- environment fingerprint；
- state capability fingerprint；
- import set fingerprint；
- failure memory fingerprint；
- forbidden declaration fingerprint。

## 8. Recursive Action Executor

新增：

- agent/generative_reduction/recursive_runtime.py。

该文件承载 candidate lookup、action execution、frame verification和 subgoal synthesis 适配，避免继续扩大 orchestrator。

### 8.1 CLOSED

执行顺序：

1. 检查 action.lean_verified；
2. 确认 proof term exact type；
3. mark_action_attempted；
4. 创建 ReusableFragment；
5. 如果 goal 是普通 root/child goal，关闭 goal；
6. 如果 goal 对应 binder slot，绑定 slot 并调用 Lean 重新实例化 dependent premises；
7. 如果 goal 对应 proposition premise slot，填充 slot；
8. 激活新 ready premises；
9. 若 frame saturated，立即重建并 Lean 检查该 frame；
10. frame verified 后生成 parent fragment。

### 8.2 DECOMPOSED

执行顺序：

1. 从 plan.ranked_proof_guidance 精确找到 guidance_id；
2. 调用 Lean rule instantiation probe；
3. 验证 probe conclusion 与 goal exact type 一致；
4. 创建 ApplicationFrame；
5. 将 already_closed_premises 填入对应 slot；
6. 只激活当前依赖已经满足的 premise；
7. 将 parent goal 从 open_goals 移除；
8. 返回包含 frame 和 child goals 的新 ProofState。

以下情况不得创建 child state：

- candidate conclusion 不能重新统一；
- residual premise 含未受 frame 管理的 unresolved metavariable；
- theorem application 只产生与 parent 相同的 goal，且没有新 binding、fragment 或 capability；
- declaration、binding 和 residual multiset 与祖先 frame 完全相同；
- route 使用 forbidden declaration。

### 8.3 SYNTHESIS_REQUIRED

把 orchestrator._attempt_open_synthesis 的可复用逻辑迁移为子目标 executor：

    execute_synthesis(state, goal, plan, action)

约束：

- expected declaration type 必须等于 goal.exact_type；
- prompt 只要求实现当前 child capability，不要求直接证明根 problemIsNPHard；
- model strategy 可以选择 helper、intermediate 或 construction mode；
- authoring 每次只写 job-local generated module；
- 每次 materialization 必须先确认 goal、plan fingerprint 和 capability fingerprint 仍有效；
- 编译成功后注册 generated capability；
- generated module 使用内容 hash 或 job/state/action hash 命名；
- 新 capability 立即关闭当前 slot 或重新进入 Planner；
- 编译失败更新 action failure memory，并回到全局 frontier；
- 单个 model call 失败只淘汰当前 synthesis attempt；
- model policy required 只有在所有剩余分支均要求模型且 provider 不可用时，才聚合为顶层 FAILED_MODEL。

### 8.4 Action failure

action executor 不得用空 children 表示“整个 state 无路可走”。

普通失败返回：

    state
      -> mark_action_attempted
      -> remember_failure
      -> push back to GlobalProofFrontier

只有当前 goal 的所有 action 都已尝试，且重新规划也没有新 candidate 时，当前 state 才被淘汰。

## 9. SearchCoordinator 修正

修改 agent/generative_reduction/search.py。

### 9.1 调度

每轮流程：

1. pop best state；
2. 如果 state complete，返回 completed_state；
3. 选择 ready OpenGoal；
4. state-aware candidate lookup；
5. planner.plan；
6. 过滤 attempted actions；
7. ReadyActionBuckets 选择 provider-aware action；
8. executor 返回 success child、failure-memory child 或多个 OR child；
9. 将所有合法 child 推回同一个 GlobalProofFrontier。

### 9.2 多 action 与回退

第一版可以继续每次只扩张一个 action，但必须满足：

- 失败 state 重新入队；
- 下次不会再次选择同一个 action；
- alternative theorem/reuse/synthesis action 仍然存在；
- provider activation deadline 在多次回队后仍正确累计。

如果实现复杂度可控，可以增加 choose_many：

- exact CLOSED action 立即执行；
- 其余 provider 每轮各保留最多一个 action；
- 受 max_branching_per_expansion 限制；
- 每个 action 产生独立 immutable child state。

choose_many 不是首个实现版本的硬要求，正确回队是硬要求。

### 9.3 Goal 选择

select_open_goal 改为只选择 ready goal。建议排序：

1. 可以 exact close 的 goal；
2. data binder，因为它可能解锁多个 dependent premises；
3. 预计 deterministic coverage 高的 proposition；
4. residual count 少的 theorem/path goal；
5. synthesis goal。

排序只能影响成本，不得成为 provider 门禁。

### 9.4 循环与进展

新增通用 progress fingerprint：

- parent GoalKey；
- selected declaration；
- binder substitutions；
- residual GoalKey multiset；
- generated capability delta。

如果 action 后：

- parent goal 等价地重新出现；
- residual multiset 没有减少或具体化；
- 没有新 verified fragment；
- 没有新 binder substitution；
- 没有新 generated capability；

则记录 non_progressing_decomposition 并淘汰该 action。

### 9.5 顶层终止语义

- VERIFIED：completed state 经整树重建和最终 Lean 验证；
- BLOCKED：frontier 为空，预算仍有剩余，且所有 state/action 均已穷尽；
- BUDGET_EXHAUSTED：统一 BudgetTracker 抛出预算停止；
- FAILED_MODEL：模型是所有剩余可行分支的必要条件，并且 required provider 全部失败或不可用；
- FAILED_LEAN：输入/环境/最终验证发生不能归属于普通 branch 的基础设施或可信边界错误。

每个 BLOCKED 必须包含：

- 最佳 state；
- 所有剩余或最后淘汰的 goals；
- 每个 goal 已尝试 action；
- action failure codes；
- 是否存在 dormant dependent premises；
- frontier exhaustion receipt；
- provider statistics；
- remaining budget。

## 10. Frame Verification 与 Proof Reconstruction

### 10.1 局部 frame 验证

当一个 ApplicationFrame 的全部 binder 和 premise slots 已填充时：

1. 生成 job-local frame theorem；
2. 使用保存的 application skeleton 和 child proof terms；
3. 精确声明 parent_exact_type；
4. 运行 Lean；
5. 成功后把 frame 标记为 verified，并创建 parent ReusableFragment；
6. 失败后将对应 theorem action 标记失败，保存 diagnostic，并让其他 OR branch 继续。

state 不能仅因 open_goals 为空就完成；每个 frame 必须已经通过上述局部验证。

### 10.2 整树重建

在 agent/generative_reduction/reconstruction.py 中新增：

    build_search_artifact_source(completed_state, ...)

职责：

- 按 application frame DAG 拓扑排序；
- 导入 base modules、plugin modules 和当前 completed branch 的 generated modules；
- 发出 generated helper；
- 发出每个 verified frame 对应的局部 theorem；
- 发出精确根声明 problemIsNPHard；
- 保留 assert_standard_axioms；
- 保留 forbidden source scan；
- 保留最终 theorem 的传递依赖 RouteAudit；
- 保留 endpoint 和 exact type 检查。

最终 Artifact.lean 仍需独立编译。Python 的 completed_state 只表示“具备完整、局部已验证的重建材料”，不能取代最终 Lean 权威。

### 10.3 最终重建失败

如果局部 frame 都已验证但最终 artifact 失败：

- 首先分类为 import/order/name collision、stale capability、route audit 或真实 proof mismatch；
- 可定位到具体 frame/action 时，把诊断写入 failure memory 并恢复到最近可重建 state；
- 只有无法归因于普通 proof branch 的基础设施错误才返回 FAILED_LEAN；
- 不允许直接丢弃整棵搜索树而不保存 reconstruct receipt。

## 11. Orchestrator 接线

修改 agent/generative_reduction/orchestrator.py。

### 11.1 保留前段

以下前置流程原样保留：

- request 和 job store；
- stable entrypoint guard；
- input certification；
- environment snapshot；
- optional input module build；
- closed resolver fast path；
- root theorem index；
- plugin installation；
- route policy；
- BudgetTracker；
- final result/report 写入。

### 11.2 替换中段

在 INDEX_READY 之后：

1. 建立 RecursiveSearchRuntime；
2. 建立 ProofState.initial；
3. 建立 SearchCoordinator；
4. 调用 coordinator.run(initial_state)；
5. 持续写入 state、plan、frame 和 action events；
6. completed_state 进入 build_search_artifact_source；
7. blocked/budget/model outcome 进入统一 failure result。

删除生产路径中的：

- 根目标只运行一次 planner 的终止语义；
- root-substep-plan 作为唯一 plan 的假设；
- 非 closed 根目标直接跳到整体 _attempt_open_synthesis 的行为。

旧 _attempt_open_synthesis 在子目标 executor 完成迁移并通过测试后删除；迁移期间不得保留两个可同时触发的 authoring 入口。

### 11.3 状态事件

至少记录：

- STATE_PUSHED；
- STATE_POPPED；
- GOAL_SELECTED；
- PLAN_REUSED；
- PLAN_COMPUTED；
- ACTION_EXPANDED；
- ACTION_FAILED_REQUEUED；
- GOAL_DECOMPOSED；
- BINDER_BOUND；
- DEPENDENT_GOAL_ACTIVATED；
- GOAL_CLOSED；
- FRAME_SATURATED；
- FRAME_VERIFIED；
- GENERATED_CAPABILITY_REGISTERED；
- STATE_COMPLETED；
- FRONTIER_EXHAUSTED；
- PROOF_RECONSTRUCTED。

## 12. 报告字段

GeneralNPHardResult 和 report.json 增加：

- expanded_state_count；
- requeued_failure_state_count；
- pruned_cycle_count；
- max_observed_search_depth；
- application_frame_count；
- verified_application_frame_count；
- data_binding_count；
- dependent_goal_activation_count；
- recursive_substep_plan_count；
- generated_capability_count；
- final_frontier_size；
- frontier_exhaustion_receipt；
- proof_tree；
- per-goal attempted actions；
- per-action blocker code；
- branch-local generated imports；
- final route audit receipt。

真实 API 报告还必须包含：

- provider 和 model；
- strategy call count；
- authoring call count；
- HTTP status receipt；
- accepted response count；
- generated source hashes；
- 每个 generated declaration 的 exact type；
- 最终 artifact 是否实际使用 generated declaration；
- 不包含 API key、authorization header 或完整敏感请求。

## 13. 按功能拆分的实施任务

以下列表全部是未完成事项。

### 失败回队与搜索终止语义

修改文件：

- agent/generative_reduction/models.py；
- agent/generative_reduction/proof_state.py；
- agent/generative_reduction/search.py；
- agent/generative_reduction/proof_frontier.py；
- tests/test_generative_reduction.py。

任务：

- [ ] 实现 mark_action_attempted；
- [ ] attempted action 进入 state fingerprint；
- [ ] normalized failure fingerprint 进入 state fingerprint；
- [ ] SearchCoordinator 使用 state-aware CandidateLookup 签名；
- [ ] executor 失败返回 failure-memory child；
- [ ] Planner/action merge 过滤 attempted actions；
- [ ] action alternative 可以在下一个 search round 被选择；
- [ ] BLOCKED 只在 frontier exhausted 时产生；
- [ ] 增加 non-progressing decomposition guard；
- [ ] 增加对应 unit tests。

验收：

- 第一个 theorem action 失败后，同一 goal 的第二个 theorem action被扩张；
- theorem action 失败后 synthesis action仍可被扩张；
- failure-memory child 不被 dedup；
- self-loop theorem 不消耗全部 search depth；
- 单个 model/Lean action 失败不直接返回顶层 BLOCKED。

### ApplicationFrame 与 dependent binder

修改文件：

- agent/generative_reduction/models.py；
- agent/generative_reduction/proof_state.py；
- agent/generative_reduction/theorem_index.py；
- agent/generative_reduction/lean_bridge.py；
- Lean/Reference/ComplexityReduction/Agent/GenerativeReduction/RuleApplication.lean；
- Lean/Reference/ComplexityReduction/Agent/GenerativeReduction/TheoremIndex.lean；
- tests/test_generative_reduction.py。

任务：

- [ ] 定义 BinderSlot、PremiseSlot、ApplicationFrame；
- [ ] Lean probe 输出稳定 binder ordinal 和 dependency graph；
- [ ] 禁止 unresolved metavariable exact_type 进入 OpenGoal；
- [ ] dormant premise 在依赖绑定前不进入 frontier；
- [ ] data binder 关闭后由 Lean 重新实例化 dependent premises；
- [ ] 同一 binder substitution 同时作用于全部 sibling premises；
- [ ] 增加 branch-specific binding fingerprint；
- [ ] 增加 data witness downstream coverage ranking；
- [ ] 实现 frame serialization/resume round-trip；
- [ ] 增加 synthetic dependent theorem tests。

验收：

- Γ' 选择一个具体 Gamma 后，interpretation 和 source hardness 精确引用同一个 declaration；
- 两个不同 Gamma witness 形成两个不同 ProofState；
- 不出现含 ?m 或 ?Γ' 的独立 OpenGoal；
- wrong witness 或 wrong dependent proof 被 Lean 拒绝；
- resume 后能够重建相同 frame 和 exact child types。

### Recursive Action Executor

修改文件：

- 新增 agent/generative_reduction/recursive_runtime.py；
- agent/generative_reduction/capability_planner.py；
- agent/generative_reduction/exact_closure_probe.py；
- agent/generative_reduction/guided_proof_planner.py；
- agent/generative_reduction/providers/reuse.py；
- agent/generative_reduction/providers/theorem.py；
- agent/generative_reduction/providers/synthesis.py；
- tests/test_generative_reduction.py。

任务：

- [ ] 实现 CLOSED handler；
- [ ] 实现 DECOMPOSED handler；
- [ ] 已闭合 premise 精确填入 frame slot；
- [ ] child goal closure 自动填回 producer slot；
- [ ] frame saturated 后生成 parent fragment；
- [ ] 实现 branch-local candidate lookup；
- [ ] generated modules 纳入 capability fingerprint；
- [ ] forbidden declaration 在每个 child lookup 中继续生效；
- [ ] action diagnostics 规范化为稳定 blocker code；
- [ ] provider statistics 按真实 expansion 更新。

验收：

- 一个三层 theorem application tree 可在 model disabled 下闭合；
- 普通 Prop、data binder、typeclass premise 均走同一 executor；
- child fragment 不会填入错误 frame slot；
- 当前 branch 的 generated capability 不会出现在 sibling branch；
- provider statistics 与 event log 一致。

### 局部 frame 验证与整树重建

修改文件：

- agent/generative_reduction/reconstruction.py；
- agent/generative_reduction/proof_state.py；
- agent/generative_reduction/verification/core.py；
- Lean/Reference/ComplexityReduction/Agent/GenerativeReduction/ProofReconstruction.lean；
- Lean/Reference/ComplexityReduction/Agent/GenerativeReduction/FinalCheck.lean；
- tests/test_generative_reduction.py。

任务：

- [ ] frame saturated 时生成局部 Lean theorem；
- [ ] 局部 theorem 通过后 frame 才标记 verified；
- [ ] verified frame 产生 parent ReusableFragment；
- [ ] build_search_artifact_source 按 DAG 拓扑排序；
- [ ] root_fragment 精确绑定根 endpoint；
- [ ] generated modules 只导入 completed branch 实际使用集合；
- [ ] 最终 artifact 保留 axiom 和 forbidden dependency audit；
- [ ] reconstruction failure 可定位到 frame/action；
- [ ] 增加 independent final replay tests。

验收：

- Python 手工伪造 complete state 不能绕过 frame verification；
- child 顺序或 binder substitution 错误时 Lean 失败；
- 正确多层 tree 可生成独立 Artifact.lean；
- final theorem 精确为请求的 NativeTMNPHard target；
- forbidden dichotomy 的直接和传递依赖都被拒绝。

### Orchestrator 生产接线

修改文件：

- agent/generative_reduction/orchestrator.py；
- agent/generative_reduction/reporting.py；
- agent/generative_reduction/job.py；
- scripts/prove_np_hard_general.py；
- tests/test_generative_reduction.py。

任务：

- [ ] INDEX_READY 后实例化 SearchCoordinator；
- [ ] root initial state 进入 GlobalProofFrontier；
- [ ] state、goal、plan、action、frame events 持久化；
- [ ] completed outcome 进入整树 reconstruction；
- [ ] blocked/budget/model outcome 统一映射；
- [ ] 移除根目标一次性 planner 的生产终止路径；
- [ ] 移除根目标整体 authoring 的默认 fallback；
- [ ] 保留 closed resolver fast path；
- [ ] resume 能恢复 frontier 和 frame；
- [ ] report 输出递归 proof tree 和 frontier exhaustion receipt。

验收：

- rg 搜索能够找到生产代码对 SearchCoordinator 的真实实例化；
- 非 fast-path job 至少运行两个不同 GoalKey 的 SubstepPlan；
- 一个 action 失败后日志出现 ACTION_FAILED_REQUEUED，随后出现其他 action expansion；
- BLOCKED report 能证明 frontier 已耗尽；
- fast-path case 行为和结果保持不变。

### 子目标级模型生成

修改文件：

- agent/generative_reduction/recursive_runtime.py；
- agent/generative_reduction/model/strategy.py；
- agent/generative_reduction/model/authoring.py；
- agent/generative_reduction/synthesis/actions.py；
- agent/generative_reduction/synthesis/designs.py；
- agent/generative_reduction/synthesis/materialize.py；
- agent/generative_reduction/construction_frontier.py；
- agent/generative_reduction/orchestrator.py；
- tests/test_generative_reduction.py。

任务：

- [ ] 将 _attempt_open_synthesis 迁移为 execute_synthesis；
- [ ] prompt 固定当前 child exact type；
- [ ] authoring 输出一个可命名、可复用的局部 declaration；
- [ ] compile diagnostics 只反馈当前 subgoal 和 design；
- [ ] 成功 capability 立即注入当前 state；
- [ ] 新 capability 触发相关 Planner cache 增量失效；
- [ ] 同一 plan fingerprint 的 repair 不重复 strategy call；
- [ ] design 改变时创建新 action/design fingerprint；
- [ ] 单次 API 失败保留 theorem/reuse alternatives；
- [ ] 删除旧 root-only synthesis 入口。

验收：

- 模型不再被要求每次直接实现 problemIsNPHard；
- 一个 child interpretation/helper 编译成功后可被 parent frame 使用；
- generated declaration exact type 与 child goal 一致；
- 一个 synthesis design 失败后可以切换 theorem 或另一个 design；
- report 能区分 strategy、authoring、accepted capability 和 final usage。

### Boolean CSP 非 dichotomy 纵向通路

优先目标：

- Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case02PositiveNAE4；
- 如该 case 暴露额外库能力缺口，先使用同型 synthetic theorem 验证调度，再回到真实 case，不用 case-specific Python 分支绕过。

预期 proof shape：

    NativeTMNPHard target
      <- interpretation transport theorem
         AND source language witness
         AND LanguageInterpretation source target
         AND NativeTMNPHard (cspOf source)

任务：

- [ ] 根目标选择通用 interpretation/path/reduction theorem；
- [ ] source data binder 由 typed index 提供候选；
- [ ] source hardness 通过库内已有 theorem/path 关闭；
- [ ] interpretation 通过复用、helper authoring 或局部 synthesis 关闭；
- [ ] parent frame 重建；
- [ ] final artifact 通过 forbidden declaration transitive audit；
- [ ] proof tree 不引用 dichotomy 结论；
- [ ] 保存完整 state/action/model/Lean receipts。

硬验收：

- 至少一个此前 BLOCKED 的真实 Boolean CSP case 变为 VERIFIED；
- 该 case 至少包含一个 DECOMPOSED action和两个递归 child goals；
- source hardness 与 interpretation 使用同一个 source binder；
- 最终 proof 不是 direct dichotomy wrapper；
- 如果调用模型，存在真实 HTTP 200 receipt；
- 如果未调用模型，报告必须明确全部 child capability 来自库内复用。

### Boolean CSP 20 题真实 API 全量回归

固定禁止声明：

- ComplexityReduction.Domain.BooleanCSP.Hardness.NativeTMNPHard_of_notSchaeferTractable；
- ComplexityReduction.Domain.BooleanCSP.Hardness.NativeTMNPHard_of_notSchaeferTractable_with_oneInThree；
- ComplexityReduction.Domain.BooleanCSP.schaefer_dichotomy。

任务：

- [ ] 对 20 个 case 全部运行新 recursive orchestrator；
- [ ] model policy 使用真实 provider 配置；
- [ ] 每个实际模型调用保存 provider、model、HTTP status 和 response hash；
- [ ] 验证所有 case 均生成终态 report；
- [ ] 对每个 BLOCKED 检查 frontier exhaustion receipt；
- [ ] 对每个 FAILED_MODEL 检查不存在仍可执行的非模型 action；
- [ ] 对每个 VERIFIED 检查完整 proof tree 和 final route audit；
- [ ] 汇总递归深度、frame、binding、requeue 和 provider statistics；
- [ ] 生成新的独立报告，不覆盖此前基线。

建议输出：

    Reports/GENERAL_AGENT_BOOLEAN_CSP_RECURSIVE_DICHOTOMY_FREE_REAL_API_REPORT.json

架构验收：

- 20/20 case 均完成真实全量运行；
- 不存在 root-only authoring 路径；
- 不存在 action 失败后仍有 alternative 却直接 BLOCKED 的 case；
- 所有 unresolved metavariable 都停留在 Lean frame 内部，不作为孤立 OpenGoal；
- 至少一个此前 BLOCKED case 通过递归路径 VERIFIED；
- 真实 API 调用数与 HTTP 200 receipts 一致；
- 0 个 forbidden declaration direct/transitive dependency。

能力目标：

- 尽可能提高 VERIFIED 数；
- 20/20 VERIFIED 是后续产品目标；
- 如果未达到 20/20，每个失败必须归因到明确的数学/library/model capability gap，而不是递归调度缺失或 premature BLOCKED。

## 14. 测试矩阵

### 14.1 Python unit

- [ ] failure state fingerprint 与原 state 不同；
- [ ] attempted action 不会再次执行；
- [ ] alternative action 在失败后被选择；
- [ ] frontier 为空前不能返回 BLOCKED；
- [ ] data binder closure 激活全部 dependent premises；
- [ ] sibling premises 共享同一 binder term；
- [ ] dormant premise 不进入 select_open_goal；
- [ ] branch-local generated module 不交叉污染；
- [ ] self-loop theorem 被 progress guard 拒绝；
- [ ] state/frame serialization round-trip；
- [ ] saturated but unverified frame 不计 complete；
- [ ] verified frame 产生 parent fragment；
- [ ] reconstructed root tree 顺序稳定。

### 14.2 Lean synthetic

- [ ] 带一个 data binder 和两个 dependent premises 的 theorem；
- [ ] 两层 dependent theorem application；
- [ ] 普通 proposition recursive theorem；
- [ ] typeclass dependent premise；
- [ ] wrong binder witness；
- [ ] wrong child proof term；
- [ ] theorem A -> A non-progress cycle；
- [ ] generated helper exact child closure；
- [ ] final multi-node artifact independent replay；
- [ ] forbidden dependency transitive rejection。

### 14.3 Integration

- [ ] model disabled 的纯 theorem recursion；
- [ ] mock authoring 的 child capability generation；
- [ ] real provider 的单 case child authoring；
- [ ] real provider 的 action failure + backtrack；
- [ ] resume 后继续同一个 frontier；
- [ ] budget exhausted 与 frontier exhausted 分离；
- [ ] closed resolver fast path 不回归；
- [ ] synthesis-required 仍禁止直接根闭包，但允许子目标复用。

### 14.4 防退化

- [ ] 不增加 Boolean CSP case ID 分支；
- [ ] 不增加 Gamma/NAE 名称判断到 generic search；
- [ ] 不通过 Python 字符串替换 Lean binder；
- [ ] 不创建 Reuse/Theorem/Synthesis 三个独立 ProofState frontier；
- [ ] 不因 theorem bucket 非空禁止 synthesis；
- [ ] 不因模型失败丢弃非模型 branch；
- [ ] 不因 physical generated file 存在把它泄漏到其他 branch；
- [ ] 不把 completed_state 当成最终 kernel proof；
- [ ] 不降低 forbidden route audit；
- [ ] 不修改旧 Boolean CSP runner 的公开协议。

## 15. 预算与配置新增项

如现有 Budget 尚未覆盖，增加：

- max_branching_per_expansion；
- max_application_frames；
- max_data_witness_candidates；
- max_dependent_reinstantiations；
- max_action_failures_per_goal；
- max_frame_verification_checks；
- max_reconstruction_repairs；
- max_requeues_per_state；
- max_recursive_substep_plans。

预算规则：

- action failure requeue 消耗 search round，但不能重复消耗同一个 action；
- binder re-instantiation 消耗 Lean check；
- frame verification 消耗 Lean check；
- final artifact verification 单独保留不可被前序耗尽的检查预算；
- synthesis provider 保留既有 reserved budget；
- 达到 budget 时返回 BUDGET_EXHAUSTED，不伪装为 BLOCKED。

## 16. 完成标准

本计划完成必须同时满足：

1. 生产 orchestrator 真实实例化并使用 SearchCoordinator；
2. theorem premise、data witness 和 generated capability 均能递归进入同一 GlobalProofFrontier；
3. action 失败后 state 带 failure memory 重新入队，其他 alternative 可继续；
4. ProofState fingerprint 能区分 attempted actions、binder substitutions 和 branch-local capabilities；
5. OpenGoal 不保存不可恢复的 unresolved Lean metavariable；
6. ApplicationFrame 能表达并验证 dependent theorem application；
7. frame saturated 后经过 Lean 局部验证，整树经过最终独立验证；
8. BLOCKED 只表示全局 frontier exhausted；
9. 子目标 synthesis 替代根目标整体 authoring；
10. forbidden dichotomy 的召回、源码和传递依赖审计继续生效；
11. 至少一个此前 BLOCKED 的真实 Boolean CSP case 通过非 dichotomy 递归路径 VERIFIED；
12. 完成 Boolean CSP 20 题真实 API 全量运行并生成独立报告；
13. 所有未验证 case 的 blocker 能定位到具体 goal、action、frame 或 capability gap；
14. 旧入口和旧 benchmark 协议不回归。

## 17. 立即执行顺序

1. 完成失败回队、attempted action 和 BLOCKED 语义；
2. 完成 ApplicationFrame、stable binder slot 和 dependent premise 激活；
3. 完成统一 Recursive Action Executor；
4. 完成局部 frame 验证与整树 reconstruction；
5. 将 SearchCoordinator 接入生产 orchestrator；
6. 运行 model-disabled theorem recursion synthetic/integration tests；
7. 迁移为子目标级 model synthesis；
8. 完成一个真实 API 单 case 纵向验证；
9. 完成 Boolean CSP 非 dichotomy 真实 case；
10. 完成 Boolean CSP 20 题真实 API 全量回归；
11. 根据明确 capability gap 再决定是否进入新的 library theorem、domain plugin 或模型能力计划。

本轮的核心判据是：

> 一个局部 action 失败后，Agent 仍能携带正确的绑定、失败记忆和已验证 fragments 返回全局搜索；只有所有 ProofState 和所有 alternative 都被真实耗尽后，才允许报告 BLOCKED。
