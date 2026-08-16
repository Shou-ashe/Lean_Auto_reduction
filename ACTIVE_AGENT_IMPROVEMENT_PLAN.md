# 通用自动归约 Agent：Planner-Guided Capability Generation 实施计划

> 状态：Active
>
> 更新日期：2026-08-15
>
> 当前唯一实施主线：保留并强化 LLM Planner 对 theorem、action、design 和证明路线的判断能力，同时建立独立的 Gadget、direct-TM、semantic Generator，使 Agent 能在库内缺失相应 capability 时生成新的 Lean 定义、程序、witness、invariant 和证明，而不是退化为只会召回现有定理的搜索器。

## 0. 文档范围

本文件取代此前以 Strategy 接线、StructuralActionProvider、ContextCapsule、stateful repair 和 finite gadget 插件为主要待办的旧计划。

这些基础设施目前已经全部或部分进入生产路径：

- 全局递归搜索和 GlobalProofFrontier 已经工作；
- theorem application 可以形成 ApplicationFrame；
- dependent data binder 可以绑定、重新实例化和回溯；
- StrategyDecision 已经能够映射到 action 或 design；
- stateful initial authoring 和 repair 协议已经存在；
- generated capability 可以通过 Lean 后回注 ProofState；
- proof-producing Boolean CSP finite gadget 插件已经存在；
- final artifact 继续经过独立 Lean、kernel、axiom、endpoint 和 forbidden dependency 审计；
- direct-TM 与 semantic 已经具有可复现的独立能力门禁和 20 题真实 API 报告。

因此，下一阶段不再重复建设上述接线，而是解决以下核心问题：

1. Planner 目前只能选择 action 或 design，不能输出面向独立 Generator 的完整能力构造方案；
2. ContextCapsule 声明了环境 grounding 结构，但 direct-TM 和 semantic 目标实际得到的构造知识为空；
3. 临时 RuleInstantiationProbe 声明会泄漏到后续独立生成文件；
4. synthesis budget 会被不可执行 design 和上游子步骤耗尽；
5. Gadget Generator 仍依赖有限的命名识别和固定模板集合；
6. direct-TM 尚无程序 DAG、primitive coverage 和节点级生成器；
7. semantic 尚无 witness transformation、invariant 和方向级 helper DAG；
8. 报告虽然能区分 reuse 和 generated capability，但还不能精确说明 Planner、Generator、deterministic solver 和已有 theorem 各自贡献了什么。

本计划的目标不是禁止现有 theorem，而是建立清晰的混合能力：

- 库内已有 theorem 时，Planner 可以直接选择并快速结束子步骤；
- theorem 留下 residual obligations 时，Planner 可以把 theorem 作为 scaffold，并给 Generator 提供证明建议；
- 库内缺失 capability 时，Planner 必须形成可执行构造计划，由独立 Generator 生成新 artifact；
- 所有结果都必须由 Lean 验证，并在报告中准确归因。

## 1. 当前基线与证据

### 1.1 已完成的 Gadget 能力

当前 Boolean CSP finite gadget 路径已经能够：

- 识别一部分 LanguageInterpretation 和 pointwise Gadget 目标；
- 枚举有限 pp-formula 候选；
- 对完整 Boolean truth table 做可执行检查；
- materialize Lean Spec；
- 使用 Spec.toGadget 把有限 certificate 提升为正式 Gadget；
- 将 Lean-verified Gadget 或 LanguageInterpretation 注册为 generated capability；
- 在禁用 CanonicalDatabase.gadget 和 canonical closure theorem 时继续工作。

但当前实现仍有明显限制：

- agent/generative_reduction/plugins/boolean_csp.py 通过若干已知 hard-core 名称识别 source；
- Lean 侧 defaultSpecs 主要由固定 templates 驱动；
- Planner 没有真正决定 witness grammar、变量界、约束界和 CEGIS 策略；
- Generator 没有从任意 finite Gamma 的 relation table 动态产生搜索空间；
- generated gadget 虽然能通过 Lean，但其后 direct-TM 或 semantic 失败时，最终 artifact 无法完成。

### 1.2 direct-TM 独立门禁

权威报告：

    Reports/GENERAL_AGENT_BOOLEAN_CSP_DIRECT_TM_GATE_REAL_API_REPORT.json

设置：

- 保留 semantic library theorem；
- 禁止现有 direct-TM closure theorem 和相关自动 transport wrapper；
- 同时保持 CanonicalDatabase.gadget 及两个 canonical closure theorem 的禁用；
- 使用真实 DeepSeek API；
- 执行 Boolean CSP benchmark 20 题。

结果：

- 20/20 case 有终态；
- 3 个 VERIFIED，均为完整证明复用控制组；
- 17 个 BUDGET_EXHAUSTED；
- 293 次真实 API 调用，293 次 HTTP 200；
- 17/17 个非复用 case 到达精确 TMPolyTimeMap 子目标；
- 0 个目标形状 direct-TM capability 被生成、注册并由最终 artifact 使用；
- 0 forbidden direct/transitive dependency。

进一步审计：

- direct-TM 目标相关 ContextCapsule 共 53 个；
- 53/53 的 candidate_signatures 为空；
- 53/53 的 relevant_lemmas 为空；
- token_estimate 只有约 150 到 162；
- 17 个 case 虽然都到达目标，但只有 8 个 case 真正获得 target-specific authoring design；
- 其余 case 在 gadget、interpretation 或其他上游 design 上耗尽全局 synthesis_designs；
- direct-TM 目标 design 中约一半是没有 residual goal 的 helper-first design，创建后立即废弃；
- 常见候选错误包括把 interpret 函数当作 TM proof、猜测不存在的 toTMPolyTimeMap、polyTime、interpretation_to_poly_time_map 等接口。

结论：

当前测试证明端到端 Agent 尚不具备 direct-TM 生成能力，但失败同时包含：

- 构造知识缺失；
- dependent handle 不稳定；
- Planner 设计不足；
- design budget 调度错误；
- Generator 本身的程序证明能力不足。

不能把全部失败归因于底层模型。

### 1.3 semantic 独立门禁

权威报告：

    Reports/GENERAL_AGENT_BOOLEAN_CSP_SEMANTIC_GATE_REAL_API_REPORT.json

设置：

- 保留 direct-TM library theorem；
- 禁止完整 satisfiable iff、formula-level forward、formula-level reverse closure theorem 和相关 transport wrapper；
- 同时保持 CanonicalDatabase.gadget 及两个 canonical closure theorem 的禁用；
- 使用真实 DeepSeek API；
- 执行 Boolean CSP benchmark 20 题。

结果：

- 20/20 case 有终态；
- 3 个 VERIFIED，均为完整证明复用控制组；
- 17 个 BUDGET_EXHAUSTED；
- 267 次真实 API 调用；
- 266 次 HTTP 200；
- 17/17 个非复用 case 到达精确 semantic iff 子目标；
- 0 个目标形状 semantic capability 被生成、注册并由最终 artifact 使用；
- 0 forbidden direct/transitive dependency。

进一步审计：

- semantic 目标相关 ContextCapsule 共 94 个；
- 94/94 的 candidate_signatures 为空；
- 94/94 的 relevant_lemmas 为空；
- token_estimate 只有约 164 到 186；
- 17/17 case 都获得 target-specific authoring；
- 86 个 semantic 目标 design 中，43 个 theorem-composition design 因没有 residual helper goal 而立即废弃；
- 43 个 direct-authoring design 中，大量失败来自遗漏 frozen declaration、临时 probe 名称、协议截断、forbidden source 和不存在的 structure field；
- 只有少部分失败真正到达具体的 semantic Lean residual goal。

结论：

semantic 当前更接近“Planner 和 grounding 没有给 Generator 形成可执行证明设计”，而不是经过充分条件后仍无法生成。

### 1.4 当前最小问题陈述

当前 Agent 已经能够找到数学瓶颈，也能在部分场景生成 gadget 和辅助声明。

真正缺少的是：

> 把一个被识别出的 capability gap 转换成一个可执行、类型化、可修复、可回溯的 Planner→Generator 合同，并按 capability 的语义结构生成新的 Lean artifact。

## 2. 核心术语与贡献分类

### 2.1 theorem 候选角色

不要用主观的“高层”或“低层”决定 theorem 是否可用，而应根据它对当前 exact goal 的 Lean 行为分类。

#### Exact closure

一个 theorem 实例化后直接得到当前 exact goal，且没有 residual obligations。

例如在未屏蔽时：

    interpretation_tmPolyTime interpretation

可以直接关闭 direct-TM 目标。

处理方式：

- Planner 应优先选择；
- 由 deterministic theorem executor 直接 materialize；
- 一般不需要调用 Generator LLM；
- 结果归类为 THEOREM_REUSE。

#### Conditional closure / scaffold

一个 theorem 可以得到当前 exact goal，但实例化后留下实质性 residual obligations。

例如显式 NP-hardness packaging theorem可以留下：

- LanguageInterpretation；
- direct-TM；
- semantic iff。

处理方式：

- Planner 可以选择并给出 theorem application plan；
- ApplicationFrame 管理 residual obligations；
- 已有 premise 由 theorem search、reuse 或 solver 关闭；
- 缺失 premise 分别拉起对应 Generator；
- 结果归类为 THEOREM_GUIDED_GENERATION 或 THEOREM_COMPOSITION。

#### Primitive

只提供局部构造能力或局部规律的 declaration，例如：

- structure constructor；
- Gadget.correct；
- TMPolyTimeMap.comp；
- map、fold、flatten、encoding primitive；
- membership、assignment agreement、finite certificate theorem。

处理方式：

- Planner 可以排序并推荐；
- Generator 可以调用；
- 它们是构造基础，不是完整答案。

#### Verified example

与当前目标结构相似、但不直接闭合目标的已验证例子。

处理方式：

- 只能在明确的 example policy 下提供；
- 必须通过 dependency 和 answer-leak audit；
- 能省略时优先省略；
- 能提供 type/outline 时，不直接提供完整 proof body；
- 能否使用由运行模式决定。

### 2.2 最终结果分类

报告至少区分：

- THEOREM_REUSE：现有 exact closure 直接关闭目标；
- THEOREM_COMPOSITION：只组合已有高层 theorem，没有新 substantive helper；
- THEOREM_GUIDED_GENERATION：Planner 使用 scaffold，Generator 补齐 residual capability；
- GENERATED_GLUE：生成了新的证明 glue，但没有新的计算对象或 witness；
- GENERATED_CAPABILITY：生成了新的程序、witness、interpretation、invariant 或 substantive helper，并由最终 artifact 实际使用；
- DETERMINISTIC_GENERATED_CAPABILITY：新 capability 由 enumerator、compiler 或 solver 生成，未依赖 LLM authoring；
- MODEL_GENERATED_CAPABILITY：新 capability 的结构或实现由 Generator LLM 产生；
- HYBRID_GENERATED_CAPABILITY：Planner LLM、Generator LLM 和 deterministic solver 共同产生。

生产 Agent 允许所有合法类型。

能力测试只有明确要求的生成类别计为成功，不能把 THEOREM_REUSE 计为 GENERATED_CAPABILITY。

## 3. 运行模式

### 3.1 production-hybrid

目标是最快、最可靠地完成用户请求。

默认顺序：

1. exact closure；
2. verified reuse；
3. conditional closure / scaffold；
4. structural action；
5. deterministic solver/plugin；
6. Planner-guided Generator；
7. direct authoring fallback。

如果库内已有 direct-TM、semantic 或 gadget theorem，应直接使用。

### 3.2 capability-gate

目标是测试某一项 capability generation。

规则：

- 只屏蔽当前能力的 exact closure、near-exact closure、alias 和自动 transport；
- 保留能够暴露该能力 exact child goal 的 scaffold；
- 保留 lower-level primitive；
- 保留其他独立能力的 theorem；
- final artifact 做 direct/transitive forbidden dependency audit；
- exact closure 控制组不计入 generation success。

例子：

- direct-TM gate：屏蔽 interpretation_tmPolyTime，保留 semantic；
- semantic gate：屏蔽 iff、forward、reverse closure，保留 direct-TM；
- gadget gate：屏蔽完整 gadget/interpretation closure，保留 Gadget.mk、finite semantics 和 certificate primitive。

### 3.3 from-basis

目标是研究 Generator 从较低抽象层构造 capability 的能力。

规则：

- 不提供 exact closure；
- 不提供 near-identical proof body；
- 只提供 definitions、constructors、primitive contracts 和显式允许的 scaffold；
- Planner 仍可以对这些候选排序并给出证明建议；
- Generator 必须产生新的 substantive artifact。

该模式不是默认生产模式，只用于能力研究和更严格的 held-out 测试。

## 4. 目标架构

整体流程：

    OpenGoal
      → Lean Typed Discovery
      → Deterministic Exact Closure
      → Planner LLM
          ├─ select exact theorem application
          ├─ select scaffold and residual DAG
          ├─ select deterministic plugin/compiler
          └─ produce CapabilityPlan + GeneratorBrief
      → Action/ApplicationFrame/SynthesisDesign
      → Independent Generator
      → Lean materialization
      → diagnostic-driven repair or planner replan
      → generated capability registration
      → GlobalProofFrontier
      → final reconstruction and audit

### 4.1 Planner LLM 的职责

Planner 负责：

- 对 theorem、reuse、plugin、structural action 和 synthesis design 排序；
- 选择 source core、theorem route 和 construction mode；
- 判断 theorem 是 exact closure、scaffold 还是 primitive；
- 选择要交给 Generator 的 typed basis；
- 给 Generator 提供有顺序的 proof advice；
- 提议 helper role 和 exact type；
- 提议 witness schema、program decomposition 或 semantic invariant；
- 在 repair、switch-design 和 backtrack 之间做选择；
- 根据 diagnostics、counterexamples、历史成功率和预算重新规划；
- 请求额外 lookup 或 definition expansion。

Planner 不负责：

- 声明 proof 已经正确；
- 返回未经 Lean 验证的成功结论；
- 通过自由文本发明一个可直接执行的 theorem 名称；
- 绕过 forbidden declaration；
- 把自然语言建议直接写入 ProofState；
- 在 Generator 失败后静默改变 frozen plan。

### 4.2 Independent Generator 的职责

Generator 以新模型调用、独立上下文和冻结的 GeneratorBrief 启动。

Generator 负责：

- 生成新的 Lean declaration body；
- 生成新 witness、program、helper、invariant 或 proof glue；
- 调用 Planner 选定的 theorem/primitive；
- 对同一 design 根据 Lean diagnostics 做局部 repair；
- 返回 plan-infeasible，要求 Planner 重新规划；
- 明确报告实际使用的 planner advice 和 declaration IDs。

Generator 不应看到：

- 不属于当前 plan 的完整 theorem index；
- 被 capability gate 禁止的 theorem body；
- benchmark oracle；
- case-specific 答案；
- Planner 的隐藏推理文本；
- 与当前 design 无关的完整模块源码。

### 4.3 Deterministic executor 的职责

以下工作不需要浪费 Generator LLM：

- exact closure theorem application；
- structure constructor 的机械组装；
- ApplicationFrame 重建；
- 已知 primitive 的机械 composition；
- finite candidate 的 executable checking；
- Lean command 执行；
- proof dependency 和 forbidden audit；
- fixed declaration envelope；
- schema repair；
- stable handle canonicalization。

如果统一接口要求经过 Generator 层，也应使用 deterministic materializer，而不是调用模型。

### 4.4 不建立平行 frontier

Gadget、direct-TM 和 semantic Generator 都是现有 GlobalProofFrontier 中的 capability-specific SynthesisDesign executor。

它们不能：

- 各自维护与主搜索无关的根目标；
- 绕过 ApplicationFrame；
- 绕过 failure memory；
- 绕过 global budget；
- 绕过 capability registration；
- 绕过 final reconstruction。

“独立拉起 Generator”只表示新的模型上下文和冻结合同，不表示创建另一套证明搜索器。

## 5. 共享数据协议

### 5.1 CandidateReceipt

新增或扩展：

    CandidateReceipt
      candidate_id
      declaration
      exact_type
      module
      declaration_kind
      candidate_role
      exact_closure
      residual_obligations
      application_skeleton
      dependency_distance
      forbidden_status
      historical_success
      estimated_cost

candidate_role 取值：

- exact-closure；
- conditional-closure；
- scaffold；
- primitive；
- constructor；
- verified-example。

候选角色必须由 Lean application receipt 和 residual obligations 决定，不能只靠名称。

### 5.2 TheoremApplicationPlan

    TheoremApplicationPlan
      plan_id
      candidate_id
      exact_instantiation
      application_skeleton
      solved_premises
      residual_obligations
      expected_result_type
      contribution_class
      forbidden_receipt

如果 residual obligations 为空，直接交 deterministic executor。

如果不为空，创建 ApplicationFrame。

### 5.3 CapabilityPlan

    CapabilityPlan
      plan_id
      capability_kind
      goal_id
      exact_goal
      selected_route
      selected_action_id
      selected_design_id
      selected_candidate_ids
      construction_basis_ids
      forbidden_closure_ids
      proof_outline
      helper_specs
      witness_schema
      residual_goal_dag
      budget_allocation
      fallback_plans
      context_requirements
      plan_fingerprint

capability_kind 至少支持：

- gadget；
- language-interpretation；
- direct-tm；
- semantic；
- final-packaging；
- generic-helper。

### 5.4 GeneratorBrief

    GeneratorBrief
      brief_id
      plan_id
      exact_declaration_name
      exact_declaration_type
      fixed_declaration_envelope
      selected_design
      selected_candidate_ids
      ordered_proof_hints
      helper_contracts
      witness_contract
      expected_residuals
      allowed_identifier_manifest
      forbidden_declarations
      generated_capability_signatures
      local_context
      relevant_definitions
      prior_counterexamples
      prior_diagnostics
      failed_source_hashes
      brief_fingerprint

proof hint 至少支持：

- apply-candidate；
- unfold-definition；
- introduce-helper；
- construct-witness；
- split-structurally；
- prove-endpoint-equality；
- request-lookup；
- avoid-failed-pattern。

如果 hint 引用 theorem，必须引用 candidate_id。

自然语言建议可以存在，但不能代替 typed ID 和 exact type。

### 5.5 GeneratorResult

    GeneratorResult
      result_id
      brief_id
      status
      implementation_body
      helper_declarations
      used_candidate_ids
      used_generated_capabilities
      planner_hints_followed
      planner_hints_rejected
      rejection_reason
      requested_lookup
      requested_replan
      implementation_hash

status 至少支持：

- proposed；
- plan-infeasible；
- needs-lookup；
- needs-replan；
- protocol-invalid。

### 5.6 ContributionReceipt

    ContributionReceipt
      capability_declaration
      contribution_class
      exact_closure_candidates_used
      scaffold_candidates_used
      primitive_candidates_used
      planner_advice_ids
      generated_helpers
      generated_data_objects
      deterministic_solver_steps
      model_generated_source_hashes
      final_artifact_used
      forbidden_audit_passed
      independent_lean_passed

报告必须能够回答：

- Planner 选择了什么；
- Generator 新生成了什么；
- 哪些已有 theorem 被直接调用；
- 哪些已有 theorem 只是 primitive；
- 新 capability 是否被最终 artifact 使用。

## 6. 共享基础设施改进

### 6.1 构造知识检索，而不是无边界答案检索

当前 theorem index 主要检索可以直接统一当前 conclusion head 的 declaration。

新增 construction-basis discovery：

1. 提取 exact goal 中全部 constants；
2. 提取目标函数和目标 predicate 的 definition；
3. 提取 constructor 和 structure fields；
4. 检索引用这些 constants 的 declaration；
5. 检索 Planner 已选 candidate 的 premise dependencies；
6. 检索 diagnostics 中 unknown/invalid field 的真实声明；
7. 建立一到两层 typed dependency neighborhood；
8. 根据 candidate role、dependency distance 和 token budget 排序。

限制：

- production-hybrid 可以召回 exact closure；
- capability-gate 将被禁 closure 从 executable candidates 中删除；
- Generator 只收到 Planner 选定的 construction basis；
- 不把完整 theorem index 或完整模块源码发送给模型。

### 6.2 完成 ContextCapsule

当前 ContextCapsule 中以下字段不能继续固定为空：

- goal_head_type；
- goal_head_definition；
- relevant_definitions；
- relevant_lemmas；
- constructors；
- verified_examples；
- application_skeletons。

新增强制门禁：

如果一个非平凡 generation goal 的 capsule 同时满足：

- candidate_signatures 为空；
- relevant_definitions 为空；
- constructors 为空；
- application_skeletons 为空；

则禁止调用 Generator，必须先：

- expand context；
- request lookup；
- 或返回 context-insufficient blocker。

不能继续在只有 150 到 180 token 构造知识的情况下消耗大模型调用。

### 6.3 稳定 dependent handle

当前 RuleInstantiationProbe 可能创建：

    RuleInstantiationProbe.N...bound3
    RuleInstantiationProbe.N...bound4

这些声明只存在于 probe 文件，不能进入独立生成文件的 exact goal。

修复要求：

1. 已有 fragment.declaration 且 Lean 证明其 exact type 匹配时，优先使用稳定 declaration；
2. 不再通过 proof_term 文本是否等于 declaration 决定稳定绑定；
3. 如果 proof term 需要 eta-expansion，生成 job-local stable wrapper；
4. dependent sibling 的 exact type 必须使用 stable declaration 重新 elaboration；
5. Generator 调用前运行 resolvable-constant audit；
6. exact goal 中出现 RuleInstantiationProbe namespace 时禁止 authoring。

### 6.4 固定 declaration envelope

runtime 负责生成：

    noncomputable def capability_x : ExactType := by
      <generator body>

Generator 默认只返回 proof body 或显式 helper declarations 加 proof body。

不再要求模型每轮重复：

- exact declaration name；
- exact type；
- namespace；
- frozen source/target；
- 固定 wrapper。

这将消除大量 omitted frozen declaration 和 editable fence 失败。

### 6.5 allowed identifier manifest

GeneratorBrief 提供动态白名单：

- Lean core syntax 和标准构造器；
- local context identifiers；
- Planner 选择的 candidate declarations；
- selected primitive；
- generated capability declarations；
- diagnostics expansion 后新增的合法声明。

Generator 可以提出 request-lookup，但不能直接使用未解析的猜测名称。

source fence 在 Lean 前先做 identifier audit：

- 未在 manifest 中的完整 qualified name 触发 needs-lookup；
- forbidden name 立即拒绝；
- 已知不存在的 field 不再次进入 Lean；
- lookup 扩充后才能继续 repair。

### 6.6 design 预验证和预算隔离

当前不可执行 helper-first 或 theorem-composition design 会先写入并消耗 synthesis_designs。

改进：

- 没有 residual helper goal 时，不生成 helper-first design；
- 没有 selected theorem application 时，不生成 theorem-composition design；
- constructor-first 只有 StructuralActionProvider 确认构造器可用时才创建；
- finite design 只有 plugin support receipt 通过时才创建；
- direct-authoring 只有 context-ready 后才计入 materialization budget；
- 只有 materializable design 计入 synthesis_designs；
- budget 超限事件不能先写入第 N+1 个 design 再报错。

预算从全 case 单一计数改为：

    case budget
      → route budget
      → capability budget
      → design budget
      → repair budget

每个已激活的关键能力至少保留：

- 一次 Planner decision；
- 一个 executable design；
- 一次 initial generation；
- 一次 Lean check；
- 一次 diagnostic-driven repair；
- final verification reserve。

### 6.7 repair 与 replan 分离

同一 Generator repair：

- parser error；
- 局部 unknown identifier，在 lookup 后可修；
- type mismatch；
- invalid field；
- 一个局部 unsolved goal；
- declaration envelope 内的小范围错误；
- schema 或输出格式错误。

返回 Planner replan：

- witness 被 counterexample 推翻；
- program DAG 缺失关键 primitive；
- endpoint equality 说明当前分解错误；
- 同一 diagnostic 重复；
- helper role 不足以关闭 parent；
- forbidden dependency；
- design cost 超出剩余预算；
- Generator 明确返回 plan-infeasible。

Generator 不得在 repair 中静默：

- 更换 source core；
- 更换 theorem route；
- 更换 witness schema；
- 更换 direct-TM program decomposition；
- 更换 semantic direction strategy。

这些必须回到 Planner 并形成新的 plan_id。

### 6.8 模型协议可靠性

- Strategy 和 Generator 使用独立 schema；
- schema repair 与数学 generation 分离；
- schema repair 不创建新的数学 design；
- stale base hash 由 runtime request binding 保证，不要求模型承担并发一致性；
- response hash 和 request ID 由 runtime 记录；
- finish_reason=length 时缩小任务、减少输出范围或拆分 helper；
- transport failure 至少允许一次有界 retry；
- retry 不重置 repair lineage；
- Planner 和 Generator 使用独立模型预算。

## 7. Root Route Planner

Root Planner 负责选择整体 reduction route，而不是生成所有证明。

对 Boolean CSP hardness，典型 route：

    source hardness
      + LanguageInterpretation source target
      + direct-TM of interpret
      + semantic iff of interpret
      → explicit certified reduction
      → target NP-hardness

Planner 输入：

- root exact goal；
- 可用 source hard cores；
- source hardness closure；
- 每个 source 到 target 的 gadget constructibility；
- direct-TM 和 semantic capability 状态；
- forbidden declarations；
- 历史 branch 成本；
- 当前 generated capabilities。

Planner 输出：

- selected source；
- selected packaging scaffold；
- child capability DAG；
- child priority；
- 是否允许 direct-TM 和 semantic 在 interpretation 完成后并行进入 frontier；
- fallback source 顺序；
- 每个 capability 的初始 budget。

Root Planner 可以直接选择库内完整 NP-hardness theorem。

如果 production-hybrid 下 exact closure 可用，则立即结束。

如果 capability-gate 禁止该 closure，则必须选择显式 scaffold，暴露被测试子目标。

## 8. Gadget Planner + Generator

### 8.1 目标形状

至少支持：

    Gadget target relation

    (symbol : source.Symbol) →
      Gadget target (source.relationOf symbol)

    LanguageInterpretation source target

LanguageInterpretation packaging 本身优先由 structural constructor 完成。

真正需要 Generator 的核心是 pointwise Gadget。

### 8.2 Gadget Planner 输入

由 Lean reify：

- source Gamma 的 Symbol 是否 finite；
- 当前 source symbol；
- source relation arity；
- source relation 完整 truth table；
- target Gamma 的全部 symbols；
- 每个 target relation 的 arity 和 truth table；
- target semantics 是否 decidable；
- 可用 variable carrier；
- 已有 generated gadgets；
- 已有 primitive/certificate；
- previous candidates；
- accumulated counterexamples；
- finite search budget；
- forbidden gadget/interpretation closures。

不能使用：

- benchmark case ID；
- split 标签；
- oracle witness；
- Case02、NAE4、ExactlyTwo 等题目名称分支。

### 8.3 Gadget Planner 输出

新增 GadgetCapabilityPlan：

    GadgetCapabilityPlan
      source_relation_receipt
      target_gamma_receipt
      design_kind
      variable_bound
      constraint_bound
      witness_grammar
      output_schema
      symmetry_breaking
      seed_patterns
      selected_generated_gadgets
      selected_primitive_ids
      counterexample_policy
      enumeration_order
      fallback_designs

design_kind：

- existing-gadget-composition；
- constructor-first；
- finite-enumeration；
- cegis-finite-spec；
- symbolic-formula；
- direct-authoring。

Planner LLM 可以：

- 根据 relation table 识别 symmetry、complement、cardinality 特征；
- 决定是否优先 repeated-variable constraint；
- 决定是否需要 auxiliary variables；
- 推荐 output mapping；
- 推荐先组合已有 gadget 还是重新搜索；
- 根据 counterexample 修改 grammar；
- 给 Generator 解释候选 formula 应满足什么。

Planner 不直接声明某个 formula 正确。

### 8.4 Gadget Generator

#### finite-enumeration

deterministic enumerator 按 Planner 给定 grammar 搜索：

- constraint 数；
- auxiliary variable 数；
- relation symbol；
- argument projection；
- argument permutation；
- repeated variables；
- formula conjunction；
- output mapping。

先运行 executable semantics，只有通过完整 truth table 的候选才 materialize Lean。

#### cegis-finite-spec

Independent Generator LLM 提出：

- FiniteFormula；
- outputs；
- auxiliary layout；
- formula shape rationale。

checker 返回：

- source tuple；
- expected source relation value；
- 当前 formula satisfiability；
- 必要时给出 target assignment 或不存在 witness 的 receipt。

下一轮 Generator 必须满足累计 counterexamples。

#### symbolic-formula

Generator 产生：

- formula definition；
- output definition；
- injectivity proof；
- correctness helper DAG。

该模式只在 finite checking 不适用或 grammar 太大时启用。

### 8.5 Lean materialization

优先路径：

    generated Spec
      + executable full-table receipt
      + Lean proof of Spec.Correct
      → Spec.toGadget

Python 或 LLM 的 executable check 不能替代 Lean proof。

Lean materializer 必须输出：

- exact Gadget declaration；
- candidate source hash；
- truth-table certificate receipt；
- no-placeholder receipt；
- dependency audit。

### 8.6 当前实现改进

修改 agent/generative_reduction/plugins/boolean_csp.py：

- 删除仅通过已知 hard-core 名称决定支持性的核心依赖；
- 从 Lean reification receipt 读取任意 finite Gamma；
- 将固定 templates 降级为 seed_patterns；
- Planner 动态控制 bound 和 grammar；
- 支持多轮 CEGIS；
- 每个 counterexample 持久化；
- 支持已有 generated gadget composition；
- plugin action metadata 引用 GadgetCapabilityPlan。

扩展 Lean/Reference/ComplexityReduction/Agent/GenerativeReduction/Plugins/BooleanCSPFiniteGadget.lean：

- 通用 finite Gamma reification receipt；
- parameterized variableCount；
- parameterized grammar materialization；
- candidate certificate；
- counterexample rendering；
- 任意 finite symbol list；
- 不把默认模板作为唯一入口。

### 8.7 Gadget feedback

同 design repair：

- formula Lean syntax；
- output index 类型；
- injectivity proof；
- materializer 错误。

Planner replan：

- truth-table counterexample；
- search bound exhausted；
- grammar 无法表达 relation；
- auxiliary variable bound 不足；
- 当前 target Gamma 不支持 finite reification；
- composition route 循环。

### 8.8 Gadget 成功判据

- 生成新 formula 或组合结构；
- 完整 finite semantics 通过；
- Lean Spec.Correct 通过；
- Gadget exact type 通过；
- capability 注册；
- parent LanguageInterpretation 使用；
- final artifact 使用；
- 0 forbidden dependency。

只调用已有完整 Gadget theorem 时归类为 THEOREM_REUSE。

## 9. LanguageInterpretation 组装

LanguageInterpretation 是 Gadget 与后续两项能力之间的稳定边界。

默认不需要独立 Generator LLM。

执行：

1. StructuralActionProvider 应用 LanguageInterpretation.mk；
2. intro source symbol；
3. 对每个 symbol 激活 pointwise Gadget child goal；
4. exact closure、reuse、generated gadget 分别关闭 child；
5. ApplicationFrame 重建完整 interpretation；
6. 注册稳定 declaration；
7. 后续 direct-TM 和 semantic exact goal 只引用稳定 declaration。

只有以下情况才调用 Generator：

- symbol dependent pattern 需要非平凡 matching；
- source.Symbol 不是有限可枚举类型；
- pointwise gadget 需要共享新的 helper；
- structural reconstruction 暴露真实 Lean gap。

成功判据：

- declaration stable；
- 无 RuleInstantiationProbe handle；
- direct-TM 和 semantic 都能引用同一 declaration；
- interpretation 是 final artifact 的真实依赖。

## 10. direct-TM Planner + Generator

### 10.1 目标形状

核心目标：

    TMPolyTimeMap sourceEncoded targetEncoded function

在 Boolean CSP gate 中：

    function = interpret interpretation

direct-TM 的真正生成对象不是一句 theorem application，而是：

- 一个程序分解；
- 每个节点的 polynomial-time proof；
- 节点 composition；
- 编码转换；
- 最终 endpoint equality。

### 10.2 direct-TM Planner 输入

必须包含：

- source EncodedType；
- target EncodedType；
- target function 的完整 type；
- target function 的按需 definition expansion；
- encoding 和 decoding declarations；
- 已有 TMPolyTimeMap primitives；
- composition、map、fold、flatten、pair、projection 等通用 combinators；
- 已有 generated helpers；
- exact closure 和 forbidden status；
- prior program DAG；
- node-level diagnostics；
- endpoint equality diagnostics；
- budget。

不能只提供：

- exact goal；
- interpretation signature；
- 完整 import 列表。

### 10.3 Program IR

新增通用 TypedProgramNode：

    TypedProgramNode
      node_id
      operation
      input_type
      output_type
      function_term
      child_node_ids
      candidate_primitive_ids
      coverage_status
      residual_tm_goal
      residual_equality_goal
      estimated_cost

operation 至少支持：

- identity；
- constant；
- composition；
- pair；
- projection；
- map；
- flatMap；
- fold；
- append；
- flatten；
- branch；
- encoding equivalence；
- code-to-structure；
- user-defined-helper。

新增 DirectTMCapabilityPlan：

    DirectTMCapabilityPlan
      source_encoding
      target_encoding
      target_function
      normalized_program_dag
      selected_primitive_ids
      covered_nodes
      nodes_to_generate
      endpoint_equality_plan
      size_or_runtime_obligations
      helper_specs
      composition_order
      fallback_dags

### 10.4 direct-TM Planner 的作用

Planner LLM 可以：

- 决定在 formula 层还是 code 层证明；
- 对多个 definition expansion 选择最适合 TM primitives 的表示；
- 选择 program DAG 的 stage boundaries；
- 排序 TMPolyTimeMap.comp、map、flatten、encoding 等候选；
- 建议先生成哪个 helper；
- 识别某个节点需要新 executable helper；
- 识别 endpoint equality 应单独生成；
- 根据 diagnostics 换 DAG；
- 根据预算在短但难的直接证明与长但结构化的节点证明之间选择。

Planner 输出的 theorem 建议必须引用 candidate_id。

Planner 可以在 production-hybrid 下直接选择 interpretation_tmPolyTime。

在 direct-TM capability-gate 中，该 exact closure 不可执行，Planner 必须选择 lower-level DAG。

### 10.5 direct-TM Generator

Generator 每次只处理一个：

- uncovered program node；
- missing TM primitive instance；
- endpoint equality；
- small composition group。

GeneratorBrief 示例内容：

    exact node goal
    node operation
    child node capabilities
    selected primitive signatures
    function definition
    expected composition skeleton
    endpoint obligation
    forbidden closures

Generator 可以产生：

- 新 executable helper；
- 新 TMPolyTimeMap helper；
- composition proof；
- conversion proof；
- extensional equality；
- 必要的 map/fold invariant。

不能让 Generator 每次从整个 NP-hardness 根目标重新开始。

### 10.6 deterministic TM compiler

新增 typed compiler：

    normalized Program DAG
      + node capability map
      → Lean composition source

compiler 负责机械部分：

- TMPolyTimeMap.comp；
- type-aligned node wiring；
- child proof substitution；
- stable helper declarations；
- final composition；
- exact endpoint check。

贡献分类：

- 所有节点已存在，只机械 composition：THEOREM_COMPOSITION；
- compiler 从一般 expression 自动产生新 theorem：DETERMINISTIC_GENERATED_CAPABILITY；
- LLM 生成新 helper/DAG/equality：MODEL 或 HYBRID GENERATED_CAPABILITY。

### 10.7 direct-TM repair 与 replan

同 Generator repair：

- 一个 node 的 type mismatch；
- primitive application 参数错误；
- 局部 endpoint simp 失败；
- missing import 已由 manifest 发现；
- composition 顺序错误。

Planner replan：

- target definition 无法映射到当前 DAG；
- 多个节点缺失同一种 primitive；
- endpoint equality 表明 normalization 不正确；
- 当前 code-level route 比 formula-level route更困难；
- repeated unknown field/theorem；
- node budget 超限。

### 10.8 direct-TM 成功判据

- 17 个有效 gate case 都获得 target-specific DirectTMCapabilityPlan；
- 不再出现到达目标但未分配 target authoring 的 case；
- 每个 plan 至少一个 executable DAG；
- 所有 node exact type 可解析；
- final TMPolyTimeMap kernel verified；
- 不是被禁 theorem 的 alias；
- generated node/helper 被 final theorem 使用；
- final artifact 使用 direct-TM capability；
- 0 forbidden dependency。

## 11. semantic Planner + Generator

### 11.1 目标形状

核心目标：

    ∀ formula,
      Satisfiable (interpret interpretation formula)
        ↔ Satisfiable formula

semantic capability 由两个方向组成：

- target assignment → source satisfaction；
- source assignment → target witness。

真正困难的部分是：

- witness transformation；
- source-variable agreement；
- fresh auxiliary variable consistency；
- instantiated gadget correctness；
- constraint-to-formula lifting。

### 11.2 通用 structural decomposition

在调用 semantic Planner 前，deterministic structural provider 应优先形成：

    intro formula
    constructor

必要时继续展开：

    intro satisfiable witness
    rcases witness with assignment, satisfies

但 structural provider 不能擅自选择 semantic witness。

选择 witness 和 invariant 属于 Planner 与 Generator。

### 11.3 semantic Planner 输入

必须包含：

- Formula.Satisfiable definition；
- Formula.Satisfies definition；
- interpret definition；
- instantiate definition；
- Gadget structure 和 Gadget.correct；
- formula membership structure；
- constraint membership structure；
- source/target assignment type；
- 可用 lower-level semantic primitive；
- generated interpretation；
- prior witness schemas；
- prior counterexamples 或 unsolved goals；
- forbidden iff/forward/reverse closures；
- current local context。

### 11.4 SemanticCapabilityPlan

    SemanticCapabilityPlan
      formula_binder
      reverse_direction_plan
      forward_direction_plan
      selected_primitive_ids
      witness_schemas
      invariant_specs
      helper_dag
      structural_steps
      membership_decomposition
      fresh_variable_policy
      fallback_witnesses

每个 direction plan：

    SemanticDirectionPlan
      direction
      input_witness_type
      output_witness_schema
      transformation_helper
      local_invariants
      constraint_level_goal
      formula_level_goal
      selected_candidate_ids
      helper_specs

### 11.5 semantic Planner 的作用

Planner LLM 可以：

- 选择 reverse witness 是原 assignment、restriction 还是 projection；
- 选择 forward witness 的 fresh-variable 编码；
- 判断是否复用已有 assignment function 但重新证明其性质；
- 排序 Gadget.correct、instantiate-level primitive、membership theorem；
- 决定先证明 output agreement 还是 formula-level statement；
- 把一个大 Iff 规划为 helper DAG；
- 根据 unsolved goal 修改 invariant；
- 在 constraint induction、list membership decomposition 和直接逐约束证明之间选择；
- 给 Generator 说明两个方向如何共享 helper。

Planner 在 production-hybrid 下可以直接选择 interpret_satisfiable_iff。

在 semantic capability-gate 中，完整 iff、formula-level forward 和 formula-level reverse closure 不可执行，但 Planner 仍可推荐更低层 primitive。

### 11.6 semantic Generator

Generator 按 helper DAG 分阶段生成。

#### reverse direction

可能生成：

- assignment restriction/projection；
- one interpreted block implies source constraint；
- target formula satisfaction implies every source constraint；
- source satisfiable witness。

#### forward direction

可能生成：

- generatedForwardAssignment；
- source coordinate preservation；
- fresh auxiliary variable allocation；
- per-gadget witness selection；
- fresh assignments 之间的非冲突 invariant；
- one source constraint produces one satisfied target block；
- target formula satisfaction；
- target satisfiable witness。

#### final assembly

只有在两个 direction capability 都通过 Lean 后，才生成最终 Iff。

如果正向已经通过而反向失败，正向 capability 必须保留并回注 ProofState。

### 11.7 helper-first 的真实语义

semantic helper-first 不能再是没有 residual goal 的标签。

Planner 必须产生 exact helper specs，例如：

    helper role: source-coordinate-preservation
    exact type: ...
    consumed by: forward-constraint-proof

    helper role: interpreted-block-reverse
    exact type: ...
    consumed by: formula-reverse

这些 helper 作为普通 child goals 进入 GlobalProofFrontier。

如果 Planner 没有产生 helper exact type，则不创建 helper-first design。

### 11.8 semantic feedback

同 Generator repair：

- intro/rcases 结构错误；
- local binder 名称和类型；
- 一个 membership lemma application；
- witness exact type mismatch；
- 一个 constraint-level unsolved goal。

Planner replan：

- witness transformation 无法满足 invariant；
- fresh variables 冲突；
- direction helper DAG 缺边；
- 当前 decomposition 依赖被禁 closure；
- repeated same residual goal；
- formula-level proof需要新的 constraint primitive。

### 11.9 semantic 成功判据

- 17 个有效 gate case 都产生 SemanticCapabilityPlan；
- 94/94 空 context 的问题消失；
- 每个方向都有明确 witness schema；
- 至少一个 direction helper 由 Generator 新生成；
- 两个方向独立 Lean verified；
- final Iff 使用生成的 helpers；
- 不是现有 iff/forward/reverse theorem 的 alias；
- final artifact 使用 semantic capability；
- 0 forbidden dependency。

## 12. Final Packaging

当以下 capability 可用：

- source hardness；
- stable LanguageInterpretation；
- direct-TM；
- semantic iff；

final packaging 应由 deterministic scaffold 完成。

优先使用显式 packaging theorem：

    certifiedReduction_of_interpretation_explicit
    nPHard_of_interpretation_explicit

Planner 可以选择其他合法 scaffold。

final packaging 不应重新调用 Gadget、direct-TM 或 semantic Generator。

如果 packaging 失败，应报告：

- endpoint mismatch；
- interpretation declaration mismatch；
- direct-TM function 不同；
- semantic function 不同；
- source hardness endpoint 不同；
- forbidden dependency；
- reconstruction bug。

不能把 packaging 失败笼统记为 generation failure。

## 13. Planner 调用策略

### 13.1 必须调用 Planner 的情况

- 至少两个 executable theorem/action/design；
- exact closure 与 generation route 都合法，且需要成本/贡献权衡；
- 一个 scaffold 有多个 residual solving order；
- gadget 有多个 grammar/bound；
- direct-TM 有多个 program DAG；
- semantic 有多个 witness schema；
- repair 与 switch-design 之间需要选择；
- data witness 或 source core 需要回溯；
- 剩余预算不足以展开全部方案。

### 13.2 可以跳过 Planner 的情况

- 唯一 exact closure；
- 唯一 deterministic structural action；
- 唯一 plugin action，且没有失败历史；
- 当前 plan 已冻结，只需同 design repair；
- schema repair；
- deterministic final packaging。

### 13.3 Planner 输出的建议必须生效

每次 Planner 调用必须产生：

- selected action；
- selected theorem application；
- selected design；
- GeneratorBrief；
- request lookup；
- replan；
- 或 current-state backtrack。

新增 PlannerEffectReceipt：

    PlannerEffectReceipt
      plan_id
      selected_action_id
      selected_candidate_ids
      selected_design_id
      generated_brief_id
      applied_effect
      subsequent_event_id
      override_reason

要求：

- valid Planner proposal 不能被静默忽略；
- subsequent Generator 必须引用 brief_id；
- final report 能从 Planner decision 追踪到 generated declaration。

## 14. Generator 调用策略

### 14.1 独立上下文

每个 initial Generator call：

- 使用冻结 GeneratorBrief；
- 不继承 Planner 对话历史；
- 不继承其他 case 的模型上下文；
- 不包含 API credential；
- 不包含 oracle；
- 不包含未选择 theorem 候选；
- 不包含被禁 closure body。

### 14.2 生成粒度

Generator 默认只处理最小 substantive gap：

- 一个 Gadget Spec；
- 一个 program node；
- 一个 endpoint equality；
- 一个 semantic helper；
- 一个 witness transformation；
- 一个 invariant；
- 一个 direction proof。

禁止把整个 NP-hardness root 作为 direct authoring fallback，除非：

- 其他分解全部不可用；
- Planner 明确选择；
- context 完整；
- goal size 在限制内；
- report 标记为 monolithic fallback。

### 14.3 失败保留

已经 Lean-verified 的生成结果必须保留：

- gadget 成功后 direct-TM 失败，gadget 仍保留；
- semantic forward 成功后 reverse 失败，forward 仍保留；
- direct-TM node 成功后 endpoint equality 失败，node 仍保留；
- plan switch 复用所有 exact-type-compatible capability。

## 15. 报告与指标

### 15.1 通用字段

新增或明确：

- theorem_exact_closure_count；
- theorem_scaffold_count；
- theorem_primitive_count；
- planner_call_count；
- planner_plan_count；
- planner_brief_count；
- planner_advice_used_count；
- planner_advice_rejected_count；
- generator_initial_count；
- generator_repair_count；
- generator_replan_request_count；
- context_insufficient_count；
- unresolved_probe_handle_count；
- executable_design_count；
- rejected_nonexecutable_design_count；
- capability_contribution_receipts；
- generated_capability_final_used_count。

### 15.2 Gadget 字段

- gadget_plan_count；
- gadget_design_kind_counts；
- finite_candidate_count；
- truth_table_rejection_count；
- counterexample_count；
- bound_expansion_count；
- gadget_certificate_count；
- gadget_registered_count；
- gadget_final_used_count。

### 15.3 direct-TM 字段

- direct_tm_plan_count；
- program_dag_count；
- program_node_count；
- primitive_covered_node_count；
- generated_node_count；
- node_lean_success_count；
- endpoint_equality_attempt_count；
- endpoint_equality_success_count；
- direct_tm_registered_count；
- direct_tm_final_used_count。

### 15.4 semantic 字段

- semantic_plan_count；
- forward_plan_count；
- reverse_plan_count；
- witness_schema_count；
- semantic_helper_count；
- forward_helper_success_count；
- reverse_helper_success_count；
- semantic_iff_registered_count；
- semantic_iff_final_used_count。

### 15.5 强制一致性

要求：

    planner_plan_count
      = planner_brief_count
      + theorem_application_plan_count
      + planner_replan_count
      + planner_backtrack_count

    generated_capability_final_used_count
      ≤ registered_generated_capability_count
      ≤ lean_verified_generated_capability_count

每个 capability-gate success 必须有：

- target exact goal receipt；
- Planner plan；
- Generator 或 deterministic synthesis receipt；
- Lean receipt；
- contribution receipt；
- final-used receipt；
- forbidden dependency receipt。

## 16. 测试策略

### 16.1 Python unit

- candidate role classification；
- exact closure 与 scaffold 区分；
- Planner candidate ranking；
- Planner GeneratorBrief schema；
- invalid candidate ID rejection；
- request-lookup；
- context-insufficient gate；
- stable declaration rebinding；
- RuleInstantiationProbe handle rejection；
- non-executable design 不计预算；
- capability-scoped budget reserve；
- fixed declaration envelope；
- allowed identifier manifest；
- repair 与 replan 分流；
- contribution classification。

### 16.2 Lean synthetic

#### Shared

- exact closure zero residual；
- scaffold with dependent residuals；
- stable generated declaration进入 dependent sibling；
- unresolved probe handle 被拒绝；
- generated helper final-used；
- alias existing theorem 被识别为 reuse；
- forbidden transitive dependency rejection。

#### Gadget

- 任意 synthetic finite Gamma reification；
- 非预置 relation table；
- bounded finite search；
- counterexample-guided repair；
- generated Spec.toGadget；
- multiple source symbols；
- no benchmark name branch。

#### direct-TM

- simple composition DAG；
- map + flatten DAG；
- encoding equivalence；
- missing node generation；
- endpoint equality；
- wrong DAG replan；
- generated node reused in final TM theorem。

#### semantic

- generic Iff structural split；
- generated forward witness；
- generated reverse projection；
- constraint-level helper；
- formula-level lifting；
- forward success preserved after reverse failure；
- final Iff uses both generated directions。

### 16.3 Integration

- production exact theorem reuse；
- scaffold + one generated residual；
- Planner advice passed to independent Generator；
- Generator request lookup；
- Generator plan-infeasible triggers replan；
- gadget → interpretation → direct-TM → semantic → packaging；
- capability survives branch requeue/resume；
- source switch reuses compatible generated capability；
- complete contribution report。

### 16.4 防退化

- root fast path 不回归；
- theorem recursion 不回归；
- data binding backtrack 不回归；
- exact closure 在 production 模式仍优先；
- Planner 仍能排序 theorem 候选；
- capability-gate 不泄漏被禁 closure；
- Generator 不收到完整 theorem index；
- generic core 不包含 Boolean CSP case ID；
- plugin executable check 不替代 Lean；
- no parallel frontier；
- final audit 不降低。

## 17. 真实 API 验证矩阵

### 17.1 Case02 分层门禁

Case02 继续作为小规模黑盒验收，不作为实现特判。

依次运行：

1. production-hybrid；
2. gadget capability-gate；
3. direct-TM capability-gate；
4. semantic capability-gate；
5. from-basis research mode。

每轮报告：

- exact closures allowed/forbidden；
- Planner selected route；
- GeneratorBrief；
- generated declarations；
- final contribution classification；
- forbidden dependency。

### 17.2 Gadget 20 题

目标：

- 禁止完整 gadget/interpretation closure；
- direct-TM 和 semantic 可复用；
- 统计实际需要 gadget generation 的 case；
- 生成 capability 必须 final-used；
- 测试 arbitrary finite relation adapter，而不是只测试已有 core 名称。

### 17.3 direct-TM 20 题

沿用：

    python -m agent.generative_reduction.boolean_csp_capability_gate

但必须先满足：

- 17/17 case 获得 DirectTMCapabilityPlan；
- target-specific authoring/design coverage 为 17/17；
- direct-TM capsule 非空；
- no RuleInstantiationProbe handle；
- no non-executable helper design；
- capability-scoped budget 已保留。

### 17.4 semantic 20 题

必须先满足：

- 17/17 case 获得 SemanticCapabilityPlan；
- forward/reverse plan 均存在；
- semantic capsule 包含定义、primitive 和 constructor；
- no empty theorem-composition design；
- direction helper 可以独立保存和复用。

### 17.5 交叉领域 held-out

为了证明通用性，新增非 Boolean CSP held-out：

- finite graph gadget 或有限自动机 witness；
- 一个非 Boolean CSP 的 direct-TM program composition；
- 一个非 Boolean CSP 的 bidirectional semantic witness proof。

验收：

- 不增加 case-specific planner rule；
- 使用相同 CapabilityPlan/GeneratorBrief；
- 使用相同 contribution classification；
- 至少一项 generated capability kernel verified。

## 18. 实施阶段

### Phase 0：模型和报告 schema

修改：

- agent/generative_reduction/models.py；
- agent/generative_reduction/model/protocol.py；
- agent/generative_reduction/reporting.py；
- tests/test_generative_reduction.py。

任务：

- CandidateReceipt；
- TheoremApplicationPlan；
- CapabilityPlan；
- GeneratorBrief；
- GeneratorResult；
- ContributionReceipt；
- PlannerEffectReceipt；
- serialization/resume；
- report consistency。

验收：

- mock Planner plan 可序列化；
- brief 与 plan fingerprint 一致；
- GeneratorResult 只能引用 brief 中候选；
- contribution report 可区分 reuse 和 generation。

### Phase 1：P0 正确性修复

修改：

- agent/generative_reduction/context_capsule.py；
- agent/generative_reduction/lean_bridge.py；
- agent/generative_reduction/recursive_runtime.py；
- agent/generative_reduction/providers/synthesis.py；
- agent/generative_reduction/model/authoring.py；
- tests。

任务：

- stable dependent binding；
- probe handle audit；
- context-insufficient gate；
- construction-basis expansion；
- fixed declaration envelope；
- identifier manifest；
- non-executable design prefilter；
- capability-scoped budgets；
- transport/protocol retry；
- repair/replan split。

验收：

- direct-TM 和 semantic synthetic capsule 不为空；
- exact goal 不含 RuleInstantiationProbe；
- omitted frozen declaration 类错误消失；
- helper-first 无 residual 时不创建 design；
- target capability 至少保留一轮完整 generation budget。

### Phase 2：Planner → Independent Generator

修改：

- agent/generative_reduction/model/strategy.py；
- 新增或扩展 capability planner 模块；
- agent/generative_reduction/capability_planner.py；
- agent/generative_reduction/recursive_runtime.py；
- agent/generative_reduction/model/authoring.py；
- tests。

任务：

- Planner 输出 theorem plan 或 CapabilityPlan；
- Planner 生成 GeneratorBrief；
- typed proof hints；
- request-lookup；
- plan-infeasible；
- brief-bound Generator；
- Planner effect receipt；
- Generator hint usage receipt；
- plan switch。

验收：

- Planner 选择 theorem 后 deterministic closure；
- Planner 选择 scaffold 后 residual 进入 frontier；
- Planner 建议第二个 primitive，Generator 实际使用；
- Generator 不能使用 brief 外 theorem；
- Generator request-replan 能形成新 plan_id。

### Phase 3：Gadget Planner/Generator v2

修改：

- agent/generative_reduction/plugins/boolean_csp.py；
- finite synthesis protocol；
- BooleanCSPFiniteGadget.lean；
- capability-specific planner/generator adapter；
- tests。

任务：

- arbitrary finite Gamma reification；
- dynamic grammar/bounds；
- fixed templates 降级为 seeds；
- Planner-selected enumeration/CEGIS；
- counterexample accumulation；
- generated gadget composition；
- contribution receipts。

验收：

- 一个非预置 synthetic relation 生成 Gadget；
- Case02 gadget gate 通过；
- 至少一个 Boolean CSP benchmark gadget final-used；
- 无 canonical closure dependency。

### Phase 4：Semantic Planner/Generator

修改/新增：

- semantic capability plan；
- structural direction decomposition；
- witness/invariant generator；
- helper DAG execution；
- direction-level capability registration；
- tests。

任务：

- forward/reverse plans；
- witness schema；
- exact helper specs；
- direction-level GeneratorBrief；
- preserve successful direction；
- final Iff assembler；
- semantic contribution receipt。

验收：

- synthetic semantic proof 不调用完整 iff/forward/reverse closure；
- Case02 semantic gate 通过；
- semantic 20 题中至少一个非复用 case 生成并 final-use semantic capability；
- 17/17 case 具有有效 plan 和非空 context。

### Phase 5：direct-TM Planner/Generator

修改/新增：

- TypedProgramNode；
- DirectTMCapabilityPlan；
- program normalization probe；
- TM primitive registry；
- node Generator；
- deterministic TM compiler；
- endpoint equality generator；
- tests。

任务：

- function definition expansion；
- program DAG；
- node primitive coverage；
- missing node helper generation；
- node-level repair；
- endpoint equality；
- final TM theorem assembly；
- direct-TM contribution receipt。

验收：

- synthetic map/flatten program 通过；
- Case02 direct-TM gate 通过；
- direct-TM 20 题中至少一个非复用 case 生成并 final-use direct-TM capability；
- 17/17 case 获得 target-specific plan。

### Phase 6：完整回归与 held-out

任务：

- production-hybrid Boolean CSP 20 题；
- gadget gate 20 题；
- direct-TM gate 20 题；
- semantic gate 20 题；
- from-basis 小规模测试；
- 非 Boolean CSP held-out；
- token/cost/wall-time comparison；
- contribution audit。

硬验收：

- 所有 suite 有完整终态；
- 0 forbidden dependency；
- 0 unresolved probe handles；
- 0 empty-context Generator call；
- 0 ignored valid Planner decision；
- 0 non-executable design 消耗数学 design budget；
- 每项能力至少一个真正 generated capability final-used；
- production 模式已有 theorem 仍能快速复用；
- generic core 无 benchmark 特判。

## 19. 完成标准

本计划完成必须同时满足：

1. Planner LLM 仍能排序 theorem、action 和 design；
2. exact closure 在未屏蔽时可以直接快速结束子步骤；
3. scaffold 可以形成 residual DAG 并向 Generator 传递 typed proof advice；
4. Generator 以独立上下文和冻结 brief 工作；
5. Generator 能生成新的 Gadget witness；
6. Generator 能生成新的 direct-TM program node/helper 或 endpoint proof；
7. Generator 能生成新的 semantic witness/invariant/helper；
8. ContextCapsule 不再为空壳；
9. dependent goals 不再引用临时 probe declarations；
10. repair 和 replan 边界明确；
11. design budget 不再被不可执行方案消耗；
12. 每个 generated capability 有 Lean、dependency、contribution 和 final-used receipt；
13. production-hybrid 和 capability-gate 的结果不会混淆；
14. direct-TM、semantic 和 gadget 各至少有一个真实 API 非复用成功；
15. held-out 证明机制不依赖 Boolean CSP case/name；
16. final artifact 继续通过完整可信审计。

## 20. 立即执行顺序

1. 定义 CandidateReceipt、CapabilityPlan、GeneratorBrief 和 ContributionReceipt；
2. 修复 stable dependent binding 和 RuleInstantiationProbe 泄漏；
3. 加入 context-insufficient gate；
4. 完成 construction-basis ContextCapsule；
5. fixed declaration envelope；
6. non-executable design prefilter；
7. capability-scoped budget；
8. 扩展 Planner 输出 theorem plan、proof advice 和 GeneratorBrief；
9. 建立 independent Generator execution；
10. 将 Gadget 固定模板改为 Planner-controlled grammar/CEGIS；
11. 实现 semantic direction plan 和 helper DAG；
12. 实现 direct-TM program DAG 和 node generator；
13. 运行 synthetic tests；
14. 运行 Case02 分层门禁；
15. 依次运行 gadget、semantic、direct-TM 20 题能力门禁；
16. 运行 production-hybrid 20 题回归；
17. 运行非 Boolean CSP held-out。

本轮核心判据：

> Planner 可以充分利用库内已有 theorem，也可以把 theorem、primitive 和数学建议交给独立 Generator；但只有 Generator 或确定性 synthesis 真正产生并由最终 artifact 使用的新程序、witness、invariant 或 substantive helper，才计为库内缺失能力的生成。
