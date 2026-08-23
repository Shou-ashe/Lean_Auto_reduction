# Boolean CSP Agent“真实数学生成”门禁实施计划

> 状态：Active
>
> 更新日期：2026-08-20
>
> 当前唯一实施主线：显式 pp-gadget 作者化门禁。
>
> 命名约束：本文及后续实现只使用描述能力的语义名称；文件名、目录名、CLI 值、
> policy key、报告名和测试名不得使用“单字母加序号”的阶段代号。
>
> 本文件已完整取代此前的 Agent improvement plan。旧计划不再作为当前实施依据。

## 0. 执行结论

### 稳定命名约定

门禁名称必须描述被测试的能力，执行先后只通过依赖关系和 rollout 顺序表达，不能编码进
名称。实现中优先使用以下稳定 slug：

- `gadget-authoring`
- `gadget-correctness-proof`
- `formula-semantics`
- `assignment-witness-authoring`
- `direct-tm-program-dag`
- `direct-tm-low-level-compiler`
- `three-sat-to-nae3`
- `three-sat-to-one-in-three`
- `certificate-assembly`

schema 名中的版本后缀只表示数据格式版本，不表示门禁层级或项目阶段。

下一步不应继续通过“多删几个定理”来测试模型，也不应禁掉整个
`BooleanCSPFiniteGadget` 模块。

当前应实现一个独立的 `gadget-authoring` 门禁：

1. 禁止所有会搜索、枚举、选择或套用现成 gadget 的路径；
2. 保留 `FiniteConstraint`、`FiniteFormula`、`Spec`、`Spec.Correct`
   和 `Spec.toGadget` 等中性证书与验证基础设施；
3. 要求模型明确给出：
   - 选择的源 hard core；
   - 辅助变量数；
   - 每一个目标约束及其变量映射；
   - 输出变量映射；
4. 确定性程序只能忠实序列化模型给出的对象、检查真值表并反馈反例，不能增加、
   删除、替换或搜索任何约束；
5. 最终 30 题中的非锚点题必须实际使用本次运行中模型生成的 gadget；
6. 只有 `MODEL_GENERATED_CAPABILITY` 且 final-used 的贡献才计入作者化成功。

显式 Gadget 作者化门禁测试的是“模型能否提出正确的数学构造”。有限真值表验证可以由 Lean
`by decide` 完成，因为验证器自动检查一个明确提出的构造，并不替模型寻找构造。

“模型手写完整双向证明”是独立的 Gadget 正确性证明门禁。不能在第一阶段同时混入，否则无法区分：

- 模型没有找到 gadget；
- 模型找到了 gadget，但不会写 Lean 证明；
- 模型会证明，但被框架样板或上下文问题阻塞。

## 1. 研究目标与判定边界

### 1.1 核心研究问题

本门禁必须回答：

> 在没有有限模板搜索器、canonical gadget、目标专用现成 gadget 和 Schaefer
> 通用闭包定理的情况下，Agent 是否能够根据源关系和目标语言的真值表，提出一个新的
> pp-definition，并生成一个被最终 NP-hardness 证明实际使用的 Lean-verified gadget？

### 1.2 什么计为“真实数学内容”

对 显式 Gadget 作者化门禁，一份 gadget 的实质数学内容定义为以下语义载荷：

```text
source_core
source_symbol
variable_count
formula = [(target_symbol, variable_mapping), ...]
outputs = [output_variable_0, ..., output_variable_(arity-1)]
```

其中：

- `source_core` 决定从 NAE-3 或 1-IN-3 等哪个已知 NP-hard core 出发；
- `formula` 是一个存在量词合取公式；
- 每个约束使用目标语言 `Γ` 中的一个 relation symbol；
- `variable_mapping` 指定该目标 relation 的各坐标连接到哪些输入或辅助变量；
- `outputs` 指定源 relation 的自由变量。

只有当这些字段来自模型响应，且被最终 Lean artifact 使用时，才计为模型生成的数学
构造。

以下内容不计为新的数学构造：

- 模型只说“使用 NAE gadget”或“搜索一个 pp-definition”；
- 模型只选择一个 theorem、plugin 或模板；
- 确定性程序枚举候选并选择第一个正确项；
- 模型引用库中已有的 `Gadget` 或 `LanguageInterpretation`；
- 模型生成的声明通过 Lean，但最终证明未使用它；
- 模型只生成策略文本，最终 capability 由 deterministic compiler 产生；
- 确定性 renderer 在模型计划之外补充了数学约束。

### 1.3 语义作者化与 Lean 语法作者化分离

显式 Gadget 作者化门禁不要求模型亲自拼写所有 Lean record 语法。允许以下两种实现：

- 推荐：模型输出结构化 `BooleanCSPGadgetPlanV1`，确定性 renderer 原样转成
  `Spec`；
- 兼容：模型直接输出含显式局部 `Spec` 的 Lean proof body。

正式门禁优先采用结构化计划。原因是该方式更容易证明：

- 数学对象确实由模型给出；
- renderer 没有暗中搜索；
- 每次 repair 改变了哪些约束；
- 可稳定提取变量数、约束数和输出映射；
- Lean 语法错误不会污染对数学构造能力的测量。

确定性 renderer 只要满足“结构保持、零数学补全”，不改变贡献分类：

```text
模型选择全部语义字段
        +
确定性语法序列化与验证
        =
MODEL_GENERATED_CAPABILITY
```

如果确定性程序搜索、选择、添加或替换任何公式原子，则必须分类为
`HYBRID_GENERATED_CAPABILITY` 或
`DETERMINISTIC_GENERATED_CAPABILITY`，不能通过 显式 Gadget 作者化门禁。

### 1.4 非目标

显式 Gadget 作者化门禁暂不测试：

- 从 Cook–Levin 起完整构造 NAE-3 或 1-IN-3 NP-hardness；
- 手工展开整个公式层面的 satisfiability 等价；
- 手工证明 TM 多项式时间；
- 手工展开 `NativeTMNPHard` 的所有证书量词；
- gadget 必须不同于所有经典构造；
- 最短 gadget 或最少辅助变量。

这些目标分别属于 Gadget 正确性证明门禁、语义与复杂度作者化、源 NP-hard 归约作者化门禁或独立优化实验。

## 2. 当前代码事实与原计划修正

### 2.1 finite gadget 插件并非 authoritative

`BooleanCSPExplicitFiniteGadgetPlugin` 和
`BooleanCSPCanonicalDatabaseFinitePlugin` 当前都声明：

```python
authoritative_typed_compiler = False
```

它们通常获胜，是因为 action 成本低且确定性成功，而不是因为 authoritative provider
压制了模型通道。

因此不能通过“把 model provider 全局设为 authoritative”解决问题。正确做法是：

- 门禁运行时按 capability kind 过滤竞争插件；
- 只对 `Gadget` / `LanguageInterpretation` 目标禁用确定性 gadget 插件；
- 保留 exact reuse 对锚点题和其他 capability 的正常行为；
- 保留 direct-TM 与 semantic compiler，避免 显式 Gadget 作者化门禁同时测试三个不同能力。

相关实现位置：

- `agent/generative_reduction/plugins/boolean_csp.py`
- `agent/generative_reduction/action_providers.py`
- `agent/generative_reduction/orchestrator.py`

### 2.2 不能禁掉整个 finite gadget 模块

`BooleanCSPFiniteGadget.lean` 同时包含两类声明。

允许保留的中性证书声明：

- `FiniteConstraint`
- `FiniteConstraint.Satisfies`
- `FiniteConstraint.toConstraint`
- `FiniteFormula`
- `FiniteFormula.Satisfies`
- `FiniteFormula.toFormula`
- `FiniteFormula.extend`
- `FiniteFormula.restrict`
- `FiniteFormula.satisfies_extend_iff`
- `FiniteFormula.satisfies_restrict_iff`
- `Spec`
- `Spec.Correct`
- `Spec.toGadget`

必须禁止的发现、搜索与选择声明：

- `AnyCorrect`
- `anyCorrectDecidable`
- `chooseCorrect`
- `gadgetOfCandidates`
- `plannedMappedVariable`
- `plannedConstraintOfMapping`
- `plannedSpecOfFormula`
- `plannedFormulasForTemplate`
- `plannedSpecs`
- `firstPlannedCounterexample?`
- `renderPlannedCounterexample`
- `gadgetOfPlannedSearch`
- `mappedVariable`
- `constraintOfMapping`
- `formulasForTemplate`
- `templates`
- `defaultSpecs`
- `gadgetOfDefaultSearch`

门禁实现应对该 namespace 采用“允许列表”而不是只维护一个容易漏项的禁止列表：

```text
BooleanCSPFiniteGadget namespace 中：
    仅允许证书定义、语义定义和 Spec.toGadget 提升引理；
    其他声明默认禁止。
```

### 2.3 当前 evaluator 已经过时

`agent/generative_reduction/boolean_csp_capability_gate.py` 当前：

- 只支持 `direct-tm` 和 `semantic`；
- 通过目标类型字符串判断 capability；
- 硬编码 `required_nonreuse_cases = 17`；
- 不要求 contribution class 为 `MODEL_GENERATED_CAPABILITY`；
- 不验证显式 gadget 载荷；
- 不验证 deterministic gadget plugin 是否被实际禁用。

30 题 suite 已存在后，任何继续使用固定数字 17 的 gate 都不能作为正式作者化证据。

### 2.4 当前 authoring 通道可以复用

已有基础设施包括：

- `lean-authoring-initial`；
- `lean-authoring-repair`；
- runtime-owned declaration header；
- `proof_body` 与 `helper_declarations`；
- source hash；
- independent Lean check；
- forbidden dependency audit；
- `ContributionReceipt`；
- `MODEL_GENERATED_CAPABILITY`。

显式 Gadget 作者化门禁不需要重写整个 authoring 系统。应在其上增加一个 Boolean CSP 专用的结构化
gadget protocol，并复用模型调用、预算、repair、source binding 和最终贡献审计。

## 3. 门禁阶梯

| 层级 | 状态 | 禁止内容 | 模型必须产生 | 主要测量 |
|---|---|---|---|---|
| 确定性基线门禁 | 已有 | Schaefer 通用捷径及 canonical closure | 允许 finite search 产生 gadget | 端到端基础能力 |
| **显式 Gadget 作者化门禁** | **当前实施** | 搜索器、模板、candidate selection、现成 gadget | 完整 pp-formula 和输出映射 | 数学构造 |
| Gadget 正确性证明门禁| 显式 Gadget 作者化门禁稳定后 | 再限制整段 `by decide` | 正向、反向局部等价证明 | 有限证明组织 |
| 公式语义作者化门禁| 后续 | 高层公式语义组装器 | 公式级 satisfiability iff | 归约正确性 |
| Direct-TM 复杂度作者化门禁| 后续 | 高层 TM/time 组装器 | 尺寸界与多项式时间证明 | 复杂度分析 |
| 源 NP-hard 归约作者化门禁| 高风险 canary | NAE-3、1-IN-3 硬 core theorem | 3SAT 到 hard core 的完整归约 | 长程归约 |
| 证书与 Hardness 量词作者化门禁| 可选 | 通用证书组装器 | 手工展开 `CertifiedReduction` 等 | 框架/API 掌握 |

证书与 Hardness 量词作者化门禁不作为“数学能力最高等级”。它很可能主要测量 Lean 框架样板和库 API 熟悉度。

## 4. 显式 Gadget 作者化门禁

### 4.1 目标 capability

每个 required case 至少生成一个：

```lean
LanguageInterpretation sourceCore targetGamma
```

或一个被该 interpretation 直接使用的 pointwise：

```lean
(symbol : sourceCore.Symbol) →
  Gadget targetGamma (sourceCore.relationOf symbol)
```

源 hard core 可以是当前库内已有 NP-hardness 的有限 Boolean core，例如：

- NAE-3；
- 1-IN-3。

选择哪个 source core 可以由 Planner LLM 完成，也可以由已验证 scaffold 暴露出来，但
必须在 contribution receipt 中记录。显式 Gadget 作者化门禁的核心评分对象仍是具体 gadget，而不是 source
hardness theorem。

### 4.2 结构化模型协议

新增 schema：

```json
{
  "schema": "boolean_csp_gadget_plan_v1",
  "source_core": "nae3 | one_in_three3",
  "gadgets": [
    {
      "source_symbol": "<stable source symbol id>",
      "variable_count": 6,
      "outputs": [0, 1, 2],
      "constraints": [
        {
          "target_symbol": "<stable target symbol id>",
          "vars": [0, 3, 4, 1]
        }
      ]
    }
  ],
  "mathematical_rationale": "<short natural-language explanation>"
}
```

约束：

- `gadgets` 必须覆盖 source language 的每个 symbol；
- `variable_count` 必须至少覆盖全部 outputs；
- `outputs` 长度必须等于 source relation arity；
- outputs 必须两两不同；
- 每个 `vars` 长度必须等于对应 target relation arity；
- 所有变量编号必须小于 `variable_count`；
- constraints 的顺序只影响稳定 hash，不影响语义；
- `mathematical_rationale` 用于审计，不作为证明权威；
- 模型不得提交候选列表，必须每次提交一个确定构造。

### 4.3 模型必须看到的上下文

Generator brief 必须包含：

- 当前 case ID、input module 和 exact goal；
- source core 的关系 arity 和完整真值表；
- target `Γ` 的全部 symbol、arity 和完整真值表；
- pp-definition 的自然语言语义；
- `Spec.Correct` 的精确定义；
- schema；
- 当前资源上限；
- 上一次失败的 schema error、语义反例或 Lean error；
- 允许使用的中性声明签名；
- 禁止声明列表及 policy hash。

不得包含：

- `templates` 的内容；
- Python `_dual_cardinality_template`；
- 任何已知正确 gadget 的 formula；
- q-b07 的现成 complement gadget；
- oracle、gold proof 或隐藏评分字段；
- 其他 benchmark case 的成功 gadget；
- deterministic search 产生的候选列表；
- 能直接关闭当前 gadget 目标的现成 theorem body。

可以提供一个与 benchmark 无关、只解释 JSON 字段格式的微型语法例子，但不能提供与
NAE、1-IN-3、固定基数或随机表语言同构的答案模板。

### 4.4 允许的确定性工作

以下操作是验证或编译，不改变作者归因：

- JSON schema validation；
- relation symbol 和 arity 检查；
- 把模型的整数变量编号忠实序列化为 `Fin`；
- 把 constraints 原样序列化为 `FiniteConstraint`；
- 构造模型明确给出的 outputs；
- 用 `by decide` 证明有限 outputs injectivity；
- 对模型提交的单个 formula 枚举辅助变量赋值，检查完整真值表；
- 返回第一个 false-positive 或 false-negative 反例；
- 用 `Spec.Correct` 和 `Spec.toGadget` 进行 Lean kernel 验证；
- 使用现有 semantic/direct-TM compiler 将已验证 interpretation 组装进最终证明。

验证器可以搜索“给定 formula 是否存在辅助变量赋值”，因为这是 pp-formula 语义的一部分。
它不能搜索“应该使用哪个 formula”。

### 4.5 禁止的确定性工作

以下任一行为发生时，显式 Gadget 作者化门禁失败：

- 枚举多个 formula；
- 从多个 candidate 中选择正确项；
- 自动增加、删除、重排之外地修改 constraint；
- 自动选择 target symbol；
- 自动扩大 formula 并重试；
- 根据真值表反例自动合成新 constraint；
- 调用 fixed template、dual-cardinality template 或 canonical database；
- 复用库中现成 gadget；
- 将搜索结果伪装成模型 proposal；
- renderer 产生模型 payload 中不存在的数学原子。

变量编号的规范化、record 语法、namespace、类型标注和证明样板不属于数学原子。

### 4.6 repair 协议

一次 authoring attempt 的状态机：

```text
MODEL_PROPOSAL
    → SCHEMA_CHECK
    → FINITE_SEMANTIC_CHECK
    → LEAN_MATERIALIZATION
    → INDEPENDENT_REPLAY
    → REGISTER_CAPABILITY
    → FINAL_USE_AUDIT
```

失败反馈分三类：

1. Schema failure：
   - 缺字段；
   - arity 不匹配；
   - 越界变量；
   - outputs 非单射。
2. Semantic failure：
   - source tuple；
   - 期望 relation truth value；
   - 当前 formula 是否存在 extension；
   - 方向：false-positive 或 false-negative。
3. Lean failure：
   - 最小化后的类型错误；
   - 固定 header 和 exact expected type；
   - 不返回任何已知正确候选。

repair 必须满足：

- 每次均产生新的 model response hash；
- gadget semantic payload hash 必须发生变化，否则判为重复尝试；
- 不允许 deterministic fixer 修改计划；
- 默认最多 5 次 repair；
- 达到上限后标记明确 failure code，不得回退到 deterministic gadget plugin。

### 4.7 推荐资源上限

初始资源 profile：

- `max_initial_authoring_attempts = 1`；
- `max_gadget_repairs = 5`；
- `model_max_tokens = 16000`；
- `model_timeout_seconds = 300`；
- `lean_timeout_seconds = 600`；
- `wall_clock_timeout_seconds = 3600`；
- `max_lean_checks = 400`；
- `max_model_calls = 16`；
- `max_authoring_calls = 12`。

公式资源上限不应沿用旧模板的“最多 6 变量、7 约束”。建议先通过 microbenchmark
确定两个 profile：

- canary：最多 8 个变量、16 个约束；
- full：最多 12 个变量、24 个约束。

这些是计算资源限制，不是 template grammar。模型可以在限制内给出任意约束结构。若
发现正式题确实需要更大 witness，应版本化提高 profile，而不是暗中加入新模板。

## 5. 门禁策略与代码结构

### 5.1 新增统一 GatePolicy

建议新增：

```text
agent/generative_reduction/capability_gate_policy.py
```

核心数据结构建议为：

```python
@dataclass(frozen=True)
class CapabilityGatePolicy:
    name: str
    policy_version: str
    required_case_ids: tuple[str, ...]
    anchor_case_ids: tuple[str, ...]
    required_capability_kind: CapabilityKind
    required_contribution_classes: tuple[ContributionClass, ...]
    disabled_finite_synthesis_plugins: tuple[str, ...]
    forbidden_declarations: tuple[str, ...]
    excluded_candidate_declarations: tuple[str, ...]
    allowed_certificate_declarations: tuple[str, ...]
    require_model_semantic_payload: bool
    require_final_artifact_use: bool
    require_independent_lean: bool
    require_zero_forbidden_dependencies: bool
```

所有 case 数量由 policy 的 case IDs 推导，禁止再次硬编码 17、27 或其他数字。

### 5.2 Orchestrator 增加门禁感知插件过滤

`GenerativeReductionConfig` 至少新增：

```python
gate_policy: CapabilityGatePolicy | None = None
```

安装插件后、传入 `RecursiveSearchRuntime` 前执行：

```python
finite_plugins = tuple(
    plugin
    for plugin in finite_plugins
    if plugin.name not in gate_policy.disabled_finite_synthesis_plugins
)
```

显式 Gadget 作者化门禁必须禁用：

- `boolean-csp-explicit-finite-gadget`
- `boolean-csp-canonical-database`

必须保留：

- `boolean-csp-direct-tm-compiler`
- `boolean-csp-semantic-compiler`

报告必须记录：

- 安装前插件名；
- 被 policy 禁用的插件名；
- 实际传给 runtime 的插件名；
- policy version 和 policy hash。

如果被声明禁用的插件仍产生 action 或 receipt，运行立即判定为 policy violation。

### 5.3 theorem 路由过滤

继续保留现有基础禁令：

- `NativeTMNPHard_of_notSchaeferTractable`
- `NativeTMNPHard_of_notSchaeferTractable_with_oneInThree`
- `schaefer_dichotomy`
- `CanonicalHardCores.oneInThreeInterpretation`
- `CanonicalHardCores.naeInterpretation`
- `CanonicalDatabase.gadget`
- canonical closed lemmas。

显式 Gadget 作者化门禁再增加：

- finite gadget namespace 中所有非 allowlist 声明；
- q-b07 的
  `oneInThreeGadgetOfExactlyTwo3`；
- q-b07 的
  `exactlyTwo3InterpretsOneInThree`；
- theorem index 中任何能够无实质 residual obligation 关闭 required-case
  `Gadget` 或 `LanguageInterpretation` 目标的现成声明。

例外：

- `Spec.toGadget` 可以作为 constructor/scaffold；
- 它必须消费本次模型生成的显式 `Spec` 和正确性证据；
- source core NP-hardness theorem 可以复用；
- 显式 interpretation packaging theorem 可以复用；
- direct-TM 和 semantic 的确定性编译器可以在 显式 Gadget 作者化门禁使用。

### 5.4 不全局改变 provider 权威性

显式 Gadget 作者化门禁通过 policy 过滤不合格 action，不修改生产模式下的默认 provider 语义。

这保证：

- production-hybrid 仍可优先使用确定性 gadget；
- 其他 benchmark 不受影响；
- q-b01、q-b03、q-b04 等锚点仍能合法 exact reuse；
- 门禁行为完全由报告中的 policy hash 重放。

## 6. 专用 Gadget Generator

### 6.1 Planner 输出

Planner 只负责形成类型化构造合同，不得提交候选 formula 列表。

计划至少包含：

- source core 选择；
- source/target truth-table handles；
- 每个 source symbol 需要一个 gadget；
- variable/constraint resource bounds；
- 是否允许常量模拟、重复变量和辅助变量；
- expected exact Lean type；
- 最终 interpretation declaration；
- 后续 semantic、direct-TM 和 final packaging 节点。

Planner 提议不计为 gadget 成功。只有 Generator 的结构化计划通过验证并 final-used 才计分。

### 6.2 Generator 输出

新增专用 provider，例如：

```text
BooleanCSPGadgetAuthoringGenerator
```

模型调用 purpose 建议为：

- `gadget-authoring-initial`
- `gadget-authoring-repair`

底层仍复用现有 JSON model client、调用记录、预算和错误处理。

### 6.3 Canonical renderer

新增纯序列化器，例如：

```text
render_boolean_csp_gadget_plan
```

输出形状应稳定：

```lean
by
  classical
  refine { gadgetOf := ?_ }
  intro sourceSymbol
  fin_cases sourceSymbol
  let spec : BooleanCSPFiniteGadget.Spec target relation variableCount := {
    formula := [
      -- 与模型 constraints 一一对应
    ]
    outputs := ...
    outputs_injective := by decide
  }
  exact BooleanCSPFiniteGadget.Spec.toGadget spec (by decide)
```

renderer 的约束：

- constraints 数量与顺序必须与模型 payload 完全一致；
- target symbol 与变量数组必须逐项一致；
- outputs 必须逐项一致；
- 不得调用任何 search helper；
- 生成前后都计算 canonical semantic payload hash；
- 报告 `renderer_added_semantic_atom_count = 0`；
- renderer 版本进入 policy hash。

### 6.4 独立有限语义检查器

在 Lean 前增加一个诊断检查器：

```text
check_explicit_gadget_plan(plan, source_tables, target_tables)
```

它对每个 source tuple 检查：

[
R(\bar x)
\iff
\exists \bar y\;
\bigwedge_i C_i(\bar x,\bar y).
]

检查器只接受一个模型 plan，不枚举 plan 空间。

输出：

- success；
- 或第一个稳定排序的反例；
- 被检查的 source row 数；
- 被检查的 auxiliary assignment 数；
- checker version 和 input hash。

最终证明权威仍是 Lean，不是 Python checker。Python checker 只用于快速反馈和可解释报告。

## 7. 贡献归因与审计

### 7.1 AuthorshipEvidence

建议在通用 `ContributionReceipt` 中增加可选的作者化证据：

```python
@dataclass(frozen=True)
class AuthorshipEvidence:
    semantic_payload_schema: str
    semantic_payload_sha256: str
    model_response_sha256: str
    origin: str
    renderer_name: str
    renderer_version: str
    renderer_added_semantic_atom_count: int
    validation_only_steps: tuple[str, ...]
    variable_count: int | None
    constraint_count: int | None
    output_mapping: tuple[int, ...]
    relation_symbols_used: tuple[str, ...]
    repair_payload_hashes: tuple[str, ...]
```

显式 Gadget 作者化门禁要求：

```text
origin == "model"
semantic_payload_schema == "boolean_csp_gadget_plan_v1"
renderer_added_semantic_atom_count == 0
model_response_sha256 非空
semantic_payload_sha256 非空
```

### 7.2 Contribution class 规则

`MODEL_GENERATED_CAPABILITY`：

- 全部 semantic atoms 来自模型 payload；
- renderer 只序列化；
- checker 只验证；
- final artifact 使用该 capability。

`HYBRID_GENERATED_CAPABILITY`：

- 模型提出部分结构；
- deterministic solver 补充、搜索或选择了其余结构。

`DETERMINISTIC_GENERATED_CAPABILITY`：

- formula 由 template、enumerator、canonical database 或 solver 产生。

显式 Gadget 作者化门禁只接受第一类。

### 7.3 final-use 不能靠脆弱字符串搜索

当前 `_artifact_uses` 通过在文件中搜索 declaration name 判断使用关系，只能作为辅助。

正式 显式 Gadget 作者化门禁应使用：

- Lean environment 中的声明依赖闭包；
- generated declaration 的 fully-qualified name；
- final endpoint declaration 的 transitive dependency graph；
- source hash 与声明注册记录；
- independent replay 结果。

字符串命中可以保留为诊断，但不能作为唯一通过依据。

### 7.4 禁止依赖审计

每个 required case 必须满足：

- forbidden direct dependency count = 0；
- forbidden transitive dependency count = 0；
- oracle/gold dependency count = 0；
- disabled plugin contribution count = 0；
- pre-existing exact gadget reuse count = 0；
- unresolved probe handle count = 0；
- final-used deterministic gadget receipt count = 0。

## 8. 显式 Gadget 作者化门禁评估器

新增：

```text
evaluate_gadget_authoring_gate(report, policy)
```

不要继续把 gadget 逻辑塞进只支持 direct-TM/semantic 的字符串分支。

### 8.1 每题状态

每题输出以下互斥状态之一：

- `ANCHOR_REUSE_VERIFIED`
- `MODEL_GADGET_VERIFIED_AND_FINAL_USED`
- `ROUTE_NOT_REACHED`
- `MODEL_PLAN_NOT_PRODUCED`
- `MODEL_PROTOCOL_INVALID`
- `GADGET_PLAN_SCHEMA_INVALID`
- `GADGET_SEMANTIC_COUNTEREXAMPLE`
- `LEAN_MATERIALIZATION_FAILED`
- `FORBIDDEN_DEPENDENCY`
- `ATTRIBUTION_MISMATCH`
- `CAPABILITY_NOT_FINAL_USED`
- `BUDGET_EXHAUSTED`
- `SYSTEM_ERROR`

这一区分很重要：`ROUTE_NOT_REACHED` 不能被解释为模型不会构造 gadget。

### 8.2 required-case 硬检查

对 policy 中每个 required case：

- case 完成；
- root proof 为 `VERIFIED`；
- 至少一个 final-used gadget receipt；
- capability kind 为 `gadget` 或明确绑定的
  `language-interpretation`；
- contribution class 为 `MODEL_GENERATED_CAPABILITY`；
- authorship evidence 完整；
- semantic payload 来自本 case 的模型调用；
- independent Lean passed；
- forbidden audit passed；
- final root artifact 的依赖闭包含生成声明；
- 无 deterministic gadget contribution；
- 无搜索、模板、canonical 或目标专用 gadget 依赖。

### 8.3 anchor-case 硬检查

锚点题：

- 允许 `THEOREM_REUSE`；
- 必须 `VERIFIED`；
- 不要求模型生成 gadget；
- 不得被计入 authored success numerator 或 denominator。

### 8.4 suite 级输出

报告同时给出：

- `integrity_passed`：所有来源、依赖、policy 和重放检查通过；
- `required_case_count`；
- `authored_success_count`；
- `authored_success_rate`；
- `anchor_verified_count`；
- `route_failure_count`；
- `mathematical_failure_count`；
- `lean_only_failure_count`；
- `system_failure_count`；
- `strict_gate_passed`。

`strict_gate_passed` 的定义：

```text
integrity_passed
and all anchor cases verified
and authored_success_count == required_case_count
```

研究报告必须保留部分成功率，不能因为 strict gate 未通过就丢失能力信号。

## 9. 30 题的分组策略

### 9.1 锚点题

显式 Gadget 作者化门禁锚点：

- q-b01-canonical-three-sat-like；
- q-b03-positive-nae3；
- q-b04-positive-exactly-one3。

原因：

- q-b01 是库内 endpoint reuse 基线；
- q-b03、q-b04 本身就是允许作为 source 的 hard core；
- 强制它们“再解释自身”不能有效测试新的目标语言 gadget。

### 9.2 正式 required cases

显式 Gadget 作者化门禁的正式 authored set 共 27 题：

- q-b02；
- q-b05–q-b30。

其中 q-b07 必须额外禁止现成 exactly-two/one-in-three gadget 和 interpretation。

不要在 evaluator 中写 `27`。该数字必须由 policy 中显式 case IDs 计算。

### 9.3 开发、验证与 heldout 纪律

现有 split：

- dev：q-b01–q-b04；
- validation：q-b05–q-b10；
- heldout：q-b11–q-b30。

开发阶段只能反复使用：

- q-b02；
- 新增的非正式 `ga-dev-*` synthetic gadget fixtures。

建议增加三个不计入正式 30 题的开发 fixture：

- 一个四元单关系随机 hard-side 语言；
- 一个固定基数的对偶变体；
- 一个双 relation、混合 arity 语言。

它们只用于协议、renderer 和 repair 调试。

在 policy、prompt、renderer 和预算冻结后：

1. 一次性运行 validation q-b05–q-b10；
2. 不根据 heldout 单题答案修改 prompt；
3. 最后一次性运行 q-b11–q-b30；
4. 若查看 heldout 失败后修改系统，必须提升 gate version，并把旧 heldout 结果标为已污染，
   不能与首次结果合并。

q-b21–q-b30 的随机真值表题尤其不能被用作日常 prompt 调参 canary。

## 10. 组件门禁与端到端门禁

只从 `NativeTMNPHard problem` 根目标运行，会把以下失败混在一起：

- Planner 没有选择 source core；
- theorem scaffold 没有展开；
- gadget authoring 没获得预算；
- gadget 构造失败；
- 后续 semantic/TM packaging 失败。

因此 显式 Gadget 作者化门禁采用双层检查。

### 10.1 组件级 authoring checkpoint

门禁 runner 为每个 required case 创建一个类型化 gadget construction contract：

- 输入是公开的 source/target truth tables；
- Planner 选择一个允许的 source core；
- Generator 产生 `BooleanCSPGadgetPlanV1`；
- renderer 和 Lean 得到 verified
  `LanguageInterpretation`。

该 checkpoint 判断模型是否真正找到局部数学构造。

### 10.2 原题端到端 final-use checkpoint

组件级 capability 注册后，继续运行原始目标：

```lean
NativeTMNPHard problem
```

允许现有确定性 semantic/direct-TM machinery 使用这个 interpretation。

最终通过仍要求：

- 原始 root proof verified；
- root declaration 的依赖闭包含模型生成 interpretation；
- 组件 capability 不是孤立的 side artifact。

### 10.3 调度保证

显式 Gadget 作者化门禁为 gadget capability 预留独立预算，不能让上游无效 design 消耗：

- 一个初始 Planner 调用；
- 一个 initial gadget authoring 调用；
- 五个 repair slot；
- 对应 Lean checks。

如果根搜索没有自然暴露 gadget 子目标，runner 应通过经过验证的显式 scaffold 创建该
subgoal，而不是回退到通用 Schaefer theorem。

## 11. 测试计划

### 11.1 Policy 单元测试

新增测试：

- required 与 anchor case 不相交；
- 两者并集符合当前 suite policy；
- 未知 case ID 被拒绝；
- 未知 plugin 名被拒绝；
- policy hash 稳定；
- required count 从 case IDs 动态计算；
- q-b07 特殊禁令存在；
- finite gadget namespace allowlist 无漏放。

### 11.2 插件过滤测试

验证 显式 Gadget 作者化门禁：

- explicit finite gadget plugin 不进入 runtime；
- canonical database plugin 不进入 runtime；
- direct-TM compiler 仍存在；
- semantic compiler 仍存在；
- production-hybrid 不受影响；
- disabled plugin 若产生 action，立即 policy violation。

### 11.3 Schema 与 renderer 测试

覆盖：

- 单 relation target；
- 双 relation target；
- 不同 arity；
- 重复变量；
- 辅助变量；
- 非前缀 outputs；
- 越界变量拒绝；
- arity mismatch 拒绝；
- 非单射 outputs 拒绝；
- canonical payload hash 稳定；
- renderer 不增加 semantic atom；
- 同一 payload 产生字节稳定的 Lean body。

### 11.4 有限 checker 测试

覆盖：

- 正确 gadget；
- false-positive；
- false-negative；
- 无辅助变量；
- 多辅助变量；
- 多 target relation；
- 反例排序稳定；
- checker 与 Lean `Spec.Correct` 在 fixture 上一致。

### 11.5 归因负测试

以下 fixture 必须被 gate 拒绝：

- 模型只输出 strategy；
- final receipt 为 deterministic；
- model source hash 为空；
- 声明未被 final artifact 使用；
- 调用 `gadgetOfPlannedSearch`；
- 调用 `gadgetOfCandidates`；
- 调用 `CanonicalDatabase.gadget`；
- q-b07 复用现成 interpretation；
- renderer 添加一条模型未给出的 constraint；
- 只有字符串命中但 Lean dependency graph 不包含生成声明；
- 模型计划来自另一个 case 的未绑定 response；
- source/policy/brief hash 不一致。

### 11.6 repair 测试

使用 fake model：

1. 第一次提交 schema-invalid plan；
2. 第二次提交语义错误 plan；
3. 第三次提交正确 plan；
4. 验证反馈只包含错误与反例；
5. 验证第三次 payload final-used；
6. 验证前两次不能被记为贡献。

重复提交相同 payload 必须被识别并停止浪费预算。

### 11.7 evaluator 测试

构造 30 题 synthetic report：

- 3 个 anchor reuse；
- 27 个 model-authored final-used gadget；
- strict gate 应通过。

逐项破坏以下字段并验证失败：

- 一个 required case 缺失；
- 一个 contribution class 错误；
- 一个 source hash 为空；
- 一个 forbidden dependency；
- 一个 independent Lean failure；
- 一个 final-use failure；
- 一个 disabled plugin receipt；
- selected/completed case 集合漂移。

### 11.8 真实 Lean smoke test

在调用真实 API 前至少完成：

- 一个手工 fixture 的结构化 plan → Lean `Spec.toGadget`；
- interpretation → semantic/direct-TM → root proof；
- 独立 replay；
- dependency closure audit；
- clean output directory 重放。

## 12. 分阶段实施

### 冻结现状与对照报告

任务：

- 保存当前 30 题 确定性基线 路径报告；
- 记录每题最终 contribution class；
- 记录 finite plugin、canonical theorem 和 exact reuse 使用情况；
- 生成现有系统的作者化归因表。

完成标准：

- 能明确区分 30 题中的 theorem reuse、deterministic gadget、generic Schaefer route；
- 对照报告有 suite hash、代码 commit、model 配置和 policy hash。

### GatePolicy 与插件过滤

任务：

- 新增 `CapabilityGatePolicy`；
- 给 orchestrator 接入 policy；
- 按 plugin name 过滤 finite synthesis plugin；
- 报告实际 plugin 集合；
- 将旧 evaluator 的 17 改为 policy-driven；
- 新增 `gadget-authoring` CLI 选项或独立 runner。

完成标准：

- 单元测试证明两个 gadget 插件在 显式 Gadget 作者化门禁完全不可见；
- direct-TM/semantic compiler 仍可用；
- production 模式行为不变。

### 结构化 Gadget Generator

任务：

- 定义 `BooleanCSPGadgetPlanV1`；
- 构造 answer-free Generator brief；
- 实现 schema validator；
- 实现 canonical semantic payload hash；
- 实现 Lean renderer；
- 接入 initial/repair model calls。

完成标准：

- fake model 可以生成一个 verified `Spec`；
- renderer 的 semantic atom count 与 payload 完全一致；
- 没有 search helper dependency。

### 显式 checker 与 CEGIS repair

任务：

- 实现单计划有限语义 checker；
- 输出稳定反例；
- 把反例接入 repair prompt；
- 区分 schema、semantic、Lean failure；
- 记录全部 attempt hashes。

完成标准：

- 错误计划得到正确方向的反例；
- checker 不生成候选；
- fake model 三步 repair 测试通过；
- 最终 Lean 仍是证明权威。

### 贡献归因与 final-use

任务：

- 增加 `AuthorshipEvidence`；
- 明确 model/hybrid/deterministic 分类规则；
- 用 Lean 依赖闭包替代单纯字符串 final-use；
- 实现显式 Gadget 作者化门禁评估器；
- 增加全部负测试。

完成标准：

- deterministic plugin 结果不能伪装为 model-generated；
- 孤立的生成 gadget 不能通过；
- 所有来源 hash 可以从 report 重放。

### 开发 canary

运行：

- q-b02；
- 三个 `ga-dev-*` fixture。

目标不是立即证明模型 4/4，而是验证：

- 每题都真正调用 gadget Generator；
- 上下文非空且 answer-free；
- 每个失败都有准确 failure class；
- 至少一个模型构造通过完整 component + end-to-end 路径；
- 没有 deterministic fallback。

若失败主要为 route、schema 或 renderer 问题，继续修工程。只有当失败已稳定落在
`GADGET_SEMANTIC_COUNTEREXAMPLE`，才开始将其视为模型数学能力信号。

### 冻结后 validation

冻结：

- policy version；
- prompt template；
- schema；
- renderer；
- checker；
- model 与参数；
- 预算；
- validation case 集合。

一次性运行 q-b05–q-b10。

完成标准：

- 所有运行完整结束；
- 无 policy/integrity failure；
- 输出逐题能力结果；
- 不根据某题正确 gadget 手工增加模板。

### heldout 与完整 30 题

在不修改冻结配置的情况下运行：

- q-b11–q-b30 heldout；
- 最后合并 q-b01–q-b30 full report。

正式 full gate：

- 3 个 anchor verified；
- 27 个 required case 都有
  `MODEL_GADGET_VERIFIED_AND_FINAL_USED`；
- zero forbidden dependency；
- zero disabled-plugin contribution；
- independent replay 全部通过。

如果未达到 27/27，报告 strict gate failure，同时保留作者化成功率和失败分类。不得把
部分成功包装成 gate passed。

### Gadget 正确性证明门禁

仅当 显式 Gadget 作者化门禁的工程性失败接近零后启动。

任务：

- 冻结显式 Gadget 作者化门禁的 gadget payload；
- 增加 `ForwardCorrect`、`ReverseCorrect` 和 `ExplicitCorrectness` 中性接口；
- 实现 构造性正确性证书 proof-plan schema；
- 实现 witness、forward、reverse 独立 authoring；
- 增加 whole-goal decide closure audit；
- 先运行 q-b02 和 dev fixtures，再运行分层 validation。

完成标准：

- formula drift 为 0；
- 至少一个非平凡 gadget 的双向 proof model-authored；
- forward/reverse sibling preservation 工作；
- final `Spec.Correct` 依赖模型 proof。

### 公式语义作者化门禁

任务：

- 禁用 semantic deterministic compiler；
- 扩展 `SemanticCapabilityPlan`；
- 先完成 公式语义提升 generic theorem；
- 再实现 Assignment Witness 作者化 assignment witness authoring；
- 实现 unique generic capability 与 27 次 final-use 分离统计。

完成标准：

- 一个 generic semantic certificate verified；
- Assignment Witness 作者化 witness origin 为 model；
- 27 个 required case final-use；
- forbidden semantic closure dependency 为 0。

### Direct-TM 复杂度作者化门禁

任务：

- 先跑 Direct-TM API 校准；
- 增加 growth certificate interface；
- 禁用 direct-TM deterministic compiler；
- 扩展 `DirectTMCapabilityPlan` 的 node origin 和 growth fields；
- 完成 程序 DAG 与增长界 generic program DAG；
- 底层解释器编译证明 只保留一个高风险 diagnostic canary。

完成标准：

- model-authored growth certificate verified；
- code DAG 核心节点 model-authored；
- generic direct-TM theorem final-used 于 27 个 required case；
- `interpretCode_tmPolyTime` forbidden dependency 为 0。

### 3SAT→NAE-3 源归约

任务：

- 建立 answer-free 3SAT/NAE3 facade；
- 隔离现有完整 NAE route；
- 实现 source reduction plan、clause-block checker 和 artifact DAG；
- 分别生成 executable、forward、reverse、growth、certificate；
- 从 Cook–Levin source hardness 得到 NAE3 root hardness。

完成标准：

- 3SAT→NAE3 完整 model-authored reduction verified；
- existing NAE route dependency 为 0；
- program/semantic/complexity 三者绑定同一 executable。

### 3SAT→1-IN-3 源归约

任务：

- 禁止所有现成 1-IN-3 hardness route；
- 组合 model-authored 3SAT→NAE-3 源归约 与 model-authored NAE3→1-IN-3 interpretation；
- 验证两段来源和 composition dependency；
- 将 direct 3SAT→1-IN-3 保留为后续扩展。

完成标准：

- 1-IN-3 root hardness verified；
- 两段 substantive capability 都是 model-authored；
- existing GraphColoring/ExactCover/oneInThree route dependency 为 0。

### 证书与 Hardness 量词作者化门禁

任务：

- 冻结前级 reduction、semantic 和 TM artifacts；
- 依次实现 CertifiedReduction 记录构造、CertifiedReduction 手工组合、NativeTMNPHard 手工运输；
- 禁止 certificate/hardness 高层 packager；
- 增加 formal glue 与 mathematical novelty 分离统计。

完成标准：

- 三个 generic certificate artifacts verified；
- 27 个 required case final-use；
- packager dependency 为 0；
- novelty credit 不被错误增加。

## 13. Gadget 正确性证明门禁

### 13.1 研究问题

Gadget 正确性证明门禁回答：

> 在一个 pp-formula 已经冻结且已知正确的情况下，模型能否自己组织“可实现性”和
> “可靠性”两个方向的形式证明，而不是让整个真值表命题被一个 `by decide` 关闭？

Gadget 正确性证明门禁不再测试 formula 的发现。公式发现已经由 显式 Gadget 作者化门禁测量。Gadget 正确性证明门禁必须冻结：

- 显式 Gadget 作者化门禁的 semantic payload hash；
- variable count；
- constraints；
- outputs；
- source/target truth tables；
- renderer version。

在一次 Gadget 正确性证明门禁运行中，模型不得修改上述任何字段。若模型认为 formula 难以证明而提出新
formula，应返回 `REQUEST_GADGET_REPLAN`，本次 Gadget 正确性证明门禁记为未通过，不能在 proof repair 中
悄悄改变数学对象。

### 13.2 将 `Spec.Correct` 拆成显式方向

建议在 `BooleanCSPFiniteGadget.lean` 或一个独立的中性 gate interface 中增加：

```lean
def Spec.OutputsAgree
    (spec : Spec Γ relation variableCount)
    (assignment : Fin variableCount → Bool)
    (tuple : BooleanTuple relation.arity) : Prop :=
  ∀ index, assignment (spec.outputs index) = tuple index

def Spec.ForwardCorrect
    (spec : Spec Γ relation variableCount) : Prop :=
  ∀ tuple, relation.Holds tuple →
    ∃ assignment,
      spec.formula.Satisfies assignment ∧
      spec.OutputsAgree assignment tuple

def Spec.ReverseCorrect
    (spec : Spec Γ relation variableCount) : Prop :=
  ∀ tuple assignment,
    spec.formula.Satisfies assignment →
    spec.OutputsAgree assignment tuple →
    relation.Holds tuple

structure Spec.ExplicitCorrectness
    (spec : Spec Γ relation variableCount) : Prop where
  forward : spec.ForwardCorrect
  reverse : spec.ReverseCorrect

theorem Spec.correct_of_explicit
    (proof : spec.ExplicitCorrectness) : spec.Correct := ...
```

`correct_of_explicit` 是允许复用的中性逻辑包装器。它只把两个方向重新组装为 iff，
不包含任何目标关系特有的数学内容。

### 13.3 强制构造性的 forward witness

仅要求一个 forward theorem 仍可能被整段 finite decision procedure 关闭。正式 Gadget 正确性证明门禁
还应要求模型定义一个显式 witness assignment：

```lean
noncomputable def authoredWitness
    (tuple : BooleanTuple relation.arity) :
    Fin variableCount → Bool := ...
```

然后证明：

```lean
theorem authoredWitness_realizes :
  ∀ tuple, relation.Holds tuple →
    spec.formula.Satisfies (authoredWitness tuple) ∧
    spec.OutputsAgree (authoredWitness tuple) tuple := ...
```

允许 witness 采用：

- 按 tuple 分支；
- Hamming weight 分支；
- 布尔表达式；
- 显式辅助变量表；
- 由已有输入位计算辅助位的函数。

不允许 runtime 根据 formula 自动求出 witness 再写回模型 proof。

### 13.4 reverse 方向的数学载荷

reverse proof 必须说明目标约束为何排除了所有非法 source tuple。模型至少应提交：

- 使用哪些 constraint；
- 从每个 constraint 得到什么局部事实；
- 如何把这些事实组合成 source relation；
- 是否按 tuple、Hamming weight、布尔恒等式或矛盾分类。

对固定基数关系，一个合理 proof outline 例如：

```text
目标约束 1、2 ⇒ 至少 t 个输出为真
目标约束 3、4 ⇒ 至多 t 个输出为真
二者合并 ⇒ Hamming weight = t
```

门禁不要求证明必须使用这种形式，但要求 reverse artifact 的依赖闭包包含模型生成的局部
invariant/helper，而不是只包含一个完整 decidability closure。

### 13.5 两个子级

#### 构造性正确性证书

模型输出结构化：

```json
{
  "schema": "boolean_csp_gadget_correctness_plan_v1",
  "frozen_gadget_payload_sha256": "sha256:...",
  "forward_witness": {
    "definition_name": "...",
    "construction_kind": "case_split | boolean_expression | table",
    "definition_body": "..."
  },
  "forward_invariants": [],
  "reverse_invariants": [],
  "case_split": "tuple | hamming_weight | custom",
  "proof_outline": []
}
```

构造性正确性证书 要求结构化证书和 witness 通过独立有限 checker，但可以暂不要求完整 Lean proof。
它用于确认模型已经给出可验证的证明思路。

#### Gadget Lean 双向证明

Gadget Lean 双向证明 是正式 Gadget 正确性证明门禁：

- witness definition 由模型生成；
- forward theorem 由模型生成；
- reverse theorem 由模型生成；
- `ExplicitCorrectness` 由模型组装；
- `correct_of_explicit` 可以确定性调用；
- 最终 `Gadget.correct` 依赖上述四项。

Gadget Lean 双向证明 只有在 构造性正确性证书 计划固定后启动。Lean repair 可以改 proof body，但不能改 frozen
gadget 或 proof plan 的核心 witness schema。

### 13.6 `decide` 使用政策

不能仅搜索字符串 `by decide`。正式政策为：

- 禁止用一个 decision proof 关闭：
  - `Spec.Correct`；
  - `Spec.ForwardCorrect`；
  - `Spec.ReverseCorrect`；
  - `Spec.ExplicitCorrectness`；
  - 含完整 `∃ assignment` 的方向目标。
- 允许在被标注为 `computational_leaf` 的 helper 中使用 `decide`；
- leaf 只能证明：
  - 一个具体 Bool 等式；
  - 一个具体 Fin 索引事实；
  - 一个固定 tuple 的 relation truth；
  - 一个固定 constraint 的 satisfaction；
  - 小型 list membership。
- leaf exact type 不得量化所有 tuple 或所有 assignment；
- final direction proof 必须显式引用 witness、invariant 和 case split helper；
- dependency audit 应识别 `of_decide_eq_true`、`native_decide` 等完整闭包形式。

如果无法可靠区分顶层和 leaf 计算，宁可先把该运行标记为
`AUTOMATION_ATTRIBUTION_UNCERTAIN`，不要误报为模型证明。

### 13.7 允许与禁止

允许：

- 冻结的显式 Gadget 作者化门禁 `Spec`；
- `FiniteFormula.Satisfies` 与 relation 基本定义；
- `Spec.OutputsAgree`；
- Bool、Fin、List 的基础引理；
- `simp`、`fin_cases`、`omega` 等局部工具；
- `correct_of_explicit`；
- 已证明的、与当前 gadget 无关的通用布尔恒等式。

禁止：

- `Spec.Correct` 的 Decidable instance直接闭包；
- 显式 Gadget 作者化门禁使用的 `by decide` correctness；
- 同一 gadget 的任何库内 `correct` theorem；
- 搜索器和 canonical gadget；
- 自动生成 witness assignment；
- 从有限 checker 导出完整 Lean proof；
- proof repair 修改 formula。

### 13.8 模型调用与 repair

调用 purpose：

- `gadget-proof-plan`
- `gadget-proof-forward-initial`
- `gadget-proof-reverse-initial`
- `gadget-proof-forward-repair`
- `gadget-proof-reverse-repair`
- `gadget-proof-assembly`

forward 与 reverse 使用独立预算和独立状态。一个方向通过后，另一个方向失败时必须保留
已验证 artifact，不得重新生成已通过方向。

repair 反馈只包含：

- 当前方向 exact type；
- frozen witness/invariant schema；
- Lean error；
- 未闭合 goals；
- 已允许的 lemma signatures。

不得返回 library 中同构 gadget 的完整 proof body。

### 13.9 贡献归因

每题至少产生以下 receipt：

- witness data/function；
- forward theorem；
- reverse theorem；
- explicit correctness assembly。

硬检查：

- 四项均有 model source hash；
- frozen gadget payload hash 一致；
- forward/reverse final-used；
- final `Spec.Correct` 依赖 `correct_of_explicit`；
- 无完整 decide closure；
- 无 formula drift；
- independent Lean replay；
- forbidden dependency 为 0。

### 13.10 case 分层

开发：

- q-b02；
- 一个固定基数 dev fixture；
- 一个双 relation dev fixture。

validation 建议选择：

- q-b05：组合不同 relation；
- q-b07：布尔互补；
- q-b10：固定基数对偶；
- q-b20：OR/XOR 混合。

heldout：

- 从 q-b11–q-b19 选择至少三个不同 Hamming weight；
- 从 q-b21–q-b30 选择至少三个随机关系；
- 完整的 Gadget 正确性证明门禁最终可扩展到显式 Gadget 作者化门禁的全部 27 个 required cases。

不能把同一证明模板在对偶题上的机械实例化计为两个独立 proof idea。报告必须同时给出：

- unique proof-plan hash 数；
- final-use instance 数；
- alpha-renaming/布尔对偶归一化后的重复数。

### 13.11 预算

建议每题：

- proof-plan 1 次；
- forward initial 1 次、repair 6 次；
- reverse initial 1 次、repair 8 次；
- assembly repair 2 次；
- `model_max_tokens = 24000`；
- `model_timeout_seconds = 480`；
- `lean_timeout_seconds = 900`；
- `max_lean_checks = 800`；
- `wall_clock_timeout_seconds = 7200`。

reverse 通常比 forward 困难，因此预算不对称。

### 13.12 测试

必须覆盖：

- witness hash 与 frozen gadget 不匹配；
- forward 通过、reverse 失败后 forward 被保留；
- proof repair 试图改变 formula；
- 顶层 `by decide` 被拒绝；
- leaf `decide` 被允许；
- final theorem 未依赖 witness；
- final theorem 未依赖 reverse helper；
- library correct theorem 被间接调用；
- 同一 proof plan 被多题重复实例化时 unique count 正确。

### 13.13 完成标准

- 显式 Gadget 作者化门禁已稳定；
- 至少一个非平凡 gadget 的 forward/reverse 均由模型证明；
- validation 四类关系全部有明确结果；
- 工程性 failure 与数学 proof failure 可区分；
- 完整 decide closure 为 0；
- final artifact 使用模型 proof；
- 独立重放和依赖审计通过。

## 14. 公式语义作者化门禁

### 14.1 研究问题

公式语义作者化门禁回答：

> 已知每个局部 gadget 正确时，模型能否构造全局 assignment 变换，并证明把每个源约束
> 替换成 gadget 后，整个 CSP 公式的可满足性双向保持？

当前 `PPDefinability.lean` 已包含完整通用证明：

- `witness`；
- `forwardAssignment`；
- `instantiate_satisfies_forward`；
- `instantiate_satisfies_reverse`；
- `interpret_satisfies_forward`；
- `interpret_satisfies_reverse`；
- `interpret_satisfiable_iff`。

当前 deterministic semantic compiler 也会直接生成方向 helper。因此 公式语义作者化门禁必须禁用
`boolean-csp-semantic-compiler`，否则模型仍不会生成最终数学证明。

### 14.2 通用能力不能按 27 题重复计数

公式语义定理对任意 `Γ'`、`Γ` 和 `LanguageInterpretation` 参数化。它本质上是一个
通用 theorem，而不是 27 个不同 theorem。

正式统计必须区分：

- `unique_model_generated_semantic_capability_count`；
- `semantic_final_use_instance_count`。

同一个模型生成通用 theorem 可以在 27 个 case 中实例化，但数学贡献只计一次，final-use
覆盖率可以计 27 次。

### 14.3 两个子级

#### 公式语义提升

禁止高层 theorem，但允许低层 assignment 和单块语义 primitive。

模型必须生成：

- formula-level reverse helper；
- formula-level forward helper；
- satisfiable iff。

允许复用：

- `forwardAssignment`；
- `forwardAssignment_source`；
- `forwardAssignment_fresh`；
- `instantiate_satisfies_forward`；
- `instantiate_satisfies_reverse`；
- `constraint_vars_le_formula_maxVar`；
- `List.mem_flatMap`。

公式语义提升 测试模型能否从局部 invariant 提升到列表/公式层面。它是较低风险的第一步。

#### Assignment Witness 作者化

在 公式语义提升 基础上进一步禁止：

- `witness`；
- `witness_spec`；
- `forwardAssignment`；
- `forwardAssignment_source`；
- `forwardAssignment_fresh`；
- `instantiate_satisfies_forward`；
- `instantiate_satisfies_reverse`。

模型必须自己定义：

- source 变量区域与 fresh 变量区域；
- 每个 source constraint 的局部 gadget witness；
- fresh variable key 的一致性；
- 不同 gadget block 辅助变量不冲突；
- forward assignment；
- reverse assignment/restriction；
- 单块和全公式语义。

Assignment Witness 作者化 才是完整的 assignment transformation 作者化门禁。

### 14.4 中性接口

建议新增一个不包含证明的接口：

```lean
structure InterpretationSemanticCertificate
    (interpretation : LanguageInterpretation Γ' Γ) where
  forwardMap :
    ∀ formula source,
      Formula.Satisfies formula source →
      SAT.Assignment
  forward :
    ∀ formula source sourceSatisfies,
      Formula.Satisfies (interpret interpretation formula)
        (forwardMap formula source sourceSatisfies)
  reverse :
    ∀ formula target,
      Formula.Satisfies (interpret interpretation formula) target →
      Formula.Satisfies formula target
```

允许一个中性 theorem 从该 structure 推出：

```lean
∀ formula,
  Formula.Satisfiable (interpret interpretation formula) ↔
  Formula.Satisfiable formula
```

公式语义提升 可以把 `forwardMap` 设为现有 `forwardAssignment`；Assignment Witness 作者化 要求
`forwardMap` 本身来自模型。

### 14.5 SemanticCapabilityPlan 扩展

复用已有 `SemanticCapabilityPlan`，增加：

```text
authoring_level = formula-lift | witness-authoring
witness_origin = library | model
fresh_variable_scheme
block_separation_invariant
source_region_invariant
forward_helper_id
reverse_helper_id
final_iff_helper_id
```

计划必须是 DAG：

```text
local witness
    ├── source-region agreement
    ├── fresh-region agreement
    └── block separation
              ↓
        forward direction

block extraction
              ↓
        reverse direction

forward + reverse
              ↓
        satisfiable iff
```

一个方向失败时保留另一个方向的 verified helper。

### 14.6 禁止声明

公式语义提升 禁止：

- `interpret_satisfiable_iff`；
- `interpret_satisfies_forward`；
- `interpret_satisfies_reverse`；
- 所有直接包装上述 theorem 的 case-specific iff；
- `boolean-csp-semantic-compiler`。

Assignment Witness 作者化 再禁止：

- `witness`；
- `witness_spec`；
- `forwardAssignment`；
- `forwardAssignment_source`；
- `forwardAssignment_fresh`；
- `instantiate_satisfies_forward`；
- `instantiate_satisfies_reverse`；
- 与这些声明等价的 transport wrapper。

允许：

- `instantiate`、`instantiateVar`、`freshVar` 的定义；
- gadget.correct；
- fresh key injectivity/above-reference 基础引理；
- formula/list membership 基础引理；
- Bool/Fin/Nat 基础库。

### 14.7 模型上下文

必须提供：

- `Gadget.correct` 和 `LanguageInterpretation` 签名；
- `instantiateVar`、`instantiate`、`interpret` 的定义；
- `freshVar` 及其 injectivity/region lemmas；
- `Formula.Satisfies`、`Formula.Satisfiable` 定义；
- `List.mem_flatMap` 等必要签名；
- 当前 authoring level；
- 禁止声明列表；
- exact helper types。

不得提供：

- 三个被禁高层 theorem 的 proof body；
- deterministic semantic compiler 生成的固定 proof text；
- 已生成的 generic semantic theorem；
- gold direction helper。

### 14.8 模型协议

新增或扩展 schema：

```json
{
  "schema": "boolean_csp_semantic_plan_v2",
  "authoring_level": "formula-lift | witness-authoring",
  "forward": {
    "assignment_definition": "...",
    "invariants": [],
    "helper_declarations": [],
    "proof_body": "..."
  },
  "reverse": {
    "assignment_recovery": "...",
    "invariants": [],
    "helper_declarations": [],
    "proof_body": "..."
  },
  "final_iff": {
    "proof_body": "..."
  }
}
```

在 Assignment Witness 作者化 中，`assignment_definition` 不能为空且 origin 必须为 model。

### 14.9 component 与 final-use

组件目标是生成一个通用：

```lean
noncomputable def authoredInterpretationSemantics
    {Γ' Γ : Gamma}
    (interpretation : LanguageInterpretation Γ' Γ) :
    InterpretationSemanticCertificate interpretation := ...
```

然后从该 certificate 得到通用 satisfiable iff。

端到端检查：

- q-b02 canary；
- q-b05–q-b10 validation；
- q-b11–q-b30 heldout；
- 27 个 required case 的显式 NP-hardness packaging 均使用该 model-generated theorem。

锚点题不计 final-use coverage。

### 14.10 评估器

硬检查：

- unique generic semantic capability 至少 1；
- contribution class 为 `MODEL_GENERATED_CAPABILITY`；
- Assignment Witness 作者化 时 witness origin 为 model；
- forward、reverse、iff 三个 helper final-used；
- deterministic semantic compiler receipt 为 0；
- 被禁 theorem dependency 为 0；
- 27 个 required case 的 final-use coverage 完整；
- 不把 27 次实例化计为 27 个 unique capability；
- independent Lean replay；
- sibling direction preservation 生效。

失败分类：

- `SEMANTIC_PLAN_INVALID`
- `FORWARD_ASSIGNMENT_INVALID`
- `FRESH_VARIABLE_COLLISION`
- `FORWARD_BLOCK_PROOF_FAILED`
- `REVERSE_BLOCK_EXTRACTION_FAILED`
- `IFF_ASSEMBLY_FAILED`
- `GENERICITY_LOST`
- `SEMANTIC_NOT_FINAL_USED`

`GENERICITY_LOST` 表示模型只证明了某个具体 case，而 gate 要求通用 theorem。

### 14.11 测试

必须覆盖：

- 只有 forward；
- 只有 reverse；
- final iff 未引用两个方向；
- forwardMap 偷用 library `forwardAssignment`（Assignment Witness 作者化）；
- fresh key 在两个 source constraint 间冲突；
- reverse 只证明单个 block；
- theorem 对固定 Γ 有效但没有泛化；
- deterministic compiler 仍产生 action；
- 一个 generic theorem 在 27 题复用时 unique count 为 1；
- 某个 case 没有 final-use 时 coverage 失败。

### 14.12 预算与 rollout

公式语义提升：

- model tokens 20000；
- forward/reverse 各 5 次 repair；
- Lean checks 600；
- wall time 5400 秒。

Assignment Witness 作者化：

- model tokens 32000；
- witness 4 次 repair；
- forward 8 次 repair；
- reverse 8 次 repair；
- Lean checks 1200；
- wall time 10800 秒。

实施顺序：

1. synthetic two-constraint formula；
2. q-b02 interpretation；
3. generic 公式语义提升；
4. validation final-use；
5. generic Assignment Witness 作者化；
6. heldout final-use。

### 14.13 完成标准

- semantic compiler 在门禁中不可见；
- 至少一个 generic model-authored semantic certificate verified；
- Assignment Witness 作者化 的 assignment transformation 来自模型；
- forward/reverse 都 final-used；
- 27 个 required case 使用同一个经过审计的 generic capability；
- unique contribution 与实例化次数正确区分；
- forbidden dependency 和独立重放全部通过。

## 15. Direct-TM 复杂度作者化门禁

### 15.1 研究问题

Direct-TM 复杂度作者化门禁回答：

> 模型能否把 pp-substitution 写成一个明确的 code-level 程序 DAG，证明该程序按输入公式
> 规模多项式运行，并把 code-level 程序正确运输回语义上的 `interpret`？

只禁止 `interpretation_tmPolyTime` 不够。当前 deterministic compiler 会自动生成：

- formula encoding helper；
- `interpretCode_tmPolyTime` 的 composition；
- endpoint equality；
- `formula_tmPolyTime_of_code` transport。

这种运行主要测试 fixed compiler，不测试模型复杂度推理。

### 15.2 复杂度数学载荷

Direct-TM 复杂度作者化门禁的实质内容至少包括：

- 程序节点及数据流；
- 每个 source constraint 产生的 target block；
- list map/flatMap/flatten 的组合；
- fresh variable 编码的增长；
- 约束数量界；
- 编码长度或最大变量编号的多项式界；
- 最终 `TMPolyTimeMap`。

仅从已有 `TMPolyTimeMap` 投影 `outputSizeBound` 不算模型生成了尺寸分析。模型必须先给出
一个独立、可读的组合界。

### 15.3 建议新增中性尺寸接口

```lean
def maxGadgetConstraintCount
    (interpretation : LanguageInterpretation Γ' Γ) : Nat := ...

def maxGadgetVariable
    (interpretation : LanguageInterpretation Γ' Γ) : Nat := ...

structure InterpretationGrowthCertificate
    (interpretation : LanguageInterpretation Γ' Γ) where
  constraintBound : Nat
  variableDegree : Nat
  constraint_count :
    ∀ formula,
      (interpret interpretation formula).length ≤
        constraintBound * formula.length
  variable_bound :
    ∀ formula constraint,
      constraint ∈ interpret interpretation formula →
      Constraint.maxVar constraint ≤
        growthPolynomial variableDegree
          (Formula.maxVar formula + formula.length + 1)
```

定义与 generic aggregation 可以由库提供；具体 bound 值与证明必须由模型生成。

### 15.4 三个子级

#### Direct-TM API 校准

只禁 `interpretation_tmPolyTime`，允许 `interpretCode_tmPolyTime`、
`interpretCode_eq_formulaCode` 和 `formula_tmPolyTime_of_code`。

该级只校准 authoring/Lean API，不计“复杂度数学能力”正式得分。

#### 程序 DAG 与增长界

正式推荐级别。

禁止：

- `interpretation_tmPolyTime`；
- `interpretCode_tmPolyTime`；
- automatic direct-TM compiler；
- automatic reduction packager。

允许：

- `instantiateCode_tmPolyTime`；
- `codeMaxVar_tmPolyTime`；
- list map、context map、flatten 的通用 TM primitive；
- `interpretCode_eq_formulaCode`；
- `formula_tmPolyTime_of_code`；
- encoding equivalence primitive。

模型必须生成：

- `InterpretationGrowthCertificate`；
- code-level program DAG；
- `interpretCode` 的 TM proof；
- final semantic `interpret` TM proof。

#### 底层解释器编译证明

进一步禁止：

- `instantiateCode_tmPolyTime`；
- `instantiateRow_tmPolyTime`；
- `instantiateVarCode_tmPolyTime`；
- `rowsByCode_tmPolyTime`；
- `interpretCode_eq_formulaCode`；
- `formula_tmPolyTime_of_code`。

模型必须从 pair、Nat arithmetic、list lookup、map、fold、flatten 和 encoding transport 等
更低层 primitive 重建完整 compiler。

底层解释器编译证明 很可能达到数百行，只在 程序 DAG 与增长界 稳定后做一个 generic canary。

### 15.5 DirectTMCapabilityPlan 扩展

已有 `DirectTMCapabilityPlan` 和 `TypedProgramNode` 可以复用。增加：

```text
authoring_level
node_origin
growth_certificate_id
growth_bound_dependencies
program_node_source_hash
endpoint_equality_origin
transport_origin
```

每个 node 必须标注：

- `library-primitive`；
- `model-authored-helper`；
- `deterministic-syntax-only`。

程序 DAG 与增长界 的核心 code node 和 growth certificate 必须是
`model-authored-helper`。

### 15.6 模型协议

```json
{
  "schema": "boolean_csp_direct_tm_plan_v2",
  "authoring_level": "program-dag-growth | low-level-compiler",
  "growth_certificate": {
    "constraint_bound": "...",
    "variable_bound": "...",
    "proof_helpers": []
  },
  "nodes": [
    {
      "node_id": "...",
      "operation": "map | flatMap | flatten | composition | transport",
      "exact_type": "...",
      "dependencies": [],
      "primitive_declarations": [],
      "proof_body": "..."
    }
  ],
  "final_node_id": "...",
  "endpoint_equality": {
    "origin": "library | model",
    "proof_body": "..."
  }
}
```

runtime 只验证 DAG、冻结 exact types 并逐节点调用 Lean，不得替模型选择 program node。

### 15.7 禁止与允许

程序 DAG 与增长界 必须禁用：

- `boolean-csp-direct-tm-compiler`；
- `interpretation_tmPolyTime`；
- `interpretCode_tmPolyTime`；
- `certifiedReduction_of_interpretation_auto`；
- `nPHard_of_interpretation_auto`；
- 所有直接提供目标 exact `TMPolyTimeMap` 的 wrapper。

保留：

- semantic theorem 或公式语义作者化门禁输出；
- `TMPolyTimeMap.comp`、`prod_mk`、`list_map`；
- context-list map；
- flatten；
- Nat pair/add/lookup primitive；
- `PolyProg` compiler；
- 程序 DAG 与增长界 指定的 code/semantic endpoint bridge。

### 15.8 节点级 authoring 与 repair

节点按拓扑顺序生成：

1. formula encoding；
2. reference/max-var；
3. per-constraint block；
4. context attachment；
5. list map；
6. flatten；
7. code endpoint；
8. semantic transport。

一个节点 verified 后写入 capability store。后续节点失败不能重写已通过节点，除非
Planner 明确发出 replan 并使所有下游 artifact 失效。

repair 只接收：

- 当前 node exact type；
- 已验证 dependency signatures；
- Lean error；
- 允许 primitive；
- growth invariant。

不得接收完整 `InterpretCompiler.lean` proof body。

### 15.9 通用 capability 与 27 题 final-use

与 公式语义作者化门禁相同，Direct-TM 复杂度作者化门禁目标是一个 generic theorem：

```lean
∀ {Γ' Γ} (interpretation : LanguageInterpretation Γ' Γ),
  TMPolyTimeMap ... (interpret interpretation)
```

正式统计：

- unique model-generated direct-TM capability；
- generated node 数；
- model-authored node 数；
- library primitive node 数；
- 27 个 case 的 final-use 实例数。

不能把同一 generic theorem 的 27 次实例化计成 27 次复杂度发现。

### 15.10 评估器

程序 DAG 与增长界 硬检查：

- direct-TM deterministic compiler receipt 为 0；
- generic direct-TM theorem model-generated；
- growth certificate model-generated 且 final-used；
- `interpretCode_tmPolyTime` forbidden dependency 为 0；
- code node DAG acyclic、类型一致；
- 至少一个非平凡 list map/flatten node 来自模型；
- final semantic transport verified；
- 27 个 required case final-use；
- unique/instance count 分离；
- independent Lean replay。

失败分类：

- `PROGRAM_DAG_INVALID`
- `MISSING_GROWTH_BOUND`
- `GROWTH_BOUND_FALSE`
- `NODE_TYPE_MISMATCH`
- `PRIMITIVE_NOT_ALLOWED`
- `NODE_PROOF_FAILED`
- `ENDPOINT_EQUALITY_FAILED`
- `DIRECT_TM_NOT_FINAL_USED`
- `DETERMINISTIC_COMPILER_LEAK`

### 15.11 测试

必须覆盖：

- DAG cycle；
- dependency 缺失；
- input/output encoded type 不匹配；
- renderer 自动插入 node；
- growth certificate 未被 final theorem 使用；
- 只调用被禁 `interpretCode_tmPolyTime`；
- final theorem 与 code node function 不一致；
- node verified 后 sibling failure preservation；
- generic theorem 只对固定 Γ 成立；
- 27 次实例化的 unique count 为 1。

### 15.12 预算

程序 DAG 与增长界：

- planner 2 次；
- growth certificate 6 次 authoring/repair；
- 每个 program node 4 次 repair；
- model tokens 28000；
- Lean checks 1200；
- wall time 10800 秒。

底层解释器编译证明：

- model tokens 48000；
- Lean checks 2400；
- wall time 21600 秒；
- 只运行一个 generic canary。

### 15.13 完成标准

- deterministic direct-TM compiler 在门禁中不可见；
- 一个 generic model-authored direct-TM theorem verified；
- 一个显式增长证书 final-used；
- 程序 DAG 与增长界 code DAG 的核心节点来自模型；
- 27 个 required case 复用该 theorem 完成 root proof；
- 无 high-level direct-TM closure 依赖；
- 独立重放通过。

## 16. 源 NP-hard 归约作者化门禁

### 16.1 研究问题

源 NP-hard 归约作者化门禁回答：

> 在只保留 Cook–Levin/3SAT hardness 锚点和中性程序、证书接口时，模型能否发明并形式化
> 3SAT 到一个 Boolean CSP hard core 的完整多项式时间 many-one reduction？

源 NP-hard 归约作者化门禁的数学对象不再是局部 pp-gadget，而是：

- 全局变量编码；
- 每个 clause 的替换块；
- 可能共享的 reference/constant 变量；
- 新辅助变量分配；
- forward assignment；
- reverse assignment；
- clause 与全公式正确性；
- 多项式规模/时间；
- 精确 endpoint 的 `CertifiedReduction`。

### 16.2 不能只禁两个 hardness theorem

只禁 `nae3CoreNPHard` 和 `oneInThreeCoreNPHard` 不够。当前库还存在：

- `nae3CoreReduction`；
- `ThreeSATToNAEThreeSAT.executable`；
- `ThreeSATToNAEThreeSAT.executable_correct`；
- `ThreeSATToNAEThreeSAT.executable_tmPolyTime`；
- `BooleanCSPAuthoringSources.PositiveNAE3CSP.*`；
- `threeSATToPositiveNAE3CSPIngress`；
- `GraphColoringToOneInThree.*` 的完整 route；
- ExactCover/GraphColoring 等可到达 1-IN-3 的完整 route；
- 多个 transport wrapper。

源 NP-hard 归约作者化门禁必须执行 route-level quarantine：

- prompt 不暴露上述 proof body；
- theorem index 不提供这些 exact/conditional closure；
- final dependency audit 禁止整个完整 route；
- 只通过 answer-free facade 暴露 source/target 数据定义和基础语义。

### 16.3 两条门禁

#### 3SAT→NAE-3 源归约

正式第一个 canary。

模型需要发现类似以下数学问题的解，而不是获得答案：

- 如何用一个全局 reference bit 表示 literal polarity；
- 如何把三文字析取转成 NAE 条件；
- 如何把可能出现的 NAE-4 block 拆成 NAE-3；
- 如何给每个 clause 分配互不冲突的辅助变量；
- satisfying assignment 如何扩展；
- target assignment 如何恢复 source truth assignment，必要时处理全局 complement。

精确目标建议是：

```lean
CertifiedReduction
  ThreeSATSourceProblem
  (cspOf nae3Core)
```

source endpoint 必须与 Cook–Levin hardness 锚点精确兼容。

#### 3SAT→1-IN-3 源归约

分两步实施。

第一步允许组合：

```text
模型生成的 3SAT → NAE-3 reduction
        +
模型生成的 NAE-3 → 1-IN-3 interpretation/gadget
```

两段都必须来自当前或受信任的先前 model-authored artifact，不能复用现成
`oneInThreeCoreNPHard`。

第二步 `直接 3SAT→1-IN-3 源归约扩展` 再要求模型直接给出 3SAT clause 到 1-IN-3 blocks 的 reduction。
direct 版本是高风险扩展，不作为 源 NP-hard 归约作者化门禁初始完成条件。

### 16.4 分离组合数学与证书样板

源 NP-hard 归约作者化门禁允许：

- `CertifiedReduction` structure；
- `CertifiedReduction.comp`；
- `NativeTMNPHard.alongPath`；
- `PolyProg` 和通用 compiler；
- generic list/map/flatMap TM primitive。

这些包装器在 证书与 Hardness 量词作者化门禁才禁。

因此 源 NP-hard 归约作者化门禁评分只关注：

- reduction program；
- assignment transformations；
- semantic correctness；
- size/time evidence。

root hardness theorem 可以是 hybrid packaging，但上述四项必须有 final-used
`MODEL_GENERATED_CAPABILITY` receipt。

### 16.5 Answer-free facade

新增专用接口模块，只暴露：

- 3CNF/ThreeSATLike input type；
- clause、literal 和 satisfaction 定义；
- target `nae3Core` / `oneInThreeCore` 的 relation 定义；
- formula/constraint constructors；
- encoded endpoint；
- Bool、List、Nat 的中性基础引理；
- Cook–Levin source hardness declaration的签名。

不得暴露：

- 现有 executable；
- literalKey/referenceVar/splitWitness 的答案性定义；
- existing assignment transformation；
- existing correctness proof；
- route-specific helper names；
- 完整 TM proof。

Lean import closure中这些声明可能仍存在，因此最终还必须靠 forbidden dependency audit，
不能只依赖 prompt 隐藏。

### 16.6 ReductionPlan 协议

```json
{
  "schema": "boolean_csp_source_reduction_plan_v1",
  "route": "three_sat_to_nae3 | three_sat_to_one_in_three",
  "variable_layout": {
    "source_variables": "...",
    "global_variables": [],
    "per_clause_auxiliary_variables": "...",
    "injectivity_invariants": []
  },
  "clause_blocks": [
    {
      "case": "polarity/shape selector",
      "target_constraints": [],
      "local_correctness_statement": "..."
    }
  ],
  "program": {
    "definition_body": "...",
    "program_dag": []
  },
  "forward_assignment": {
    "definition_body": "...",
    "invariants": []
  },
  "reverse_assignment": {
    "definition_body": "...",
    "invariants": []
  },
  "semantic_helpers": [],
  "growth_bound": {},
  "proof_dag": []
}
```

Planner 可以要求 replan，但 deterministic runtime 不得生成 clause block。

### 16.7 局部 verifier

允许一个 answer-free checker 验证模型给出的单个 clause block：

- 枚举 source clause 的有限 literal truth values；
- 枚举模型声明的局部辅助变量；
- 检查局部 iff；
- 返回 false-positive/false-negative row。

checker 不验证全局 variable collision，也不生成新 block。全局 injectivity、共享 reference
和 formula correctness 必须由 Lean proof。

### 16.8 必需 artifact DAG

3SAT→NAE-3 源归约 至少生成：

1. variable layout；
2. clause block constructor；
3. clause block local correctness；
4. whole-formula executable；
5. forward assignment；
6. forward semantics；
7. reverse assignment或读取规则；
8. reverse semantics；
9. growth bound；
10. direct-TM / `PolyProg`；
11. `CertifiedReduction`；
12. root hardness transport。

每个 substantive artifact 记录独立 source hash。后续节点失败时，已验证的上游节点保留。

### 16.9 禁止策略

3SAT→NAE-3 源归约 至少禁止：

- `nae3CoreReduction`；
- `nae3CoreNPHard`；
- `ThreeSATToNAEThreeSAT` 中完整 executable、correctness、TM 和 certificate；
- `PositiveNAE3CSP` 中对应完整声明；
- `threeSATToPositiveNAE3CSPIngress`；
- 能从这些 route 直接推出目标的 wrapper。

3SAT→1-IN-3 源归约 再禁止：

- `oneInThreeCoreNPHard`；
- `GraphColoringToOneInThree.oneInThreeCoreNPHard`；
- GraphColoring→1-IN-3 完整 executable/correctness/TM route；
- ExactCover→1-IN-3 完整 route；
- 现成 NAE/1-IN-3 interpretation；
- 能形成同一目标的 complete path。

应使用“exact route dependency set + 动态 closure filter”，不要只维护两个 theorem 名。

### 16.10 模型上下文与泄漏控制

模型可以看到：

- source/target 的公开自然语言定义；
- exact Lean types；
- local checker 反例；
- 中性 constructor/primitive signatures；
- proof obligation DAG；
- 已验证的本次运行 helper signatures。

模型不能看到：

- 现有 route 的声明名提示；
- 现有 clause block 数量；
- 现有 auxiliary layout；
- 现有 witness function；
- gold program；
- 其他模型运行中成功的源 NP-hard 归约作者化门禁计划。

源 NP-hard 归约作者化门禁的 heldout 变体可对 literal 坐标、clause 顺序、变量编码 facade 做语义保持的重命名，降低
代码记忆的作用。

### 16.11 evaluator

3SAT→NAE-3 源归约 硬检查：

- Cook–Levin/3SAT source hardness是允许的唯一 hardness anchor；
- model-authored program final-used；
- model-authored forward/reverse semantics final-used；
- model-authored growth/complexity evidence final-used，或明确由模型 program 的通用 compiler
  合法投影；
- existing NAE route dependency 为 0；
- root `NativeTMNPHard (cspOf nae3Core)` verified；
- independent replay。

3SAT→1-IN-3 源归约 硬检查：

- NAE3/1-IN-3 两个新段的来源均可追踪；
- 不依赖现成 oneInThree hardness；
- composition 的 dependency DAG 完整；
- root `NativeTMNPHard (cspOf oneInThreeCore)` verified。

失败分类：

- `REDUCTION_PLAN_INVALID`
- `CLAUSE_GADGET_COUNTEREXAMPLE`
- `VARIABLE_LAYOUT_COLLISION`
- `FORWARD_SEMANTIC_FAILURE`
- `REVERSE_SEMANTIC_FAILURE`
- `GLOBAL_COMPLEMENT_ARGUMENT_MISSING`
- `GROWTH_BOUND_MISSING`
- `SOURCE_ENDPOINT_MISMATCH`
- `EXISTING_ROUTE_LEAK`
- `CERTIFIED_REDUCTION_NOT_FINAL_USED`

### 16.12 测试

必须覆盖：

- 一个局部 clause block 正确但全局 auxiliary key 冲突；
- forward 正确、reverse 错误；
- reference bit complement 情形遗漏；
- source endpoint presentation 不一致；
- program 与 semantic theorem 使用不同 executable；
- growth theorem针对另一个 program；
- existing route 经 wrapper 间接泄漏；
- 3SAT→1-IN-3 源归约 只有一段 model-authored；
- local checker 试图自动修复 block；
- root artifact 未使用 authored reduction。

### 16.13 rollout 与预算

3SAT→NAE-3 源归约 阶段：

1. clause block plan only；
2. local finite verification；
3. executable；
4. forward semantics；
5. reverse semantics；
6. complexity；
7. certificate/root。

预算建议：

- plan 3 次；
- clause block repair 8 次；
- forward 10 次；
- reverse 12 次；
- complexity 8 次；
- certificate 4 次；
- model tokens 48000；
- Lean checks 2400；
- wall time 21600 秒。

3SAT→1-IN-3 源归约 composition 预算可在 3SAT→NAE-3 源归约 基础上增加 50%。

### 16.14 完成标准

源 NP-hard 归约作者化门禁的初始完成要求：

- 3SAT→NAE-3 源归约 完整通过；
- 3SAT→1-IN-3 源归约 composition 通过；
- 两条 root hardness artifact verified；
- existing complete route dependency 为 0；
- program、语义和复杂度来源清晰；
- 直接 3SAT→1-IN-3 源归约扩展 可以保持为后续扩展。

源 NP-hard 归约作者化门禁不对 30 个 target language 重复运行。30 题用于局部 Gadget、
公式语义和复杂度门禁；本门禁只测试 source hard-core 归约的生成。

## 17. 证书与 Hardness 量词作者化门禁

### 17.1 定位

证书与 Hardness 量词作者化门禁测试：

> 模型是否理解本库的精确 endpoint、`PolyProg`、`CertifiedReduction` 和
> `NativeTMNPHard` 定义，并能在没有通用组装器时手工闭合证书？

证书与 Hardness 量词作者化门禁主要是 formal framework authoring，不应计入“新数学构造”总分。

### 17.2 冻结输入

证书与 Hardness 量词作者化门禁不允许模型同时重新发明 gadget、semantic 或 TM 程序。输入必须是前级已经验证的：

- source hardness；
- source→target `CertifiedReduction` 或其 program + correctness；
- exact source/target presentations；
- program endpoint equality。

证书与 Hardness 量词作者化门禁只负责重新组装证书和 hardness 的全称量词。

### 17.3 三个子级

#### CertifiedReduction 记录构造

给定：

- 一个 `TMPolyTimeMap`；
- 对应 executable；
- exact semantic iff。

禁止：

- `certifiedReduction_of_interpretation`；
- `certifiedReduction_of_interpretation_explicit`；
- `certifiedReduction_of_interpretation_auto`；
- 其他 target-specific certificate constructor。

模型必须自己构造：

```lean
{
  program := .atom (Primitive.ofTMPolyTime executable directTM)
  correct := ...
}
```

并证明 `program.run` 与 semantic theorem 使用同一 executable。

#### CertifiedReduction 手工组合

给定：

- `before : CertifiedReduction source middle`；
- `after : CertifiedReduction middle target`。

禁止：

- `CertifiedReduction.comp`；
- `CertifiedPath.toCertifiedReduction`；
- path composition wrapper。

模型必须自己构造：

```lean
{
  program := .comp after.program before.program
  correct := by
    intro input
    exact (before.correct input).trans
      (after.correct (before.program.run input))
}
```

正式测试不向模型提供上述完整 body，只提供 structure 和 field signatures。

#### NativeTMNPHard 手工运输

给定：

- `coreHardness : NativeTMNPHard core`；
- `step : CertifiedReduction core target`。

禁止：

- `nPHard_of_interpretation`；
- `nPHard_of_interpretation_explicit`；
- `nPHard_of_interpretation_auto`；
- `NativeTMNPHard.alongPath`；
- `NativeTMNPHard.ofCompleteAlongPath`；
- `CompletenessTransport.alongPath`；
- `CertifiedReduction.comp`；
- RuleKernel/FinalCheck 的 hardness transport wrapper。

模型必须展开：

```lean
∀ source : PresentedProblem,
  NativeTMInNP source →
  Nonempty (CertifiedReduction source target)
```

对任意 source：

- 调用 `coreHardness source sourceMembership`；
- 取出 source→core reduction；
- 手工构造 source→target program composition；
- 手工证明 correctness transitivity；
- 放回 `Nonempty`。

### 17.4 Gate artifact

建议先生成一个 generic theorem：

```lean
theorem authored_hardness_transport
    {core target : PresentedProblem}
    (coreHardness : NativeTMNPHard core)
    (step : CertifiedReduction core target) :
    NativeTMNPHard target := ...
```

随后在 27 个 Boolean CSP required case 中实例化，验证 final-use。

同样只计：

- 1 个 unique generic certificate theorem；
- 27 个 final-use instances。

### 17.5 贡献分类

证书与 Hardness 量词作者化门禁默认应分类为：

- `GENERATED_GLUE`，若只展开 record 和量词；
- `MODEL_GENERATED_CAPABILITY`，仅当模型还生成了新的可复用证书 combinator，
  且该 combinator 超出单次目标样板。

报告必须增加：

```text
authorship_category = formal-certificate-assembly
mathematical_novelty_credit = 0
```

不得把 证书与 Hardness 量词作者化门禁成功加入 gadget、semantic 或 reduction 数学能力分数。

### 17.6 模型协议

```json
{
  "schema": "certificate_assembly_plan_v1",
  "level": "reduction-record | reduction-composition | hardness-transport",
  "binders": [],
  "input_certificates": [],
  "program_expression": "...",
  "semantic_chain": [],
  "nonempty_elimination": "...",
  "proof_body": "..."
}
```

runtime 冻结 binders 和 exact endpoints。模型不得更换 source、middle 或 target。

### 17.7 允许与禁止

允许：

- `CertifiedReduction` structure及字段投影；
- `PolyProg.atom`、`PolyProg.comp`；
- `Primitive.ofTMPolyTime`；
- `Iff.trans`；
- `Nonempty` 的构造与消去；
- `NativeTMNPHard` 定义；
- 已冻结的 program/semantic/direct-TM capability。

禁止：

- 所有高层 reduction/hardness composition；
- exact endpoint 自动 transport；
- theorem search 找到等价 generic transport；
- deterministic certificate compiler；
- 修改冻结 program；
- 使用不同 semantic theorem。

### 17.8 evaluator

硬检查：

- generic theorem body model-authored；
- forbidden packager dependency 为 0；
- `CertifiedReduction.comp` dependency 为 0；
- `NativeTMNPHard.alongPath` dependency 为 0；
- exact source/middle/target 一致；
- program composition final-used；
- correctness chain包含 before 与 after；
- 27 个 required case final-use；
- unique contribution count 为 1；
- contribution 不计数学 novelty；
- independent replay。

失败分类：

- `CERTIFICATE_ENDPOINT_MISMATCH`
- `PROGRAM_SEMANTIC_MISMATCH`
- `NONEMPTY_ELIMINATION_FAILED`
- `HARDNESS_QUANTIFIER_NOT_UNFOLDED`
- `FORBIDDEN_PACKAGER_USED`
- `CERTIFICATE_NOT_FINAL_USED`
- `NOVELTY_MISCLASSIFIED`

### 17.9 测试

必须覆盖：

- source/middle endpoint 对不上；
- program 用 after∘before，但 correctness 写反；
- semantic theorem针对不同 executable；
- 忘记 `Nonempty`；
- 偷用 `CertifiedReduction.comp`；
- 偷用 `alongPath`；
- generic theorem只对一个具体 target；
- 27 次实例化被错误计成 27 个数学贡献；
- 证书与 Hardness 量词作者化门禁的 contribution 被错误加入 novelty score。

### 17.10 预算

CertifiedReduction 记录构造：

- model tokens 12000；
- repair 4 次；
- Lean checks 200。

CertifiedReduction 手工组合：

- model tokens 12000；
- repair 4 次；
- Lean checks 250。

NativeTMNPHard 手工运输：

- model tokens 18000；
- repair 6 次；
- Lean checks 400；
- wall time 3600 秒。

### 17.11 完成标准

- CertifiedReduction 记录构造、CertifiedReduction 手工组合、NativeTMNPHard 手工运输 各有一个 generic verified artifact；
- 所有高层 packager 禁令生效；
- 27 个 required case 能使用 NativeTMNPHard 手工运输 artifact 完成 final packaging；
- unique/instance count 正确；
- formal authoring 与 mathematical novelty 分数严格分离；
- independent replay 和 endpoint audit 通过。

## 18. 报告与产物

### 18.1 报告命名

- `Reports/GENERAL_AGENT_BOOLEAN_CSP_GADGET_AUTHORING_DEV_REAL_API_REPORT.json`
- `Reports/GENERAL_AGENT_BOOLEAN_CSP_GADGET_AUTHORING_VALIDATION_REAL_API_REPORT.json`
- `Reports/GENERAL_AGENT_BOOLEAN_CSP_GADGET_AUTHORING_HELDOUT_REAL_API_REPORT.json`
- `Reports/GENERAL_AGENT_BOOLEAN_CSP_GADGET_AUTHORING_FULL_REAL_API_REPORT.json`
- `Reports/GENERAL_AGENT_BOOLEAN_CSP_GADGET_PROOF_REAL_API_REPORT.json`
- `Reports/GENERAL_AGENT_BOOLEAN_CSP_FORMULA_SEMANTIC_REAL_API_REPORT.json`
- `Reports/GENERAL_AGENT_BOOLEAN_CSP_ASSIGNMENT_WITNESS_AUTHORING_REAL_API_REPORT.json`
- `Reports/GENERAL_AGENT_BOOLEAN_CSP_DIRECT_TM_PROGRAM_DAG_REAL_API_REPORT.json`
- `Reports/GENERAL_AGENT_BOOLEAN_CSP_DIRECT_TM_LOW_LEVEL_COMPILER_REAL_API_REPORT.json`
- `Reports/GENERAL_AGENT_BOOLEAN_CSP_THREE_SAT_TO_NAE3_REAL_API_REPORT.json`
- `Reports/GENERAL_AGENT_BOOLEAN_CSP_THREE_SAT_TO_ONE_IN_THREE_REAL_API_REPORT.json`
- `Reports/GENERAL_AGENT_BOOLEAN_CSP_CERTIFICATE_ASSEMBLY_REAL_API_REPORT.json`

每份报告还必须有不可变 run manifest：

```text
gate_name
gate_version
policy_sha256
suite_sha256
source_commit
model_name
model_parameters
prompt_template_sha256
renderer/checker/compiler versions
forbidden declaration set sha256
allowed primitive set sha256
start/end timestamp
```

### 18.2 通用逐项记录

对 case-based gate，每题至少记录：

- case ID 与 split；
- source core；
- exact capability type；
- model call purpose/status/usage；
- plan、brief、prompt 和 policy hashes；
- 每次模型 semantic/proof/program payload hash；
- gate-specific 数学对象统计；
- checker 或 Lean 反例；
- Lean attempt 结果；
- generated declarations 与 dependency DAG；
- contribution class；
- unique capability ID；
- final-use instance ID；
- final-use dependency path；
- forbidden audit；
- independent replay；
- 最终 failure class。

对 generic theorem gate，必须记录：

- generic exact type；
- genericity audit；
- unique source hash；
- 参数化变量；
- 每个 benchmark instance 的实例化目标；
- unique contribution count；
- final-use instance count；
- duplicate/alpha-equivalent artifact count。

### 18.3 分层指标

显式 Gadget 作者化门禁：

- anchor 通过数；
- required case 数；
- model-authored gadget final-used 数；
- deterministic/hybrid 数；
- 平均/中位约束数和辅助变量数；
- 与已知模板的相似度诊断；

Gadget 正确性证明门禁：

- witness、forward、reverse、assembly 通过数；
- whole-goal decide closure 数；
- unique proof-plan 数；
- proof helper 数；
- formula drift 数。

公式语义作者化门禁：

- unique generic semantic capability 数；
- forward/reverse 独立通过率；
- model-authored assignment transformation 数；
- fresh-variable invariant failure 数；
- 27 题 final-use coverage。

Direct-TM 复杂度作者化门禁：

- unique generic direct-TM capability 数；
- model-authored program node 数；
- library primitive node 数；
- growth certificate 数；
- failed DAG node 分布；
- 27 题 final-use coverage。

源 NP-hard 归约作者化门禁：

- clause block、program、forward、reverse、growth、certificate 分阶段通过情况；
- local counterexample 数；
- route leak 数；
- source endpoint mismatch 数。

证书与 Hardness 量词作者化门禁：

- reduction-record、composition、hardness-transport 通过情况；
- endpoint mismatch 数；
- forbidden packager 使用数；
- formal glue 数；
- mathematical novelty credit 固定为 0。

### 18.4 suite 汇总

所有报告至少给出：

- route、数学、Lean、预算、系统失败数；
- initial 成功与 repair 成功数；
- model、hybrid、deterministic、reuse、glue 贡献数；
- unique capability 与 final-use instance 数；
- exact duplicate payload 数；
- forbidden direct/transitive dependency 数；
- integrity checks；
- strict gate result；
- partial capability score。

相似度只做诊断，不做硬条件。

### 18.5 预计代码改动点

通用 policy 与 evaluator：

- `agent/generative_reduction/capability_gate_policy.py`；
- `agent/generative_reduction/boolean_csp_capability_gate.py`；
- `agent/generative_reduction/orchestrator.py`；
- `agent/generative_reduction/models.py`；
- `agent/generative_reduction/generator_protocol.py`。

显式 Gadget 作者化门禁/Gadget 正确性证明门禁：

- `agent/generative_reduction/plugins/boolean_csp.py`；
- 新增 Boolean CSP gadget plan/checker/renderer 模块；
- `Lean/Reference/ComplexityReduction/Agent/GenerativeReduction/Plugins/BooleanCSPFiniteGadget.lean`
  或新增独立 authoring interface；
- `agent/generative_reduction/model/authoring.py`。

公式语义作者化门禁：

- `agent/generative_reduction/capability_compilers.py` 中保留 production compiler，但 gate
  policy 禁用其 action；
- 扩展 `SemanticCapabilityPlan`；
- 新增 semantic authoring provider 和方向级 repair；
- 新增 genericity/final-use evaluator。

Direct-TM 复杂度作者化门禁：

- 扩展 `DirectTMCapabilityPlan` 与 `TypedProgramNode`；
- 新增 growth certificate authoring；
- 新增 node-level model provider；
- 在 `InterpretCompiler.lean` 附近增加中性 growth interface，不能加入答案性 theorem。

源 NP-hard 归约作者化门禁：

- 新增 answer-free Lean facade；
- 新增 source-reduction plan/parser/checker；
- 新增 artifact DAG runner；
- 新增 route-level forbidden dependency builder；
- 新增 3SAT→NAE-3 源归约/3SAT→1-IN-3 源归约 evaluator。

证书与 Hardness 量词作者化门禁：

- 新增 certificate assembly plan；
- 新增 endpoint binder validator；
- 新增 generic CertifiedReduction 记录构造/CertifiedReduction 手工组合/NativeTMNPHard 手工运输 authoring runner；
- 扩展 contribution report，以区分 formal glue 和 mathematical novelty。

测试：

- 扩展 `tests/test_generative_reduction.py`；
- 复杂 gate 建议拆分为
  `tests/test_boolean_csp_gadget_gates.py`、
  `tests/test_boolean_csp_semantic_tm_gates.py`、
  `tests/test_boolean_csp_source_reduction_gate.py` 和
  `tests/test_certificate_assembly_gate.py`；
- 每个 gate 均包含 positive、negative、attribution、final-use 和 independent replay fixture。

## 19. 反背诵与实验完整性

### 19.1 不采用“必须非同构”

不要求 gadget 与库内构造不同构。理由：

- 重新发现经典最优构造是有效数学能力；
- 变量重命名、约束排列和布尔对偶使同构判定复杂；
- 强制不同会鼓励无意义地增加辅助变量。

### 19.2 采用输入隔离

正式措施：

- 不向模型提供 template source；
- 不提供其他 case 的成功 formula；
- 禁止 oracle/gold import；
- prompt 中只含当前公开 relation table；
- heldout 运行前冻结所有代码与 prompt hash；
- 使用全新 output root；
- 报告 suite hash、commit hash、policy hash 和模型参数。

### 19.3 随机题的角色

q-b21–q-b30 用于检验：

- 无语义名称时是否仍能推理；
- 是否只会匹配固定基数和 NAE 模板；
- 是否能处理双 relation 与混合 arity；
- 是否能利用 counterexample 修正一个明确 formula。

这些题不得在正式 heldout 前用于反复 prompt 调试。

### 19.4 Gadget 正确性证明门禁：证明泄漏控制

- 不提供现有 gadget correct proof body；
- 不提供其他 case 的 witness definition；
- leaf computation 与完整 proof 分开审计；
- proof-plan hash 在 Lean authoring 前冻结；
- formula payload 在整个 Gadget 正确性证明门禁运行中不可变。

### 19.5 语义与复杂度作者化：通用 theorem 泄漏控制

- prompt 只提供被允许 primitive 的签名；
- 不提供被禁 generic theorem 的 proof body；
- deterministic semantic/direct-TM compiler 在相应 gate 中禁用；
- generic theorem 生成一次，后续 case 只实例化；
- 报告不得用实例化次数夸大数学贡献。

### 19.6 源 NP-hard 归约作者化门禁：路线隔离

- 使用 answer-free facade；
- 现有完整 reduction namespace进入 forbidden dependency set；
- theorem index 排除 exact/conditional closure；
- prompt 不出现现有 route helper 的答案性名称；
- local checker只验证模型 block，不搜索 block。

### 19.7 证书与 Hardness 量词作者化门禁：评分隔离

- 证书与 Hardness 量词作者化门禁产物单独标记 formal-certificate-assembly；
- novelty credit 固定为 0；
- 证书与 Hardness 量词作者化门禁成功不提升 gadget、semantic、complexity 或 reduction 数学得分；
- 只衡量形式框架掌握和证书闭合率。

## 20. 风险与缓解

### 风险 1：根搜索到不了 gadget 目标

缓解：

- 使用组件级 authoring checkpoint；
- 给 gadget capability 预留预算；
- 单独记录 `ROUTE_NOT_REACHED`；
- 通过显式、已验证 scaffold 暴露 residual gadget goal。

### 风险 2：结构化 renderer 被误认为确定性数学生成

缓解：

- semantic payload 完全由模型给出；
- renderer 一一映射；
- 记录 `renderer_added_semantic_atom_count = 0`；
- 对 payload 与 Lean AST/依赖做一致性检查；
- renderer 无 candidate enumeration API。

### 风险 3：`by decide` 掩盖证明能力

缓解：

- 显式 Gadget 作者化门禁明确只评分构造；
- Gadget 正确性证明门禁单独评分 forward/reverse proof；
- 不把二者混成一个结论。

### 风险 4：公式资源上限导致假阴性

缓解：

- 资源 profile 版本化；
- 先做有限 verifier microbenchmark；
- 报告 `RESOURCE_BOUND_EXCEEDED`；
- 不通过加入新模板来解决。

### 风险 5：模型从名称背诵

缓解：

- 随机真值表 heldout；
- prompt 以 truth table 为主；
- 记录名称可见性；
- 后续增加坐标置换和 relation symbol 重命名变体。

### 风险 6：validation/heldout 被开发污染

缓解：

- 只使用 q-b02 和 `ga-dev-*` 迭代；
- 冻结后一次性运行 validation；
- heldout 结果一旦用于修改系统，提升版本并标记污染。

### 风险 7：模型生成了 gadget，但最终走了另一条 proof

缓解：

- component success 与 root final-use 分开；
- strict gate 要求 root dependency closure；
- side artifact 不计成功。

### 风险 8：同一个 generic theorem 被重复计分

缓解：

- 以 normalized exact type + source hash 形成 unique capability ID；
- 实例化另计 final-use instance；
- 报告同时显示 unique count 和 instance count；
- promotion 规则使用 unique capability 与 coverage 的组合，而不是简单 artifact 数。

### 风险 9：Direct-TM 复杂度作者化门禁退化为 API 拼接

缓解：

- Direct-TM API 校准 只作校准；
- 正式得分要求 model-authored growth certificate；
- 禁 `interpretCode_tmPolyTime`；
- 记录每个 program node 的 origin；
- 至少一个核心 map/flatten DAG 由模型生成。

### 风险 10：源 NP-hard 归约作者化门禁通过间接 wrapper 复用旧 route

缓解：

- 对完整 route 做 transitive dependency quarantine；
- 动态排除能关闭 exact target 的候选；
- 对 final artifact 做 Lean environment dependency closure；
- 不依赖声明字符串扫描。

### 风险 11：前级 artifact 错误污染后级结论

缓解：

- 每层只接受前级 independent-replay-passed artifact；
- 输入 artifact hash 固定；
- 后级 report记录 prerequisite gate/version；
- 前级 artifact 变化自动使后级缓存失效。

### 风险 12：长 proof 的预算失败被误认为数学失败

缓解：

- 节点级 artifact preservation；
- failure taxonomy 区分预算、route、Lean 与数学反例；
- 先跑 component gate；
- 只在工程 failure 接近零后解释模型能力；
- 源 NP-hard 归约作者化门禁/底层解释器编译证明 使用独立大预算 profile。

## 21. 完成定义

### 21.1 显式 Gadget 作者化门禁：基础设施完成

以下全部满足：

- policy-driven case 集合；
- 无硬编码 17；
- 两个 deterministic gadget 插件被过滤；
- finite gadget namespace allowlist 生效；
- 结构化 plan schema、renderer、checker 和 repair 工作；
- authorship evidence 可重放；
- Lean dependency final-use 审计工作；
- 全部 unit、negative 和 smoke tests 通过；
- production 模式无行为回归。

### 21.2 显式 Gadget 作者化门禁：开发 canary 完成

- q-b02 与三个 dev fixture 全部产生明确终态；
- 至少一个真实模型 gadget 完成 component + root final-use；
- 所有失败都能归入稳定 failure taxonomy；
- 无 deterministic fallback；
- 无 forbidden dependency；
- 无 oracle 泄漏。

### 21.3 显式 Gadget 作者化门禁：正式评测完成

- validation 和 heldout 使用冻结配置；
- 30 题全部完成；
- 3 个 anchor verified；
- 27 个 required case 均为
  `MODEL_GADGET_VERIFIED_AND_FINAL_USED`；
- independent Lean replay 全通过；
- forbidden dependency 为 0；
- disabled plugin contribution 为 0；
- full report、逐题 artifact 和 provenance receipts 完整。

未达到 27/27 时，显式 Gadget 作者化门禁的严格能力判定保持失败，但基础设施仍可视为完成；报告必须如实给出模型
实际成功率。

### 21.4 Gadget 正确性证明门禁完成

- 构造性正确性证书 proof plan 可验证；
- Gadget Lean 双向证明 witness、forward、reverse、assembly 均由模型生成；
- whole-goal decide closure 为 0；
- frozen 显式 Gadget 作者化门禁 payload 无变化；
- validation 关系类型覆盖完成；
- full run 给出 unique proof-plan 与 instance coverage。

### 21.5 公式语义作者化门禁完成

- 公式语义提升 generic theorem通过；
- Assignment Witness 作者化 assignment transformation 来自模型；
- semantic compiler leak 为 0；
- forward/reverse/iff 全部 final-used；
- 27 个 required case final-use；
- unique theorem count 与实例化数分离。

### 21.6 Direct-TM 复杂度作者化门禁完成

- 程序 DAG 与增长界 generic direct-TM theorem通过；
- growth certificate model-authored；
- deterministic direct-TM compiler leak 为 0；
- program DAG 核心节点 model-authored；
- 27 个 required case final-use；
- 底层解释器编译证明 至少完成一个 diagnostic canary 或明确标为后续高风险项。

### 21.7 源 NP-hard 归约作者化门禁完成

- 3SAT→NAE-3 完整 reduction 通过；
- 3SAT→1-IN-3 组合路线通过；
- program、forward、reverse、growth 和 certificate 来源可追踪；
- existing source route dependency 为 0；
- 两个 root hardness artifacts 独立重放通过。

### 21.8 证书与 Hardness 量词作者化门禁完成

- CertifiedReduction 记录构造、CertifiedReduction 手工组合、NativeTMNPHard 手工运输 generic artifacts通过；
- 高层 packager dependency 为 0；
- 27 个 required case final-use；
- formal glue 与数学 novelty 严格分离；
- endpoint audit 和独立重放通过。

### 21.9 整体计划完成

只有在以下事实能够从报告自动验证时，整个 improvement plan 才完成：

- gadget 构造由模型产生；
- gadget proof 由模型产生；
- generic formula semantics 由模型产生；
- generic complexity proof 和增长界由模型产生；
- 至少一条 source hard-core reduction 由模型产生；
- certificate assembly 来源单独归类；
- 所有最终结论具有 dependency、source hash 和 independent replay 证据；
- reuse、deterministic、hybrid、model 和 glue 不再混淆。

## 22. 当前优先级

按以下顺序执行，不并行扩大范围：

1. 冻结对照报告；
2. GatePolicy、插件过滤、动态 case evaluator；
3. 结构化 gadget plan 与 renderer；
4. 有限 checker 与 repair；
5. 作者归因和 dependency final-use；
6. q-b02 + dev fixtures；
7. 冻结后 validation；
8. heldout 与完整 30 题；
9. 构造性正确性证书：proof plan 与 witness schema；
10. Gadget Lean 双向证明：forward/reverse Lean authoring；
11. 公式语义提升：公式提升；
12. Assignment Witness 作者化：assignment witness；
13. Direct-TM API 校准：API 校准，不计正式得分；
14. 程序 DAG 与增长界；
15. 3SAT→NAE-3 源归约：3SAT→NAE3；
16. 3SAT→1-IN-3 源归约：组合得到 1-IN-3；
17. CertifiedReduction 记录构造/CertifiedReduction 手工组合/NativeTMNPHard 手工运输；
18. 底层解释器编译证明 与 直接 3SAT→1-IN-3 源归约扩展 高风险扩展。

在显式 Gadget 作者化门禁完成前，不启动全量语义与复杂度作者化、源 NP-hard 归约作者化门禁或
证书与 Hardness 量词作者化门禁，也不通过新增 deterministic template 提高通过率。

每一层只有在以下条件满足后才能升级：

- 当前层工程性 failure 已接近零；
- 当前层至少一个真实模型 artifact verified；
- contribution attribution 完整；
- forbidden dependency audit 稳定；
- independent replay 稳定；
- 下一层不会把当前层失败重新混入测量。

## 23. 自适应 Token 收敛门禁（2026-08-22 阶段）

### 23.1 触发证据

随机补充题 q-b21 至 q-b30 的真实 API 高预算诊断报告
`Reports/GENERAL_AGENT_BOOLEAN_CSP_HIGH_TOKEN_RANDOM10_REAL_API_REPORT.json`
显示：64k 单档从 16k 基线的 2/10 提升到 6/10，但 q-b23、q-b27、q-b29 的两个 source-core
调用仍在 64k 以 `finish_reason=length` 终止；q-b24 则先产生可检查但错误的 gadget，再在语义 repair
阶段耗尽 64k。由此，下一阶段不把所有请求无条件放大，而是把“上下文不足”“搜索不收敛”和“语义
修复不收敛”拆成可审计终态。

### 23.2 冻结调用协议

- 模型配置 ceiling 固定为 64k，单个逻辑 authoring attempt 首先使用 16k；
- 只有未产生有效 plan 且 provider 明确返回 `finish_reason=length` 时，允许一次 64k 升级；
- 升级调用必须保持 system prompt、JSON prompt、answer-free brief、repair base hash、case、source core
  和 logical attempt 不变；以 request payload SHA-256 自动审计；
- schema invalid、semantic counterexample、Lean failure、timeout、HTTP error 和普通空响应不得触发 token
  升级；它们继续走各自 repair 或 failure taxonomy；
- 每个逻辑 attempt 最多一次升级，不允许 64k 后继续扩大或无界重试；
- 运行预算提升为 `max_authoring_calls=24`、`max_model_calls=32`，覆盖两个允许 source core 在六个逻辑
  attempt 下的最坏 16k→64k 调用数，并保持 strategy 与 authoring 总预算闭合。

### 23.3 新增终态与归因

- `MODEL_SEARCH_NONCONVERGENT`：同一提示词在 16k 和 64k 均以 length 终止；
- `GADGET_SEMANTIC_REPAIR_FAILED`：已有有限语义反例，针对该反例的同上下文 repair 在 16k 和 64k
  均不收敛；
- `GADGET_SEMANTIC_COUNTEREXAMPLE` 仅表示模型确实返回了可解析 plan 且 finite checker 给出反例，不再
  混入 repair token 耗尽；
- 每个 model call 和 typed receipt 必须记录 token profile、requested max tokens、finish reason、prompt
  hash、logical/transport attempt、source core、authoring context key 和 escalation lineage；
- full report 分别汇总 base/high 调用数、length 次数、成功升级数、终止不收敛数、语义 repair 不收敛数
  和各 source-core 调用数。

### 23.4 阶段门禁

- generator/receipt/policy/freeze 协议全部升版并重新计算组件哈希；
- 单元测试覆盖 16k 直接成功、16k length→64k 成功、双 length 非收敛、语义 repair 双 length、非 length
  错误不升级、预算与 base-hash 审计；
- 全量本地测试和 Lean 独立重放通过；
- 阶段完成后，必须使用冻结配置和真实网络 API 重新运行 CSP benchmark 全部 30 题；
- 只有完整报告、30 个逐题终态、API/usage 记账、forbidden dependency、final-use、source-route 和自适应
  token 审计均完整，才允许进入下一阶段。

### 23.5 真实 API 执行结果

冻结 full30 于 2026-08-22 使用真实 DeepSeek API 完成，正式报告为
`Reports/GENERAL_AGENT_BOOLEAN_CSP_ADAPTIVE_TOKEN_FULL30_REAL_API_REPORT.json`：

- 30/30 题均形成终态，3/3 anchor verified；
- 27 个 required case 中 23 个达到 `MODEL_GADGET_VERIFIED_AND_FINAL_USED`，作者化成功率为
  23/27（85.19%），全套为 26/30 verified；
- q-b23、q-b24、q-b26 为 `MODEL_SEARCH_NONCONVERGENT`，q-b30 为
  `GADGET_SEMANTIC_REPAIR_FAILED`，因此严格能力门禁保持失败；
- 156 次真实外部调用中 155 次 HTTP 200，总计 2,739,581 tokens；54 次 16k base、36 次 64k
  escalation、47 次 length exhaustion、24 次成功升级、11 个终止不收敛 receipt、5 个语义 repair
  不收敛 receipt；
- configuration freeze、forbidden dependency、final-use、作者归因、source-route、base-hash、升级链和
  token-profile 审计全部通过；正式运行唯一 API 完整性失败来自 q-b24 repair 的一次偶发
  `IncompleteRead`；
- q-b24 随后以同配置单题隔离复测，报告为
  `Reports/GENERAL_AGENT_BOOLEAN_CSP_ADAPTIVE_TOKEN_Q24_NETWORK_RETRY_REAL_API_REPORT.json`；两条
  source-core 路线的 16k/64k 共四次 gadget-authoring 调用均 HTTP 200 且均以
  `finish_reason=length` 终止，确认网络中断不是该题失败的主因。

本阶段的自适应 token 协议与审计基础设施视为完成，但显式 Gadget 作者化的严格能力门禁不通过。
下一阶段应优先实现 source-core 路线排序与路线级止损，并让 repair 根据有限语义反例产生受控多样性；
不得把继续提高 max token 作为主改进手段。

---

本计划的最终判据不是“Agent 是否调用过模型”或“最终 Lean 文件是否通过”，而是：

> 对每一层被声称为模型生成的数学内容，能否指出其精确语义载荷、模型 source hash、
> Lean 声明、依赖闭包和最终使用路径，并证明确定性系统只完成了该层政策允许的验证、
> 序列化或中性组装工作。
