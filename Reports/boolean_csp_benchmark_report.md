# Boolean CSP NP-hardness Benchmark 报告

> 面向计算复杂度领域读者的技术报告。第 1 部分用标准计算复杂度语言描述 20 道题；
> 第 2 部分解释门禁（被禁止引用的定理）之后需要生成哪些 Lean 代码，并逐条对应到
> 自然语言证明中的步骤，附一个通过案例的完整代码示例；第 3 部分给出本 agent 与
> Archon、One-shot API 调用的对比。
>
> 相关文件：
> - 题面与 suite 说明：`Benchmark/Hardness/Suites/boolean_csp_np_hard_v1.md`、`boolean_csp_np_hard_public_v1.json`
> - Lean 题面：`Lean/Reference/Benchmark/Hardness/Inputs/BooleanCSPNPHard/Case*.lean`
> - 门禁定义：`agent/generative_reduction/boolean_csp_regression.py`（8 条基础禁令）、
>   `agent/generative_reduction/boolean_csp_capability_gate.py`（direct-TM / semantic 两层门禁）
> - 库内通用归约机制：`Lean/Reference/ComplexityReduction/Domain/BooleanCSP/Hardness/`
>   （`PPDefinability.lean`、`InterpretCompiler.lean`、`CoreReductions.lean`、`CanonicalHardCores.lean`、`CanonicalDatabase.lean`）

---

## 1. 20 道题：标准计算复杂度语言描述

### 1.1 统一背景

固定一个**有限的布尔约束语言** Γ：每个关系符号带一个有限元数（arity），其解释是
{0,1} 上的一个有限真值表（“该元组是否被接受”）。CSP(Γ) 是判定问题：给定一组 Γ 约束
（每个约束把一个 Γ 关系作用到若干布尔变量上）的合取，问是否存在满足所有约束的
布尔赋值。这是经典的约束满足问题（CSP）框架。

判定所有 20 题的 NP-难性的数学依据是 **Schaefer 二分定理**（Schaefer, STOC 1978）：
对有限布尔约束语言 Γ，若 Γ 同时**不**属于以下六个可多项式时间求解的闭包类中的
任何一个——0-valid、1-valid、Horn、dual-Horn、bijunctive（2-CNF）、affine（GF(2)
线性方程）——则 CSP(Γ) 是 NP-complete。本题库把这六个类的并记作
`IsSchaeferTractable Γ`，对每个 Γ 都可以按真值表直接判定。

每道题的形式目标是生成并通过 Lean 内核验证一条定理：

```lean
ComplexityReduction.Certificate.NativeTMNPHard problemᵢ
```

其含义（库内定义）是：**每一个 NP 问题都存在到 CSP(Γᵢ) 的多项式时间多一归约**
（`NativeTMNPHard P := ∀ Q, NativeTMInNP Q → Nonempty (CertifiedReduction Q P)`），
其中 `CertifiedReduction A B` 由一个多项式时间程序 `program` 和正确性证明
`∀ x, A.accepts x ↔ B.accepts (program.run x)` 组成——即标准的 NP-难定义（在 ≤ₚ 下）。
归约方向必须是“库内已证 NP-难的源 → 输入问题”，即

```text
ThreeSATLike ≤ₚ CSP(Γᵢ)      （或 NAE-3-SAT ≤ₚ CSP(Γᵢ)、1-IN-3-SAT ≤ₚ CSP(Γᵢ)）
```

反方向 CSP(Γᵢ) ≤ₚ SAT 只证明属于 NP，不能证明 NP-难。

第 1 题是“库内已有端点”的检索基线；其余 19 题都不再包含完整的 3SAT-like 硬子语言，
也不是换符号或换编码。第 2–4、6–19 题各只有一个具有明确组合语义的关系；第 5、20 题
各由两个单独可解、合在一起没有共同 tractable 类的关系组成。

### 1.2 题目清单

记号：`EXACTLY-t-OF-k` 接受且仅接受 Hamming 重量恰为 t 的 k 位元组；`NAEₖ`
（Not-All-Equal）接受且仅接受同时含 0 和 1 的 k 位元组；`ORₖ` 是 k 元析取；
`XOR₂(x,y)` 即 x⊕y=1；`EVEN-PARITY₃(x,y,z)` 即 x⊕y⊕z=0。

| # | case | 语言 Γ | 计算复杂度描述 |
|---:|---|---|---|
| 1 | canonical-three-sat-like | 8 个三元关系，对应 3SAT 子句的 8 种 polarity 模式（每个子句是三个带正负号字面量的析取） | 就是 3SAT 本身。由 Cook–Levin 定理 NP-complete。本题检验 agent 能否检索到库内已证端点，是零构造基线。 |
| 2 | positive-nae4 | {NAE₄} | NAE-4-SAT：四元组不得全 0 或全 1，等价于 4-均匀超图的二染色。由 NAE-3-SAT ≤ₚ NAE-4-SAT（升 arity gadget：每约束引入两个新变量 w,w′，用 NAE₄(x,y,z,w) ∧ NAE₄(x,y,z,w′) ∧ NAE₄(w,w,w′,w′) 表达）得 NP-complete。 |
| 3 | positive-nae3 | {NAE₃}（真值表 01111110：拒 000、111） | NAE-3-SAT，3-均匀超图二染色，Schaefer 的经典硬 core；3SAT ≤ₚ NAE-3-SAT，NP-complete。库内有已证 hardness 锚点。 |
| 4 | positive-exactly-one3 | {EXACTLY-1-OF-3} | 单调 1-IN-3-SAT：每个三元组恰好一个 1。Schaefer 1978 原始归约的硬 core；也可由 3-染色 ≤ₚ 1-IN-3-SAT 得 NP-complete。 |
| 5 | or2-even-parity3 | {OR₂, EVEN-PARITY₃} | OR₂(x∨y) 单独生成 bijunctive（2-CNF）语言，EVEN-PARITY₃ 单独是 affine（GF(2) 方程 x⊕y⊕z=0）；两类约束耦合后不在六个 Schaefer 类中任何一个之内，故 NP-complete。 |
| 6 | positive-nae5 | {NAE₅} | NAE-5-SAT，5-均匀超图二染色；NAE-3 ≤ₚ NAE-5 升 arity，NP-complete。 |
| 7 | positive-exactly-two3 | {EXACTLY-2-OF-3} | 与 1-IN-3-SAT 互补对偶（全局变量取反）；由 1-IN-3-SAT ≤ₚ EXACTLY-2-OF-3-SAT 得 NP-complete。 |
| 8 | positive-exactly-one4 | {EXACTLY-1-OF-4} | 4 元唯一选择约束；由 1-IN-3-SAT 升 arity 归约，NP-complete。 |
| 9 | positive-exactly-two4 | {EXACTLY-2-OF-4} | 平衡的局部基数约束；既非 parity 方程也非 2-CNF 关系；NP-complete。 |
| 10 | positive-exactly-three4 | {EXACTLY-3-OF-4} | 第 8 题的互补对偶；NP-complete。 |
| 11 | positive-exactly-one5 | {EXACTLY-1-OF-5} | 高 arity 唯一选择约束；NP-complete。 |
| 12 | positive-exactly-two5 | {EXACTLY-2-OF-5} | 固定基数 2 的局部基数约束；NP-complete。 |
| 13 | positive-exactly-three5 | {EXACTLY-3-OF-5} | 第 12 题的互补对偶；NP-complete。 |
| 14 | positive-exactly-four5 | {EXACTLY-4-OF-5} | 第 11 题的互补对偶，等价于每个约束唯一选出一个 0；NP-complete。 |
| 15 | positive-exactly-one6 | {EXACTLY-1-OF-6} | 六元唯一选择约束；NP-complete。 |
| 16 | positive-exactly-two6 | {EXACTLY-2-OF-6} | 固定基数 2 的六元局部基数约束；NP-complete。 |
| 17 | positive-exactly-three6 | {EXACTLY-3-OF-6} | 完全平衡但非 affine 的局部基数约束（“数量为 3”不是模 2 方程）；NP-complete。 |
| 18 | positive-exactly-four6 | {EXACTLY-4-OF-6} | 第 16 题的互补对偶；NP-complete。 |
| 19 | positive-exactly-five6 | {EXACTLY-5-OF-6} | 第 15 题的互补对偶，等价于每个约束唯一选出一个 0；NP-complete。 |
| 20 | or3-xor2 | {OR₃, XOR₂} | OR₃(x∨y∨z) 单独是 1-valid（全 1 赋值恒满足），XOR₂ 单独是 affine；两类约束耦合后落在二分定理的 hard 侧，NP-complete。 |

所有 19 个新语言的 `IsSchaeferTractable` 判定结果都是 false（直接用真值表检查六个闭包
条件）。因此“用二分定理得出结论”对 19 题都可行——这正是门禁要禁止的捷径（见第 2 部分）。
门禁之下，每题需要一条**显式构造的**多一归约：构造局部 gadget（pp-定义），给出实例
变换，证明多项式时间可计算性与双向语义正确性。

---

## 2. 门禁之后需要生成什么 Lean 代码

### 2.1 库内已有的“通用机器”与“锚点”

库（`ComplexityReduction.Domain.BooleanCSP`）已经形式化了一套通用的 pp-解释（
primitive-positive interpretation，原始正定义解释）归约机器，以及几个硬 core 锚点：

**通用机器**（对任意 Γ′, Γ）：

- `Gadget Γ R`：**一个关系 R 的 pp-定义（gadget）**——一条 Γ 公式、一组输出变量、
  输出互异证明、以及正确性 `R(tuple) ↔ ∃ 赋值, 公式被满足 ∧ 赋值在输出变量上等于 tuple`。
  这正是 CSP/universal algebra 文献里的 primitive-positive definability（pp-可定义性）。
- `LanguageInterpretation Γ′ Γ`：**pp-解释**——给 Γ′ 的每个关系符号一个 Γ-gadget。
- `interpret I φ`：**实例变换**——把 φ 的每个约束替换为对应 gadget，每条约束的辅助
  变量都取全新的变量（逐出现 fresh）。
- `interpret_satisfiable_iff I φ`：`Satisfiable (interpret I φ) ↔ Satisfiable φ`——
  归约的**双向语义正确性**（完备性 + 可靠性合为一条 iff）。
- `interpretation_tmPolyTime I`：`interpret I` 是**多项式时间可计算**的（
  `TMPolyTimeMap` 是一台多项式时间图灵机实现该函数的形式证据）。
- `nPHard_of_interpretation` / `nPHard_of_interpretation_explicit`：**运输定理**——
  源 NP-难 + 上述证据 ⇒ 目标 NP-难（组装 `CertifiedReduction` 与 `NativeTMNPHard`）。

**硬 core 锚点**（始终允许引用，是归约的起点）：

- `threeSATLikeCoreNPHard`：库内 Cook–Levin 定理（3SAT NP-complete）。
- `nae3CoreNPHard`：3SAT ≤ₚ CSP(NAE₃) 的已验证归约（Schaefer 的 NAE-3 core）。
- `oneInThreeCoreNPHard`：3SAT（经图染色构造）≤ₚ CSP(EXACTLY-1-OF-3) 的已验证归约。

**被门禁的“捷径”**（即本 benchmark 禁止直接调用的现成结论）：

- Schaefer 二分定理本身 `schaefer_dichotomy`，以及由它推出的
  `NativeTMNPHard_of_notSchaeferTractable`（“非 tractable ⇒ NP-难”的打包结论）。
- 两个 canonical 硬 core 解释 `oneInThreeInterpretation`、`naeInterpretation`——即
  Schaefer 证明中把 1-IN-3 / NAE-3 硬 core pp-解释进任意非 tractable Γ 的“万能 gadget”
  （universal gadget，源自 clone 论数据库），以及 `CanonicalDatabase.gadget`。
- 自动运输定理：`nPHard_of_interpretation_auto`、`certifiedReduction_of_interpretation_auto`、
  `nPHard_of_interpretsHardCore`（给解释就自动生成全部证据的打包器）。
- 预打包的 1-IN-3 ↔ EXACTLY-2-OF-3 对偶运输（`nPHard_oneInThree_of_exactlyTwo3` 等
  四条）与 `exactlyTwo3CoreNPHard`。
- 视门禁层级：direct-TM 证据本身（`interpretation_tmPolyTime`）或语义证据本身
  （`interpret_satisfiable_iff`、`interpret_satisfies_forward/reverse`、
  `nPHard_of_interpretation`、`certifiedReduction_of_interpretation` 等）。

### 2.2 三层门禁（禁止声明清单）

`boolean_csp_regression.py` 定义了 8 条基础禁令（对每题都生效），
`boolean_csp_capability_gate.py` 在其上叠加 direct-TM 或 semantic 两层门禁。
所有禁令都是**传递依赖审计**：最终定理的 Lean 依赖闭包中不得出现被禁声明，
用别名或包装也无法绕过。

| 层级 | 额外被禁声明（相对上一层） | 被禁内容在自然语言证明中的位置 | 必须改为生成什么 |
|---|---|---|---|
| 基础 8 条 | `schaefer_dichotomy`；`NativeTMNPHard_of_notSchaeferTractable`(_with_oneInThree)；`oneInThreeInterpretation`；`naeInterpretation`；`CanonicalDatabase.gadget`；`exactlyOne_closed_of_notSchaeferTractable`；`nae_closed_of_notSchaeferTractable` | 二分定理 + 其 hardness 方向的两个推论 + 两个 canonical 万能 gadget（Schaefer 证明的“universality”一步） | 对每个源关系显式构造 pp-定义（gadget），即自己重做 Schaefer hardness 方向的局部构造 |
| direct-TM 门禁（共 16 条） | `nPHard_of_interpretation_auto`；`certifiedReduction_of_interpretation_auto`；`nPHard_of_interpretsHardCore`；`nPHard_oneInThree_of_exactlyTwo3`；`nPHard_exactlyTwo3_of_oneInThree`；`exactlyTwo3CoreNPHard_of_oneInThree`；`exactlyTwo3CoreNPHard`；`interpretation_tmPolyTime` | “实例变换显然是多项式时间的”这一步（自然语言论文里通常一句话带过）与全部自动运输 | 自己生成 `TMPolyTimeMap`：证明 `interpret I` 由多项式时间图灵机实现 |
| semantic 门禁（共 22 条） | 与 direct-TM 共享 7 条运输禁令，但**不**禁 `interpretation_tmPolyTime`，改禁：`nPHard_of_interpretation`；`certifiedReduction_of_interpretation`；`interpret_satisfiable_iff`；`interpret_satisfies_forward`；`interpret_satisfies_reverse`；`oneInThree_satisfiable_iff_exactlyTwo3`；`exactlyTwo3_satisfiable_iff_oneInThree` | 归约的**完备性与可靠性**（双向语义正确性）这一步 | 自己生成双向语义证明：source 可满足 ⇒ target 可满足（forward 扩展赋值）、target 可满足 ⇒ source 可满足（reverse 限制赋值），并合为 iff |

说明：direct-TM 门禁与 semantic 门禁是两个正交的“割”：
- direct-TM 门禁下，语义机器（`interpret_satisfiable_iff` 等）仍可引用，但**多项式时间证据必须生成**；
- semantic 门禁下，`interpretation_tmPolyTime` 仍可引用，但**完备性+可靠性证明必须生成**。
两层门禁都保留通用组装器 `nPHard_of_interpretation`（direct-TM）/`nPHard_of_interpretation_explicit`
（semantic）与硬 core 锚点，因此生成工作严格集中在“归约的局部构造 + 被割掉的那一类证据”。

门禁的精确含义（“禁用的究竟是什么”）：所有禁令都是**声明名层面**的——被禁的是若干
打包定理出现在最终定理的传递依赖闭包中，而不是某类推理。效果是把库的证明依赖图在
某几处切断，允许引用被禁定理**下一层**的引理，迫使 agent 用自己构造的具体对象重放
打包定理的证明骨架。两个逐行对照：

- **direct-TM 门禁**：被禁的 `interpretation_tmPolyTime` 证明体是
  `hFormulaCode`（formulaCode 的 TM 证据，`of_encodingEquiv`）+ `hCode`
  （`TMPolyTimeMap.comp interpretCode_tmPolyTime hFormulaCode`）+
  `formula_tmPolyTime_of_code hCode (interpretCode_eq_formulaCode I)`；生成的
  `direct_tm_formula_code_…`/`direct_tm_interpret_code_…`/`direct_tm_endpoint_…`/
  `capability_…` 恰好是这四步用该题具体解释实例化的结果。
- **semantic 门禁**：被禁的 `interpret_satisfies_forward/reverse` 证明体逐行等于
  生成的 `semantic_forward/reverse`（引理层换成允许的 `instantiate_satisfies_*` 与
  `forwardAssignment_*`）；被禁的 `interpret_satisfiable_iff` 的 `constructor` 双向
  合并在生成物中手工重做。

因此门禁分两类：基础 8 条中的 dichotomy 与 canonical 万能 gadget 是**实质禁令**——
删除非构造的全局结论（二分定理 + universality），使“证 NP-难”必须显式给出一个多一
归约；而 direct-TM / semantic 两层**不改变证明义务**（最终定理的数学内容相同），只
把“引用打包引理”降级为“用其下一层引理重放推导”，并要求具体 witness（具体解释的
`TMPolyTimeMap` 值、具体 forward/reverse 证明项）出现在依赖闭包中。这印证：生成物
是库内证明骨架的重实例化，不含新引理与新证明技巧；要让 LLM 生成新数学，需要禁的是
合成原语（有限搜索器、确定性编译器），见第 4 部分“Gadget 作者化门禁”的设计。

### 2.3 需生成的代码部分 ↔ 自然语言证明步骤的对应

以“证明 NAE-4-SAT 是 NP-难的”（第 2 题）为例，自然语言证明是：

1. 取已知 NP-难的源：NAE-3-SAT。
2. 对源语言唯一的（三元）关系构造 gadget：用若干 NAE₄ 约束 + 辅助变量 pp-定义 NAE₃。
3. 定义实例变换 f：把每个 NAE-3 约束替换为其 gadget（每个约束用全新的辅助变量）。
4. 说明 f 多项式时间可计算（每约束展开为常数个约束）。
5. 完备性：φ 可满足 ⇒ f(φ) 可满足（把满足赋值按 gadget 的 witness 扩展到辅助变量）。
6. 可靠性：f(φ) 可满足 ⇒ φ 可满足（把赋值限制回源变量；由 gadget 的 iff 正确性，
   每个源约束被满足）。
7. 由 1+3+4+5+6 得 NAE-3-SAT ≤ₚ NAE-4-SAT，故 NAE-4-SAT NP-难。

对应到门禁下的 Lean 生成物（`A` 表示必须生成，`引` 表示允许引用库定理，括号内为
direct-TM / semantic 两层门禁的要求差异）：

| 自然语言步骤 | Lean 中对应部分 | 门禁下要求 | 出现在示例代码中的位置（见 2.4） |
|---|---|---|---|
| 1. 选定已证 NP-难源 | 引用 `nae3CoreNPHard` 或 `oneInThreeCoreNPHard` | 引（锚点，永不禁） | 最终定理参数 ② |
| 2. 局部 gadget 构造（pp-定义） | 生成 `Gadget Γ relation`：公式 + 输出变量 + 互异 + `correct` 双向正确性。本 agent 用有限模板搜索 `gadgetOfPlannedSearch` 枚举“≤6 变量、≤7 约束、允许变量重复与辅助变量”的候选公式，并用真值表穷举（`by decide`）认证正确性 | A（所有门禁层级） | `capability_364e...` |
| 3. 实例变换（逐约束替换 + fresh 变量） | 生成 `LanguageInterpretation Γ′ Γ`（`LanguageInterpretation.mk` 由各符号的 gadget 组装）；替换函数 `interpret` 及其 fresh 变量机制由库提供 | A（所有门禁层级） | `stable_binding_0184...` |
| 4. f 是多项式时间可计算的 | 生成 `TMPolyTimeMap (enc Γ′) (enc Γ) (interpret I)`：由“公式编码”映射的 `TMPolyTimeMap`（`of_encodingEquiv`）、库内 `interpretCode_tmPolyTime`（逐约束替换的逐符号代价分析）复合，再用端点等式 `interpretCode_eq_formulaCode` 收口 | A（direct-TM 门禁）；引 `interpretation_tmPolyTime`（semantic 门禁） | `direct_tm_formula_code_…`、`direct_tm_interpret_code_…`、`direct_tm_endpoint_…`、`capability_6afb…` |
| 5. 完备性（forward） | 库内 `instantiate_satisfies_forward`/`forwardAssignment`：源赋值 + 每个已满足约束的 gadget witness ⇒ 扩展赋值满足替换后的约束 | 引（direct-TM）；A 生成（semantic：显式写出 forward 证明） | semantic 版 `semantic_forward_…` |
| 6. 可靠性（reverse） | 库内 `instantiate_satisfies_reverse`：目标赋值限制回源变量即满足源约束 | 引（direct-TM）；A 生成（semantic） | semantic 版 `semantic_reverse_…` |
| 7. 双向 iff 组装 | `∀ φ, Satisfiable (interpret I φ) ↔ Satisfiable φ` | 引 `interpret_satisfiable_iff`（direct-TM）；A 生成（semantic：把 5、6 合为一条 Iff） | semantic 版 `capability_aeed…` |
| 8. 组装 NP-难结论 | `nPHard_of_interpretation`（direct-TM 版，参数：TMPolyTimeMap + 源 NP-难 + 解释）或 `nPHard_of_interpretation_explicit`（semantic 版，参数：TM + 语义 iff + 源 NP-难 + 解释）⇒ `NativeTMNPHard problemᵢ` | 引（通用组装器，保留） | 最终定理 `problemIsNPHard` |
| 9. 合规审计 | 逐条 `#generative_reduction_assert_not_transitive_dependency`（最终定理不依赖每条被禁声明）+ `assert_standard_axioms`（无 sorry/axiom/unsafe）+ 独立重放（换一台 worker 重新编译验证） | A（所有层级） | 文件末尾指令块 |

简言之：门禁把 Schaefer 二分定理这条“免构造”捷径拿掉后，agent 必须在库的 pp-解释
框架内**重新生成一篇可验证的归约证明**，其中：
- 所有层级都必须生成：局部 gadget（步骤 2，证明的核心）+ pp-解释（步骤 3）；
- direct-TM 门禁额外必须生成：多项式时间证据（步骤 4，自然语言里通常最敷衍的一步）；
- semantic 门禁额外必须生成：完备性与可靠性证明（步骤 5–7，归约正确性）。

第 7 题（EXACTLY-2-OF-3）有一个值得注意的变体：库提供了解释对象本身
`exactlyTwo3InterpretsOneInThree`（1-IN-3 → EXACTLY-2 的七约束补 gadget，即互补对偶的
局部构造），但门禁禁掉了它的全部自动运输；因此该题只需生成被割掉的证据层
（direct-TM 门禁下生成 `TMPolyTimeMap`，semantic 门禁下生成双向语义证明，且可由确定性
编译器零模型调用地展开）。

#### Gadget/PP 环节在自然语言证明中的位置（以 NAE₃ → NAE₄ 为例）

论文式证明“NAE-4-SAT 是 NP-难的”会这样写：

> 把 NAE-3-SAT 多项式时间归约到 NAE-4-SAT。对 NAE-3 实例的每个约束 (x,y,z)（要求
> x,y,z 不全相等），引入两个**新的辅助变量** w,w′，替换成三个 NAE-4 约束：
>
> NAE₄(x,y,z,w) ∧ NAE₄(x,y,z,w′) ∧ NAE₄(w,w,w′,w′)
>
> **断言（局部等价）**：(x,y,z) 不全相等 ⟺ 存在 w,w′ 使上面三个约束同时成立。
> - (⇒) 若 x,y,z 不全相等：恰有一个 1 时取 w=0,w′=1，恰有两个 1 时取 w=1,w′=0，
>   三个约束都同时含 0 和 1，成立。
> - (⇐) 若三个约束被 w,w′ 满足：第三个约束 NAE₄(w,w,w′,w′) 成立当且仅当 w≠w′。
>   若 x=y=z=0，则前两个约束分别迫使 w=1、w′=1，与 w≠w′ 矛盾；x=y=z=1 时对称矛盾。
>   故 x,y,z 不全相等。∎
>
> 之后逐约束替换（每条约束用全新的辅助变量），变换多项式时间，由局部等价得到双向
> 可满足性保持。

其中加粗的“**构造约束块 + 断言局部等价 + 两个方向的验证**”就是 Gadget/PP 环节，
即 CSP 文献里的 **primitive-positive definability（pp-可定义性）**：只用存在量词、
合取、变量重复/重命名，在目标语言 Γ 中定义源关系 R。它与 `Gadget Γ R` 的字段一一
对应：

| 自然语言 | `Gadget Γ R` 的字段 |
|---|---|
| “替换成的约束块” | `formula : CSP.Formula Γ`（一条 Γ 公式，即约束列表） |
| “x,y,z 是原约束的变量（输出变量）” | `outputs : Fin R.arity → Nat`（指明哪些变量承载源元组的各坐标） |
| “输出变量两两不同” | `outputs_injective` |
| “断言（局部等价）及其两个方向的验证” | `correct : ∀ tuple, R(tuple) ↔ ∃ 赋值, formula 被满足 ∧ 赋值在 outputs 上等于 tuple`（⇒ 即上例第一段，⇐ 即第二段） |

在 benchmark 中该环节是**每一层门禁都必须现场生成**的部分（实例变换、多项式时间
证据、语义运输大多是库内通用机器，只有被门禁割掉的那一类证据才需生成）。agent 不
手写上述 case 分析，而是枚举有限模板（≤6 变量、≤7 约束、允许变量重复与辅助变量），
对每个候选用真值表穷举验证 `correct`（示例产物中的 `by decide`），取第一个正确候选。

同一环节的第二个例子是第 7 题的互补对偶：库内 `oneInThreeGadgetOfExactlyTwo3` 用
7 条 EXACTLY-2-OF-3 约束实现“局部取反”——两条 `EXACTLY2(xᵢ,uᵢ,vᵢ) ∧ EXACTLY2(vᵢ,vᵢ,uᵢ′)`
迫使 `uᵢ = ¬xᵢ`，最后一条 `EXACTLY2(u₀,u₁,u₂)` 即 `EXACTLY2(¬x₀,¬x₁,¬x₂)` ⟺
恰好一个 xᵢ 为 1——正是“1-IN-3 与 EXACTLY-2 互补对偶”这一自然语言观察的逐约束实现。

#### Gadget 在 Lean 中的实现方式与本 agent 的实际生成路径

`Gadget Γ R` 的四字段之外，库还垫了一层**可判定的候选规范**：`Spec`（有界变量数的
小公式 + 输出映射）带 `Spec.Correct` 的 Decidable 实例——局部等价命题按有限真值表可
机械判定；`AnyCorrect`/`chooseCorrect` 在候选表里挑第一个正确者，`Spec.toGadget`
升为 `Gadget`；`gadgetOfPlannedSearch` 按计划器选定的文法物化候选并取证。

本 benchmark 的实际运行里，gadget 的获得方式分三种：

1. **现场搜出构造（16 题，主路径）**：`gadgetOfPlannedSearch` 枚举候选 pp-公式
   （模板约束形状 × 目标语言符号赋值 × 变量映射：投影/置换/重复/辅助变量），每个
   候选用 `by decide` 做完整真值表判定 `Spec.Correct`，取第一个通过者。搜出来的就是
   自然语言证明里的那个构造（可能是经典 gadget 或等价变体），证书是机器核验的；
   全部失败时用真值表反例（`firstPlannedCounterexample?`）驱动重计划（扩界/换模板，
   CEGIS 式）。这 16 题的 gadget 代码体**不是模型写的**：模型调用全部是
   `strategy-proposal`（计划器选路线/文法/模板/界），gadget 体是确定性渲染。
2. **实例化库内已有的手写 gadget（仅第 7 题）**：`exactlyTwo3InterpretsOneInThree`
   是库内手写的 7 约束补 gadget（`correct` 为手写证明），不在禁令清单内；门禁只禁其
   自动运输，故该题仍须现场生成被割掉的证据层。
3. **未发生的两条路**：用组合算子把已证 gadget 组合成新 gadget（agent 生成路径是
   扁平搜索，不是递归组合）；模型手写 gadget 体。（另有一个 canonical-database 配方
   插件按 clone 数据库配方重建 canonical gadget，但它引用基础门禁所禁的
   `exactlyOne/nae_closed_of_notSchaeferTractable`，本 benchmark 下会被传递依赖审计
   拒绝，实测未使用。）

用标准计算复杂度语言重述整个环节：

- **Gadget/PP 是归约的局部替换方案**：对源语言每个关系 R 固定一组含其 k 个坐标变量
  与新辅助变量 ȳ 的目标语言约束合取 G_R，满足局部等价 `R(x̄) ⟺ ∃ȳ G_R(x̄,ȳ)`——即
  CSP 文献中的 pp-可定义性（仅用 ∃、合取、变量重合/重命名）。
- **整个归约由它机械生成**：逐约束替换（每约束用互不相同的全新辅助变量）得实例
  变换 f；|f(φ)|=O(|φ|)，故 f 多项式时间可计算；**完备性**（φ 可满足 ⇒ f(φ) 可满足）
  逐约束取 witness 扩展赋值，**可靠性**（f(φ) 可满足 ⇒ φ 可满足）限制回源变量——两者
  都由局部等价的两侧给出。复合已知 NP-难源即得目标 NP-难。
- **局部等价是可穷举判定的有限命题**：R 与 G_R 均有限，只需检查全部 2^k 元组 × 2^m
  辅助赋值；人类证明的双向 case 分析在形式化中就是真值表穷举。
- **本 agent 的做法**：在有界候选空间（有界变量/约束数 × 变量映射 × 目标符号赋值）
  上枚举候选，对每个候选执行真值表穷举，取第一个满足局部等价者（失败则扩界/换
  模板重搜）；即“现场搜索合成局部替换方案 + 机器核验证书”，而非引用现成万能 gadget
  （门禁禁止）或组合已证 gadget（未实现该路径）。第 7 题是唯一例外：直接采用库内
  已手写验证的局部替换方案（1-IN-3 → EXACTLY-2 的七约束取反方案）。

#### 哪些是 agent 生成的真实数学内容（与“检索定理”的界限）

以最终两轮运行（direct-TM V10、semantic V10）为准，分类如下：

- **新数学内容（库中此前不存在）**：
  1. 16 个局部替换方案（pp-定义/gadget）——每个都是目标语言里的新约束块与新变量
     映射，是归约中唯一“有创意”的构造步骤；产生方式是有界文法枚举 + 真值表穷举
     核验，而非模型推理或库内 gadget 复用。
  2. 17 题各自的新归约正确性/代价定理——semantic 门禁下针对具体归约的
     `Sat(f(φ)) ↔ Sat(φ)`、direct-TM 门禁下的 `f ∈ TMPolyTimeMap`：即论文里
     “双向保持/多项式时间”的 Claim 及其证明，由通用 pp-归约机器确定性例化得到。
  3. 组装对象（pp-解释、能力绑定）：机械组装，无新数学。
- **不是新数学（检索/复用）**：第 1、3、4 题直接引用库内已证 NP-难定理（纯检索，
  零新数学，即设计上的可复用端点基线）；第 7 题的 pp-定义复用库内手写的七约束取反
  gadget（只生成被门禁割掉的运输证据）；所有通用机器定理均为库内定理的实例化。
- **模型的贡献**：两轮全部 49/32 次模型调用均为 `strategy-proposal`（选择路线、变量
  界、模板文法），0 次代码起草、0 次修复；所有最终被使用的贡献均为
  `DETERMINISTIC_GENERATED_CAPABILITY`。早期迭代不同：V8 有 4 个模型起草的
  capability（未进入最终产物）、V9 有 4 个（其中 1 个进入最终产物），V10 起被确定
  性编译器完全取代。
- 边界：gadget 环节是“对候选构造的穷举搜索”（产生新数学对象，创意被编码进人设计的
  模板文法与通用 pp-机器），而第 1/3/4 题是“定理检索”（不产生新数学）。用标准语言
  说：agent 生成了新数学对象与新定理实例（16 个新归约 + 17 个新正确性/代价定理），
  但不生成新的证明技巧。

### 2.4 通过的案例代码示例：第 2 题 positive NAE-4（direct-TM 门禁）

下面是从 `general-agent-boolean-csp-direct-tm-v10` 运行中取出的最终产物
（`Artifact.lean`，略有排版整理，注释为中文讲解）。它一次性生成：源语言唯一关系符号
NAE₃ 的 gadget（有限搜索 + 真值表穷举认证）、pp-解释、多项式时间证据、最终 NP-难
定理，并在文件末尾逐条断言不依赖任何被禁声明。

```lean
import Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case02PositiveNAE4   -- 题面：Γ={NAE₄}，problem = cspOf Γ
import ComplexityReduction.Agent.GenerativeReduction.FinalCheck        -- 门禁/端点审计指令
import ComplexityReduction.Agent.GenerativeReduction.Plugins.BooleanCSPFiniteGadget -- 有限 gadget 搜索
import ComplexityReduction.Domain.BooleanCSP.Hardness.PPDefinability   -- Gadget / LanguageInterpretation / interpret
import ComplexityReduction.Agent.Hardness.BooleanCSPAuthoringSources   -- 源语言 PositiveNAE3CSP
import ComplexityReduction.Domain.BooleanCSP.Hardness.CoreReductions   -- nae3CoreNPHard 锚点
import ComplexityReduction.Domain.BooleanCSP.Hardness.InterpretCompiler -- interpretCode 及其 TM 代价分析

-- ① 局部 gadget 构造（自然语言步骤 2）：
--    源语言 PositiveNAE3CSP 只有一个关系符号（NAE₃）。下面 fin_cases 后依次尝试三组
--    候选搜索配置（对辅助变量的“强制取值表”分别取 [()]、[false,true]、全部取值），
--    first 选取第一个能成功认证的配置。
--    gadgetOfPlannedSearch：在有限模板语法（≤6 变量、≤7 约束、允许变量重复与辅助变量、
--    枚举符号赋值）上搜索；候选正确性由真值表穷举（by decide）认证，
--    即对每个元组验证  R(tuple) ↔ ∃赋值, 公式被满足 ∧ 输出变量取 tuple 值。
noncomputable def capability_364e5ac7eb95ba0d2394 :
    (symbol : PositiveNAE3CSP.gamma.Symbol) →
    Hardness.Gadget Case02PositiveNAE4.gamma (PositiveNAE3CSP.gamma.relationOf symbol) := by
  classical
  intro symbol
  apply Classical.choice
  fin_cases symbol <;>
    first
    | exact ⟨Plugins.BooleanCSPFiniteGadget.gadgetOfPlannedSearch _
        [()] _ 6 (by decide) (by decide) Plugins.BooleanCSPFiniteGadget.templates
        (by simp [PositiveNAE3CSP.gamma, Case02PositiveNAE4.gamma] <;> decide)⟩
    | exact ⟨Plugins.BooleanCSPFiniteGadget.gadgetOfPlannedSearch _
        [false, true] _ 6 (by decide) (by decide) Plugins.BooleanCSPFiniteGadget.templates
        (by simp [PositiveNAE3CSP.gamma, Case02PositiveNAE4.gamma] <;> decide)⟩
    | exact ⟨Plugins.BooleanCSPFiniteGadget.gadgetOfPlannedSearch _
        (Finset.univ.toList) _ 6 (by decide) (by decide) Plugins.BooleanCSPFiniteGadget.templates
        (by simp [PositiveNAE3CSP.gamma, Case02PositiveNAE4.gamma] <;> decide)⟩

-- ② 实例变换（自然语言步骤 3）：把逐符号的 gadget 组装成一个 pp-解释。
--    替换函数 interpret 由库定义：每条源约束展开为其 gadget，辅助变量取全新变量。
noncomputable def stable_binding_0184b5467b7a5252d1aa :
    Hardness.LanguageInterpretation PositiveNAE3CSP.gamma Case02PositiveNAE4.gamma := by
  apply_generative_rule_exact Hardness.LanguageInterpretation.mk [ ( …capability_364e… ) ]

-- ③ 多项式时间证据（自然语言步骤 4，direct-TM 门禁的核心生成物）：
--    a) “取公式编码”本身是 TMPolyTimeMap（编码等价）；
--    b) 逐约束替换 interpretCode 的多项式时间由库内 interpretCode_tmPolyTime 给出，
--       与 a) 复合得 interpretCode ∘ formulaCode 的 TM 证据；
--    c) 端点等式 interpretCode = formulaCode ∘ interpret（库内 interpretCode_eq_formulaCode）；
--    d) 三者收口成：interpret I 是 TMPolyTimeMap。
noncomputable def direct_tm_formula_code_ce93917f0a0e :
    TMPolyTimeMap (FiniteDomainCSPTable.encodedType PositiveNAE3CSP.gamma)
      FiniteDomainCSPTable.formulaCodeEncodedType
      (fun formula => FiniteDomainCSPTable.formulaCode PositiveNAE3CSP.gamma formula) := by
  exact TMPolyTimeMap.of_encodingEquiv _ _ _ (Equiv.refl _)
    (by intro formula
        change FiniteDomainCSPTable.formulaCodeEncodedType.encode
            (FiniteDomainCSPTable.formulaCode PositiveNAE3CSP.gamma formula) =
          List.map id (FiniteDomainCSPTable.formulaCodeEncodedType.encode
            (FiniteDomainCSPTable.formulaCode PositiveNAE3CSP.gamma formula))
        rw [List.map_id])

noncomputable def direct_tm_interpret_code_ce93917f0a0e :
    TMPolyTimeMap (FiniteDomainCSPTable.encodedType PositiveNAE3CSP.gamma)
      FiniteDomainCSPTable.formulaCodeEncodedType
      (fun formula => Hardness.interpretCode …stable_binding…
        (FiniteDomainCSPTable.formulaCode PositiveNAE3CSP.gamma formula)) := by
  have hComp := TMPolyTimeMap.comp
    (Hardness.interpretCode_tmPolyTime …stable_binding…) direct_tm_formula_code_ce93917f0a0e
  simpa [Function.comp] using hComp

noncomputable def direct_tm_endpoint_ce93917f0a0e : ∀ input,
    Hardness.interpretCode …stable_binding… (FiniteDomainCSPTable.formulaCode PositiveNAE3CSP.gamma input)
      = FiniteDomainCSPTable.formulaCode Case02PositiveNAE4.gamma
          (@Hardness.interpret PositiveNAE3CSP.gamma Case02PositiveNAE4.gamma …stable_binding… input) := by
  exact Hardness.interpretCode_eq_formulaCode …stable_binding…

noncomputable def capability_6afb6a1445860ba125cb :
    TMPolyTimeMap
      (FiniteDomainCSPTable.encodedType PositiveNAE3CSP.gamma)
      (FiniteDomainCSPTable.encodedType Case02PositiveNAE4.gamma)
      (@Hardness.interpret PositiveNAE3CSP.gamma Case02PositiveNAE4.gamma …stable_binding…) := by
  exact FiniteDomainCSPTable.formula_tmPolyTime_of_code
    direct_tm_interpret_code_ce93917f0a0e direct_tm_endpoint_ce93917f0a0e

-- ④ 组装 NP-难结论（自然语言步骤 1+7+8）：
--    nPHard_of_interpretation 的语义正确性部分引用库内 interpret_satisfiable_iff
--    （direct-TM 门禁允许）；源 NP-难引用 nae3CoreNPHard 锚点。
theorem problemIsNPHard :
    Certificate.NativeTMNPHard Case02PositiveNAE4.problem := by
  apply_generative_rule_exact Hardness.nPHard_of_interpretation [
    ( …capability_6afb… ),                              -- 生成的 TMPolyTimeMap
    ( by apply_generative_rule Hardness.nae3CoreNPHard ), -- 源 NP-难锚点
    ( PositiveNAE3CSP.gamma ),                            -- 源语言
    ( …stable_binding… )                                 -- 生成的 pp-解释
  ]

-- ⑤ 门禁合规审计（自然语言证明之外的形式化审查）：逐条断言最终定理的
--    Lean 依赖闭包不包含任何被禁声明；最后审计标准公理（无 sorry/axiom/unsafe）。
#generative_reduction_assert_not_transitive_dependency Generated.problemIsNPHard
  "ComplexityReduction.Domain.BooleanCSP.schaefer_dichotomy"
#generative_reduction_assert_not_transitive_dependency Generated.problemIsNPHard
  "ComplexityReduction.Domain.BooleanCSP.Hardness.NativeTMNPHard_of_notSchaeferTractable"
-- ……（其余被禁声明逐条同形，此处省略）……
#generative_reduction_assert_not_transitive_dependency Generated.problemIsNPHard
  "ComplexityReduction.Domain.BooleanCSP.Hardness.interpretation_tmPolyTime"

assert_standard_axioms Generated.problemIsNPHard
```

同一题在 **semantic 门禁**下的产物差异只有两步：不生成 `TMPolyTimeMap`（改为引用库内
`interpretation_tmPolyTime`），而是生成双向语义证明并合为 iff，再改用
`nPHard_of_interpretation_explicit` 组装：

```lean
-- 可靠性（步骤 6）：target 可满足 ⇒ source 可满足（把赋值限制回源变量）
noncomputable def semantic_reverse_af2eb33ec4c2 :
    ∀ (formula : CSP.Formula PositiveNAE3CSP.gamma) {targetAssignment : SAT.Assignment},
      CSP.Formula.Satisfies (@Hardness.interpret PositiveNAE3CSP.gamma Case02PositiveNAE4.gamma
        …stable_binding… formula) targetAssignment →
        CSP.Formula.Satisfies formula targetAssignment := by
  intro formula targetAssignment targetSatisfies constraint constraintMember
  apply Hardness.instantiate_satisfies_reverse …stable_binding… (CSP.Formula.maxVar formula) constraint
  intro instantiatedConstraint instantiatedMember
  exact targetSatisfies instantiatedConstraint
    (List.mem_flatMap.mpr ⟨constraint, constraintMember, instantiatedMember⟩)

-- 完备性（步骤 5）：source 可满足 ⇒ target 可满足（forwardAssignment 把源赋值
-- 按每个已满足约束的 gadget witness 扩展到辅助变量）
noncomputable def semantic_forward_af2eb33ec4c2 :
    ∀ (formula : CSP.Formula PositiveNAE3CSP.gamma) {sourceAssignment : SAT.Assignment},
      (sourceSatisfies : CSP.Formula.Satisfies formula sourceAssignment),
      CSP.Formula.Satisfies (@Hardness.interpret PositiveNAE3CSP.gamma Case02PositiveNAE4.gamma
        …stable_binding… formula)
        (@Hardness.forwardAssignment PositiveNAE3CSP.gamma Case02PositiveNAE4.gamma
          …stable_binding… formula sourceAssignment sourceSatisfies) := by
  intro formula sourceAssignment sourceSatisfies instantiatedConstraint instantiatedMember
  rcases List.mem_flatMap.mp instantiatedMember with ⟨constraint, constraintMember, inBlock⟩
  apply Hardness.instantiate_satisfies_forward …stable_binding… (CSP.Formula.maxVar formula)
    (sourceSatisfies := sourceSatisfies constraint constraintMember)
    (target := @Hardness.forwardAssignment PositiveNAE3CSP.gamma Case02PositiveNAE4.gamma
      …stable_binding… formula sourceAssignment sourceSatisfies)
  · intro var below
    exact Hardness.forwardAssignment_source …stable_binding… formula below
  · intro index
    exact Hardness.constraint_vars_le_formula_maxVar constraintMember index
  · intro gadgetVariable
    exact Hardness.forwardAssignment_fresh …stable_binding… formula constraintMember gadgetVariable
  exact inBlock

-- 步骤 7：把两个方向合为 satisfiability iff（semantic 门禁的核心生成物）
noncomputable def capability_aeed688baaf0dee5cd97 :
    ∀ (formula : CSP.Formula PositiveNAE3CSP.gamma),
      Iff (CSP.Formula.Satisfiable Case02PositiveNAE4.gamma
            (@Hardness.interpret PositiveNAE3CSP.gamma Case02PositiveNAE4.gamma …stable_binding… formula))
          (CSP.Formula.Satisfiable PositiveNAE3CSP.gamma formula) := by
  intro formula
  constructor
  · rintro ⟨targetAssignment, targetSatisfies⟩
    exact ⟨targetAssignment, semantic_reverse_af2eb33ec4c2 formula targetSatisfies⟩
  · rintro ⟨sourceAssignment, sourceSatisfies⟩
    exact ⟨@Hardness.forwardAssignment PositiveNAE3CSP.gamma Case02PositiveNAE4.gamma
        …stable_binding… formula sourceAssignment sourceSatisfies,
      semantic_forward_af2eb33ec4c2 formula sourceSatisfies⟩

-- 组装改用显式版本：TM 证据引用库（semantic 门禁允许），语义 iff 用上面的生成物
theorem problemIsNPHard :
    Certificate.NativeTMNPHard Case02PositiveNAE4.problem := by
  apply_generative_rule_exact Hardness.nPHard_of_interpretation_explicit [
    ( by apply_generative_rule Hardness.interpretation_tmPolyTime ), -- 库内 TM 证据
    ( …capability_aeed… ),                                          -- 生成的语义 iff
    ( by apply_generative_rule Hardness.nae3CoreNPHard ),            -- 源 NP-难锚点
    ( PositiveNAE3CSP.gamma ),
    ( …stable_binding… )                                            -- 生成的 pp-解释
  ]
```

---

## 3. 本 agent 与 Archon、One-shot 的对比

### 3.1 三个臂的设定（模型侧完全一致）

三者使用同一模型配置：`deepseek-v4-flash`，temperature 0，reasoning effort low，
300 秒超时，0 重试；对每题可见的**公共题面完全相同**（题目陈述、形式目标、证明要求），
均不可见库源码、推荐证明、oracle、路由与诊断信息。

| | 本 agent（递归生成 agent） | Archon 黑盒臂 | One-shot LLM 臂 |
|---|---|---|---|
| 形态 | 规划 + 有限合成 + 模型 authoring 的递归证明搜索，带 Lean 编译反馈、门禁与传递依赖审计 | Archon 多智能体形式化循环（plan + prover 角色），本次配置 max 1 次迭代、每角色 16 轮工具、每例 7200 秒循环超时 | 每题恰好 1 次 chat-completions 请求，无工具、无 Lean 反馈、无后续轮次、无 reviewer |
| 入口 | `agent/generative_reduction/boolean_csp_regression.py`（direct-TM / semantic 门禁配置） | `scripts/run_hardness_benchmark.py --agent archon --lane boolean_csp` | `scripts/run_hardness_benchmark.py --agent oneshot-llm --lane boolean_csp` |
| 判定 | Lean kernel 验证 + 独立重放 + 端点等式 + 公理审计 + 被禁声明传递依赖审计 | 模型产出后由本仓库编译验证 `NativeTMNPHard` 目标类型 | 同左 |

### 3.2 Boolean CSP 20 题结果（2026-08-16 运行）

三臂在同一 20 题、同一公共题面、同一模型配置（deepseek-v4-flash, temperature 0,
low effort）下的对照（本仓库 runner 实测）：

| 臂 | kernel 验证通过 | 状态分布 | 消耗 | 墙钟（4 并发） |
|---|---|---|---:|---:|
| **本 agent**（direct-TM V10，16 条禁令） | **20/20** | VERIFIED 20 | 49 次模型调用、约 74K token | 2035 s |
| **本 agent**（semantic V10，22 条禁令） | **20/20** | VERIFIED 20 | 32 次模型调用、约 46K token | 2290 s |
| Archon 黑盒 | **0/20** | FAILED_LEAN 20 | 40 个 Archon sessions、约 1620 万 token、约 $1.30 | 921 s |
| One-shot LLM | **0/20** | FAILED_LEAN 20 | 20 次请求、约 42 万 token（模型输出了很长的未验证尝试）、约 $0.12 | 1132 s |

审计口径：One-shot 臂以 Archon 臂的报告做公共输入审计，20/20 题公共输入 SHA-256
一致、模型配置一致（`run_valid=true`），即两个黑盒臂面对的任务材料完全相同。

要点：

- **Archon 与 One-shot 全部 20 题 FAILED_LEAN，包括第 1 题**（3SAT 端点，本 agent 与
  旧生产 agent 都是零构造直接复用库内定理）。原因是这两个黑盒臂只拿到公共题面
  （“证明 problem 是 NP-难的”+ 形式目标类型），看不到库内的 core 锚点、pp-解释机器
  与归约路线，也没有可用的检索/规划/编译反馈回路；Archon 循环（本次配置 max 1 次
  迭代、每角色 16 轮工具）产出的多是未完成证明的骨架（例如只写
  `unfold NativeTMNPHard`），One-shot 的一次性输出同样无法通过内核。
- **本 agent 在最严两层门禁下仍 20/20**，且 17/20 题的最终定理使用的是当场生成的
  新证据（direct-TM 门禁下生成的多项式时间证据、semantic 门禁下生成的双向语义
  证明），不是库内现成定理；其余 3 题（1、3、4）是设计上的可复用端点。
- 代价与效率：本 agent 用 32–49 次**定向**模型调用（每次对应一个具体子目标）完成
  全部 20 题，而 Archon 在 0 通过率下消耗了约 1620 万 token（约 $1.30）；One-shot
  最便宜（$0.13）但也最无效。
- 门禁评估硬性指标全部通过：20 题全部 VERIFIED、被禁声明直接或传递依赖计数为 0、
  真实 API 被调用、全部 HTTP 200、计划/预算/收据审计一致。

本 agent 在同一 suite 上的消融阶梯（说明门禁的渐进难度与 agent 的迭代改进）：

| 阶段 | 配置 | 结果 |
|---|---|---|
| 2026-08-14 无门禁 | 允许 dichotomy 全套 | 20/20（20 次模型调用，全部复用库内 `NativeTMNPHard_of_notSchaeferTractable` 等） |
| 2026-08-14 dichotomy-free（早期非递归版） | 3 条禁令 | 3/20（仅 3SAT/NAE-3/EXACTLY-2 三个可复用端点；其余 BLOCKED/FAILED_MODEL） |
| 2026-08-15 无 canonical 解释/数据库（递归版） | 8 条禁令 | 20/20，16 题使用生成的 capability |
| 2026-08-15 direct-TM 门禁 P0 | 16 条禁令 | 3/20（生成层未打通） |
| 2026-08-16 direct-TM V8 → V9 → V10 | 16 条禁令 | 17/20 → 19/20 → **20/20** |
| 2026-08-15 semantic 门禁 P0 | 22 条禁令 | 3/20 |
| 2026-08-16 semantic V10 | 22 条禁令 | **20/20** |

### 3.3 历史口径（2026-08-10，旧 50 题注册表：capability 24 + exact-edge 24 + frontier 2）

作为参考，同一对比框架在 Boolean CSP suite 引入之前跑过旧注册表（**不同题集，口径需注明**）：

| 臂 | 结果 |
|---|---|
| 生产 agent（deepseek） | capability 24 题中 23 题 kernel 验证通过（26 次模型调用、约 40 万 token） |
| Archon 黑盒 | 50 题 **0** kernel 验证通过（35 FAILED_LEAN、15 BLOCKED_INPUT；70 个 Archon sessions、约 3030 万 token、约 $2.40、墙钟 1471 秒） |
| One-shot LLM | 50 题 **0** kernel 验证通过（35 FAILED_LEAN、15 BLOCKED_INPUT；35 次请求、约 11 万 token、约 $0.03、墙钟 314 秒） |

### 3.4 结论

在本 Boolean CSP benchmark 上：黑盒的 Archon 循环与 One-shot 调用对**全部 20 题**（含
最简单的第 1 题）都无法产出可通过内核的证明；而本 agent 在禁止调用 Schaefer 二分
定理、canonical 万能 gadget、自动运输、乃至多项式时间证据（direct-TM 门禁）或双向
语义证明（semantic 门禁）的最严配置下，仍对全部 20 题产出 kernel 验证通过、独立
重放通过、被禁声明依赖为 0 的 NP-难证明，其中 17 题的证明使用了当场生成的新归约
证据。差异的来源是：本 agent 拥有受门禁约束的库内归约机制（pp-解释框架 + 硬 core
锚点 + 有限真值表合成），并把“证明归约”分解为可逐个生成、逐个编译检查的小目标；
两个黑盒臂只有公共题面，必须在一次输出或一次短循环内凭空重建整个库与全部归约。

---

## 4. 下一步：让 LLM 生成新数学内容的门禁设计

现有门禁只删**定理**、不删**合成器**（gadget 有限搜索、direct-TM/semantic 确定性
编译器均为 `authoritative_typed_compiler`），因此无论删多少定理，新内容仍由确定性
程序产出，模型只做 `strategy-proposal`。要让 LLM 手写真实数学，需要按阶梯禁合成
原语：

| 层级 | 禁什么 | 逼 LLM 手写什么（对应论文部分） | 风险 |
|---|---|---|---|
| **G1 gadget 作者化**（推荐下一步） | `Plugins.BooleanCSPFiniteGadget.*`（搜索器、模板、候选物化），并使 Python 侧有限插件对 Gadget 目标失效 | 每个源关系的 pp-定义：约束块构造（归约唯一有创意的步骤）+ `correct` 双向 case 分析 | 低：证明是有限 case 分析，可编译反馈迭代；首跑预期通过率先跌（参照 P0 的 3/20）再回升 |
| **G2 语义/代价机器作者化** | 再禁 `instantiate_satisfies_*`、`interpretCode_tmPolyTime`、`interpretCode_eq_formulaCode`、`formula_tmPolyTime_of_code`、`forwardAssignment_*` | 从 `interpret`/`Satisfies`/`TMPolyTimeMap` 定义出发自己证完备性、可靠性与多项式时间 | 中：证明义务显著变长，需放宽预算 |
| **G3 源归约作者化** | 禁 `nae3CoreNPHard`、`oneInThreeCoreNPHard`（保留 Cook–Levin 3SAT 端点） | 自己构造 3SAT→NAE-3、3SAT→1-IN-3 两条经典归约（Schaefer 1978 原始归约） | 高：先跑单题 canary 再全量 |
| **G4 证书作者化** | 禁通用组装器 `nPHard_of_interpretation(_explicit)`、`CertifiedReduction.comp`、`NativeTMNPHard.alongPath` | 直接构造 `CertifiedReduction` 并闭合 NP-难定义中的全称量词 | 高：可能整体 BLOCKED |

横向变体：出新题使目标语言的 pp-定义超出模板文法可达范围（更大变量/约束界、更深
嵌套），或禁多约束模板迫使走 pp-组合（先证 R₁ pp-可定义于 Γ，再证 R pp-可定义于
Γ∪{R₁}），才会逼出新的证明技巧而非新构造实例。工程上模型起草通道已存在
（V8/V9 的 `lean-authoring-*` 曾产出 `MODEL_GENERATED_CAPABILITY`），G1 只需新增禁令
元组 + 从插件注册表移除两个有限插件 + 让 model-authoring provider 对 Gadget 目标
权威化，并把门禁评估从“要求确定性生成”改为“要求 `MODEL_GENERATED_CAPABILITY`
final-used 且独立重放通过”。

---

### 附：关键文件索引

- 20 题公共 suite：`Benchmark/Hardness/Suites/boolean_csp_np_hard_public_v1.json`
- 题面说明：`Benchmark/Hardness/Suites/boolean_csp_np_hard_v1.md`
- 门禁（8 条基础禁令）：`agent/generative_reduction/boolean_csp_regression.py`
- 门禁（direct-TM / semantic 层）：`agent/generative_reduction/boolean_csp_capability_gate.py`
- 本 agent 运行产物：`.reduction-agent/general-agent-boolean-csp-direct-tm-v10-real-api-20260816/`
  与 `.reduction-agent/general-agent-boolean-csp-semantic-v10-real-api-20260816/`
  （每题的 `cases/<Case>/Artifact.lean` 为最终产物）
- 报告 JSON：`Reports/GENERAL_AGENT_BOOLEAN_CSP_DIRECT_TM_V10_REAL_API_REPORT.json`、
  `Reports/GENERAL_AGENT_BOOLEAN_CSP_SEMANTIC_V10_REAL_API_REPORT.json`
- 本报告引用的黑盒臂运行产物：
  - Archon：`.reduction-agent/benchmark-archon-blackbox-boolean-csp-20260816/report.json`
  - One-shot：`.reduction-agent/benchmark-oneshot-llm-boolean-csp-20260816-v2/report.json`
    （含对 Archon 臂的公共输入一致性审计）
- Archon / One-shot 臂实现：`agent/hardness/archon_blackbox_benchmark.py`、`compare/OneShotLLM/`
