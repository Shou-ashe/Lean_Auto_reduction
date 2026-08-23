# Boolean CSP NP-hard benchmark：30 道正式 suite 题目

本文件说明 `Suites/` 下独立维护的 Boolean CSP suite；其中第 21--30 题是固定随机种子生成的补充题。
公开 runner 只读取 `boolean_csp_np_hard_public_v1.json`；数学依据、预期结果和评分信息位于隔离的
`Evaluation/boolean_csp_np_hard_oracle_v1.json`，production run 不读取 oracle。

## 统一题目

每一题给出一个闭合的有限 Boolean relation language `Γᵢ` 和精确的
`PresentedProblem problemᵢ`。目标是生成并通过 Lean kernel 验证：

```lean
ComplexityReduction.Certificate.NativeTMNPHard problemᵢ
```

证明方向必须是库内已知 NP-hard source 到输入问题：

```text
ThreeSATLike CSP  ≤ₚ  CSP(Γᵢ)
```

反方向 `CSP(Γᵢ) ≤ₚ SAT` 不能单独证明 hardness。除第 1 题这个“库内已有端点”检索
基线外，其余 29 题都不再包含完整的 3SAT-like hard 子语言，也不是 symbol 重命名或
presentation 换皮。第 2--4、6--19 题各自只有一个具有明确组合语义的 relation；第 5、
20 题各由两个单独可解、合在一起却没有共同 tractable class 的 relation 构成；第
21--30 题直接给出随机真值表，避免 agent 仅依靠关系名称或熟悉模板匹配。

数学依据是 Schaefer 的 Boolean satisfiability dichotomy：有限 Boolean relation language
若既非 0-valid、1-valid、Horn、dual-Horn、bijunctive，也非 affine，则其 CSP 是
NP-complete。测试会直接从完整真值表检查这六个闭包条件；29 个非基线语言的共同分类
结果均为空。参见 [Schaefer, *The Complexity of Satisfiability Problems*
(1978)](https://doi.org/10.1145/800133.804350)。所有 Γ 都是固定的有限真值表语言，赋值
本身是多项式可验证 witness；本 suite 的形式目标仍只评分 `NativeTMNPHard`。

随机补充使用 `SplitMix64`、种子 `20260820`。前 5 题筛选单关系 hard-side 语言，后 5 题
筛选由一个 0-valid 关系和一个 1-valid 关系组成、但语言层面六类交集为空的双关系语言。
采样器同时保存每个失败闭包的首个字典序反例，见隔离审计 receipt。

## 30 道题目

| # | case | 自然语言题目与精确 Γ | 数学意义 / 归约挑战 |
|---:|---|---|---|
| 1 | canonical-three-sat-like | 普通 3SAT：每个约束是三个带正负号 literal 的析取；`Γ` 含八种 polarity 的三元 clause relation。 | 检查 agent 能否发现库内已有 hardness 路径，是唯一的零 authoring 基线。 |
| 2 | positive-nae4 | 正 NAE-4-SAT：每个四元约束要求四个变量不全相等，即至少有一个 0 且至少有一个 1；`Γ={NAE₄}`。 | 等价于 4-uniform hypergraph 的二染色；必须构造 NAE gadget，不能注入 3SAT 子语言。 |
| 3 | positive-nae3 | 正 NAE-3-SAT：每个三元组不能是 `000` 或 `111`；`Γ={NAE₃}`，bits `01111110`。 | 即 3-uniform hypergraph 二染色，是经典的非平凡 CSP。 |
| 4 | positive-exactly-one3 | 正 1-IN-3-SAT：每个三元约束中恰好一个变量取 1；`Γ={EXACTLY-1-OF-3}`。 | 精确满足约束同时表达“至少一个”和“至多一个”。 |
| 5 | or2-even-parity3 | 每个约束要么是二元 `x∨y`，要么要求三个变量中 1 的个数为偶数；`Γ={OR₂, EVEN-PARITY₃}`。 | OR 部分单独是 bijunctive，parity 部分单独是 affine；组合后不存在共同 Schaefer 类。 |
| 6 | positive-nae5 | 正 NAE-5-SAT：每个五元组必须同时出现 0 和 1；`Γ={NAE₅}`。 | 5-uniform hypergraph 二染色，考查 arity-changing gadget。 |
| 7 | positive-exactly-two3 | 每个三元组中恰好两个变量为 1；`Γ={EXACTLY-2-OF-3}`。 | 是 1-IN-3 的布尔互补对偶，但形式归约必须显式处理全局变量取反。 |
| 8 | positive-exactly-one4 | 每个四元组中恰好一个变量为 1；`Γ={EXACTLY-1-OF-4}`。 | 4 元精确覆盖型约束，要求把 clause satisfaction 编成唯一选择。 |
| 9 | positive-exactly-two4 | 每个四元组中恰好两个变量为 1；`Γ={EXACTLY-2-OF-4}`。 | 平衡的局部基数约束；既不是 parity 方程，也不是 2-CNF relation。 |
| 10 | positive-exactly-three4 | 每个四元组中恰好三个变量为 1；`Γ={EXACTLY-3-OF-4}`。 | 第 8 题的互补对偶，用来检验归约能否系统迁移而非匹配名字。 |
| 11 | positive-exactly-one5 | 每个五元组中恰好一个变量为 1；`Γ={EXACTLY-1-OF-5}`。 | 高 arity 的唯一选择约束。 |
| 12 | positive-exactly-two5 | 每个五元组中恰好两个变量为 1；`Γ={EXACTLY-2-OF-5}`。 | 非对称的固定基数约束，不能退化为 affine 求解。 |
| 13 | positive-exactly-three5 | 每个五元组中恰好三个变量为 1；`Γ={EXACTLY-3-OF-5}`。 | 第 12 题的互补对偶；需保持约束共享变量时的一致性。 |
| 14 | positive-exactly-four5 | 每个五元组中恰好四个变量为 1；`Γ={EXACTLY-4-OF-5}`。 | 第 11 题的互补对偶，语义等价于每个约束唯一选出一个 0。 |
| 15 | positive-exactly-one6 | 每个六元组中恰好一个变量为 1；`Γ={EXACTLY-1-OF-6}`。 | 六元唯一选择 CSP，测试 gadget 的规模参数化。 |
| 16 | positive-exactly-two6 | 每个六元组中恰好两个变量为 1；`Γ={EXACTLY-2-OF-6}`。 | 固定权重为 2 的局部基数 CSP。 |
| 17 | positive-exactly-three6 | 每个六元组中恰好三个变量为 1；`Γ={EXACTLY-3-OF-6}`。 | 完全平衡但非 affine 的局部基数 CSP；“数量为 3”不是模 2 方程。 |
| 18 | positive-exactly-four6 | 每个六元组中恰好四个变量为 1；`Γ={EXACTLY-4-OF-6}`。 | 第 16 题的互补对偶。 |
| 19 | positive-exactly-five6 | 每个六元组中恰好五个变量为 1；`Γ={EXACTLY-5-OF-6}`。 | 第 15 题的互补对偶，等价于每个约束唯一选出一个 0。 |
| 20 | or3-xor2 | 每个约束要么是正三元析取 `x∨y∨z`，要么是二元异或 `x⊕y=1`；`Γ={OR₃, XOR₂}`。 | OR₃ 单独总可由全 1 满足，XOR₂ 单独可线性求解；两类约束耦合后落在 hard side。 |
| 21 | random-table-a | `Γ={TT(4, 0x14E4)}`，接受 16 个四元 tuple 中的 6 个。 | 无语义名称的单关系 hard-side 真值表；六类闭包均有显式反例。 |
| 22 | random-table-b | `Γ={TT(5, 0x5AE4ED46)}`，接受 32 个五元 tuple 中的 17 个。 | 较稠密的五元随机关系，测试完整有限反射而非低元 gadget 匹配。 |
| 23 | random-table-c | `Γ={TT(4, 0x6890)}`，接受 5 个四元 tuple。 | 稀疏随机关系，排除由密度启发式猜测复杂度。 |
| 24 | random-table-d | `Γ={TT(5, 0x6C2A2F22)}`，接受 14 个五元 tuple。 | 五元非对称随机关系。 |
| 25 | random-table-e | `Γ={TT(4, 0x69C6)}`，接受 8 个四元 tuple。 | 恰好半密度但非 affine、非 bijunctive 的随机关系。 |
| 26 | random-table-f | `Γ={TT(3, 0x21), TT(3, 0xE6)}`。 | 第一关系 0-valid、第二关系 1-valid；合并后没有共同 Schaefer 类。 |
| 27 | random-table-g | `Γ={TT(3, 0x71), TT(4, 0x8CF8)}`。 | 混合 arity 双关系语言，常量可满足性在两个 relation 间冲突。 |
| 28 | random-table-h | `Γ={TT(4, 0x6AC7), TT(4, 0x96E2)}`。 | 两个单独可由常量赋值满足的半稠密关系，组合后为 hard side。 |
| 29 | random-table-i | `Γ={TT(4, 0x0C39), TT(5, 0x8DF51404)}`。 | 4/5 元混合随机语言，要求语言层而非单 relation 分类。 |
| 30 | random-table-j | `Γ={TT(5, 0x64ADBF05), TT(3, 0xCA)}`。 | 5/3 元反向混合，补充不同 relation 顺序和闭包反例分布。 |

`EXACTLY-t-OF-k` 接受且仅接受 Hamming weight 为 `t` 的 `k` 位 tuple；`NAEₖ` 接受且
仅接受同时含 0 和 1 的 tuple。若列出真值表 bit，其顺序按 `000…0, …, 111…1`，`1`
表示该 tuple 被 relation 接受。
`TT(k, mask)` 的第 `i` 位对应二进制编号为 `i` 的 `k` 元 tuple，最低位对应全 0 tuple。

## 文件布局与隔离

- Lean 题面：`Lean/Reference/Benchmark/Hardness/Inputs/BooleanCSPNPHard/Case*.lean`
- 公共构造器：`.../BooleanCSPNPHard/Common.lean`，不含 reduction 或 hardness theorem
- 编译聚合：`Lean/Reference/Benchmark/Hardness/BooleanCSPNPHardRegression.lean`
- 公开 suite：`boolean_csp_np_hard_public_v1.json`，不含 expected、gold、route 或 hint
- 隔离 oracle：`Evaluation/boolean_csp_np_hard_oracle_v1.json`
- 随机生成与闭包反例 receipt：`Evaluation/boolean_csp_random_supplement_v1.json`
- 可复现采样/分类器：`agent/hardness/boolean_csp_random.py`
- 唯一 runner：`scripts/run_hardness_benchmark.py`
- scorer：由唯一 runner 在全部选中实例结束后调用库内 scorer，不存在独立评分脚本

## 运行

仅列题和校验公开 suite：

```bash
python scripts/run_hardness_benchmark.py --list
```

复核随机生成结果及 Schaefer 分类：

```bash
python -m agent.hardness.boolean_csp_random
```

运行全部 30 题：

```bash
python scripts/run_hardness_benchmark.py \
  --lane boolean_csp \
  --authoring model-auto \
  --jobs 4 \
  --output-root tmp/boolean-csp-np-hard-v1
```

只跑指定题：

```bash
python scripts/run_hardness_benchmark.py \
  --lane boolean_csp \
  --boolean-csp-case-id q-b01-canonical-three-sat-like \
  --authoring disabled \
  --output-root tmp/boolean-csp-np-hard-smoke
```

生产运行全部结束后，唯一 runner 自动在库内打开隔离 oracle 并写出 score；开发时可用
`--no-score` 禁止评分。
