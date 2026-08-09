# 归约证书输出契约：一次归约 LLM 需要产出什么

日期：2026-06-21
适用：DeepSeek API runner（`scripts/run_deepseek_api_benchmark.py`）及同一 Lean proposition 通道
相关：`DEEPSEEK_API_RUNNER_DESIGN.md`、`Benchmark/README.md`（per-level target shape）

本文回答一个具体问题：**在不编写任何新图灵机（TM）Lean 代码的前提下，LLM 在一次归约中
需要输出哪些文件、每个文件包含哪些内容（语义等价/包含证明、多项式时间证明、路径组合）。**

---

## 1. 输出契约：一个 JSON、一个文件、一段证明

LLM 不接触可写工作区。它只返回**一个 JSON 对象**：

```json
{"certificate_text": "theorem targetClaim : <public target type> := by\n  ...\n"}
```

runner 拥有全部写盘与校验：把 `certificate_text` 写入**唯一文件** `ProofCertificate.lean`，
然后把 **公开 preamble + 该证书** 拼接，用 `lake env lean` 端到端类型检查。判定只看 Lean
是否编译通过。

要点：

- **只有一个文件** `ProofCertificate.lean`，**没有第二个证书文件**，**不写任何 TM 代码**。
- 该文件内可自由定义辅助 `def`/`theorem`，但必须闭合公开的 `targetClaim`（其类型由样例的
  `lean_target_type` 固定）。
- `certificate_text` 通过严格 JSON 抽取（runner `extract_certificate_text`），key 可为
  `certificate_text`/`lean`/`code`。

### 1.1 Phase 1 输出 outcome

Phase 1 的证书 DAG / benchmark 输出只允许两个公开 outcome：

- `verified_certificate`：validator 通过，且机械编译层可以用已有 typed atoms 产出 Lean 证书。
- `typed_missing_obligation`：validator 失败，但失败只由公开 missing-obligation 词表中的代码解释，
  例如 `missing_route_edge`、`missing_source_view_bridge`、`missing_target_bridge`、
  `missing_membership_packet`。

其它失败不伪装成证书 outcome；runner 应报告 failure bucket：
`source_structure_not_recognized`、`library_missing_view_schema_or_target_bridge` 或
`lean_composition_failed_after_schema_selection`。

Phase 1 指标把四条轨道分开统计，不能用 hardness/lower-bound 证明替代 membership：

- lower-bound / hardness verified
- membership verified
- NP-complete verified（需要 lower-bound route 与 target membership 同时闭合）
- boundary-obligation accuracy（missing obligation 是否落在公开 typed 边界上）

若某条指标没有 denominator，报告字符串计数 `0/0`，rate/accuracy/precision 字段为 `null`。
当前 manifest 暴露的 Phase 1 指标包括：
`lower_bound_verified_rate`、`membership_verified_rate`、`npcomplete_verified_rate`、
`boundary_obligation_accuracy`、`view_recognition_success_rate`、`sort_binding_accuracy`、
`relation_binding_accuracy`、`schema_edge_selection_accuracy`、
`source_to_view_bridge_success_rate`、`view_to_target_bridge_success_rate`、
`missing_obligation_precision`。

Phase 8 还要求 outcome 按 obligation layer 记录。报告使用 JSON 友好的 snake_case 层名：
`membership`、`source_to_ir`、`view_to_view`、`view_to_target`、`composition`、
`missing_primitive`、`post_extension_reuse`。runner 接受显式 `phase1.obligation_layer`
或 `phase1.obligation_layers`，也会从 typed missing-obligation code 推断 layer。公开指标为：
`phase1_obligation_layer_outcome_counts`、
`phase1_obligation_layer_verified_certificate_counts`、
`phase1_obligation_layer_typed_missing_obligation_counts`、
`phase1_obligation_layer_total_count`。

---

## 2. 多项式时间从哪来：类型携带 + 组合算子自动传播

这是“不写 TM”可行的根本原因：

- 库中每条已有归约边都是完整的 `KarpReductionM`（含映射 f + 正确性 + 多项式时间），
  而库内的 `PolyTimeMap`/`CostedReduction` 在 `CostedPolyTimeModel` 下**已把复杂度直至 TM
  那一层证好并封装**（`Reference/.../Bridges/CostedToTM`）。
- 因此 LLM **从不单独写一段“多项式时间证明”**。它只要保证：
  - 每个新映射用已有组合子拼（`PolyTimeMap.comp/fst/snd/prod_mk/const/id`）——
    这些算子的返回类型自带 poly-time 证明，复合时自动传播；
  - 每条路径边引用库里现成的 `KarpReductionM`；
  - 多跳用 `PolyReducibleM.trans` 串联——`CostedReduction.comp` 保证组合后仍多项式。
- 结论：**多项式时间是“类型层面的副产品”，不是 LLM 手写的命题证明。**

唯一例外（硬边界）：若引入库中**没有任何 TM-backed 边的全新 base problem**，那条新边的
`CostedMap` 仍需有人把 size bound 证到 TM 层——这是 LLM 跨不过去、必须依赖库已有 gadget
的地方，不在本契约的“外围胶水”范围内。

### 2.1 Declaration index 与 generated route theorem symbol

声明索引里的原始 baseline `KarpReductionM` 声明只表示“可发现的库声明行”，独立于 route
descriptor 是否能导出 generated theorem symbol。可作为证明定理使用的 generated route
descriptor 必须同时具备已检查的 semantic iff、size、costed、TM-backed 四个槽位证据；support-only
symbol 或缺槽 descriptor 不能描述为 generated proof theorem symbol，也不能因 migration status
被提升为 theorem-usable。

已挂载的 Karp21 descriptor row 若缺 costed/size/TM evidence，不得导出 generated descriptor proof
symbol；对应的原始 `KarpReductionM` declaration 仍可作为 declaration-index row 单独检索。

## 3. 证书的统一骨架（所有族共享）

无论 direct membership、多跳 route、本地 adapter 还是 CSP gadget，闭合 `targetClaim` 的证书
都由同一套五段骨架组成（视目标类型裁剪其中若干段）：

1. **编码桥接 / 适配层**（当输入编码 ≠ 库 reference 问题的 exact 形态时）：构造一个
   `ProblemEquivM` 或 `PolyTimeMap` 适配器，把 public `problem` 对齐到 `normalizedProblem`。
2. **路径边**：每跳引用库里现成 `KarpReductionM`，用 `simpa [...] using <库定理>` 对齐 abbrev。
3. **路径组合**：用 `PolyReducibleM.trans` 折叠成 `PolyReducibleM problem target`，
   桥接前缀用 `ProblemEquivM.transportSource bridge route`。
4. **NP 成员收口**：终点 `InNPEnc` 引用库定理；源 `InNPEnc` 由
   `InNPEnc.of_reduction composedReduction targetInNP` 反推。
5. **最终元组**：`refine ⟨…, ?_⟩; exact ⟨…⟩` 按 `targetClaim` 的存在量词/合取顺序收口。

**语义等价/包含**体现在第 1 段的 `to_correct`/`inv_correct` 和第 2 段每跳的 `correct`，
多数情形是 `Iff.rfl` 或 `simpa`。**多项式时间**体现在第 1、2、3 段所用构件的类型里，自动传播。

---

## 4. 四类样例的 certificate 实样

### 4.1 L0 direct membership —— 最简，只有一行

输入要求 `InNPEnc M problem`，且 `problem` 就是库 reference 问题：

```lean
def goldCertificate : <target type> := by
  exact ComplexityReduction.Karp21.Clique.cliqueInNP
```

LLM 只需：定位库里现成的 `*InNP` 定理并 `exact`。无适配、无路径、无组合。
（来源：`Benchmark/GoldProofs/L0/clique.lean`）

### 4.2 L10 三跳 route synthesis —— 五段骨架全展开

输入 `problem` 是带 flag 的 nested 编码，要求合成一条到某 NPC 目标的多跳 route。证书包含：

```lean
-- 第 1 段：编码桥接（语义等价 + poly-time 映射）
def sourceProjection : PolyTimeMap CostedPolyTimeModel problem.Instance sourceProblem.Instance :=
  PolyTimeMap.comp (PolyTimeMap.snd ...) (PolyTimeMap.comp (PolyTimeMap.fst ...) (PolyTimeMap.fst ...))
def sourceInjection : PolyTimeMap ... sourceProblem.Instance problem.Instance :=
  PolyTimeMap.prod_mk (PolyTimeMap.prod_mk (PolyTimeMap.const ... false) (PolyTimeMap.id ...)) ...
def encodingBridgeCertificate : ProblemEquivM CostedPolyTimeModel problem normalizedProblem where
  toMap := sourceProjection
  invMap := sourceInjection
  to_correct := fun _ => Iff.rfl      -- 语义等价：isYes 双向蕴含
  inv_correct := fun _ => Iff.rfl

-- 第 2 段：三条路径边，各引用库里现成 KarpReductionM
def reductionStep1 : KarpReductionM ... normalizedProblem routeTarget1 := by
  simpa [...] using ComplexityReduction.Karp21.SetCovering.vertexCoverToSetCoveringKarpReduction
def reductionStep2 : KarpReductionM ... routeTarget1 routeTarget2 := by simpa [...] using ...
def reductionStep3 : KarpReductionM ... routeTarget2 routeTarget3 := by simpa [...] using ...

-- 第 3 段：组合（trans 折叠 + 桥接 transportSource）
def normalizedRoute : PolyReducibleM ... normalizedProblem routeTarget3 :=
  PolyReducibleM.trans (PolyReducibleM.trans ⟨reductionStep1⟩ ⟨reductionStep2⟩) ⟨reductionStep3⟩
def composedReduction : PolyReducibleM ... problem routeTarget3 :=
  ProblemEquivM.transportSource encodingBridgeCertificate normalizedRoute

-- 第 4 段：NP 成员收口
def routeTarget3InNP : InNPEnc ... routeTarget3 := by simpa [...] using ...steinerTreeInNP
def sourceInNP : InNPEnc ... problem := InNPEnc.of_reduction composedReduction routeTarget3InNP

-- 第 5 段：最终存在量词元组
theorem goldCertificate : ∃ normalizedProblem ..., ∃ routeTarget1 ..., ...,
    PolyReducibleM ... problem routeTarget3 ∧ InNPEnc ... routeTarget3 ∧ InNPEnc ... problem := by
  refine ⟨normalizedProblem, routeTarget1, routeTarget2, routeTarget3,
          encodingBridgeCertificate, reductionStep1, reductionStep2, reductionStep3, ?_⟩
  exact ⟨composedReduction, routeTarget3InNP, sourceInNP⟩
```

（来源：`Benchmark/GoldProofs/L10/deep_vertex_cover_three_hop_synthesis.lean`）

### 4.3 L8 本地 adapter —— 用 PolyTimeMap 自建一条归约边

输入编码是 nested wrapper，目标问题在投影分量上。证书自建一条 adapter 归约：

```lean
def localAdapterProof : ∀ x, problem.isYes x ↔ localAdapterTarget.isYes x.1.2 := by
  exact Iff.rfl                                  -- 语义包含：投影后 isYes 一致
def localAdapterMap : PolyTimeMap ... := PolyTimeMap.comp innerSnd outerFst   -- 用组合子拼，poly-time 自动
def localAdapterReduction : KarpReductionM ... := ...   -- 由 map + correct 组装
...
theorem goldCertificate : ... := by
  exact ⟨localAdapterReduction, localAdapterRoute, localAdapterTargetInNP, sourceInNP⟩
```

（来源：`Benchmark/GoldProofs/L8/nested_nae3_csp_local_adapter.lean`）

### 4.4 L11 CSP gadget 组合 —— 用已有 gadget 边拼新路线

输入要求把已有 CSP gadget 归约组合成一条经 3SAT pivot 的新路线：

```lean
def sourceToPivotGadget : KarpReductionM ... normalizedProblem pivot := by simpa [...] using <库 gadget 边>
def pivotToTargetGadget : KarpReductionM ... pivot targetProblem := by simpa [...] using <库 gadget 边>
def composedGadgetRoute : PolyReducibleM ... := PolyReducibleM.trans ⟨sourceToPivotGadget⟩ ⟨pivotToTargetGadget⟩
def sourceInNP : InNPEnc ... := InNPEnc.of_reduction composedGadgetRoute targetInNP
theorem goldCertificate : ... := ...
```

（来源：`Benchmark/GoldProofs/L11/left_nested_nae3_roundtrip_composed_gadget.lean`）

---

## 5. LLM 实际要动脑写的“外围胶水”一览

| 要素 | 写法 | 多项式时间从哪来 |
| --- | --- | --- |
| 文件数 | **1 个** `ProofCertificate.lean` | — |
| 语义等价/包含 | `ProblemEquivM` 的 `to_correct`/`inv_correct`、各跳 `correct`（多为 `Iff.rfl`/`simpa`） | LLM 写，通常 `rfl` |
| 编码适配映射 | `PolyTimeMap.comp/fst/snd/prod_mk/const/id` 拼 | **类型自带，组合子自动传播** |
| 各跳归约 | `simpa using <库 KarpReductionM>` | **封装在库定理里** |
| 多跳组合 | `PolyReducibleM.trans` / `ProblemEquivM.transportSource` | **`.trans` 自动复合，无需重证** |
| NP 收口 | `InNPEnc.of_reduction` + 存在量词元组 | 库定理 |
| TM 复杂度 | **不写** | 库 `Bridges/CostedToTM` 已封装 |

**一句话**：不写 TM 时，LLM 的全部产出 = 一个 `ProofCertificate.lean`，内含「选 route + 写编码
桥接的投影/注入映射 + 证几个 `correct` 的 `Iff`（多数 `rfl`）+ 用 `trans`/`transportSource`
组合 + `of_reduction` 收口」。多项式时间消耗的证明随类型自动复合，无需手写。
