# Complexity Reduction Agent：活动改进计划

> 状态：Active
>
> 更新日期：2026-08-10
>
> 当前唯一优先主线：把 `problems.7z` 中冻结的真实 reduction 题变成可运行、可评分、真实调用模型的 exact-edge benchmark。

## 0. 本文档只保留未完成工作

以下内容已经完成，不再在活动计划中重复维护：

- H-I 已由 `Reports/MAIN_H_I_FULL_REPORT.json` 证明通过；
- H-J 已由 `Reports/MAIN_H_J_FULL_REPORT.json` 证明通过；
- H-I/H-J 冻结记录：44 个公共 identity、24 个唯一方向、至少 8 个此前没有现成最终路线的 heldout authoring 方向、至少 4 个 authoring family；
- unified benchmark、capability v2、frontier 边界组、exact-edge 三个 split、归档审计和 24 题转换计划已经存在；
- 旧文档中按 H-I/H-J case 逐条展开的历史实施表、已经失效的 baseline 数字、重复的 reserve 列表和旧 runner 入口说明全部删除。

H-K publication/reuse 代码路径仍可作为后续独立工作包，但不再占用本活动计划；必须先完成本计划中的真实 exact-edge authoring 闭环。

当前权威输入是：

- `Reports/PROBLEM_ARCHIVE_AUDIT.json`；
- `Planning/ProblemConversionPlan/exact_edge/PLAN.json`；
- `Planning/ProblemConversionPlan/frontier/PLAN.json`；
- `Benchmark/Hardness/EXACT_REDUCTION_EDGE_MANIFEST.json`；
- `Benchmark/Hardness/Suites/exact_reduction_edge_dev_v1.json`；
- `Benchmark/Hardness/Suites/exact_reduction_edge_validation_v1.json`；
- `Benchmark/Hardness/Suites/exact_reduction_edge_heldout_v1.json`；
- `Evaluation/exact_reduction_edge_oracle_v1.json`；
- `Benchmark/Hardness/BENCHMARK_REGISTRY.json`。

如果文档与这些机器可读文件冲突，以审计报告、转换计划和冻结 manifest 为准，并在同一个变更中修正文档。

## 1. 当前事实与问题定义

### 1.1 已经完成的数据工作

`problems.7z` 的权威结构化来源包含：

- 63 道清洗后题目；
- 60 个唯一 reduction direction；
- 37 个 solution、16 个 hint；
- 24 个已冻结 exact-edge case，split 为 dev 6、validation 6、heldout 12；
- 初始 7 个端点 ready、17 个 `blocked_endpoint_formalization`；已按本计划 2.2 完成全部 17 个端点的形式化，当前 24/24 端点 ready（`Evaluation/exact_reduction_edge_oracle_v1.json` 与 `Planning/ProblemConversionPlan/exact_edge/PLAN.json` 的 status/status_counts 已同步，归档审计 selection 文件保留 7/17 初始状态绑定）。

归档的 README 中残留 64 题的陈旧描述已经记录为 documentation drift，不得覆盖 `problems_clean.json` 和审计报告中的 63 题权威计数。

### 1.2 当前 benchmark 状态

统一 registry 已包含 50 个 case：

- capability：24；
- frontier：2；
- exact-edge：24。

当前 exact-edge 运行虽然能完成调度和评分，但还没有形成“新 reduction 由模型逐阶段写出”的闭环：

- 已存在路线的控制题可以被检索并以零模型调用完成，这是预期行为；
- 要求新 primitive 的题仍可能复用已有路线，随后才被隐藏 scorer 判为 bypass；
- 端点 ready、但没有现成 planner DAG 的题会以 `exact_edge_authoring_dag_unavailable` 结束；
- 17 个端点未形式化的题必须在模型调用前 fail closed，不能让 LLM 临时定义 benchmark 端点；
- 当前 exact-edge lane 主要把 case 交给通用 `reduce_to` agent，尚缺 exact-edge 专用的多阶段 task class、公开 construction policy 和逐节点真实调用协议。

本计划实现状态（代码与数据已完成，等待真实 API 里程碑运行）：

- 公开 case schema 已包含 `construction_policy`、`statement_hash`、`endpoint_contract_version`；
- `typed_exact_edge_construction_dag` task class、planner DAG、单节点 answer-free prompt、逐节点 ledger、checkpoint/resume 与 staged executor 已实现并接入 exact-edge lane；
- 24/24 端点 ready；scorer 对 public policy 与 oracle policy 做一一对应校验。

### 1.3 本计划的完成定义

最终系统必须区分三种情况：

1. `existing_edge_reconstruction`：允许检索已有 exact edge，预期零模型调用，但仍要重新执行全部 exact-edge 审计；
2. `direct_new_edge`：禁止通过已有 route 或组合绕过，必须由 LLM 多阶段写出新 primitive、证明和最终证书；
3. `blocked_endpoint_formalization`：端点未通过独立审计时不调用 LLM，不计入可解分母。

exact-edge 成功必须得到题目指定的精确 `CertifiedReduction source target`。仅证明 target NP-hard、找到其他终点、或通过已有 route 间接到达 target 都不能算成功。

## 2. 加入真实题目前，项目代码必须先写什么

这一部分由项目实现者完成，不是 benchmark 运行时交给 LLM 的内容。

### 2.1 公开 case schema 与答案隔离

升级 exact-edge public suite schema。每个公开 case 至少包含：

```json
{
  "case_id": "...",
  "module": "...",
  "source": "exact PresentedProblem declaration",
  "target": "exact PresentedProblem declaration",
  "statement": "answer-free problem statement",
  "statement_hash": "sha256:...",
  "budget_profile": "formal-default",
  "construction_policy": {
    "mode": "existing_edge_reconstruction | direct_new_edge",
    "allow_composition": false,
    "require_new_primitive": true
  },
  "endpoint_contract_version": "..."
}
```

公开 `construction_policy` 是任务要求，不是答案泄漏。它必须在 production run 前可见，使 runner 能在生成阶段阻止错误路线；以下内容继续只存在于隐藏 oracle：

- solution、hint、PDF 证明内容及其可恢复文本；
- 归档中的 transform plan 和推荐构造；
- `existing_route` 的 gold 绑定；
- 精确 `forbidden_route_imports`；
- scorer mutation、solution hash 和选择注释。

运行隔离要求：

- `problems.7z`、解压目录、`problems_clean.json`、PDF、solution、hint、conversion plan 和隐藏 oracle 均不得进入 agent workspace；
- prompt 只能包含公开 statement、精确端点、当前节点签名、允许的公共 API、已验收依赖和上一轮编译诊断；
- 任何 `recommended_first_body`、预填 `response_template`、gold declaration body 或可直接拼装答案的 packet 都不得用于 `direct_new_edge`；
- statement、source、target、policy、prompt 和最终 artifact 必须通过 hash 链绑定。

需要修改或重新冻结：

- `agent/hardness/np_hard_exact_edge.py` 的 suite/manifest schema 校验；
- 三个 exact-edge suite；
- exact-edge manifest 的 suite hash；
- benchmark registry 的绑定 hash；
- exact-edge oracle 与公开 case 的一一对应检查；
- archive/oracle isolation 和 schema 负例测试。

### 2.2 17 个缺失端点必须先形式化

每个新问题端点至少需要提交以下静态 Lean 组件：

- `Instance`/carrier 类型；
- `accepts`、`isYes` 或等价判定谓词；
- 输入 well-formedness 和非法输入语义；
- `LawfulEncodedType`/codec，且大小度量与二进制编码一致；
- 精确的 `PresentedProblem` 或 `StructuredProblem` declaration；
- identity reduction、membership/endpoint probe 或等价的独立可用性证明；
- declaration hash、依赖闭包、axiom、kernel replay 和 endpoint audit；
- 与归档 statement 的语义对齐说明，但不得把 solution 放入 public module。

端点状态只能在上述组件全部通过后由 `blocked_endpoint_formalization` 改为 `ready`。缺少任一端点时，runner 必须在创建 model client/request 之前停止该 case。

端点形式化状态（已完成）：E1 的 `HalfClique`、`DoubleThreeSAT`、`NAEThreeSAT`（codec 审计）、`SubsetSum`、`IndependentSet`，E2 的复用 wrapper（`IndependentSet`/`NAEThreeSAT`/`SubsetSum` + `Partition` 数值编码核对），E3 的 `DominatingSet`、`DenseSubgraph`、`TSP`、`HamiltonianPath`，E4 的 `SetSplitting`、`OneInThreeSAT`、`ExactCoverBy3`、`ExactCoverBy4` 均已提交 `Lean/Reference/ComplexityReduction/Presentation/`，通过 `lake env lean` 编译、`assert_standard_axioms` 与两个 Endpoints 导入模块编译；`_prepare_case_wrapper` 对 24/24 case 的公开 wrapper 编译通过。

按依赖顺序实施：

| 波次 | Case | 需要新增或冻结的端点工作 |
|---|---|---|
| E1 validation 基础 | `edge-val-02-clique-to-half-clique` | `HalfClique` 的实例、阈值语义、well-formedness、codec、PresentedProblem |
| E1 validation 基础 | `edge-val-03-three-sat-to-double-sat` | `DoubleThreeSAT`，特别是声明变量集合上的赋值计数语义 |
| E1 validation 基础 | `edge-val-04-three-sat-to-nae-three-sat` | `NAEThreeSAT` 的精确三元 relation presentation 与 codec |
| E1 validation 基础 | `edge-val-05-subset-sum-to-knapsack` | `SubsetSum` presentation、数值编码和目标值合法性 |
| E1 validation 基础 | `edge-val-06-clique-to-independent-set` | `IndependentSet` presentation、至少 k 个点的语义和边界输入 |
| E2 复用 E1 | `edge-held-03-independent-set-to-vertex-cover` | 复用 `IndependentSet`，新增本 case 的 exact wrapper 和 statement binding |
| E2 复用 E1 | `edge-held-08-nae-three-sat-to-chromatic` | 复用 `NAEThreeSAT`，新增本 case 的 exact wrapper 和 statement binding |
| E2 复用 E1 | `edge-held-10-subset-sum-to-partition` | 复用 `SubsetSum`，核对 `Partition` 的数值编码契约并冻结 wrapper |
| E3 图与优化端点 | `edge-held-01-vertex-cover-to-dominating-set` | `DominatingSet` presentation 和退化图语义 |
| E3 图与优化端点 | `edge-held-02-clique-to-dense-subgraph` | `DenseSubgraph (G,a,b)`、参数合法性和无溢出 Nat 语义 |
| E3 图与优化端点 | `edge-held-04-independent-set-to-set-packing` | `SetPacking` presentation、集合去重与元素身份语义 |
| E3 图与优化端点 | `edge-held-11-hamiltonian-cycle-to-tsp` | `TSP`/`WeightedGraphInput`、complete tour、cost bound 和 directed flag |
| E3 图与优化端点 | `edge-held-12-hamiltonian-cycle-to-path` | `HamiltonianPath` presentation，空图和单点图语义 |
| E4 CSP/集合族端点 | `edge-held-05-nae-three-sat-to-set-splitting` | `SetSplitting` presentation 和二分 witness 语义 |
| E4 CSP/集合族端点 | `edge-held-06-three-sat-to-one-in-three-sat` | `OneInThreeSAT` 的 exact-three relation presentation |
| E4 CSP/集合族端点 | `edge-held-07-one-in-three-to-exact-cover` | `ExactCover` 的元素身份、无重复集合和 witness 语义 |
| E4 CSP/集合族端点 | `edge-held-09-exact-cover-three-to-four` | `ExactCoverBy3`/`ExactCoverBy4` restricted presentations 和 size promise |

`Planning/ProblemConversionPlan/exact_edge/PLAN.json` 继续作为 24 个 direction、split、role 和 endpoint readiness 的权威矩阵，不在本文复制归档 solution 或完整构造方案。

## 3. Runner 必须如何修改

### 3.1 保留统一入口，改造 exact-edge lane

顶层命令继续使用 `scripts/run_hardness_benchmark.py`，不再增加新的并行 benchmark 入口。需要修改的是 exact-edge lane 内部：

- `scripts/run_hardness_benchmark.py` 只负责 registry、lane、`--jobs 4`、model client、resume 和输出目录；
- `agent/hardness/np_hard_exact_edge.py` 负责 endpoint preflight、construction policy、case workspace、逐节点 ledger 和 exact scorer binding；
- `agent/hardness/np_hard_authoring_planner.py` 增加 exact-edge 专用 task class；
- `agent/hardness/np_hard_authoring.py` 和 `np_hard_authoring_contract.py` 增加节点类型、prompt/response schema、prefix checkpoint 和 fail-closed 校验；
- 通用 `HardnessAgent(objective="reduce_to")` 可以继续提供检索和基础 probe，但不能再作为 `direct_new_edge` 的唯一执行逻辑。

### 3.2 新 task class

新增 `typed_exact_edge_construction_dag`。planner 根据公开端点类型、公开 construction policy 和 capability catalog 生成 typed DAG，但不得读取 solution/oracle 来生成代码。

该 task class 至少支持以下 LLM-written 节点；具体 case 可省略不适用的 optional 节点，但不能跳过最终审计要求：

| 节点 | 运行时由 LLM 写什么 | 验收边界 |
|---|---|---|
| `parameter-normalization` | 非法、退化或显然 yes/no 输入的正规化 body | 编译、端点类型、分支覆盖 |
| `reduction-primitive` | 直接 source instance 到 target instance 的构造 | 禁止 route bypass；输出类型精确 |
| `gadget-definitions` | case 所需 gadget、辅助变量或中间结构 | 只能依赖公开 API 和已验收节点 |
| `output-wellformed` | 构造保持 target well-formedness 的证明 | 独立 Lean replay |
| `semantic-forward` | source witness/acceptance 推出 target acceptance | 不允许使用 reverse lemma 循环证明 |
| `semantic-reverse` | target witness/acceptance 恢复 source acceptance | deletion/dependency audit |
| `semantic-iff` | 将两个方向封装为精确 iff | source/target statement hash 绑定 |
| `poly-program` | 可执行 reduction program 或对应 `PolyProgram` body | 程序可运行且输出与 primitive 对齐 |
| `polynomial-bound` | 时间/输出大小/编码长度的多项式界 | binary-size audit，不接受仅数学值界 |
| `program-direct-tm-coherence` | program、direct TM 和数学 primitive 的一致性 | coherence audit |
| `certified-reduction` | 最终精确 `CertifiedReduction source target` body | kernel、replay、axiom、endpoint、dependency 全通过 |

runner 生成 imports、namespace、declaration signatures、占位标记和最终 wrapper；LLM 只返回当前节点允许替换的 body，不得一次返回整个文件或修改已验收节点。

### 3.3 一个 case 的多阶段调用协议

一个 `direct_new_edge` case 必须按 DAG 顺序多次调用模型：

1. planner 冻结节点、依赖和每节点允许的 declaration；
2. runner 为当前节点创建最小 prompt；
3. 模型返回单节点 body；
4. runner 写入隔离 workspace，执行 Lean 编译和节点专属 policy audit；
5. 成功则把节点加入 `accepted_nodes` checkpoint，失败只把压缩后的相关诊断交给同一节点下一次 attempt；
6. 当前节点 attempt budget 耗尽则停止该 case，不得跳过节点或回退到预写答案；
7. 全部节点通过后再构建最终 artifact，执行独立 clean replay 和 scorer。

默认每节点最多 4 次真实调用。调用预算按“实际 DAG 节点数 × 每节点 attempt budget”计算，而不是继续沿用“一个 case 最多 4 次、每次尝试整份证明”的语义。

并行规则：

- case 之间最多 4 并行，与 `--jobs 4` 一致；
- 同一个 case 内节点按依赖顺序串行；
- 每次调用必须记录 request id、case id、node id、attempt、model、HTTP status、token usage、prompt hash、response hash、workspace hash 和最终状态；
- run 结束时 active model calls 必须为 0；
- resume 只能复用 hash 完全匹配且已独立验证的节点 checkpoint。

### 3.4 Prompt 内容

`direct_new_edge` prompt 只能包含：

- answer-free statement；
- source/target 的精确 declaration 名称和可见类型；
- 当前节点签名、允许返回的 JSON/body schema；
- construction policy，例如“必须直接构造、禁止组合 route”；
- public API allowlist；
- 已通过节点的 declaration signatures，必要时包含其公开 body；
- 上一次 attempt 的最小 Lean/policy diagnostics；
- 剩余 token、attempt 和 timeout budget。

禁止包含：

- `recommended_first_body`；
- 已填好的 replacement body；
- solution、hint、PDF proof、conversion `transform_plan`；
- hidden oracle、gold route、gold theorem body；
- 其他 case，尤其 validation/heldout case 的答案或中间产物。

### 3.5 Production 与 scorer 的 policy 对齐

当前 `allow_composition`、`require_new_primitive` 等关键约束只在隐藏 scorer 中出现，会导致 production 先走错误路线、评分时才拒绝。改造后：

- 公开 suite 给出抽象 construction policy；
- production runner 根据抽象 policy 阻止 composition、route import 和非新 primitive；
- hidden oracle 继续保存精确 forbidden declarations、gold route、审计列表和 mutation；
- production report 不得写出 oracle 内容；
- scorer 重新计算 endpoint、dependency、directness、coherence、semantic iff 和 polynomial bound，不能信任 run report 的汇总布尔值。

## 4. 24 个冻结 case 的实施顺序

### 4.1 第一里程碑：先让 7 个 ready case 行为正确

| Case | 预期运行方式 | 当前要补的内容 |
|---|---|---|
| `edge-dev-01-three-sat-to-clique` | existing reconstruction，零调用 | 精确 route 重放和完整审计 |
| `edge-dev-02-three-sat-to-zero-one-ip` | existing program/gadget，零调用 | program/direct-TM coherence 和参数审计 |
| `edge-dev-03-three-sat-to-chromatic` | existing multi-node edge，零调用 | gadget、固定 k=3 和 endpoint 参数审计 |
| `edge-dev-04-chromatic-to-clique-cover` | existing graph duality，零调用 | 精确 `(G,k)` endpoint 和 complement coherence |
| `edge-dev-05-set-cover-to-hitting-set` | existing route，零调用 | 先冻结归档 source metadata correction，再重放 exact edge |
| `edge-dev-06-undirected-to-directed-hc` | `direct_new_edge`，多阶段真实调用 | 新 primitive、两个语义方向、poly/coherence、最终 certificate |
| `edge-val-01-vertex-cover-to-set-cover` | `direct_new_edge`，多阶段真实调用 | 禁止复用现有 route；新 cross-representation program 和全部证明 |

第一里程碑不以“有模型请求”笼统计分，而是要求：前 5 个控制题保持零调用，后 2 个新边题均产生非零、逐节点、HTTP 200 的真实调用 ledger，并最终通过 exact-edge scorer。

### 4.2 第二里程碑：补齐 validation

E1 五个端点已完成，validation 已从 1 个 ready 扩展到 6 个 ready。每个新晋 ready case 都使用 `typed_exact_edge_construction_dag`，不得把 `Planning/ProblemConversionPlan/exact_edge/PLAN.json` 中的构造说明放进 prompt。

完成条件：dev 6 + validation 6 共 12 个 case 全部具有诚实终态；所有 direct-new case 有真实模型 ledger，所有 existing controls 维持零调用。

### 4.3 第三里程碑：补齐 heldout

E2、E3、E4 端点依赖顺序已完成，heldout 12 个 case 全部 endpoint-ready。heldout 在 endpoint、schema、prompt 和 planner DAG 冻结后不得用于调 prompt 或人工挑选策略。

heldout 运行时：

- 不向模型暴露 split 对应的 archive source、solution 或 transform plan；
- 不允许从 dev/validation 复制 case-specific theorem body；
- 允许复用已经正式发布、content-addressed 且不含 case-specific gold 的通用组件；
- scorer 对 route bypass、unexpected existing route、statement drift 和 dependency stale 做 mutation 检查。

最终目标是 24 个 case 全部 endpoint-ready，并在冻结环境中完成 24/24 的诚实 exact-edge 结果。

## 5. Frontier 组如何处理

当前两个 unary Knapsack/Partition frontier case 是 encoding-aware hardness boundary。它们的零模型调用是预期语义：缺少合法 reverse bridge 时应直接 blocked，不能为了产生调用而让模型猜证明。

真正的“高难真实试题 frontier”应从 `Planning/ProblemConversionPlan/frontier/PLAN.json` 中另行晋升，并满足：

- source/target 两端已独立 endpoint-ready；
- direction 没有泄漏到 capability/dev 的 case-specific artifact；
- 需要新 gadget、跨 representation primitive、数值编码证明或多节点 witness 证明；
- public construction policy 已冻结；
- hidden oracle 和 mutation 已在运行前冻结；
- 运行时使用与 exact-edge 相同的多阶段 LLM authoring 协议。

在 24 个 problems exact-edge 没有完成前，不扩充 frontier scored denominator。

## 6. 测试、报告和验收门槛

### 6.1 必须新增或更新的测试

- `tests/test_hardness_np_hard_exact_edge.py`：public policy schema、endpoint preflight、多节点 ledger、directness、resume；
- `tests/test_hardness_np_hard_authoring_planner_v2.py`：`typed_exact_edge_construction_dag` 的节点和依赖；
- `tests/test_hardness_np_hard_authoring_v2.py`：单节点 response、accepted-prefix、失败重试和禁止回写旧节点；
- `tests/test_hardness_benchmark_oracle_isolation.py`：archive、solution、hint、oracle、transform plan 不进入 workspace/prompt/output；
- `tests/test_hardness_np_hard_archive_audit.py`：63/60/37/16、24、7/17 和 split 计数保持绑定；
- `tests/test_hardness_np_hard_unified_benchmark.py`：4 并行 case 调度、case 内串行 DAG、真实 ledger 汇总；
- negative/mutation tests：已有 route bypass、composition bypass、statement drift、endpoint alias、stale checkpoint、伪造 token ledger、binary-size bound 缺失。

测试不得通过把 `recommended_first_body` 直接复制为模型响应来证明 direct-new 路径可用。可以为 parser/协议单测使用最小 synthetic body，但正式 integration 必须使用与 production 相同的无答案 prompt。

### 6.2 分阶段真实 API 运行

每个里程碑都运行：

1. 无模型的 schema、endpoint、oracle-isolation、mutation 和 deterministic tests；
2. `--lane exact_edge --jobs 4` 的真实 API production run；
3. 隔离 scorer；
4. fresh output 的第二次 clean run；
5. resume/replay run；
6. 汇总正式 report，并绑定命令、git tree、manifest、suite、oracle、model config、token usage 和所有 case artifact hash。

正式报告建议新增为 `Reports/MAIN_PROBLEMS_EXACT_EDGE_FULL_REPORT.json`，只聚合已有 production/score 证据，不在 report builder 内运行模型或 Lean。

### 6.3 硬门槛

数据与隔离：

- archive hash、63 道题、24 个冻结方向、6/6/12 split、7/17 初始状态全部一致；
- solution/hint/PDF/conversion plan/oracle 零 prompt 泄漏；
- public statement 与 artifact statement hash 完全一致。

模型调用：

- `direct_new_edge` 的 verified case 必须 `model_calls > 0`；
- 每个 model call 必须对应唯一 case/node/attempt；
- existing controls 和 endpoint-blocked cases 必须 `model_calls == 0`；
- 不允许 deterministic fallback、预写 body fallback 或 scorer-side 补证明；
- 真实运行结束时 active calls 为 0，最大 case 并行度为 4。

形式化正确性：

- exact source/target endpoint；
- Lean kernel compile 与独立 clean replay；
- axiom audit；
- dependency/deletion audit；
- endpoint well-formedness；
- program/direct-TM coherence；
- semantic iff；
- polynomial time、output size 和 binary encoding bound。

策略正确性：

- `require_new_primitive` 不得被已有 route 或组合绕过；
- hidden forbidden imports 命中时 fail closed；
- blocked endpoint 不进入可解分母；
- unexpected existing route、statement drift 或 stale dependency 使总报告失败。

里程碑通过标准：

- M1：7 个初始 ready case 全部通过；5 个 existing controls 零调用，2 个 direct-new case 多阶段真实调用；
- M2：dev+validation 12/12 通过；
- M3：24 个 frozen exact-edge case endpoint-ready 且 24/24 通过；
- M4：在不改变 unary frontier 边界语义的前提下，再冻结新的 endpoint-ready frontier 真实试题。

## 7. 实施顺序

1. 升级 public construction policy、suite schema、manifest/hash 和 isolation tests；
2. 实现 `typed_exact_edge_construction_dag`、单节点 prompt/response 和逐节点 ledger；
3. 用 7 个 ready case 完成 M1，先修复 dev06 与 val01 的真实 direct-new authoring；
4. 完成 E1 端点并运行 M2；
5. 完成 E2/E3/E4 端点，冻结 heldout 后运行 M3；
6. 生成 `MAIN_PROBLEMS_EXACT_EDGE_FULL_REPORT`；
7. 只有 M3 通过后，才恢复 publication/reuse 工作包或扩充 frontier。

在本计划完成前，不再以“runner 返回了 Lean 代码”作为充分证据。必须同时回答：代码来自已有路线还是模型新写、写了哪些节点、每个节点是否真实调用、最终是否为题目指定的精确 reduction，以及全部证明和复杂度审计是否独立通过。
