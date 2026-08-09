# Complexity Reduction Agent：活动改进计划

> 状态：Active  
> 更新日期：2026-08-09  
> 当前工作包：H-G（正式 CLI 输入契约与验收配置统一）  
> 初步目标：用户输入 Complexity Reduction 公共 Lean 库内已有的决策问题，agent 自动复用或构造从库内已知 NP-hard 问题到该输入的正向规约，并输出由 Lean kernel 接受、结论精确为 `NativeTMNPHard input` 的证明。

本文件已删除此前的完成态内容，只保留尚未完成的改进工作。工作包通过全部验收后必须从本文件删除；实现历史、命令、指标和内容哈希只保留在 `Benchmark/Hardness/MAIN_H_*_FULL_REPORT.json` 及其引用报告中。

## 一、初步目标的严格输入与成功定义

### 1. 输入对象

1. 正式输入是一个库内已有的决策问题，而不只是数据表示类型：
   - 首选完整 Lean `PresentedProblem` 声明；
   - 允许 stable ID、alias 或 wrapper；
   - 裸 `LawfulEncodedType` 只有在当前模块真实 import closure 中能够唯一解析到一个已有 lawful presentation 时才可接受。
2. 多个判定谓词可能共享同一个 encoding，因此裸 encoding 无法唯一确定问题时必须返回 `ambiguous_lawful_presentation`，不得猜测用户意图。
3. 用户给出完整声明时，CLI 应能够自动解析所属模块；仍允许显式 `--module` 覆盖。不存在、越出公共 import closure 或无法形成 lawful presentation 时必须返回稳定失败码。

### 2. 成功对象

一次正式成功必须同时满足：

1. 证明目标精确为用户输入的 canonical `PresentedProblem`，最终 Lean 类型为 `NativeTMNPHard input`。
2. 规约方向必须是从已知 NP-hard seed/hub 到输入问题；反向规约、相似端点、相同 representation 的其他谓词均不得算成功。
3. 最终 artifact 通过 Lean kernel、独立 replay、standard axiom audit、endpoint equality audit 和依赖删除审计。
4. 模型只能填写确定性 planner 生成的精确 typed gap，不得决定目标、方向、成功判定、axiom policy 或评测答案。
5. 已有确定性路线和结构性负例保持零模型调用。

### 3. 目标边界

1. 当前目标只证明 NP-hard，不证明 NP membership 或 NP-complete。
2. 不要求、也不允许对所有库内问题一概证明 NP-hard；2-CNF、well-formedness、内部 IR 辅助谓词等可能不属于目标集合。
3. 必须建立 identity 级的正式目标矩阵，区分：
   - `in_scope_np_hard`：本轮必须最终验证为精确 `NativeTMNPHard input`；
   - `auxiliary_or_non_target`：有可审计的库结构或正式策略依据，不进入 NP-hard 成功分母；
   - `unclassified`：暂时未知，计划完成前必须清零；
   - `blocked_missing_formal_prerequisite`：已识别准确缺失定理或组件，但仍属于未完成工作，不得冒充目标完成。
4. “没有找到证明”不得被解释为“该问题不是 NP-hard”；二者必须使用不同状态与失败码。

## 二、当前基线与已确认差距

以下数字来自 H-E inventory 和 held-out 报告，只作为新计划基线，后续以重新生成的内容寻址报告为准：

1. 公共库 inventory 包含 200 个模块、253 个 `PresentedProblem` 声明和 44 个唯一问题 identity。
2. 44 个 identity 中只有 22 个具有已知正向 hardness route；另外 22 个没有路线，也没有真正执行 authoring 资格化。
3. 原 inventory 中 79 个声明被标记为 `not_evaluated_outside_initial_np_hard_target_set`，因此“枚举到”不等于“可证明或已正确阻塞”。
4. H-E 的 8 个正例中，只有 Vertex Cover 与 Exact Cover 直接来自 `ComplexityReduction.*` 公共模块，且均复用已有路线。
5. H-E 的 4 个 model-authoring 正例全部来自 `Benchmark.Hardness.Inputs.*` 合成 fixture；真实公共库 authoring 验证数为 0。
6. 当前 authoring planner 只支持 `semantic_proof`、`program_composition`、`program_synthesis` 三类固定 task，并依赖预先存在的 hardness hub、typed gap、poly program、mapping relation 或 primitives。
7. 正式 `scripts/prove_np_hard.py` 默认仍为 120 秒、4096 tokens、8 次调用预算，而通过真实 V4 Flash 验收的 NP-hard 配置为 300 秒、16000 tokens。
8. `scripts/run_np_hard_release_stability.py` 的源码默认模型仍是 `deepseek-chat`；此前通过验收依赖显式命令行覆盖。
9. 生成证明主要保存在 fresh `tmp/...` job 中，尚未形成可稳定 import、可登记、可在下一任务零调用复用的公共证明资产。
10. 三轮稳定性重复固定 fixture，尚未给出不同真实公共问题上的首次成功率、预算内成功率和跨 family 泛化率。

因此，旧 `Complete` 只能解释为“安全框架与代表性 benchmark 完成”，不能解释为“初步目标已覆盖真实公共库输入”。

## 三、所有工作包统一强制回归协议

H-G 至 H-K 每个工作包结束时都必须在全新 output/job 目录依次通过以下门禁；任一门禁失败都不得删除当前工作包或进入下一阶段。

### 1. 代码与 Lean 门禁

1. 运行本工作包全部相关 Python 单元测试、契约测试、mutation 测试与 Lean 编译测试。
2. 运行完整 `pytest`，不得跳过长测试、mock 生产编排或历史回归。
3. 对新增成功 artifact 执行独立 Lean process replay、standard axiom audit、endpoint equality audit、fresh-core dependency rediscovery 和逐节点删除审计。

### 2. 真实 DeepSeek V4 Flash 门禁

所有正式模型门禁必须明确使用：

```text
provider             = DeepSeek
base_url             = https://api.deepseek.com
model                = deepseek-v4-flash
reasoning_effort      = low
temperature           = 0
max_retries           = 0
NP-hard max_tokens    = 16000
NP-hard timeout       = 300 seconds
main-45 max_tokens    = suite 中已验收的 16384
```

要求：

1. 禁止使用 `deepseek-chat`、其他模型、fixture client、录制响应、缓存响应或离线响应冒充正式调用。
2. 使用 `scripts/run_hardness_benchmark.py --agent-phase 7` 完整执行主 45 benchmark：45/45 必须符合预期，所有真实模型 HTTP 调用必须为 200，正例必须通过 kernel/replay/axiom audit。
3. 使用 `scripts/run_np_hard_release_stability.py` 在全新目录执行 3 轮完整发布套件：最低门禁为 36/36、15/15 authoring、已有路线零模型调用、全部删除审计通过、worker fallback 为零。
4. 运行本工作包新增的全部 held-out/qualification 案例；必须通过 `scripts/prove_np_hard.py` 或相同生产 `NPHardOrchestratorV2`，不得绕过正式入口直接调用内部 runtime。
5. 每个模型 gap 节点必须保存 prompt/response 内容哈希、HTTP 状态、模型名、finish reason、token usage、Lean diagnostics 和候选验证结果。
6. API key、Authorization header 与敏感环境变量不得写入 prompt、日志或公共报告。

### 3. 报告门禁

1. 每个工作包生成 `Benchmark/Hardness/MAIN_H_<阶段>_FULL_REPORT.json`。
2. 报告记录 schema、源码哈希、活动计划测试前/完成后哈希、Lean toolchain、lake manifest、输入 suite 哈希、模型配置、真实调用数、token usage、全部 replay/audit 结果和 fresh output 路径。
3. `.git` 不可用时必须记录原因，并以逐文件 SHA-256 作为权威 source control 证据。
4. 只有相关测试、完整测试、主 45、三轮稳定性和阶段 held-out 全部通过时，报告才允许写入 `passed: true`。

## 五、H-G：正式 CLI 输入契约与验收配置统一

### 目标

确保用户执行默认生产命令时，使用的正是已经通过真实 V4 Flash 验收的配置与输入语义，不再依赖人工补充隐藏参数。

### 实现内容

1. 将 `scripts/prove_np_hard.py` 默认配置统一为 `deepseek-v4-flash`、low reasoning、300 秒、16000 tokens、0 SDK retries；调用预算必须按 DAG 节点数和 attempt budget 安全计算，不得小于完整 DAG 的最小需求。
2. 修复 `.env`、环境变量和 CLI 参数的优先级：显式 CLI > 环境/`.env` > 已验收默认值；不得用 argparse 的旧默认值静默覆盖 `.env`。
3. 将 `scripts/run_np_hard_release_stability.py`、H-E/H-F runner、README 和 `.env.example` 的默认模型全部统一为 `deepseek-v4-flash`，删除生产路径中的 `deepseek-chat` 默认值。
4. 增加启动 preflight：打印并写入脱敏后的实际 provider、model、timeout、tokens、reasoning effort、call budget；非 V4 Flash 正式 qualification 必须 fail closed。
5. 支持只给完整 `--problem` 时自动发现所属公共模块；显式 `--module` 仍可覆盖并接受一致性校验。
6. 对裸 encoding 返回 canonical presentation 或稳定的 missing/ambiguous 错误与候选列表，不得猜测谓词。
7. 统一机器可读输出 schema，清楚区分 `VERIFIED`、`BLOCKED_NOT_TARGET`、`BLOCKED_MISSING_PREREQUISITE`、`FAILED_MODEL`、`FAILED_LEAN` 与输入错误。

### 完成标准

1. README 中最短默认命令无需额外 timeout/token 参数即可复现已验收配置。
2. 契约测试证明所有生产 runner 的默认模型均为 `deepseek-v4-flash`，仓库生产路径不存在 `deepseek-chat` 默认值。
3. 至少一个真实公共库 authoring 案例通过用户可见 CLI 默认配置产生真实 V4 Flash 调用并最终 `VERIFIED`。
4. 输入模块自动发现、显式覆盖、missing presentation 和 ambiguous presentation 均通过正式入口测试。
5. 主 45、三轮稳定性和 H-G CLI held-out 全部通过真实 V4 Flash 门禁。

## 六、H-H：公共库已有路线的逐 identity 生产验证

### 目标

把 inventory 中“图可达”升级为真实生产入口逐 identity 的 kernel-verified 结果，验证所有已有路线目标，而不把 catalog reachability 当作成功证明。

### 实现内容

1. 对 H-F 矩阵中所有具有正向路线的公共 identity 逐一调用生产 orchestrator；definitionally equal alias 只验证一次 canonical identity，并另测 alias normalization。
2. 为每个 identity 生成精确 `NativeTMNPHard input` artifact、独立 replay、axiom 和 endpoint audit。
3. 验证 shortest route、组合 route 与 representation adapter 的方向和端点；发现 catalog edge 与实际 Lean artifact 不一致时 fail closed。
4. 已有路线全程模型调用必须为零；任何非零调用都视为 deterministic reuse 回归。
5. 生成 identity 级 `PUBLIC_EXISTING_ROUTE_QUALIFICATION_REPORT.json`，不得按 174 个重复声明夸大覆盖。

### 完成标准

1. H-F 矩阵中全部 existing-route canonical identity 均由正式入口验证；预期基线为 22/22，实际数量以 H-F 重算结果为准。
2. 全部成功 artifact 精确命中 canonical 输入，模型调用为 0，replay/axiom/endpoint audit 通过。
3. 至少 12 个 answer-free organic held-out 全部来自 `ComplexityReduction.*`，覆盖 route 长度 0 至当前最大长度和至少 5 个 family。
4. 主 45、三轮稳定性和 H-H 公共路线 held-out 全部通过真实 V4 Flash 门禁；模型调用只允许发生在统一门禁中明确需要 authoring 的案例。

## 七、H-I：面向真实公共问题的通用 typed authoring planner

### 目标

将 authoring 从三个合成 fixture 模板扩展为可对真实公共库 NP-hard 目标构造新规约的通用 typed capability planner。

### 实现内容

1. 对 H-F 中 `blocked_missing_formal_prerequisite` 的真实目标聚类，按缺失能力而不是问题名设计可复用节点。
2. 在现有三类 task 基础上增加可组合能力节点，至少覆盖：
   - representation/instance adapter；
   - reduction function 或 gadget construction；
   - parameter transformation；
   - mapping invariant；
   - semantic forward/reverse implication；
   - executable relation coherence；
   - polynomial-size/time bound；
   - CertifiedReduction 组装与 NativeTMNPHard 传递。
3. planner 必须从真实 Lean catalog、公开源码和 exact typed gaps 生成 DAG；禁止按 case ID、目标名称或 benchmark 特判选择模板。
4. DeepSeek 每次只编辑一个节点的精确 declaration body；已接受节点内容寻址并冻结，后续节点只能引用已发布依赖。
5. 支持在多个 hardness hub 中按可验证的安全/成本排序选择唯一正向 hub；并列时返回 `ambiguous_authoring_hub`，不得任意选择。
6. 对缺少库级数学前提的目标生成精确 blocker，例如缺 reduction specification、缺 gadget invariant、缺 polynomial bound；禁止退化成笼统的 `authoring_plan_missing_capability`。
7. 优先覆盖真实公共候选：Knapsack、Hitting Set、MaxCut、Partition、Feedback Node/Arc Set、3D Matching，以及 H-F 新发现的其他 in-scope 目标。

### 完成标准

1. 至少 8 个此前没有现成最终路线的真实 `ComplexityReduction.*` canonical identity 通过模型 authoring 得到精确 `NativeTMNPHard input`。
2. 覆盖至少 4 个 family、单缺口、多缺口、程序组合、新 gadget/program synthesis 和 polynomial bound。
3. 8 个成功目标不得来自 `Benchmark.Hardness.Inputs.*`，不得通过 alias 重复计数，且不得包含按目标名称硬编码的 planner 分支。
4. 每个节点通过 fresh-core、逐节点删除审计；删除任一节点后最终证明必须失效。
5. 主 45、三轮稳定性和 H-I organic authoring held-out 全部通过真实 V4 Flash 门禁。

## 八、H-J：证明资产发布、登记与跨任务零调用复用

### 目标

把一次性 `tmp/.../Final.lean` 转换为稳定、可 import、可审计、可作为后续 hardness seed/route 使用的公共证明资产。

### 实现内容

1. 设计 generated hardness package 与 publication manifest，记录 canonical endpoint、source hub、route、源码哈希、toolchain、lake manifest、模型调用证据和全部 audit 哈希。
2. 发布前在隔离目录重建，不得依赖原 job 的绝对路径、worker 状态、临时 `.olean` 或未声明文件。
3. 发布成功后将 theorem/CertifiedReduction 登记到公共 hardness/connection catalog，并触发完整 catalog 重建与 identity fingerprint 更新。
4. 对同一输入再次运行生产入口时，必须自动发现已发布路线并保持零模型调用。
5. 处理源码或依赖漂移：旧资产标记 stale，禁止静默复用；重新验证成功后生成新内容地址。
6. 提供非破坏性的候选审阅/发布命令；正式 benchmark 可以在隔离发布区验证，但不得污染手写公共库源码。

### 完成标准

1. 至少 4 个 H-I 真实公共 authoring 证明发布为稳定 Lean 模块并被 catalog 发现。
2. clean dependency checkout 风格 replay 全部通过，artifact 不引用原 fresh output 绝对路径。
3. 对已发布的 4 个目标二次运行全部零模型调用，结论与第一次 canonical endpoint 完全一致。
4. 删除或篡改发布节点、manifest 或依赖哈希时必须 fail closed。
5. 主 45、三轮稳定性和 H-J publication/reuse held-out 全部通过真实 V4 Flash 门禁。

## 九、H-K：真实公共库泛化、可靠性门禁与初步目标最终封板

### 目标

用完全 organic、answer-free、未参与 planner 开发的公共库输入证明系统达成初步目标，并以 identity 级目标矩阵而不是 fixture 成绩作为完成依据。

### 实现内容

1. 建立最终 answer-free held-out suite：
   - 全部输入来自公共 `ComplexityReduction.*`；
   - 至少 16 个不同 canonical identity；
   - 至少 5 个 family；
   - 同时覆盖 existing route、已发布 authored route、首次 authoring、missing/ambiguous presentation、wrong direction 和非目标输入；
   - 至少一半正例不得参与 H-F 至 H-J 的 planner/template 开发。
2. 评测 oracle 单独保存，生产 suite 只含 module/problem/family，不含 expected、task class、gap nodes、gold、route 或 authoring policy。
3. 对首次 authoring 节点记录 first-attempt pass rate、budgeted pass rate、每问题调用数、token、Lean 失败类型和修复次数。
4. 执行至少 3 轮全新 job 的 organic held-out；每轮重新调用真实 V4 Flash，不得复用模型响应。
5. 对 H-F 目标矩阵重新全量资格化：所有 `in_scope_np_hard` identity 必须最终 `VERIFIED`；`unclassified` 与 `blocked_missing_formal_prerequisite` 必须为 0，才能宣告初步目标完成。
6. 生成最终覆盖报告，分别报告 canonical identity 覆盖、declaration/alias 数、existing-route 数、authored 数、发布复用数、正确非目标数、失败数、真实 API 调用和 token；稳定性重复轮次不得冒充不同问题覆盖。

### 完成标准

1. 最终 organic held-out 所有正例得到精确 `NativeTMNPHard input`，所有负例/非目标得到正确稳定状态。
2. 至少 16 个正例 canonical identity 全部验证，其中首次 authoring 与 published reuse 均有覆盖；不得使用 `Benchmark.Hardness.Inputs.*` 作为 organic 成功分子。
3. 三轮 organic held-out 均 100% 在规定 attempt/call budget 内完成，已有路线与发布复用路线模型调用为 0，worker fallback 为 0。
4. 全部模型调用为真实 `deepseek-v4-flash` HTTP 200；报告中不存在 `deepseek-chat`、fixture、缓存响应、答案泄漏、hidden/gold import 或敏感信息。
5. H-F 目标矩阵中全部 `in_scope_np_hard` identity 为 `VERIFIED`，没有未分类或缺 formal prerequisite 的目标。
6. 主 45、三轮发布稳定性、最终 organic held-out、完整 pytest 与所有 Lean/audit 门禁同时通过。
7. 只有满足以上全部条件后，才能删除 H-K，将计划状态改为 `Complete`，并将“尚存升级内容”写为“无”。

## 十、执行顺序

```text
H-G 正式 CLI 与 V4 默认配置统一
  -> H-H 公共库已有路线逐 identity 生产验证
  -> H-I 真实公共问题通用 authoring
  -> H-J 证明发布与跨任务复用
  -> H-K organic 泛化与最终封板
```

不得跳过依赖阶段。允许在当前工作包内部并行实现 schema、测试、Lean fixture 和报告工具，但只有当前工作包的相关测试、完整测试、主 45、三轮稳定性、阶段 held-out 与内容寻址报告全部通过后，才能删除当前工作包并推进下一阶段。
