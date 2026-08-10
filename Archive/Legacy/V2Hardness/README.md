# V2 Hardness Agent Benchmark

本目录是第一版 V2 hardness 自动归约 Agent 的 smoke/regression benchmark。它测试的不是 LLM
能否手写 Lean proof，而是以下闭环是否成立：

```text
exact PresentedProblem 输入
  -> 可选 checked Cook–Levin root
  -> validated registry 路线（可直接停在 3SAT，或接 production suffix）
  -> 可选 DeepSeek allowlist 重排
  -> ClosedResolver 重新闭合
  -> kernel-checked TypedAutoReductionResult
```

总体设计见根目录 `V2_HARDNESS_AGENT_DESIGN.md`，Lean 可信入口见
`LeanAutoReduction/Agent/V2/Hardness.lean`。

## 目录

```text
Benchmark/V2Hardness/
  Inputs/
    ThreeSAT.lean
    TaggedThreeSAT.lean
    KnapsackNativeNP.lean
  MANIFEST.json
  README.md
```

`Inputs/` 中的文件是输入 ABI 样例；`MANIFEST.json` 是不可信的测试编排数据，不是 registry 或
proof certificate。

## 当前用例

| case id | 输入能力 | 覆盖点 | 最低原子数 |
| --- | --- | --- | ---: |
| `three_sat_to_known_np` | canonical structured 3SAT `PresentedProblem` | 不生成新 root，直接复用 production registry 到一个 native-NP target | 1 |
| `tagged_three_sat_normalization` | 带 ignored Boolean tag 的 3SAT wrapper | 复用 registered ingress normalization 到 native target，并允许继续走下游 route | 1 |
| `native_np_via_checked_cook_levin` | structured Knapsack + exact `NativeTMInNP` | job 内生成 checked `source -> structured 3SAT` root；3SAT 可直接作为 native-NP target，也可继续接 production suffix | 1 |

当前 manifest 故意不固定最终 target。registry 扩展后，deterministic planner 可以选到另一条更短路线；
benchmark 的稳定验收条件是最终 artifact verified 且路线至少含指定数量的 validated atoms，而不是
匹配一个 Python 中写死的 theorem name。

## 输入 ABI

最小输入只需一个闭合的 exact V2 presentation：

```lean
import Some.V2.Module

namespace MyInput

abbrev source : ComplexityReduction_IR.V2.Encoding.PresentedProblem :=
  somePresentedProblem

end MyInput
```

若希望任意 V2-native NP source 都能经统一 Cook–Levin root 接入已有路线，再提供：

```lean
theorem membership :
    ComplexityReduction_IR.V2.Certificate.NativeTMInNP source :=
  someNativeMembership
```

这里必须是 exact `NativeTMInNP source`，只有 backend `ComplexityReduction.TMInNP` 不够。
runner 会把输入文本复制到 `Probe.lean` 和 `Artifact.lean`，并在 Lean 中以所给全限定 term 重新检查
类型。以 `prelude` 开头或包含 `#exit` 的输入会被拒绝。

## 运行 benchmark

离线、可复现的默认运行：

```bash
python3 scripts/run_v2_hardness_benchmark.py
```

等价的显式命令：

```bash
python3 scripts/run_v2_hardness_benchmark.py \
  --manifest Benchmark/V2Hardness/MANIFEST.json \
  --planner deterministic
```

只跑一个或多个 case：

```bash
python3 scripts/run_v2_hardness_benchmark.py \
  --case native_np_via_checked_cook_levin \
  --planner deterministic
```

指定输出目录：

```bash
python3 scripts/run_v2_hardness_benchmark.py \
  --output-root .reduction-agent/manual-v2-hardness-benchmark
```

benchmark 默认输出到：

```text
.reduction-agent/v2_hardness_benchmark/<UTC timestamp>/
```

全部选中 case 均通过时退出码为 `0`；任一失败或没有选中任何 case 时退出码为 `1`。

2026-07-18 对当前实现实际执行 deterministic 全集的结果为：

```text
three_sat_to_known_np                 PASS  verified  atoms=1
tagged_three_sat_normalization       PASS  verified  atoms=1
native_np_via_checked_cook_levin     PASS  verified  atoms=1
total                                3/3
```

这是 smoke baseline；最终可信判据仍是每个 `Artifact.lean` 的重新编译，而不是这段文档中的计数。

## 运行单个 Agent job

已有 registry source：

```bash
python3 scripts/run_v2_hardness_agent.py \
  --input Benchmark/V2Hardness/Inputs/ThreeSAT.lean \
  --source Benchmark.V2Hardness.ThreeSAT.source \
  --planner deterministic
```

使用 checked Cook–Levin root：

```bash
python3 scripts/run_v2_hardness_agent.py \
  --input Benchmark/V2Hardness/Inputs/KnapsackNativeNP.lean \
  --source Benchmark.V2Hardness.KnapsackNativeNP.source \
  --membership Benchmark.V2Hardness.KnapsackNativeNP.membership \
  --planner deterministic \
  --output-dir .reduction-agent/v2-hardness-knapsack
```

还可以用 `--target` 将候选限制为 probe 输出的 exact target term，或该 target 的 native-membership
declaration。这个 Python filter 只影响候选集合；最终 target、route 和 membership 仍由 Lean 重新
检查。

单 job 的退出码：

- `0`：`verified`；
- `2`：`blocked`，例如没有可达 native-NP target，或显式 `deepseek` 模式缺少 key；
- `1`：其他输入、构建、probe 或 final artifact 失败。

若未给 `--output-dir`，默认输出到：

```text
.reduction-agent/v2_hardness/<UTC timestamp>_<input stem>/
```

## 使用 DeepSeek

默认 API 配置为：

```text
base URL: https://api.deepseek.com
model:    deepseek-chat
key env:  DEEPSEEK_API_KEY
```

runner 会依次读取项目根目录 `.env` 与 `.env.local`，但只补充尚未存在的环境变量。也可以通过
CLI 传入 key、base URL、model 和 timeout。示例：

```bash
export DEEPSEEK_API_KEY='...'
python3 scripts/run_v2_hardness_benchmark.py --planner deepseek
```

planner 模式的含义：

- `deterministic`：选原子数最少的 validated route，再按 target/atoms 做稳定字典序 tie-break；
- `deepseek`：必须成功调用模型并返回 allowlist 中的 `route_id`，否则 job blocked；
- `auto`：有 key 时调用 DeepSeek；无 key、请求失败或响应无效时回退 deterministic。

单 job CLI 默认 `auto`；benchmark CLI 为离线复现默认 `deterministic`。

DeepSeek 收到的只是 Lean probe 已验证的 route allowlist，包括 target、membership declaration、原子
provenance 和 role。它只能返回一个 `route_id`，不能提交 Lean term、添加 route、改变 endpoint 或
授予证明能力。API key 不写入 `report.json`。

## Manifest 格式

当前 schema：

```json
{
  "schema_version": "lean_auto_reduction_v2_hardness_benchmark_v1",
  "cases": [
    {
      "id": "case_id",
      "input": "Benchmark/V2Hardness/Inputs/Input.lean",
      "source": "Fully.Qualified.source",
      "membership": "Fully.Qualified.membership",
      "target": "Optional.Exact.Target.OrMembershipDeclaration",
      "minimum_route_atoms": 1
    }
  ]
}
```

字段说明：

- `id`：输出子目录名和 `--case` 选择键；
- `input`：相对项目根目录的 Lean 输入文件；
- `source`：闭合 `PresentedProblem` term；
- `membership`：可选，exact `NativeTMInNP source` term；
- `target`：可选，限制候选 target；
- `minimum_route_atoms`：benchmark 额外检查的最小 validated 原子数。

`membership` 和 `target` 可省略。manifest 中的字符串不会直接成为证明；它们会进入生成的 Lean
source 或候选 filter，错误值最终导致 probe/final elaboration 失败或 blocked。

## 每个 job 的生成物

每个 case/job 输出目录包含：

```text
Probe.lean
Artifact.lean                 # 找到可达路线后生成
report.json
deepseek/
  route_selection_prompt.txt  # 仅实际调用 DeepSeek 时
  route_selection_response.json
```

### `Probe.lean`

它导入 `LeanAutoReduction.Agent.V2.Hardness` 和原输入；若 manifest/CLI 提供 membership，还声明一个
带 typed-edge attribute 的本地 Cook–Levin root。随后执行：

```lean
#v2_hardness_probe source
```

probe 日志包含 source、所有 validated native-NP targets，以及已经由 `ClosedResolver` 解析出的
非空路线；`V2_HARDNESS_REGISTRY` 还记录由 validated candidate name 与 elaborated type hash
构成的轻量 read-only fingerprint。日志和 fingerprint 都是观察结果，不是 certificate，也不是
密码学承诺。

### `Artifact.lean`

它重新声明同一个可选 Cook–Levin root，固定 exact-user policy 和
`.reduceToKnownNP source selectedTarget` request，最终只用：

```lean
noncomputable def result : TypedAutoReductionResult request :=
  by_v2_hardness_resolver
```

文件尾部对 `result` 以及本地 Cook–Levin root（若有）执行 `assert_v2_standard_axioms`。因此
`Artifact.lean` 成功编译才是 `verified` 的判据；注释中列出的 selected atoms 仅用于审计。

### `report.json`

报告记录：

- build、probe 和 artifact 命令的退出码、截断日志与耗时；
- probe targets/routes；
- `goal_ir`：source/membership、输入文件 SHA-256、objective、policy、elaborated source 和 registry
  fingerprint；
- `hardness_plan`：target、native membership、atoms/roles、planner selection 和 registry fingerprint；
- planner 模式、选择和 DeepSeek usage/error；
- selected target、native membership、atoms 和 roles；
- blockers、trust-policy 摘要和生成文件路径。

GoalIR/HardnessPlan、输入 SHA-256 和 fingerprint 都是可复现审计数据，没有反向恢复为 registry
capability 的入口。报告不是 proof；修改 `status`、`selected_atoms`、GoalIR/HardnessPlan 或 benchmark
顶层 `passed` 不会产生 Lean certificate。

benchmark 根目录另有汇总 `report.json`，schema 为
`lean_auto_reduction_v2_hardness_benchmark_report_v1`。

## 独立验证

验证 Lean runtime 和端到端 regression：

```bash
lake env lean LeanAutoReduction/Agent/V2/Hardness.lean
lake env lean LeanAutoReduction/Agent/V2/HardnessRegression.lean
lake build LeanAutoReduction Benchmark
python3 -m pytest -q tests/test_v2_hardness_agent.py
```

也可以直接重新编译某次生成物：

```bash
lake env lean .reduction-agent/v2_hardness_benchmark/<run>/<case>/Artifact.lean
```

## 如何判断失败

优先按以下顺序检查：

1. `report.json` 的 `blockers`；
2. `build.stderr` / `build.stdout`；
3. `probe_check.stderr` / `probe_check.stdout`；
4. `Probe.lean` 中 source 和可选 membership 的精确类型；
5. `planner` 是否因 target filter、缺 key 或无效 route ID blocked；
6. `artifact_check.stderr` / `artifact_check.stdout`；
7. `Artifact.lean` 的 exact request target 是否仍存在于当前 production registry。

没有路线时，先判断 source 是否本来就有 registered outgoing edge；若没有，应提供 exact
`NativeTMInNP source` 以启用 checked Cook–Levin。只有 backend membership 时应补 V2 verifier
encoding discipline，而不是把 theorem name 写进 manifest 规避检查。

## 已知边界

- 这是三例 smoke benchmark，不是任意 NP 问题的覆盖率评测；
- 只覆盖 exact `PresentedProblem`、V2-native membership 与 polynomial-time many-one reduction；
- 不测试自动发明新 gadget、adapter、primitive、verifier 或语义 proof；
- target 会随 production registry 演化，当前测试不固定具体问题名；
- DeepSeek 只测 allowlist reranking，不测 whole-proof generation；
- 未覆盖 semantic-source presentation admission、native completeness 输出、logspace、counting、
  approximation 或 optimization reduction；
- production aggregate 未导入的声明不会成为候选；
- 参数化/open family 必须先形成闭合的、可验证的具体 Lean 声明。
