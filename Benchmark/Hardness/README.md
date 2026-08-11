# Hardness benchmark

本仓库只有一个 benchmark runner：

```text
scripts/run_hardness_benchmark.py
```

它直接调用 `agent/hardness/` 中的库 API；不得通过 subprocess、`runpy` 或
Python 脚本路径调用其他 runner。仓库中不得再增加第二个 `run_*.py`。

公开 `Suites/*.json` 一共冻结 78 个互不重复的实例：

| lane | 数量 | 评分 |
|---|---:|---|
| capability | 32 | isolated capability oracle |
| frontier | 2 | 不评分 |
| exact_edge | 24 | isolated exact-edge oracle |
| boolean_csp | 20 | isolated Boolean-CSP oracle |
| 总计 | 78 | 76 个评分实例 |

`BENCHMARK_REGISTRY.json` 必须与全部 suite 精确一致。runner 的生产阶段只读公开
suite；oracle 只能在该 lane 全部实例运行结束后由库内 scorer 打开。

## 命令

列出并校验全部 78 个实例，不调用 Lean 或模型：

```bash
python3 scripts/run_hardness_benchmark.py --list
```

使用正式 DeepSeek 配置运行和评分全部实例：

```bash
python3 scripts/run_hardness_benchmark.py \
  --output-root .reduction-agent/benchmark-full \
  --jobs 4
```

只运行一个或多个 lane：

```bash
python3 scripts/run_hardness_benchmark.py \
  --lane boolean_csp \
  --output-root .reduction-agent/benchmark-boolean-csp \
  --jobs 4
```

合法 lane 为 `capability`、`frontier`、`exact_edge`、`boolean_csp`；重复传入
`--lane` 可以组合。Boolean CSP 还支持 `--boolean-csp-case-id` 和
`--boolean-csp-split`，Capability/Frontier 支持 `--capability-case-id`，Exact Edge
支持对应的 case/split 选择参数。

## 非 runner 工具

`prove_np_hard.py` 是单个 Lean 问题的证明 CLI，不负责 suite、benchmark 计数或
评分。仓库不再保留历史 Gate、stage builder 或 publication runner；任何需要执行
benchmark 的工作都必须进入唯一 runner。
