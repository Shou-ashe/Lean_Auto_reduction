# `problems.7z` 真实归约题转化计划

按 benchmark 当前三个 lane 分类，将 `ACTIVE_AGENT_IMPROVEMENT_PLAN.md` §12（`problems.7z`
真实归约题转化计划）落为三个子目录下的结构化计划文件：

| 子目录 | lane | 内容 | 对应计划章节 |
|---|---|---|---|
| `exact_edge/PLAN.json` | exact_edge（计分 v1） | 第一批 24 个唯一方向候选（dev 6 / validation 6 / held-out 12） | §12.2 |
| `frontier/PLAN.json` | frontier（不评分 F0/reserve） | 第二批结构化 reserve 15 个 + PDF-only reserve/frontier 16 个 + 长期 F0 编号 | §12.4、§12.5、§12.6 |
| `capability/PLAN.json` | capability（计分 v2） | spot-check 与 capability_weight 0 条目；无 problems.7z 题目进入计分分母 | §12.1.4、§12.3.2、§12.5 |

## 与其他数据文件的关系

- `exact_edge/PLAN.json` 的 24 个 case 与 `Suites/exact_reduction_edge_{dev,validation,heldout}_v1.json`
  的 case_id 一一对应，状态来自 `Evaluation/np_hard_problem_archive_selection_v1.json` 与
  `PROBLEM_ARCHIVE_AUDIT.json`。
- `frontier/PLAN.json` 的 PDF-only 候选 id 与 `PROBLEM_ARCHIVE_AUDIT.json` 的
  `pdf_only_candidates[].candidate_id` 一致。
- 转换计划本身（solution、hint、PDF proof、本节转化说明）均视为 oracle/provenance 数据，
  运行时 filesystem allowlist 必须排除 `problems.7z` 及其任何解压副本（§12.1.5）。plan 文件
  不得被 runner 或 prompt builder 读取。

## 验收规则（§12.7）

1. split 隔离须同时按 endpoint、direction motif 与 construction family 校验，防止 dev 模板
   以改名形式进入 held-out。
2. 报告须分别输出 `unique_directions`、`statement_variants`、`endpoint_ready`、
   `new_presentations`、`existing_edge_reconstructed`、`new_edge_verified`、
   `direct_gadget_verified` 与 blocker 分布。
3. `blocked_endpoint_formalization` 的 17 个 case 在两端 PresentedProblem 通过独立
   definition/encoding/membership/identity 审计前不进入计分分母。