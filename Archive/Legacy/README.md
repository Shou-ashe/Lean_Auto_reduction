# Quarantined legacy benchmark sources

本目录不是当前 benchmark，也不能交给 current runner 执行。

- `Opencode/` 保存原 107 个 YAML、68 个 HiddenTargets、39 个 GoldProofs 及旧文档；
- `V2Hardness/` 保存原 3 个 `ComplexityReduction_IR.V2` 输入与旧 manifest；
- 所有 110 个旧 case 的处置状态见 `../MIGRATION_LEDGER.json`。

这些文件保留是为了让仍标为 `deferred` 的 case 可继续逐项重写，而不是保留旧评测入口。旧 schema
会被 `agent.hardness.benchmark` 以 `unsupported_legacy_benchmark` 拒绝。正式运行、模型 workspace、
candidate import allowlist、production aggregate 和当前通过率都排除整个 `Legacy/`。

当某个 deferred case 完成 current exact-type port 后，应：

1. 在 `Lean/Reference/Benchmark/Hardness/Inputs/` 建立 public importable module；
2. 加入相应 `Suites/*.json`；
3. 添加 non-authoritative `Expected/<case-id>.json`；
4. 通过 exact request、resolver、axiom gate 和 replay；
5. 将 ledger disposition 更新为 `migrated`、`split` 或经审计的 `deprecated`。

在 ledger 中仍有 `deferred` 项时，不删除其唯一迁移来源。
