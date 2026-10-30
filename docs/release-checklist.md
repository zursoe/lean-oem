# 0.1.0 候选版本发布检查清单

## 仓库和版本

- [x] `lean-toolchain` 固定 Lean `v4.35.0`。
- [x] `lakefile.toml` 固定 Mathlib 输入版本 `v4.35.0`。
- [x] `lake-manifest.json` 记录 Mathlib 和传递依赖提交。
- [x] `.lake`、编译产物和本机规则文件没有进入 Git。
- [x] `scripts/run_audit.sh` 和 `scripts/validate_oem_numeric.py` 在 Git 中保留执行位。
- [x] `api/linear-core` 从远端 `main` 建立，并已通过 PR #1 合并到远端主线。
- [x] 版本说明、范围说明和来源映射已写入 `docs/`。
- [x] `.github/workflows/ci.yml` 已固定 action 提交，并覆盖构建、审计和精确数值校验。

## 构建和测试

- [x] 本地 `lake build` 成功。
- [x] `LeanOEM.Tests.Basic` 编译成功。
- [x] 一维精确矩阵示例编译成功。
- [x] 秩亏 `2 × 1` 示例编译成功。
- [x] 负定、零矩阵和非对称协方差边界编译成功。
- [x] `scripts/validate_oem_numeric.py` 独立有理数验证成功。
- [x] `scripts/run_audit.sh` 完整运行成功。
- [x] 本地按 CI 顺序运行 `lake build`、`bash scripts/run_audit.sh --no-build` 和 `python3 scripts/validate_oem_numeric.py` 成功。
- [x] 干净 checkout 重新物化依赖并完成 3166 个构建目标。

## 可信性和公理

- [x] 源代码没有 `sorry`、`admit` 或未登记自定义 `axiom`。
- [x] 核心定理执行 `#print axioms`。
- [x] 核心定理只依赖 `propext`、`Classical.choice` 和 `Quot.sound`。
- [x] 形式假设、形式定理、数值证据和外部文献已分开记录。

## 公开前人工审查

- [x] 检查矩阵方向和转置约定。
- [x] 检查 `observationErrorCovariance` 的语义。
- [x] 检查总函数矩阵逆的使用条件。
- [x] 检查后验、Joseph 和信息形式的适用假设。
- [x] 检查数值脚本没有成为 Lean 证明的隐含依据。
- [x] 在远端 GitHub runner 上完成 CI 运行并检查日志；push、PR 和合并到 `main` 的运行均通过。
- [x] 线性核心实现已完成审阅并合并到 `main`；后续正演和辐射传输模块按新路线单独审阅。
