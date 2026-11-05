# 0.1.0 候选版本发布检查清单

当前状态：尚未发布。线性核心的历史审查已经完成，但当前主线还包含实验性 Physics 模块和
前向/Jacobian 联合误差扩展；以下清单需要针对完整主线重新执行。

## 仓库和版本

- [x] `lean-toolchain` 固定 Lean `v4.35.0`。
- [x] `lakefile.toml` 固定 Mathlib 输入版本 `v4.35.0`。
- [x] `lake-manifest.json` 记录 Mathlib 和传递依赖提交。
- [x] `.lake`、编译产物和本机规则文件没有进入 Git。
- [x] `scripts/run_audit.sh` 和 `scripts/validate_oem_numeric.py` 在 Git 中保留执行位。
- [x] `api/linear-core` 从远端 `main` 建立，并已通过 PR #1 合并到远端主线。
- [x] 版本说明、范围说明和来源映射已写入 `docs/`。
- [x] 稳定 `LeanOEM.Core` 与实验 `LeanOEM.Physics` 的入口边界已由独立 `CoreEntry` 和显式 Physics 导入示例验证。
- [x] 奇异半正定先验的 `SupportFactor` 接口保持在稳定 Core，未修改正定 `PriorFactor` 的语义。
- [x] 半正定先验的自动 `PriorSqrtFactor` 和 canonical `range` support 已加入稳定 Core。
- [x] canonical support 的 EuclideanSpace 正交规范基、有限坐标列矩阵及其满列秩/像空间
  契约已加入稳定 Core。
- [x] `PriorSqrtFactor.toSupportFactor` 已自动提供平方根支持因子的 Gram 恒等式和满列秩。
- [x] 自动支持因子的列空间等于 canonical support。
- [x] 当前主线已有与代码范围一致的版本说明和审计提交号（`4cc7343`）。
- [x] `.github/workflows/ci.yml` 已固定 action 提交，并覆盖构建、审计和精确数值校验。

## 构建和测试

- [x] 本地 `lake build` 成功。
- [x] `LeanOEM.Tests.Basic` 编译成功。
- [x] 一维精确矩阵示例编译成功。
- [x] 秩亏 `2 × 1` 示例编译成功。
- [x] 奇异先验支持坐标、支持内可观测/不可观测和 ambient 不可观测边界示例编译成功。
- [x] 负定、零矩阵和非对称协方差边界编译成功。
- [x] `scripts/validate_oem_numeric.py` 独立有理数验证成功。
- [x] `scripts/run_audit.sh` 完整运行成功。
- [x] 本地按 CI 顺序运行 `lake build`、`bash scripts/run_audit.sh --no-build` 和 `python3 scripts/validate_oem_numeric.py` 成功。
- [x] 历史提交 `e803313` 的干净 checkout 重新物化依赖并完成 3166 个构建目标。
- [ ] 当前候选代码重新完成干净 checkout 构建。

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
- [ ] 前向模型/Jacobian 联合误差和两状态有限层 fixture 已完成独立审阅。
- [ ] Physics 模块的参数有效性、合成例子和形式边界已完成审阅。
- [ ] 先验白化的因子方向、谱界假设及非对称合成例子已完成独立语义审阅。
- [ ] 奇异先验支持因子的满列秩语义、支持坐标谱界和 ambient/支持可辨识性边界已完成独立语义审阅。
- [ ] canonical support 自动矩形 `SupportFactor` 的满列秩语义、协方差因子方向和支持谱边界
  已完成独立语义审阅。
- [ ] 创建与发布说明一致的 Git tag 和 GitHub Release。
