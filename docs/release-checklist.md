# 0.1.0 候选版本发布检查清单

当前状态：尚未发布。候选版本定位为纯 Lean 数学库：`LeanOEM.Core` 是稳定入口，
`LeanOEM.Physics` 随包提供但保持实验性；以下清单针对当前完整主线执行。

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
- [x] ambient averaging kernel 与支持白化矩阵的特征多项式乘幂关系已形式化。
- [x] ambient/support 非零谱集合相等和零根代数重数关系已形式化并纳入测试与公理审计。
- [x] 版本说明区分数学实现基线 `52e36b1` 和本轮起点 `9bb9f25`；实际受检提交在构建记录中登记。
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
- [x] 历史非零谱批次已在干净 detached worktree 中构建通过（3429 个目标，结论登记于 `9bb9f25`）。
- [x] 本轮候选 `ff3ca1d` 从固定提交建立干净 worktree，完成 3423 个构建目标和完整审计；
  依赖 Git 对象与下载缓存的使用方式见 [构建记录](audit/build-report.md)。
- [x] 默认测试构建涵盖 Physics 聚合入口；审计失败时显示原始 Lean 错误并保留退出码。

## 可信性和公理

- [x] 源代码没有 `sorry`、`admit` 或未登记自定义 `axiom`。
- [x] 全部 192 个显式公开定理及 3 个因子构造执行 `#print axioms`，195 项输出完整。
- [x] 核心定理只依赖 `propext`、`Classical.choice` 和 `Quot.sound`。
- [x] 形式假设、形式定理、独立验证证据和数学来源已分开记录。

## 历史审查与本轮内部复核

- [x] 检查矩阵方向和转置约定。
- [x] 检查 `observationErrorCovariance` 的语义。
- [x] 检查总函数矩阵逆的使用条件。
- [x] 检查后验、Joseph 和信息形式的适用假设。
- [x] 检查数值脚本没有成为 Lean 证明的隐含依据。
- [x] 历史线性核心在远端 GitHub runner 完成 push、PR 和合并后的 CI；当前候选不沿用该结论。
- [x] 历史线性核心实现已完成审阅并合并到远端 `main`。
- [x] 已完成本轮发布候选内部语义审阅，覆盖前向/Jacobian 误差、Physics 边界、先验白化和
  canonical support；记录见 [发布候选审阅](review/release-candidate-review.md)。

## 发布前仍需完成

- [ ] 前向模型/Jacobian 联合误差和两状态有限层 fixture 的独立人工语义复核。
- [ ] Physics 参数有效性、合成例子和归一化边界的独立人工语义复核。
- [ ] 正定先验白化方向、谱界假设及非对称例子的独立人工语义复核。
- [ ] 奇异先验支持因子、canonical 自动因子及 ambient/support 谱边界的独立人工语义复核。
- [ ] 发布决策后同步当前候选至远端并检查该提交的 GitHub CI。
- [ ] 创建与发布说明一致的 Git tag 和 GitHub Release。
