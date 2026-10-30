# lean-oem

`lean-oem` 是一个使用 Lean 4 和 Mathlib 形式化最优估计、线性逆问题、协方差、Jacobian、averaging kernel、DOFS 和可观测性的库。

当前主线从有限维、实数、矩阵表示的线性模型开始。状态向量使用 `Fin n → ℝ`，观测向量使用 `Fin m → ℝ`，Jacobian 的形状是 `m × n`。核心 API 将原始矩阵数据与正定性等形式假设分开保存。

## 构建

本项目锁定 Lean `v4.35.0` 和 Mathlib 输入版本 `v4.35.0`。在取得仓库后执行：

```bash
lake build
scripts/run_audit.sh
python3 scripts/validate_oem_numeric.py
```

Mathlib 的版本和提交由 `lean-toolchain`、`lakefile.toml` 与 `lake-manifest.json` 共同固定。`.lake` 目录是本机缓存和编译产物，不属于源代码发布内容。

## 当前范围

当前模块包含：

- 线性观测问题、预测和创新；
- 创新协方差与最优增益；
- 任意增益的线性估计器和确定性误差分解；
- 良定性假设、创新协方差的逆矩阵性质和增益规格；
- 标准后验协方差、Joseph 协方差及其半正定性。
- 精确的一维和秩亏二维测试例子，以及非法协方差边界测试。
- averaging kernel 的 DOFS trace 定义和静态可辨识性接口。
- 信息矩阵、Woodbury 后验公式和后验逆矩阵恒等式。

形式定理只说明给定定义和显式假设下的数学性质。它们不自动证明某个 ARTS 配置、观测数据、数据库参数或有限精度程序符合这些假设。范围、信任边界、来源映射和后续路线见 [`docs/scope.md`](docs/scope.md)、[`docs/source-mapping.md`](docs/source-mapping.md) 与 [`docs/roadmap.md`](docs/roadmap.md)。

## 许可证

本项目使用 Apache License 2.0，见 [`LICENSE`](LICENSE)。
