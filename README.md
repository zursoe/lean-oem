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

- `LeanOEM.Core` 稳定核心入口，以及 `LeanOEM.Physics` 实验性物理模型入口；
- 线性观测问题、预测和创新；
- 创新协方差与最优增益；
- 任意增益的线性估计器和确定性误差分解；
- 良定性假设、创新协方差的逆矩阵性质和增益规格；
- 标准后验协方差、Joseph 协方差及其半正定性。
- 精确的一维和秩亏二维测试例子，以及非法协方差边界测试。
- averaging kernel 的 DOFS trace 定义、显式矩阵序条件下的上下界，以及正定先验/观测误差下
  最优增益的 `0 ≤ DOFS ≤ n` 定理和静态可辨识性接口。
- 信息矩阵、Woodbury 后验公式和后验逆矩阵恒等式。
- 通用 `ForwardModel`、Jacobian 导数规格、锚点线性化余项和 `Problem.predict` 连接。
- 最小有限层无散射辐射传输递推，以及非负性、上界保持和两层组合性质。
- 两层共同源项有限层正演、显式 Jacobian，以及透过率离散误差到 OEM 更新误差底的传播。
- 两通道、两状态有限层正演模型及其显式 Jacobian 导数契约。
- 有限通道响应权重和谱值误差界，以及通道 Jacobian 到 OEM 误差契约的连接。
- 归一化 Planck 函数、带正线宽参数包的 Gaussian 谱线、Doppler 频移和非负归一化通道响应的基本性质。
- 非线性 MAP 目标、Gauss–Newton 正规方程规格，以及与线性 OEM 信息形式的连接。
- Gauss–Newton 迭代轨迹、步长停止判据，以及显式收缩条件下的收敛和停止误差界。
- 正定权重下的正规矩阵性质，以及线性化正规梯度的一阶驻点规格。
- 可替换正演模型的 `residualFor`、`normalRhsFor` 和 `withModel`，以及前向模型/Jacobian
  联合误差到正规方程和一步更新误差的契约。

稳定核心可以独立导入：

```lean
import LeanOEM.Core
```

需要实验性 Physics 模型时再显式导入：

```lean
import LeanOEM.Physics
```

兼容入口 `import LeanOEM` 只导出稳定核心。

形式定理只说明给定定义和显式假设下的数学性质。当前状态、范围、外部边界、来源映射和后续路线见 [`docs/status.md`](docs/status.md)、[`docs/scope.md`](docs/scope.md)、[`docs/source-mapping.md`](docs/source-mapping.md) 与 [`docs/roadmap.md`](docs/roadmap.md)。

## 后续方向

`LeanOEM.Core` 提供通用数学 API，`LeanOEM.Physics` 保存仍在演化的归一化模型、定理和合成例子。后续重点是完善数学接口、假设边界、反例、文档和可复现构建。迭代语义和证明边界见 [`docs/iteration.md`](docs/iteration.md)。

## 许可证

本项目使用 Apache License 2.0，见 [`LICENSE`](LICENSE)。
