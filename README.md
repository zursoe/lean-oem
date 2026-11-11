# lean-oem

`lean-oem` 是一个使用 Lean 4 和 Mathlib 形式化最优估计、线性逆问题、协方差、Jacobian、averaging kernel、DOFS 和可观测性的库。

当前主线从有限维、实数、矩阵表示的线性模型开始。状态向量使用 `Fin n → ℝ`，观测向量使用 `Fin m → ℝ`，Jacobian 的形状是 `m × n`。核心 API 将原始矩阵数据与正定性等形式假设分开保存。

`0.1.0` 的固定版本引用为 `v0.1.0`，功能与适用条件见 [版本说明](docs/release-notes.md)，
发布结果见 [GitHub Release](https://github.com/zursoe/lean-oem/releases/tag/v0.1.0)。

## 构建

本项目锁定 Lean `v4.35.0` 和 Mathlib 输入版本 `v4.35.0`。在取得仓库后执行：

```bash
lake build
scripts/run_audit.sh
python3 scripts/validate_oem_numeric.py
```

Mathlib 的版本和提交由 `lean-toolchain`、`lakefile.toml` 与 `lake-manifest.json` 共同固定。`.lake` 目录是本机缓存和编译产物，不属于源代码发布内容。
其中 `scripts/validate_oem_numeric.py` 只是独立精确算术审计工具，不是库的运行依赖或主线目标。

## 当前范围

当前模块包含：

- `LeanOEM.Core` 稳定核心入口，以及 `LeanOEM.Physics` 实验性物理模型入口；
- 线性观测问题、预测和创新；
- 创新协方差与最优增益；
- 任意增益的线性估计器和确定性误差分解；
- 良定性假设、创新协方差的逆矩阵性质和增益规格；
- 标准后验协方差、Joseph 协方差及其半正定性。
- 精确的一维和秩亏二维测试例子，以及非法协方差边界测试。
- averaging kernel 的 DOFS trace 定义、显式矩阵序条件下的上下界和逐特征值界，以及正定先验/观测误差下
  最优增益的 `0 ≤ DOFS ≤ n` 定理和静态可辨识性接口。
- 正定先验的平方根因子、白化相似变换、原 averaging kernel 的实谱 `[0,1)` 界及 DOFS 特征值求和公式，见 [谱诊断规格](docs/spectral-diagnostics.md)。
- 奇异半正定先验的矩形支持因子、支持坐标白化、严格谱界、零谱和秩/DOFS 界，见
  [奇异先验支持白化规格](docs/singular-prior-design.md)。
- 任意半正定先验的精确平方根因子和 canonical `range` support。
- canonical support 的 EuclideanSpace 正交规范基、有限坐标列矩阵，以及列矩阵满列秩和
  像空间契约。
- `PriorSqrtFactor.toSupportFactor` 自动构造平方根支持因子，并证明协方差 Gram 恒等式和
  满列秩与列空间等于 canonical support。
- 支持因子下 ambient 与支持 averaging kernel 的特征多项式乘幂关系。
- 支持因子下 ambient 与支持 averaging kernel 的非零实谱集合接口，以及零根代数重数关系。
- 信息矩阵、Woodbury 后验公式和后验逆矩阵恒等式。
- 通用 `ForwardModel`、Jacobian 导数规格、锚点线性化余项和 `Problem.predict` 连接。
- 最小有限层无散射辐射传输递推，以及非负性、上界保持和两层组合性质。
- 两层共同源项有限层正演、显式 Jacobian，以及透过率离散误差到 OEM 更新误差底的传播。
- 两通道、两状态有限层正演模型及其显式 Jacobian 导数契约。
- 有限通道响应权重和谱值误差界，以及通道 Jacobian 到 OEM 误差契约的连接。
- 归一化 Planck 函数、带正线宽参数包的 Gaussian 谱线、Doppler 频移和非负归一化通道响应的基本性质。
- 矩阵加权二次目标、Gauss–Newton 代数正规方程规格，以及协方差总函数逆的权重映射。
- Gauss–Newton 迭代轨迹、步长停止判据，以及显式收缩条件下的收敛、停止误差界和统一加性误差底界。
- 正定权重下的正规矩阵性质，以及可逆正规矩阵下更新点的代数正规残差归零。
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

正规方程的梯度解释要求对称权重；把 `TargetStationary` 解释为原目标驻点还要求真实
Jacobian。`Problem.toNonlinear` 本身只是总函数逆权重映射，奇异先验下不保证与原估计器
等价。条件与回归反例见 [语义复核收口记录](docs/review/independent-ai-review.md)。

外部边界：本库不依赖 ARTS、Python 工程、真实数据或 SCI 论文项目；这些内容可以在库外作为应用背景或独立验证来源，但不属于主库目标、依赖、稳定 API 或发布门槛。

形式定理只说明给定定义和显式假设下的数学性质。当前状态、范围、外部边界、来源映射和后续路线见 [`docs/status.md`](docs/status.md)、[`docs/scope.md`](docs/scope.md)、[`docs/source-mapping.md`](docs/source-mapping.md) 与 [`docs/roadmap.md`](docs/roadmap.md)。
本库使用 Lean/Mathlib 的经典逻辑；审计允许 `propext`、`Classical.choice` 和 `Quot.sound`，记录见 [公理审计](docs/audit/axioms.md)。

## 后续维护

`LeanOEM.Core` 提供通用数学 API，`LeanOEM.Physics` 保存仍在演化的归一化模型、定理和合成例子。当前维护重点是稳定 API 审查、假设边界、反例、文档和可复现构建；新的数学模块只有在明确的纯 Lean 问题形成后再加入。迭代语义和证明边界见 [`docs/iteration.md`](docs/iteration.md)。

## 许可证

本项目使用 Apache License 2.0，见 [`LICENSE`](LICENSE)。
