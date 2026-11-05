# 奇异先验支持白化规格

状态：矩形支持因子第一批、自动平方根/range support、canonical 坐标层和自动矩形因子
已实现；ambient 全空间谱关系保留为后续工作。

## 目标和边界

当前 `Problem.PriorFactor` 要求可逆方阵因子，因此只覆盖正定先验。本规格为半正定先验
增加一个独立的矩形支持因子接口，不改变已有 `PriorFactor` 的含义和定理。

先验协方差写成

$$
S_a=L L^{\mathsf T},\qquad L:\mathbb{R}^{r}\to\mathbb{R}^{n},
$$

其中 `L` 满列秩，`Fin r` 是先验支持坐标。状态均值仍属于 ambient 状态空间；支持因子
只描述先验协方差允许变化的方向。

本模块不使用奇异矩阵的总函数逆，也不定义 Moore–Penrose 伪逆。支持坐标中的先验是单位
协方差，所有逆矩阵定理继续只在正定观测误差假设下使用。

## 核心 API

`Problem.PriorSqrtFactor.ofPosSemidef` 对任意半正定先验自动构造精确平方根因子，并定义

```text
support = LinearMap.range (sqrt Sa).mulVecLin
```

该 canonical support 不要求平方根可逆；`support_finrank_eq_priorCovariance_rank` 证明其
有限维维数等于先验协方差的矩阵秩。

`LeanOEM.Core.SupportCoordinates` 进一步定义：

- `euclideanSupport` 是 canonical support 在 `EuclideanSpace` 中的像；
- `euclideanSupportBasis` 使用 `stdOrthonormalBasis` 提供正交规范基；
- `supportBasis` 将该基搬回 `State n` 的支持子空间，`supportBasisMatrix` 将其写成列矩阵；
- `supportBasisMatrix.mulVec` 单射，且
  `LinearMap.range supportBasisMatrix.mulVecLin = support`；
- 坐标索引先固定为 `Fin (Module.finrank ℝ support)`，再由
  `support_finrank_eq_priorCovariance_rank` 识别为 `Fin (rank Sₐ)` 的维数。
- `toSupportFactor` 自动定义矩阵
  `sqrt(Sₐ) · supportBasisMatrix`，并证明其满列秩、协方差恒等式和列空间等于
  canonical support。

由于核心 `State n` 保持函数空间表示，本层不为它添加与既有范数不相容的内积实例；正交
性只在 `euclideanSupport` 中使用，矩阵 API 仍然使用原有的 `State n` 坐标。

`Problem.SupportFactor` 保存：

- `matrix : Matrix (Fin n) (Fin r) ℝ`；
- `injective : Function.Injective matrix.mulVec`；
- `covariance_eq : Sₐ = L Lᴴ`。

由此定义

$$
K_s=K L,qquad
B_s=K_s^{\mathsf T}S^{-1}K_s.
$$

对应的 Lean 对象位于 [SupportWhitening.lean](../LeanOEM/Core/SupportWhitening.lean)。

## 已证明结果

在 `Sᵧ` 正定时，当前接口已经证明：

- `Sₐ` 半正定，支持白化矩阵 `Bₛ` 半正定；
- `I - Bₛ` 正定；
- `Bₛ` 的特征值属于 `[0, 1)`；
- `Bₛ` 正定当且仅当支持 Jacobian `Kₛ` 可辨识；
- `0` 属于 `Bₛ` 的谱当且仅当支持 Jacobian 不可辨识；
- `rank Bₛ = rank Kₛ`；
- `DOFS = trace Bₛ`，且 `DOFS ≤ r`、`DOFS ≤ rank(Kₛ)`、`DOFS ≤ rank(Sₐ)`；
- 支持因子的矩阵秩和先验协方差秩都等于 `r`。
- 任意半正定先验都可以自动得到平方根因子和 canonical support，且 support 维数等于 `rank(Sₐ)`。

`trace A = trace Bₛ` 是本批对 ambient averaging kernel 的连接。它不依赖 `L` 可逆，
但不等同于 `A` 与 `Bₛ` 的完整特征多项式相似关系。

## 合成边界

测试使用

$$
S_a=\begin{pmatrix}1&0\\0&0\end{pmatrix},qquad
L=\begin{pmatrix}1\\0\end{pmatrix}.
$$

当 `K = (1,0)`、`Sᵧ = 1` 时，支持白化矩阵为 `[1/2]`，ambient averaging kernel 为
`diag(1/2, 0)`，`DOFS = 1/2`。此时 ambient Jacobian 不可单射，但支持 Jacobian 可辨识。

当 `K = (0,1)` 时，支持 Jacobian 为零矩阵，支持白化矩阵出现零特征值。该例子把先验
零方差方向与支持子空间内不可观测方向分开。

## 后续工作

下一批研究 ambient averaging kernel 与支持矩阵的非零谱关系。对

$$
A=XY,\qquad B_s=YX,
$$

目标是证明特征多项式的乘幂关系或等价的非零谱结论；奇异情形下不把它升级为完整相似
变换。自动 `SupportFactor` 已经完成协方差和满列秩契约，后续只需在这个接口上处理
ambient/支持之间的非可逆边界。
