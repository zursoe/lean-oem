# 奇异先验支持白化规格

状态：矩形支持因子、自动平方根/range support、canonical 坐标层、自动矩形因子和
ambient/support 非零实谱接口均已实现；完整相似变换仍不属于本规格。

## 目标和边界

当前 `Problem.PriorFactor` 要求可逆方阵因子，因此只覆盖正定先验。本规格为半正定先验
增加一个独立的矩形支持因子接口，不改变已有 `PriorFactor` 的含义和定理。

先验协方差写成

$$
S_a=L L^{\mathsf T},\qquad L:\mathbb{R}^{r}\to\mathbb{R}^{n},
$$

其中 `L` 满列秩，`Fin r` 是先验支持坐标。状态均值仍属于 ambient 状态空间；支持因子
只描述先验协方差允许变化的方向。

本模块不使用奇异先验协方差的总函数逆，也不定义 Moore–Penrose 伪逆。支持坐标中的先验
是单位协方差。创新协方差的总函数逆也出现在无条件代数恒等式中；只有给出正定观测误差
等可逆性依据时，才将它解释为通常逆。

## 核心 API

`Problem.PriorSqrtFactor.ofPosSemidef` 对任意半正定先验自动构造精确平方根因子，并定义

```text
support = LinearMap.range (sqrt Sa).mulVecLin
```

该 canonical support 不要求平方根可逆；`support_finrank_eq_priorCovariance_rank` 证明其
有限维维数等于先验协方差的矩阵秩。
当前没有单独形式化它与 `range(Sₐ)` 的子空间集合等式；此处的 support 按上述平方根像空间定义。

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
- `averagingKernel_charpoly_eq_support_factor` 对任意支持因子证明
  `χ_A = X^(n-r) χ_{Bₛ}`，用特征多项式乘幂表达 ambient 与支持矩阵的谱关系。
- `averagingKernel_nonzeroSpectrum_eq_support_factor` 将上述关系整理为 ambient 与支持
  白化矩阵的非零实谱集合相等；本接口不记录重数，也未单独形式化复谱版本。
- `averagingKernel_zero_rootMultiplicity_eq` 记录零根代数重数的加法关系；支持坐标可辨识
  时，`averagingKernel_zero_rootMultiplicity_eq_dim_sub_support_of_observableOnSupport`
  给出精确的 `n-r` 零方向重数。

由于核心 `State n` 保持函数空间表示，本层不为它添加与既有范数不相容的内积实例；正交
性只在 `euclideanSupport` 中使用，矩阵 API 仍然使用原有的 `State n` 坐标。

`Problem.SupportFactor` 保存：

- `matrix : Matrix (Fin n) (Fin r) ℝ`；
- `injective : Function.Injective matrix.mulVec`；
- `covariance_eq : Sₐ = L Lᴴ`。

由此定义

$$
K_s=K L,\qquad S=K S_a K^{\mathsf T}+S_y,\qquad
B_s=K_s^{\mathsf T}S^{-1}K_s.
$$

对应的 Lean 对象位于 [SupportWhitening.lean](../LeanOEM/Core/SupportWhitening.lean)。

## 已证明结果

在 `Sᵧ` 正定时，当前接口已经证明：

- `Sₐ` 半正定，支持白化矩阵 `Bₛ` 半正定；
- `I - Bₛ` 正定；
- `Bₛ` 的特征值属于 `[0, 1)`；
- 支持 Jacobian `Kₛ` 可辨识时 `Bₛ` 正定；反向可由下一项零谱等价及正定矩阵可逆推出，
  目前没有单独命名的双向定理；
- `0` 属于 `Bₛ` 的谱当且仅当支持 Jacobian 不可辨识；
- `rank Bₛ = rank Kₛ`；
- `DOFS = trace Bₛ`，且 `DOFS ≤ r`、`DOFS ≤ rank(Kₛ)`、`DOFS ≤ rank(Sₐ)`；
- 支持因子的矩阵秩和先验协方差秩都等于 `r`。
- 任意半正定先验都可以自动得到平方根因子和 canonical support，且 support 维数等于 `rank(Sₐ)`。
- ambient/support 的非零实谱集合相等；零根重数由 ambient 维数差和支持矩阵自身的零根重数共同决定。

`trace A = trace Bₛ` 是本批对 ambient averaging kernel 的连接。它不依赖 `L` 可逆，
但不等同于 `A` 与 `Bₛ` 的完整特征多项式相似关系。

## 合成边界

测试使用

$$
S_a=\begin{pmatrix}1&0\\0&0\end{pmatrix},\qquad
L=\begin{pmatrix}1\\0\end{pmatrix}.
$$

当 `K = (1,0)`、`Sᵧ = 1` 时，支持白化矩阵为 `[1/2]`，ambient averaging kernel 为
`diag(1/2, 0)`，`DOFS = 1/2`。此时 ambient Jacobian 不可单射，但支持 Jacobian 可辨识。

当 `K = (0,1)` 时，支持 Jacobian 为零矩阵，支持白化矩阵出现零特征值。该例子把先验
零方差方向与支持子空间内不可观测方向分开。

## 后续工作

本规格的数学接口已完成下一阶段目标。后续工作转入 Core/Physics 入口审查、发布材料
同步和干净环境复现；奇异情形下仍不把非零谱关系升级为完整相似变换。自动 `SupportFactor`
继续同时保留显式构造和 canonical 自动构造两种接口。
