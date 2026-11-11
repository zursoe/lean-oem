# 先验白化与 OEM 谱诊断

`LeanOEM.Core.PriorWhitening` 将已有的 Hermitian 条件谱界连接到最优增益。
在先验协方差和观测误差协方差正定时，原 averaging kernel 的特征多项式在实数上完全分裂，
所有特征值属于 $[0,1)$，DOFS 等于这些特征值按代数重数求和。半正定先验的支持坐标接口
见 [奇异先验支持白化规格](singular-prior-design.md)。

## 数学规格

沿用库中的矩阵方向：$K$ 为 $m\times n$，$S_a$ 为 $n\times n$，$S_y$ 为 $m\times m$。

$$
S=KS_aK^\mathsf{T}+S_y,\qquad
G=S_aK^\mathsf{T}S^{-1},\qquad A=GK.
$$

`Problem.PriorFactor` 保存一个可逆的 $n\times n$ 矩阵 $L$ 以及恒等式
$S_a=LL^\mathsf{T}$。它兼容满足该恒等式的三角因子和对称平方根。
`PriorFactor.ofPosDef` 使用 Mathlib 的 `CFC.sqrt` 从正定先验构造因子，并证明其可逆性与
因子恒等式，因此高层谱定理只要求原来的两项协方差正定性。

白化坐标中的 averaging kernel 定义为

$$
B=(KL)^\mathsf{T}S^{-1}(KL).
$$

`averagingKernel_mul_factor` 与 `whitenedAveragingKernel_eq_conjugate` 分别证明

$$
AL=LB,\qquad B=L^{-1}AL.
$$

相似变换的方向固定为 $x=Lz$。原矩阵 $A$ 可以不对称，不能直接将其用作
`Matrix.IsHermitian.eigenvalues` 的输入。

## 证明链与公开入口

1. 创新协方差正定，因此 $S^{-1}$ 正定，合同变换给出 $B\succeq0$。
2. 取 Jacobian 为 $KL$、先验为 $I$、观测误差仍为 $S_y$ 的坐标问题。
   它的创新协方差仍为 $S$，后验协方差等于 $I-B$。已有信息形式定理给出 $I-B\succ0$。
3. 对 $B$ 使用 `eigenvalues_bounds_of_posSemidef`，得到每个特征值属于 $[0,1]$；
   `one_sub_whitenedAveragingKernel_posDef` 和 `eigenvalues_lt_one` 进一步给出严格上界。
4. `charpoly_eq` 保证 $A$ 与 $B$ 具有相同特征多项式；`spectrum_eq_range_eigenvalues`
   把原矩阵的实谱识别为白化特征值集合，`charpoly_splits` 保证全部根都是实数。
5. 相似变换保持迹，`dofs_eq_sum_eigenvalues` 给出 DOFS 的谱解释。

若 `Observable p.jacobian` 成立，`whitenedAveragingKernel_posDef_of_observable` 和
`eigenvalues_pos_of_observable` 给出白化矩阵的严格正特征值。任意 Jacobian 下，
`whitenedAveragingKernel_rank_le` 给出白化矩阵秩不超过 Jacobian 秩；这为零特征值和
可辨识性连接保留了明确入口。
在观测误差正定时，`whitenedAveragingKernel_rank_eq` 使用观测协方差平方根恢复等式
`rank B = rank K`；因此白化矩阵的非零特征值数量正好受 Jacobian 秩控制。
`whitenedAveragingKernel_mulVec_eq_zero_iff` 先把 $Bv=0$ 化为 $(KL)v=0$，
`whitenedAveragingKernel_mulVec_eq_zero_iff_jacobian` 再显式写成
$K(Lv)=0$，因此零特征值的证明已经降到 Jacobian 核问题。
`whitenedAveragingKernel_mulVec_injective_iff_observable` 证明白化矩阵的线性映射可辨识性
与原 Jacobian 的 `Observable` 等价；`whitenedAveragingKernel_zero_mem_spectrum_iff_not_observable`
进一步把零谱存在性与 `¬ Observable` 连接起来。
`dofs_le_jacobian_rank` 将特征值求和界收口为
$\mathrm{DOFS}\leq\operatorname{rank}(K)$。
`eigenvalues_lt_one` 和 `dofs_lt_state_dim` 进一步说明非空状态空间且观测误差正定时，
DOFS 严格小于状态维数；它们不需要 Jacobian 满秩。

## 奇异先验的支持坐标

`Problem.SupportFactor` 允许使用满列秩矩形因子 `L : n × r` 表示半正定先验：

$$
S_a=L L^\mathsf{T},\qquad K_s=K L,\qquad
B_s=K_s^\mathsf{T}S^{-1}K_s.
$$

支持坐标使用 `Fin r` 和单位先验。`SupportWhitening` 已证明 `Bₛ` 半正定、`I-Bₛ`
正定、特征值严格小于 `1`、支持内零谱与 `¬ Observable Kₛ` 等价，以及

$$
\operatorname{trace}(A)=\operatorname{trace}(B_s),\qquad
\mathrm{DOFS}\leq r,\qquad
\mathrm{DOFS}\leq\operatorname{rank}(K_s),\qquad
\mathrm{DOFS}\leq\operatorname{rank}(S_a).
$$

这里的 `ObservableOnSupport` 与 ambient `Observable` 有意分开：ambient Jacobian 可以在先验
零方差方向上不单射，而支持 Jacobian 仍然可辨识。当前接口不把 `Bₛ` 与 ambient `A` 的完整
特征多项式宣称为相似，也不定义奇异矩阵的伪逆。

通过 `import LeanOEM.Core` 可以直接使用：

```lean
example {n m : ℕ} (p : LeanOEM.Problem n m)
    (hPrior : p.priorCovariance.PosDef)
    (hObservation : p.observationErrorCovariance.PosDef) :
    spectrum ℝ (LeanOEM.averagingKernel p.gain p.jacobian) ⊆ Set.Icc (0 : ℝ) 1 :=
  p.averagingKernel_spectrum_subset_Icc hPrior hObservation
```

同样的两项假设可用于 `Problem.averagingKernel_charpoly_splits`。需要逐项访问或求和时，
使用 `PriorFactor.ofPosDef hPrior` 得到因子，再调用其 `eigenvalues hObservation`、
`eigenvalues_bounds` 和 `dofs_eq_sum_eigenvalues`。

## 合成例子和边界

`LeanOEM/Tests/PriorWhitening.lean` 使用

$$
L=\begin{pmatrix}1&1\\0&1\end{pmatrix},\quad
S_a=\begin{pmatrix}2&1\\1&1\end{pmatrix},\quad
K=\begin{pmatrix}1&0\end{pmatrix},\quad S_y=1.
$$

Lean 精确验证

$$
A=\begin{pmatrix}2/3&0\\1/3&0\end{pmatrix},\qquad
B=\begin{pmatrix}1/3&1/3\\1/3&1/3\end{pmatrix},\qquad
\sigma(A)=\{0,2/3\},\qquad \mathrm{DOFS}=2/3.
$$

测试显式证明 $A$ 非 Hermitian，并使用正定性入口得到谱界。
另有零 Jacobian 的一般例子和空状态空间例子；谱定理没有满列秩或 $n>0$ 假设。
`scripts/validate_oem_numeric.py` 用 `Fraction` 独立复算该二维例子的因子化、相似变换方向、
两个特征对及 DOFS。这些复算是辅助证据，通用定理由 Lean 内核检查。

当前高层 `PriorFactor` 接口仍要求正定先验；奇异先验使用独立的 `SupportFactor` 接口。
任意半正定矩阵的精确平方根和 `range(sqrt Sₐ)` canonical support 已由
`PriorSqrtFactor.ofPosSemidef` 提供；有限坐标、自动矩形支持因子以及 ambient/support 的非零谱
和零根重数接口已在 `SupportCoordinates` 中完成，见 [奇异先验支持白化规格](singular-prior-design.md)。
矩阵平方根是精确实数构造，本模块没有承诺浮点 Cholesky 或特征值算法的数值稳定性。
