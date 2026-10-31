# Jacobian 离散化误差规格

本模块连接中心有限差分等数值 Jacobian 构造与非线性 OEM 的误差契约。
所有结果都在精确实数和显式范数界下成立，不把浮点运行或 ARTS 输出自动解释为形式定理。

## Jacobian 误差

`WeightedJacobianErrorBound p approx exact epsilon` 定义：

$$
\left\|K_h^\mathsf{T}W_yv-K^\mathsf{T}W_yv\right\|
\leq \epsilon\|v\|.
$$

`weightedJacobianActionBound_of_error` 说明，如果理想 Jacobian 的加权作用界为 $\beta$，
离散化误差为 $\epsilon$，则近似 Jacobian 可以使用作用常数

$$
\beta_h=\beta+\epsilon.
$$

该结论只需要三角不等式；`epsilon` 的具体来源可以是中心有限差分、插值、求积或其他
外部数值分析证明。

## 目标驻点误差

若理想目标 Jacobian 满足非线性 MAP 驻点，而近似目标 Jacobian 只满足上面的误差界，
且目标残差满足 $\|r(x_\star)\|\leq\sigma$，则
`normalRhs_norm_le_of_weightedJacobianError` 给出

$$
\|b_h(x_\star)\|\leq\epsilon\sigma.
$$

`normalDefect_additive_bound_of_stationarity_residual` 将该项和线性化余项合并：

$$
\|d_h(x)\|
\leq \eta\|x-x_\star\|+\tau,
$$

其中 $\tau$ 可以取目标正规方程残差的上界。再结合正规矩阵逆作用界 $\gamma$，
`gaussNewtonUpdate_error_le_of_inverse_and_additive_defect` 给出

$$
\|x_h^+-x_\star\|
\leq \gamma\eta\|x-x_\star\|+\gamma\tau.
$$

因此 Jacobian 离散化误差在存在目标残差时会形成误差底；它不会被无条件地吸收到原来的
几何收缩因子中。

## 中心有限差分 fixture

`LeanOEM/Tests/DiscretizationError.lean` 使用 $f(x)=x^3$、$x=1$ 和 $h=1/10$。
已有 `centralDifference_error_bound` 给出

$$
\left|D_hf(1)-f'(1)\right|\leq h^2.
$$

测试进一步使用精确 Jacobian $3$、近似 Jacobian $301/100$，验证加权 Jacobian 误差为
$1/100$；目标残差取 $1/10$ 时，目标正规方程残差界为 $1/1000$。

这些数字是可复现的有理数 fixture，不是浮点误差统计，也不代表真实 ARTS 配置。
