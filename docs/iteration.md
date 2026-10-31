# 非线性 OEM 迭代规格

本模块服务于检查反演程序的迭代编号、Jacobian 刷新方式和停止判据。输入是已有的
`NonlinearProblem`、初值、Jacobian 策略及绝对容差；输出是精确实数轨迹和有条件的误差定理。
它不调用 ARTS，也不实现浮点求解器。

## 轨迹与停止语义

`gaussNewtonIterate` 按以下规则定义：

$$
x_0=x_{\mathrm{init}},\qquad
x_{i+1}=x_i+\Delta_i,\qquad
\Delta_i=H_i^{-1}b_i.
$$

`jacobian : ℕ → State n → Jacobian n m` 决定第 $i$ 步使用的矩阵。
`fun _ x => K x` 表示随状态刷新，`fun _ _ => k` 表示冻结矩阵。
函数参数不自动证明矩阵是真实导数；这仍需 `ForwardModel.HasJacobianAt`。
正规矩阵可逆时，已有单步定理证明 $H_i\Delta_i=b_i$。
本模块另证明零增量与 $b_i=0$ 的等价也需要该可逆条件。

`StepSmall` 要求 $\epsilon\geq0$ 且 $\|\Delta_i\|_\infty\leq\epsilon$。
`StoppedAt ... i` 表示返回当前状态 $x_i$，尚未施加 $\Delta_i$；它不表示首次停止。
`State n = Fin n → ℝ` 使用最大绝对分量范数，不是欧氏范数、先验加权范数或相对步长。
变量尺度由调用者统一。最大迭代次数、首次停止搜索和浮点判定暂不在实现范围。

## 收缩与误差

`ContractsTowardAlong` 是需要另行证明的假设：对给定目标 $x_\star$，每步满足

$$
\|x_{i+1}-x_\star\|_\infty\leq q\|x_i-x_\star\|_\infty.
$$

已证明 $q\geq0$ 时的几何误差界

$$
\|x_i-x_\star\|_\infty\leq q^i\|x_0-x_\star\|_\infty.
$$

在 $0\leq q<1$ 下，轨迹趋于 $x_\star$，任意正容差最终满足停止判据。
停止时有

$$
\|x_i-x_\star\|_\infty\leq\frac{\epsilon}{1-q}.
$$

零容差不保证有限步满足；$q=1$ 不满足收敛和停止误差定理的条件。
`contractsTowardAlong_of_lipschitzOn` 提供局部条件入口：初值和目标属于集合 $D$，
每步更新将 $D$ 映回自身，在 $D$ 上有共同 Lipschitz 常数 $q<1$，且目标是每步更新的
共同不动点。这些条件推出沿轨迹收缩。它们尚未从正演的导数、余项或协方差条件推导。

目标点作为参数给定；本批没有证明目标存在、唯一、是目标函数极小点或等于真实大气状态。
几何误差定理复用锁定 Mathlib 的 `le_geom`，收敛复用幂序列极限和夹逼定理；局部接口复用
`LipschitzOnWith`。停止误差估计由三角不等式得到，与 Mathlib
`Topology/MetricSpace/Contracting.lean` 的不动点距离估计一致。

## 局部缺陷契约

`normalDefect p x target k` 定义正规方程右端与目标位移的差：

$$
d(x)=b(x)-H(x)(x_\star-x).
$$

在正规矩阵可逆时，`gaussNewtonUpdate_sub_target_eq_inverse_normalDefect` 精确给出

$$
x^+-x_\star=H(x)^{-1}d(x).
$$

如果调用者能证明

$$
\|H(x)^{-1}v\|\leq\gamma\|v\|,
\qquad
\|d(x)\|\leq\eta\|x-x_\star\|,
$$

则 `gaussNewtonUpdate_error_le_of_inverse_and_defect` 给出

$$
\|x^+-x_\star\|\leq\gamma\eta\|x-x_\star\|.
$$

这把模型余项、权重和正规矩阵条件留在显式契约中；本模块没有声称具体辐射传输模型
自动满足 $\gamma$、$\eta$ 界。当前批次已经在显式二次余项契约下完成了第一条推导链；
一般 MAP 目标和非零观测残差仍留在后续模块。

## 余项到正规缺陷

`ForwardModel.QuadraticRemainderBound` 显式记录锚点线性化的二次余项界：

$$
\|F(x)-F(x_a)-K(x-x_a)\|
\leq \rho\|x-x_a\|^2.
$$

该契约不把 `HasJacobianAt` 当作二阶误差保证。导数存在只说明一阶线性化成立；
二次界还需要 Lipschitz Jacobian、二阶导数界或调用者提供的独立余项证明。

在观测满足 $y=F(x_\star)$、先验均值满足 $x_a=x_\star$ 时，
`normalDefect_eq_weighted_linearizationRemainder` 证明：

$$
d(x)=K(x)^\mathsf{T}W_y
\bigl(F(x_\star)-F(x)-K(x)(x_\star-x)\bigr).
$$

若加权 Jacobian 的作用界为 $\beta$，余项系数为 $\rho$，且当前点位于
$\|x-x_\star\|\leq r$ 的邻域，则
`normalDefectBound_of_quadraticRemainder` 给出

$$
\|d(x)\|\leq \beta\rho r\|x-x_\star\|.
$$

再结合逆作用界 $\gamma$，单步收缩因子为

$$
q=\gamma\beta\rho r.
$$

`contractsTowardAlong_of_inverse_and_defect` 将每一步的这些显式界直接组合成
`ContractsTowardAlong`，随后可以复用本模块已有的几何收敛和停止误差定理。

## 标量平方模型闭环

测试模块 `LeanOEM/Tests/LocalContraction.lean` 使用
$F(x)=x^2$、目标 $x_\star=0$、单位先验权重和单位观测权重，取邻域
$|x|\leq 1/2$。该模型满足

$$
K(x)=2x,\qquad
r(x)=x^2,\qquad
d(x)=2x^3,\qquad
H(x)=4x^2+1.
$$

在该邻域内可以取 $\beta=1$、$\rho=1$、$r=1/2$ 和 $\gamma=1$，所以
$q=1/2<1$。Lean 已检查邻域不变性、单步误差界和迭代收敛；
这只是精确实数的数学 fixture，不是具体 ARTS 场景或现实观测结论。

## 例子与反例

`LeanOEM/Tests/Iteration.lean` 包含：

- $F(x)=x$、$y=4$、零先验、两个权重均为一：任意初值一步到达 $x=2$；
- $F(x)=x^2$、$y=4$、零先验、两个权重均为一：刷新矩阵得到 $1,2,32/17$，冻结矩阵得到 $1,2,8/5$；
- 同一平方模型在零初值使用真实导数，正规矩阵为一且增量为零，目标函数值为 $8$，而 $x=2$ 时为 $2$。该反例证明零步长和正规矩阵可逆不足以保证最优；
- 负容差不能通过判据；空状态空间仍可定义轨迹；
- $q=1$ 的不增条件允许上述非最优停滞；第零步停止的例子检查误差界对应返回的当前状态。

`scripts/validate_oem_numeric.py` 用 `Fraction` 独立复算上述有限数值案例。
有限案例是工程交叉验证；误差定理由 Lean 内核检查，收缩条件和物理模型适用性仍需另外证明或验证。
