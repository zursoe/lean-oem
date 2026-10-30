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

## 例子与反例

`LeanOEM/Tests/Iteration.lean` 包含：

- $F(x)=x$、$y=4$、零先验、两个权重均为一：任意初值一步到达 $x=2$；
- $F(x)=x^2$、$y=4$、零先验、两个权重均为一：刷新矩阵得到 $1,2,32/17$，冻结矩阵得到 $1,2,8/5$；
- 同一平方模型在零初值使用真实导数，正规矩阵为一且增量为零，目标函数值为 $8$，而 $x=2$ 时为 $2$。该反例证明零步长和正规矩阵可逆不足以保证最优；
- 负容差不能通过判据；空状态空间仍可定义轨迹；
- $q=1$ 的不增条件允许上述非最优停滞；第零步停止的例子检查误差界对应返回的当前状态。

`scripts/validate_oem_numeric.py` 用 `Fraction` 独立复算上述有限数值案例。
有限案例是工程交叉验证；误差定理由 Lean 内核检查，收缩条件和物理模型适用性仍需另外证明或验证。
