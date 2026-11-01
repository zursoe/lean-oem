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

## 两层有限层 fixture

`LeanOEM/Physics/FiniteLayerDiscretization.lean` 把归一化两层递推实例化为一维状态和一维观测。
两层共享状态源项 $x$，透过率和入射辐亮度属于固定模型参数：

$$
F(x)=	au_2	au_1 I_0+
\bigl(\tau_2(1-\tau_1)+(1-\tau_2)\bigr)x.
$$

因此 Jacobian 是常数

$$
K=1-	au_1	au_2.
$$

`twoLayerSource_hasJacobianAt` 在有限维函数空间中证明了这个 Jacobian 的导数契约。
若精确透过率和离散透过率分别满足

$$
|\widehat\tau_1-\tau_1|\leq e_1,
\qquad
|\widehat\tau_2-\tau_2|\leq e_2,
$$

并且两组透过率都位于 $[0,1]$，则

$$
|\widehat\tau_1\widehat\tau_2-	au_1\tau_2|
\leq e_1+e_2.
$$

该乘积界给出整体 Jacobian 系数误差，并通过
`twoLayerSource_weightedJacobianErrorBound_of_unitWeight` 接入已有的
`WeightedJacobianErrorBound`。在 $|I_0|\leq B_I$、$|x|\leq B_x$ 时，正演误差满足

$$
\|F_h(x)-F(x)\|
\leq (e_1+e_2)(B_I+B_x).
$$

测试 fixture 取

$$
(\tau_1,\tau_2,I_0)=\left(\frac12,\frac34,2\right),
\qquad
(\widehat\tau_1,\widehat\tau_2,I_0)=\left(\frac35,\frac7{10},2\right).
$$

精确和近似 Jacobian 系数分别为 $5/8$ 和 $29/50$，透过率误差预算为
$e_1+e_2=3/20$。在 $x=1/2$ 时，正演误差为 $27/400$；目标残差取 $1/10$ 时，
正规方程残差为 $9/2000$，并由 OEM 误差定理传到更新误差底。

这些结论是显式范围假设下的精确实数定理。它们没有引入连续频率积分、单位转换、浮点舍入、
谱线数据库或 ARTS 代码依赖。

## 有限通道响应 fixture

`LeanOEM/Physics/ChannelDiscretization.lean` 将两个有限通道响应之间的权重差定义为

$$
E_w=\sum_i|\widehat w_i-w_i|.
$$

若有限频率样本满足 $|v_i|\leq B$，则

$$
|C_{\widehat w}(v)-C_w(v)|\leq B E_w.
$$

若谱值本身也有逐点误差 $|\widehat v_i-v_i|\leq E_v$，则组合界为

$$
|C_{\widehat w}(\widehat v)-C_w(v)|
\leq B E_w+E_v.
$$

`channelJacobian` 对有限频率灵敏度执行同样的加权求和，因此该组合界可以直接转为
一行 Jacobian 的系数误差，并通过 `channelJacobian_weightedErrorBound_of_unitWeight`
接入 `WeightedJacobianErrorBound`。

测试使用两频率响应

$$
w=\left(\frac34,\frac14\right),
\qquad
\widehat w=\left(\frac7{10},\frac3{10}\right),
$$

并把两层有限层输出分别取为

$$
v=\left(\frac{17}{16},\frac{49}{50}\right),
\qquad
\widehat v=\left(\frac{113}{100},\frac{41}{40}\right).
$$

此时 $E_w=1/10$，输出误差为 $453/8000$，在 $B=6/5$、$E_v=7/100$ 下满足
$B E_w+E_v=19/100$。对应的通道 Jacobian 系数误差为 $151/4000$，测试使用
$3/10$ 的组合预算接入 OEM 契约。

该结果只证明有限样本和显式误差预算下的加权和界。它没有证明连续频率积分、具体求积
规则的 $h^p$ 阶数，也没有引入单位、谱线数据库或 ARTS 输出。
