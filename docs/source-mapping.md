# Lean OEM 定义、定理和外部证据映射

本文档把 Lean 中的形式对象、形式假设、形式定理、独立数值验证和外部科研来源分开记录。外部来源用于说明术语、公式和应用背景，不作为 Lean 内核的证明输入。

## 公式来源

本项目采用的线性 OEM 记号和 averaging kernel、后验协方差、信息形式、DOFS 术语与 Rodgers 的大气反演教材一致：

- Clive D. Rodgers, *Inverse Methods for Atmospheric Sounding: Theory and Practice*, World Scientific, 2000；
- DOI：[`10.1142/3171`](https://doi.org/10.1142/3171)；
- Crossref 元数据现场核对日期：2026-10-30。

该书是术语和模型来源。它没有被导入 Lean，也没有把书中的现实假设自动转化为形式定理。

## 定义映射

- `LeanOEM.Problem.jacobian`：线性观测 Jacobian $K$，形状为观测维度乘状态维度；见 `LeanOEM/Core/LinearModel.lean`。
- `priorMean`：先验状态 $x_a$。
- `priorCovariance`：先验协方差 $S_a$。
- `observationErrorCovariance`：观测误差协方差 $S_\varepsilon$。
- `Problem.predict`：线性预测 $Kx$。
- `Problem.innovation`：观测减预测 $y-Kx$。
- `Problem.innovationCovariance`：

  $$
  S=K S_a K^\mathsf{T}+S_\varepsilon.
  $$

- `Problem.gain`：

  $$
  G=S_aK^\mathsf{T}S^{-1}.
  $$

- `estimateWithGain`：

  $$
  \hat{x}=x_a+G(y-Kx_a).
  $$

- `averagingKernel`：$A=GK$。
- `dofs`：$\operatorname{trace}(A)$。
- `posteriorCovariance`：

  $$
  S_{post}=S_a-S_aK^\mathsf{T}S^{-1}KS_a.
  $$

- `josephCovariance`：

  $$
  (I-GK)S_a(I-GK)^\mathsf{T}+G S_\varepsilon G^\mathsf{T}.
  $$

- `informationMatrix`：

  $$
  \Lambda=S_a^{-1}+K^\mathsf{T}S_\varepsilon^{-1}K.
  $$

- `Observable k`：`k.mulVec` 为单射，表示给定线性模型下的静态可辨识性。

## 形式假设和定理映射

- `Problem.WellPosed` 记录先验半正定和观测误差正定；它不声称现实数据自动满足这些条件。
- `innovationCovariance_posDef`：在先验半正定、观测误差正定时，创新协方差正定。
- `innovationCovariance_inv_mul` 与 `innovationCovariance_mul_inv`：在正定假设下，矩阵总函数逆满足两侧消去。
- `retrievalError_decomposition`：

  $$
  \hat{x}-x=(I-A)(x_a-x)+G\varepsilon.
  $$

- `josephCovariance_posSemidef`：Joseph 形式在两个输入协方差半正定时半正定。
- `posteriorCovariance_eq_josephCovariance`：标准后验公式与最优增益的 Joseph 形式等价。
- `posteriorCovariance_posSemidef`：良定性假设下后验协方差半正定。
- `prior_minus_posterior_posSemidef`：先验减后验为半正定合同变换。
- `informationMatrix_posDef`：先验正定时信息矩阵正定。
- `posteriorCovariance_eq_informationMatrix_inv`：由 Mathlib Woodbury 恒等式得到

  $$
  S_{post}=\Lambda^{-1}.
  $$

- `posteriorCovariance_inv_eq_informationMatrix`：

  $$
  S_{post}^{-1}=\Lambda.
  $$

- `weightedNormalMatrix_posDef`：正定观测权重和可辨识 Jacobian 给出正定 $K^\mathsf{T}SK$。

### 非线性观测模型第一批映射

- `ForwardModel.observe`：ARTS 无关的状态到观测函数 $F$，见 `LeanOEM/Core/ForwardModel.lean`；
- `ForwardModel.linearizedObserve`：锚点线性化模型 $F(x_a)+K(x-x_a)$；
- `ForwardModel.linearizationRemainder`：精确余项 $F(x)-F(x_a)-K(x-x_a)$；
- `ForwardModel.linearizedOffset`：将锚点模型改写为偏置加 `Problem.predict` 的偏置项；
- `ForwardModel.HasJacobianAt`：连续 Fréchet 导数由 `K : m × n` 表示的规格；
- `ForwardModel.JacobianSpec`：把连续线性导数和矩阵表示一起保存的结构；
- `ForwardModel.matrixDerivative`：有限函数基下的矩阵到连续线性映射转换。

第一批只证明代数恒等式和导数表示契约。它没有引入辐射传输方程、单位、ARTS 数据或浮点
误差界；标量平方模型位于 `LeanOEM/Tests/ForwardModel.lean`，用于检查非线性导数和二阶余项。

### 有限层辐射传输第一批映射

- `RadiativeTransfer.Layer.transmissivity`：归一化层透过率 $\tau$；
- `RadiativeTransfer.Layer.source`：归一化层源项 $S$；
- `RadiativeTransfer.Layer.propagate`：单层递推

  $$
  I_{out}=\tau I_{in}+(1-\tau)S;
  $$

- `RadiativeTransfer.Layer.Valid`：$0\leq\tau\leq1$ 且 $S\geq0$ 的形式假设；
- `RadiativeTransfer.propagateLayers`：有限层列表的顺序传播；
- `RadiativeTransfer.propagateLayers_nonneg` 和 `propagateLayers_bounds`：传播过程的非负性和上界保持；
- `RadiativeTransfer.propagateTwo_eq`：两层递推的显式组合公式。

这些定理只负责归一化有限层模型的数学性质，不负责谱线参数、Planck 函数、单位转换、ARTS
数值误差或真实大气有效性。测试例子位于 `LeanOEM/Tests/FiniteLayer.lean`。

### 频谱和通道响应第一批映射

- `planckRadiance`：带显式常数和正参数假设的归一化 Planck 函数；
- `planckRadiance_pos`：正频率、正温度和正物理常数下辐亮度为正；
- `dopplerShift`：一阶无量纲 Doppler 频移；
- `dopplerShift_zero`、`dopplerShift_expand`、`dopplerShift_pos`：零速度、代数展开和正性结论；
- `ChannelResponse`：非负且归一化的有限通道权重；
- `ChannelResponse.apply`：通道加权求和；
- `ChannelResponse.apply_nonneg`、`apply_le_of_le`、`apply_const`：非负性、上界保持和常量保持。

这些结果见 `LeanOEM/Physics/Spectral.lean`。它们没有引入单位、真实谱线参数、ARTS 采样或
浮点误差界；测试例子位于 `LeanOEM/Tests/Spectral.lean`。

## 独立数值证据

`scripts/validate_oem_numeric.py` 使用 Python 标准库 `fractions.Fraction` 独立实现小型矩阵运算，避免依赖 Lean、Mathlib、NumPy 或 SciPy。它核对：

- 一维例子 $K=2$、$S_a=3$、$S_\varepsilon=5$；
- 创新协方差 $17$、增益 $6/17$、averaging kernel $12/17$、后验协方差 $15/17$；
- Joseph 形式、信息矩阵 $17/15$、后验逆矩阵和确定性误差分解；
- `2 × 1` 秩亏观测、不可观测状态方向和未收缩后验分量。
- 线性问题一步到达正则化解、非线性刷新/冻结 Jacobian 轨迹，以及零步长但目标值非最优的反例。

运行命令：

```bash
python3 scripts/validate_oem_numeric.py
```

这些结果是独立实现的精确有理数交叉验证，不能替代 Lean 证明，也不能证明 ARTS、观测数据库或有限精度程序满足模型假设。

## 计划中的正演和算法映射

P9 的第一批已经完成：后续形式化仍不把 ARTS 代码直接导入 Lean，而是继续建立独立的数学规格：

- `ForwardModel`：状态到观测的函数 $F : X \to Y$；
- `JacobianSpec`：$K(x)$ 作为 $F$ 的导数矩阵、导数的近似，或带明确误差界的数值构造；
- `linearizationRemainder`：

  $$
  F(x)=F(x_a)+K(x_a)(x-x_a)+r(x);
  $$

- `F_h`、`K_h`：有限层、有限差分、频率求积或通道离散化产生的数值近似；
- `GaussNewtonStep`：在非线性观测模型下使用 $F$、$K$、先验和观测误差的单步更新。

这些对象的形式定理可以证明维度、导数关系、递推性质、线性化余项条件和局部误差结论。ARTS/Python fixture 则记录具体版本、配置、谱线库、单位、数组哈希和数值误差，用来支持“具体 ARTS 输出符合某个形式规格”的工程判断。该判断不会被写成无条件的 Lean 定理。

### 非线性 OEM 第一批映射

- `NonlinearProblem`：观测、先验均值、先验权重和观测权重的非线性 MAP 规格；
- `NonlinearProblem.residual`：$y-F(x)$；
- `NonlinearProblem.objective`：带观测权重和先验权重的二次目标；
- `NonlinearProblem.normalMatrix`：$K^\mathsf{T}W_yK+W_a$；
- `NonlinearProblem.normalRhs`：$K^\mathsf{T}W_y(y-F(x))-W_a(x-x_a)$；
- `NonlinearProblem.gaussNewtonStep`：正规矩阵总函数逆定义的状态增量；
- `normalMatrix_mulVec_gaussNewtonStep`：在正规矩阵可逆条件下，增量满足正规方程；
- `Problem.toNonlinear`：线性 `Problem` 到非线性规格的权重形式映射；
- `Problem.toNonlinear_normalMatrix_eq_informationMatrix`：该映射的正规矩阵退化为信息矩阵；
- `WeightWellPosed`：先验权重和观测权重的正定性假设；
- `normalMatrix_posDef` / `normalMatrix_isUnit`：正定权重与可观测 Jacobian 给出的正规矩阵条件；
- `linearizedGradient`：线性化子问题的正规梯度表达式；
- `quadraticGradient` / `quadraticForm_add`：实数二次型的一阶系数与显式二阶余项展开；
- `quadraticSubproblem` / `quadraticSubproblem_add`：对称正规矩阵线性化子问题的增量展开；
- `gaussNewtonUpdate_linearizedGradient_eq_zero`：可逆正规矩阵下更新点满足该正规梯度为零。
- `residual_hasFDerivAt_of_hasJacobianAt`：`HasJacobianAt` 沿残差映射传播，残差导数为负 Jacobian。

当前批次只证明代数规格和可逆性条件，不证明非线性迭代的全局收敛、阻尼策略或现实正演有效性。

### 迭代与停止映射

`LeanOEM/Core/Iteration.lean` 增加精确实数轨迹、步长判据和条件定理，完整语义见
[迭代规格](iteration.md)。`gaussNewtonIterate` 的矩阵策略可以依赖步数和状态；`StepSmall`
和 `StoppedAt` 对当前状态的下一步增量使用最大绝对分量范数。

`ContractsTowardAlong` 是外加的误差收缩条件。`gaussNewtonIterate_error_le` 复用锁定 Mathlib
`Analysis/SpecificLimits/Basic.lean` 的 `le_geom`，`gaussNewtonIterate_tendsto` 复用几何序列
极限与夹逼定理。`contractsTowardAlong_of_lipschitzOn` 使用 Mathlib `LipschitzOnWith`，
并显式要求集合不变性和共同不动点。停止误差估计来自三角不等式，对应 Mathlib
`Topology/MetricSpace/Contracting.lean` 中的不动点距离估计。

`stoppedAt_error_le` 给出当前状态误差不超过容差除以 `1-q`；`eventually_stoppedAt` 只保证
正容差最终满足判据。测试证明线性一步解、刷新/冻结策略差异和平方模型的非最优停滞，
独立 Python 有理数复算覆盖相同案例。上述目标点的最优性、实际问题的收缩性质和浮点误差
不由本批结果自动给出。

`normalDefect`、`gaussNewtonUpdate_sub_target_eq_inverse_normalDefect` 和
`gaussNewtonUpdate_error_le_of_inverse_and_defect` 把正规方程缺陷和逆作用界连接成单步
局部收缩界。它们需要调用者显式提供正规矩阵可逆、$\gamma$ 逆作用界和 $\eta$ 缺陷界。

当前新增的局部收缩桥接位于 `LeanOEM/Core/LocalContraction.lean`：

- `ForwardModel.QuadraticRemainderBound` 是显式的二次线性化余项假设；
- `WeightedJacobianActionBound` 是观测权重与 Jacobian 组合的范数作用界；
- `normalDefect_eq_weighted_linearizationRemainder` 只在
  $y=F(x_\star)$ 且先验均值为 $x_\star$ 时成立；
- `normalDefectBound_of_quadraticRemainder` 在邻域半径 $r$ 内给出
  $\eta=\beta\rho r$；
- `contractsTowardAlong_of_inverse_and_defect` 给出收缩因子
  $q=\gamma\eta$。

标量平方模型的形式 fixture 取 $F(x)=x^2$、目标和先验均值为零、两个权重为一，
在 $|x|\leq1/2$ 内得到 $q=1/2$。该结果证明的是指定数学模型和显式契约，
不证明 ARTS、谱线数据库或真实大气自动满足余项和逆作用界。独立有理数复算
已加入 `scripts/validate_oem_numeric.py`。

## 当前边界

- 形式化核心没有单位系统；公式中的每个量默认已经在同一组一致单位下表达。
- 没有把随机变量、概率测度、期望或统计协方差引入核心；当前 `Covariance` 是带正定性假设的矩阵。
- 迭代误差界只在精确实数和显式收缩条件下成立；没有浮点、条件数或舍入误差保证。
- 没有把 Python、ARTS 代码、运行数据、观测数据库或具体场景输出作为 Lean 依赖。
- 连续辐射传输方程、由光滑性导出有限差分余项界、非线性求解器阻尼及模型收缩条件仍待形式化；已有谱线、差分契约和条件迭代结果不替代这些工作。
- DOFS 的上下界、谱半径和特征值结论尚未加入；当前只定义 trace 并验证其代数性质。
- Rodgers 的教材支持术语和公式来源，不自动支持某个现实场景中的参数、先验或误差模型。
