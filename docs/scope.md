# 核心 API 范围

核心采用有限维、实数、矩阵表示，包含线性 OEM 和非线性迭代的数学规格。

稳定入口为 `LeanOEM.Core`；`LeanOEM.Physics` 聚合与外部工程无关、仍在演化的归一化数学模型和
离散化 fixture，属于实验性 API。兼容根入口 `LeanOEM` 只导出稳定核心；使用实验性 Physics
时需要显式导入 `LeanOEM.Physics`。

状态向量属于 `Fin n → ℝ`，观测向量属于 `Fin m → ℝ`，Jacobian 是
`Matrix (Fin m) (Fin n) ℝ`。`Problem n m` 保存 Jacobian、先验均值、先验协方差
和观测误差协方差 `observationErrorCovariance`。

当前协方差只是矩阵别名。正定或半正定性质通过定理假设显式提供，不由结构字段
自动声称。矩阵逆是 Mathlib 中的总函数；任何把它解释为通常逆矩阵的结论都必须
先给出正定性或其他可逆性条件。

当前已实现的对象和结论包括：

- 创新协方差 $K S_a K^\mathsf{T} + S_y$；
- 由创新协方差定义的增益；
- 任意增益的线性估计器；
- averaging kernel $A = gK$；
- 创新协方差的正定性和可逆性；
- 良定性假设、创新协方差逆矩阵的两侧消去和增益规格；
- 标准后验协方差、Joseph 协方差及其半正定性；
- averaging kernel 的 DOFS trace 定义、加法性、`0 ≤ A ≤ I` 条件下的上下界和静态可辨识性；
- 正定先验下的信息矩阵和后验逆矩阵恒等式；
- 奇异半正定先验的矩形支持因子、支持坐标白化、支持谱界、零谱和秩界；
- 半正定先验的自动平方根因子和 `range(sqrt Sₐ)` canonical support；
- canonical support 的 EuclideanSpace 正交规范基和有限坐标列矩阵契约；
- 从 canonical support 自动构造矩形 `SupportFactor` 的协方差、满列秩与列空间契约；
- ambient/support averaging kernel 的特征多项式乘幂关系；
- 确定性误差分解

  $$
  \hat{x}-x=(I-A)(x_a-x)+g\varepsilon.
  $$

当前还实现了一个抽象的非线性观测模型契约：`ForwardModel`、`HasJacobianAt`、
`JacobianSpec`、锚点线性化、线性化余项，以及它们与现有 `Problem.predict` 的连接。
测试中的标量平方模型验证了一个非线性 Jacobian 和二阶锚点余项；这仍是数学接口示例，
不是辐射传输模型。

Physics 模块实现了归一化的有限层、无散射传输递推、Planck 正性、Doppler 基本性质、带正线宽
参数包的 Gaussian 谱线和通道响应范围性质。它们是独立数学模型，不代表任何具体工程实现。

测试模块包含一维精确数值、秩亏 `2 × 1` 观测、非法协方差边界和 Physics 参数非法反例；自动审计脚本位于
`scripts/run_audit.sh`，独立精确算术核对位于 `scripts/validate_oem_numeric.py`，定义和数学来源映射见
`docs/source-mapping.md`。当前没有把这些定义解释为某个具体工程配置、真实观测或有限精度程序的事实。
概率测度、单位系统和完整传感器响应未纳入当前范围，也不是发布门槛；已有 Gaussian 简化谱线、
显式余项条件下的标量中心差分误差契约和代数正规方程规格。

`linearizedGradient` 记录代数正规残差；梯度解释要求对称权重。`TargetStationary` 只记录
目标处的正规右端为零；解释为原目标一阶驻点还需要 `HasJacobianAt`。当前没有形式化一般
目标导数与正规驻点的完整连接定理。`Problem.toNonlinear` 只进行协方差总函数逆权重映射，
通常 OEM/MAP 的权重解释要求先验和观测误差协方差正定；奇异先验下不承诺估计问题等价。

P11 还定义了权重正定性、按步选择 Jacobian 的精确实数轨迹和绝对步长停止判据，并在显式沿轨迹收缩条件下
证明几何误差界、收敛和停止误差界；新增带统一加性误差底的轨迹界和 $\tau/(1-q)$ 稳态界。范数为最大绝对分量范数；停止时返回当前状态。
当前还增加了一个局部收缩垂直切片：在无噪声、先验均值等于目标状态、显式二次线性化余项界、
加权 Jacobian 作用界和正规矩阵逆作用界下，正规缺陷界可以推出沿轨迹收缩。标量平方模型
已经完成该条件链的形式测试。当前还加入了目标正规右端为零、目标残差和 Jacobian 变化项的
正规缺陷分解及界；调用者仍需在 Lean 中证明显式契约，独立数值复核仅提供辅助证据。
目标点的存在、极小性或现实 MAP 含义未由这些接口自动证明。
P12 第一批还定义了 Jacobian 离散化误差契约，证明其对加权作用常数、目标正规方程残差、
正规缺陷和更新误差底的影响，并用中心差分三次函数 fixture 验证。浮点舍入、条件数和
有限层/通道离散化的完整误差仍未纳入核心。当前 P12 第二批已增加两层共同源项有限层
fixture：它证明固定透过率误差如何传播到正演、Jacobian、正规方程残差和更新误差底；
它不等同于温度、吸收系数、风速或真实谱线参数的物理参数化。
P12-C 第一批进一步定义有限通道响应的权重 `L¹` 误差、谱值误差和通道 Jacobian 误差，
并用两频率有限层 fixture 验证组合界；连续频率积分、求积阶数和网格细化误差仍未纳入核心。
P12-C-2 第一批增加了显式 `C h^p` 点态误差到通道输出和 Jacobian 的传播定理，并用中心
有限差分的 $h^2$ 误差作实例；这仍不证明具体积分规则自动满足该阶数。

当前还增加了 `ForwardModelErrorBound`、`normalRhsFor` 和前向模型/Jacobian 联合误差定理。
若近似前向模型的误差为 $\varepsilon_F$、近似 Jacobian 的加权误差为 $\varepsilon_K$、
近似 Jacobian 的加权作用常数为 $\beta$，则目标处的正规右端误差满足

$$
\|b_h-b\|\leq \varepsilon_K\sigma+\beta\varepsilon_F,
$$

并可在显式逆作用界下传到一步 Gauss–Newton 更新误差。该结果仍是精确实数契约，
不包含浮点舍入或具体工程符合性判断。

`LeanOEM.Physics.TwoLayerState` 进一步定义两个通道、两个独立层源项的有限层模型，
并证明其显式矩阵是 `ForwardModel` 的导数表示。源项仍是归一化模型变量，不自动代表
温度、吸收系数或风速。
零步长却非最优的平方模型反例见 [迭代规格](iteration.md)。

## 后续形式化边界

后续模块遵循“纯 Lean 数学、显式假设和合成例子”的架构：

- `ForwardModel` 抽象描述状态到观测的函数，Jacobian 作为导数的矩阵表示或带误差的近似规格；
- 简化辐射传输、Doppler 频移、通道响应和有限层递推在独立数学模块中定义；
- 非线性 Gauss–Newton OEM 已有目标、单步、权重正定性、正规驻点、轨迹和有条件收敛结果，
  以及显式余项/逆作用界到收缩的桥接；阻尼、一般模型自动满足这些界和目标最优性仍待独立研究；
- 单位、谱线数据库、浮点误差和观测有效性保持为独立假设，不进入当前主线。

外部边界：本库不依赖 ARTS、Python 工程、真实数据或 SCI 论文项目；这些内容可以在库外作为应用背景或独立验证来源，但不属于主库目标、依赖、稳定 API 或发布门槛。

当前 DOFS 上下界有三层接口：通用定理接收 averaging kernel 半正定以及 `I - A` 半正定作为显式
矩阵序假设；`Problem.dofs_bounds_of_posDef` 在正定先验和正定观测误差下直接证明最优增益满足
$0\leq\mathrm{DOFS}\leq n$；`Problem.SupportFactor` 则把半正定先验限制到支持坐标，证明
$\mathrm{DOFS}\leq r$、$\mathrm{DOFS}\leq\operatorname{rank}(K L)$ 和
$\mathrm{DOFS}\leq\operatorname{rank}(S_a)$。

在显式矩阵序条件下，`eigenvalues_bounds_of_posSemidef` 证明每个 Hermitian 特征值落在 `[0, 1]`。
`PriorWhitening` 通过可逆先验因子 `Sₐ = L Lᴴ` 构造 `B = L⁻¹ A L`，证明其半正定性、
补矩阵正定性、严格上界、零谱刻画和 DOFS 谱求和。`SupportWhitening` 对矩形满列秩因子
`Sₐ = L Lᴴ` 在支持坐标中复用同一证明链；`SupportCoordinates` 进一步用特征多项式乘幂
关系给出 ambient/support 的非零实谱集合相等和零根代数重数关系，仍不声称奇异因子下的
完整相似变换。

正定先验可用矩阵平方根自动构造可逆因子，因此 `Problem.averagingKernel_spectrum_subset_Icc`
只要求先验与观测误差正定。半正定先验现在已有自动平方根、canonical range support、有限
坐标列矩阵、自动矩形支持因子、ambient/support 特征多项式乘幂关系和非零实谱集合接口；
见 [奇异先验支持白化规格](singular-prior-design.md)。
