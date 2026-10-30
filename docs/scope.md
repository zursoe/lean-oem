# 第一阶段核心 API 范围

本阶段只处理有限维、实数、矩阵表示的线性 OEM 规格。

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
- averaging kernel 的 DOFS trace 定义、加法性和静态可辨识性；
- 正定先验下的信息矩阵和后验逆矩阵恒等式；
- 确定性误差分解

  $$
  \hat{x}-x=(I-A)(x_a-x)+g\varepsilon.
  $$

当前还实现了一个与 ARTS 无关的非线性观测模型契约：`ForwardModel`、`HasJacobianAt`、
`JacobianSpec`、锚点线性化、线性化余项，以及它们与现有 `Problem.predict` 的连接。
测试中的标量平方模型验证了一个非线性 Jacobian 和二阶锚点余项；这仍是数学接口示例，
不是辐射传输模型。

P10 当前批次还实现了 `LeanOEM.Physics.FiniteLayer` 和 `LeanOEM.Physics.Spectral`：归一化的有限层、
无散射传输递推、Planck 正性、Doppler 基本性质和通道响应范围性质。它们是独立数学模型，
不代表 ARTS 的完整实现。

测试模块包含一维精确数值、秩亏 `2 × 1` 观测和非法协方差边界；自动审计脚本位于
`scripts/run_audit.sh`，独立数值核对位于 `scripts/validate_oem_numeric.py`，定义和证据映射见
`docs/source-mapping.md`。当前没有把这些定义解释为某个具体 ARTS 配置、真实观测或有限精度程序的事实。
概率测度、简化谱线响应、单位系统、传感器响应和 ARTS 连接属于后续模块；当前 Planck、
Doppler、通道响应和 Gauss–Newton 只实现了无量纲或单步数学性质。

## 后续形式化边界

后续模块遵循“理论和算法独立于 ARTS，实现和数据作为外部证据”的架构：

- `ForwardModel` 抽象描述状态到观测的函数，Jacobian 作为导数的矩阵表示或带误差的近似规格；
- 简化辐射传输、Doppler 频移、通道响应和有限层递推在独立数学模块中定义；
- 非线性 Gauss–Newton OEM 先形式化目标函数、单步更新和局部条件，不直接声称全局收敛；当前已实现目标函数、正规方程和可逆矩阵下的单步规格；
- ARTS/Python 只通过固定版本、配置、fixture 和误差报告与形式模型建立符合性证据；
- 真实单位、谱线数据库、浮点误差和观测有效性保持为独立假设或工程证据。

完整 ARTS 代码、数据库和真实项目数据不进入 `lean-oem` 的核心依赖。只有当一个辐射传输模块拥有独立 API、非平凡定理、可复现 fixture 和完整审计后，才考虑建立独立公开包。
