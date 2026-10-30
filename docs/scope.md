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
- 确定性误差分解

  $$
  \hat{x}-x=(I-A)(x_a-x)+g\varepsilon.
  $$

测试模块包含一维精确数值、秩亏 `2 × 1` 观测和非法协方差边界；自动审计脚本位于
`scripts/run_audit.sh`。当前没有把这些定义解释为某个具体 ARTS 配置、真实观测或有限精度程序的事实。
概率测度、非线性 Jacobian、单位系统、传感器响应和 ARTS 连接属于后续模块。
