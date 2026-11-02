# 当前开发状态

更新时间：2026-11-02。

本批从本地提交 `edef89e` 开始，新增先验白化与最优增益谱界。验证结果和代码基线以
[构建记录](audit/build-report.md) 和 [公理记录](audit/axioms.md) 为准；本批仅作本地提交。

## 已完成基线

- 有限维、实数、矩阵表示的线性 OEM 核心；
- 后验协方差、Joseph 形式、信息形式和确定性误差分解；
- DOFS trace、显式矩阵序条件下的上下界和逐特征值界、正定 OEM 条件下最优增益的 `0 ≤ DOFS ≤ n` 定理和静态可辨识性接口；
- 正定先验的平方根因子、白化相似关系、原 averaging kernel 的全部实特征值 `[0,1]` 界及 DOFS 谱求和；
- Physics 中 Gaussian 线宽的正性参数包及其合成测试；
- `ForwardModel`、Jacobian 导数契约、局部收缩和 Gauss–Newton 迭代规格；
- 带统一加性误差底的 Gauss–Newton 轨迹有限步界和稳态误差界；
- Jacobian、有限层和有限通道离散化误差契约；
- 前向模型/Jacobian 联合误差到正规方程和一步更新误差的契约；
- 两通道两状态有限层模型及其显式 Jacobian；
- `LeanOEM.Core` 稳定聚合入口和 `LeanOEM.Physics` 实验聚合入口。
- `LeanOEM` 兼容根入口只导出 `LeanOEM.Core`；实验性 Physics 通过显式导入保持隔离。

## 当前信任边界

形式定理只负责 Lean 定义和显式假设。当前仍没有形式化单位系统、概率测度、浮点舍入、
连续频率积分、完整谱线数据库或外部工程代码。两状态模型中的源项是归一化数学变量，
不能直接称为温度、吸收系数或风速。

`normalMatrix_posDef` 现在区分了带正定先验的 MAP 可解性和 `Observable` 表示的数据可辨识性。
后续测试和文档应继续保持这两个概念分开。

## 下一工作包

下一阶段优先连接白化矩阵的零特征值、Jacobian 核与 `Observable`，然后完善 DOFS 的秩界及
严格上界。统一误差底与具体模型契约的桥接仍为独立后续工作包。

## 发布状态

当前 `lakefile.toml` 的包版本仍为 `0.1.0`，但仓库尚未创建 Git tag 或 GitHub Release。
发布前必须同步更新发布说明、审计提交号、稳定/实验入口说明，并重新执行干净 checkout 构建。
