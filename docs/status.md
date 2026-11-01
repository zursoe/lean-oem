# 当前开发状态

更新时间：2026-11-02。

本轮开始时的远端主线基线为 `23c6473`，工作区干净且与 `origin/main` 同步。当前修改完成后，
应以最后一次 `lake build`、`scripts/run_audit.sh --no-build` 和
`python3 scripts/validate_oem_numeric.py` 的现场输出作为最终验证记录。

## 已完成基线

- 有限维、实数、矩阵表示的线性 OEM 核心；
- 后验协方差、Joseph 形式、信息形式和确定性误差分解；
- DOFS trace 和静态可辨识性接口；
- `ForwardModel`、Jacobian 导数契约、局部收缩和 Gauss–Newton 迭代规格；
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

下一阶段继续做纯 Lean 数学工作：完善 Physics 模块的参数有效性结构、误差契约、合成反例、
DOFS/可辨识性定理和稳定 API。外部工程和真实数据不进入主线开发目标。

## 发布状态

当前 `lakefile.toml` 的包版本仍为 `0.1.0`，但仓库尚未创建 Git tag 或 GitHub Release。
发布前必须同步更新发布说明、审计提交号、稳定/实验入口说明，并重新执行干净 checkout 构建。
