# 当前开发状态

更新时间：2026-11-05。

本批从本地提交 `724f9df` 开始，完成 canonical support 到自动矩形 `SupportFactor` 的转换。
验证结果和代码基线以 [构建记录](audit/build-report.md) 和 [公理记录](audit/axioms.md) 为准；
本批代码已在 `ac8df74` 收口。

## 已完成基线

- 有限维、实数、矩阵表示的线性 OEM 核心；
- 后验协方差、Joseph 形式、信息形式和确定性误差分解；
- DOFS trace、显式矩阵序条件下的上下界和逐特征值界、正定 OEM 条件下最优增益的 `0 ≤ DOFS ≤ n` 定理和静态可辨识性接口；
- 正定先验的平方根因子、白化相似关系、原 averaging kernel 的全部实特征值 `[0,1)` 界及 DOFS 谱求和；
- `Observable` 下白化矩阵严格正特征值和白化矩阵秩的 Jacobian 上界；
- 观测误差正定时白化矩阵秩等于 Jacobian 秩；
- 白化 averaging kernel 的逐向量核等价已连接到 `K (L v) = 0`；
- 白化矩阵的可辨识性与 `Observable` 等价，零谱存在性与 `¬ Observable` 等价；
- Physics 中 Gaussian 线宽的正性参数包及其合成测试；
- `ForwardModel`、Jacobian 导数契约、局部收缩和 Gauss–Newton 迭代规格；
- 带统一加性误差底的 Gauss–Newton 轨迹有限步界和稳态误差界；
- Jacobian、有限层和有限通道离散化误差契约；
- 前向模型/Jacobian 联合误差到正规方程和一步更新误差的契约；
- 两通道两状态有限层模型及其显式 Jacobian；
- `LeanOEM.Core` 稳定聚合入口和 `LeanOEM.Physics` 实验聚合入口。
- `LeanOEM` 兼容根入口只导出 `LeanOEM.Core`；实验性 Physics 通过显式导入保持隔离。
- 奇异半正定先验的 `Problem.SupportFactor` 支持因子接口；支持坐标白化、谱界、零谱、秩界和
  `DOFS ≤ rank(Sₐ)` 已完成，见 [奇异先验支持白化规格](singular-prior-design.md)。
- `Problem.PriorSqrtFactor.ofPosSemidef` 已能自动构造半正定先验的精确平方根因子，并把
  `range(sqrt Sₐ)` 定义为 canonical support；support 维数等于 `rank(Sₐ)`。
- `LeanOEM.Core.SupportCoordinates` 已为 canonical support 建立可复用坐标契约：在
  `EuclideanSpace` 表示中选择 `stdOrthonormalBasis`，再搬回既有 `State n` 代数表示；
  得到 `supportBasisMatrix`，并证明其 `mulVec` 单射、列空间等于 canonical support，
  以及矩阵秩和 support 维数/先验协方差秩的对应关系。
- 已证明 `supportBasisMatrixᴴ * supportBasisMatrix = I`，并由此证明
  `sqrt(Sₐ) * supportBasisMatrix` 的协方差 Gram 等式和满列秩；
  `PriorSqrtFactor.toSupportFactor` 现在可以自动构造 `SupportFactor`，且其列空间等于
  canonical support。

## 当前信任边界

形式定理只负责 Lean 定义和显式假设。当前仍没有形式化单位系统、概率测度、浮点舍入、
连续频率积分、完整谱线数据库或外部工程代码。两状态模型中的源项是归一化数学变量，
不能直接称为温度、吸收系数或风速。

`normalMatrix_posDef` 现在区分了带正定先验的 MAP 可解性和 `Observable` 表示的数据可辨识性。
后续测试和文档应继续保持这两个概念分开。

奇异先验路径不使用先验协方差的逆矩阵，也不把总函数矩阵逆解释为伪逆。支持因子描述先验
协方差的变化子空间；ambient 状态均值和支持内可辨识性仍然分开记录。

## 下一工作包

下一阶段优先处理 ambient averaging kernel 与支持矩阵之间的非零谱/特征多项式乘幂关系，
并复用自动 `SupportFactor` 验证其支持谱接口；统一误差底与具体模型契约的桥接仍为独立
后续工作包。

## 发布状态

当前 `lakefile.toml` 的包版本仍为 `0.1.0`，但仓库尚未创建 Git tag 或 GitHub Release。
发布前必须同步更新发布说明、审计提交号、稳定/实验入口说明，并重新执行干净 checkout 构建。
