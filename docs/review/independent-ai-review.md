# 独立 AI 语义复核收口

日期：2026-11-11。Claude Code 和 Codex 分别审阅了 `88e65c5`，其数学实现与候选
`ff3ca1d` 相同。两份报告均为“有条件通过”。本记录整理采纳意见、回归证据及处理边界，
不复制会话原始日志，也不将 AI 复核登记为独立人工复核。

本批基于 `88e65c5` 修订源码注释和文档，增加测试与审计登记；Core/Physics 的数学定义、
接口名称和证明项保持原样。验证对象是包含本批修改的工作区，结果另记于
[构建记录](../audit/build-report.md) 和 [公理记录](../audit/axioms.md)。

## 两处接口语义

`linearizedGradient` 定义的是 `H (z - x) - b`。`TargetStationary` 定义的是目标处的
`normalRhs = 0`。它们作为代数对象允许任意权重和候选矩阵。赋予线性化子问题梯度解释需要
两个权重对称；将目标正规零点解释为原目标一阶驻点还需要目标处的 `HasJacobianAt`。
`WeightWellPosed` 提供对称性，不提供真实导数。当前没有形式化一般目标导数与该正规零点
的完整连接定理。缺陷恒等式和条件误差界仅使用其明确列出的代数与范数条件。

`Problem.toNonlinear` 直接把协方差总函数逆作为权重。通常 OEM/MAP 的权重解释要求先验
和观测误差协方差正定；无条件的正规矩阵等式不证明两个估计问题等价。奇异先验的零方差
方向约束可能丢失；如要描述受先验支持约束的状态，应另在 `x = xₐ + L z` 上建立规格。
当前映射没有提供这一构造，支持白化定理也没有声称已经完成奇异非线性求解器。

## 回归证据

[SemanticBoundaries.lean](../../LeanOEM/Tests/SemanticBoundaries.lean) 使用真实公开定义，
提供五项具名回归，并由默认 `LeanOEMTests` 构建与 `Axioms.lean` 审计覆盖：

1. `nonsymmetric_stationarity_counterexample`：恒等正演和真实 Jacobian 下，非对称观测
   权重可使正规右端为零，而目标沿一个方向的导数为 `-1/4`，且附近存在更低的目标值。
2. `wrongJacobian_stationarity_counterexample`：两个权重均正定，但传入错误候选矩阵，
   正规右端为零时目标方向导数仍为 `-1`。它单独隔离真实导数条件。
3. `singular_conversion_counterexample`：先验为 `diag(1,0)`、Jacobian 和观测误差协方差
   均为单位矩阵、观测为 `(0,1)`。原问题良定且估计为零；先验的总函数逆为整个零矩阵，
   转换后的正规矩阵可逆，零初值的一步更新却为 `(0,1)`。
4. `twoLayerState_nonzero_offset`：有效透过率下零状态也可产生非零输出，表明含固定入射
   偏置的两状态模型通常是仿射映射；减去偏置后才是线性映射。
5. `gaussian_zero_width`：裸 Gaussian 总函数在零线宽时处处为一；谱线解释另需正线宽。

这些是 Lean 内核检查的具体反例及边界事实。公理记录分别列出原有 195 项 Core/Physics
登记和新增 5 项回归；具体反例不替代通用定理，也不提供现实工程保证。

## 文档与 API 意见处理

- 将正规矩阵正定性说明改为接口实际要求的两个权重均正定；本批不新增更弱假设的定理。
- Gaussian 的“归一化”统一解释为中心峰值为一；`strength` 是乘法峰值幅度，不自动表示
  积分线强度。`GaussianLineParameters.profile` 接受全部参数，正线宽由 `Valid` 另给。
- Doppler 的正速度降低频率，负速度提高频率；正性条件不证明一阶近似的现实精度。
- 两状态模型统一称为仿射模型，修复离散化文档中的 `\tau` 转义。
- 将集合接口统一注明为非零实谱；它不记录重数，也未单独形式化复谱版本。
- 支持矩阵“正定推出支持可辨识”可由已有零谱等价和正定可逆性推出。文档给出该推导入口，
  不把缺少独立命名定理认作数学错误。
- 原 averaging kernel 的 `[0,1)` 严格界通过实谱与白化特征值集合相等、特征值严格小于一
  组合得到；高层 `averagingKernel_spectrum_subset_Icc` 直接给出的仍是 `[0,1]`。
- canonical support 按 `range(sqrt Sₐ)` 定义，维数等于 `rank(Sₐ)` 已形式化；与
  `range(Sₐ)` 的子空间集合等式尚无独立定理，文档不声称已完成该接口。

本批完成后，独立人工复核、当前候选远端 CI 和正式发布仍分别按
[发布清单](../release-checklist.md) 记录。
