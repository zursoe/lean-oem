# 当前开发状态

更新时间：2026-11-11。

最近代码批次从本地提交 `724f9df` 开始，完成 canonical support 到自动矩形 `SupportFactor` 的转换，
并在 `52e36b1` 收口。本轮发布准备从 `9bb9f25` 开始；历史代码提交号仍保留在审计记录中。
首次干净受检候选为 `ff3ca1d`。本批从 `88e65c5` 继续处理独立 AI 语义复核意见，
验证结果以 [构建记录](audit/build-report.md) 和 [公理记录](audit/axioms.md) 的最新条目为准。

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
- 已证明自动支持因子的 ambient averaging kernel 与支持白化矩阵满足特征多项式乘幂关系
  `χ_A = X^(n-r) χ_{Bₛ}`，并已整理为非零实谱集合相等和零根代数重数加法接口。

## 当前信任边界

形式定理只负责 Lean 定义和显式假设。当前仍没有形式化单位系统、概率测度、浮点舍入、
连续频率积分、完整谱线数据库或外部工程代码。两状态模型中的源项是归一化数学变量，
不能直接称为温度、吸收系数或风速。

`normalMatrix_posDef` 现在区分了带正定先验的 MAP 可解性和 `Observable` 表示的数据可辨识性。
后续测试和文档应继续保持这两个概念分开。

奇异先验路径不使用先验协方差的逆矩阵，也不把总函数矩阵逆解释为伪逆。支持因子描述先验
协方差的变化子空间；ambient 状态均值和支持内可辨识性仍然分开记录。

`linearizedGradient` 和 `TargetStationary` 只记录代数正规残差及正规右端零点。梯度和
原目标驻点的解释需要对称权重及真实 Jacobian；`WeightWellPosed` 只提供前一项。
`toNonlinear` 直接映射协方差总函数逆，奇异先验下不承诺保持原估计问题。

## 首次发布候选收口

以下工作已完成：

1. 项目规则、README、范围、路线和候选说明统一为纯 Lean 数学库目标；
2. 完成 Core/Physics 入口、联合误差、正定/奇异先验谱的内部源码复核，见
   [候选审阅](review/release-candidate-review.md)；
3. 公理登记覆盖全部 192 个显式公开定理及 3 个因子构造，195 项输出完整通过；
4. 修复干净构建遗漏 Physics 聚合入口的问题，并使审计脚本保留 Lean 失败输出和退出码；
5. 修正后本地与干净 worktree 构建均通过，完成 3423 个目标，审计和独立精确算术复核通过。

## 独立 AI 复核后的语义收口

Claude Code 和 Codex 均对 `88e65c5` 给出“有条件通过”。本批修正正规零点和梯度的解释
条件、奇异先验转换边界、Physics 参数说明及文档精度，保留现有数学定义、接口名称和
Core/Physics 证明项。五项具名语义回归已加入默认测试构建及公理登记；处理依据见
[独立 AI 复核收口记录](review/independent-ai-review.md)。

本批构建和审计针对包含这些修改的本地工作区，不沿用 `ff3ca1d` 的历史验证结论。
完整构建通过 3425 个目标，公理输出 200/200 项完整，独立精确算术、占位扫描和编译产物
跟踪检查均通过；依赖仍只有允许的三项基础公理。
独立 AI 复核与人工审查分别记录。当前候选的远端 CI、tag 和 Release 仍未执行，
不能用历史提交的远端验证代替。具体待办见 [发布清单](release-checklist.md)。

统一误差底与具体模型契约的桥接、阻尼迭代和其他新数学功能均属于发布后的独立工作包。

## 发布状态

当前 `lakefile.toml` 的包版本仍为 `0.1.0`，仓库尚未创建 Git tag 或 GitHub Release。
本轮起点 `9bb9f25` 比 `origin/main` 超前 30 个提交；本轮只维护本地候选材料。
本批基于 `88e65c5` 归档为本地语义边界修正提交；发布材料区分历史干净候选和本批验证。
最终需要作者核对的数学含义见 [作者语义核对](review/author-semantic-review.md)，尚待确认。
后续如修改源代码、测试、构建配置或审计脚本，应重新验证相应候选。
