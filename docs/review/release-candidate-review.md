# `0.1.0` 发布候选内部审阅

审阅日期：2026-11-11

审阅对象：从本地提交 `9bb9f25` 开始的发布收口批次；数学实现基线为 `52e36b1`。
本记录由 AI 对源代码、定理陈述和合成例子进行内部复核形成；独立人工语义审查仍待完成。
实际受检提交与构建结果以 [构建记录](../audit/build-report.md) 的本轮条目为准。
首次发布收口的受检候选为 `ff3ca1d`。此后的独立 AI 意见及语义说明修正见
[语义复核收口记录](independent-ai-review.md)，本轮验证不沿用历史候选的构建结论。

## 版本定位

本候选版本是纯 Lean 4 + Mathlib 数学库。`LeanOEM.Core` 提供稳定的有限维 OEM 数学 API，
`LeanOEM.Physics` 提供与外部工程无关的归一化数学定义、定理和合成例子，并保持实验性 API。

ARTS、Python 工程、真实数据和 SCI 论文项目不属于本库目标、依赖、稳定 API 或发布门槛。
独立精确算术脚本只用于辅助验证，不能替代 Lean 内核检查。

## 审阅结论

### 入口边界

- `LeanOEM.Core` 聚合通用 OEM、协方差、可观测性、迭代和误差契约模块。
- `LeanOEM.Physics` 通过显式入口聚合有限层、谱线、通道响应和离散化数学模块。
- 兼容入口 `LeanOEM` 只导出稳定核心；Core-only 测试不导入 Physics。

证据：入口文件 [LeanOEM.lean](../../LeanOEM.lean)、[Core.lean](../../LeanOEM/Core.lean)、
[Physics.lean](../../LeanOEM/Physics.lean) 和 [CoreEntry 测试](../../LeanOEM/Tests/CoreEntry.lean)。
依赖方向为 Physics → Core；Core 的直接和传递 LeanOEM 导入均未进入 Physics 或测试目录。

### 核心语义

- 状态、观测和 Jacobian 的维度约定在类型和文档中保持一致。
- 协方差的正定或半正定性质由显式假设提供，不由矩阵别名自动声称。
- 总函数矩阵逆只在正定或其他可逆性条件下被解释为通常逆。
- 后验协方差、Joseph 形式、信息形式、DOFS 和可观测性定理均保留适用条件。

证据：[Assumptions](../../LeanOEM/Core/Assumptions.lean)、[Covariance](../../LeanOEM/Core/Covariance.lean)、
[Information](../../LeanOEM/Core/Information.lean) 和 [NonlinearOEM](../../LeanOEM/Core/NonlinearOEM.lean)。
`WeightWellPosed` 要求先验和观测权重正定，正规矩阵正定性不额外要求 Jacobian 可观测。
迭代的范数仍是最大绝对分量范数，停止返回当前状态，零步长不保证目标最优。
`linearizedGradient` 和 `TargetStationary` 记录代数正规残差与正规右端零点；梯度和原目标
驻点的解释分别需要对称权重及真实 Jacobian。`toNonlinear` 的总函数逆权重映射不对奇异
先验保证估计问题等价。这些边界已由后续独立 AI 复核指出并补入源码及回归。

### 联合误差和迭代

[DiscretizationError](../../LeanOEM/Core/DiscretizationError.lean) 比较相同观测、先验和权重下的
两个正演模型，正规右端误差为 `εK · σ + βh · εF`。更新误差定理还要求近似正规矩阵可逆、
非负逆作用常数和显式逆作用界，结论针对同一目标处的一步更新。

[三次模型测试](../../LeanOEM/Tests/DiscretizationError.lean) 实例化了两类误差和逆作用界；
[Iteration](../../LeanOEM/Core/Iteration.lean) 中的统一误差底轨迹定理另要求沿轨迹契约。
两者之间的一般组合接口仍是后续数学工作包，不能把一步结果写成整体迭代收敛。

### 奇异先验接口

- `SupportFactor` 使用满列秩矩形因子表达半正定先验的变化子空间。
- canonical `range(sqrt Sₐ)` support、有限坐标和自动矩形因子之间的契约已经连接。
- ambient/support 特征多项式乘幂、非零实谱集合和零根代数重数关系已经记录。
- 模块不使用 Moore–Penrose 伪逆，也不声称奇异情形下的完整相似变换。

证据：[PriorWhitening](../../LeanOEM/Core/PriorWhitening.lean)、
[SupportWhitening](../../LeanOEM/Core/SupportWhitening.lean)、
[SupportCoordinates](../../LeanOEM/Core/SupportCoordinates.lean) 及其对应测试。
正定先验路径的方向是 `B = L⁻¹ A L`；非对称相关先验例子检查了该方向。
奇异路径中，正交规范基在 EuclideanSpace 中选择后搬回矩阵坐标，既有状态范数未被更改。
`L = sqrt(Sₐ) Q` 才是协方差因子，`Q` 本身只提供支持坐标。

特征多项式、非零实谱集合和零根重数的代数恒等式不要求观测误差正定；支持谱界及可辨识时
零根重数为 `n-r` 的结论要求观测误差正定。非零实谱集合接口不记录重数。

### Physics 边界

- 有限层、Planck、Doppler、Gaussian、通道响应和两状态模型使用归一化数学变量。
- 有限层的范围结果要求透过率在 `[0,1]`；Planck 正性有五项正参数条件，Doppler 正性要求
  正频率、正的速度尺度和 `velocity < lightSpeed`，不构成近似模型精度结论。
- Gaussian 原始总函数在零线宽下处处为一，`GaussianLineParameters.Valid` 单独要求正线宽；
  “归一化”在此表示中心峰值为一，不是积分归一化概率密度。
- 通道响应是有限个非负、和为一的权重；连续积分或具体求积规则的误差阶数未被证明。
- 模块没有把源项、线宽或速度自动解释成现实工程量，也没有引入外部数据库或工程代码。

证据：[Spectral](../../LeanOEM/Physics/Spectral.lean)、[有限层误差模块](../../LeanOEM/Physics/FiniteLayerDiscretization.lean)、
[TwoLayerState](../../LeanOEM/Physics/TwoLayerState.lean) 及其测试。两状态 fixture 检查导数表示、
有理数输出和参数扰动的正演误差；该测试没有建立完整两状态迭代误差链。

## 本轮修正与结论

接受现有数学 API 作为候选范围，Physics 继续保持实验性。复核过程中修正了三类文档问题：
旧的外部工程/论文目标，已完成支持坐标工作仍被标为待办，以及矩形因子交换说明把
创新协方差 `S = K Sₐ Kᴴ + Sᵧ` 误记成观测误差协方差。对应代码始终使用创新协方差。

首次收口补充了 22 个已有公开辅助定理和 `toSupportFactor` 构造，原 Core/Physics 登记为
195 项。首次收口不增加数学定义或定理，不修改现有证明项；后续增加的 5 项语义边界回归
单独登记于公理记录，Core/Physics 定义和证明项仍保持原样。

候选 `9512730` 的干净构建还暴露了一个构建图缺口：测试原先只导入各个 Physics 子模块，
没有导入聚合入口，导致后续公理审计找不到 `LeanOEM/Physics.olean`。测试根入口现已显式导入
`LeanOEM.Physics`，Core-only 测试继续单独导入 Core。审计脚本也已改为先显示 Lean 的错误输出，
再按原退出码停止，避免错误只留在被丢弃的命令输出中。

## 验证依据

修正后候选 `ff3ca1d` 的本地和干净 worktree 均完成 `lake build LeanOEM LeanOEMTests`
（3423 个目标）、`bash scripts/run_audit.sh --no-build`、独立精确算术复核和 `git diff --check`。
195 项公理输出完整，仅使用允许的基础公理；缺失入口产物的审计失败分支也经过回归检查。
干净构建重新检出 9 个锁定依赖，复用 Git 对象与 Mathlib 下载缓存，项目自身产物全部重建。

后续语义修正于 `7cf0e67` 归档，作者已确认范围。含确认文档的候选 `7f8265f`
[远端 CI](https://github.com/zursoe/lean-oem/actions/runs/43010549697) 已通过 3425 个构建目标和
200 项公理审计；两者的源码与测试一致。完整记录见构建记录的最新条目。

## 尚待完成

- 独立人工复核联合误差、正定/奇异先验谱和 Physics 语义；本内部记录供复核者逐项查阅。
- 候选分支已通过远端 CI，用户已于 2026-11-11 决定正式发行 `0.1.0`；主线、tag 和 Release
  结果按发布检查及构建记录登记。上项独立人工审查尚未完成，保留为后续维护事项。
- 发布后再单独评估新的纯数学工作包。
