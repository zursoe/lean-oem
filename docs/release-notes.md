# lean-oem `0.1.0` 版本说明

版本引用：`v0.1.0`。作者已确认本版数学含义和范围，并于 2026-11-11 明确决定将当前候选
正式定为 `0.1.0`。发布结果见 [GitHub Release](https://github.com/zursoe/lean-oem/releases/tag/v0.1.0)，
受检提交与流程证据分别记于 [构建记录](audit/build-report.md) 和 [发布检查](release-checklist.md)。

版本定位：这是纯 Lean 4 + Mathlib OEM 数学库的首个版本。`LeanOEM.Core` 是稳定通用入口，
`LeanOEM.Physics` 是随包提供的实验性归一化数学模块，不构成外部工程适配承诺。

## 导入与兼容性

`import LeanOEM` 和 `import LeanOEM.Core` 提供通用核心；使用实验模型时增加
`import LeanOEM.Physics`。此前依赖根入口间接导入 Physics 的调用方需要显式增加该导入。
Physics 随包构建、接受相同的无占位证明要求，但尚不承诺 API 兼容性。

非线性接口明确 `linearizedGradient` 和 `TargetStationary`
的代数含义，以及梯度解释所需的对称权重和真实导数条件。`Problem.toNonlinear` 明确为
协方差总函数逆权重映射，奇异先验下不保证估计问题等价。新增五项语义边界回归纳入默认
构建与公理审计，处理详情见 [独立 AI 复核收口](review/independent-ai-review.md)。

## Core 范围

- 有限维、实数、矩阵表示的线性 OEM 问题规格；
- 预测、创新、创新协方差、增益、后验协方差、Joseph 形式和信息形式；
- averaging kernel、DOFS trace、显式矩阵序条件下的上下界、静态可辨识性和确定性检索误差；
- `ForwardModel`、Jacobian 导数规格、二次余项和局部收缩契约；
- 非线性 Gauss–Newton 轨迹、停止判据和条件误差界；
- 通用正演和 Jacobian 离散化误差契约；
- 前向模型/Jacobian 联合误差到正规方程和一步更新误差的传播；
- 带统一加性误差底的 Gauss–Newton 轨迹有限步界和稳态界；
- 显式矩阵序条件下的 DOFS 和 Hermitian 逐特征值界，以及正定先验/观测误差下
  最优增益的 `0 ≤ DOFS ≤ n` 定理；
- 正定先验的平方根因子、白化相似变换、原 averaging kernel 的实谱 `[0,1)` 界、
  特征多项式实数分裂和 DOFS 特征值求和；
- 奇异半正定先验的矩形 `SupportFactor`、支持坐标白化、严格谱界、零谱、秩界和 DOFS 支持维数界；
- 任意半正定先验的精确 `PriorSqrtFactor` 和 `range(sqrt Sₐ)` canonical support；
- canonical support 的 EuclideanSpace 正交规范基、有限坐标列矩阵、满列秩和像空间定理；
- `PriorSqrtFactor.toSupportFactor` 自动构造矩形支持因子，并提供协方差、满列秩和列空间定理；
- 支持因子下 ambient/support 特征多项式乘幂关系；
- 支持因子下 ambient/support 非零实谱集合相等、零根代数重数加法，以及支持可辨识时的
  `n-r` 零方向重数；
- `Observable` 下的严格正特征值结论，以及白化 averaging kernel 的 Jacobian 秩上界；
- Core-only 调用例子、精确矩阵和迭代边界反例。

## Physics 实验范围

- 归一化无散射有限层递推、非负性、上界和两层组合性质；
- Planck 正性、Gaussian 正线宽参数包、Doppler 和有限通道权重的基本定理；
- 两层共同源项及两通道两状态模型、显式 Jacobian 和导数契约；
- 有限层参数、有限通道权重/谱值和给定步长误差到 OEM 契约的传播；
- 零线宽、零温度、Doppler 正性边界、空网格及非法透过率等合成反例。

## 形式化边界

定理只对 Lean 定义和显式假设负责。单位、概率测度、浮点舍入、连续频率积分、完整谱线数据库、
真实观测和有限精度程序未纳入本库主线。奇异先验结果不使用伪逆，也不承诺完整相似变换。
一步更新误差结果不自动给出整体迭代收敛；统一误差底轨迹仍需要显式沿轨迹契约。

外部边界：本库不依赖 ARTS、Python 工程、真实数据或 SCI 论文项目；这些内容可以在库外作为应用背景或独立验证来源，但不属于主库目标、依赖、稳定 API 或发布门槛。

## 复现

```bash
lake build LeanOEM LeanOEMTests
bash scripts/run_audit.sh --no-build
python3 scripts/validate_oem_numeric.py
```

依赖版本由 `lean-toolchain`、`lakefile.toml` 和 `lake-manifest.json` 固定。Mathlib 源码和
`.lake` 编译缓存不进入 Git。独立精确算术脚本只用于审计；Lean 定理允许的基础公理为
`propext`、`Classical.choice`、`Quot.sound`，结果见 [公理记录](audit/axioms.md)。

默认测试构建显式导入 Physics 聚合入口，保证干净环境下公理审计所需的产物存在。
审计脚本在 Lean 失败时显示原始错误并保留退出码；相关复现记录见构建记录的首次候选失败条目。

## 验证与审查记录

内部源码复核见 [候选审阅记录](review/release-candidate-review.md)，两份独立 AI 报告及处理
情况见 [语义收口记录](review/independent-ai-review.md)。作者已确认范围，候选 `7f8265f`
远端 CI 已通过：3425 个构建目标、200 项公理审计和精确有理数复核均成功；最终主线与
标签验证结果见构建记录。两份 AI 复核与作者确认分别登记，独立人工逐项数学审查尚未
登记完成，作为后续审查事项保留。本次正式发布按用户明确决定执行，见
[发布检查与审查记录](release-checklist.md)。
