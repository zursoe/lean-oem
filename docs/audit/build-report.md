# 干净 checkout 构建记录

历史记录（提交 `e803313`，2026-10-31）：

验证步骤：

1. 从提交建立临时 worktree `/tmp/lean-oem-final-review`；
2. 临时 worktree 没有当前工作区的 `.lake` 目录；
3. `lake build` 重新物化锁定的 Mathlib 和传递依赖；
4. 完成 3166 个构建目标；
5. 在修正脚本执行位后运行 `scripts/run_audit.sh --no-build`。

## 当前提交验证

验证日期：2026-11-01

验证提交：`92325a6`。

本次在当前锁定依赖和工作区执行完整构建，结果为：

```text
Build completed successfully (3266 jobs).
数值交叉验证：通过
公理审计：通过
占位证明扫描：通过
编译产物跟踪检查：通过
```

本次新增通道步长误差提升接口、中心有限差分 $h^2$ fixture 和独立有理数复算；精确交叉验证
额外通过“两层有限层离散化误差交叉验证”、“通道响应离散化误差交叉验证”和“通道中心差分
h² 误差交叉验证”。新的 `LeanOEM` 和 `LeanOEMTests` 目标均已纳入构建。

此前历史记录中的临时 worktree 已删除；当前项目目录没有保留额外构建目录或后台进程。

## 当前工作区验证

验证日期：2026-11-02。

本轮在起始提交 `23c6473` 的未提交工作区上完成了以下检查：

```text
Build completed successfully (3270 jobs).
数值交叉验证：通过
公理审计：通过
占位证明扫描：通过
编译产物跟踪检查：通过
```

本轮新增 `LeanOEM.Core` 和 `LeanOEM.Physics` 聚合入口、前向模型/Jacobian 联合误差契约、
两通道两状态有限层模型及其精确有理数测试；独立 `Fraction` 脚本额外复算了前向/Jacobian
联合误差到一步更新误差底的 fixture。公理输出仍只有
`propext`、`Classical.choice` 和 `Quot.sound`。

本轮随后收紧入口边界：`LeanOEM` 只导出 `LeanOEM.Core`，`LeanOEM.Tests.CoreEntry` 在不导入
Physics 的情况下验证稳定核心，公理审计则显式分别导入 `LeanOEM.Core` 和 `LeanOEM.Physics`。
重新构建完成 3270 个目标，审计和独立精确数值验证均通过。

随后新增 DOFS 的显式矩阵序条件上下界、对应的一维最优增益合成例子，以及
`GaussianLineParameters.Valid` 线宽正性接口；这些增量目标已分别通过定向构建。

当前批次进一步新增 `LeanOEM.Core.SpectralDiagnostics`，用 Hermitian 谱分解建立半正定矩阵
乘积迹的非负性，并证明正定先验/观测误差下最优增益的 DOFS 总迹界。完整工作区构建完成
3366 个目标；新增公理审计目标仍只报告 `propext`、`Classical.choice` 和 `Quot.sound`。

最终代码收口提交：`365067d`。提交内容对应上述构建、公理审计、占位扫描和独立精确数值验证结果。

随后批次新增 `ContractsTowardAlongWithFloor` 的有限步误差底和稳态误差底定理，并加入有限层、
Gaussian、Doppler、Planck 和两层状态参数的非法合成反例；完整构建仍为 3366 个目标，公理审计
仍通过。当前代码提交为 `5554692`。

当前批次新增显式 Hermitian averaging kernel 的逐特征值 `[0,1]` 界，以及通道空网格、负误差
常数、零步长和有限层参数边界反例；完整构建完成 3416 个目标，公理审计和独立精确数值验证均通过。

当前代码提交为 `3087b5a`。

## 先验白化与最优增益谱界

验证日期：2026-11-02。本批从本地提交 `edef89e` 开始，新增
`LeanOEM.Core.PriorWhitening`、Core-only 调用测试和独立合成测试。

```text
lake build：Build completed successfully (3418 jobs).
bash scripts/run_audit.sh --no-build：通过
先验白化、相似变换和精确特征对的 Fraction 交叉验证：通过
占位证明扫描与编译产物跟踪检查：通过
git diff --check：通过
```

本批 14 项新增构造与公开定理已全部执行 `#print axioms`，输出只依赖
`propext`、`Classical.choice` 和 `Quot.sound`。
相关先验、秩亏观测的二维测试明确验证原 averaging kernel 非 Hermitian，
白化矩阵对称、谱为 `{0, 2/3}`，DOFS 为 `2/3`；零 Jacobian 和空状态也已覆盖。
完整构建未留下本批新增警告。

上述构建复用当前锁定依赖和本地缓存，并非新建干净 checkout；当前候选代码的干净构建与
独立人工语义审阅仍在发布清单中保留为未完成项。本批没有修改依赖版本或创建远端发布。

代码审计基线：`856860f`。

当前批次补充 `Observable` 下的严格正特征值接口和白化矩阵的 Jacobian 秩上界。
重新构建完成 3418 个目标；公理审计覆盖新增定理，精确数值复算和格式检查均通过。

本批继续补充白化 averaging kernel 的逐向量核等价和精确秩等式。重新构建仍完成 3418 个目标；
公理审计共输出 132 项，先验白化谱相关 20 项，均只依赖 `propext`、`Classical.choice` 和
`Quot.sound`。独立有理数复算、占位扫描与编译产物跟踪检查全部通过。

本批再补充零谱与 `¬ Observable` 的双向命题，以及按非零特征值集合收缩得到的
`DOFS ≤ rank(K)`。完整构建仍为 3418 个目标；公理审计输出 135 项，无额外公理，
独立数值复算和格式检查继续通过。

当前批次加入正定观测误差下的特征值严格小于 `1` 定理和非空状态空间的严格 DOFS 上界。
完整构建仍为 3418 个目标；公理审计输出 137 项，额外公理为零，独立数值复算和格式检查继续通过。

代码审计基线：`44c08be`。

代码审计基线：`d4d8531`。

代码审计基线：`f83b239`。

代码审计基线：`4ad0b02`。

## 奇异先验支持白化

验证日期：2026-11-03。本批代码提交：`6ff28c1`。

```text
lake build：Build completed successfully (3420 jobs).
bash scripts/run_audit.sh --no-build：通过
python3 scripts/validate_oem_numeric.py：通过
git diff --check：通过
```

本批新增 `LeanOEM.Core.SupportWhitening` 和对应的 Core-only 精确测试。`SupportFactor` 使用
满列秩矩形因子表示半正定先验，在支持坐标中复用单位先验的谱证明链；新增公理审计共 17 项，
全部只依赖 `propext`、`Classical.choice` 和 `Quot.sound`。Lean 精确例子和独立 `Fraction`
复算覆盖 `Sₐ = diag(1,0)`、支持内可观测、支持内不可观测、ambient 不可观测以及
`DOFS ≤ rank(Sₐ)` 边界。没有引入伪逆、外部工程依赖或自定义公理。

## Canonical support square root

验证日期：2026-11-04。本批代码提交：`4cc7343`。

```text
lake build：Build completed successfully (3420 jobs).
bash scripts/run_audit.sh --no-build：通过
python3 scripts/validate_oem_numeric.py：通过
git diff --check：通过
```

本批在 `SupportWhitening` 中增加 `PriorSqrtFactor.ofPosSemidef`、平方根因子对应的
`range` canonical support，以及 `support_finrank_eq_priorCovariance_rank`。新增 4 项公理审计，
仍只依赖 `propext`、`Classical.choice` 和 `Quot.sound`。矩形 `SupportFactor` 保持不变；
从 canonical support 选择有限坐标和构造满列秩矩形因子留在下一批。

## Canonical support 坐标小批次

验证日期：2026-11-05。当前工作区在未提交状态完成了支持坐标层的实现与验证：

```text
lake build LeanOEM：通过（2828 个目标）
lake build LeanOEMTests：通过（3421 个目标）
bash scripts/run_audit.sh --no-build：通过
python3 scripts/validate_oem_numeric.py：通过
git diff --check：通过
```

本批新增 `LeanOEM/Core/SupportCoordinates.lean` 和
`LeanOEM/Tests/SupportCoordinates.lean`。坐标层在 EuclideanSpace 表示中选择正交规范
基，再搬回既有 `State n` 表示；Lean 已检查列矩阵单射、列空间等于 canonical support、
矩阵秩与支持维数对应关系。公理审计覆盖新增公开定理，仍只有
`propext`、`Classical.choice` 和 `Quot.sound`。本批没有修改依赖、没有引入伪逆或自定义
公理，也没有创建远端发布。

## 自动矩形 SupportFactor 小批次

验证日期：2026-11-05。本批代码提交 `ac8df74` 完成自动矩形因子和合成测试：

```text
lake build LeanOEM：通过（2828 个目标）
lake build LeanOEMTests：通过（3421 个目标）
bash scripts/run_audit.sh --no-build：通过
python3 scripts/validate_oem_numeric.py：通过
git diff --check：通过
```

本批在 `SupportCoordinates` 中新增正交基 Gram 恒等式、平方根因子协方差恒等式、满列秩
证明、列空间等于 canonical support 的定理和 `Problem.PriorSqrtFactor.toSupportFactor` 自动
构造。`diag(1,0)` 合成测试直接检查自动因子的协方差、满列秩、列空间和秩值。新增公理审计仍只依赖
`propext`、`Classical.choice` 和 `Quot.sound`；没有引入伪逆、外部工程依赖或自定义公理。

## Ambient/support 特征多项式关系小批次

验证日期：2026-11-07。本批代码提交 `ab5881f` 完成 ambient/support 特征多项式关系：

```text
lake build LeanOEM：通过（2828 个目标）
lake build LeanOEMTests：通过（3421 个目标）
bash scripts/run_audit.sh --no-build：通过
python3 scripts/validate_oem_numeric.py：通过
git diff --check：通过
```

本批新增 `Problem.SupportFactor.averagingKernel_charpoly_eq_support_factor`。证明使用
`A = XY`、`Bₛ = YX` 和 Mathlib 矩形特征多项式恒等式，得到
`χ_A = X^(n-r) χ_{Bₛ}`；合成测试覆盖自动 `diag(1,0)` 支持因子。公理审计仍只有
`propext`、`Classical.choice` 和 `Quot.sound`。
