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
