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

验证提交：`061ac50`。

本次在当前锁定依赖和工作区执行完整构建，结果为：

```text
Build completed successfully (3264 jobs).
数值交叉验证：通过
公理审计：通过
占位证明扫描：通过
编译产物跟踪检查：通过
```

本次新增两层有限层正演/Jacobian 离散化误差切片和独立有理数 fixture；精确交叉验证额外通过
“两层有限层离散化误差交叉验证”。新的 `LeanOEM` 和 `LeanOEMTests` 目标均已纳入构建。

此前历史记录中的临时 worktree 已删除；当前项目目录没有保留额外构建目录或后台进程。
