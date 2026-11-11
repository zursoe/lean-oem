# 构建与复现记录

本文保留历次验证记录；最新结果见文末。工作区构建与干净 checkout 的验证方式分别说明。

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

## Ambient/support 非零谱接口小批次

验证日期：2026-11-07。本批代码提交 `52e36b1`：

```text
lake build LeanOEM LeanOEMTests：通过（3422 个目标）
bash scripts/run_audit.sh --no-build：通过
python3 scripts/validate_oem_numeric.py：通过
git diff --check：通过
```

本批新增 `nonzeroSpectrum`、ambient/support 非零谱集合相等、零根代数重数加法，以及
支持坐标可辨识时零根重数为 `n-r` 的定理。新增公开定理均已纳入 `LeanOEM/Tests/Axioms.lean`；
审计结果仍只有 `propext`、`Classical.choice` 和 `Quot.sound`。

## 纯 Lean 发布候选收口

验证日期：2026-11-11。本轮起点为 `9bb9f25`，数学实现基线仍为 `52e36b1`。

本轮统一项目目标、Core/Physics 发布范围和历史/当前验证状态，修正创新协方差记号与过期
待办，并补齐 22 个公开辅助定理及自动支持因子构造的公理登记。Lean 数学定义和证明项未改动。

首次候选 `9512730` 的本地工作区验证：

```text
lake build LeanOEM LeanOEMTests：通过（3422 个目标）
bash scripts/run_audit.sh --no-build：通过（含独立精确算术核对）
公理输出：195 项完整，依赖集合仅为 propext、Classical.choice、Quot.sound
公开定理显式审计覆盖：192/192
Core/根入口的 LeanOEM 导入闭包：通过，不包含 Physics 或测试模块
git diff --check：通过
README/docs 相对文件链接：通过
```

本地缓存日志保存在 `.lake/release-local-audit-fiu5vy64.log`，不进入源代码发布内容。
干净验证复用锁定依赖的 Git 对象和 Mathlib 下载缓存，重新检出依赖并重建项目产物。
首次失败和修正后结果分别记录如下。

首次干净验证固定到 `9512730`：重新检出全部 9 个锁定依赖，从本机已有 Mathlib 缓存解包
9030 项产物（另 1 项已有），`lake build LeanOEM LeanOEMTests` 完成 3422 个目标。
后续公理审计失败，直接诊断为缺少 `LeanOEM/Physics.olean`：测试根入口仅导入各个 Physics
子模块，没有让 Lake 构建聚合入口。既有本地缓存包含该入口，因而本地检查没有暴露缺口。

修正为在 `LeanOEMTests.lean` 显式导入 `LeanOEM.Physics`，并让审计脚本在 Lean 失败时显示
错误输出、保留退出码。失败分支回归检查证实脚本以退出码 1 停止，并显示缺失 Physics
模块的原始错误；之后恢复临时工作树中的脚本，首次失败记录保留。

### 修正后候选验证

最终受检提交：`ff3ca1dad57da9b3336f25a5af386266ebe7a2e5`。

在另一个干净 detached worktree 中执行以下流程：

1. 重新检出提交，并确认项目没有 `.lake/build`；
2. 使用本机 Git 对象缓存克隆 9 个依赖，逐一 checkout 到锁文件的精确提交；依赖也不携带构建目录；
3. 执行 `lake exe cache unpack`，从已有下载缓存恢复依赖产物，无新增网络下载；
4. 执行 `lake build LeanOEM LeanOEMTests`，重新生成项目及测试产物；
5. 执行 `bash scripts/run_audit.sh --no-build`，核对每项公理输出和允许集合，并检查工作树仍干净。

```text
修正后本地构建：通过（3423 个目标）
修正后干净构建：Build completed successfully (3423 jobs).
LeanOEM/Physics.olean：由测试构建正常生成
公理输出：195 项完整，依赖集合仅为 propext、Classical.choice、Quot.sound
独立精确算术核对：通过
占位证明扫描与编译产物跟踪检查：通过
git diff --check 与干净工作树检查：通过
```

修正后本地日志为 `.lake/release-local-fixed-audit.log`，干净验证日志为
`.lake/release-clean-ff3ca1d.log`。两个本轮临时 worktree 均已清理；日志留在忽略的本地
缓存目录，不进入公开源代码。

该验证使用依赖缓存，不能解释为不使用缓存从源码重编整个 Mathlib；LeanOEM 自身的产物
确实从空构建目录重新生成。后续仅更新审计结果和候选状态文档，不改变该受检提交的代码、
测试、脚本或依赖锁定内容。

本轮未同步远端，也没有创建 tag 或 Release。内部源码复核见
[候选审阅记录](../review/release-candidate-review.md)；独立人工语义审查仍待完成。

## 独立 AI 复核后的语义说明与边界回归

验证日期：2026-11-11。基础提交为 `88e65c57f6ee90c556cc75f27ecc6391b4f4ff34`，
受检对象是包含本批语义说明、五项回归、测试入口及公理登记修改的本地工作区。
验证在提交前的工作区完成，随后随本批语义修正归档；不将结果记到旧候选 `ff3ca1d` 名下。

四个 Core/Physics 修改文件去除注释和空行后与基线完全一致，数学定义、定理陈述和原证明项
没有改变。新增反例及采纳意见见 [独立 AI 复核收口](../review/independent-ai-review.md)。

首次构建在新增回归模块失败：具名公开定理引用了私有测试规格，部分类型及实例也只作
私有导入。修正为公开所需的测试规格及直接导入；这些声明位于测试命名空间，不进入
稳定 Core。首次失败日志保留，修正后重新执行完整目标构建。

```text
lake build LeanOEM LeanOEMTests：Build completed successfully (3425 jobs).
新增语义回归模块与测试聚合入口：通过，无新增警告
bash scripts/run_audit.sh --no-build：通过
独立精确有理数交叉验证：全部通过
公理输出：200/200 项完整、无重复、无缺失
Core/Physics：原有 195 项，覆盖 192 个显式公开定理及 3 个因子构造
语义边界回归：新增 5 项
公理依赖集合：propext、Classical.choice、Quot.sound
占位证明扫描与编译产物跟踪检查：通过
git diff --check、README/docs 相对文件链接与制表符检查：通过
```

本次复用固定的 Lean/Mathlib 依赖及本地缓存，没有新建干净 checkout，也未重新从源码构建
整个 Mathlib。旧候选的干净构建证据保留在前一节，本批工作区验证与其分开记录。

本地忽略日志分别为 `.lake/semantic-boundary-build.log`（首次失败）、
`.lake/semantic-boundary-build-fixed.log`（修正后构建）和
`.lake/semantic-boundary-audit.log`（最终审计）。这些日志不进入公开源代码。
验证完成后只更新结果文档；未推送远端，也未创建 tag 或 Release。

## 作者确认与候选远端 CI

验证日期：2026-11-11。作者在会话中回复“确认符合”，确认本版四项数学含义与范围，
记录见 [作者语义核对](../review/author-semantic-review.md)。该确认与独立人工逐项数学
审查分别登记，不代替尚未完成的审查记录。

将含确认文档的候选推送至 `release/0.1.0-candidate`：

- 受检完整提交：`7f8265f57576b85d59b300598ab33eed22b9011d`；
- 数学说明与回归提交：`7cf0e673dd971161ba67101454b520af14cfe5e7`；两者之间仅修改确认文档；
- 工作流：`Lean OEM CI`，事件为 `push`；
- [运行 43010549697](https://github.com/zursoe/lean-oem/actions/runs/43010549697)；
- 开始：2026-11-11 11:16:18 UTC，结束：11:19:13 UTC；
- 结果：`completed / success`，全部工作流步骤成功。

远端日志已逐项核对：Lean 为固定版本 `4.35.0`，完成 3425 个构建目标，仓库公理登记
200/200 项完整、无重复或缺失，依赖并集仅为 `propext`、`Classical.choice`、`Quot.sound`。
独立精确有理数复核、占位扫描及编译产物跟踪检查均通过。该运行使用 GitHub runner 与
Mathlib 缓存，结论不能表述为从源码重编整个 Mathlib。

本地忽略证据为 `.lake/candidate-ci-7f8265f-result.json`、
`.lake/candidate-ci-7f8265f.log` 和 `.lake/candidate-ci-7f8265f-watch.log`。
远端 `main` 未合并此候选，尚未创建 tag 或 GitHub Release。本次结果归档提交仅修改文档，
其源码、测试、依赖锁、脚本和工作流与受检候选一致。

## 0.1.0 正式发布

发布日期：2026-11-11。用户在会话中明确决定“确定把当前候选版正式定为 0.1.0”，
据此将候选及发布文档快进合并至远端 `main`，执行主线验证后创建附注标签并发布 Release。
独立人工逐项审查尚未登记完成，按发布检查保留后续维护事项，不改写为已经完成。

- 正式版本提交：`ab4b0b9d54c3a4a9873ac36acd5803b2dcdf4bd6`；
- 附注标签：`v0.1.0`，标签对象为 `692ef22b19b9d69dae9b6f70b844241fba917674`；
- [主线 CI 43015103436](https://github.com/zursoe/lean-oem/actions/runs/43015103436)：
  2026-11-11 11:49:22 至 11:52:18 UTC，`completed / success`；
- [标签 CI 43015815874](https://github.com/zursoe/lean-oem/actions/runs/43015815874)：
  同一版本提交，全部工作流步骤成功；
- [GitHub Release](https://github.com/zursoe/lean-oem/releases/tag/v0.1.0)：
  2026-11-11 11:55:22 UTC 正式发布，为 latest，非草稿、非预发布版本。

下载主线结果与日志，已核对 3425 个构建目标通过，200 项公理输出完整、无重复或缺失，
依赖并集仍仅为 `propext`、`Classical.choice`、`Quot.sound`；独立精确有理数核对、占位
扫描与编译产物跟踪检查通过。核对 GitHub API 中附注标签指向的提交与主线受检提交相同，
Release 正文与准备的版本说明一致。源码、测试、依赖、脚本及工作流仍与受检候选一致。

本地忽略证据：`.lake/release-main-ab4b0b9-result.json`、`.lake/release-main-ab4b0b9.log`、
`.lake/release-tag-v0.1.0-result.json`、`.lake/v0.1.0-tag-ref.json`、
`.lake/v0.1.0-tag-object.json`、`.lake/v0.1.0-release-result.json` 和
`.lake/v0.1.0-release-body.md`。结果归档仅修改文档，版本标签保持固定。
