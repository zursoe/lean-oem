# Lean OEM 后续路线

本文档记录第一阶段最小 API 之后的开发顺序、形式化边界和发布门槛。它以当前本机工作区、锁定的 Lean/Mathlib 版本和远端仓库状态为依据；代码实现完成后应同步更新本文件。

## 当前基线

当前工作区已经形成有限维、实数、矩阵表示的线性 OEM 核心：

- `State n` 和 `Observation m` 是 `Fin n → ℝ` 与 `Fin m → ℝ`；
- Jacobian 的形状是 `Matrix (Fin m) (Fin n) ℝ`，行对应观测，列对应状态；
- `Problem` 保存 Jacobian、先验均值、先验协方差和观测误差协方差；
- 已定义创新协方差、增益、线性估计器、averaging kernel 和确定性误差；
- 已证明半正定先验加正定观测误差得到正定创新协方差，并证明误差分解

  $$
  \hat{x}-x=(I-A)(x_a-x)+g\varepsilon.
  $$

当前验证结果：`lake build` 成功；核心定理的 `#print axioms` 只有
`propext`、`Classical.choice` 和 `Quot.sound`；源代码没有 `sorry`、`admit` 或自定义 `axiom`。

本机包使用 Lean `v4.35.0`、Mathlib 输入版本 `v4.35.0`，锁定提交记录在 `lake-manifest.json`。工作区已经接入远端 `zursoe/lean-oem`，当前开发分支是本地 `api/linear-core`；远端 `main` 仍只有初始提交，本地实现尚未推送到远端。

## 先冻结的设计决策

在加入后验协方差之前，先固定以下契约，避免以后为兼容性反复改名和改方向。

1. 保留 `Fin n → ℝ` 作为核心向量表示。它能直接使用 Mathlib 的 `Matrix.mulVec`，暂不换成 `EuclideanSpace` 或更高层的坐标无关类型。
2. 保留 `K : m × n`、`g : n × m` 的矩阵方向。所有文档和示例都沿用“Jacobian 行是观测、列是状态”的约定。
3. 原始 `Problem` 只保存数据，不内置正定性证明。先验可以半正定，观测误差协方差需要正定；这些属于可复用的显式假设。
4. 继续使用 Mathlib 的总函数矩阵逆。`A⁻¹` 在奇异时有总函数值，只有在 `PosDef` 或其他可逆性假设下才把它解释成通常逆。核心 API 需要提供两侧消去定理，避免每个后续证明重复处理 `IsUnit` 和行列式。
5. 已将字段名固定为 `observationErrorCovariance`，明确它表示观测误差协方差。
6. `conjTranspose` 留在内部矩阵公式中，以便复用 Mathlib 的合同变换定理；实数专用定理中再明确说明它等于转置。

## 阶段 P0：建立可审查的远端基线

本批次已完成本地部分：工作区已建立 Git 仓库、配置 `origin`、取得远端 `main`，并创建 `api/linear-core` 分支。远端主线尚未修改。

先把本地代码放入远端仓库的本地分支，不立即推送或修改远端主线。建议流程是：取得远端 `main`，创建 `api/linear-core` 分支，把当前 Lean 包、`docs/scope.md` 和本路线纳入一次可复现提交，然后在干净目录重新构建。

这一阶段的交付物：

- 根 `README.md`：说明用途、范围、Lean/Mathlib 版本、构建命令和信任边界；
- `docs/scope.md` 与本文档互相链接；
- `.gitignore` 排除 `.lake`、编译产物、缓存和本机数据；
- 本地提交包含完整的 `lake-manifest.json`，但不包含 Mathlib 源码或编译缓存；
- 远端推送前保留一次人工审查点。

## 阶段 P1：稳定最小 API

本批次已完成：新增 `Problem.WellPosed`、预测和创新函数、创新协方差逆矩阵的正定性与两侧消去定理，以及最优增益规格定理。

这一阶段的目标是让后续定理能够使用统一假设和统一矩阵身份，当前批次已经达到这一目标。

已新增 `LeanOEM/Core/Assumptions.lean`，其中的命题结构为：

```lean
structure Problem.WellPosed {n m : ℕ} (p : Problem n m) : Prop where
  prior_posSemidef : p.priorCovariance.PosSemidef
  observation_posDef : p.observationErrorCovariance.PosDef
```

同时保留接受两个独立假设的低层定理，方便调用者只提供所需条件。应补齐以下辅助结果：

- `innovationCovariance_inv_posDef`；
- `innovationCovariance_mul_inv`；
- `innovationCovariance_inv_mul`；
- 增益与创新协方差相乘后恢复 `priorCovariance * jacobianᴴ` 的规格定理；
- 先验和创新协方差的 Hermitian 性质；
- `Problem.predict` 与 `Problem.innovation` 这类小型函数，减少估计器和误差定理中的重复表达式。

验收标准是：后续证明不再直接展开 `Matrix.isUnit_iff_isUnit_det`，且每一个把逆矩阵当作普通逆矩阵的定理都显式接收 `PosDef` 或 `WellPosed` 假设。

## 阶段 P2：后验协方差和 Joseph 形式

本批次已完成第一组核心结果：新增标准后验协方差和 Joseph 协方差，证明 Joseph 半正定性、两种表达式的等价、后验半正定性，以及先验减后验的合同变换和半正定性。

这是当前批次的主线，后续维护优先级仍高于 DOFS 和物理接口。已新增 `LeanOEM/Core/Covariance.lean`，其中定义标准公式和用于证明正定性的 Joseph 公式：

```lean
def posteriorCovariance (p : Problem n m) : Square n :=
  p.priorCovariance - p.priorCovariance * p.jacobianᴴ *
    p.innovationCovariance⁻¹ * p.jacobian * p.priorCovariance

def josephCovariance (p : Problem n m) (g : Matrix (Fin n) (Fin m) ℝ) : Square n :=
  (1 - g * p.jacobian) * p.priorCovariance *
      (1 - g * p.jacobian)ᴴ
    + g * p.observationErrorCovariance * gᴴ
```

定理顺序建议如下：

1. 对任意增益，Joseph 形式在先验半正定、观测误差协方差半正定时是半正定；
2. 在 `WellPosed` 假设下，标准后验公式等于最优增益的 Joseph 形式；
3. 后验协方差是半正定；
4. 先验减后验可以写成 `g * innovationCovariance * gᴴ`，从而得到不确定性减少的半正定结论；
5. 先验正定时再单独研究后验正定，不把这个更强结论混入半正定基本定理。

Joseph 恒等式应先抽象成一个小型非交换矩阵代数引理，再实例化到 `Problem`。这样可以把 `Matrix.mul_assoc`、逆矩阵两侧消去和 Hermitian 逆的细节集中在一个位置。Mathlib 已有 `PosSemidef.mul_mul_conjTranspose_same`、`PosSemidef.add`、`PosDef.inv`、`Matrix.mul_nonsing_inv` 和 `Matrix.nonsing_inv_mul`，不需要自建正定性体系。

## 阶段 P3：精确矩阵示例和自动审计

本批次已完成：新增 `LeanOEM/Tests/Examples.lean`，覆盖一维精确数值、`2 × 1` 秩亏观测、不可观测状态方向、后验未收缩分量，以及负定、零矩阵和非对称矩阵边界；新增 `scripts/run_audit.sh` 统一执行构建、公理输出、占位扫描和编译产物检查。

核心定理稳定后，新增独立的矩阵示例测试，而不是把数值例子混入定义模块。

- `1 × 1` 精确实数例子：验证创新协方差、增益、averaging kernel 和后验协方差的方向与数值；
- `2 × 1` 秩亏观测例子：展示某个状态方向没有被观测，并验证后验仍可半正定；
- 奇异先验例子：验证半正定假设允许零特征方向；
- 负定、非对称或奇异观测误差矩阵作为失败边界，确保测试不会把原始矩阵别名误认为自动满足协方差条件。

这些例子使用精确的 `ℝ` 矩阵和 Mathlib 证明；浮点数、NumPy 和 ARTS 交叉验证放在独立脚本或 `lean-atmo-lab`，不能替代核心证明。

自动检查至少包括：

- 干净环境中的 `lake build`；
- 公开测试模块的编译；
- `#print axioms` 审计输出；
- 排除规则文件后的 `sorry`、`admit`、自定义 `axiom` 扫描；
- 检查 `.lake` 和本机缓存没有进入 Git。

## 阶段 P4：averaging kernel、DOFS 和静态可辨识性

本批次已完成第一层接口：新增 `dofs` 和 `Problem.dofs` 的 trace 定义、零增益与增益加法性质；新增 `Observable`、核为零刻画和正定权重下的加权正规矩阵定理；示例覆盖一维 DOFS、单位 Jacobian 和秩亏 Jacobian。DOFS 上下界和谱理论仍未声明。

后验协方差完成后再扩展诊断量。

1. 将 `averagingKernel` 的最优增益特例固定为 `A = gK`，并添加 `dofs` 的定义 `Matrix.trace A`。
2. 先证明 trace 的代数性质和示例值，不立即声明 `0 ≤ DOFS ≤ n`。这个界需要明确的正定性、谱理论和相似变换论证。
3. 定义静态可辨识性，例如 `Observable K := Function.Injective K.mulVec`，与“某个具体先验下的后验不确定性”分开。
4. 先证明 `Kᴴ * S * K` 在 `S` 正定且 `K` 满列秩时正定，再考虑矩阵秩的等价刻画。
5. `Matrix.rank`、谱分解、DOFS 上下界和信息形式属于独立模块，避免把复杂谱理论塞进最小 API。

## 阶段 P5：信息形式和科研工程桥接

本批次已完成信息形式的核心数学部分：新增信息矩阵及其正定性，使用 Mathlib 的 Woodbury 恒等式证明后验协方差等于信息矩阵的逆，并证明正定先验下的后验正定性和后验逆矩阵恒等式。单位、浮点误差、ARTS 运行结果和工程桥接仍未进入公开核心。

信息形式

$$
S_{post}^{-1}=S_a^{-1}+K^\mathsf{T}S_\varepsilon^{-1}K
$$

需要先验正定和更强的矩阵恒等式；本批次已经完成其形式化核心。它可以支持后验正定、协方差单调性、条件数讨论和数值实现核对，但不自动提供有限精度误差界。

ARTS、Python、单位系统、传感器响应、非线性 Jacobian、概率测度和有限精度误差模型继续留在独立模块或 `lean-atmo-lab`。公开核心只记录给定矩阵和显式假设下的形式结论，不把某个 ARTS 场景或某次数值运行提升为无条件定理。

## 阶段 P6：数值交叉验证和来源映射

本批次已完成：新增 `scripts/validate_oem_numeric.py`，用独立的 `Fraction` 矩阵运算核对一维和秩亏二维公式；新增 `docs/source-mapping.md`，记录 Lean 定义、形式假设、形式定理、数值证据和 Rodgers 文献来源之间的边界；`run_audit.sh` 已将数值交叉验证纳入审计流程。

数值脚本只复算固定精确例子，不把浮点近似、ARTS 输出或单位约定写成 Lean 定理。Python/ARTS 的工程桥接需要单独记录输入版本、单位、误差和运行证据。

## 阶段 P7：公开发布前收口

本批次已完成：新增 `docs/release-notes.md`、`docs/release-checklist.md`、`docs/review/linear-core-review.md` 和 `docs/audit/axioms.md`，集中记录候选版本、验证命令、公理审计结果、审查问题和明确不包含的内容。远端推送仍保留为维护者审查后的独立动作。

## 阶段 P8：CI 和远端审查

当前状态：本地 `api/linear-core` 已完成构建、公理、数值和干净 checkout 审计；已新增固定 action 提交的 `.github/workflows/ci.yml`，本地等价检查和远端 push/PR 两次 CI 均已通过；审查分支已推送，draft PR 已建立，远端 `main` 仍未修改。

后续按以下顺序推进：

1. **已完成**：新增 GitHub Actions 工作流，在 `push`、`pull_request` 和手动触发时运行构建、审计和精确数值校验；
2. **已完成**：使用 `leanprover/lean-action` 的 Mathlib 缓存和 axiom audit，并将 `actions/checkout` 与 `leanprover/lean-action` 固定到已核对的完整提交；
3. **已完成**：在本地重新运行工作流等价命令，确认脚本不依赖 WSL 私有路径、代理、缓存或登录态；
4. **已完成**：已将 `api/linear-core` 推送为远端审查分支并建立 [draft PR #1](https://github.com/zursoe/lean-oem/pull/1)；下一步等待维护者审阅 `docs/review/linear-core-review.md`；
5. 根据审查结果冻结 API 名称、矩阵方向和假设边界，再决定是否打 `0.1.0` 标签。

这一阶段的验收标准是：干净 GitHub runner 可以完成构建和审计；远端审查分支可复现；没有把 `.lake`、Mathlib 源码、科研数据或凭据提交到仓库。合并和打标签仍属于外部仓库写操作，保持为独立授权步骤。

## 阶段 P9：审查后的两条研发路线

远端审查通过后再在下面两条路线中择一作为主线：

- **谱理论路线**：在正定先验和正定观测误差条件下形式化 averaging kernel 的谱性质，最后再研究 `0 ≤ DOFS ≤ n`。需要使用 Mathlib 的 Hermitian、谱分解和矩阵序理论，先建立反例和边界条件。
- **工程桥接路线**：建立机器可读的精确 fixture 和独立 NumPy/Python 对照，记录单位、矩阵方向、误差模型和 ARTS 输入输出版本；桥接内容放入独立模块或 `lean-atmo-lab`，不改变核心定理的信任边界。

SciLean 继续暂缓：其当前主分支工具链仍为 Lean `v4.28.0-rc1`，与本项目锁定的 Lean/Mathlib `v4.35.0` 不兼容。只有在兼容性、依赖责任和数值接口经过单独验证后，才重新评估是否引入。

## 发布门槛

在把线性协方差模块提升为公开稳定主线前，需要同时满足：

- API 名称、矩阵方向、逆矩阵语义和协方差假设已经冻结；
- 后验协方差至少有 Joseph 等价、半正定性和一个不确定性减少结果；
- 有精确矩阵示例、失败边界和可重复构建命令；
- 没有 `sorryAx`、`admit` 或未登记自定义公理；
- 每个公开核心定理都有 `#print axioms` 记录；
- README、范围文档和来源映射明确写出“已证明范围”和“尚未证明范围”；
- 干净 checkout 可以在锁定工具链和 `lake-manifest.json` 下完成构建。

下一次实际编码批次进入 P8：先补 CI 工作流和远端审查准备；继续保持经验数据、单位系统和有限精度误差界的独立边界。
