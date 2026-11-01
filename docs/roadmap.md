# Lean OEM 后续路线

本文档记录纯 Lean OEM 数学库的开发顺序、形式化边界和发布门槛。它以锁定的 Lean/Mathlib 版本、当前 API 和可复现构建为依据；代码实现完成后应同步更新本文件。

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

本机包使用 Lean `v4.35.0`、Mathlib 输入版本 `v4.35.0`，锁定提交记录在 `lake-manifest.json`。有限维实数矩阵核心已经合并到远端 `main`，合并提交为 `1fd31f1`；`api/linear-core` 作为历史实现分支保留。

## 总体架构原则

后续扩展遵循“纯 Lean 数学、显式假设、合成例子、可复现构建”的方向：

1. `LeanOEM.Core` 保持通用 OEM、协方差、可观测性、非线性迭代和误差契约核心。
2. `LeanOEM.Physics` 只保存与外部工程无关的数学模型、形式定理和合成 fixture，不承诺具体工程实现。
3. 形式定义、形式假设、形式定理和数值交叉验证继续分开记录。
4. 外部工程和真实数据属于库外使用场景，不进入主线路线或发布门槛。

## 先冻结的设计决策

在加入后验协方差之前，先固定以下契约，避免以后为兼容性反复改名和改方向。

1. 保留 `Fin n → ℝ` 作为核心向量表示。它能直接使用 Mathlib 的 `Matrix.mulVec`，暂不换成 `EuclideanSpace` 或更高层的坐标无关类型。
2. 保留 `K : m × n`、`g : n × m` 的矩阵方向。所有文档和示例都沿用“Jacobian 行是观测、列是状态”的约定。
3. 原始 `Problem` 只保存数据，不内置正定性证明。先验可以半正定，观测误差协方差需要正定；这些属于可复用的显式假设。
4. 继续使用 Mathlib 的总函数矩阵逆。`A⁻¹` 在奇异时有总函数值，只有在 `PosDef` 或其他可逆性假设下才把它解释成通常逆。核心 API 需要提供两侧消去定理，避免每个后续证明重复处理 `IsUnit` 和行列式。
5. 已将字段名固定为 `observationErrorCovariance`，明确它表示观测误差协方差。
6. `conjTranspose` 留在内部矩阵公式中，以便复用 Mathlib 的合同变换定理；实数专用定理中再明确说明它等于转置。

## 阶段 P0：建立可审查的远端基线

本阶段已完成：建立 Git 仓库和 `origin`，固定 Lean/Mathlib 版本，提交 `lake-manifest.json`、范围文档、审计脚本和发布材料；`api/linear-core` 已推送并合并到远端 `main`。Mathlib 源码、`.lake` 缓存、科研数据和本机路径没有进入公开仓库。

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

已新增 `LeanOEM/Core/Covariance.lean`，其中定义标准公式和用于证明正定性的 Joseph 公式：

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

这些例子使用精确的 `ℝ` 矩阵和 Mathlib 证明；浮点数和 NumPy 结果不替代核心证明。

自动检查至少包括：

- 干净环境中的 `lake build`；
- 公开测试模块的编译；
- `#print axioms` 审计输出；
- 排除规则文件后的 `sorry`、`admit`、自定义 `axiom` 扫描；
- 检查 `.lake` 和本机缓存没有进入 Git。

## 阶段 P4：averaging kernel、DOFS 和静态可辨识性

本批次已完成第一层接口：新增 `dofs` 和 `Problem.dofs` 的 trace 定义、零增益与增益加法性质；新增 `Observable`、核为零刻画和正定权重下的加权正规矩阵定理；示例覆盖一维 DOFS、单位 Jacobian 和秩亏 Jacobian。DOFS 的 `0 ≤ A ≤ I` 矩阵序条件上下界已补齐；最优增益的谱结构仍未自动推导。

后验协方差完成后再扩展诊断量。

1. 将 `averagingKernel` 的最优增益特例固定为 `A = gK`，并添加 `dofs` 的定义 `Matrix.trace A`。
2. 先证明 trace 的代数性质和示例值，再以显式 `A` 与 `I - A` 半正定假设得到
   `0 ≤ DOFS ≤ n`；从最优增益、正定先验和观测误差条件自动推出这些矩阵序条件仍需谱理论和相似变换论证。
3. 定义静态可辨识性，例如 `Observable K := Function.Injective K.mulVec`，与“某个具体先验下的后验不确定性”分开。
4. 先证明 `Kᴴ * S * K` 在 `S` 正定且 `K` 满列秩时正定，再考虑矩阵秩的等价刻画。
5. `Matrix.rank`、谱分解、最优增益的 DOFS 上下界和信息形式属于独立模块，避免把复杂谱理论塞进最小 API。

## 阶段 P5：信息形式和纯数学扩展

本批次已完成信息形式的核心数学部分：新增信息矩阵及其正定性，使用 Mathlib 的 Woodbury 恒等式证明后验协方差等于信息矩阵的逆，并证明正定先验下的后验正定性和后验逆矩阵恒等式。

信息形式

$$
S_{post}^{-1}=S_a^{-1}+K^\mathsf{T}S_\varepsilon^{-1}K
$$

需要先验正定和更强的矩阵恒等式；本批次已经完成其形式化核心。它可以支持后验正定、协方差单调性、条件数讨论和数值实现核对，但不自动提供有限精度误差界。

单位系统、传感器响应、概率测度和有限精度误差模型不属于当前核心；后续只在有明确纯数学 API 和定理边界时单独评估。

## 阶段 P6：数值交叉验证和来源映射

本批次已完成：新增 `scripts/validate_oem_numeric.py`，用独立的 `Fraction` 矩阵运算核对一维和秩亏二维公式；新增 `docs/source-mapping.md`，记录 Lean 定义、形式假设、形式定理、数值证据和 Rodgers 文献来源之间的边界；`run_audit.sh` 已将数值交叉验证纳入审计流程。

数值脚本只复算固定精确例子，不把浮点近似或工程实现写成 Lean 定理。

## 阶段 P7：公开发布前收口

本批次已完成：新增 `docs/release-notes.md`、`docs/release-checklist.md`、`docs/review/linear-core-review.md` 和 `docs/audit/axioms.md`，集中记录候选版本、验证命令、公理审计结果、审查问题和明确不包含的内容；核心已经合并到远端 `main`。

## 阶段 P8：CI 和远端审查

当前状态：线性核心已完成本地审计、远端审查和 `main` 合并；固定 action 提交的 `.github/workflows/ci.yml` 已在 push、PR 和合并后的 `main` 运行通过。

后续按以下顺序推进：

1. **已完成**：新增 GitHub Actions 工作流，在 `push`、`pull_request` 和手动触发时运行构建、审计和精确数值校验；
2. **已完成**：使用 `leanprover/lean-action` 的 Mathlib 缓存和 axiom audit，并将 `actions/checkout` 与 `leanprover/lean-action` 固定到已核对的完整提交；
3. **已完成**：在本地重新运行工作流等价命令，确认脚本不依赖 WSL 私有路径、代理、缓存或登录态；
4. **已完成**：已将 `api/linear-core` 推送为远端审查分支并建立、合并 [PR #1](https://github.com/zursoe/lean-oem/pull/1)；
5. API 名称、矩阵方向和假设边界已形成第一版稳定契约；`0.1.0` 标签等候后续模块边界和发布材料再次收口。

这一阶段的验收标准已达到：干净 GitHub runner 可以完成构建和审计；远端 `main` 可复现；没有把 `.lake`、Mathlib 源码、科研数据或凭据提交到仓库。

## 阶段 P9：通用正演模型和 Jacobian 契约

第一批已完成：在抽象数学模型的前提下，建立了 OEM 所需的正演对象和 Jacobian 关系契约。

- `LeanOEM/Core/ForwardModel.lean` 定义 `ForwardModel`、`HasJacobianAt`、`JacobianSpec`、
  `matrixDerivative`、锚点线性化、余项和 `Problem.predict` 连接；
- `LeanOEM/Tests/ForwardModel.lean` 用标量平方模型证明非线性 Jacobian，并证明锚点余项是二阶项；
- `LeanOEM/Tests/Axioms.lean` 已纳入新公开定理的公理记录。

- 定义与外部工程无关的 `ForwardModel` 抽象：状态到观测的函数 `F`，并记录观测维度、状态维度和上下文参数；
- 定义 Jacobian 规格 `K(x)`，明确它是 `F` 的导数、导数的矩阵表示，还是独立给出的近似；
- 形式化锚点线性化 `F(x) = F(xₐ) + K(xₐ)(x-xₐ) + r(x)` 的余项接口；
- 证明线性化模型与现有 `Problem`/OEM 核心的连接，保持 `K : m × n` 的方向契约；
- 低维实数例子已经完成；简单多层模型、辐射传输和有限差分误差留在 P10/P12，不在本批次引入单位数据库或浮点误差。

验收标准已达到：抽象接口可以被 OEM 核心调用；至少一个非线性函数有可检查的导数/Jacobian
例子；线性化余项以精确定义保存。余项的范数界和适用条件属于 P12。

## 阶段 P10：最小辐射传输理论模型

当前批次已完成：在独立的数学模块中实现了归一化有限层、无散射模型，以及 Planck、Doppler 和有限通道响应的基本性质。

- `LeanOEM/Physics/FiniteLayer.lean` 定义 `Layer`、有效层假设、单层递推、有限层传播和两层组合；
- `LeanOEM/Tests/FiniteLayer.lean` 覆盖精确数值、非负性、上界和两层传播；
- `LeanOEM/Physics/Spectral.lean` 定义 `planckRadiance`、`dopplerShift` 和 `ChannelResponse`；
- `LeanOEM/Tests/Spectral.lean` 覆盖正性、零速度、Doppler 正性、通道加权和边界性质；
- `LeanOEM/Tests/Axioms.lean` 已纳入有限层公开定理的公理记录。

- 有限层辐射传输递推和边界条件；
- 透过率、发射项和辐亮度的非负性及范围性质；
- Planck 函数、Doppler 频移和简化谱线响应；
- 通道响应、双边带合成和观测量变换；
- 对温度、吸收系数和风扰动的导数，以及 Jacobian 的链式组合。

当前批次使用归一化量；真实单位系统另立模块，避免把单位转换混入基础证明。

当前批次验收已达到：有限层递推、Planck 正性、Doppler 基本代数/正性和通道响应范围性质均有形式定理与测试。简化谱线响应、失败边界和离散误差继续作为 P10/P12 后续批次。

## 阶段 P11：非线性 Gauss–Newton OEM 规格

第一批已完成：定义了非线性 MAP 目标、残差、正规矩阵、右端项和 Gauss–Newton 单步，并证明可逆正规矩阵下的正规方程；没有声称全局收敛。

- `LeanOEM/Core/NonlinearOEM.lean` 定义 `NonlinearProblem`、目标函数、正规方程和单步更新；
- `LeanOEM/Tests/NonlinearOEM.lean` 覆盖标量平方模型、正规矩阵、正规方程和线性信息形式连接；
- `LeanOEM/Tests/Axioms.lean` 已纳入新公开定理的公理记录。

- 定义非线性观测模型、残差、加权目标函数和 Gauss–Newton 更新；
- 证明在固定 `F`、`K`、先验和观测误差下，单步更新与线性 OEM 的关系；
- 定义迭代轨迹、停止条件和每轮使用的 Jacobian；
- 区分 Jacobian 刷新、冻结 Jacobian、初值和阻尼等算法配置；
- 在明确的局部正则性、可逆性和小余项条件下，再研究局部误差或收敛结论。

第一批已实现正规方程与线性信息形式连接。第二批的实现位于 `LeanOEM/Core/Iteration.lean`：

- 精确实数轨迹支持按步、按当前状态选择 Jacobian，可表达刷新与冻结；
- `StepSmall` / `StoppedAt` 检查非负绝对容差和最大绝对分量范数，返回尚未施加增量的当前状态；
- `ContractsTowardAlong` 显式要求沿轨迹误差收缩，推出几何误差界和 `0 ≤ q < 1` 下的收敛；
- 集合不变性、共同不动点及集合内 Lipschitz 界提供局部条件入口；
- 已有停止误差界 `tolerance / (1-q)` 和正容差最终满足停止条件的定理；
- 测试覆盖线性一步解、刷新/冻结轨迹差异、负容差、空状态，以及真实导数和可逆正规矩阵下零步长却非最优的反例。

第三批补充了 `quadraticGradient` / `quadraticForm_add` 的二次型一阶项和显式二阶余项，
并用 `quadraticSubproblem_add` 描述对称正规矩阵子问题的增量；同时用
`residual_hasFDerivAt_of_hasJacobianAt` 把 ForwardModel 的 Jacobian 导数传到残差。
第四批补充了 `normalDefect`、`gaussNewtonUpdate_sub_target_eq_inverse_normalDefect` 和
`gaussNewtonUpdate_error_le_of_inverse_and_defect`：在显式逆作用界 `γ` 与缺陷界 `η` 下，
单步误差收缩因子为 `γ·η`。当前仍未从具体模型的 Jacobian、线性化余项和权重条件自动推出
这些界。

第五批新增 `LeanOEM/Core/LocalContraction.lean`，完成了第一条可实例化的局部收缩桥接：

- `ForwardModel.QuadraticRemainderBound` 显式记录二次线性化余项界；
- `WeightedJacobianActionBound` 记录观测权重与 Jacobian 的组合算子界；
- `normalDefect_eq_weighted_linearizationRemainder` 在无噪声且先验均值等于目标状态的条件下，
  将正规方程缺陷化为加权 Jacobian 作用在线性化余项上；
- `normalDefectBound_of_quadraticRemainder` 将余项界转成 `η = β·ρ·r` 的相对缺陷界；
- `contractsTowardAlong_of_inverse_and_defect` 将逐步 `γ`、`η` 界自动组合成收缩契约。

`LeanOEM/Tests/LocalContraction.lean` 对标量平方模型完成了正规矩阵逆作用界、邻域不变性、
单步误差界和 `q = 1/2` 下的轨迹收敛证明。该例子是精确实数数学 fixture，不代表一般
辐射传输模型已经满足这些假设；`HasJacobianAt` 仍不被解释为自动提供二次余项界。

随后又补充了一般非线性 MAP 驻点接口：`TargetStationary`、Jacobian 变化作用界、
驻点下的正规缺陷分解，以及 `η = δ·σ + β·ρ·r` 的缺陷界。测试覆盖目标残差非零、
先验均值不等于目标状态的标量平方模型。P11 当前完成了从特殊无噪声模型到一般驻点模型的
局部收缩契约；阻尼、首次停止与最大步数求解器、浮点误差仍未实现。

## 阶段 P12：数值 Jacobian、离散化和误差契约

此阶段连接数学导数和实际计算方法，重点是误差边界而不是把浮点程序直接当作证明。

- 定义中心有限差分 Jacobian，并在光滑性假设下证明截断误差形式；
- 定义有限层递推、频率求积和通道离散化的误差参数；
- 研究 `F_h`、`K_h` 与理想模型 `F`、`K` 的关系；
- 记录矩阵范数、状态扰动范围和误差如何进入 OEM 更新或后验量；
- 对条件数、舍入误差和浮点实现保持外部数值证据边界，除非以后单独建立可信浮点模型。

P12 第一批已完成：

- `LeanOEM/Core/DiscretizationError.lean` 定义 `WeightedJacobianErrorBound`；
- 证明离散化误差把加权 Jacobian 作用常数从 `β` 增加到 `β + ε`；
- 证明目标 Jacobian 误差在目标残差为 `σ` 时产生不超过 `ε·σ` 的正规方程残差；
- 证明该残差以加性项进入正规缺陷和 Gauss–Newton 更新误差界；
- 用三次函数中心差分 fixture 独立验证 `h²` Jacobian 误差和 `1/1000` 的正规方程残差界。

本批仍未把有限层、频率求积或通道响应的具体离散实现自动转换为这些契约；这些属于 P12
后续批次。

验收标准：至少一个简化模型有有限差分误差界和独立数值验证；误差界的假设、范数和适用范围可读且可复现。

P12 第二批已完成第一条具体有限层垂直切片：

- `LeanOEM/Physics/FiniteLayerDiscretization.lean` 定义两层共同源项正演模型、显式 Jacobian
  和透过率乘积误差界；
- `twoLayerSource_hasJacobianAt` 证明该有限层模型的 Jacobian 是正演函数的导数表示；
- 逐层透过率误差被传播为整体 Jacobian 系数误差，再提升为单位观测权重下的
  `WeightedJacobianErrorBound`；
- 有界入射辐亮度和状态下，正演误差也有显式上界；
- `LeanOEM/Tests/FiniteLayerDiscretization.lean` 验证有限层正演、Jacobian、正规方程残差和
  Gauss–Newton 更新误差底；`scripts/validate_oem_numeric.py` 用独立有理数复算同一 fixture。

该切片只把共同源项作为一维状态，透过率作为固定模型参数。它验证的是离散误差传播链，
不等同于温度、吸收系数或风速已经完成物理参数化。

P12-C 第一批已完成有限通道响应组合切片：

- `LeanOEM/Physics/ChannelDiscretization.lean` 定义通道权重 `L¹` 误差、逐点谱值误差和组合误差界；
- `channelJacobian` 将有限频率灵敏度加权为一行标量 Jacobian，并可提升为单位观测权重下的
  `WeightedJacobianErrorBound`；
- `LeanOEM/Tests/ChannelDiscretization.lean` 使用两个频率样本组合两层有限层输出和 Jacobian
  灵敏度，验证观测输出误差和通道 Jacobian 误差；独立 `Fraction` 复算同步覆盖该 fixture。

当前结果把离散权重和谱值误差作为显式契约，尚未从连续积分、网格步长或具体梯形/Simpson
规则自动推出误差阶数。步长误差的传播接口在 P12-C-2 第一批中补齐，阻尼和正则化的
非线性 Gauss–Newton 规格仍在后续。

P12-C-2 第一批已完成步长误差提升接口：

- `ChannelResponse.ValueStepErrorBound` 记录逐点的 $C h^p$ 误差；
- `apply_error_le_of_valueStepError` 将该误差提升为通道输出的同阶界；
- `channelJacobian_coefficient_error_le_of_valueStepError` 和
  `channelJacobian_weightedErrorBound_of_valueStepError` 将该界提升到通道 Jacobian 和 OEM
  Jacobian 误差契约；
- 测试用中心有限差分的 $h^2$ 定理实例化两频率通道灵敏度误差，并由独立有理数脚本复算。

这一批只传播已经给定的点态 $C h^p$ 界，没有从连续积分或网格结构自动生成该界。

## 阶段 P12-C-3：前向模型和 Jacobian 联合误差

当前批次已完成第一条联合误差链：

- `NonlinearProblem.residualFor`、`normalRhsFor` 和 `withModel` 支持在相同观测、先验和
  权重规格下比较两个正演模型；
- `ForwardModelErrorBound` 记录状态处的前向输出误差；
- `normalRhsFor_difference_eq` 给出前向误差和 Jacobian 误差进入正规右端的精确恒等式；
- `normalRhsFor_difference_norm_le_of_forward_and_jacobian_error` 给出

  $$
  \|b_h-b\|\leq\varepsilon_K\sigma+\beta_h\varepsilon_F;
  $$

- `normalRhsFor_norm_le_of_forward_and_jacobian_error` 将精确目标驻点条件下的正规右端
  误差写成显式误差底；
- `gaussNewtonUpdate_error_le_of_forward_and_jacobian_error` 在近似正规矩阵的逆作用界下
  将该误差传到同一目标处的一步更新。

该批次的测试使用标量三次模型和两个误差来源；它不声称全局迭代收敛，也不包含浮点误差。

## 阶段 P12-C-4：两层两状态垂直切片

当前批次新增 `LeanOEM/Physics/TwoLayerState.lean`：每个通道包含两个独立层源项，
透过率和入射辐亮度是固定参数，输出是两通道状态到观测的显式线性模型。已完成：

- 两通道两状态有限层正演和显式 Jacobian；
- `twoLayerState_hasJacobianAt` 导数契约；
- 精确有理数输出、Jacobian 和透过率扰动前向误差 fixture；
- `LeanOEM.Core` 与 `LeanOEM.Physics` 两个聚合入口。

源项仍是归一化数学变量。温度、光学厚度、谱线数据库和单位等物理参数化不属于本批次。

## 后续纯 Lean 工作包

P12-C-3 和 P12-C-4 已完成第一条前向模型/Jacobian 联合误差链以及两层两状态合成模型。
下一阶段继续围绕可复用数学 API 推进：

1. 完善 Physics 模块的参数有效性结构，例如正频率、正温度、正线宽和速度范围；Gaussian
   线宽参数包的正性约束已完成第一条切片；
2. 增加有限层、通道响应和离散化误差的合成反例；
3. 将 DOFS、可辨识性和秩亏方向连接到有限维模型；
4. 研究阻尼 Gauss–Newton、有限步停止和更一般的误差底契约；
5. 为稳定 Core 与实验 Physics 入口补充外部导入示例和 API 文档。

这些工作都保持在精确实数、显式假设和合成例子范围内，不把外部工程或真实数据作为验收内容。

## 发布门槛

在为线性核心打 `0.1.0` 标签，或把后续辐射传输模块提升为公开稳定模块前，需要满足相应门槛：

- API 名称、矩阵方向、逆矩阵语义和协方差假设已经冻结；
- 后验协方差至少有 Joseph 等价、半正定性和一个不确定性减少结果；
- 有精确矩阵示例、失败边界和可重复构建命令；
- 没有 `sorryAx`、`admit` 或未登记自定义公理；
- 每个公开核心定理都有 `#print axioms` 记录；
- README、范围文档和来源映射明确写出“已证明范围”和“尚未证明范围”；
- 干净 checkout 可以在锁定工具链和 `lake-manifest.json` 下完成构建。

下一次实际编码批次继续完善纯 Lean 数学 API：先补 Physics 参数有效性、合成反例和
DOFS/可辨识性定理，再考虑阻尼和有限步停止契约。
