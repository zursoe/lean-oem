# Lean OEM 后续路线

本文档记录线性 OEM 核心之后的开发顺序、形式化边界和发布门槛。它以锁定的 Lean/Mathlib 版本、远端仓库状态和辐射计项目的数学需求为依据；代码实现完成后应同步更新本文件。

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

后续扩展遵循“理论和算法独立于 ARTS，实现和数据作为外部证据”的方向：

1. `LeanOEM` 保持通用 OEM、协方差和可观测性核心，不依赖 ARTS、Python、谱线数据库或科研数据。
2. 辐射传输理论和离散算法在独立的 Lean 模块中定义，先证明模型性质、导数关系和误差条件，再讨论具体实现。
3. ARTS 是一个重要的数值实现和参考生成器，但不是 Lean 的代码依赖。ARTS/Python 通过固定版本、配置、fixture 和误差报告与形式模型建立符合性关系。
4. 每个结果继续区分形式定义、形式假设、形式定理、数值证据和现实观测证据；证明形式模型成立不等于证明 ARTS 数据库或真实大气正确。

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

ARTS、Python、单位系统、传感器响应、非线性 Jacobian、概率测度和有限精度误差模型继续留在独立模块或 `lean-atmo-lab`。后续会先在 ARTS 无关的数学模型中定义其中可复用的部分，再用 ARTS 场景和数值运行建立外部符合性证据。

## 阶段 P6：数值交叉验证和来源映射

本批次已完成：新增 `scripts/validate_oem_numeric.py`，用独立的 `Fraction` 矩阵运算核对一维和秩亏二维公式；新增 `docs/source-mapping.md`，记录 Lean 定义、形式假设、形式定理、数值证据和 Rodgers 文献来源之间的边界；`run_audit.sh` 已将数值交叉验证纳入审计流程。

数值脚本只复算固定精确例子，不把浮点近似、ARTS 输出或单位约定写成 Lean 定理。Python/ARTS 的工程桥接需要单独记录输入版本、单位、误差和运行证据。

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

第一批已完成：在不依赖 ARTS 的前提下，建立了 OEM 所需的正演对象和 Jacobian 关系契约。

- `LeanOEM/Core/ForwardModel.lean` 定义 `ForwardModel`、`HasJacobianAt`、`JacobianSpec`、
  `matrixDerivative`、锚点线性化、余项和 `Problem.predict` 连接；
- `LeanOEM/Tests/ForwardModel.lean` 用标量平方模型证明非线性 Jacobian，并证明锚点余项是二阶项；
- `LeanOEM/Tests/Axioms.lean` 已纳入新公开定理的公理记录。

- 定义 ARTS 无关的 `ForwardModel` 抽象：状态到观测的函数 `F`，并记录观测维度、状态维度和上下文参数；
- 定义 Jacobian 规格 `K(x)`，明确它是 `F` 的导数、导数的矩阵表示，还是独立给出的近似；
- 形式化锚点线性化 `F(x) = F(xₐ) + K(xₐ)(x-xₐ) + r(x)` 的余项接口；
- 证明线性化模型与现有 `Problem`/OEM 核心的连接，保持 `K : m × n` 的方向契约；
- 低维实数例子已经完成；简单多层模型、辐射传输和有限差分误差留在 P10/P12，不在本批次引入 ARTS、单位数据库或浮点误差。

验收标准已达到：抽象接口可以被 OEM 核心调用；至少一个非线性函数有可检查的导数/Jacobian
例子；线性化余项以精确定义保存。余项的范数界和适用条件属于 P12。

## 阶段 P10：最小辐射传输理论模型

当前批次已完成：在独立于 ARTS 的数学模块中实现了归一化有限层、无散射模型，以及 Planck、Doppler 和有限通道响应的基本性质。

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

当前核心是线性 OEM，而辐射计项目实际使用的是逐轮重算正演和 Jacobian 的非线性 MAP 迭代。此阶段只先形式化算法规格和单步性质，不提前声称全局收敛。

- 定义非线性观测模型、残差、加权目标函数和 Gauss–Newton 更新；
- 证明在固定 `F`、`K`、先验和观测误差下，单步更新与线性 OEM 的关系；
- 定义迭代轨迹、停止条件和每轮使用的 Jacobian；
- 区分 Jacobian 刷新、冻结 Jacobian、初值和阻尼等算法配置；
- 在明确的局部正则性、可逆性和小余项条件下，再研究局部误差或收敛结论。

验收标准：不把“代码运行收敛”写成定理；每个收敛或误差结论都列出局部条件；与当前线性 `Problem` 的接口保持兼容。

## 阶段 P12：数值 Jacobian、离散化和误差契约

此阶段连接数学导数和实际计算方法，重点是误差边界而不是把浮点程序直接当作证明。

- 定义中心有限差分 Jacobian，并在光滑性假设下证明截断误差形式；
- 定义有限层递推、频率求积和通道离散化的误差参数；
- 研究 `F_h`、`K_h` 与理想模型 `F`、`K` 的关系；
- 记录矩阵范数、状态扰动范围和误差如何进入 OEM 更新或后验量；
- 对条件数、舍入误差和浮点实现保持外部数值证据边界，除非以后单独建立可信浮点模型。

验收标准：至少一个简化模型有有限差分误差界和独立数值验证；误差界的假设、范数和适用范围可读且可复现。

## 阶段 P13：ARTS/Python 符合性桥接

ARTS 在这一阶段作为实现和数据证据，不作为 Lean 包依赖。

- 设计机器可读 fixture：状态、配置、频率/通道、`F`、`K`、单位、版本和哈希；
- 用 Python 检查 ARTS 输出是否符合形式模型的维度、方向、范围和误差契约；
- 记录 ARTS 版本、谱线库、数值选项和输入来源；
- 将外部数值对照放入独立脚本或 `lean-atmo-lab`，不把科研数据和大型数据库提交到公开核心；
- 明确区分“Lean 证明参考模型性质”和“ARTS 运行结果符合参考模型的工程证据”。

验收标准：一个脱敏、可分发的小型 fixture 可以在干净环境中复核；桥接报告能指出哪些内容是形式定理、哪些内容是数值结果、哪些内容仍是物理假设。

## 阶段 P14：辐射计应用案例和发布收口

完成前述通用模块后，再选择一个来自太赫兹风场项目的最小案例接入：固定状态定义、观测通道、几何、单位和协方差，比较 ARTS、简化模型、代理模型和非线性 OEM 的结果。

- 先使用脱敏或合成 fixture，不把真实项目数据作为公开库依赖；
- 用完整非线性 OEM 作为工程基线，报告正演、Jacobian、迭代和回退成本；
- 检查观测残差、后验协方差、averaging kernel、DOFS 和状态误差是否满足预定契约；
- 把适用范围、失败案例和未证明内容写入来源映射与发布说明；
- 只有当模块拥有独立 API、非平凡定理、可复现 fixture 和完整审计后，才考虑拆出独立辐射传输公开库。

推荐顺序是 P9 → P10/P12 → P11 → P13 → P14。DOFS 谱理论作为并行但次优先的数学路线，等正演和非线性接口稳定后再推进。

SciLean 继续暂缓：其当前主分支工具链仍为 Lean `v4.28.0-rc1`，与本项目锁定的 Lean/Mathlib `v4.35.0` 不兼容。只有在兼容性、依赖责任和数值接口经过单独验证后，才重新评估是否引入。

## 发布门槛

在为线性核心打 `0.1.0` 标签，或把后续辐射传输模块提升为公开稳定模块前，需要满足相应门槛：

- API 名称、矩阵方向、逆矩阵语义和协方差假设已经冻结；
- 后验协方差至少有 Joseph 等价、半正定性和一个不确定性减少结果；
- 有精确矩阵示例、失败边界和可重复构建命令；
- 没有 `sorryAx`、`admit` 或未登记自定义公理；
- 每个公开核心定理都有 `#print axioms` 记录；
- README、范围文档和来源映射明确写出“已证明范围”和“尚未证明范围”；
- 干净 checkout 可以在锁定工具链和 `lake-manifest.json` 下完成构建。

下一次实际编码批次继续 P10/P12：增加简化谱线响应并开始有限差分/离散化误差契约；继续保持理论、算法、ARTS 实现和现实证据的边界。
