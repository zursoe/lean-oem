module

public import LeanOEM.Core.ForwardModel
public import LeanOEM.Core.Information
public import LeanOEM.Core.Observability
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Analysis.Calculus.FDeriv.Add

@[expose] public section

namespace LeanOEM

noncomputable section

/-- 非线性 OEM 的观测、先验和权重规格。

`observationWeight` 与 `priorWeight` 表示误差协方差的逆或其他显式权重；
本结构允许任意矩阵，不自动声称它们来自正定协方差。正规方程的梯度解释要求
两个权重对称；把候选 Jacobian 用于原目标的一阶条件还要求 `HasJacobianAt`。
-/
structure NonlinearProblem (n m : ℕ) where
  model : ForwardModel n m
  observation : Observation m
  priorMean : State n
  priorWeight : Square n
  observationWeight : Square m

/-- 两个权重均正定的假设；实数上的 `PosDef` 同时保证对称性。 -/
structure WeightWellPosed (p : NonlinearProblem n m) : Prop where
  prior_posDef : p.priorWeight.PosDef
  observation_posDef : p.observationWeight.PosDef

namespace NonlinearProblem

/-- 非线性观测残差。 -/
def residual (p : NonlinearProblem n m) (x : State n) : Observation m :=
  p.observation - p.model.observe x

/-- 用指定正演模型计算残差，供比较精确模型和近似模型的误差契约使用。 -/
def residualFor (p : NonlinearProblem n m) (model : ForwardModel n m)
    (x : State n) : Observation m :=
  p.observation - model.observe x

@[simp] theorem residualFor_model (p : NonlinearProblem n m) (x : State n) :
    p.residualFor p.model x = p.residual x := rfl

/-- 将同一观测、先验和权重规格换成另一个正演模型。 -/
def withModel (p : NonlinearProblem n m) (model : ForwardModel n m) :
    NonlinearProblem n m :=
  { p with model := model }

/-- Jacobian 契约沿残差映射传播：残差导数是负的观测 Jacobian。 -/
theorem residual_hasFDerivAt_of_hasJacobianAt
    (p : NonlinearProblem n m) (x : State n) (k : Jacobian n m)
    (hJacobian : p.model.HasJacobianAt x k) :
    ∃ derivative : State n →L[ℝ] Observation m,
      HasFDerivAt (fun z => p.residual z) derivative x ∧
        ∀ h, derivative h = -(k.mulVec h) := by
  rcases hJacobian with ⟨derivative, hDerivative, hMatrix⟩
  refine ⟨-derivative, ?_, ?_⟩
  · simpa [residual] using hDerivative.const_sub p.observation
  · intro h
    simp [hMatrix]

/-- 矩阵权重下的二次型。 -/
def quadraticForm {n : ℕ} (weight : Square n) (v : State n) : ℝ :=
  dotProduct v (weight.mulVec v)

/-- 二次型的一阶系数：实数矩阵情形使用 `W + Wᵀ`。 -/
def quadraticGradient {n : ℕ} (weight : Square n) (v : State n) : State n :=
  (weight + weight.transpose).mulVec v

/-- 二次型的精确展开，末项是二阶余项。 -/
theorem quadraticForm_add {n : ℕ} (weight : Square n) (v h : State n) :
    quadraticForm weight (v + h) =
      quadraticForm weight v + dotProduct h (quadraticGradient weight v)
        + quadraticForm weight h := by
  unfold quadraticForm quadraticGradient
  rw [Matrix.mulVec_add]
  simp only [add_dotProduct, dotProduct_add]
  have hcross : dotProduct v (weight.mulVec h) =
      dotProduct h (weight.transpose.mulVec v) := by
    simpa using (Matrix.dotProduct_transpose_mulVec weight.transpose v h)
  rw [hcross]
  rw [Matrix.add_mulVec]
  rw [dotProduct_add]
  ring

/-- 线性化二次子问题：正规矩阵 `H`、右端项 `b` 和增量 `d`。 -/
def quadraticSubproblem {n : ℕ} (H : Square n) (b d : State n) : ℝ :=
  (1 / 2 : ℝ) * quadraticForm H d - dotProduct b d

/-- 对称正规矩阵下二次子问题的增量展开。 -/
theorem quadraticSubproblem_add {n : ℕ} (H : Square n) (b d h : State n)
    (hSymmetric : H.transpose = H) :
    quadraticSubproblem H b (d + h) - quadraticSubproblem H b d =
      dotProduct h (H.mulVec d - b) + (1 / 2 : ℝ) * quadraticForm H h := by
  unfold quadraticSubproblem
  rw [quadraticForm_add H d h]
  rw [dotProduct_add]
  simp [quadraticGradient, hSymmetric, Matrix.add_mulVec, dotProduct_add]
  rw [dotProduct_comm b h]
  ring

/-- 带两个矩阵权重的二次目标。

通常 OEM/MAP 二次目标的解释需另给权重条件；本定义不包含概率模型。 -/
def objective (p : NonlinearProblem n m) (x : State n) : ℝ :=
  (1 / 2 : ℝ) * quadraticForm p.observationWeight (p.residual x)
    + (1 / 2 : ℝ) * quadraticForm p.priorWeight (x - p.priorMean)

/-- 给定候选 Jacobian 的代数正规矩阵；对称权重下用于 Gauss–Newton 子问题。 -/
def normalMatrix (p : NonlinearProblem n m) (_x : State n)
    (k : Jacobian n m) : Square n :=
  k.conjTranspose * p.observationWeight * k + p.priorWeight

/-- 指定模型及候选 Jacobian 的代数正规右端；梯度解释需对称权重和真实导数。 -/
def normalRhsFor (p : NonlinearProblem n m) (model : ForwardModel n m) (x : State n)
    (k : Jacobian n m) : State n :=
  k.conjTranspose.mulVec (p.observationWeight.mulVec (p.residualFor model x))
    - p.priorWeight.mulVec (x - p.priorMean)

/-- 当前模型及候选 Jacobian 的代数正规右端。

只有权重对称且 `k` 满足当前模型的 `HasJacobianAt` 时，才将其解释为目标的负梯度。
这些解释条件不包含在本定义内。 -/
def normalRhs (p : NonlinearProblem n m) (x : State n)
    (k : Jacobian n m) : State n :=
  k.conjTranspose.mulVec (p.observationWeight.mulVec (p.residual x))
    - p.priorWeight.mulVec (x - p.priorMean)

theorem normalRhsFor_model (p : NonlinearProblem n m) (x : State n)
    (k : Jacobian n m) :
    p.normalRhsFor p.model x k = p.normalRhs x k := rfl

/-- 正定先验权重和正定观测权重给出的正规矩阵正定性。

带正定先验的 MAP 子问题即使 Jacobian 秩亏也有正定正规矩阵；观测可辨识性
是独立的诊断性质，不是该可解性结论的必要条件。 -/
theorem normalMatrix_posDef (p : NonlinearProblem n m) (x : State n)
    (k : Jacobian n m) (hWeights : WeightWellPosed p) :
    (p.normalMatrix x k).PosDef := by
  unfold normalMatrix
  simpa [add_comm] using hWeights.prior_posDef.add_posSemidef
    (Matrix.PosSemidef.conjTranspose_mul_mul_same
      hWeights.observation_posDef.posSemidef k)

/-- 正规矩阵正定性足以得到其总函数逆的可逆条件。 -/
theorem normalMatrix_isUnit (p : NonlinearProblem n m) (x : State n)
    (k : Jacobian n m) (hWeights : WeightWellPosed p) :
    IsUnit (p.normalMatrix x k) :=
  (p.normalMatrix_posDef x k hWeights).isUnit

/-- 兼容旧调用方式的辅助定理；可辨识性假设在这里不参与正规矩阵正定性证明。 -/
theorem normalMatrix_posDef_of_observable (p : NonlinearProblem n m) (x : State n)
    (k : Jacobian n m) (hWeights : WeightWellPosed p) (_hObservable : Observable k) :
    (p.normalMatrix x k).PosDef :=
  p.normalMatrix_posDef x k hWeights

theorem normalMatrix_isUnit_of_observable (p : NonlinearProblem n m) (x : State n)
    (k : Jacobian n m) (hWeights : WeightWellPosed p) (_hObservable : Observable k) :
    IsUnit (p.normalMatrix x k) :=
  p.normalMatrix_isUnit x k hWeights

/-- 线性化正规方程的代数残差；保留 `linearizedGradient` 名称以兼容既有调用。

对称权重下，它是线性化二次子问题在 `z` 处的梯度表达式。定义本身只记录
`H (z - x) - b`，不保证权重对称或候选 Jacobian 是原模型的真实导数。 -/
def linearizedGradient (p : NonlinearProblem n m) (x : State n)
    (k : Jacobian n m) (z : State n) : State n :=
  (p.normalMatrix x k).mulVec (z - x) - p.normalRhs x k

/-- 可逆正规矩阵条件下的 Gauss–Newton 状态增量。 -/
def gaussNewtonStep (p : NonlinearProblem n m) (x : State n)
    (k : Jacobian n m) : State n :=
  (p.normalMatrix x k)⁻¹.mulVec (p.normalRhs x k)

/-- 使用全步长增量的 Gauss–Newton 更新。 -/
def gaussNewtonUpdate (p : NonlinearProblem n m) (x : State n)
    (k : Jacobian n m) : State n :=
  x + p.gaussNewtonStep x k

theorem normalMatrix_mulVec_gaussNewtonStep
    (p : NonlinearProblem n m) (x : State n) (k : Jacobian n m)
    (hNormal : IsUnit (p.normalMatrix x k)) :
    (p.normalMatrix x k).mulVec (p.gaussNewtonStep x k) = p.normalRhs x k := by
  unfold gaussNewtonStep
  rw [Matrix.mulVec_mulVec]
  rw [Matrix.mul_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).mp hNormal), Matrix.one_mulVec]

/-- 可逆正规矩阵使更新点的代数正规残差为零；不单独断言原目标驻点。 -/
theorem gaussNewtonUpdate_linearizedGradient_eq_zero
    (p : NonlinearProblem n m) (x : State n) (k : Jacobian n m)
    (hNormal : IsUnit (p.normalMatrix x k)) :
    p.linearizedGradient x k (p.gaussNewtonUpdate x k) = 0 := by
  unfold linearizedGradient gaussNewtonUpdate
  rw [add_sub_cancel_left, p.normalMatrix_mulVec_gaussNewtonStep x k hNormal]
  simp

end NonlinearProblem

/-- 将线性 `Problem` 的协方差总函数逆映射为非线性规格的权重。

通常 OEM/MAP 的权重解释要求先验和观测误差协方差正定。奇异先验的总函数逆
不能保持零方差方向的约束；本映射不构造 `x = priorMean + L z` 的受支持约束问题，
也没有对任意先验承诺与线性估计器等价。 -/
def Problem.toNonlinear {n m : ℕ} (p : Problem n m) (y : Observation m) :
    NonlinearProblem n m :=
  { model := { observe := p.predict }
    observation := y
    priorMean := p.priorMean
    priorWeight := p.priorCovariance⁻¹
    observationWeight := p.observationErrorCovariance⁻¹ }

@[simp] theorem Problem.toNonlinear_residual_eq_innovation
    {n m : ℕ} (p : Problem n m) (y : Observation m) (x : State n) :
    (p.toNonlinear y).residual x = p.innovation x y := rfl

theorem Problem.toNonlinear_normalMatrix_eq_informationMatrix
    {n m : ℕ} (p : Problem n m) (y : Observation m) (x : State n) :
    (p.toNonlinear y).normalMatrix x p.jacobian = informationMatrix p := by
  simp [NonlinearProblem.normalMatrix, Problem.toNonlinear, informationMatrix, add_comm]

end
end LeanOEM
