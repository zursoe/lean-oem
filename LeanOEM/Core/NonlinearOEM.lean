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
本结构不自动声称它们来自正定协方差。
-/
structure NonlinearProblem (n m : ℕ) where
  model : ForwardModel n m
  observation : Observation m
  priorMean : State n
  priorWeight : Square n
  observationWeight : Square m

/-- 非线性 OEM 权重的正定性假设。 -/
structure WeightWellPosed (p : NonlinearProblem n m) : Prop where
  prior_posDef : p.priorWeight.PosDef
  observation_posDef : p.observationWeight.PosDef

namespace NonlinearProblem

/-- 非线性观测残差。 -/
def residual (p : NonlinearProblem n m) (x : State n) : Observation m :=
  p.observation - p.model.observe x

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

/-- 带先验约束的非线性 MAP 目标函数。 -/
def objective (p : NonlinearProblem n m) (x : State n) : ℝ :=
  (1 / 2 : ℝ) * quadraticForm p.observationWeight (p.residual x)
    + (1 / 2 : ℝ) * quadraticForm p.priorWeight (x - p.priorMean)

/-- 当前状态和 Jacobian 下的 Gauss–Newton 正规矩阵。 -/
def normalMatrix (p : NonlinearProblem n m) (_x : State n)
    (k : Jacobian n m) : Square n :=
  k.conjTranspose * p.observationWeight * k + p.priorWeight

/-- 当前状态和 Jacobian 下的 Gauss–Newton 右端项。 -/
def normalRhs (p : NonlinearProblem n m) (x : State n)
    (k : Jacobian n m) : State n :=
  k.conjTranspose.mulVec (p.observationWeight.mulVec (p.residual x))
    - p.priorWeight.mulVec (x - p.priorMean)

/-- 正定权重和可观测 Jacobian 给出的正规矩阵正定性。 -/
theorem normalMatrix_posDef (p : NonlinearProblem n m) (x : State n)
    (k : Jacobian n m) (hWeights : WeightWellPosed p) (hObservable : Observable k) :
    (p.normalMatrix x k).PosDef := by
  unfold normalMatrix
  exact Matrix.PosDef.add
    (weightedNormalMatrix_posDef k p.observationWeight
      hWeights.observation_posDef hObservable)
    hWeights.prior_posDef

/-- 正规矩阵正定性足以得到其总函数逆的可逆条件。 -/
theorem normalMatrix_isUnit (p : NonlinearProblem n m) (x : State n)
    (k : Jacobian n m) (hWeights : WeightWellPosed p) (hObservable : Observable k) :
    IsUnit (p.normalMatrix x k) :=
  (p.normalMatrix_posDef x k hWeights hObservable).isUnit

/-- 线性化子问题的正规梯度表达式；其零点就是 Gauss–Newton 正规方程。 -/
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

theorem gaussNewtonUpdate_linearizedGradient_eq_zero
    (p : NonlinearProblem n m) (x : State n) (k : Jacobian n m)
    (hNormal : IsUnit (p.normalMatrix x k)) :
    p.linearizedGradient x k (p.gaussNewtonUpdate x k) = 0 := by
  unfold linearizedGradient gaussNewtonUpdate
  rw [add_sub_cancel_left, p.normalMatrix_mulVec_gaussNewtonStep x k hNormal]
  simp

end NonlinearProblem

/-- 将线性 `Problem` 视为一个非线性规格的特例。 -/
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
