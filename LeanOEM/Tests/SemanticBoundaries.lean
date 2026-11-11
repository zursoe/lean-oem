module

public import LeanOEM.Core.LocalContraction
public import LeanOEM.Physics.TwoLayerState
public import LeanOEM.Physics.Spectral
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic

/-!
# 语义边界回归

反例分别隔离权重对称性、真实 Jacobian 和正定先验的解释条件。
它们使用公开定义，防止把代数正规方程、总函数逆或参数总函数误解为更强的规格。
-/

@[expose] public section

namespace LeanOEM.Tests.SemanticBoundaries

open LeanOEM LeanOEM.NonlinearProblem LeanOEM.RadiativeTransfer

noncomputable section

/-- 非对称观测权重的回归规格，仅供测试使用。 -/
def nonsymmetric : NonlinearProblem 2 2 where
  model := ⟨id⟩
  observation := ![1, 0]
  priorMean := 0
  priorWeight := 1
  observationWeight := !![1, 1; 0, 1]

private theorem nonsymmetric_hasJacobianAt (x : State 2) :
    nonsymmetric.model.HasJacobianAt x 1 := by
  refine ⟨ContinuousLinearMap.id ℝ (State 2), ?_, ?_⟩
  · simpa [nonsymmetric] using
      (ContinuousLinearMap.id ℝ (State 2)).hasFDerivAt (x := x)
  · intro h
    simp

private theorem nonsymmetric_normalRhs_zero :
    nonsymmetric.TargetStationary (![1/2, 0] : State 2) 1 := by
  unfold TargetStationary normalRhs NonlinearProblem.residual
  ext i
  fin_cases i <;>
    norm_num [nonsymmetric, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

private theorem nonsymmetric_objective_path (t : ℝ) :
    nonsymmetric.objective (![1/2, t] : State 2) = 1/4 - t/4 + t^2 := by
  norm_num [objective, quadraticForm, NonlinearProblem.residual, nonsymmetric,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

private theorem nonsymmetric_path_derivative :
    HasDerivAt (fun t : ℝ => nonsymmetric.objective (![1/2, t] : State 2))
      (-1/4) 0 := by
  simp_rw [nonsymmetric_objective_path]
  convert HasDerivAt.add
    (HasDerivAt.sub (hasDerivAt_const (0 : ℝ) (1/4 : ℝ))
      (HasDerivAt.div_const (hasDerivAt_id (0 : ℝ)) 4))
    (HasDerivAt.pow (hasDerivAt_id (0 : ℝ)) 2) using 1 <;> norm_num
  funext t
  rfl

/-- 即使 Jacobian 是真实导数，非对称权重下正规右端为零也不保证目标驻点或极小值。 -/
theorem nonsymmetric_stationarity_counterexample :
    nonsymmetric.model.HasJacobianAt (![1/2, 0] : State 2) 1 ∧
      nonsymmetric.TargetStationary (![1/2, 0] : State 2) 1 ∧
      HasDerivAt (fun t : ℝ => nonsymmetric.objective (![1/2, t] : State 2))
        (-1/4) 0 ∧
      nonsymmetric.objective (![1/2, 1/8] : State 2) <
        nonsymmetric.objective (![1/2, 0] : State 2) := by
  refine ⟨nonsymmetric_hasJacobianAt _, nonsymmetric_normalRhs_zero,
    nonsymmetric_path_derivative, ?_⟩
  rw [nonsymmetric_objective_path, nonsymmetric_objective_path]
  norm_num

/-- 权重正定、用于隔离错误候选 Jacobian 的回归规格。 -/
def wrongJacobian : NonlinearProblem 1 1 where
  model := ⟨id⟩
  observation := ![1]
  priorMean := 0
  priorWeight := 1
  observationWeight := 1

private theorem wrongJacobian_objective_path (t : ℝ) :
    wrongJacobian.objective (![t] : State 1) = 1/2 - t + t^2 := by
  norm_num [objective, quadraticForm, NonlinearProblem.residual, wrongJacobian,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

private theorem wrongJacobian_path_derivative :
    HasDerivAt (fun t : ℝ => wrongJacobian.objective (![t] : State 1)) (-1) 0 := by
  simp_rw [wrongJacobian_objective_path]
  convert HasDerivAt.add
    (HasDerivAt.sub (hasDerivAt_const (0 : ℝ) (1/2 : ℝ))
      (hasDerivAt_id (0 : ℝ)))
    (HasDerivAt.pow (hasDerivAt_id (0 : ℝ)) 2) using 1 <;> norm_num
  funext t
  rfl

/-- 正定权重不能替代真实导数条件：任意候选矩阵的正规零点仍可能不是目标驻点。 -/
theorem wrongJacobian_stationarity_counterexample :
    WeightWellPosed wrongJacobian ∧ wrongJacobian.TargetStationary 0 0 ∧
      HasDerivAt (fun t : ℝ => wrongJacobian.objective (![t] : State 1)) (-1) 0 := by
  refine ⟨⟨Matrix.PosDef.one, Matrix.PosDef.one⟩, ?_, wrongJacobian_path_derivative⟩
  simp [TargetStationary, normalRhs, wrongJacobian]

/-- 半正定奇异先验的回归规格，仅供测试使用。 -/
def singular : Problem 2 2 where
  jacobian := 1
  priorMean := 0
  priorCovariance := Matrix.diagonal ![1, 0]
  observationErrorCovariance := 1

private theorem singular_wellPosed : singular.WellPosed := by
  constructor
  · apply Matrix.PosSemidef.diagonal
    intro i
    fin_cases i <;> norm_num
  · exact Matrix.PosDef.one

private theorem singular_prior_inverse : singular.priorCovariance⁻¹ = 0 := by
  apply Matrix.nonsing_inv_apply_not_isUnit
  norm_num [singular, Matrix.det_fin_two]

private theorem singular_estimate : estimate singular (![0, 1] : Observation 2) = 0 := by
  have hS : singular.innovationCovariance = Matrix.diagonal (![2, 1] : State 2) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Problem.innovationCovariance, singular, Matrix.one_apply, Matrix.diagonal]
  unfold estimate estimateWithGain Problem.gain
  rw [hS, Matrix.inv_diagonal]
  ext i
  fin_cases i <;> norm_num [singular, Problem.innovation, Problem.predict,
    Matrix.mulVec, Matrix.mul_apply, Matrix.diagonal, Matrix.one_apply,
    dotProduct, Fin.sum_univ_succ, Ring.inverse]

private theorem singular_converted_normal :
    (singular.toNonlinear (![0, 1] : Observation 2)).normalMatrix 0 1 = 1 := by
  change (1 : Square 2).conjTranspose * (1 : Square 2)⁻¹ * 1 +
    singular.priorCovariance⁻¹ = 1
  rw [singular_prior_inverse]
  simp

private theorem singular_converted_update :
    (singular.toNonlinear (![0, 1] : Observation 2)).gaussNewtonUpdate 0 1 = ![0, 1] := by
  unfold gaussNewtonUpdate gaussNewtonStep
  rw [singular_converted_normal]
  simp [normalRhs, Problem.toNonlinear, NonlinearProblem.residual,
    singular, Problem.predict]

/-- 良定的奇异先验经总函数逆权重映射后，更新可以丢失原估计器的零方差方向约束。 -/
theorem singular_conversion_counterexample :
    singular.WellPosed ∧ singular.priorCovariance⁻¹ = 0 ∧
      IsUnit ((singular.toNonlinear (![0, 1] : Observation 2)).normalMatrix 0 1) ∧
      estimate singular (![0, 1] : Observation 2) = 0 ∧
      (singular.toNonlinear (![0, 1] : Observation 2)).gaussNewtonUpdate 0 1 = ![0, 1] ∧
      estimate singular (![0, 1] : Observation 2) ≠
        (singular.toNonlinear (![0, 1] : Observation 2)).gaussNewtonUpdate 0 1 := by
  refine ⟨singular_wellPosed, singular_prior_inverse, ?_,
    singular_estimate, singular_converted_update, ?_⟩
  · rw [singular_converted_normal]
    exact isUnit_one
  · rw [singular_estimate, singular_converted_update]
    intro h
    have hComponent := congrFun h (1 : Fin 2)
    norm_num at hComponent

/-- 固定非零入射量和有效透过率的仿射回归参数。 -/
def affineParameters : TwoLayerStateParameters where
  firstTransmissivity := fun _ => 1/2
  secondTransmissivity := fun _ => 1/2
  incoming := fun _ => 1

/-- 有效透过率下模型仍可有非零入射偏置，因此状态到观测通常是仿射映射。 -/
theorem twoLayerState_nonzero_offset :
    affineParameters.Valid ∧ twoLayerStateObserve affineParameters 0 ≠ 0 := by
  constructor
  · constructor <;> intro i <;> norm_num [affineParameters]
  · intro h
    have hComponent := congrFun h (0 : Fin 2)
    norm_num [twoLayerStateObserve, twoLayerStateOffset, affineParameters] at hComponent

/-- 裸 Gaussian 总函数在零线宽时处处为一；谱线语义需另给正线宽条件。 -/
theorem gaussian_zero_width (frequency center : ℝ) :
    gaussianLineProfile frequency center 0 = 1 := by
  simp [gaussianLineProfile]

end
end LeanOEM.Tests.SemanticBoundaries
