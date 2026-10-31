module

public import LeanOEM.Core.LocalContraction
public import LeanOEM.Tests.ForwardModel
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-!
# 局部收缩契约测试

这些测试使用无噪声标量平方模型检查余项表示和正规缺陷界。
它们是精确实数的数学 fixture，不代表 ARTS 或真实观测场景。
-/

@[expose] public section

namespace LeanOEM.Tests.LocalContraction

open LeanOEM LeanOEM.NonlinearProblem
open Filter
open scoped Topology

noncomputable section

private def squareProblemZero : NonlinearProblem 1 1 where
  model := { observe := fun x => ![(x 0) ^ 2] }
  observation := ![0]
  priorMean := ![0]
  priorWeight := !![1]
  observationWeight := !![1]

private def squareJacobianAt (x : State 1) : Jacobian 1 1 := !![2 * x 0]

private lemma state_one_eq (x : State 1) : x = ![x 0] := by
  ext i
  fin_cases i
  rfl

private lemma scalar_norm (a : ℝ) : ‖(![a] : State 1)‖ = |a| := by
  have h : (![a] : State 1) = fun _ => a := by
    ext i
    fin_cases i
    rfl
  rw [h, pi_norm_const, Real.norm_eq_abs]

private lemma square_remainder_zero (x : State 1) :
    ForwardModel.linearizationRemainder squareProblemZero.model x
        (![0] : State 1) (squareJacobianAt x) = ![(x 0) ^ 2] := by
  funext i
  fin_cases i
  simp [ForwardModel.linearizationRemainder, squareProblemZero, squareJacobianAt,
    Matrix.vecHead]
  ring

private lemma square_normalDefect_zero (x : State 1) :
    NonlinearProblem.normalDefect squareProblemZero x (![0] : State 1)
        (squareJacobianAt x) =
      ![2 * (x 0) ^ 3] := by
  funext i
  fin_cases i
  simp [normalDefect, normalRhs, normalMatrix, NonlinearProblem.residual,
    squareProblemZero, squareJacobianAt, Matrix.mul_apply, Matrix.mulVec,
    Matrix.conjTranspose, Matrix.transpose, Matrix.vecHead, dotProduct]
  ring

private lemma square_normalMatrix_eq (x : State 1) :
    squareProblemZero.normalMatrix x (squareJacobianAt x) =
      !![4 * (x 0) ^ 2 + 1] := by
  ext i j
  fin_cases i
  fin_cases j
  simp [normalMatrix, squareProblemZero, squareJacobianAt, Matrix.mul_apply,
    Matrix.conjTranspose, Matrix.transpose]
  ring

example (x : State 1) :
    ForwardModel.QuadraticRemainderBound squareProblemZero.model x
      (![0] : State 1) (squareJacobianAt x) 1 := by
  unfold ForwardModel.QuadraticRemainderBound
  rw [square_remainder_zero]
  have hx : x = ![x 0] := state_one_eq x
  rw [hx]
  simp [scalar_norm]

private lemma square_weighted_action_bound (x : State 1)
    (hRadius : ‖x - (![0] : State 1)‖ ≤ (1 / 2 : ℝ)) :
    squareProblemZero.WeightedJacobianActionBound (squareJacobianAt x) 1 := by
  have hxState : x = ![x 0] := state_one_eq x
  have hx : |x 0| ≤ (1 / 2 : ℝ) := by
    rw [hxState] at hRadius
    simpa [scalar_norm] using hRadius
  intro v
  have hvState : v = ![v 0] := state_one_eq v
  rw [hxState, hvState]
  change ‖(squareJacobianAt ![x 0]).conjTranspose.mulVec
      (squareProblemZero.observationWeight.mulVec ![v 0])‖ ≤
      1 * ‖![v 0]‖
  have hWeight : squareProblemZero.observationWeight = (!![1] : Square 1) := by
    rfl
  rw [hWeight]
  have hActionEq :
      (squareJacobianAt ![x 0]).conjTranspose.mulVec
          ((!![1] : Square 1).mulVec ![v 0]) = ![2 * x 0 * v 0] := by
    ext i
    fin_cases i
    simp [squareJacobianAt, Matrix.mulVec, Matrix.conjTranspose,
      Matrix.transpose, dotProduct]
  rw [hActionEq, scalar_norm, scalar_norm, abs_mul]
  have hTwoX : |2 * x 0| ≤ (1 : ℝ) := by
    rw [abs_mul]
    norm_num
    nlinarith [hx]
  exact mul_le_mul_of_nonneg_right hTwoX (abs_nonneg _)

private lemma square_normalDefect_bound (x : State 1)
    (hRadius : ‖x - (![0] : State 1)‖ ≤ (1 / 2 : ℝ)) :
    NonlinearProblem.NormalDefectBound squareProblemZero x (![0] : State 1)
      (squareJacobianAt x) (1 / 2 : ℝ) := by
  have hBound := normalDefectBound_of_quadraticRemainder
    squareProblemZero x (![0] : State 1) (squareJacobianAt x)
    (beta := (1 : ℝ)) (rho := (1 : ℝ)) (radius := (1 / 2 : ℝ))
    (by simp [squareProblemZero]) (by simp [squareProblemZero])
    (by norm_num) (by norm_num) hRadius
    (square_weighted_action_bound x hRadius) (by
      unfold ForwardModel.QuadraticRemainderBound
      rw [square_remainder_zero]
      have hxState : x = ![x 0] := state_one_eq x
      rw [hxState]
      simp [scalar_norm])
  simpa using hBound

private lemma square_inverse_action_bound (x : State 1) :
    squareProblemZero.InverseActionBound x (squareJacobianAt x) 1 := by
  intro v
  have hvState : v = ![v 0] := state_one_eq v
  rw [square_normalMatrix_eq x]
  have hInvMatrix :
      (!![4 * (x 0) ^ 2 + 1] : Square 1)⁻¹ =
        !![(4 * (x 0) ^ 2 + 1)⁻¹] := by
    rw [Matrix.inv_subsingleton]
    ext i j
    fin_cases i
    fin_cases j
    simp [Ring.inverse_eq_inv]
  rw [hInvMatrix, hvState]
  have hDen : 0 < 4 * (x 0) ^ 2 + 1 := by positivity
  have hDenOne : 1 ≤ 4 * (x 0) ^ 2 + 1 := by
    nlinarith [sq_nonneg (x 0)]
  have hActionEq :
      (!![(4 * (x 0) ^ 2 + 1)⁻¹] : Square 1).mulVec ![v 0] =
        ![(4 * (x 0) ^ 2 + 1)⁻¹ * v 0] := by
    ext i
    fin_cases i
    simp [Matrix.mulVec]
  rw [hActionEq, scalar_norm, scalar_norm, abs_mul,
    abs_of_nonneg (inv_nonneg.mpr hDen.le)]
  exact mul_le_mul_of_nonneg_right
    (inv_le_one_of_one_le₀ hDenOne) (abs_nonneg _)

private lemma square_update_error_bound (x : State 1)
    (hRadius : ‖x - (![0] : State 1)‖ ≤ (1 / 2 : ℝ)) :
    ‖squareProblemZero.gaussNewtonUpdate x (squareJacobianAt x) -
        (![0] : State 1)‖ ≤
      (1 / 2 : ℝ) * ‖x - (![0] : State 1)‖ := by
  have hBound := gaussNewtonUpdate_error_le_of_inverse_and_defect
    squareProblemZero x (![0] : State 1) (squareJacobianAt x)
    (gamma := (1 : ℝ)) (eta := (1 / 2 : ℝ))
    (by
      rw [square_normalMatrix_eq x]
      norm_num [Matrix.isUnit_iff_isUnit_det]
      positivity)
    (by norm_num) (square_inverse_action_bound x)
    (square_normalDefect_bound x hRadius)
  simpa using hBound

private def squareDomain : Set (State 1) :=
  {x | ‖x - (![0] : State 1)‖ ≤ (1 / 2 : ℝ)}

private def squareRefreshed : ℕ → State 1 → Jacobian 1 1 :=
  fun _ x => squareJacobianAt x

private lemma square_normal_isUnit (x : State 1) :
    IsUnit (squareProblemZero.normalMatrix x (squareJacobianAt x)) := by
  rw [square_normalMatrix_eq x]
  norm_num [Matrix.isUnit_iff_isUnit_det]
  positivity

private lemma square_maps_domain :
    Set.MapsTo
      (fun x => squareProblemZero.gaussNewtonUpdate x (squareJacobianAt x))
      squareDomain squareDomain := by
  intro x hx
  have hRadius : ‖x - (![0] : State 1)‖ ≤ (1 / 2 : ℝ) := by
    exact hx
  change ‖squareProblemZero.gaussNewtonUpdate x (squareJacobianAt x) -
      (![0] : State 1)‖ ≤ (1 / 2 : ℝ)
  have hUpdate := square_update_error_bound x hRadius
  have hNorm : 0 ≤ ‖x - (![0] : State 1)‖ := norm_nonneg _
  nlinarith

private lemma square_contracts (initial : State 1)
    (hInitial : initial ∈ squareDomain) :
    squareProblemZero.ContractsTowardAlong squareRefreshed initial
      (![0] : State 1) (1 / 2 : ℝ) := by
  have hContract := contractsTowardAlong_of_inverse_and_defect
    squareProblemZero squareRefreshed initial (![0] : State 1)
    (gamma := (1 : ℝ)) (eta := (1 / 2 : ℝ)) (by norm_num)
    (by
      intro i
      exact square_normal_isUnit
        (squareProblemZero.gaussNewtonIterate squareRefreshed initial i))
    (by
      intro i
      exact square_inverse_action_bound
        (squareProblemZero.gaussNewtonIterate squareRefreshed initial i))
    (by
      intro i
      apply square_normalDefect_bound
      exact squareProblemZero.gaussNewtonIterate_mem squareRefreshed initial
        hInitial (by
          intro i x hx
          exact square_maps_domain hx) i)
  simpa using hContract

example (initial : State 1) (hInitial : initial ∈ squareDomain) :
    Tendsto
      (squareProblemZero.gaussNewtonIterate squareRefreshed initial)
      atTop (𝓝 (![0] : State 1)) := by
  apply squareProblemZero.gaussNewtonIterate_tendsto
    (q := (1 / 2 : ℝ)) squareRefreshed initial (![0] : State 1)
    (by norm_num) (by norm_num)
  exact square_contracts initial hInitial

example (x : State 1) :
    NonlinearProblem.normalDefect squareProblemZero x (![0] : State 1)
        (squareJacobianAt x) =
      (squareJacobianAt x).conjTranspose.mulVec
        (squareProblemZero.observationWeight.mulVec
        (ForwardModel.linearizationRemainder squareProblemZero.model x
          (![0] : State 1) (squareJacobianAt x))) := by
  rw [square_normalDefect_zero, square_remainder_zero]
  funext i
  fin_cases i
  simp [squareProblemZero, squareJacobianAt, Matrix.mulVec,
    Matrix.conjTranspose, Matrix.transpose, dotProduct]
  ring

/-! ## 非零目标残差与非零先验偏差的驻点模型 -/

private def squareStationaryProblem : NonlinearProblem 1 1 where
  model := { observe := fun x => ![(x 0) ^ 2] }
  observation := ![(11 / 10 : ℝ)]
  priorMean := ![0]
  priorWeight := !![(1 / 5 : ℝ)]
  observationWeight := !![1]

private def squareStationaryTarget : State 1 := ![1]

private def squareStationaryJacobianAt (x : State 1) : Jacobian 1 1 :=
  !![2 * x 0]

private def squareStationaryJacobianTarget : Jacobian 1 1 := !![2]

private lemma square_stationary_target :
    squareStationaryProblem.TargetStationary squareStationaryTarget
      squareStationaryJacobianTarget := by
  unfold TargetStationary normalRhs NonlinearProblem.residual
  funext i
  fin_cases i
  norm_num [squareStationaryProblem, squareStationaryTarget,
    squareStationaryJacobianTarget, Matrix.mul_apply, Matrix.mulVec,
    Matrix.conjTranspose, Matrix.transpose, Matrix.vecHead, dotProduct]

example (x : State 1) :
    squareStationaryProblem.normalDefect x squareStationaryTarget
        (squareStationaryJacobianAt x) =
      (squareStationaryJacobianAt x).conjTranspose.mulVec
          (squareStationaryProblem.observationWeight.mulVec
            (squareStationaryProblem.residual squareStationaryTarget)) -
        squareStationaryJacobianTarget.conjTranspose.mulVec
          (squareStationaryProblem.observationWeight.mulVec
            (squareStationaryProblem.residual squareStationaryTarget)) +
        (squareStationaryJacobianAt x).conjTranspose.mulVec
          (squareStationaryProblem.observationWeight.mulVec
            (ForwardModel.linearizationRemainder squareStationaryProblem.model x
              squareStationaryTarget (squareStationaryJacobianAt x))) := by
  exact normalDefect_eq_jacobianVariation_add_remainder_of_stationary
    squareStationaryProblem x squareStationaryTarget
      (squareStationaryJacobianAt x) squareStationaryJacobianTarget
      square_stationary_target

end
end LeanOEM.Tests.LocalContraction

