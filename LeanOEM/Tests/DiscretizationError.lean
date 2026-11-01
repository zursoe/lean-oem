module

public import LeanOEM.Core.DiscretizationError
public import LeanOEM.Physics.Discretization
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-!
# Jacobian 离散化误差测试

测试把中心有限差分的误差界和 OEM 的加权 Jacobian 误差契约连接起来。
所有数值均为精确有理数，不代表浮点实现或 具体实现输出。
-/

@[expose] public section

namespace LeanOEM.Tests.DiscretizationError

open LeanOEM LeanOEM.NonlinearProblem
open LeanOEM.RadiativeTransfer

noncomputable section

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

private def cubicProblem : NonlinearProblem 1 1 where
  model := { observe := fun x => ![(x 0) ^ 3] }
  observation := ![(11 / 10 : ℝ)]
  priorMean := ![0]
  priorWeight := !![(3 / 10 : ℝ)]
  observationWeight := !![1]

private def exactJacobian : Jacobian 1 1 := !![3]
private def approximateJacobian : Jacobian 1 1 := !![(301 / 100 : ℝ)]

private def approximateCubicModel : ForwardModel 1 1 where
  observe := fun x => ![(x 0) ^ 3 + (1 / 100 : ℝ)]

example :
    |centralDifference (fun z => z ^ 3) (1 : ℝ) (1 / 10 : ℝ) - 3| ≤
      (1 / 10 : ℝ) ^ 2 := by
  have hBound := centralDifference_error_bound (f := fun z => z ^ 3)
    (x := 1) (h := (1 / 10 : ℝ)) (derivative := 3)
    (quadratic := 3) (rPlus := (1 / 10 : ℝ) ^ 3)
    (rMinus := -(1 / 10 : ℝ) ^ 3) (C := 1)
    (by norm_num) (by ring) (by ring)
    (by norm_num [abs_of_nonneg]) (by norm_num [abs_of_nonneg])
  norm_num at hBound ⊢
  exact hBound

private lemma cubic_jacobian_error :
    cubicProblem.WeightedJacobianErrorBound approximateJacobian exactJacobian
      (1 / 100 : ℝ) := by
  intro v
  have hv : v = ![v 0] := state_one_eq v
  rw [hv]
  change ‖(approximateJacobian).conjTranspose.mulVec
      ((!![1] : Square 1).mulVec ![v 0]) -
      (exactJacobian).conjTranspose.mulVec
        ((!![1] : Square 1).mulVec ![v 0])‖ ≤
    (1 / 100 : ℝ) * ‖![v 0]‖
  have hEq :
      (approximateJacobian).conjTranspose.mulVec
          ((!![1] : Square 1).mulVec ![v 0]) -
        (exactJacobian).conjTranspose.mulVec
          ((!![1] : Square 1).mulVec ![v 0]) =
        ![(1 / 100 : ℝ) * v 0] := by
    ext i
    fin_cases i
    simp [approximateJacobian, exactJacobian, Matrix.conjTranspose,
      Matrix.transpose, Matrix.mulVec, Matrix.vecHead,
      dotProduct]
    ring
  rw [hEq, scalar_norm, scalar_norm, abs_mul]
  norm_num

private lemma cubic_target_stationary :
    cubicProblem.TargetStationary (![1] : State 1) exactJacobian := by
  unfold TargetStationary normalRhs NonlinearProblem.residual
  funext i
  fin_cases i
  norm_num [cubicProblem, exactJacobian, Matrix.mul_apply, Matrix.mulVec,
    Matrix.conjTranspose, Matrix.transpose, Matrix.vecHead, dotProduct]

private lemma cubic_approximate_action :
    cubicProblem.WeightedJacobianActionBound approximateJacobian (301 / 100 : ℝ) := by
  intro v
  have hv : v = ![v 0] := state_one_eq v
  rw [hv]
  change ‖approximateJacobian.conjTranspose.mulVec
      ((!![1] : Square 1).mulVec ![v 0])‖ ≤
    (301 / 100 : ℝ) * ‖![v 0]‖
  have hEq :
      approximateJacobian.conjTranspose.mulVec
          ((!![1] : Square 1).mulVec ![v 0]) =
        ![(301 / 100 : ℝ) * v 0] := by
    ext i
    fin_cases i
    simp [approximateJacobian, Matrix.conjTranspose, Matrix.transpose,
      Matrix.mulVec, dotProduct]
  rw [hEq, scalar_norm, scalar_norm, abs_mul]
  norm_num [abs_of_nonneg]

private lemma cubic_forward_error :
    ForwardModelErrorBound approximateCubicModel cubicProblem.model
      (![1] : State 1) (1 / 100 : ℝ) := by
  unfold ForwardModelErrorBound
  have hEq :
      approximateCubicModel.observe (![1] : State 1) -
          cubicProblem.model.observe (![1] : State 1) =
        ![(1 / 100 : ℝ)] := by
    funext i
    fin_cases i
    norm_num [approximateCubicModel, cubicProblem]
  rw [hEq, scalar_norm]
  norm_num

example :
    ‖cubicProblem.normalRhs (![1] : State 1) approximateJacobian‖ ≤
      (1 / 1000 : ℝ) := by
  have hResidual : ‖cubicProblem.residual (![1] : State 1)‖ ≤
      (1 / 10 : ℝ) := by
    have hResEq : cubicProblem.residual (![1] : State 1) =
        ![(1 / 10 : ℝ)] := by
      funext i
      fin_cases i
      norm_num [NonlinearProblem.residual, cubicProblem]
    rw [hResEq, scalar_norm]
    norm_num
  have hBound := normalRhs_norm_le_of_weightedJacobianError
    cubicProblem (![1] : State 1) approximateJacobian exactJacobian
    (epsilon := (1 / 100 : ℝ)) (sigma := (1 / 10 : ℝ))
    (by norm_num) cubic_target_stationary cubic_jacobian_error hResidual
  norm_num at hBound ⊢
  exact hBound

/-- 前向模型误差和 Jacobian 误差共同进入正规方程右端。 -/
example :
    ‖cubicProblem.normalRhsFor approximateCubicModel (![1] : State 1)
        approximateJacobian‖ ≤
      (311 / 10000 : ℝ) := by
  have hResidual : ‖cubicProblem.residualFor cubicProblem.model
      (![1] : State 1)‖ ≤ (1 / 10 : ℝ) := by
    have hResEq : cubicProblem.residualFor cubicProblem.model
        (![1] : State 1) = ![(1 / 10 : ℝ)] := by
      funext i
      fin_cases i
      norm_num [NonlinearProblem.residualFor, cubicProblem]
    rw [hResEq, scalar_norm]
    norm_num
  have hBound := normalRhsFor_norm_le_of_forward_and_jacobian_error
    cubicProblem (![1] : State 1) approximateCubicModel cubicProblem.model
      approximateJacobian exactJacobian
      (beta := (301 / 100 : ℝ)) (epsilonJacobian := (1 / 100 : ℝ))
      (epsilonForward := (1 / 100 : ℝ)) (sigma := (1 / 10 : ℝ))
      (by norm_num) (by norm_num) cubic_target_stationary
      cubic_approximate_action cubic_jacobian_error cubic_forward_error hResidual
  norm_num at hBound ⊢
  exact hBound

private lemma cubic_approximate_normalMatrix :
    (cubicProblem.withModel approximateCubicModel).normalMatrix
        (![1] : State 1) approximateJacobian =
      !![(93601 / 10000 : ℝ)] := by
  unfold NonlinearProblem.withModel NonlinearProblem.normalMatrix
  ext i j
  fin_cases i
  fin_cases j
  norm_num [cubicProblem, approximateJacobian, Matrix.mul_apply,
    Matrix.conjTranspose, Matrix.transpose, dotProduct]

private lemma cubic_approximate_inverse_action :
    (cubicProblem.withModel approximateCubicModel).InverseActionBound
      (![1] : State 1) approximateJacobian 1 := by
  intro v
  have hv : v = ![v 0] := state_one_eq v
  rw [hv, cubic_approximate_normalMatrix]
  have hInvMatrix :
      (!![(93601 / 10000 : ℝ)] : Square 1)⁻¹ =
        !![(10000 / 93601 : ℝ)] := by
    rw [Matrix.inv_subsingleton]
    ext i j
    fin_cases i
    fin_cases j
    norm_num [Ring.inverse_eq_inv]
  rw [hInvMatrix]
  have hActionEq :
      (!![(10000 / 93601 : ℝ)] : Square 1).mulVec ![v 0] =
        ![(10000 / 93601 : ℝ) * v 0] := by
    ext i
    fin_cases i
    simp [Matrix.mulVec]
  rw [hActionEq, scalar_norm, scalar_norm, abs_mul]
  have hLe : |(10000 / 93601 : ℝ)| ≤ 1 := by
    norm_num [abs_of_nonneg]
  simpa using mul_le_mul_of_nonneg_right hLe (abs_nonneg (v 0))

/-- 联合误差契约在近似正规矩阵的逆作用界下给出一步更新误差底。 -/
example :
    ‖(cubicProblem.withModel approximateCubicModel).gaussNewtonUpdate
        (![1] : State 1) approximateJacobian - ![1]‖ ≤
      (311 / 10000 : ℝ) := by
  have hResidual : ‖cubicProblem.residualFor cubicProblem.model
      (![1] : State 1)‖ ≤ (1 / 10 : ℝ) := by
    have hResEq : cubicProblem.residualFor cubicProblem.model
        (![1] : State 1) = ![(1 / 10 : ℝ)] := by
      funext i
      fin_cases i
      norm_num [NonlinearProblem.residualFor, cubicProblem]
    rw [hResEq, scalar_norm]
    norm_num
  have hNormal : IsUnit ((cubicProblem.withModel approximateCubicModel).normalMatrix
      (![1] : State 1) approximateJacobian) := by
    rw [cubic_approximate_normalMatrix]
    norm_num [Matrix.isUnit_iff_isUnit_det]
  have hBound := gaussNewtonUpdate_error_le_of_forward_and_jacobian_error
    cubicProblem (![1] : State 1) approximateCubicModel cubicProblem.model
      approximateJacobian exactJacobian
      (beta := (301 / 100 : ℝ)) (epsilonJacobian := (1 / 100 : ℝ))
      (epsilonForward := (1 / 100 : ℝ)) (sigma := (1 / 10 : ℝ)) (gamma := 1)
      (by norm_num) (by norm_num) cubic_target_stationary
      cubic_approximate_action cubic_jacobian_error cubic_forward_error hResidual
      hNormal (by norm_num) cubic_approximate_inverse_action
  norm_num at hBound ⊢
  exact hBound

end
end LeanOEM.Tests.DiscretizationError

