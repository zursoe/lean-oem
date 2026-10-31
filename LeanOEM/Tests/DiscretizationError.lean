module

public import LeanOEM.Core.DiscretizationError
public import LeanOEM.Physics.Discretization
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-!
# Jacobian 离散化误差测试

测试把中心有限差分的误差界和 OEM 的加权 Jacobian 误差契约连接起来。
所有数值均为精确有理数，不代表浮点实现或 ARTS 输出。
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

end
end LeanOEM.Tests.DiscretizationError

