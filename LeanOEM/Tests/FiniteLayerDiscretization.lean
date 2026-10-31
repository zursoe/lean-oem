module

public import LeanOEM.Physics.FiniteLayerDiscretization
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-!
# 两层有限层离散化测试

使用精确有理数检查有限层正演、Jacobian 误差和 OEM 正规方程误差的传播。
-/

@[expose] public section

namespace LeanOEM.Tests.FiniteLayerDiscretization

open LeanOEM
open LeanOEM.NonlinearProblem
open LeanOEM.RadiativeTransfer

noncomputable section

private def exactParameters : TwoLayerSourceParameters :=
  { firstTransmissivity := 1 / 2
    secondTransmissivity := 3 / 4
    incoming := 2 }

private def approximateParameters : TwoLayerSourceParameters :=
  { firstTransmissivity := 3 / 5
    secondTransmissivity := 7 / 10
    incoming := 2 }

private def target : State 1 := ![(1 / 2 : ℝ)]

private def twoLayerProblem : NonlinearProblem 1 1 where
  model := twoLayerSourceModel exactParameters
  observation := ![(93 / 80 : ℝ)]
  priorMean := ![(7 / 16 : ℝ)]
  priorWeight := !![1]
  observationWeight := !![1]

private lemma exact_valid : exactParameters.Valid := by
  constructor <;> norm_num [exactParameters]

private lemma approximate_valid : approximateParameters.Valid := by
  constructor <;> norm_num [approximateParameters]

private lemma transmissivity_errors :
    |approximateParameters.firstTransmissivity - exactParameters.firstTransmissivity|
        ≤ (1 / 10 : ℝ) ∧
      |approximateParameters.secondTransmissivity - exactParameters.secondTransmissivity|
        ≤ (1 / 20 : ℝ) := by
  constructor <;> norm_num [approximateParameters, exactParameters, abs_of_nonneg,
    abs_of_pos]

/-- 两层传播的闭式输出与独立 `propagateTwo` 定义一致。 -/
example :
    twoLayerSourceObserve exactParameters target = ![(17 / 16 : ℝ)] := by
  norm_num [twoLayerSourceObserve, exactParameters, target,
    twoLayerSourceCoefficient]

/-- 精确 Jacobian 的系数为 `5/8`，近似 Jacobian 的系数为 `29/50`。 -/
example : twoLayerSourceJacobian exactParameters = !![(5 / 8 : ℝ)] := by
  norm_num [twoLayerSourceJacobian, exactParameters, twoLayerSourceCoefficient]

example : twoLayerSourceJacobian approximateParameters = !![(29 / 50 : ℝ)] := by
  norm_num [twoLayerSourceJacobian, approximateParameters, twoLayerSourceCoefficient]

/-- 有限层正演模型的导数由显式 Jacobian 表示。 -/
example (x : State 1) :
    (twoLayerSourceModel exactParameters).HasJacobianAt x
      (twoLayerSourceJacobian exactParameters) := by
  exact twoLayerSource_hasJacobianAt exactParameters x

private lemma twoLayer_jacobian_error :
    twoLayerProblem.WeightedJacobianErrorBound
      (twoLayerSourceJacobian approximateParameters)
      (twoLayerSourceJacobian exactParameters) (3 / 20 : ℝ) := by
  rcases transmissivity_errors with ⟨hFirst, hSecond⟩
  have h := twoLayerSource_weightedJacobianErrorBound_of_unitWeight
    twoLayerProblem rfl exactParameters approximateParameters
    exact_valid approximate_valid hFirst hSecond
  norm_num at h ⊢
  exact h

/-- 逐层透过率误差给出 `3/20` 的 Jacobian 误差上界。 -/
example :
    |twoLayerSourceCoefficient approximateParameters -
      twoLayerSourceCoefficient exactParameters| ≤ (3 / 20 : ℝ) := by
  rcases transmissivity_errors with ⟨hFirst, hSecond⟩
  have h := twoLayerSourceJacobian_coefficient_error_le
    exactParameters approximateParameters exact_valid approximate_valid hFirst hSecond
  norm_num at h ⊢
  exact h

/-- 正演离散误差在有界入射辐亮度和状态下满足显式界。 -/
example :
    ‖twoLayerSourceObserve approximateParameters target -
      twoLayerSourceObserve exactParameters target‖ ≤ (3 / 8 : ℝ) := by
  rcases transmissivity_errors with ⟨hFirst, hSecond⟩
  have h := twoLayerSource_forward_error_le
    exactParameters approximateParameters exact_valid approximate_valid rfl target
    (incomingBound := (2 : ℝ)) (stateBound := (1 / 2 : ℝ))
    (by norm_num) (by norm_num)
    hFirst hSecond (by norm_num [exactParameters]) (by norm_num [target])
  norm_num at h ⊢
  exact h

private lemma twoLayer_target_stationary :
    twoLayerProblem.TargetStationary target
      (twoLayerSourceJacobian exactParameters) := by
  unfold TargetStationary normalRhs NonlinearProblem.residual
  funext i
  fin_cases i
  norm_num [twoLayerProblem, target, exactParameters, twoLayerSourceModel,
    twoLayerSourceObserve, twoLayerSourceJacobian,
    twoLayerSourceCoefficient, Matrix.mul_apply, Matrix.mulVec,
    Matrix.conjTranspose, Matrix.transpose, Matrix.vecHead, dotProduct]

/-- 非零目标残差下，近似 Jacobian 产生的正规方程残差符合 `epsilon * sigma` 界。 -/
example :
    ‖twoLayerProblem.normalRhs target
        (twoLayerSourceJacobian approximateParameters)‖ ≤ (3 / 200 : ℝ) := by
  have hResidual : ‖twoLayerProblem.residual target‖ ≤ (1 / 10 : ℝ) := by
    have hResEq : twoLayerProblem.residual target = ![(1 / 10 : ℝ)] := by
      funext i
      fin_cases i
      norm_num [NonlinearProblem.residual, twoLayerProblem, target,
        twoLayerSourceModel, twoLayerSourceObserve, exactParameters,
        twoLayerSourceCoefficient]
    rw [hResEq, observationOneNorm]
    norm_num
  have hBound := normalRhs_norm_le_of_weightedJacobianError
    twoLayerProblem target (twoLayerSourceJacobian approximateParameters)
      (twoLayerSourceJacobian exactParameters)
      (epsilon := (3 / 20 : ℝ)) (sigma := (1 / 10 : ℝ))
      (by norm_num) twoLayer_target_stationary twoLayer_jacobian_error hResidual
  norm_num at hBound ⊢
  exact hBound

private lemma twoLayer_normalMatrix_approx :
    twoLayerProblem.normalMatrix target
        (twoLayerSourceJacobian approximateParameters) =
      !![(3341 / 2500 : ℝ)] := by
  unfold NonlinearProblem.normalMatrix
  ext i j
  fin_cases i
  fin_cases j
  norm_num [twoLayerProblem, twoLayerSourceJacobian, approximateParameters,
    twoLayerSourceCoefficient, Matrix.mul_apply, Matrix.conjTranspose,
    Matrix.transpose, Fin.sum_univ_succ]

private lemma twoLayer_inverse_action_bound :
    twoLayerProblem.InverseActionBound target
      (twoLayerSourceJacobian approximateParameters) 1 := by
  intro v
  have hv : v = ![v 0] := by
    ext i
    fin_cases i
    rfl
  rw [twoLayer_normalMatrix_approx, hv]
  have hInvMatrix :
      (!![(3341 / 2500 : ℝ)] : Square 1)⁻¹ =
        !![(2500 / 3341 : ℝ)] := by
    rw [Matrix.inv_subsingleton]
    ext i j
    fin_cases i
    fin_cases j
    norm_num [Ring.inverse_eq_inv]
  rw [hInvMatrix]
  have hActionEq :
      (!![(2500 / 3341 : ℝ)] : Square 1).mulVec ![v 0] =
        ![(2500 / 3341 : ℝ) * v 0] := by
    ext i
    fin_cases i
    simp [Matrix.mulVec]
  rw [hActionEq, stateOneNorm, stateOneNorm, abs_mul]
  have hInvLe : |(2500 / 3341 : ℝ)| ≤ 1 := by
    norm_num [abs_of_nonneg]
  exact mul_le_mul_of_nonneg_right hInvLe (abs_nonneg _)

/-- Jacobian 离散化造成的正规方程误差进一步形成更新误差底。 -/
example :
    ‖twoLayerProblem.gaussNewtonUpdate target
        (twoLayerSourceJacobian approximateParameters) - target‖ ≤
      (3 / 200 : ℝ) := by
  have hNormal : IsUnit (twoLayerProblem.normalMatrix target
      (twoLayerSourceJacobian approximateParameters)) := by
    rw [twoLayer_normalMatrix_approx]
    norm_num [Matrix.isUnit_iff_isUnit_det]
  have hRhs :
      ‖twoLayerProblem.normalRhs target
          (twoLayerSourceJacobian approximateParameters)‖ ≤ (3 / 200 : ℝ) := by
    have hResidual : ‖twoLayerProblem.residual target‖ ≤ (1 / 10 : ℝ) := by
      have hResEq : twoLayerProblem.residual target = ![(1 / 10 : ℝ)] := by
        funext i
        fin_cases i
        norm_num [NonlinearProblem.residual, twoLayerProblem, target,
          twoLayerSourceModel, twoLayerSourceObserve, exactParameters,
          twoLayerSourceCoefficient]
      rw [hResEq, observationOneNorm]
      norm_num
    have hBound := normalRhs_norm_le_of_weightedJacobianError
      twoLayerProblem target (twoLayerSourceJacobian approximateParameters)
        (twoLayerSourceJacobian exactParameters)
        (epsilon := (3 / 20 : ℝ)) (sigma := (1 / 10 : ℝ))
        (by norm_num) twoLayer_target_stationary twoLayer_jacobian_error hResidual
    norm_num at hBound ⊢
    exact hBound
  have hDefect :
      ‖twoLayerProblem.normalDefect target target
          (twoLayerSourceJacobian approximateParameters)‖ ≤
        (0 : ℝ) * ‖target - target‖ + (3 / 200 : ℝ) := by
    simpa [normalDefect] using hRhs
  have hBound := gaussNewtonUpdate_error_le_of_inverse_and_additive_defect
    twoLayerProblem target target (twoLayerSourceJacobian approximateParameters)
      (gamma := (1 : ℝ)) (eta := (0 : ℝ)) (tau := (3 / 200 : ℝ))
      hNormal (by norm_num) twoLayer_inverse_action_bound hDefect
  norm_num at hBound ⊢
  exact hBound

end
end LeanOEM.Tests.FiniteLayerDiscretization
