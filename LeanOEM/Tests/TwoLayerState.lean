module

public import LeanOEM.Physics.TwoLayerState
public import LeanOEM.Core.DiscretizationError
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-!
# 两层两状态模型测试

测试使用精确有理数检查显式 Jacobian、正演输出、导数契约和一个有限层
参数扰动的前向误差。它是 OEM 误差链的数学 fixture，不是 具体工程场景。
-/

@[expose] public section

namespace LeanOEM.Tests.TwoLayerState

open LeanOEM
open LeanOEM.RadiativeTransfer
open LeanOEM.NonlinearProblem

noncomputable section

private def exactParameters : TwoLayerStateParameters :=
  { firstTransmissivity := ![(1 / 2 : ℝ), (2 / 3 : ℝ)]
    secondTransmissivity := ![(3 / 4 : ℝ), (4 / 5 : ℝ)]
    incoming := ![(2 : ℝ), (1 : ℝ)] }

private def approximateParameters : TwoLayerStateParameters :=
  { firstTransmissivity := ![(3 / 5 : ℝ), (7 / 10 : ℝ)]
    secondTransmissivity := ![(3 / 4 : ℝ), (4 / 5 : ℝ)]
    incoming := ![(2 : ℝ), (1 : ℝ)] }

private def target : State 2 := ![(1 / 2 : ℝ), (1 / 3 : ℝ)]

private lemma exact_valid : exactParameters.Valid := by
  constructor <;> intro i <;> fin_cases i <;> norm_num [exactParameters]

private lemma approximate_valid : approximateParameters.Valid := by
  constructor <;> intro i <;> fin_cases i <;> norm_num [approximateParameters]

private def invalidParameters : TwoLayerStateParameters :=
  { firstTransmissivity := ![(3 / 2 : ℝ), 1 / 2]
    secondTransmissivity := ![(1 / 2 : ℝ), 1 / 2]
    incoming := ![0, 0] }

/-- 超过一的透过率参数不能满足两层状态模型的有效性假设。 -/
example : ¬ invalidParameters.Valid := by
  intro h
  have hUpper := h.first_le_one 0
  norm_num [invalidParameters] at hUpper

/-- 两个通道的显式 Jacobian。 -/
example : twoLayerStateJacobian exactParameters =
    !![(3 / 8 : ℝ), 1 / 4; 4 / 15, 1 / 5] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [twoLayerStateJacobian, twoLayerStateFirstCoefficient,
      twoLayerStateSecondCoefficient, exactParameters]

/-- 两层状态模型的精确正演输出。 -/
example : twoLayerStateObserve exactParameters target =
    ![(49 / 48 : ℝ), (11 / 15 : ℝ)] := by
  ext i
  fin_cases i <;>
    norm_num [twoLayerStateObserve, twoLayerStateOffset, twoLayerStateJacobian,
      twoLayerStateFirstCoefficient, twoLayerStateSecondCoefficient,
      exactParameters, target, Matrix.mulVec, Matrix.vecHead, dotProduct,
      Matrix.vecTail, Function.comp_apply, Fin.sum_univ_succ]

/-- 显式 Jacobian 满足 `ForwardModel` 导数契约。 -/
example (x : State 2) :
    (twoLayerStateModel exactParameters).HasJacobianAt x
      (twoLayerStateJacobian exactParameters) := by
  exact twoLayerState_hasJacobianAt exactParameters x

/-- 透过率参数扰动的正演误差可以接入通用前向误差契约。 -/
example :
    ForwardModelErrorBound
      (twoLayerStateModel approximateParameters)
      (twoLayerStateModel exactParameters) target (9 / 80 : ℝ) := by
  unfold ForwardModelErrorBound
  have hDifference :
      twoLayerStateObserve approximateParameters target -
          twoLayerStateObserve exactParameters target =
        ![(9 / 80 : ℝ), (1 / 75 : ℝ)] := by
    ext i
    fin_cases i <;>
      norm_num [twoLayerStateObserve, twoLayerStateOffset, twoLayerStateJacobian,
        twoLayerStateFirstCoefficient, twoLayerStateSecondCoefficient,
        approximateParameters, exactParameters, target, Matrix.mulVec,
        Matrix.vecHead, Matrix.vecTail, Function.comp_apply, dotProduct,
        Fin.sum_univ_succ]
  change ‖twoLayerStateObserve approximateParameters target -
    twoLayerStateObserve exactParameters target‖ ≤ (9 / 80 : ℝ)
  rw [hDifference, pi_norm_le_iff_of_nonneg (by norm_num)]
  intro i
  fin_cases i <;> norm_num [Real.norm_eq_abs]

end
end LeanOEM.Tests.TwoLayerState
