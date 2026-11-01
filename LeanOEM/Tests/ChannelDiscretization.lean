module

public import LeanOEM.Physics.ChannelDiscretization
public import LeanOEM.Physics.FiniteLayerDiscretization
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-!
# 通道响应离散化测试

该 fixture 使用两个频率样本，把有限层输出、通道权重误差和标量 Jacobian 误差组合起来。
所有数值均为精确有理数。
-/

@[expose] public section

namespace LeanOEM.Tests.ChannelDiscretization

open LeanOEM
open LeanOEM.NonlinearProblem
open LeanOEM.RadiativeTransfer

noncomputable section

private def exactResponse : ChannelResponse 2 where
  weights := ![(3 / 4 : ℝ), (1 / 4 : ℝ)]
  nonneg := by
    intro i
    fin_cases i <;> norm_num
  normalized := by
    norm_num [Fin.sum_univ_succ]

private def approximateResponse : ChannelResponse 2 where
  weights := ![(7 / 10 : ℝ), (3 / 10 : ℝ)]
  nonneg := by
    intro i
    fin_cases i <;> norm_num
  normalized := by
    norm_num [Fin.sum_univ_succ]

private def exactLayerParameters : Fin 2 → TwoLayerSourceParameters :=
  ![{ firstTransmissivity := 1 / 2
      secondTransmissivity := 3 / 4
      incoming := 2 },
    { firstTransmissivity := 2 / 5
      secondTransmissivity := 4 / 5
      incoming := 2 }]

private def approximateLayerParameters : Fin 2 → TwoLayerSourceParameters :=
  ![{ firstTransmissivity := 3 / 5
      secondTransmissivity := 7 / 10
      incoming := 2 },
    { firstTransmissivity := 1 / 2
      secondTransmissivity := 7 / 10
      incoming := 2 }]

private def target : State 1 := ![(1 / 2 : ℝ)]

private def exactValues : Fin 2 → ℝ := ![(17 / 16 : ℝ), (49 / 50 : ℝ)]

private def approximateValues : Fin 2 → ℝ :=
  ![(113 / 100 : ℝ), (41 / 40 : ℝ)]

private def exactSensitivities : Fin 2 → ℝ :=
  ![(5 / 8 : ℝ), (17 / 25 : ℝ)]

private def approximateSensitivities : Fin 2 → ℝ :=
  ![(29 / 50 : ℝ), (13 / 20 : ℝ)]

private def channelProblem : NonlinearProblem 1 1 where
  model := twoLayerSourceModel (exactLayerParameters 0)
  observation := ![0]
  priorMean := ![0]
  priorWeight := !![1]
  observationWeight := !![1]

private lemma exact_values_from_finite_layer :
    exactValues = fun i =>
      (twoLayerSourceObserve (exactLayerParameters i) target) 0 := by
  funext i
  fin_cases i <;>
    norm_num [exactValues, exactLayerParameters, target,
      twoLayerSourceObserve, twoLayerSourceCoefficient]

private lemma approximate_values_from_finite_layer :
    approximateValues = fun i =>
      (twoLayerSourceObserve (approximateLayerParameters i) target) 0 := by
  funext i
  fin_cases i <;>
    norm_num [approximateValues, approximateLayerParameters, target,
      twoLayerSourceObserve, twoLayerSourceCoefficient]

private lemma exact_sensitivities_from_finite_layer :
    exactSensitivities = fun i =>
      twoLayerSourceCoefficient (exactLayerParameters i) := by
  funext i
  fin_cases i <;>
    norm_num [exactSensitivities, exactLayerParameters,
      twoLayerSourceCoefficient]

private lemma approximate_sensitivities_from_finite_layer :
    approximateSensitivities = fun i =>
      twoLayerSourceCoefficient (approximateLayerParameters i) := by
  funext i
  fin_cases i <;>
    norm_num [approximateSensitivities, approximateLayerParameters,
      twoLayerSourceCoefficient]

private lemma channel_weight_l1_error :
    approximateResponse.weightL1Error exactResponse = (1 / 10 : ℝ) := by
  norm_num [ChannelResponse.weightL1Error, approximateResponse, exactResponse,
    Fin.sum_univ_succ]

private lemma approximate_value_bound :
    ∀ i, |approximateValues i| ≤ (6 / 5 : ℝ) := by
  intro i
  fin_cases i <;> norm_num [approximateValues, abs_of_nonneg]

private lemma channel_value_error :
    ∀ i, |approximateValues i - exactValues i| ≤ (7 / 100 : ℝ) := by
  intro i
  fin_cases i <;> norm_num [approximateValues, exactValues, abs_of_nonneg]

/-- 通道权重和有限层谱值误差共同给出观测输出误差。 -/
example :
    |approximateResponse.apply approximateValues -
      exactResponse.apply exactValues| ≤ (19 / 100 : ℝ) := by
  have h := ChannelResponse.apply_error_le_of_weight_and_value
    approximateResponse exactResponse approximateValues exactValues
    (bound := (6 / 5 : ℝ)) (epsilon := (7 / 100 : ℝ))
    approximate_value_bound channel_value_error
  rw [channel_weight_l1_error] at h
  norm_num at h ⊢
  exact h

private lemma approximate_sensitivity_bound :
    ∀ i, |approximateSensitivities i| ≤ (1 : ℝ) := by
  intro i
  fin_cases i <;> norm_num [approximateSensitivities, abs_of_nonneg]

private lemma channel_sensitivity_error :
    ∀ i, |approximateSensitivities i - exactSensitivities i| ≤ (1 / 5 : ℝ) := by
  intro i
  fin_cases i <;>
    norm_num [approximateSensitivities, exactSensitivities, abs_of_nonneg]

/-- 通道 Jacobian 是有限层 Jacobian 灵敏度的加权和。 -/
example :
    |(channelJacobian approximateResponse approximateSensitivities) 0 0 -
      (channelJacobian exactResponse exactSensitivities) 0 0| ≤
      (3 / 10 : ℝ) := by
  have h := channelJacobian_coefficient_error_le
    approximateResponse exactResponse approximateSensitivities exactSensitivities
    (bound := (1 : ℝ)) (epsilon := (1 / 5 : ℝ))
    approximate_sensitivity_bound channel_sensitivity_error
  rw [channel_weight_l1_error] at h
  norm_num at h ⊢
  exact h

private lemma channel_jacobian_error :
    channelProblem.WeightedJacobianErrorBound
      (channelJacobian approximateResponse approximateSensitivities)
      (channelJacobian exactResponse exactSensitivities) (3 / 10 : ℝ) := by
  apply channelJacobian_weightedErrorBound_of_unitWeight
    channelProblem rfl
  have h := channelJacobian_coefficient_error_le
    approximateResponse exactResponse approximateSensitivities exactSensitivities
    (bound := (1 : ℝ)) (epsilon := (1 / 5 : ℝ))
    approximate_sensitivity_bound channel_sensitivity_error
  rw [channel_weight_l1_error] at h
  norm_num at h ⊢
  exact h

/-- 通道 Jacobian 误差已经进入通用 OEM 契约。 -/
example :
    channelProblem.WeightedJacobianErrorBound
      (channelJacobian approximateResponse approximateSensitivities)
      (channelJacobian exactResponse exactSensitivities) (3 / 10 : ℝ) :=
  channel_jacobian_error

end
end LeanOEM.Tests.ChannelDiscretization
