module

public import LeanOEM.Core.DiscretizationError
public import LeanOEM.Physics.Spectral
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-!
# 有限通道响应离散化

本模块把有限频率网格上的通道响应误差写成精确实数契约。
权重误差使用有限和的 `L¹` 界，谱值误差使用逐点绝对误差界；两者都可以
直接提升为标量通道 Jacobian 的 OEM 误差契约。
-/

@[expose] public section

namespace LeanOEM.RadiativeTransfer

open LeanOEM
open LeanOEM.NonlinearProblem

noncomputable section

namespace ChannelResponse

/-- 有限频率样本的统一步长误差契约：逐点误差不超过 `constant * step ^ order`。 -/
def ValueStepErrorBound (approximate exact : Fin n → ℝ)
    (constant step : ℝ) (order : ℕ) : Prop :=
  ∀ i, |approximate i - exact i| ≤ constant * step ^ order

/-- 两个有限通道响应权重的 `L¹` 误差。 -/
def weightL1Error (approximate exact : ChannelResponse n) : ℝ :=
  ∑ i, |approximate.weights i - exact.weights i|

@[simp] theorem weightL1Error_self (response : ChannelResponse n) :
    response.weightL1Error response = 0 := by
  simp [weightL1Error]

/-- 固定谱值下，通道权重误差给出的输出误差界。 -/
theorem apply_error_le_of_weightL1
    (approximate exact : ChannelResponse n) (values : Fin n → ℝ)
    {bound : ℝ} (hValues : ∀ i, |values i| ≤ bound) :
    |approximate.apply values - exact.apply values| ≤
      bound * approximate.weightL1Error exact := by
  unfold apply weightL1Error
  calc
    |(∑ i, approximate.weights i * values i) -
        ∑ i, exact.weights i * values i| =
        |∑ i, (approximate.weights i - exact.weights i) * values i| := by
      congr 1
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ ∑ i, |(approximate.weights i - exact.weights i) * values i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |approximate.weights i - exact.weights i| * |values i| := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [abs_mul]
    _ ≤ ∑ i, |approximate.weights i - exact.weights i| * bound := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hValues i) (abs_nonneg _)
    _ = bound * ∑ i, |approximate.weights i - exact.weights i| := by
      rw [← Finset.sum_mul]
      ring

/-- 固定通道响应下，逐点谱值误差给出的输出误差界。 -/
theorem apply_error_le_of_value_error
    (response : ChannelResponse n) (approximateValues exactValues : Fin n → ℝ)
    {epsilon : ℝ}
    (hValues : ∀ i, |approximateValues i - exactValues i| ≤ epsilon) :
    |response.apply approximateValues - response.apply exactValues| ≤ epsilon := by
  unfold apply
  calc
    |(∑ i, response.weights i * approximateValues i) -
        ∑ i, response.weights i * exactValues i| =
        |∑ i, response.weights i *
          (approximateValues i - exactValues i)| := by
      congr 1
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ ∑ i, |response.weights i *
        (approximateValues i - exactValues i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, response.weights i *
        |approximateValues i - exactValues i| := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [abs_mul, abs_of_nonneg (response.nonneg i)]
    _ ≤ ∑ i, response.weights i * epsilon := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hValues i) (response.nonneg i)
    _ = epsilon := by
      rw [← Finset.sum_mul, response.normalized]
      ring

/-- 将逐点 `C · h^p` 误差提升为通道输出的同阶误差。 -/
theorem apply_error_le_of_valueStepError
    (response : ChannelResponse n) (approximateValues exactValues : Fin n → ℝ)
    (constant step : ℝ) (order : ℕ)
    (hError : ValueStepErrorBound approximateValues exactValues constant step order) :
    |response.apply approximateValues - response.apply exactValues| ≤
      constant * step ^ order := by
  unfold ValueStepErrorBound at hError
  exact response.apply_error_le_of_value_error approximateValues exactValues hError

/-- 权重误差和谱值误差的组合界。 -/
theorem apply_error_le_of_weight_and_value
    (approximate exact : ChannelResponse n)
    (approximateValues exactValues : Fin n → ℝ)
    {bound epsilon : ℝ}
    (hApproximateValues : ∀ i, |approximateValues i| ≤ bound)
    (hValueError : ∀ i, |approximateValues i - exactValues i| ≤ epsilon) :
    |approximate.apply approximateValues - exact.apply exactValues| ≤
      bound * approximate.weightL1Error exact + epsilon := by
  calc
    |approximate.apply approximateValues - exact.apply exactValues| ≤
        |approximate.apply approximateValues - exact.apply approximateValues| +
          |exact.apply approximateValues - exact.apply exactValues| := by
      calc
        |approximate.apply approximateValues - exact.apply exactValues| =
            |(approximate.apply approximateValues - exact.apply approximateValues) +
              (exact.apply approximateValues - exact.apply exactValues)| := by
              congr 1
              ring
        _ ≤ |approximate.apply approximateValues - exact.apply approximateValues| +
            |exact.apply approximateValues - exact.apply exactValues| :=
          abs_add_le _ _
    _ ≤ bound * approximate.weightL1Error exact + epsilon := by
      exact add_le_add
        (approximate.apply_error_le_of_weightL1 exact approximateValues
          hApproximateValues)
        (exact.apply_error_le_of_value_error approximateValues exactValues
          hValueError)

end ChannelResponse

/-- 由有限频率灵敏度加权得到的一维通道 Jacobian。 -/
def channelJacobian (response : ChannelResponse n)
    (sensitivities : Fin n → ℝ) : Jacobian 1 1 :=
  !![response.apply sensitivities]

private theorem channelStateOneNorm (a : ℝ) : ‖(![a] : State 1)‖ = |a| := by
  have h : (![a] : State 1) = fun _ => a := by
    ext i
    fin_cases i
    rfl
  rw [h, pi_norm_const, Real.norm_eq_abs]

/-- 通道 Jacobian 系数的组合误差界。 -/
theorem channelJacobian_coefficient_error_le
    (approximate exact : ChannelResponse n)
    (approximateSensitivities exactSensitivities : Fin n → ℝ)
    {bound epsilon : ℝ}
    (hApproximateSensitivities : ∀ i, |approximateSensitivities i| ≤ bound)
    (hSensitivityError : ∀ i,
      |approximateSensitivities i - exactSensitivities i| ≤ epsilon) :
    |(channelJacobian approximate approximateSensitivities) 0 0 -
      (channelJacobian exact exactSensitivities) 0 0| ≤
      bound * approximate.weightL1Error exact + epsilon := by
  change |approximate.apply approximateSensitivities -
    exact.apply exactSensitivities| ≤ _
  exact approximate.apply_error_le_of_weight_and_value exact
    approximateSensitivities exactSensitivities
    hApproximateSensitivities hSensitivityError

/-- 统一步长误差契约给出通道 Jacobian 的同阶系数误差。 -/
theorem channelJacobian_coefficient_error_le_of_valueStepError
    (response : ChannelResponse n)
    (approximateSensitivities exactSensitivities : Fin n → ℝ)
    (constant step : ℝ) (order : ℕ)
    (hError : ChannelResponse.ValueStepErrorBound approximateSensitivities
      exactSensitivities constant step order) :
    |(channelJacobian response approximateSensitivities) 0 0 -
      (channelJacobian response exactSensitivities) 0 0| ≤
      constant * step ^ order := by
  change |response.apply approximateSensitivities -
    response.apply exactSensitivities| ≤ _
  exact response.apply_error_le_of_valueStepError approximateSensitivities
    exactSensitivities constant step order hError

/-- 标量通道 Jacobian 系数误差给出单位观测权重下的作用界。 -/
theorem channelJacobian_weightedErrorBound_unit
    (approximate exact : ChannelResponse n)
    (approximateSensitivities exactSensitivities : Fin n → ℝ)
    {epsilon : ℝ}
    (hCoefficient :
      |(channelJacobian approximate approximateSensitivities) 0 0 -
        (channelJacobian exact exactSensitivities) 0 0| ≤ epsilon) :
    ∀ v : Observation 1,
      ‖(channelJacobian approximate approximateSensitivities).conjTranspose.mulVec
          ((!![1] : Square 1).mulVec v) -
        (channelJacobian exact exactSensitivities).conjTranspose.mulVec
          ((!![1] : Square 1).mulVec v)‖ ≤ epsilon * ‖v‖ := by
  intro v
  have hV : v = ![v 0] := by
    ext i
    fin_cases i
    rfl
  rw [hV]
  have hEq :
      (channelJacobian approximate approximateSensitivities).conjTranspose.mulVec
          ((!![1] : Square 1).mulVec ![v 0]) -
        (channelJacobian exact exactSensitivities).conjTranspose.mulVec
          ((!![1] : Square 1).mulVec ![v 0]) =
        ![((channelJacobian approximate approximateSensitivities) 0 0 -
          (channelJacobian exact exactSensitivities) 0 0) * v 0] := by
    ext i
    fin_cases i
    simp [channelJacobian, Matrix.conjTranspose, Matrix.transpose,
      Matrix.mulVec, Matrix.vecHead, dotProduct]
    ring
  rw [hEq, channelStateOneNorm, channelStateOneNorm, abs_mul]
  exact mul_le_mul_of_nonneg_right hCoefficient (abs_nonneg _)

/-- 将通道 Jacobian 误差提升为 OEM 的单位观测权重契约。 -/
theorem channelJacobian_weightedErrorBound_of_unitWeight
    (p : NonlinearProblem 1 1) (hWeight : p.observationWeight = !![1])
    (approximate exact : ChannelResponse n)
    (approximateSensitivities exactSensitivities : Fin n → ℝ)
    {epsilon : ℝ}
    (hCoefficient :
      |(channelJacobian approximate approximateSensitivities) 0 0 -
        (channelJacobian exact exactSensitivities) 0 0| ≤ epsilon) :
    p.WeightedJacobianErrorBound
      (channelJacobian approximate approximateSensitivities)
      (channelJacobian exact exactSensitivities) epsilon := by
  unfold WeightedJacobianErrorBound
  intro v
  rw [hWeight]
  exact channelJacobian_weightedErrorBound_unit approximate exact
    approximateSensitivities exactSensitivities hCoefficient v

/-- 将有限频率样本的步长误差直接提升为 OEM Jacobian 误差契约。 -/
theorem channelJacobian_weightedErrorBound_of_valueStepError
    (p : NonlinearProblem 1 1) (hWeight : p.observationWeight = !![1])
    (response : ChannelResponse n)
    (approximateSensitivities exactSensitivities : Fin n → ℝ)
    (constant step : ℝ) (order : ℕ)
    (hError : ChannelResponse.ValueStepErrorBound approximateSensitivities
      exactSensitivities constant step order) :
    p.WeightedJacobianErrorBound
      (channelJacobian response approximateSensitivities)
      (channelJacobian response exactSensitivities)
      (constant * step ^ order) := by
  apply channelJacobian_weightedErrorBound_of_unitWeight p hWeight
    response response approximateSensitivities exactSensitivities
  exact channelJacobian_coefficient_error_le_of_valueStepError response
    approximateSensitivities exactSensitivities constant step order hError

end
end LeanOEM.RadiativeTransfer
