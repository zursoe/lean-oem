module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Tactic

@[expose] public section

namespace LeanOEM.RadiativeTransfer

open scoped BigOperators

noncomputable section

/-- 归一化 Planck 辐亮度函数；常数和自变量的单位由调用者另行说明。 -/
def planckRadiance (h c k frequency temperature : ℝ) : ℝ :=
  (2 * h * frequency ^ 3) /
    (c ^ 2 * (Real.exp (h * frequency / (k * temperature)) - 1))

theorem planckRadiance_pos {h c k frequency temperature : ℝ}
    (hPlanck : 0 < h) (hLightSpeed : 0 < c) (hBoltzmann : 0 < k)
    (hFrequency : 0 < frequency) (hTemperature : 0 < temperature) :
    0 < planckRadiance h c k frequency temperature := by
  have hNumerator : 0 < 2 * h * frequency ^ 3 := by
    exact mul_pos (mul_pos (by norm_num) hPlanck) (pow_pos hFrequency 3)
  have hArgument : 0 < h * frequency / (k * temperature) := by
    exact div_pos (mul_pos hPlanck hFrequency) (mul_pos hBoltzmann hTemperature)
  have hExponential : 0 < Real.exp (h * frequency / (k * temperature)) - 1 := by
    have hExp : Real.exp 0 < Real.exp (h * frequency / (k * temperature)) :=
      Real.exp_strictMono hArgument
    simpa [Real.exp_zero] using hExp
  have hDenominator : 0 < c ^ 2 * (Real.exp (h * frequency / (k * temperature)) - 1) :=
    mul_pos (sq_pos_of_pos hLightSpeed) hExponential
  exact div_pos hNumerator hDenominator

/-- 一阶 Doppler 频移的无量纲形式。 -/
def dopplerShift (frequency velocity lightSpeed : ℝ) : ℝ :=
  frequency * (1 - velocity / lightSpeed)

theorem dopplerShift_zero (frequency lightSpeed : ℝ) :
    dopplerShift frequency 0 lightSpeed = frequency := by
  simp [dopplerShift]

theorem dopplerShift_expand (frequency velocity lightSpeed : ℝ) :
    dopplerShift frequency velocity lightSpeed =
      frequency - frequency * velocity / lightSpeed := by
  unfold dopplerShift
  ring

theorem dopplerShift_pos {frequency velocity lightSpeed : ℝ}
    (hFrequency : 0 < frequency) (hVelocity : velocity < lightSpeed)
    (hLightSpeed : 0 < lightSpeed) :
    0 < dopplerShift frequency velocity lightSpeed := by
  have hRatio : velocity / lightSpeed < 1 :=
    (div_lt_iff₀ hLightSpeed).2 (by simpa [one_mul] using hVelocity)
  exact mul_pos hFrequency (sub_pos.mpr hRatio)

/-- 归一化有限通道响应的非负归一化权重。 -/
structure ChannelResponse (n : ℕ) where
  weights : Fin n → ℝ
  nonneg : ∀ i, 0 ≤ weights i
  normalized : ∑ i, weights i = 1

namespace ChannelResponse

/-- 对有限通道响应做加权求和。 -/
def apply (response : ChannelResponse n) (values : Fin n → ℝ) : ℝ :=
  ∑ i, response.weights i * values i

theorem apply_nonneg (response : ChannelResponse n) (values : Fin n → ℝ)
    (hValues : ∀ i, 0 ≤ values i) :
    0 ≤ response.apply values := by
  unfold apply
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (response.nonneg i) (hValues i))

theorem apply_le_of_le (response : ChannelResponse n) (values : Fin n → ℝ)
    {upper : ℝ} (hValues : ∀ i, values i ≤ upper) :
    response.apply values ≤ upper := by
  unfold apply
  calc
    (∑ i, response.weights i * values i)
        ≤ ∑ i, response.weights i * upper := by
          exact Finset.sum_le_sum (fun i _ =>
            mul_le_mul_of_nonneg_left (hValues i) (response.nonneg i))
    _ = upper := by
      rw [← Finset.sum_mul, response.normalized]
      ring

theorem apply_const (response : ChannelResponse n) (value : ℝ) :
    response.apply (fun _ => value) = value := by
  unfold apply
  change (∑ i, response.weights i * value) = value
  rw [← Finset.sum_mul, response.normalized]
  ring

end ChannelResponse

end
end LeanOEM.RadiativeTransfer
