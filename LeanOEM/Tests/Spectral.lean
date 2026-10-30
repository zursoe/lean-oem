module

public import LeanOEM.Physics.Spectral
public import Mathlib.Tactic

@[expose] public section

namespace LeanOEM.Tests.Spectral

open LeanOEM.RadiativeTransfer
open scoped BigOperators

noncomputable section

/-- 正参数下 Planck 模型的辐亮度为正。 -/
example : 0 < planckRadiance 1 1 1 1 1 := by
  apply planckRadiance_pos <;> norm_num

/-- 零速度时 Doppler 频移保持原频率。 -/
example : dopplerShift 3 0 2 = 3 := by
  norm_num [dopplerShift]

/-- 在速度小于光速的条件下，正频率的 Doppler 频率保持为正。 -/
example : 0 < dopplerShift 2 1 3 := by
  apply dopplerShift_pos <;> norm_num

private def twoChannelResponse : ChannelResponse 2 where
  weights := ![1 / 4, 3 / 4]
  nonneg := by
    intro i
    fin_cases i <;> norm_num
  normalized := by
    norm_num [Fin.sum_univ_succ]

/-- 两通道加权响应的精确值。 -/
example : twoChannelResponse.apply (![2, 6] : Fin 2 → ℝ) = 5 := by
  norm_num [ChannelResponse.apply, twoChannelResponse, Fin.sum_univ_succ]

/-- 非负通道量的加权响应保持非负。 -/
example : 0 ≤ twoChannelResponse.apply (![2, 6] : Fin 2 → ℝ) := by
  apply ChannelResponse.apply_nonneg
  intro i
  fin_cases i <;> norm_num

/-- 通道加权响应保持逐通道上界。 -/
example : twoChannelResponse.apply (![2, 6] : Fin 2 → ℝ) ≤ 6 := by
  apply ChannelResponse.apply_le_of_le
  intro i
  fin_cases i <;> norm_num

/-- 归一化响应对常量输入保持该常量。 -/
example : twoChannelResponse.apply (fun _ => (7 : ℝ)) = 7 := by
  exact ChannelResponse.apply_const twoChannelResponse 7

end
end LeanOEM.Tests.Spectral
