module

public import LeanOEM.Physics.FiniteLayer
public import Mathlib.Tactic

@[expose] public section

namespace LeanOEM.Tests.FiniteLayer

open LeanOEM.RadiativeTransfer

noncomputable section

private def firstLayer : Layer :=
  { transmissivity := 1 / 2
    source := 4 }

private def secondLayer : Layer :=
  { transmissivity := 3 / 4
    source := 2 }

private lemma firstLayer_valid : firstLayer.Valid := by
  constructor <;> norm_num [firstLayer]

private lemma secondLayer_valid : secondLayer.Valid := by
  constructor <;> norm_num [secondLayer]

/-- 单层递推的精确数值例子。 -/
example : firstLayer.propagate 2 = 3 := by
  norm_num [Layer.propagate, firstLayer]

/-- 有效层保持非负辐亮度。 -/
example : 0 ≤ firstLayer.propagate (-0 : ℝ) :=
  firstLayer_valid.propagate_nonneg (by norm_num)

/-- 有效层保持由输入和源项共同给出的上界。 -/
example : firstLayer.propagate 2 ≤ 4 := by
  apply firstLayer_valid.propagate_le_of_le
  · norm_num
  · norm_num [firstLayer]

/-- 两层传播的精确结果。 -/
example : propagateTwo firstLayer secondLayer 2 = (11 / 4 : ℝ) := by
  norm_num [propagateTwo, Layer.propagate, firstLayer, secondLayer]

/-- 有效层列表保持非负性和上界。 -/
example :
    0 ≤ propagateLayers [firstLayer, secondLayer] 2 ∧
      propagateLayers [firstLayer, secondLayer] 2 ≤ 4 := by
  apply propagateLayers_bounds
  · intro layer hLayer
    rcases List.mem_cons.mp hLayer with hFirst | hSecond
    · subst layer
      exact firstLayer_valid
    · have hSecond' : layer = secondLayer := List.mem_singleton.mp hSecond
      subst layer
      exact secondLayer_valid
  · norm_num
  · norm_num
  · intro layer hLayer
    rcases List.mem_cons.mp hLayer with hFirst | hSecond
    · subst layer
      norm_num [firstLayer]
    · have hSecond' : layer = secondLayer := List.mem_singleton.mp hSecond
      subst layer
      norm_num [secondLayer]

end
end LeanOEM.Tests.FiniteLayer
