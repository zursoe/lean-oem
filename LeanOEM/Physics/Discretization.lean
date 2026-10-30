module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic

@[expose] public section

namespace LeanOEM.RadiativeTransfer

noncomputable section

/-- 一元函数的中心有限差分。 -/
def centralDifference (f : ℝ → ℝ) (x h : ℝ) : ℝ :=
  (f (x + h) - f (x - h)) / (2 * h)

/--
在显式三阶余项展开下，中心有限差分恢复一阶导数加余项。

`rPlus` 和 `rMinus` 是正、负扰动处的余项；该定理只使用代数展开，
不把数值函数或浮点实现自动当作满足这些条件。
-/
theorem centralDifference_eq_derivative_add_remainder
    (f : ℝ → ℝ) (x h derivative quadratic rPlus rMinus : ℝ)
    (hStep : 0 < h)
    (hPlus : f (x + h) = f x + derivative * h + quadratic * h ^ 2 + rPlus)
    (hMinus : f (x - h) = f x - derivative * h + quadratic * h ^ 2 + rMinus) :
    centralDifference f x h = derivative + (rPlus - rMinus) / (2 * h) := by
  unfold centralDifference
  rw [hPlus, hMinus]
  field_simp [ne_of_gt hStep]
  ring

/--
中心有限差分的二阶误差界。

当两侧余项都被 `C * h^3` 控制时，中心差分相对一阶导数的误差
不超过 `C * h^2`。
-/
theorem centralDifference_error_bound
    (f : ℝ → ℝ) (x h derivative quadratic rPlus rMinus C : ℝ)
    (hStep : 0 < h)
    (hPlus : f (x + h) = f x + derivative * h + quadratic * h ^ 2 + rPlus)
    (hMinus : f (x - h) = f x - derivative * h + quadratic * h ^ 2 + rMinus)
    (hPlusBound : |rPlus| ≤ C * h ^ 3)
    (hMinusBound : |rMinus| ≤ C * h ^ 3) :
    |centralDifference f x h - derivative| ≤ C * h ^ 2 := by
  have hRemainder : |rPlus - rMinus| ≤ 2 * C * h ^ 3 := by
    rcases (abs_le.mp hPlusBound) with ⟨hPlusLower, hPlusUpper⟩
    rcases (abs_le.mp hMinusBound) with ⟨hMinusLower, hMinusUpper⟩
    apply (abs_le).2
    constructor <;> nlinarith
  rw [centralDifference_eq_derivative_add_remainder f x h derivative quadratic rPlus rMinus
    hStep hPlus hMinus]
  have hDenominator : 0 < 2 * h := by positivity
  calc
    |derivative + (rPlus - rMinus) / (2 * h) - derivative| =
        |rPlus - rMinus| / (2 * h) := by
          rw [add_sub_cancel_left, abs_div, abs_of_pos hDenominator]
    _ ≤ (2 * C * h ^ 3) / (2 * h) := by
          exact div_le_div_of_nonneg_right hRemainder hDenominator.le
    _ = C * h ^ 2 := by
          field_simp [ne_of_gt hStep]

end
end LeanOEM.RadiativeTransfer
