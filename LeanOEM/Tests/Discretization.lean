module

public import LeanOEM.Physics.Discretization
public import Mathlib.Tactic

@[expose] public section

namespace LeanOEM.Tests.Discretization

open LeanOEM.RadiativeTransfer

/-- 二次函数的中心有限差分精确恢复一阶导数。 -/
example (x h : ℝ) (hStep : 0 < h) :
    |centralDifference (fun z => z ^ 2) x h - 2 * x| ≤ 0 := by
  have hBound :
      |centralDifference (fun z => z ^ 2) x h - 2 * x| ≤ 0 * h ^ 2 := by
    apply centralDifference_error_bound (f := fun z => z ^ 2) (x := x) (h := h)
      (derivative := 2 * x) (quadratic := 1) (rPlus := 0) (rMinus := 0) (C := 0)
    · exact hStep
    · ring
    · ring
    · simp
    · simp
  simpa using hBound

end LeanOEM.Tests.Discretization
