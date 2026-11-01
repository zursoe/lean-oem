module

public import LeanOEM.Core
import Mathlib.Tactic

/-!
# Core 稳定入口 smoke test

该文件只导入 `LeanOEM.Core`，用于检查稳定核心可以脱离实验性 Physics 模块独立使用。
-/

@[expose] public section

namespace LeanOEM.Tests.CoreEntry

open LeanOEM

example {n m : ℕ} (p : Problem n m)
    (hPrior : p.priorCovariance.PosSemidef)
    (hObservation : p.observationErrorCovariance.PosDef) :
    p.innovationCovariance.PosDef := by
  exact innovationCovariance_posDef p hPrior hObservation

example {n m : ℕ} (p : Problem n m)
    (hPrior : p.priorCovariance.PosDef)
    (hObservation : p.observationErrorCovariance.PosDef) :
    (informationMatrix p).PosDef := by
  exact informationMatrix_posDef p hPrior hObservation

example {n m : ℕ} (g : Matrix (Fin n) (Fin m) ℝ) (k : Jacobian n m)
    (hA : (averagingKernel g k).PosSemidef)
    (hComplement : ((1 : Square n) - averagingKernel g k).PosSemidef) :
    0 ≤ dofs g k ∧ dofs g k ≤ (n : ℝ) := by
  exact dofs_bounds_of_averagingKernel_posSemidef g k hA hComplement

example {n m : ℕ} (p : Problem n m)
    (hPrior : p.priorCovariance.PosDef)
    (hObservation : p.observationErrorCovariance.PosDef) :
    0 ≤ p.dofs ∧ p.dofs ≤ (n : ℝ) := by
  exact p.dofs_bounds_of_posDef hPrior hObservation

end LeanOEM.Tests.CoreEntry
