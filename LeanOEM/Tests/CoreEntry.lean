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

example {n : ℕ} (A : Square n) (hA : A.PosSemidef)
    (hComplement : ((1 : Square n) - A).PosSemidef) (i : Fin n) :
    0 ≤ hA.isHermitian.eigenvalues i ∧ hA.isHermitian.eigenvalues i ≤ 1 := by
  exact eigenvalues_bounds_of_posSemidef A hA hComplement i

/-- 核心入口同时提供原 averaging kernel 的谱界和实数分裂结论。 -/
example {n m : ℕ} (p : Problem n m)
    (hPrior : p.priorCovariance.PosDef)
    (hObservation : p.observationErrorCovariance.PosDef) :
    spectrum ℝ (averagingKernel p.gain p.jacobian) ⊆ Set.Icc (0 : ℝ) 1 ∧
      (averagingKernel p.gain p.jacobian).charpoly.Splits :=
  ⟨p.averagingKernel_spectrum_subset_Icc hPrior hObservation,
    p.averagingKernel_charpoly_splits hPrior hObservation⟩

example {n m : ℕ} (p : Problem n m) (f : p.PriorFactor) :
    f.whitenedAveragingKernel.rank ≤ p.jacobian.rank :=
  f.whitenedAveragingKernel_rank_le

example {n m : ℕ} (p : Problem n m) (f : p.PriorFactor)
    (hObservation : p.observationErrorCovariance.PosDef) :
    f.whitenedAveragingKernel.rank = p.jacobian.rank :=
  f.whitenedAveragingKernel_rank_eq hObservation

example {n m : ℕ} (p : Problem n m) (f : p.PriorFactor)
    (hObservation : p.observationErrorCovariance.PosDef) (v : State n) :
    f.whitenedAveragingKernel.mulVec v = 0 ↔
      p.jacobian.mulVec (f.matrix.mulVec v) = 0 :=
  f.whitenedAveragingKernel_mulVec_eq_zero_iff_jacobian hObservation v

example {n m : ℕ} (p : Problem n m) (f : p.PriorFactor)
    (hObservation : p.observationErrorCovariance.PosDef)
    (hObservable : Observable p.jacobian) (i : Fin n) :
    0 < f.eigenvalues hObservation i :=
  f.eigenvalues_pos_of_observable hObservation hObservable i

end LeanOEM.Tests.CoreEntry
