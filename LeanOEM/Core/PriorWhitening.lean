module

public import LeanOEM.Core.SpectralDiagnostics
public import LeanOEM.Core.Observability
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

/-!
# 先验因子化与 averaging kernel 的谱

给定可逆因子 `L` 和 `Sₐ = L Lᴴ`，白化坐标中的矩阵为
`B = (K L)ᴴ S⁻¹ (K L)`，满足 `A L = L B`。正定观测误差下，
`B` 半正定且 `I - B` 正定；相似关系把谱界传回通常不对称的 `A`。
正定先验可用 Mathlib 的矩阵平方根构造因子，不要求调用者另给分解。
-/

@[expose] public section

namespace LeanOEM

noncomputable section

/-- 先验协方差的可逆因子；允许平方根、Cholesky 等满足同一恒等式的因子。 -/
structure Problem.PriorFactor {n m : ℕ} (p : Problem n m) where
  matrix : Square n
  isUnit : IsUnit matrix
  covariance_eq : p.priorCovariance = matrix * matrix.conjTranspose

namespace Problem.PriorFactor

variable {n m : ℕ} {p : Problem n m}

open scoped MatrixOrder in
/-- 正定先验的半正定平方根给出可逆因子；这是精确实数构造。 -/
def ofPosDef (hPrior : p.priorCovariance.PosDef) : p.PriorFactor where
  matrix := CFC.sqrt p.priorCovariance
  isUnit := (CFC.isUnit_sqrt_iff _ hPrior.posSemidef.nonneg).mpr hPrior.isUnit
  covariance_eq := by
    have hSqrt : (CFC.sqrt p.priorCovariance).PosSemidef :=
      Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg p.priorCovariance)
    have hHermitian := hSqrt.isHermitian.eq
    rw [hHermitian, CFC.sqrt_mul_sqrt_self _ hPrior.posSemidef.nonneg]

/-- 因子恒等式本身给出先验的半正定性。 -/
theorem prior_posSemidef (f : p.PriorFactor) : p.priorCovariance.PosSemidef := by
  rw [f.covariance_eq]
  exact Matrix.posSemidef_self_mul_conjTranspose f.matrix

/-- 可逆因子进一步保证先验正定。 -/
theorem prior_posDef (f : p.PriorFactor) : p.priorCovariance.PosDef := by
  rw [f.covariance_eq]
  exact Matrix.PosDef.mul_conjTranspose_self f.matrix
    (Matrix.vecMul_injective_of_isUnit f.isUnit)

/-- 先验白化坐标中的 averaging kernel，方向为 `L⁻¹ A L`。 -/
def whitenedAveragingKernel (f : p.PriorFactor) : Square n :=
  (p.jacobian * f.matrix).conjTranspose * p.innovationCovariance⁻¹ *
    (p.jacobian * f.matrix)

/-- 原坐标与白化坐标的交织恒等式。 -/
theorem averagingKernel_mul_factor (f : p.PriorFactor) :
    averagingKernel p.gain p.jacobian * f.matrix =
      f.matrix * f.whitenedAveragingKernel := by
  simp only [averagingKernel, Problem.gain, whitenedAveragingKernel,
    f.covariance_eq, Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- 可逆因子使白化矩阵与原 averaging kernel 相似。 -/
theorem whitenedAveragingKernel_eq_conjugate (f : p.PriorFactor) :
    f.whitenedAveragingKernel =
      f.matrix⁻¹ * averagingKernel p.gain p.jacobian * f.matrix := by
  rw [Matrix.mul_assoc, f.averagingKernel_mul_factor, ← Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp f.isUnit),
    Matrix.one_mul]

/-- 相似矩阵具有相同的特征多项式，包含全部特征值及其代数重数。 -/
theorem charpoly_eq (f : p.PriorFactor) :
    (averagingKernel p.gain p.jacobian).charpoly =
      f.whitenedAveragingKernel.charpoly := by
  exact Matrix.charpoly_eq_of_mul_eq_mul
    ((Matrix.isUnit_iff_isUnit_det _).mp f.isUnit).ne_zero
    f.averagingKernel_mul_factor

/-- 观测误差正定时，白化 averaging kernel 半正定。 -/
theorem whitenedAveragingKernel_posSemidef (f : p.PriorFactor)
    (hObservation : p.observationErrorCovariance.PosDef) :
    f.whitenedAveragingKernel.PosSemidef := by
  exact (innovationCovariance_inv_posDef p f.prior_posSemidef hObservation).posSemidef
    |>.conjTranspose_mul_mul_same (p.jacobian * f.matrix)

/-- 可观测 Jacobian 下，白化 averaging kernel 正定，因而所有特征值严格为正。 -/
theorem whitenedAveragingKernel_posDef_of_observable (f : p.PriorFactor)
    (hObservation : p.observationErrorCovariance.PosDef)
    (hObservable : Observable p.jacobian) :
    f.whitenedAveragingKernel.PosDef := by
  apply Matrix.PosDef.conjTranspose_mul_mul_same
    (innovationCovariance_inv_posDef p f.prior_posSemidef hObservation)
  intro x y hxy
  have hFactor : Function.Injective f.matrix.mulVec :=
    Matrix.mulVec_injective_of_isUnit f.isUnit
  have hJacobian : p.jacobian.mulVec (f.matrix.mulVec x) =
      p.jacobian.mulVec (f.matrix.mulVec y) := by
    simpa [Matrix.mulVec_mulVec] using hxy
  exact hFactor (hObservable hJacobian)

/-- 使用单位先验的坐标问题，仅用于复用已有后验协方差定理。 -/
private def coordinateProblem (f : p.PriorFactor) : Problem n m where
  jacobian := p.jacobian * f.matrix
  priorMean := 0
  priorCovariance := 1
  observationErrorCovariance := p.observationErrorCovariance

private theorem coordinateProblem_innovation (f : p.PriorFactor) :
    f.coordinateProblem.innovationCovariance = p.innovationCovariance := by
  simp only [coordinateProblem, Problem.innovationCovariance, f.covariance_eq,
    Matrix.mul_one, Matrix.conjTranspose_mul, Matrix.mul_assoc]

private theorem coordinateProblem_posterior (f : p.PriorFactor) :
    posteriorCovariance f.coordinateProblem = 1 - f.whitenedAveragingKernel := by
  unfold posteriorCovariance
  rw [coordinateProblem_innovation]
  simp only [coordinateProblem,
    whitenedAveragingKernel, Matrix.one_mul, Matrix.mul_one]

/-- 白化矩阵的补矩阵是单位先验问题的后验协方差，因而正定。 -/
theorem one_sub_whitenedAveragingKernel_posDef (f : p.PriorFactor)
    (hObservation : p.observationErrorCovariance.PosDef) :
    (1 - f.whitenedAveragingKernel).PosDef := by
  rw [← f.coordinateProblem_posterior]
  exact posteriorCovariance_posDef f.coordinateProblem Matrix.PosDef.one hObservation

/-- 按状态维数索引的白化实特征值；原矩阵通过相似关系共享这些特征值。 -/
def eigenvalues (f : p.PriorFactor)
    (hObservation : p.observationErrorCovariance.PosDef) : Fin n → ℝ :=
  (f.whitenedAveragingKernel_posSemidef hObservation).isHermitian.eigenvalues

/-- 最优增益的每个白化特征值属于 `[0, 1]`。 -/
theorem eigenvalues_bounds (f : p.PriorFactor)
    (hObservation : p.observationErrorCovariance.PosDef) (i : Fin n) :
    0 ≤ f.eigenvalues hObservation i ∧ f.eigenvalues hObservation i ≤ 1 := by
  exact eigenvalues_bounds_of_posSemidef f.whitenedAveragingKernel
    (f.whitenedAveragingKernel_posSemidef hObservation)
    (f.one_sub_whitenedAveragingKernel_posDef hObservation).posSemidef i

/-- 可观测 Jacobian 下，白化 averaging kernel 的每个特征值严格为正。 -/
theorem eigenvalues_pos_of_observable (f : p.PriorFactor)
    (hObservation : p.observationErrorCovariance.PosDef)
    (hObservable : Observable p.jacobian) (i : Fin n) :
    0 < f.eigenvalues hObservation i := by
  exact (f.whitenedAveragingKernel_posDef_of_observable hObservation hObservable).eigenvalues_pos i

/-- 白化 averaging kernel 的矩阵秩不超过 Jacobian 的矩阵秩。 -/
theorem whitenedAveragingKernel_rank_le (f : p.PriorFactor) :
    f.whitenedAveragingKernel.rank ≤ p.jacobian.rank := by
  let c : Matrix (Fin m) (Fin n) ℝ := p.jacobian * f.matrix
  have hRank : f.whitenedAveragingKernel.rank ≤ c.rank := by
    simpa [whitenedAveragingKernel, c, Matrix.mul_assoc] using
      (Matrix.rank_mul_le_right
        ((p.jacobian * f.matrix).conjTranspose * p.innovationCovariance⁻¹)
        (p.jacobian * f.matrix))
  have hC : c.rank ≤ p.jacobian.rank := by
    dsimp [c]
    exact Matrix.rank_mul_le_left _ _
  exact hRank.trans hC

/-- 原 averaging kernel 的实谱恰好是白化矩阵特征值的取值集合。 -/
theorem spectrum_eq_range_eigenvalues (f : p.PriorFactor)
    (hObservation : p.observationErrorCovariance.PosDef) :
    spectrum ℝ (averagingKernel p.gain p.jacobian) =
      Set.range (f.eigenvalues hObservation) := by
  have hSpectrum : spectrum ℝ (averagingKernel p.gain p.jacobian) =
      spectrum ℝ f.whitenedAveragingKernel := by
    ext r
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly,
      Matrix.mem_spectrum_iff_isRoot_charpoly, f.charpoly_eq]
  exact hSpectrum.trans
    (f.whitenedAveragingKernel_posSemidef hObservation).isHermitian.spectrum_real_eq_range_eigenvalues

/-- 原 averaging kernel 的特征多项式在实数上完全分裂，不遗漏非实根。 -/
theorem charpoly_splits (f : p.PriorFactor)
    (hObservation : p.observationErrorCovariance.PosDef) :
    (averagingKernel p.gain p.jacobian).charpoly.Splits := by
  rw [f.charpoly_eq]
  exact (f.whitenedAveragingKernel_posSemidef hObservation).isHermitian.splits_charpoly

/-- DOFS 等于白化矩阵的特征值之和，按重数计数。 -/
theorem dofs_eq_sum_eigenvalues (f : p.PriorFactor)
    (hObservation : p.observationErrorCovariance.PosDef) :
    p.dofs = ∑ i, f.eigenvalues hObservation i := by
  have hTrace : p.dofs = f.whitenedAveragingKernel.trace := by
    simp only [Problem.dofs, LeanOEM.dofs, f.whitenedAveragingKernel_eq_conjugate]
    rw [Matrix.trace_mul_cycle,
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp f.isUnit),
      Matrix.one_mul]
  exact hTrace.trans
    (f.whitenedAveragingKernel_posSemidef hObservation).isHermitian.trace_eq_sum_eigenvalues

end Problem.PriorFactor

/-- 正定先验和观测误差协方差下，最优增益 averaging kernel 的实谱包含于 `[0, 1]`。 -/
theorem Problem.averagingKernel_spectrum_subset_Icc {n m : ℕ}
    (p : Problem n m) (hPrior : p.priorCovariance.PosDef)
    (hObservation : p.observationErrorCovariance.PosDef) :
    spectrum ℝ (averagingKernel p.gain p.jacobian) ⊆ Set.Icc (0 : ℝ) 1 := by
  let f := Problem.PriorFactor.ofPosDef hPrior
  rw [f.spectrum_eq_range_eigenvalues hObservation]
  rintro r ⟨i, rfl⟩
  exact f.eigenvalues_bounds hObservation i

/-- 正定 OEM 条件下，原 averaging kernel 的全部特征值都是实数。 -/
theorem Problem.averagingKernel_charpoly_splits {n m : ℕ}
    (p : Problem n m) (hPrior : p.priorCovariance.PosDef)
    (hObservation : p.observationErrorCovariance.PosDef) :
    (averagingKernel p.gain p.jacobian).charpoly.Splits :=
  (Problem.PriorFactor.ofPosDef hPrior).charpoly_splits hObservation

end
end LeanOEM
