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

open scoped MatrixOrder BigOperators

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

/-- 白化 averaging kernel 的核等于白化 Jacobian 的核。 -/
theorem whitenedAveragingKernel_mulVec_eq_zero_iff (f : p.PriorFactor)
    (hObservation : p.observationErrorCovariance.PosDef) (v : State n) :
    f.whitenedAveragingKernel.mulVec v = 0 ↔
      (p.jacobian * f.matrix).mulVec v = 0 := by
  let c : Matrix (Fin m) (Fin n) ℝ := p.jacobian * f.matrix
  let w : Square m := p.innovationCovariance⁻¹
  have hw : w.PosDef := innovationCovariance_inv_posDef p f.prior_posSemidef hObservation
  have hKernel : (c.conjTranspose * w * c).mulVec v = 0 ↔ c.mulVec v = 0 := by
    constructor
    · intro hB
      by_contra hCv
      have hPos := hw.dotProduct_mulVec_pos hCv
      have hEq : star (c.mulVec v) ⬝ᵥ (w.mulVec (c.mulVec v)) =
          star v ⬝ᵥ ((c.conjTranspose * w * c).mulVec v) := by
        simp only [Matrix.mulVec_mulVec, Matrix.star_mulVec, Matrix.dotProduct_mulVec,
          Matrix.vecMul_vecMul]
        simp [Matrix.mul_assoc, dotProduct_comm]
      rw [hB] at hEq
      have hEq' : star (c.mulVec v) ⬝ᵥ (w.mulVec (c.mulVec v)) = 0 := by
        simpa [← Matrix.mulVec_mulVec] using hEq
      exact (ne_of_gt hPos) hEq'
    · intro hCv
      simp [← Matrix.mulVec_mulVec, hCv]
  simpa [whitenedAveragingKernel, c, w] using hKernel

/-- 白化 averaging kernel 的核可写回原 Jacobian 的白化坐标核。 -/
theorem whitenedAveragingKernel_mulVec_eq_zero_iff_jacobian (f : p.PriorFactor)
    (hObservation : p.observationErrorCovariance.PosDef) (v : State n) :
    f.whitenedAveragingKernel.mulVec v = 0 ↔
      p.jacobian.mulVec (f.matrix.mulVec v) = 0 := by
  simpa [Matrix.mulVec_mulVec] using
    f.whitenedAveragingKernel_mulVec_eq_zero_iff hObservation v

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

/-- 白化 averaging kernel 的线性映射可辨识性等价于原 Jacobian 可观测。 -/
theorem whitenedAveragingKernel_mulVec_injective_iff_observable (f : p.PriorFactor)
    (hObservation : p.observationErrorCovariance.PosDef) :
    Function.Injective f.whitenedAveragingKernel.mulVec ↔ Observable p.jacobian := by
  have hFactor : Function.Bijective f.matrix.mulVec := by
    refine ⟨Matrix.mulVec_injective_of_isUnit f.isUnit, ?_⟩
    exact (Matrix.mulVec_surjective_iff_isUnit).2 f.isUnit
  constructor
  · intro hB x y hxy
    rcases hFactor.2 x with ⟨vx, hvx⟩
    rcases hFactor.2 y with ⟨vy, hvy⟩
    have hBxy : f.whitenedAveragingKernel.mulVec vx =
        f.whitenedAveragingKernel.mulVec vy := by
      have hZero : f.whitenedAveragingKernel.mulVec (vx - vy) = 0 := by
        apply (f.whitenedAveragingKernel_mulVec_eq_zero_iff_jacobian hObservation
          (vx - vy)).2
        have hKDiff : p.jacobian.mulVec
            (f.matrix.mulVec (vx - vy)) = 0 := by
          calc
            p.jacobian.mulVec (f.matrix.mulVec (vx - vy)) =
                p.jacobian.mulVec (f.matrix.mulVec vx - f.matrix.mulVec vy) := by
                  congr 1
                  exact Matrix.mulVec_sub _ _ _
            _ = p.jacobian.mulVec (x - y) := by rw [hvx, hvy]
            _ = 0 := by rw [Matrix.mulVec_sub, hxy, sub_self]
        exact hKDiff
      exact sub_eq_zero.mp (by simpa [Matrix.mulVec_sub] using hZero)
    calc
      x = f.matrix.mulVec vx := hvx.symm
      _ = f.matrix.mulVec vy := congrArg f.matrix.mulVec (hB hBxy)
      _ = y := hvy
  · intro hK x y hxy
    exact (Matrix.PosDef.mulVec_injective
      (f.whitenedAveragingKernel_posDef_of_observable hObservation hK)) hxy

/-- 白化 averaging kernel 存在零谱当且仅当原 Jacobian 不可观测。 -/
theorem whitenedAveragingKernel_zero_mem_spectrum_iff_not_observable
    (f : p.PriorFactor) (hObservation : p.observationErrorCovariance.PosDef) :
    (0 : ℝ) ∈ spectrum ℝ f.whitenedAveragingKernel ↔ ¬ Observable p.jacobian := by
  rw [spectrum.mem_iff]
  have hNeg : IsUnit (-f.whitenedAveragingKernel) ↔
      IsUnit f.whitenedAveragingKernel := by
    constructor
    · intro h
      simpa using IsUnit.neg h
    · exact IsUnit.neg
  have hGoal : ¬ IsUnit (-f.whitenedAveragingKernel) ↔ ¬ Observable p.jacobian := by
    rw [hNeg, ← Matrix.mulVec_injective_iff_isUnit,
      f.whitenedAveragingKernel_mulVec_injective_iff_observable hObservation]
  simpa using hGoal

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

/-- 正定观测误差使最优增益的每个特征值严格小于 `1`。 -/
theorem eigenvalues_lt_one (f : p.PriorFactor)
    (hObservation : p.observationErrorCovariance.PosDef) (i : Fin n) :
    f.eigenvalues hObservation i < 1 := by
  exact eigenvalues_lt_one_of_complement_posDef f.whitenedAveragingKernel
    (f.whitenedAveragingKernel_posSemidef hObservation)
    (f.one_sub_whitenedAveragingKernel_posDef hObservation) i

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

/-- 观测误差正定时，白化 averaging kernel 的秩恰好等于 Jacobian 的秩。 -/
theorem whitenedAveragingKernel_rank_eq (f : p.PriorFactor)
    (hObservation : p.observationErrorCovariance.PosDef) :
    f.whitenedAveragingKernel.rank = p.jacobian.rank := by
  let c : Matrix (Fin m) (Fin n) ℝ := p.jacobian * f.matrix
  let d : Square m := CFC.sqrt p.innovationCovariance⁻¹
  have hInv : p.innovationCovariance⁻¹.PosDef :=
    (innovationCovariance_posDef p f.prior_posSemidef hObservation).inv
  have hDUnit : IsUnit d :=
    (CFC.isUnit_sqrt_iff _ hInv.posSemidef.nonneg).mpr hInv.isUnit
  have hDHerm : d.conjTranspose = d := by
    have hdPos : d.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)
    exact hdPos.isHermitian.eq
  have hDSq : d * d = p.innovationCovariance⁻¹ :=
    CFC.sqrt_mul_sqrt_self _ hInv.posSemidef.nonneg
  have hB : f.whitenedAveragingKernel = (d * c).conjTranspose * (d * c) := by
    unfold Problem.PriorFactor.whitenedAveragingKernel
    dsimp [c]
    rw [← hDSq]
    simp only [Matrix.conjTranspose_mul, hDHerm]
    simp [Matrix.mul_assoc]
  calc
    f.whitenedAveragingKernel.rank = (d * c).rank := by
      rw [hB, Matrix.rank_conjTranspose_mul_self]
    _ = c.rank := by
      exact Matrix.rank_mul_eq_right_of_isUnit_det d c
        ((Matrix.isUnit_iff_isUnit_det _).mp hDUnit)
    _ = p.jacobian.rank := by
      dsimp [c]
      exact Matrix.rank_mul_eq_left_of_isUnit_det f.matrix p.jacobian
        ((Matrix.isUnit_iff_isUnit_det _).mp f.isUnit)

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

/-- DOFS 不超过 Jacobian 的矩阵秩。 -/
theorem dofs_le_jacobian_rank (f : p.PriorFactor)
    (hObservation : p.observationErrorCovariance.PosDef) :
    p.dofs ≤ (p.jacobian.rank : ℝ) := by
  classical
  let e : Fin n → ℝ := f.eigenvalues hObservation
  let s : Finset (Fin n) := Finset.univ.filter (fun i => e i ≠ 0)
  have hSum : (∑ i, e i) = s.sum e := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i hi hNot
    by_contra hZero
    exact hNot (Finset.mem_filter.mpr ⟨hi, hZero⟩)
  have hBound : s.sum e ≤ (s.card : ℝ) := by
    have hCard := Finset.sum_le_card_nsmul s e 1 (fun i hi =>
      (f.eigenvalues_bounds hObservation i).2)
    simpa [e, nsmul_eq_mul] using hCard
  have hRankCard : f.whitenedAveragingKernel.rank = s.card := by
    have hRank :=
      (f.whitenedAveragingKernel_posSemidef hObservation).isHermitian.rank_eq_card_non_zero_eigs
    rw [Fintype.card_subtype] at hRank
    simpa [e, s, eigenvalues] using hRank
  calc
    p.dofs = ∑ i, e i := f.dofs_eq_sum_eigenvalues hObservation
    _ = s.sum e := hSum
    _ ≤ (s.card : ℝ) := hBound
    _ = (f.whitenedAveragingKernel.rank : ℝ) := by
      rw [hRankCard]
    _ = (p.jacobian.rank : ℝ) := by
      rw [f.whitenedAveragingKernel_rank_eq hObservation]

/-- 非空状态空间下，正定观测误差给出严格的状态维数上界。 -/
theorem dofs_lt_state_dim (f : p.PriorFactor)
    (hObservation : p.observationErrorCovariance.PosDef) (hState : 0 < n) :
    p.dofs < (n : ℝ) := by
  let e : Fin n → ℝ := f.eigenvalues hObservation
  have hSum : (∑ i, e i) < (∑ i : Fin n, (1 : ℝ)) := by
    apply Finset.sum_lt_sum
    · intro i hi
      exact (f.eigenvalues_lt_one hObservation i).le
    · refine ⟨⟨0, hState⟩, Finset.mem_univ _, ?_⟩
      exact f.eigenvalues_lt_one hObservation ⟨0, hState⟩
  calc
    p.dofs = ∑ i, e i := f.dofs_eq_sum_eigenvalues hObservation
    _ < ∑ i, (1 : ℝ) := hSum
    _ = (n : ℝ) := by simp


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
