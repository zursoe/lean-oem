module

public import LeanOEM.Core.Information
public import LeanOEM.Core.Diagnostics
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Trace

@[expose] public section

namespace LeanOEM

noncomputable section

/-- 半正定 `A` 且 `I - A` 半正定时，Hermitian `A` 的每个特征值都在 `[0, 1]`。 -/
theorem eigenvalues_bounds_of_posSemidef {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A.PosSemidef)
    (hComplement : (1 - A).PosSemidef) (i : n) :
    0 ≤ hA.isHermitian.eigenvalues i ∧ hA.isHermitian.eigenvalues i ≤ 1 := by
  constructor
  · exact hA.eigenvalues_nonneg i
  · let v : n → ℝ := ⇑(hA.isHermitian.eigenvectorBasis i)
    have hv : v ≠ 0 := by
      intro hv
      apply hA.isHermitian.eigenvectorBasis.orthonormal.ne_zero i
      apply (WithLp.ofLp_eq_zero 2).mp
      simpa [v] using hv
    have hEigen : Matrix.mulVec A v = (hA.isHermitian.eigenvalues i) • v := by
      exact hA.isHermitian.mulVec_eigenvectorBasis i
    have hQuad := hComplement.dotProduct_mulVec_nonneg v
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hEigen] at hQuad
    have hNorm : 0 < dotProduct (star v) v :=
      (Matrix.dotProduct_star_self_pos_iff).2 hv
    have hQuad' :
        hA.isHermitian.eigenvalues i * dotProduct (star v) v ≤ dotProduct (star v) v := by
      simpa [smul_eq_mul, dotProduct_smul] using hQuad
    nlinarith

/-- 两个实半正定矩阵乘积的迹非负。 -/
theorem trace_mul_nonneg_of_posSemidef {n : Type*} [Fintype n]
    (A B : Matrix n n ℝ) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ Matrix.trace (A * B) := by
  classical
  rw [hA.isHermitian.spectral_theorem, Unitary.conjStarAlgAut_apply]
  let U : Matrix n n ℝ := hA.isHermitian.eigenvectorUnitary
  let D : Matrix n n ℝ := Matrix.diagonal (RCLike.ofReal ∘ hA.isHermitian.eigenvalues)
  let C : Matrix n n ℝ := (star U) * B * U
  have hC : C.PosSemidef := by
    dsimp [C, U]
    exact Matrix.PosSemidef.conjTranspose_mul_mul_same hB _
  have hTraceDiag : 0 ≤ Matrix.trace (D * C) := by
    simp only [Matrix.trace]
    apply Finset.sum_nonneg
    intro i hi
    change 0 ≤ (D * C) i i
    simp [D, Matrix.mul_apply, Matrix.diagonal]
    exact mul_nonneg (by simpa [D] using hA.eigenvalues_nonneg i)
      (hC.diag_nonneg (i := i))
  calc
    0 ≤ Matrix.trace (D * C) := hTraceDiag
    _ = Matrix.trace (C * D) := by rw [Matrix.trace_mul_comm]
    _ = Matrix.trace ((star U) * B * (U * D)) := by
      simp [C, Matrix.mul_assoc]
    _ = Matrix.trace (U * D * (star U) * B) := by
      rw [Matrix.trace_mul_comm]
      simp [Matrix.mul_assoc]

/-- 正定先验和观测误差协方差下，最优增益的 DOFS 非负。 -/
theorem Problem.dofs_nonneg_of_posDef {n m : ℕ}
    (p : Problem n m)
    (hPrior : p.priorCovariance.PosDef)
    (hObservation : p.observationErrorCovariance.PosDef) :
    0 ≤ p.dofs := by
  unfold Problem.dofs
  let t : Square m := p.jacobian * p.priorCovariance * p.jacobian.conjTranspose
  have hT : t.PosSemidef := by
    dsimp [t]
    exact Matrix.PosSemidef.mul_mul_conjTranspose_same hPrior.posSemidef p.jacobian
  have hS : p.innovationCovariance.PosDef :=
    innovationCovariance_posDef p hPrior.posSemidef hObservation
  have hSinv : p.innovationCovariance⁻¹.PosSemidef := hS.inv.posSemidef
  have hTrace : 0 ≤ Matrix.trace (t * p.innovationCovariance⁻¹) :=
    trace_mul_nonneg_of_posSemidef t p.innovationCovariance⁻¹ hT hSinv
  have hEq : LeanOEM.dofs p.gain p.jacobian = Matrix.trace (t * p.innovationCovariance⁻¹) := by
    unfold LeanOEM.dofs averagingKernel Problem.gain
    dsimp [t]
    rw [Matrix.trace_mul_cycle]
    simp [Matrix.mul_assoc]
  rw [hEq]
  exact hTrace

/-- 正定先验和观测误差协方差下，最优增益的 DOFS 不超过状态维数。 -/
theorem Problem.dofs_le_dim_of_posDef {n m : ℕ}
    (p : Problem n m)
    (hPrior : p.priorCovariance.PosDef)
    (hObservation : p.observationErrorCovariance.PosDef) :
    p.dofs ≤ (n : ℝ) := by
  unfold Problem.dofs
  let t : Square m := p.jacobian * p.priorCovariance * p.jacobian.conjTranspose
  have hPost : (posteriorCovariance p).PosSemidef :=
    posteriorCovariance_posSemidef p hPrior.posSemidef hObservation
  have hPriorInv : p.priorCovariance⁻¹.PosSemidef := hPrior.inv.posSemidef
  have hPostTrace : 0 ≤ Matrix.trace (posteriorCovariance p * p.priorCovariance⁻¹) :=
    trace_mul_nonneg_of_posSemidef (posteriorCovariance p) p.priorCovariance⁻¹
      hPost hPriorInv
  have hDofs : LeanOEM.dofs p.gain p.jacobian = Matrix.trace (t * p.innovationCovariance⁻¹) := by
    unfold LeanOEM.dofs averagingKernel Problem.gain
    dsimp [t]
    rw [Matrix.trace_mul_cycle]
    simp [Matrix.mul_assoc]
  have hTracePrior : Matrix.trace (p.priorCovariance * p.priorCovariance⁻¹) =
      (n : ℝ) := by
    rw [Matrix.mul_nonsing_inv p.priorCovariance
      ((Matrix.isUnit_iff_isUnit_det _).mp hPrior.isUnit)]
    simp [Matrix.trace_one]
  have hTraceSplit : Matrix.trace (posteriorCovariance p * p.priorCovariance⁻¹) =
      Matrix.trace (p.priorCovariance * p.priorCovariance⁻¹) -
        Matrix.trace (t * p.innovationCovariance⁻¹) := by
    have hTerm : Matrix.trace
        ((p.priorCovariance * p.jacobian.conjTranspose * p.innovationCovariance⁻¹ *
          p.jacobian * p.priorCovariance) * p.priorCovariance⁻¹) =
        Matrix.trace (t * p.innovationCovariance⁻¹) := by
      calc
        Matrix.trace
            ((p.priorCovariance * p.jacobian.conjTranspose * p.innovationCovariance⁻¹ *
              p.jacobian * p.priorCovariance) * p.priorCovariance⁻¹) =
            Matrix.trace (p.priorCovariance * p.jacobian.conjTranspose *
              p.innovationCovariance⁻¹ * p.jacobian) := by
                simp [Matrix.mul_assoc, Matrix.mul_nonsing_inv p.priorCovariance
                  ((Matrix.isUnit_iff_isUnit_det _).mp hPrior.isUnit)]
        _ = Matrix.trace (t * p.innovationCovariance⁻¹) := by
          dsimp [t]
          rw [Matrix.trace_mul_cycle]
          simp [Matrix.mul_assoc]
    unfold posteriorCovariance
    rw [sub_mul, Matrix.trace_sub]
    rw [hTerm]
  rw [hDofs]
  rw [hTracePrior] at hTraceSplit
  linarith

/-- 正定先验和观测误差协方差下，最优增益的 DOFS 落在 `[0, n]`。 -/
theorem Problem.dofs_bounds_of_posDef {n m : ℕ}
    (p : Problem n m)
    (hPrior : p.priorCovariance.PosDef)
    (hObservation : p.observationErrorCovariance.PosDef) :
    0 ≤ p.dofs ∧ p.dofs ≤ (n : ℝ) :=
  ⟨p.dofs_nonneg_of_posDef hPrior hObservation,
    p.dofs_le_dim_of_posDef hPrior hObservation⟩

end
end LeanOEM
