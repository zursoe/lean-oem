module

public import LeanOEM.Core.Estimator
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

namespace LeanOEM

noncomputable section

/-- 线性 OEM 问题的最小良定性假设。

先验协方差允许半正定，观测误差协方差要求正定。`Problem` 本身不携带这些证明，
以便区分原始输入和对输入的形式假设。 -/
structure Problem.WellPosed {n m : ℕ} (p : Problem n m) : Prop where
  prior_posSemidef : p.priorCovariance.PosSemidef
  observation_posDef : p.observationErrorCovariance.PosDef

/-- 半正定先验经过 Jacobian 合同变换后，与正定观测误差协方差相加仍为正定。 -/
theorem innovationCovariance_posDef {n m : ℕ}
    (p : Problem n m)
    (hPrior : p.priorCovariance.PosSemidef)
    (hObservation : p.observationErrorCovariance.PosDef) :
    p.innovationCovariance.PosDef := by
  unfold Problem.innovationCovariance
  exact Matrix.PosDef.posSemidef_add
    (Matrix.PosSemidef.mul_mul_conjTranspose_same hPrior p.jacobian)
    hObservation

/-- 良定性假设下的创新协方差正定性。 -/
theorem Problem.WellPosed.innovationCovariance_posDef
    {n m : ℕ} {p : Problem n m} (h : p.WellPosed) :
    p.innovationCovariance.PosDef :=
  LeanOEM.innovationCovariance_posDef p h.prior_posSemidef h.observation_posDef

/-- 正定创新协方差对应可逆的方阵。 -/
theorem innovationCovariance_isUnit {n m : ℕ}
    (p : Problem n m)
    (hPrior : p.priorCovariance.PosSemidef)
    (hObservation : p.observationErrorCovariance.PosDef) :
    IsUnit p.innovationCovariance :=
  (innovationCovariance_posDef p hPrior hObservation).isUnit

/-- 正定创新协方差的总函数逆仍为正定矩阵。 -/
theorem innovationCovariance_inv_posDef {n m : ℕ}
    (p : Problem n m)
    (hPrior : p.priorCovariance.PosSemidef)
    (hObservation : p.observationErrorCovariance.PosDef) :
    p.innovationCovariance⁻¹.PosDef :=
  (innovationCovariance_posDef p hPrior hObservation).inv

/-- 正定创新协方差的逆满足左侧消去恒等式。 -/
theorem innovationCovariance_inv_mul {n m : ℕ}
    (p : Problem n m)
    (hPrior : p.priorCovariance.PosSemidef)
    (hObservation : p.observationErrorCovariance.PosDef) :
    p.innovationCovariance⁻¹ * p.innovationCovariance = 1 := by
  exact Matrix.nonsing_inv_mul p.innovationCovariance
    ((Matrix.isUnit_iff_isUnit_det p.innovationCovariance).mp
      (innovationCovariance_posDef p hPrior hObservation).isUnit)

/-- 正定创新协方差的逆满足右侧消去恒等式。 -/
theorem innovationCovariance_mul_inv {n m : ℕ}
    (p : Problem n m)
    (hPrior : p.priorCovariance.PosSemidef)
    (hObservation : p.observationErrorCovariance.PosDef) :
    p.innovationCovariance * p.innovationCovariance⁻¹ = 1 := by
  exact Matrix.mul_nonsing_inv p.innovationCovariance
    ((Matrix.isUnit_iff_isUnit_det p.innovationCovariance).mp
      (innovationCovariance_posDef p hPrior hObservation).isUnit)

/-- Hermitian 正定创新协方差的总函数逆也是 Hermitian 的。 -/
theorem innovationCovariance_inv_conjTranspose {n m : ℕ}
    (p : Problem n m)
    (hPrior : p.priorCovariance.PosSemidef)
    (hObservation : p.observationErrorCovariance.PosDef) :
    p.innovationCovariance⁻¹.conjTranspose = p.innovationCovariance⁻¹ := by
  have hInnovation := innovationCovariance_posDef p hPrior hObservation
  calc
    p.innovationCovariance⁻¹.conjTranspose =
        p.innovationCovariance.conjTranspose⁻¹ :=
      Matrix.conjTranspose_nonsing_inv p.innovationCovariance
    _ = p.innovationCovariance⁻¹ := by rw [hInnovation.isHermitian.eq]

/-- 最优增益乘创新协方差后恢复先验项。 -/
theorem gain_mul_innovationCovariance {n m : ℕ}
    (p : Problem n m)
    (hPrior : p.priorCovariance.PosSemidef)
    (hObservation : p.observationErrorCovariance.PosDef) :
    p.gain * p.innovationCovariance =
      p.priorCovariance * p.jacobian.conjTranspose := by
  simp only [Problem.gain, Matrix.mul_assoc,
    innovationCovariance_inv_mul p hPrior hObservation, Matrix.mul_one]

/-- 良定性假设下的增益规格定理。 -/
theorem Problem.WellPosed.gain_mul_innovationCovariance
    {n m : ℕ} {p : Problem n m} (h : p.WellPosed) :
    p.gain * p.innovationCovariance =
      p.priorCovariance * p.jacobian.conjTranspose :=
  LeanOEM.gain_mul_innovationCovariance p h.prior_posSemidef h.observation_posDef

end
end LeanOEM
