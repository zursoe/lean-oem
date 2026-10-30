module

public import LeanOEM.Core.Covariance
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

namespace LeanOEM

noncomputable section

/-- 线性 OEM 的信息矩阵。 -/
def informationMatrix {n m : ℕ} (p : Problem n m) : Square n :=
  p.priorCovariance⁻¹
    + p.jacobian.conjTranspose * p.observationErrorCovariance⁻¹ * p.jacobian

/-- 正定先验和正定观测误差协方差给出正定信息矩阵。 -/
theorem informationMatrix_posDef {n m : ℕ}
    (p : Problem n m)
    (hPrior : p.priorCovariance.PosDef)
    (hObservation : p.observationErrorCovariance.PosDef) :
    (informationMatrix p).PosDef := by
  unfold informationMatrix
  exact Matrix.PosDef.add_posSemidef hPrior.inv
    (Matrix.PosSemidef.conjTranspose_mul_mul_same
      hObservation.inv.posSemidef p.jacobian)

/-- 正定矩阵的总函数逆再取逆可恢复原矩阵。 -/
private lemma inv_inv_of_posDef {n : ℕ} (A : Square n) (hA : A.PosDef) :
    (A⁻¹)⁻¹ = A := by
  exact Matrix.nonsing_inv_nonsing_inv A
    ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit)

/-- Woodbury 恒等式给出的后验协方差信息形式。 -/
theorem posteriorCovariance_eq_informationMatrix_inv {n m : ℕ}
    (p : Problem n m)
    (hPrior : p.priorCovariance.PosDef)
    (hObservation : p.observationErrorCovariance.PosDef) :
    posteriorCovariance p = (informationMatrix p)⁻¹ := by
  let hInnovation := innovationCovariance_posDef p hPrior.posSemidef hObservation
  have hPriorInvInv := inv_inv_of_posDef p.priorCovariance hPrior
  have hObservationInvInv := inv_inv_of_posDef p.observationErrorCovariance hObservation
  have hA : IsUnit p.priorCovariance⁻¹ := hPrior.inv.isUnit
  have hC : IsUnit p.observationErrorCovariance⁻¹ := hObservation.inv.isUnit
  have hAC : IsUnit
      (p.observationErrorCovariance⁻¹⁻¹
        + p.jacobian * p.priorCovariance⁻¹⁻¹ * p.jacobian.conjTranspose) := by
    simpa [Problem.innovationCovariance, hPriorInvInv, hObservationInvInv,
      add_comm, Matrix.mul_assoc] using hInnovation.isUnit
  have hWoodbury := Matrix.add_mul_mul_inv_eq_sub
    (p.priorCovariance⁻¹)
    (p.jacobian.conjTranspose)
    (p.observationErrorCovariance⁻¹)
    p.jacobian hA hC hAC
  unfold posteriorCovariance informationMatrix
  simpa [Problem.innovationCovariance, hPriorInvInv, hObservationInvInv,
    Matrix.mul_assoc, add_comm] using hWoodbury.symm

/-- 正定先验下，后验协方差也正定。 -/
theorem posteriorCovariance_posDef {n m : ℕ}
    (p : Problem n m)
    (hPrior : p.priorCovariance.PosDef)
    (hObservation : p.observationErrorCovariance.PosDef) :
    (posteriorCovariance p).PosDef := by
  rw [posteriorCovariance_eq_informationMatrix_inv p hPrior hObservation]
  exact (informationMatrix_posDef p hPrior hObservation).inv

/-- 后验协方差的逆等于信息矩阵。 -/
theorem posteriorCovariance_inv_eq_informationMatrix {n m : ℕ}
    (p : Problem n m)
    (hPrior : p.priorCovariance.PosDef)
    (hObservation : p.observationErrorCovariance.PosDef) :
    (posteriorCovariance p)⁻¹ = informationMatrix p := by
  rw [posteriorCovariance_eq_informationMatrix_inv p hPrior hObservation]
  exact Matrix.nonsing_inv_nonsing_inv (informationMatrix p)
    ((Matrix.isUnit_iff_isUnit_det (informationMatrix p)).mp
      (informationMatrix_posDef p hPrior hObservation).isUnit)

end
end LeanOEM
