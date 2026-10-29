module

public import LeanOEM.Core.Assumptions
public import Mathlib.Tactic.NoncommRing

@[expose] public section

namespace LeanOEM

noncomputable section

/-- 线性最优估计的标准后验协方差公式。 -/
def posteriorCovariance {n m : ℕ} (p : Problem n m) : Square n :=
  p.priorCovariance - p.priorCovariance * p.jacobian.conjTranspose *
    p.innovationCovariance⁻¹ * p.jacobian * p.priorCovariance

/-- 任意线性增益对应的 Joseph 协方差表达式。 -/
def josephCovariance {n m : ℕ}
    (p : Problem n m) (g : Matrix (Fin n) (Fin m) ℝ) : Square n :=
  (1 - g * p.jacobian) * p.priorCovariance *
      (1 - g * p.jacobian).conjTranspose
    + g * p.observationErrorCovariance * g.conjTranspose

/-- Joseph 协方差在半正定输入下保持半正定。 -/
theorem josephCovariance_posSemidef {n m : ℕ}
    (p : Problem n m) (g : Matrix (Fin n) (Fin m) ℝ)
    (hPrior : p.priorCovariance.PosSemidef)
    (hObservation : p.observationErrorCovariance.PosSemidef) :
    josephCovariance p g |>.PosSemidef := by
  unfold josephCovariance
  exact Matrix.PosSemidef.add
    (Matrix.PosSemidef.mul_mul_conjTranspose_same hPrior (1 - g * p.jacobian))
    (Matrix.PosSemidef.mul_mul_conjTranspose_same hObservation g)

/-- 非交换矩阵环中的 Joseph 恒等式。

该引理把逆矩阵消去和共轭转置的代数细节集中在一个位置，具体 OEM 定理只需提供
创新协方差的定义、Hermitian 性质和左侧逆恒等式。 -/
private theorem posteriorCovariance_eq_joseph_matrix
    {n m : ℕ}
    (prior : Square n) (observationError : Square m) (jacobian : Jacobian n m)
    (innovation : Square m) (gain : Matrix (Fin n) (Fin m) ℝ)
    (hPrior : prior.conjTranspose = prior)
    (hInnovationInv : innovation⁻¹.conjTranspose = innovation⁻¹)
    (hInnovation : innovation = jacobian * prior * jacobian.conjTranspose + observationError)
    (hLeft : innovation⁻¹ * innovation = 1)
    (hGain : gain = prior * jacobian.conjTranspose * innovation⁻¹) :
    prior - prior * jacobian.conjTranspose * innovation⁻¹ * jacobian * prior =
      (1 - gain * jacobian) * prior * (1 - gain * jacobian).conjTranspose
        + gain * observationError * gain.conjTranspose := by
  have hJacobian : jacobian.conjTranspose.conjTranspose = jacobian :=
    Matrix.conjTranspose_conjTranspose _
  have hObservation : observationError =
      innovation - jacobian * prior * jacobian.conjTranspose := by
    rw [hInnovation]
    noncomm_ring
  rw [hGain, hObservation]
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
    Matrix.conjTranspose_mul, hPrior, hInnovationInv, hJacobian]
  have hCore :
      innovation⁻¹ * (innovation - jacobian * prior * jacobian.conjTranspose)
          * innovation⁻¹ * jacobian * prior =
        innovation⁻¹ * jacobian * prior
          - innovation⁻¹ * jacobian * prior * jacobian.conjTranspose
              * innovation⁻¹ * jacobian * prior := by
    calc
      innovation⁻¹ * (innovation - jacobian * prior * jacobian.conjTranspose)
          * innovation⁻¹ * jacobian * prior =
          (innovation⁻¹ * innovation
            - innovation⁻¹ * (jacobian * prior * jacobian.conjTranspose))
              * innovation⁻¹ * jacobian * prior := by
            noncomm_ring
      _ = innovation⁻¹ * jacobian * prior
          - innovation⁻¹ * jacobian * prior * jacobian.conjTranspose
              * innovation⁻¹ * jacobian * prior := by
            rw [hLeft]
            simp [Matrix.sub_mul, Matrix.mul_assoc]
  have hCoreRight :
      innovation⁻¹ *
          ((innovation - jacobian * (prior * jacobian.conjTranspose))
            * (innovation⁻¹ * (jacobian * prior))) =
        innovation⁻¹ * jacobian * prior
          - innovation⁻¹ * jacobian * prior * jacobian.conjTranspose
              * innovation⁻¹ * jacobian * prior := by
    simpa only [Matrix.mul_assoc] using hCore
  have hCoreWithPrefix := congrArg
    (fun value => prior * (jacobian.conjTranspose * value)) hCoreRight
  simp only [Matrix.mul_assoc]
  rw [hCoreWithPrefix]
  simp [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]

/-- 标准后验协方差等于最优增益的 Joseph 形式。 -/
theorem posteriorCovariance_eq_josephCovariance {n m : ℕ}
    (p : Problem n m)
    (hPrior : p.priorCovariance.PosSemidef)
    (hObservation : p.observationErrorCovariance.PosDef) :
    posteriorCovariance p = josephCovariance p p.gain := by
  unfold posteriorCovariance josephCovariance
  apply posteriorCovariance_eq_joseph_matrix
  · exact hPrior.isHermitian.eq
  · exact innovationCovariance_inv_conjTranspose p hPrior hObservation
  · rfl
  · exact innovationCovariance_inv_mul p hPrior hObservation
  · rfl

/-- 先验减后验等于增益对创新协方差的合同变换。 -/
theorem prior_minus_posterior_eq_gain_covariance_gain_conjTranspose {n m : ℕ}
    (p : Problem n m)
    (hPrior : p.priorCovariance.PosSemidef)
    (hObservation : p.observationErrorCovariance.PosDef) :
    p.priorCovariance - posteriorCovariance p =
      p.gain * p.innovationCovariance * p.gain.conjTranspose := by
  have hLeft := innovationCovariance_inv_mul p hPrior hObservation
  have hPriorHermitian := hPrior.isHermitian.eq
  have hInnovationInv := innovationCovariance_inv_conjTranspose p hPrior hObservation
  have hJacobian := Matrix.conjTranspose_conjTranspose p.jacobian
  unfold posteriorCovariance Problem.gain
  simp only [Matrix.conjTranspose_mul]
  rw [hPriorHermitian, hInnovationInv, hJacobian]
  simp [Matrix.mul_assoc, hLeft]

/-- 先验减后验是半正定的，表示线性观测带来的不确定性减少。 -/
theorem prior_minus_posterior_posSemidef {n m : ℕ}
    (p : Problem n m)
    (hPrior : p.priorCovariance.PosSemidef)
    (hObservation : p.observationErrorCovariance.PosDef) :
    (p.priorCovariance - posteriorCovariance p).PosSemidef := by
  rw [prior_minus_posterior_eq_gain_covariance_gain_conjTranspose p hPrior hObservation]
  exact Matrix.PosSemidef.mul_mul_conjTranspose_same
    (innovationCovariance_posDef p hPrior hObservation).posSemidef p.gain

/-- 良定性假设下，标准后验协方差是半正定的。 -/
theorem posteriorCovariance_posSemidef {n m : ℕ}
    (p : Problem n m)
    (hPrior : p.priorCovariance.PosSemidef)
    (hObservation : p.observationErrorCovariance.PosDef) :
    posteriorCovariance p |>.PosSemidef := by
  rw [posteriorCovariance_eq_josephCovariance p hPrior hObservation]
  exact josephCovariance_posSemidef p p.gain hPrior hObservation.posSemidef

end
end LeanOEM
