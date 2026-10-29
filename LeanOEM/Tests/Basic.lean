module

public import LeanOEM

@[expose] public section

namespace LeanOEM.Tests

open LeanOEM

/-- 检查正定性定理可以通过公开根模块调用。 -/
example {n m : ℕ} (p : Problem n m)
    (hPrior : p.priorCovariance.PosSemidef)
    (hObservation : p.observationErrorCovariance.PosDef) :
    p.innovationCovariance.PosDef := by
  exact innovationCovariance_posDef p hPrior hObservation

/-- 检查良定性假设的捆绑接口。 -/
example {n m : ℕ} (p : Problem n m) (h : p.WellPosed) :
    p.innovationCovariance.PosDef := by
  exact h.innovationCovariance_posDef

/-- 检查创新协方差的逆矩阵辅助定理可以通过公开根模块调用。 -/
example {n m : ℕ} (p : Problem n m)
    (hPrior : p.priorCovariance.PosSemidef)
    (hObservation : p.observationErrorCovariance.PosDef) :
    p.innovationCovariance⁻¹ * p.innovationCovariance = 1 := by
  exact innovationCovariance_inv_mul p hPrior hObservation

/-- 检查最优增益的矩阵规格定理。 -/
example {n m : ℕ} (p : Problem n m)
    (hPrior : p.priorCovariance.PosSemidef)
    (hObservation : p.observationErrorCovariance.PosDef) :
    p.gain * p.innovationCovariance =
      p.priorCovariance * p.jacobian.conjTranspose := by
  exact gain_mul_innovationCovariance p hPrior hObservation

/-- 检查任意增益的误差分解接口及其观测方程假设。 -/
example {n m : ℕ} (p : Problem n m)
    (g : Matrix (Fin n) (Fin m) ℝ)
    (x : State n) (y ε : Observation m)
    (hObservation : y = p.predict x + ε) :
    retrievalError p g x y =
      (1 - averagingKernel g p.jacobian).mulVec (p.priorMean - x)
        + g.mulVec ε := by
  exact retrievalError_decomposition p g x y ε hObservation

/-- 检查 Joseph 协方差的半正定性接口。 -/
example {n m : ℕ} (p : Problem n m)
    (g : Matrix (Fin n) (Fin m) ℝ)
    (hPrior : p.priorCovariance.PosSemidef)
    (hObservation : p.observationErrorCovariance.PosSemidef) :
    josephCovariance p g |>.PosSemidef := by
  exact josephCovariance_posSemidef p g hPrior hObservation

/-- 检查标准后验协方差与 Joseph 形式的等价性。 -/
example {n m : ℕ} (p : Problem n m)
    (hPrior : p.priorCovariance.PosSemidef)
    (hObservation : p.observationErrorCovariance.PosDef) :
    posteriorCovariance p = josephCovariance p p.gain := by
  exact posteriorCovariance_eq_josephCovariance p hPrior hObservation

/-- 检查标准后验协方差的半正定性接口。 -/
example {n m : ℕ} (p : Problem n m)
    (hPrior : p.priorCovariance.PosSemidef)
    (hObservation : p.observationErrorCovariance.PosDef) :
    posteriorCovariance p |>.PosSemidef := by
  exact posteriorCovariance_posSemidef p hPrior hObservation

/-- 检查后验不确定性减少的半正定结论。 -/
example {n m : ℕ} (p : Problem n m)
    (hPrior : p.priorCovariance.PosSemidef)
    (hObservation : p.observationErrorCovariance.PosDef) :
    (p.priorCovariance - posteriorCovariance p).PosSemidef := by
  exact prior_minus_posterior_posSemidef p hPrior hObservation

end LeanOEM.Tests
