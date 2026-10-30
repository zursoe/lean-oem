module

public import LeanOEM.Core.Estimator

@[expose] public section

namespace LeanOEM

noncomputable section

/-- 线性观测下的确定性估计误差分解。

若 `y = K x + ε` 且 `A = g K`，则
`x̂ - x = (I - A) (xₐ - x) + g ε`。 -/
theorem retrievalError_decomposition {n m : ℕ}
    (p : Problem n m) (g : Matrix (Fin n) (Fin m) ℝ)
    (x : State n) (y ε : Observation m)
    (hObservation : y = p.predict x + ε) :
    retrievalError p g x y =
      (1 - averagingKernel g p.jacobian).mulVec (p.priorMean - x)
        + g.mulVec ε := by
  subst y
  ext i
  simp only [retrievalError, estimateWithGain, Problem.innovation, Problem.predict,
    averagingKernel,
    Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.sub_mulVec,
    Matrix.mulVec_mulVec, Matrix.one_mulVec, Pi.add_apply, Pi.sub_apply]
  ring

end
end LeanOEM
