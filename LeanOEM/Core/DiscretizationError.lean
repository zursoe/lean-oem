module

public import LeanOEM.Core.LocalContraction

/-!
# Jacobian 离散化误差契约

本模块把数值 Jacobian 与理想 Jacobian 的差异表示成显式范数界，并说明它如何
改变加权 Jacobian 作用常数和目标驻点残差。误差界是精确实数契约，不是浮点程序
正确性的自动证明。
-/

@[expose] public section

namespace LeanOEM.NonlinearProblem

noncomputable section

open LeanOEM

/-- 近似 Jacobian 相对理想 Jacobian 的加权作用误差界。 -/
def WeightedJacobianErrorBound (p : NonlinearProblem n m)
    (approx exact : Jacobian n m) (epsilon : ℝ) : Prop :=
  ∀ v, ‖approx.conjTranspose.mulVec (p.observationWeight.mulVec v) -
      exact.conjTranspose.mulVec (p.observationWeight.mulVec v)‖ ≤
    epsilon * ‖v‖

/-- Jacobian 离散化误差会把加权作用常数增加至 `beta + epsilon`。 -/
theorem weightedJacobianActionBound_of_error
    (p : NonlinearProblem n m) (approx exact : Jacobian n m)
    {beta epsilon : ℝ}
    (hExact : p.WeightedJacobianActionBound exact beta)
    (hError : p.WeightedJacobianErrorBound approx exact epsilon) :
    p.WeightedJacobianActionBound approx (beta + epsilon) := by
  intro v
  calc
    ‖approx.conjTranspose.mulVec (p.observationWeight.mulVec v)‖ =
        ‖(approx.conjTranspose.mulVec (p.observationWeight.mulVec v) -
          exact.conjTranspose.mulVec (p.observationWeight.mulVec v)) +
          exact.conjTranspose.mulVec (p.observationWeight.mulVec v)‖ := by
      congr 1
      abel
    _ ≤ epsilon * ‖v‖ + beta * ‖v‖ := by
      exact (norm_add_le _ _).trans (add_le_add (hError v) (hExact v))
    _ = (beta + epsilon) * ‖v‖ := by ring

/--
若理想目标 Jacobian 满足驻点条件，而离散化 Jacobian 只满足加权误差界，
则离散化后目标正规方程残差至多为 `epsilon * sigma`。
-/
theorem normalRhs_norm_le_of_weightedJacobianError
    (p : NonlinearProblem n m) (target : State n)
    (approx exact : Jacobian n m)
    {epsilon sigma : ℝ}
    (hEpsilon : 0 ≤ epsilon)
    (hStationary : p.TargetStationary target exact)
    (hError : p.WeightedJacobianErrorBound approx exact epsilon)
    (hResidual : ‖p.residual target‖ ≤ sigma) :
    ‖p.normalRhs target approx‖ ≤ epsilon * sigma := by
  have hIdentity :
      p.normalRhs target approx =
        (approx.conjTranspose.mulVec (p.observationWeight.mulVec
          (p.residual target)) -
          exact.conjTranspose.mulVec (p.observationWeight.mulVec
            (p.residual target))) + p.normalRhs target exact := by
    simp [normalRhs]
  rw [hIdentity]
  change p.normalRhs target exact = 0 at hStationary
  rw [hStationary, add_zero]
  calc
    ‖approx.conjTranspose.mulVec (p.observationWeight.mulVec
          (p.residual target)) -
        exact.conjTranspose.mulVec (p.observationWeight.mulVec
          (p.residual target))‖ ≤
        epsilon * ‖p.residual target‖ := hError _
    _ ≤ epsilon * sigma :=
      mul_le_mul_of_nonneg_left hResidual hEpsilon

end
end LeanOEM.NonlinearProblem

