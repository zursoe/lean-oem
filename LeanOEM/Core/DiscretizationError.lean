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

/-- 指定状态处近似正演和精确正演之间的观测空间误差界。 -/
def ForwardModelErrorBound (approximate exact : ForwardModel n m)
    (x : State n) (epsilon : ℝ) : Prop :=
  ‖approximate.observe x - exact.observe x‖ ≤ epsilon

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

/-- 两个正演模型和两个 Jacobian 的正规方程右端差异恒等式。 -/
theorem normalRhsFor_difference_eq
    (p : NonlinearProblem n m) (x : State n)
    (approximateModel exactModel : ForwardModel n m)
    (approximate exact : Jacobian n m) :
    p.normalRhsFor approximateModel x approximate -
        p.normalRhsFor exactModel x exact =
      (approximate.conjTranspose.mulVec
          (p.observationWeight.mulVec
            (p.residualFor exactModel x)) -
        exact.conjTranspose.mulVec
          (p.observationWeight.mulVec
            (p.residualFor exactModel x))) +
      approximate.conjTranspose.mulVec
        (p.observationWeight.mulVec
          (exactModel.observe x - approximateModel.observe x)) := by
  simp [normalRhsFor, residualFor, Matrix.mulVec_sub]
  abel

/-- 前向模型误差和 Jacobian 误差共同给出正规方程右端误差界。 -/
theorem normalRhsFor_difference_norm_le_of_forward_and_jacobian_error
    (p : NonlinearProblem n m) (x : State n)
    (approximateModel exactModel : ForwardModel n m)
    (approximate exact : Jacobian n m)
    {beta epsilonJacobian epsilonForward sigma : ℝ}
    (hBeta : 0 ≤ beta)
    (hEpsilonJacobian : 0 ≤ epsilonJacobian)
    (hAction : p.WeightedJacobianActionBound approximate beta)
    (hJacobian : p.WeightedJacobianErrorBound approximate exact epsilonJacobian)
    (hForward : ForwardModelErrorBound approximateModel exactModel x epsilonForward)
    (hResidual : ‖p.residualFor exactModel x‖ ≤ sigma) :
    ‖p.normalRhsFor approximateModel x approximate -
        p.normalRhsFor exactModel x exact‖ ≤
      epsilonJacobian * sigma + beta * epsilonForward := by
  rw [normalRhsFor_difference_eq p x approximateModel exactModel approximate exact]
  have hForward' :
      ‖exactModel.observe x - approximateModel.observe x‖ ≤ epsilonForward := by
    simpa only [ForwardModelErrorBound, norm_sub_rev] using hForward
  calc
    ‖(approximate.conjTranspose.mulVec
          (p.observationWeight.mulVec
            (p.residualFor exactModel x)) -
        exact.conjTranspose.mulVec
          (p.observationWeight.mulVec
            (p.residualFor exactModel x))) +
      approximate.conjTranspose.mulVec
        (p.observationWeight.mulVec
          (exactModel.observe x - approximateModel.observe x))‖ ≤
        epsilonJacobian * ‖p.residualFor exactModel x‖ +
          beta * ‖exactModel.observe x - approximateModel.observe x‖ := by
      exact (norm_add_le _ _).trans <|
        add_le_add (hJacobian _) (hAction _)
    _ ≤ epsilonJacobian * sigma + beta * epsilonForward := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hResidual hEpsilonJacobian)
        (mul_le_mul_of_nonneg_left hForward' hBeta)

/-- 精确模型在目标处满足正规驻点时，近似前向/Jacobian 的正规右端误差界。 -/
theorem normalRhsFor_norm_le_of_forward_and_jacobian_error
    (p : NonlinearProblem n m) (target : State n)
    (approximateModel exactModel : ForwardModel n m)
    (approximate exact : Jacobian n m)
    {beta epsilonJacobian epsilonForward sigma : ℝ}
    (hBeta : 0 ≤ beta)
    (hEpsilonJacobian : 0 ≤ epsilonJacobian)
    (hStationary : p.normalRhsFor exactModel target exact = 0)
    (hAction : p.WeightedJacobianActionBound approximate beta)
    (hJacobian : p.WeightedJacobianErrorBound approximate exact epsilonJacobian)
    (hForward : ForwardModelErrorBound approximateModel exactModel target epsilonForward)
    (hResidual : ‖p.residualFor exactModel target‖ ≤ sigma) :
    ‖p.normalRhsFor approximateModel target approximate‖ ≤
      epsilonJacobian * sigma + beta * epsilonForward := by
  have hDifference := normalRhsFor_difference_norm_le_of_forward_and_jacobian_error
    p target approximateModel exactModel approximate exact hBeta hEpsilonJacobian
      hAction hJacobian hForward hResidual
  have hIdentity :
      p.normalRhsFor approximateModel target approximate =
        (p.normalRhsFor approximateModel target approximate -
          p.normalRhsFor exactModel target exact) +
          p.normalRhsFor exactModel target exact := by
    abel
  rw [hIdentity, hStationary, add_zero]
  simpa [hStationary] using hDifference

/-- 在近似正规矩阵逆作用界下，前向/Jacobian 误差形成 Gauss–Newton 更新误差底。

该结论比较的是同一目标处的一步更新；它不把近似模型误差解释成全局收敛保证。 -/
theorem gaussNewtonUpdate_error_le_of_forward_and_jacobian_error
    (p : NonlinearProblem n m) (target : State n)
    (approximateModel exactModel : ForwardModel n m)
    (approximate exact : Jacobian n m)
    {beta epsilonJacobian epsilonForward sigma gamma : ℝ}
    (hBeta : 0 ≤ beta)
    (hEpsilonJacobian : 0 ≤ epsilonJacobian)
    (hStationary : p.normalRhsFor exactModel target exact = 0)
    (hAction : p.WeightedJacobianActionBound approximate beta)
    (hJacobian : p.WeightedJacobianErrorBound approximate exact epsilonJacobian)
    (hForward : ForwardModelErrorBound approximateModel exactModel target epsilonForward)
    (hResidual : ‖p.residualFor exactModel target‖ ≤ sigma)
    (hNormal : IsUnit ((p.withModel approximateModel).normalMatrix target approximate))
    (hGamma : 0 ≤ gamma)
    (hInverse : (p.withModel approximateModel).InverseActionBound target approximate gamma) :
    ‖(p.withModel approximateModel).gaussNewtonUpdate target approximate - target‖ ≤
      gamma * (epsilonJacobian * sigma + beta * epsilonForward) := by
  let tau := epsilonJacobian * sigma + beta * epsilonForward
  have hRhs :
      ‖p.normalRhsFor approximateModel target approximate‖ ≤ tau := by
    exact normalRhsFor_norm_le_of_forward_and_jacobian_error
      p target approximateModel exactModel approximate exact hBeta hEpsilonJacobian
        hStationary hAction hJacobian hForward hResidual
  have hDefect :
      ‖(p.withModel approximateModel).normalDefect target target approximate‖ ≤
        (0 : ℝ) * ‖target - target‖ + tau := by
    change ‖p.normalRhsFor approximateModel target approximate -
      (p.normalMatrix target approximate).mulVec (target - target)‖ ≤ _
    simpa using hRhs
  have hUpdate := gaussNewtonUpdate_error_le_of_inverse_and_additive_defect
    (p.withModel approximateModel) target target approximate
    (gamma := gamma) (eta := (0 : ℝ)) (tau := tau)
    hNormal hGamma hInverse hDefect
  simpa [tau] using hUpdate

end
end LeanOEM.NonlinearProblem

