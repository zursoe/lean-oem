module

public import LeanOEM.Core.Iteration

/-!
# 线性化余项与局部收缩

本模块把正演模型的局部线性化余项连接到非线性 OEM 的正规方程缺陷。
余项界、加权 Jacobian 的作用界和正规矩阵逆作用界都作为显式契约提供；
它们不会由 `HasJacobianAt` 或正定性假设自动产生。
-/

@[expose] public section

namespace LeanOEM.NonlinearProblem

noncomputable section

open LeanOEM

/-! ## 正规缺陷的余项表示 -/

/-- 加权 Jacobian 对观测余项的作用界。 -/
def WeightedJacobianActionBound (p : NonlinearProblem n m) (k : Jacobian n m)
    (beta : ℝ) : Prop :=
  ∀ v, ‖k.conjTranspose.mulVec (p.observationWeight.mulVec v)‖ ≤ beta * ‖v‖

/-
在观测等于目标状态的正演输出、先验均值等于目标状态时，
正规方程缺陷正好是加权 Jacobian 作用在线性化余项上。
-/
theorem normalDefect_eq_weighted_linearizationRemainder
    (p : NonlinearProblem n m) (x target : State n) (k : Jacobian n m)
    (hObservation : p.observation = p.model.observe target)
    (hPrior : p.priorMean = target) :
    p.normalDefect x target k =
      k.conjTranspose.mulVec
        (p.observationWeight.mulVec
          (p.model.linearizationRemainder x target k)) := by
  simp only [normalDefect, normalRhs, normalMatrix, residual,
    ForwardModel.linearizationRemainder, hObservation, hPrior,
    Matrix.mulVec_mulVec, Matrix.mulVec_add, Matrix.add_mulVec,
    Matrix.mul_assoc, sub_eq_add_neg, Matrix.mulVec_neg]
  abel

/-
线性化余项的二次界和加权 Jacobian 的作用界给出正规缺陷的相对界。
这里 `rho` 控制余项，`beta` 控制观测权重与 Jacobian 的组合，
`radius` 是目标邻域半径。
-/
theorem normalDefectBound_of_quadraticRemainder
    (p : NonlinearProblem n m) (x target : State n) (k : Jacobian n m)
    {beta rho radius : ℝ}
    (hObservation : p.observation = p.model.observe target)
    (hPrior : p.priorMean = target)
    (hBeta : 0 ≤ beta)
    (hRho : 0 ≤ rho)
    (hRadius : ‖x - target‖ ≤ radius)
    (hAction : p.WeightedJacobianActionBound k beta)
    (hRemainder : p.model.QuadraticRemainderBound x target k rho) :
    p.NormalDefectBound x target k (beta * rho * radius) := by
  unfold ForwardModel.QuadraticRemainderBound at hRemainder
  have hRemainder' :
      ‖p.model.linearizationRemainder x target k‖ ≤
        rho * ‖x - target‖ ^ 2 := by
    simpa only [norm_sub_rev] using hRemainder
  unfold NormalDefectBound
  rw [normalDefect_eq_weighted_linearizationRemainder p x target k
    hObservation hPrior]
  have hSquare : ‖x - target‖ ^ 2 ≤ radius * ‖x - target‖ := by
    rw [pow_two]
    exact mul_le_mul_of_nonneg_right hRadius (norm_nonneg _)
  calc
    ‖k.conjTranspose.mulVec
        (p.observationWeight.mulVec
          (p.model.linearizationRemainder x target k))‖ ≤
        beta * ‖p.model.linearizationRemainder x target k‖ := hAction _
    _ ≤ beta * (rho * ‖x - target‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hRemainder' hBeta
    _ ≤ beta * (rho * (radius * ‖x - target‖)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hSquare hRho) hBeta
    _ = beta * rho * radius * ‖x - target‖ := by
      ring

/-! ## 从逐步界到轨迹收缩 -/

/-- 每一步的逆作用界和正规缺陷界可直接组成沿轨迹的收缩契约。 -/
theorem contractsTowardAlong_of_inverse_and_defect
    (p : NonlinearProblem n m)
    (jacobian : ℕ → State n → Jacobian n m) (initial target : State n)
    {gamma eta : ℝ}
    (hGamma : 0 ≤ gamma)
    (hNormal : ∀ i, IsUnit (p.normalMatrix
      (p.gaussNewtonIterate jacobian initial i)
      (jacobian i (p.gaussNewtonIterate jacobian initial i))))
    (hInverse : ∀ i, p.InverseActionBound
      (p.gaussNewtonIterate jacobian initial i)
      (jacobian i (p.gaussNewtonIterate jacobian initial i)) gamma)
    (hDefect : ∀ i, p.NormalDefectBound
      (p.gaussNewtonIterate jacobian initial i) target
      (jacobian i (p.gaussNewtonIterate jacobian initial i)) eta) :
    p.ContractsTowardAlong jacobian initial target (gamma * eta) := by
  intro i
  exact p.gaussNewtonUpdate_error_le_of_inverse_and_defect
    (p.gaussNewtonIterate jacobian initial i) target
    (jacobian i (p.gaussNewtonIterate jacobian initial i))
    (hNormal i) hGamma (hInverse i) (hDefect i)

end
end LeanOEM.NonlinearProblem

