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

/-- 给定目标 Jacobian 时，目标状态满足非线性 MAP 一阶驻点的契约。 -/
def TargetStationary (p : NonlinearProblem n m) (target : State n)
    (kTarget : Jacobian n m) : Prop :=
  p.normalRhs target kTarget = 0

/-- Jacobian 变化对目标残差的加权作用界。 -/
def JacobianVariationActionBound (p : NonlinearProblem n m)
    (x target : State n) (k kTarget : Jacobian n m) (delta : ℝ) : Prop :=
  ∀ v, ‖k.conjTranspose.mulVec (p.observationWeight.mulVec v) -
      kTarget.conjTranspose.mulVec (p.observationWeight.mulVec v)‖ ≤
    delta * ‖x - target‖ * ‖v‖

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

/-! ## 一般驻点目标与 Jacobian 变化 -/

/--
正规缺陷的一般分解：目标驻点残差、Jacobian 变化和当前线性化余项分别出现。
该恒等式本身不要求目标驻点；最后一项保留目标处的正规方程右端。
-/
theorem normalDefect_eq_jacobianVariation_add_remainder_add_stationarity
    (p : NonlinearProblem n m) (x target : State n)
    (k kTarget : Jacobian n m) :
    p.normalDefect x target k =
      k.conjTranspose.mulVec (p.observationWeight.mulVec (p.residual target)) -
          kTarget.conjTranspose.mulVec (p.observationWeight.mulVec (p.residual target))
        + k.conjTranspose.mulVec
          (p.observationWeight.mulVec
            (p.model.linearizationRemainder x target k))
        + p.normalRhs target kTarget := by
  simp [normalDefect, normalRhs, normalMatrix, residual,
    ForwardModel.linearizationRemainder, Matrix.mulVec_mulVec,
    Matrix.mulVec_add,
    Matrix.add_mulVec, Matrix.mul_assoc, sub_eq_add_neg,
    Matrix.mulVec_neg]
  abel

/-- 目标满足驻点契约时，正规缺陷只剩 Jacobian 变化项和线性化余项。 -/
theorem normalDefect_eq_jacobianVariation_add_remainder_of_stationary
    (p : NonlinearProblem n m) (x target : State n)
    (k kTarget : Jacobian n m)
    (hStationary : p.TargetStationary target kTarget) :
    p.normalDefect x target k =
      k.conjTranspose.mulVec (p.observationWeight.mulVec (p.residual target)) -
          kTarget.conjTranspose.mulVec (p.observationWeight.mulVec (p.residual target))
        + k.conjTranspose.mulVec
          (p.observationWeight.mulVec
            (p.model.linearizationRemainder x target k)) := by
  rw [normalDefect_eq_jacobianVariation_add_remainder_add_stationarity
    p x target k kTarget]
  change p.normalRhs target kTarget = 0 at hStationary
  rw [hStationary, add_zero]

/--
一般驻点目标下，Jacobian 变化项和线性化余项共同给出正规缺陷的相对界。
`delta` 控制 Jacobian 变化，`sigma` 控制目标残差，`beta` 和 `rho` 控制当前
线性化余项；所有量都保持为显式契约。
-/
theorem normalDefectBound_of_stationary_target
    (p : NonlinearProblem n m) (x target : State n)
    (k kTarget : Jacobian n m)
    {delta sigma beta rho radius : ℝ}
    (hStationary : p.TargetStationary target kTarget)
    (hDelta : 0 ≤ delta)
    (hBeta : 0 ≤ beta)
    (hRho : 0 ≤ rho)
    (hRadius : ‖x - target‖ ≤ radius)
    (hResidual : ‖p.residual target‖ ≤ sigma)
    (hVariation : p.JacobianVariationActionBound x target k kTarget delta)
    (hAction : p.WeightedJacobianActionBound k beta)
    (hRemainder : p.model.QuadraticRemainderBound x target k rho) :
    p.NormalDefectBound x target k (delta * sigma + beta * rho * radius) := by
  unfold NormalDefectBound
  rw [normalDefect_eq_jacobianVariation_add_remainder_of_stationary
    p x target k kTarget hStationary]
  unfold ForwardModel.QuadraticRemainderBound at hRemainder
  have hRemainder' :
      ‖p.model.linearizationRemainder x target k‖ ≤
        rho * ‖x - target‖ ^ 2 := by
    simpa only [norm_sub_rev] using hRemainder
  have hSquare : ‖x - target‖ ^ 2 ≤ radius * ‖x - target‖ := by
    rw [pow_two]
    exact mul_le_mul_of_nonneg_right hRadius (norm_nonneg _)
  have hVariationTerm :
      ‖k.conjTranspose.mulVec (p.observationWeight.mulVec (p.residual target)) -
          kTarget.conjTranspose.mulVec (p.observationWeight.mulVec
            (p.residual target))‖ ≤
        delta * sigma * ‖x - target‖ := by
    calc
      ‖k.conjTranspose.mulVec (p.observationWeight.mulVec (p.residual target)) -
          kTarget.conjTranspose.mulVec (p.observationWeight.mulVec
            (p.residual target))‖ ≤
          delta * ‖x - target‖ * ‖p.residual target‖ := hVariation _
      _ ≤ delta * ‖x - target‖ * sigma := by
        exact mul_le_mul_of_nonneg_left hResidual
          (mul_nonneg hDelta (norm_nonneg _))
      _ = delta * sigma * ‖x - target‖ := by ring
  have hRemainderTerm :
      ‖k.conjTranspose.mulVec
          (p.observationWeight.mulVec
            (p.model.linearizationRemainder x target k))‖ ≤
        beta * rho * radius * ‖x - target‖ := by
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
      _ = beta * rho * radius * ‖x - target‖ := by ring
  calc
    ‖k.conjTranspose.mulVec (p.observationWeight.mulVec (p.residual target)) -
          kTarget.conjTranspose.mulVec (p.observationWeight.mulVec
            (p.residual target))
        + k.conjTranspose.mulVec
          (p.observationWeight.mulVec
            (p.model.linearizationRemainder x target k))‖ ≤
        delta * sigma * ‖x - target‖ +
          beta * rho * radius * ‖x - target‖ := by
            exact (norm_add_le _ _).trans
              (add_le_add hVariationTerm hRemainderTerm)
    _ = (delta * sigma + beta * rho * radius) * ‖x - target‖ := by
      ring

/--
当目标只满足近似驻点时，驻点残差以加性项进入正规缺陷界。
`tau` 可以记录 Jacobian 离散化、目标残差或其他一阶条件误差。
-/
theorem normalDefect_additive_bound_of_stationarity_residual
    (p : NonlinearProblem n m) (x target : State n)
    (k kTarget : Jacobian n m)
    {delta sigma beta rho radius tau : ℝ}
    (hDelta : 0 ≤ delta)
    (hBeta : 0 ≤ beta)
    (hRho : 0 ≤ rho)
    (hRadius : ‖x - target‖ ≤ radius)
    (hResidual : ‖p.residual target‖ ≤ sigma)
    (hVariation : p.JacobianVariationActionBound x target k kTarget delta)
    (hAction : p.WeightedJacobianActionBound k beta)
    (hRemainder : p.model.QuadraticRemainderBound x target k rho)
    (hStationarityResidual : ‖p.normalRhs target kTarget‖ ≤ tau) :
    ‖p.normalDefect x target k‖ ≤
      (delta * sigma + beta * rho * radius) * ‖x - target‖ + tau := by
  rw [normalDefect_eq_jacobianVariation_add_remainder_add_stationarity
    p x target k kTarget]
  unfold ForwardModel.QuadraticRemainderBound at hRemainder
  have hRemainder' :
      ‖p.model.linearizationRemainder x target k‖ ≤
        rho * ‖x - target‖ ^ 2 := by
    simpa only [norm_sub_rev] using hRemainder
  have hSquare : ‖x - target‖ ^ 2 ≤ radius * ‖x - target‖ := by
    rw [pow_two]
    exact mul_le_mul_of_nonneg_right hRadius (norm_nonneg _)
  have hVariationTerm :
      ‖k.conjTranspose.mulVec (p.observationWeight.mulVec (p.residual target)) -
          kTarget.conjTranspose.mulVec (p.observationWeight.mulVec
            (p.residual target))‖ ≤
        delta * sigma * ‖x - target‖ := by
    calc
      ‖k.conjTranspose.mulVec (p.observationWeight.mulVec (p.residual target)) -
          kTarget.conjTranspose.mulVec (p.observationWeight.mulVec
            (p.residual target))‖ ≤
          delta * ‖x - target‖ * ‖p.residual target‖ := hVariation _
      _ ≤ delta * ‖x - target‖ * sigma := by
        exact mul_le_mul_of_nonneg_left hResidual
          (mul_nonneg hDelta (norm_nonneg _))
      _ = delta * sigma * ‖x - target‖ := by ring
  have hRemainderTerm :
      ‖k.conjTranspose.mulVec
          (p.observationWeight.mulVec
            (p.model.linearizationRemainder x target k))‖ ≤
        beta * rho * radius * ‖x - target‖ := by
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
      _ = beta * rho * radius * ‖x - target‖ := by ring
  calc
    ‖k.conjTranspose.mulVec (p.observationWeight.mulVec (p.residual target)) -
          kTarget.conjTranspose.mulVec (p.observationWeight.mulVec
            (p.residual target))
        + k.conjTranspose.mulVec
          (p.observationWeight.mulVec
            (p.model.linearizationRemainder x target k))
        + p.normalRhs target kTarget‖ ≤
        delta * sigma * ‖x - target‖ +
          beta * rho * radius * ‖x - target‖ + tau := by
            exact (norm_add_le _ _).trans <| add_le_add
              ((norm_add_le _ _).trans
                (add_le_add hVariationTerm hRemainderTerm))
              hStationarityResidual
    _ = (delta * sigma + beta * rho * radius) * ‖x - target‖ + tau := by
      ring

/-- 加性正规缺陷界导致带误差底的单步更新界。 -/
theorem gaussNewtonUpdate_error_le_of_inverse_and_additive_defect
    (p : NonlinearProblem n m) (x target : State n) (k : Jacobian n m)
    {gamma eta tau : ℝ} (hNormal : IsUnit (p.normalMatrix x k))
    (hGamma : 0 ≤ gamma)
    (hInverse : p.InverseActionBound x k gamma)
    (hDefect : ‖p.normalDefect x target k‖ ≤
      eta * ‖x - target‖ + tau) :
    ‖p.gaussNewtonUpdate x k - target‖ ≤
      gamma * eta * ‖x - target‖ + gamma * tau := by
  rw [p.gaussNewtonUpdate_sub_target_eq_inverse_normalDefect x target k hNormal]
  calc
    ‖(p.normalMatrix x k)⁻¹.mulVec (p.normalDefect x target k)‖ ≤
        gamma * ‖p.normalDefect x target k‖ := hInverse _
    _ ≤ gamma * (eta * ‖x - target‖ + tau) :=
      mul_le_mul_of_nonneg_left hDefect hGamma
    _ = gamma * eta * ‖x - target‖ + gamma * tau := by ring

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

