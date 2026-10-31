module

public import LeanOEM.Core.NonlinearOEM
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel

/-!
# Gauss–Newton 迭代和有条件的停止误差界

沿轨迹的收缩是调用者需要证明的条件，不由单步正规方程自动推出。
目标点不自动具有 MAP 最优性。所有范数沿用 `State n` 的最大绝对分量范数。
-/

@[expose] public section

namespace LeanOEM.NonlinearProblem

open Filter
open scoped Topology

noncomputable section

/-- 精确实数迭代轨迹；策略按迭代编号和当前状态给出 Jacobian 候选矩阵。

刷新策略可写成 `fun _ x => K x`，冻结策略可写成 `fun _ _ => k`。
该定义不保证候选矩阵是模型导数，也不保证正规矩阵可逆。
-/
def gaussNewtonIterate (p : NonlinearProblem n m)
    (jacobian : ℕ → State n → Jacobian n m) (initial : State n) : ℕ → State n
  | 0 => initial
  | i + 1 =>
      let x := gaussNewtonIterate p jacobian initial i
      p.gaussNewtonUpdate x (jacobian i x)

@[simp] theorem gaussNewtonIterate_zero (p : NonlinearProblem n m)
    (jacobian : ℕ → State n → Jacobian n m) (initial : State n) :
    p.gaussNewtonIterate jacobian initial 0 = initial := rfl

@[simp] theorem gaussNewtonIterate_succ (p : NonlinearProblem n m)
    (jacobian : ℕ → State n → Jacobian n m) (initial : State n) (i : ℕ) :
    p.gaussNewtonIterate jacobian initial (i + 1) =
      p.gaussNewtonUpdate (p.gaussNewtonIterate jacobian initial i)
        (jacobian i (p.gaussNewtonIterate jacobian initial i)) := rfl

/-- 相邻轨迹点之差等于当前状态上尚未施加的增量。 -/
theorem gaussNewtonIterate_succ_sub (p : NonlinearProblem n m)
    (jacobian : ℕ → State n → Jacobian n m) (initial : State n) (i : ℕ) :
    p.gaussNewtonIterate jacobian initial (i + 1) -
        p.gaussNewtonIterate jacobian initial i =
      p.gaussNewtonStep (p.gaussNewtonIterate jacobian initial i)
        (jacobian i (p.gaussNewtonIterate jacobian initial i)) := by
  simp only [gaussNewtonIterate_succ, gaussNewtonUpdate, add_sub_cancel_left]

/-- 非负绝对容差下的步长停止判据；满足时返回当前状态，尚未施加本步增量。

这是实数上的命题规格，不是浮点求解器或成功标志。零容差不保证有限步满足。
-/
def StepSmall (p : NonlinearProblem n m) (x : State n) (k : Jacobian n m)
    (tolerance : ℝ) : Prop :=
  0 ≤ tolerance ∧ ‖p.gaussNewtonStep x k‖ ≤ tolerance

/-- 第 `i` 个轨迹状态满足步长停止判据；不声称首次停止或达到 MAP 最优点。 -/
def StoppedAt (p : NonlinearProblem n m)
    (jacobian : ℕ → State n → Jacobian n m) (initial : State n)
    (tolerance : ℝ) (i : ℕ) : Prop :=
  p.StepSmall (p.gaussNewtonIterate jacobian initial i)
    (jacobian i (p.gaussNewtonIterate jacobian initial i)) tolerance

/-- 给定目标状态时的正规方程缺陷。 -/
def normalDefect (p : NonlinearProblem n m) (x target : State n)
    (k : Jacobian n m) : State n :=
  p.normalRhs x k - (p.normalMatrix x k).mulVec (target - x)

/-- 正规矩阵逆作用在状态范数下的显式界。 -/
def InverseActionBound (p : NonlinearProblem n m) (x : State n)
    (k : Jacobian n m) (gamma : ℝ) : Prop :=
  ∀ v, ‖(p.normalMatrix x k)⁻¹.mulVec v‖ ≤ gamma * ‖v‖

/-- 给定目标时正规方程缺陷的局部界。 -/
def NormalDefectBound (p : NonlinearProblem n m) (x target : State n)
    (k : Jacobian n m) (eta : ℝ) : Prop :=
  ‖p.normalDefect x target k‖ ≤ eta * ‖x - target‖

/-- 可逆正规矩阵下，更新误差正好等于逆矩阵作用于正规方程缺陷。 -/
theorem gaussNewtonUpdate_sub_target_eq_inverse_normalDefect
    (p : NonlinearProblem n m) (x target : State n) (k : Jacobian n m)
    (hNormal : IsUnit (p.normalMatrix x k)) :
    p.gaussNewtonUpdate x k - target =
      (p.normalMatrix x k)⁻¹.mulVec (p.normalDefect x target k) := by
  unfold gaussNewtonUpdate gaussNewtonStep normalDefect
  have hDet : IsUnit (p.normalMatrix x k).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hNormal
  have hInv : (p.normalMatrix x k)⁻¹.mulVec
      ((p.normalMatrix x k).mulVec (target - x)) = target - x := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hDet, Matrix.one_mulVec]
  rw [Matrix.mulVec_sub, hInv]
  abel

/-- 逆作用界和正规方程缺陷界给出单步的误差界。 -/
theorem gaussNewtonUpdate_error_le_of_inverse_and_defect
    (p : NonlinearProblem n m) (x target : State n) (k : Jacobian n m)
    {gamma eta : ℝ} (hNormal : IsUnit (p.normalMatrix x k))
    (hGamma : 0 ≤ gamma)
    (hInverse : p.InverseActionBound x k gamma)
    (hDefect : p.NormalDefectBound x target k eta) :
    ‖p.gaussNewtonUpdate x k - target‖ ≤
      gamma * eta * ‖x - target‖ := by
  rw [p.gaussNewtonUpdate_sub_target_eq_inverse_normalDefect x target k hNormal]
  calc
    ‖(p.normalMatrix x k)⁻¹.mulVec (p.normalDefect x target k)‖ ≤
        gamma * ‖p.normalDefect x target k‖ := hInverse _
    _ ≤ gamma * (eta * ‖x - target‖) :=
      mul_le_mul_of_nonneg_left hDefect hGamma
    _ = gamma * eta * ‖x - target‖ := by ring

/-- 可逆正规矩阵下，零增量恰好对应正规方程右端为零。 -/
theorem gaussNewtonStep_eq_zero_iff (p : NonlinearProblem n m)
    (x : State n) (k : Jacobian n m) (hNormal : IsUnit (p.normalMatrix x k)) :
    p.gaussNewtonStep x k = 0 ↔ p.normalRhs x k = 0 := by
  constructor
  · intro hStep
    have h := p.normalMatrix_mulVec_gaussNewtonStep x k hNormal
    rw [hStep, Matrix.mulVec_zero] at h
    exact h.symm
  · intro hRhs
    simp [gaussNewtonStep, hRhs]

/-- 更新在集合内保持封闭时，起点在集合内的整个轨迹也在集合内。 -/
theorem gaussNewtonIterate_mem (p : NonlinearProblem n m)
    (jacobian : ℕ → State n → Jacobian n m) (initial : State n)
    {domain : Set (State n)} (hInitial : initial ∈ domain)
    (hMaps : ∀ i, Set.MapsTo (fun x => p.gaussNewtonUpdate x (jacobian i x))
      domain domain) (i : ℕ) :
    p.gaussNewtonIterate jacobian initial i ∈ domain := by
  induction i with
  | zero => exact hInitial
  | succ i ih => exact hMaps i ih

/-- 对给定目标的沿轨迹收缩条件；目标的存在、最优性和物理意义不包含在定义内。 -/
def ContractsTowardAlong (p : NonlinearProblem n m)
    (jacobian : ℕ → State n → Jacobian n m) (initial target : State n)
    (q : ℝ) : Prop :=
  ∀ i, ‖p.gaussNewtonIterate jacobian initial (i + 1) - target‖ ≤
    q * ‖p.gaussNewtonIterate jacobian initial i - target‖

/-- 在不变集合内有共同不动点和 Lipschitz 界时，可得到沿轨迹条件。

当 `q < 1` 时，这些假设给出局部收缩；集合可以是经过单独验证的邻域。
-/
theorem contractsTowardAlong_of_lipschitzOn (p : NonlinearProblem n m)
    (jacobian : ℕ → State n → Jacobian n m) (initial target : State n)
    {domain : Set (State n)} (q : NNReal)
    (hInitial : initial ∈ domain) (hTarget : target ∈ domain)
    (hMaps : ∀ i, Set.MapsTo (fun x => p.gaussNewtonUpdate x (jacobian i x))
      domain domain)
    (hFixed : ∀ i, p.gaussNewtonUpdate target (jacobian i target) = target)
    (hLipschitz : ∀ i, LipschitzOnWith q
      (fun x => p.gaussNewtonUpdate x (jacobian i x)) domain) :
    p.ContractsTowardAlong jacobian initial target q := by
  intro i
  have h := (hLipschitz i).dist_le_mul _
    (p.gaussNewtonIterate_mem jacobian initial hInitial hMaps i) target hTarget
  simpa only [gaussNewtonIterate_succ, hFixed i, dist_eq_norm] using h

/-- 显式沿轨迹条件下的几何误差界；复用 Mathlib 的 `le_geom`。 -/
theorem gaussNewtonIterate_error_le (p : NonlinearProblem n m)
    (jacobian : ℕ → State n → Jacobian n m) (initial target : State n)
    {q : ℝ} (hq : 0 ≤ q)
    (hContract : p.ContractsTowardAlong jacobian initial target q) (i : ℕ) :
    ‖p.gaussNewtonIterate jacobian initial i - target‖ ≤ q ^ i * ‖initial - target‖ := by
  exact le_geom (u := fun j => ‖p.gaussNewtonIterate jacobian initial j - target‖)
    hq i (fun j _ => hContract j)

/-- `0 ≤ q < 1` 的沿轨迹收缩推出对给定目标的收敛。 -/
theorem gaussNewtonIterate_tendsto (p : NonlinearProblem n m)
    (jacobian : ℕ → State n → Jacobian n m) (initial target : State n)
    {q : ℝ} (hq : 0 ≤ q) (hqOne : q < 1)
    (hContract : p.ContractsTowardAlong jacobian initial target q) :
    Tendsto (p.gaussNewtonIterate jacobian initial) atTop (𝓝 target) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun i => norm_nonneg _) (p.gaussNewtonIterate_error_le
    jacobian initial target hq hContract)
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq hqOne).mul_const ‖initial - target‖

/-- 相邻更新误差收缩时，由实际增量控制当前状态到目标的误差。 -/
theorem error_le_step_div_one_sub (p : NonlinearProblem n m)
    (x target : State n) (k : Jacobian n m) {q : ℝ} (hqOne : q < 1)
    (hContract : ‖p.gaussNewtonUpdate x k - target‖ ≤ q * ‖x - target‖) :
    ‖x - target‖ ≤ ‖p.gaussNewtonStep x k‖ / (1 - q) := by
  have hTriangle : ‖x - target‖ ≤
      ‖p.gaussNewtonStep x k‖ + ‖p.gaussNewtonUpdate x k - target‖ := by
    have h := norm_add_le (-p.gaussNewtonStep x k) (p.gaussNewtonUpdate x k - target)
    have hDecomp : -p.gaussNewtonStep x k + (p.gaussNewtonUpdate x k - target) =
        x - target := by
      unfold gaussNewtonUpdate
      abel
    rw [hDecomp, norm_neg] at h
    exact h
  apply (le_div_iff₀ (sub_pos.mpr hqOne)).mpr
  nlinarith

/-- 停止时返回的当前状态误差界；收缩因子必须严格小于一。 -/
theorem stoppedAt_error_le (p : NonlinearProblem n m)
    (jacobian : ℕ → State n → Jacobian n m) (initial target : State n)
    {q tolerance : ℝ} (hqOne : q < 1)
    (hContract : p.ContractsTowardAlong jacobian initial target q) (i : ℕ)
    (hStop : p.StoppedAt jacobian initial tolerance i) :
    ‖p.gaussNewtonIterate jacobian initial i - target‖ ≤ tolerance / (1 - q) := by
  exact (p.error_le_step_div_one_sub _ target _ hqOne (hContract i)).trans
    (div_le_div_of_nonneg_right hStop.2 (sub_pos.mpr hqOne).le)

/-- 沿轨迹收缩同时控制下一步增量，供有限停止判据使用。 -/
theorem gaussNewtonIterate_step_le (p : NonlinearProblem n m)
    (jacobian : ℕ → State n → Jacobian n m) (initial target : State n)
    {q : ℝ} (hq : 0 ≤ q)
    (hContract : p.ContractsTowardAlong jacobian initial target q) (i : ℕ) :
    ‖p.gaussNewtonStep (p.gaussNewtonIterate jacobian initial i)
        (jacobian i (p.gaussNewtonIterate jacobian initial i))‖ ≤
      (q + 1) * (q ^ i * ‖initial - target‖) := by
  rw [← gaussNewtonIterate_succ_sub]
  have hTriangle := norm_sub_le
    (p.gaussNewtonIterate jacobian initial (i + 1) - target)
    (p.gaussNewtonIterate jacobian initial i - target)
  simp only [sub_sub_sub_cancel_right] at hTriangle
  have hBound := p.gaussNewtonIterate_error_le jacobian initial target hq hContract i
  have hShrink := hContract i
  nlinarith

/-- 正容差下最终满足停止条件；不适用于零容差或未经证明的收缩因子。 -/
theorem eventually_stoppedAt (p : NonlinearProblem n m)
    (jacobian : ℕ → State n → Jacobian n m) (initial target : State n)
    {q tolerance : ℝ} (hq : 0 ≤ q) (hqOne : q < 1) (hTolerance : 0 < tolerance)
    (hContract : p.ContractsTowardAlong jacobian initial target q) :
    ∀ᶠ i in atTop, p.StoppedAt jacobian initial tolerance i := by
  have hLimit : Tendsto (fun i => ‖p.gaussNewtonStep (p.gaussNewtonIterate jacobian initial i)
      (jacobian i (p.gaussNewtonIterate jacobian initial i))‖) atTop (𝓝 0) := by
    apply squeeze_zero (fun i => norm_nonneg _)
      (p.gaussNewtonIterate_step_le jacobian initial target hq hContract)
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hq hqOne).mul_const
      ‖initial - target‖).const_mul (q + 1)
  filter_upwards [hLimit.eventually (gt_mem_nhds hTolerance)] with i hi
  exact ⟨hTolerance.le, hi.le⟩

end
end LeanOEM.NonlinearProblem
