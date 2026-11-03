module

public import LeanOEM.Core.PriorWhitening

/-!
# 奇异先验的支持因子白化

`PriorFactor` 处理可逆的方阵因子。本文件增加一个不要求先验正定的矩形因子接口：
给定满列秩的 `L : n × r` 和 `Sₐ = L Lᴴ`，`Fin r` 表示先验协方差的支持坐标。
在这些坐标中使用单位先验，避免把奇异矩阵的总函数逆解释成伪逆。

本批只证明支持坐标中的谱和 DOFS 结果。原 ambient averaging kernel 与支持矩阵的
完整特征多项式关系需要额外的非可逆因子理论，不在此接口中隐含声称。
-/

@[expose] public section

namespace LeanOEM

noncomputable section

open scoped MatrixOrder BigOperators

/-- 半正定先验的自动平方根因子。

该因子允许奇异；它的 `support` 是平方根矩阵的线性映射像空间。
矩形满列秩坐标因子仍由 `Problem.SupportFactor` 单独表示。
-/
structure Problem.PriorSqrtFactor {n m : ℕ} (p : Problem n m) where
  matrix : Square n
  matrix_posSemidef : matrix.PosSemidef
  covariance_eq : p.priorCovariance = matrix * matrix.conjTranspose

namespace Problem.PriorSqrtFactor

variable {n m : ℕ} {p : Problem n m}

open scoped MatrixOrder in
/-- 用 Mathlib 的精确矩阵平方根自动构造半正定先验因子。 -/
def ofPosSemidef (hPrior : p.priorCovariance.PosSemidef) :
    p.PriorSqrtFactor where
  matrix := CFC.sqrt p.priorCovariance
  matrix_posSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)
  covariance_eq := by
    have hSqrt : (CFC.sqrt p.priorCovariance).PosSemidef :=
      Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg p.priorCovariance)
    have hHermitian := hSqrt.isHermitian.eq
    rw [hHermitian, CFC.sqrt_mul_sqrt_self _ hPrior.nonneg]

/-- 平方根因子对应的 canonical support 子空间。 -/
def support (f : p.PriorSqrtFactor) : Submodule ℝ (State n) :=
  LinearMap.range f.matrix.mulVecLin

/-- support 成员正是平方根矩阵作用得到的状态向量。 -/
theorem mem_support_iff (f : p.PriorSqrtFactor) (v : State n) :
    v ∈ f.support ↔ ∃ x : State n, f.matrix.mulVec x = v := by
  rfl

/-- 因子恒等式给出原先验半正定。 -/
theorem prior_posSemidef (f : p.PriorSqrtFactor) :
    p.priorCovariance.PosSemidef := by
  rw [f.covariance_eq]
  exact Matrix.posSemidef_self_mul_conjTranspose f.matrix

/-- canonical support 的维数等于先验协方差的矩阵秩。 -/
theorem support_finrank_eq_priorCovariance_rank (f : p.PriorSqrtFactor) :
    Module.finrank ℝ f.support = p.priorCovariance.rank := by
  calc
    Module.finrank ℝ f.support = f.matrix.rank := by rfl
    _ = (f.matrix * f.matrix.conjTranspose).rank :=
      (Matrix.rank_self_mul_conjTranspose f.matrix).symm
    _ = p.priorCovariance.rank := by rw [f.covariance_eq]

end Problem.PriorSqrtFactor

/-- 半正定先验的矩形支持因子。

`matrix` 把 `Fin r` 的支持坐标注入完整状态空间；`covariance_eq` 将其 Gram 矩阵
识别为原先验协方差。`r = 0` 允许零先验协方差。
-/
structure Problem.SupportFactor {n m r : ℕ} (p : Problem n m) where
  matrix : Matrix (Fin n) (Fin r) ℝ
  injective : Function.Injective matrix.mulVec
  covariance_eq : p.priorCovariance = matrix * matrix.conjTranspose

namespace Problem.SupportFactor

variable {n m r : ℕ} {p : Problem n m}

/-- 支持坐标中的 Jacobian。 -/
def supportJacobian (f : @Problem.SupportFactor n m r p) : Matrix (Fin m) (Fin r) ℝ :=
  p.jacobian * f.matrix

/-- 支持坐标中的白化 averaging kernel。 -/
def whitenedAveragingKernel (f : @Problem.SupportFactor n m r p) : Square r :=
  (f.supportJacobian).conjTranspose * p.innovationCovariance⁻¹ * f.supportJacobian

/-- 支持坐标问题使用单位先验；它只用于复用已有正定先验定理。 -/
private def coordinateProblem (f : @Problem.SupportFactor n m r p) : Problem r m where
  jacobian := f.supportJacobian
  priorMean := 0
  priorCovariance := 1
  observationErrorCovariance := p.observationErrorCovariance

private theorem coordinateProblem_innovation (f : @Problem.SupportFactor n m r p) :
    (coordinateProblem f).innovationCovariance = p.innovationCovariance := by
  simp [coordinateProblem, Problem.innovationCovariance, supportJacobian,
    f.covariance_eq, Matrix.mul_assoc]

/-- 支持坐标问题的单位先验因子。 -/
private def unitPriorFactor (f : @Problem.SupportFactor n m r p) :
    (coordinateProblem f).PriorFactor where
  matrix := 1
  isUnit := by simp
  covariance_eq := by simp [coordinateProblem]

private theorem unit_whitened_eq (f : @Problem.SupportFactor n m r p) :
    (unitPriorFactor f).whitenedAveragingKernel = f.whitenedAveragingKernel := by
  unfold Problem.PriorFactor.whitenedAveragingKernel
  rw [coordinateProblem_innovation f]
  simp [unitPriorFactor, coordinateProblem, whitenedAveragingKernel, supportJacobian]

/-- 因子恒等式本身给出原先验的半正定性。 -/
theorem prior_posSemidef (f : @Problem.SupportFactor n m r p) :
    p.priorCovariance.PosSemidef := by
  rw [f.covariance_eq]
  exact Matrix.posSemidef_self_mul_conjTranspose f.matrix

/-- 满列秩支持因子的矩阵秩就是支持坐标维数。 -/
theorem matrix_rank_eq_support_dim (f : @Problem.SupportFactor n m r p) :
    f.matrix.rank = r := by
  rw [Matrix.rank, LinearMap.finrank_range_of_inj f.injective, Module.finrank_pi]
  simp

/-- 先验协方差的秩等于支持坐标维数。 -/
theorem priorCovariance_rank_eq_support_dim (f : @Problem.SupportFactor n m r p) :
    p.priorCovariance.rank = r := by
  rw [f.covariance_eq, Matrix.rank_self_mul_conjTranspose,
    f.matrix_rank_eq_support_dim]

/-- 支持白化矩阵在正定观测误差下半正定。 -/
theorem whitenedAveragingKernel_posSemidef (f : @Problem.SupportFactor n m r p)
    (hObservation : p.observationErrorCovariance.PosDef) :
    f.whitenedAveragingKernel.PosSemidef := by
  exact (innovationCovariance_inv_posDef p f.prior_posSemidef hObservation).posSemidef
    |>.conjTranspose_mul_mul_same f.supportJacobian

/-- 支持白化矩阵的补矩阵正定。 -/
theorem one_sub_whitenedAveragingKernel_posDef (f : @Problem.SupportFactor n m r p)
    (hObservation : p.observationErrorCovariance.PosDef) :
    (1 - f.whitenedAveragingKernel).PosDef := by
  have hPost : posteriorCovariance (coordinateProblem f) =
      1 - f.whitenedAveragingKernel := by
    unfold posteriorCovariance
    rw [coordinateProblem_innovation f]
    simp [coordinateProblem, whitenedAveragingKernel, supportJacobian]
  rw [← hPost]
  exact posteriorCovariance_posDef (coordinateProblem f) Matrix.PosDef.one hObservation

/-- 支持白化矩阵的特征值。 -/
def eigenvalues (f : @Problem.SupportFactor n m r p)
    (hObservation : p.observationErrorCovariance.PosDef) : Fin r → ℝ :=
  (f.whitenedAveragingKernel_posSemidef hObservation).isHermitian.eigenvalues

/-- 支持白化矩阵的每个特征值属于 `[0, 1]`。 -/
theorem eigenvalues_bounds (f : @Problem.SupportFactor n m r p)
    (hObservation : p.observationErrorCovariance.PosDef) (i : Fin r) :
    0 ≤ f.eigenvalues hObservation i ∧ f.eigenvalues hObservation i ≤ 1 := by
  exact eigenvalues_bounds_of_posSemidef f.whitenedAveragingKernel
    (f.whitenedAveragingKernel_posSemidef hObservation)
    (f.one_sub_whitenedAveragingKernel_posDef hObservation).posSemidef i

/-- 正定观测误差使支持白化矩阵的特征值严格小于 `1`。 -/
theorem eigenvalues_lt_one (f : @Problem.SupportFactor n m r p)
    (hObservation : p.observationErrorCovariance.PosDef) (i : Fin r) :
    f.eigenvalues hObservation i < 1 := by
  exact eigenvalues_lt_one_of_complement_posDef f.whitenedAveragingKernel
    (f.whitenedAveragingKernel_posSemidef hObservation)
    (f.one_sub_whitenedAveragingKernel_posDef hObservation) i

/-- 支持子空间上的可辨识性。 -/
def observableOnSupport (f : @Problem.SupportFactor n m r p) : Prop :=
  Observable f.supportJacobian

/-- 支持子空间可辨识时，支持白化矩阵正定。 -/
theorem whitenedAveragingKernel_posDef_of_observableOnSupport
    (f : @Problem.SupportFactor n m r p)
    (hObservation : p.observationErrorCovariance.PosDef)
    (hObservable : f.observableOnSupport) :
    f.whitenedAveragingKernel.PosDef := by
  exact Matrix.PosDef.conjTranspose_mul_mul_same
    (innovationCovariance_inv_posDef p f.prior_posSemidef hObservation)
    hObservable

/-- 支持子空间可辨识时，支持白化矩阵的特征值严格为正。 -/
theorem eigenvalues_pos_of_observableOnSupport (f : @Problem.SupportFactor n m r p)
    (hObservation : p.observationErrorCovariance.PosDef)
    (hObservable : f.observableOnSupport) (i : Fin r) :
    0 < f.eigenvalues hObservation i := by
  exact (f.whitenedAveragingKernel_posDef_of_observableOnSupport
    hObservation hObservable).eigenvalues_pos i

/-- 支持白化矩阵存在零谱当且仅当支持 Jacobian 不可辨识。 -/
theorem whitenedAveragingKernel_zero_mem_spectrum_iff_not_observableOnSupport
    (f : @Problem.SupportFactor n m r p) (hObservation : p.observationErrorCovariance.PosDef) :
    (0 : ℝ) ∈ spectrum ℝ f.whitenedAveragingKernel ↔
      ¬ f.observableOnSupport := by
  rw [← unit_whitened_eq f]
  simpa [unitPriorFactor, coordinateProblem, supportJacobian,
    observableOnSupport] using
    (unitPriorFactor f).whitenedAveragingKernel_zero_mem_spectrum_iff_not_observable
      hObservation

/-- 支持白化矩阵的秩等于支持 Jacobian 的秩。 -/
theorem whitenedAveragingKernel_rank_eq (f : @Problem.SupportFactor n m r p)
    (hObservation : p.observationErrorCovariance.PosDef) :
    f.whitenedAveragingKernel.rank = f.supportJacobian.rank := by
  rw [← unit_whitened_eq f]
  simpa [coordinateProblem, supportJacobian] using
    (unitPriorFactor f).whitenedAveragingKernel_rank_eq hObservation

/-- 原 ambient DOFS 等于支持坐标白化矩阵的迹。 -/
theorem dofs_eq_support_trace (f : @Problem.SupportFactor n m r p) :
    p.dofs = Matrix.trace f.whitenedAveragingKernel := by
  unfold Problem.dofs LeanOEM.dofs averagingKernel Problem.gain
  simp only [f.covariance_eq, whitenedAveragingKernel, supportJacobian,
    Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm]
  simp [Matrix.mul_assoc]

/-- 原 ambient DOFS 等于单位先验支持坐标问题的 DOFS。 -/
private theorem dofs_eq_coordinateProblem_dofs (f : @Problem.SupportFactor n m r p) :
    p.dofs = (coordinateProblem f).dofs := by
  rw [dofs_eq_support_trace f]
  unfold Problem.dofs LeanOEM.dofs averagingKernel Problem.gain
  rw [coordinateProblem_innovation f]
  simp [coordinateProblem, supportJacobian, whitenedAveragingKernel,
    Matrix.mul_assoc]

/-- DOFS 等于支持白化矩阵特征值之和。 -/
theorem dofs_eq_sum_eigenvalues (f : @Problem.SupportFactor n m r p)
    (hObservation : p.observationErrorCovariance.PosDef) :
    p.dofs = ∑ i, f.eigenvalues hObservation i := by
  simpa [eigenvalues] using
    (dofs_eq_support_trace f).trans
      (f.whitenedAveragingKernel_posSemidef hObservation).isHermitian.trace_eq_sum_eigenvalues

/-- DOFS 不超过支持坐标维数。 -/
theorem dofs_le_support_dim (f : @Problem.SupportFactor n m r p)
    (hObservation : p.observationErrorCovariance.PosDef) :
    p.dofs ≤ (r : ℝ) := by
  rw [dofs_eq_coordinateProblem_dofs f]
  exact ((coordinateProblem f).dofs_le_dim_of_posDef Matrix.PosDef.one hObservation)

/-- 非空支持坐标下，正定观测误差给出严格的支持维数上界。 -/
theorem dofs_lt_support_dim (f : @Problem.SupportFactor n m r p)
    (hObservation : p.observationErrorCovariance.PosDef) (hSupport : 0 < r) :
    p.dofs < (r : ℝ) := by
  rw [dofs_eq_coordinateProblem_dofs f]
  exact (unitPriorFactor f).dofs_lt_state_dim hObservation hSupport

/-- DOFS 不超过支持 Jacobian 的秩。 -/
theorem dofs_le_support_jacobian_rank (f : @Problem.SupportFactor n m r p)
    (hObservation : p.observationErrorCovariance.PosDef) :
    p.dofs ≤ (f.supportJacobian.rank : ℝ) := by
  rw [dofs_eq_coordinateProblem_dofs f]
  simpa [coordinateProblem, supportJacobian] using
    (unitPriorFactor f).dofs_le_jacobian_rank hObservation

/-- DOFS 不超过先验协方差的秩。 -/
theorem dofs_le_priorCovariance_rank (f : @Problem.SupportFactor n m r p)
    (hObservation : p.observationErrorCovariance.PosDef) :
    p.dofs ≤ (p.priorCovariance.rank : ℝ) := by
  rw [f.priorCovariance_rank_eq_support_dim]
  exact f.dofs_le_support_dim hObservation

end Problem.SupportFactor

end
end LeanOEM
