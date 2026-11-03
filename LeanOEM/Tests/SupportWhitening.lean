module

public import LeanOEM.Core.SupportWhitening
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-!
# 奇异先验支持白化的精确例子

例子使用 `Sₐ = diag(1, 0)`。第一维属于先验支持，第二维是零方差方向；
因此 ambient Jacobian 可以不可辨识，而支持坐标仍然可以可辨识。
-/

@[expose] public section

namespace LeanOEM.Tests.SupportWhitening

open LeanOEM Matrix

noncomputable section

private def singularProblem : Problem 2 1 where
  jacobian := !![1, 0]
  priorMean := 0
  priorCovariance := !![1, 0; 0, 0]
  observationErrorCovariance := 1

private def supportMatrix : Matrix (Fin 2) (Fin 1) ℝ := !![1; 0]

private def singularSupportFactor :
    @Problem.SupportFactor 2 1 1 singularProblem where
  matrix := supportMatrix
  injective := by
    intro x y hxy
    funext i
    fin_cases i
    have hFirst := congrFun hxy (0 : Fin 2)
    simpa [supportMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using hFirst
  covariance_eq := by
    change (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) =
      supportMatrix * supportMatrix.conjTranspose
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [singularProblem, supportMatrix, Matrix.mul_apply,
        Matrix.conjTranspose, Matrix.transpose, Fin.sum_univ_succ]

private lemma observation_posDef :
    singularProblem.observationErrorCovariance.PosDef :=
  Matrix.PosDef.one

private lemma innovation_eq : singularProblem.innovationCovariance = !![(2 : ℝ)] := by
  ext i j
  fin_cases i
  fin_cases j
  norm_num [Problem.innovationCovariance, singularProblem, Matrix.mul_apply,
    Matrix.conjTranspose, Fin.sum_univ_succ, Matrix.diagonal, Matrix.vecMul,
    dotProduct]

private lemma gain_eq : singularProblem.gain = !![(1 / 2 : ℝ); 0] := by
  unfold Problem.gain
  rw [innovation_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [singularProblem, Matrix.inv_diagonal, Matrix.mul_apply,
      Matrix.conjTranspose, Matrix.transpose, Matrix.diagonal, Matrix.vecMul,
      dotProduct, Fin.sum_univ_succ, Ring.inverse_eq_inv]

private lemma supportJacobian_eq :
    singularSupportFactor.supportJacobian = !![(1 : ℝ)] := by
  ext i j
  fin_cases i
  fin_cases j
  norm_num [Problem.SupportFactor.supportJacobian, singularSupportFactor,
    singularProblem, supportMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

private lemma supportWhitened_eq :
    singularSupportFactor.whitenedAveragingKernel = !![(1 / 2 : ℝ)] := by
  unfold Problem.SupportFactor.whitenedAveragingKernel
  rw [innovation_eq, supportJacobian_eq]
  ext i j
  fin_cases i
  fin_cases j
  norm_num [Matrix.inv_diagonal, Matrix.mul_apply, Matrix.conjTranspose,
    Matrix.diagonal, Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
    Ring.inverse_eq_inv]

/-- 奇异先验下，支持方向的白化矩阵仍然是正常的正定坐标问题。 -/
example : singularSupportFactor.whitenedAveragingKernel = !![(1 / 2 : ℝ)] :=
  supportWhitened_eq

/-- ambient averaging kernel 保留一个先验零方向。 -/
example : averagingKernel singularProblem.gain singularProblem.jacobian =
    !![(1 / 2 : ℝ), 0; 0, 0] := by
  rw [averagingKernel, gain_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [singularProblem, Matrix.mul_apply, Fin.sum_univ_succ]

/-- 支持坐标可辨识，但 ambient Jacobian 因零先验方向而不可辨识。 -/
private lemma support_observable : singularSupportFactor.observableOnSupport := by
  rw [Problem.SupportFactor.observableOnSupport, supportJacobian_eq]
  intro x y hxy
  funext i
  fin_cases i
  have hFirst := congrFun hxy (0 : Fin 1)
  simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using hFirst

example : singularSupportFactor.observableOnSupport := support_observable

private def canonicalSqrt :
    @Problem.PriorSqrtFactor 2 1 singularProblem :=
  Problem.PriorSqrtFactor.ofPosSemidef singularSupportFactor.prior_posSemidef

example : canonicalSqrt.matrix.PosSemidef :=
  canonicalSqrt.matrix_posSemidef

example (v : State 2) :
    v ∈ canonicalSqrt.support ↔ ∃ x : State 2, canonicalSqrt.matrix.mulVec x = v :=
  canonicalSqrt.mem_support_iff v

example : Module.finrank ℝ canonicalSqrt.support = 1 := by
  calc
    Module.finrank ℝ canonicalSqrt.support = singularProblem.priorCovariance.rank :=
      canonicalSqrt.support_finrank_eq_priorCovariance_rank
    _ = 1 := by
      exact singularSupportFactor.priorCovariance_rank_eq_support_dim

example : ¬ Observable singularProblem.jacobian := by
  intro hObservable
  have hEqual : singularProblem.jacobian.mulVec (![0, 0] : State 2) =
      singularProblem.jacobian.mulVec (![0, 1] : State 2) := by
    funext i
    fin_cases i
    norm_num [singularProblem, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  have hStates := hObservable hEqual
  norm_num at hStates

/-- 支持白化 DOFS 与 ambient DOFS 相等，且只计入先验支持方向。 -/
example : singularProblem.dofs = (1 / 2 : ℝ) := by
  rw [singularSupportFactor.dofs_eq_support_trace, supportWhitened_eq]
  norm_num [Matrix.trace_fin_one]

example : (∑ i, singularSupportFactor.eigenvalues observation_posDef i) =
    (1 / 2 : ℝ) := by
  rw [← singularSupportFactor.dofs_eq_sum_eigenvalues observation_posDef]
  rw [singularSupportFactor.dofs_eq_support_trace, supportWhitened_eq]
  norm_num [Matrix.trace_fin_one]

example (i : Fin 1) :
    0 < singularSupportFactor.eigenvalues observation_posDef i :=
  singularSupportFactor.eigenvalues_pos_of_observableOnSupport
    observation_posDef support_observable i

example : singularProblem.dofs ≤ (1 : ℝ) := by
  simpa using singularSupportFactor.dofs_le_support_dim observation_posDef

example : singularProblem.dofs ≤
    (singularSupportFactor.supportJacobian.rank : ℝ) := by
  exact singularSupportFactor.dofs_le_support_jacobian_rank observation_posDef

example : singularSupportFactor.matrix.rank = 1 := by
  exact singularSupportFactor.matrix_rank_eq_support_dim

example : singularProblem.priorCovariance.rank = 1 := by
  exact singularSupportFactor.priorCovariance_rank_eq_support_dim

example : singularProblem.dofs ≤
    (singularProblem.priorCovariance.rank : ℝ) := by
  exact singularSupportFactor.dofs_le_priorCovariance_rank observation_posDef

/-- 支持白化矩阵的特征值严格小于 `1`。 -/
example (i : Fin 1) :
    singularSupportFactor.eigenvalues observation_posDef i < 1 :=
  singularSupportFactor.eigenvalues_lt_one observation_posDef i

private def unobservableProblem : Problem 2 1 where
  jacobian := !![0, 1]
  priorMean := 0
  priorCovariance := !![1, 0; 0, 0]
  observationErrorCovariance := 1

private def unobservableSupportFactor :
    @Problem.SupportFactor 2 1 1 unobservableProblem where
  matrix := supportMatrix
  injective := singularSupportFactor.injective
  covariance_eq := by
    change (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) =
      supportMatrix * supportMatrix.conjTranspose
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [unobservableProblem, supportMatrix, Matrix.mul_apply,
        Matrix.conjTranspose, Matrix.transpose, Fin.sum_univ_succ]

private lemma unobservable_observation_posDef :
    unobservableProblem.observationErrorCovariance.PosDef :=
  Matrix.PosDef.one

private lemma unobservable_supportJacobian_eq :
    unobservableSupportFactor.supportJacobian = !![(0 : ℝ)] := by
  ext i j
  fin_cases i
  fin_cases j
  norm_num [Problem.SupportFactor.supportJacobian, unobservableSupportFactor,
    unobservableProblem, supportMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

private lemma unobservable_not_observableOnSupport :
    ¬ unobservableSupportFactor.observableOnSupport := by
  rw [Problem.SupportFactor.observableOnSupport, unobservable_supportJacobian_eq]
  intro hObservable
  have hEqual :
      (!![(0 : ℝ)] : Matrix (Fin 1) (Fin 1) ℝ).mulVec (![0] : State 1) =
        (!![(0 : ℝ)] : Matrix (Fin 1) (Fin 1) ℝ).mulVec (![1] : State 1) := by
    funext i
    fin_cases i
    norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  have hStates := hObservable hEqual
  norm_num at hStates

/-- 支持内不可辨识时出现零特征值。 -/
example : (0 : ℝ) ∈ spectrum ℝ
    unobservableSupportFactor.whitenedAveragingKernel := by
  rw [unobservableSupportFactor.whitenedAveragingKernel_zero_mem_spectrum_iff_not_observableOnSupport
    unobservable_observation_posDef]
  exact unobservable_not_observableOnSupport

end
end LeanOEM.Tests.SupportWhitening
