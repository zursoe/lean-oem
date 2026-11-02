module

public import LeanOEM.Core.PriorWhitening
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-!
# 先验白化的合成例子

相关先验 `Sₐ = [[2,1],[1,1]]` 和秩亏观测 `K = [1,0]` 给出不对称的
原 averaging kernel。显式三角因子把它转换为对称矩阵；两者的谱均为 `{0, 2/3}`。
另检查零 Jacobian 与空状态，防止引入满秩或正维数的隐含假设。
-/

@[expose] public section

namespace LeanOEM.Tests.PriorWhitening

open LeanOEM Matrix

noncomputable section

private def correlatedProblem : Problem 2 1 where
  jacobian := !![1, 0]
  priorMean := 0
  priorCovariance := !![2, 1; 1, 1]
  observationErrorCovariance := 1

private def triangularFactor : correlatedProblem.PriorFactor where
  matrix := !![1, 1; 0, 1]
  isUnit := by norm_num [Matrix.isUnit_iff_isUnit_det, Matrix.det_fin_two]
  covariance_eq := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [correlatedProblem, Matrix.mul_apply, Matrix.conjTranspose,
        Fin.sum_univ_succ]

private lemma observation_posDef : correlatedProblem.observationErrorCovariance.PosDef :=
  Matrix.PosDef.one

private lemma innovation_eq : correlatedProblem.innovationCovariance =
    Matrix.diagonal ![(3 : ℝ)] := by
  ext i j
  fin_cases i
  fin_cases j
  norm_num [Problem.innovationCovariance, correlatedProblem, Matrix.mul_apply,
    Matrix.conjTranspose, Fin.sum_univ_succ, Matrix.diagonal, Matrix.vecMul, dotProduct]

private lemma gain_eq : correlatedProblem.gain = !![(2 / 3 : ℝ); 1 / 3] := by
  unfold Problem.gain
  rw [innovation_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [correlatedProblem, Matrix.inv_diagonal, Matrix.mul_apply,
      Matrix.conjTranspose, Fin.sum_univ_succ, Matrix.diagonal, Ring.inverse_eq_inv,
      Matrix.vecMul, dotProduct]

private lemma averaging_eq : averagingKernel correlatedProblem.gain
    correlatedProblem.jacobian = !![(2 / 3 : ℝ), 0; 1 / 3, 0] := by
  rw [averagingKernel, gain_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [correlatedProblem, Matrix.mul_apply, Fin.sum_univ_succ]

/-- 合法的最优增益仍可能给出不对称的原 averaging kernel。 -/
example : ¬ (averagingKernel correlatedProblem.gain
    correlatedProblem.jacobian).IsHermitian := by
  rw [averaging_eq]
  intro h
  have h01 := congrFun (congrFun h.eq (0 : Fin 2)) (1 : Fin 2)
  norm_num [Matrix.conjTranspose] at h01

/-- 白化后的矩阵是对称的，并保留秩亏方向。 -/
example : triangularFactor.whitenedAveragingKernel =
    !![(1 / 3 : ℝ), 1 / 3; 1 / 3, 1 / 3] := by
  unfold Problem.PriorFactor.whitenedAveragingKernel
  rw [innovation_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [triangularFactor, correlatedProblem, Matrix.inv_diagonal,
      Matrix.mul_apply, Matrix.conjTranspose, Fin.sum_univ_succ,
      Matrix.diagonal, Ring.inverse_eq_inv]

private lemma charpoly_eq :
    (averagingKernel correlatedProblem.gain correlatedProblem.jacobian).charpoly =
      Polynomial.X * (Polynomial.X - Polynomial.C (2 / 3 : ℝ)) := by
  rw [averaging_eq, Matrix.charpoly_fin_two]
  norm_num [Matrix.trace, Matrix.det_fin_two, Fin.sum_univ_succ]
  ring

/-- 原不对称矩阵的完整实谱为零和 `2/3`，而不是由对称性假设强行得到。 -/
example (r : ℝ) :
    r ∈ spectrum ℝ (averagingKernel correlatedProblem.gain correlatedProblem.jacobian) ↔
      r = 0 ∨ r = 2 / 3 := by
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, charpoly_eq]
  simp [Polynomial.IsRoot, mul_eq_zero, sub_eq_zero]

/-- 仅使用正定先验和观测误差的公开入口，不需要额外输入三角因子。 -/
example : spectrum ℝ (averagingKernel correlatedProblem.gain correlatedProblem.jacobian)
    ⊆ Set.Icc (0 : ℝ) 1 :=
  correlatedProblem.averagingKernel_spectrum_subset_Icc
    triangularFactor.prior_posDef observation_posDef

/-- DOFS 是两个白化特征值之和，精确等于 `2/3`。 -/
example : (∑ i, triangularFactor.eigenvalues observation_posDef i) = (2 / 3 : ℝ) := by
  rw [← triangularFactor.dofs_eq_sum_eigenvalues observation_posDef]
  unfold Problem.dofs LeanOEM.dofs
  rw [averaging_eq]
  norm_num [Matrix.trace, Fin.sum_univ_succ]

/-- 零 Jacobian 在任何可逆先验因子下都给出零白化矩阵。 -/
example {n m : ℕ} (p : Problem n m) (f : p.PriorFactor) (hK : p.jacobian = 0) :
    f.whitenedAveragingKernel = 0 := by
  simp [Problem.PriorFactor.whitenedAveragingKernel, hK]

/-- 空状态空间也允许平方根因子和谱界，不要求 `n > 0`。 -/
example (p : Problem 0 0) (hPrior : p.priorCovariance.PosDef)
    (hObservation : p.observationErrorCovariance.PosDef) :
    spectrum ℝ (averagingKernel p.gain p.jacobian) = ∅ := by
  rw [(Problem.PriorFactor.ofPosDef hPrior).spectrum_eq_range_eigenvalues hObservation]
  simp

end
end LeanOEM.Tests.PriorWhitening
