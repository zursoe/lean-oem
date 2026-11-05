module

public import LeanOEM.Core.SupportCoordinates
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-!
# canonical 支持坐标的合成例子

使用 `Sₐ = diag(1, 0)` 检查：canonical support 的维数为一，坐标列矩阵满列秩，且其
线性映射像正好是平方根因子的 support。由于 `stdOrthonormalBasis` 是规范化选择，
测试只检查这些不依赖具体基向量符号的契约。
-/

@[expose] public section

namespace LeanOEM.Tests.SupportCoordinates

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

private def canonicalSqrt :
    @Problem.PriorSqrtFactor 2 1 singularProblem :=
  Problem.PriorSqrtFactor.ofPosSemidef singularSupportFactor.prior_posSemidef

example : Module.finrank ℝ canonicalSqrt.support = 1 := by
  calc
    Module.finrank ℝ canonicalSqrt.support = singularProblem.priorCovariance.rank :=
      canonicalSqrt.support_finrank_eq_priorCovariance_rank
    _ = 1 := singularSupportFactor.priorCovariance_rank_eq_support_dim

example : Function.Injective canonicalSqrt.supportBasisMatrix.mulVec :=
  canonicalSqrt.supportBasisMatrix_injective

example : LinearMap.range canonicalSqrt.supportBasisMatrix.mulVecLin = canonicalSqrt.support :=
  canonicalSqrt.supportBasisMatrix_range_eq_support

example : canonicalSqrt.supportBasisMatrix.rank = 1 := by
  calc
    canonicalSqrt.supportBasisMatrix.rank = Module.finrank ℝ canonicalSqrt.support :=
      canonicalSqrt.supportBasisMatrix_rank_eq_support_finrank
    _ = 1 := by
      exact canonicalSqrt.support_finrank_eq_priorCovariance_rank.trans
        singularSupportFactor.priorCovariance_rank_eq_support_dim

example : Module.finrank ℝ canonicalSqrt.euclideanSupport =
    Module.finrank ℝ canonicalSqrt.support :=
  canonicalSqrt.euclideanSupport_finrank_eq_support

example : Orthonormal ℝ canonicalSqrt.euclideanSupportBasis :=
  canonicalSqrt.euclideanSupportBasis.orthonormal

end
end LeanOEM.Tests.SupportCoordinates
