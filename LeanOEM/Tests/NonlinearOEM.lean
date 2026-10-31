module

public import LeanOEM.Core.NonlinearOEM
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic

@[expose] public section

namespace LeanOEM.Tests.NonlinearOEM

open LeanOEM
open LeanOEM.NonlinearProblem

noncomputable section

private def squareModel : ForwardModel 1 1 where
  observe := fun x => ![(x 0) ^ 2]

private def squareProblem : NonlinearProblem 1 1 where
  model := squareModel
  observation := ![4]
  priorMean := ![0]
  priorWeight := !![1]
  observationWeight := !![1]

private def squareJacobian : Jacobian 1 1 := !![2]

/-- 标量例子中的正规矩阵和右端项。 -/
private lemma squareProblem_normalMatrix_eq :
    squareProblem.normalMatrix (![1] : State 1) squareJacobian = !![5] := by
  ext i j
  fin_cases i
  fin_cases j
  norm_num [NonlinearProblem.normalMatrix, squareProblem, squareJacobian,
    Matrix.mul_apply, Matrix.vecMul, Matrix.vecHead, dotProduct,
    Matrix.conjTranspose]

example : squareProblem.normalRhs (![1] : State 1) squareJacobian = (![5] : State 1) := by
  funext i
  fin_cases i
  norm_num [NonlinearProblem.normalRhs, NonlinearProblem.residual, squareProblem,
    squareModel, squareJacobian, Problem.predict, Matrix.mulVec, Matrix.vecHead,
    dotProduct, Fin.sum_univ_succ]

/-- 正规矩阵可逆时，Gauss–Newton 步满足正规方程。 -/
example :
    (squareProblem.normalMatrix (![1] : State 1) squareJacobian).mulVec
        (squareProblem.gaussNewtonStep (![1] : State 1) squareJacobian) =
      squareProblem.normalRhs (![1] : State 1) squareJacobian := by
  apply normalMatrix_mulVec_gaussNewtonStep
  rw [squareProblem_normalMatrix_eq]
  norm_num [Matrix.isUnit_iff_isUnit_det]

/-- 正规矩阵可逆时，Gauss–Newton 更新是线性化正规梯度的零点。 -/
example :
    squareProblem.linearizedGradient (![1] : State 1) squareJacobian
      (squareProblem.gaussNewtonUpdate (![1] : State 1) squareJacobian) = 0 := by
  apply gaussNewtonUpdate_linearizedGradient_eq_zero
  rw [squareProblem_normalMatrix_eq]
  norm_num [Matrix.isUnit_iff_isUnit_det]

/-- 正定权重和可观测 Jacobian 给出正定正规矩阵。 -/
example (p : NonlinearProblem 1 1) (x : State 1) (k : Jacobian 1 1)
    (hWeights : WeightWellPosed p) (hObservable : Observable k) :
    (p.normalMatrix x k).PosDef :=
  normalMatrix_posDef p x k hWeights hObservable

/-- 线性问题在非线性规格中的残差仍是原 OEM 创新。 -/
example (p : Problem 1 1) (y : Observation 1) (x : State 1) :
    (p.toNonlinear y).residual x = p.innovation x y :=
  Problem.toNonlinear_residual_eq_innovation p y x

/-- 线性问题的 Gauss–Newton 正规矩阵退化为信息矩阵。 -/
example (p : Problem 1 1) (y : Observation 1) (x : State 1) :
    (p.toNonlinear y).normalMatrix x p.jacobian = informationMatrix p :=
  Problem.toNonlinear_normalMatrix_eq_informationMatrix p y x

end
end LeanOEM.Tests.NonlinearOEM
