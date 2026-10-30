module

public import LeanOEM.Core.Iteration
public import LeanOEM.Tests.ForwardModel
import Mathlib.Tactic

@[expose] public section

namespace LeanOEM.Tests.Iteration

open LeanOEM LeanOEM.NonlinearProblem Filter
open scoped Topology

noncomputable section

private def scalarProblem (f : ℝ → ℝ) (y : ℝ) : NonlinearProblem 1 1 where
  model := { observe := fun x => ![f (x 0)] }
  observation := ![y]
  priorMean := ![0]
  priorWeight := !![1]
  observationWeight := !![1]

private def linearProblem := scalarProblem (fun z => z) 4

private lemma scalar_norm (a : ℝ) : ‖(![a] : State 1)‖ = |a| := by
  have h : (![a] : State 1) = fun _ => a := by
    ext i
    fin_cases i
    rfl
  rw [h, pi_norm_const, Real.norm_eq_abs]

private lemma linear_update (x : State 1) :
    linearProblem.gaussNewtonUpdate x !![1] = ![2] := by
  unfold gaussNewtonUpdate gaussNewtonStep
  ext i
  fin_cases i
  norm_num [normalMatrix, normalRhs, NonlinearProblem.residual, linearProblem,
    scalarProblem, Matrix.mul_apply, Matrix.mulVec, Matrix.diagonal,
    Matrix.conjTranspose, Matrix.transpose, Matrix.vecHead, dotProduct,
    Fin.sum_univ_succ, Function.comp_def, Pi.smul_apply, Ring.inverse_eq_inv]
  ring

/-- 线性例子一步到达已知的正则化解，任意初值都适用。 -/
private lemma linear_contracts (initial : State 1) :
    linearProblem.ContractsTowardAlong (fun _ _ => !![1]) initial ![2] 0 := by
  apply linearProblem.contractsTowardAlong_of_lipschitzOn
    (fun _ _ => !![1]) initial ![2] (domain := Set.univ) 0 (by trivial) (by trivial)
  · intro i x hx
    trivial
  · intro i
    exact linear_update _
  · intro i
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simp [linear_update]

example (initial : State 1) :
    Tendsto (linearProblem.gaussNewtonIterate (fun _ _ => !![1]) initial) atTop (𝓝 ![2]) :=
  linearProblem.gaussNewtonIterate_tendsto _ initial ![2] (by norm_num)
    (by norm_num) (linear_contracts initial)

/-- 在初始状态停止时，误差界使用当前状态；这里容差为 1/2，q 为 1/2。 -/
example :
    ‖linearProblem.gaussNewtonIterate (fun _ _ => !![1]) ![(5 / 2 : ℝ)] 0 - ![2]‖ ≤
      (1 / 2 : ℝ) / (1 - (1 / 2 : ℝ)) := by
  have hContract : linearProblem.ContractsTowardAlong (fun _ _ => !![1])
      ![(5 / 2 : ℝ)] ![2] (1 / 2 : ℝ) := by
    intro i
    simp only [gaussNewtonIterate_succ, linear_update, sub_self, norm_zero]
    positivity
  have hStep : linearProblem.gaussNewtonStep ![(5 / 2 : ℝ)] !![1] =
      ![(-1 / 2 : ℝ)] := by
    unfold gaussNewtonStep
    ext i
    fin_cases i
    norm_num [normalMatrix, normalRhs, NonlinearProblem.residual, linearProblem,
      scalarProblem, Matrix.mul_apply, Matrix.mulVec, Matrix.diagonal,
      Matrix.conjTranspose, Matrix.transpose, Matrix.vecHead, dotProduct,
      Fin.sum_univ_succ, Function.comp_def, Pi.smul_apply, Ring.inverse_eq_inv]
  apply linearProblem.stoppedAt_error_le _ _ ![2] (by norm_num) hContract 0
  change 0 ≤ (1 / 2 : ℝ) ∧ ‖linearProblem.gaussNewtonStep ![(5 / 2 : ℝ)] !![1]‖ ≤ 1 / 2
  rw [hStep, scalar_norm]
  norm_num

/-- 零容差在精确到达解的线性例子上可以满足。 -/
example (initial : State 1) :
    linearProblem.StoppedAt (fun _ _ => !![1]) initial 0 1 := by
  have hStep : linearProblem.gaussNewtonStep ![2] !![1] = 0 := by
    have h := linear_update (![2] : State 1)
    simpa only [gaussNewtonUpdate, add_eq_left] using h
  simpa [StoppedAt, StepSmall, gaussNewtonIterate_succ, linear_update] using
    (show 0 ≤ (0 : ℝ) ∧ ‖linearProblem.gaussNewtonStep ![2] !![1]‖ ≤ 0 by
      simp [hStep])

/-- 停止判据包含非负容差要求。 -/
example : ¬ linearProblem.StepSmall ![2] !![1] (-1) := by
  simp [StepSmall]

private def squareProblem := scalarProblem (fun z => z ^ 2) 4
private def refreshed : ℕ → State 1 → Jacobian 1 1 := fun _ x => !![2 * x 0]
private def frozen : ℕ → State 1 → Jacobian 1 1 := fun _ _ => !![2]

/-- 刷新 Jacobian：从 1 出发，经 2 后到达 32/17。 -/
example : squareProblem.gaussNewtonIterate refreshed ![1] 2 = ![(32 / 17 : ℝ)] := by
  ext i
  fin_cases i
  norm_num [gaussNewtonIterate, gaussNewtonUpdate, gaussNewtonStep, normalMatrix,
    normalRhs, NonlinearProblem.residual, refreshed, squareProblem, scalarProblem,
    Matrix.mul_apply, Matrix.mulVec, Matrix.diagonal, Matrix.conjTranspose,
    Matrix.transpose, Matrix.vecHead, dotProduct, Fin.sum_univ_succ,
    Function.comp_def, Pi.smul_apply, Ring.inverse_eq_inv]

/-- 冻结初始 Jacobian 时第二步变为 8/5，明确两种策略的不同。 -/
example : squareProblem.gaussNewtonIterate frozen ![1] 2 = ![(8 / 5 : ℝ)] := by
  ext i
  fin_cases i
  norm_num [gaussNewtonIterate, gaussNewtonUpdate, gaussNewtonStep, normalMatrix,
    normalRhs, NonlinearProblem.residual, frozen, squareProblem, scalarProblem,
    Matrix.mul_apply, Matrix.mulVec, Matrix.diagonal, Matrix.conjTranspose,
    Matrix.transpose, Matrix.vecHead, dotProduct, Fin.sum_univ_succ,
    Function.comp_def, Pi.smul_apply, Ring.inverse_eq_inv]

/-- 反例使用的零 Jacobian 确实是模型在零点的导数。 -/
example : squareProblem.model.HasJacobianAt (0 : State 1) (!![0] : Jacobian 1 1) := by
  simpa [squareProblem, scalarProblem,
    LeanOEM.Tests.ForwardModel.squareForward, LeanOEM.Tests.ForwardModel.squareJacobian]
    using LeanOEM.Tests.ForwardModel.square_hasJacobianAt (0 : State 1)

private lemma square_update_zero :
    squareProblem.gaussNewtonUpdate (0 : State 1) !![0] = 0 := by
  unfold gaussNewtonUpdate gaussNewtonStep
  ext i
  fin_cases i
  norm_num [normalMatrix, normalRhs, NonlinearProblem.residual, squareProblem,
    scalarProblem, Matrix.mul_apply, Matrix.mulVec, Matrix.diagonal,
    Matrix.conjTranspose, Matrix.transpose, Matrix.vecHead, dotProduct,
    Fin.sum_univ_succ, Function.comp_def, Pi.smul_apply, Ring.inverse_eq_inv]

/-- 初值为零时真实导数刷新也一直停在零点。 -/
private lemma square_iterate_zero (i : ℕ) :
    squareProblem.gaussNewtonIterate refreshed 0 i = 0 := by
  induction i with
  | zero => rfl
  | succ i ih => simpa [gaussNewtonIterate_succ, ih, refreshed] using square_update_zero

/-- 停滞反例的正规矩阵仍可逆。 -/
example : IsUnit (squareProblem.normalMatrix (0 : State 1) (0 : Jacobian 1 1)) := by
  simp [normalMatrix, squareProblem, scalarProblem, Matrix.isUnit_iff_isUnit_det]

/-- 零步长可通过零容差检查。 -/
example : squareProblem.StepSmall (0 : State 1) !![0] 0 := by
  have hStep : squareProblem.gaussNewtonStep (0 : State 1) !![0] = 0 := by
    simpa [gaussNewtonUpdate] using square_update_zero
  simp [StepSmall, hStep]

/-- q=1 只给出不增条件：停滞轨迹相对目标 2 满足它，却一直保持距离 2。 -/
example : squareProblem.ContractsTowardAlong refreshed 0 ![2] 1 ∧
    ∀ i, ‖squareProblem.gaussNewtonIterate refreshed 0 i - ![2]‖ = 2 := by
  constructor
  · intro i
    simp only [square_iterate_zero, one_mul, le_refl]
  · intro i
    rw [square_iterate_zero]
    simpa using scalar_norm (-2)

/-- 零点的目标为 8，而状态 2 的目标为 2：停止并不推出最优。 -/
example : squareProblem.objective (0 : State 1) > squareProblem.objective ![2] := by
  norm_num [objective, quadraticForm, NonlinearProblem.residual, squareProblem, scalarProblem,
    Matrix.mulVec, dotProduct]

/-- 空状态空间允许定义轨迹；条件中的范数仍是合法范数。 -/
example (p : NonlinearProblem 0 0) (jacobian : ℕ → State 0 → Jacobian 0 0) (i : ℕ) :
    p.gaussNewtonIterate jacobian 0 i = 0 := Subsingleton.elim _ _

end
end LeanOEM.Tests.Iteration
