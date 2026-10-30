module

public import LeanOEM.Core.ForwardModel
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Tactic

@[expose] public section

namespace LeanOEM.Tests.ForwardModel

open LeanOEM

noncomputable section

/-- 用于检查 Jacobian 契约的标量非线性观测模型。 -/
def squareForward : ForwardModel 1 1 where
  observe := fun x => ![(x 0) ^ 2]

/-- 按核心 API 矩阵约定表示的标量平方模型导数。 -/
def squareJacobian (x : State 1) : Jacobian 1 1 := !![2 * x 0]

lemma square_hasJacobianAt (x : State 1) :
    ForwardModel.HasJacobianAt squareForward x (squareJacobian x) := by
  let derivative : State 1 →L[ℝ] Observation 1 :=
    ContinuousLinearMap.pi (fun _ =>
      (ContinuousLinearMap.toSpanSingleton ℝ (2 * x 0)).comp
        (ContinuousLinearMap.proj (0 : Fin 1)))
  refine ⟨derivative, ?_, ?_⟩
  · rw [hasFDerivAt_pi]
    intro i
    fin_cases i
    have hs : HasDerivAt (fun z : ℝ => z ^ 2) (2 * x 0) (x 0) := by
      convert (hasDerivAt_id (𝕜 := ℝ) (x 0)).pow 2 using 1
      · funext z
        simp [id]
      · simp [id]
    have hs' : HasFDerivAt (fun z : ℝ => z ^ 2)
        (ContinuousLinearMap.toSpanSingleton ℝ (2 * x 0)) (x 0) :=
      hs.hasFDerivAt
    have hx : HasFDerivAt (fun y : State 1 => y 0)
        (ContinuousLinearMap.proj (0 : Fin 1)) x :=
      hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 1) x
    have hcomp := hs'.comp x hx
    simpa [squareForward, derivative, Function.comp_def] using hcomp
  · intro h
    funext i
    fin_cases i
    simp [derivative, squareJacobian, Matrix.mulVec, dotProduct]
    ring

/-- 该非线性模型的锚点余项是非零二阶项。 -/
example (xa x : State 1) :
    squareForward.linearizationRemainder xa x (squareJacobian xa) =
      ![((x 0) - xa 0) ^ 2] := by
  funext i
  fin_cases i
  simp [ForwardModel.linearizationRemainder, squareForward, squareJacobian,
    dotProduct]
  ring

/-- 线性化模型可以由现有的 `Problem.predict` 表示。 -/
example (xa x : State 1) (p : Problem 1 1)
    (hJacobian : p.jacobian = squareJacobian xa) :
    squareForward.linearizedObserve xa x (squareJacobian xa) =
      squareForward.linearizedOffset xa (squareJacobian xa) + p.predict x := by
  exact ForwardModel.linearizedObserve_eq_problem_predict_add_offset
    squareForward xa x (squareJacobian xa) p hJacobian

end
end LeanOEM.Tests.ForwardModel
