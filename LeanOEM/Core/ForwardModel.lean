module

public import LeanOEM.Core.LinearModel
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Matrix.ToLin

@[expose] public section

namespace LeanOEM

noncomputable section

/--
与 ARTS 无关的非线性观测模型。

`observe` 将有限维状态映射到有限维观测。该结构不包含辐射传输实现、单位、
数据文件或数值方法；这些内容属于此契约之上的独立层。
-/
structure ForwardModel (n m : ℕ) where
  observe : State n → Observation m

namespace ForwardModel

instance : CoeFun (ForwardModel n m) (fun _ => State n → Observation m) :=
  ⟨ForwardModel.observe⟩

/-- 用矩阵 `k` 在 `xa` 处线性化 `f` 得到的仿射模型。 -/
def linearizedObserve (f : ForwardModel n m) (xa x : State n)
    (k : Jacobian n m) : Observation m :=
  f.observe xa + k.mulVec (x - xa)

/-- 锚点线性化留下的余项。 -/
def linearizationRemainder (f : ForwardModel n m) (xa x : State n)
    (k : Jacobian n m) : Observation m :=
  f.observe x - f.observe xa - k.mulVec (x - xa)

/--
局部二次余项契约。`k` 可以是 `f` 在 `xa` 处的精确 Jacobian，也可以是
调用者另外验证过的近似 Jacobian；本定义只记录余项界，不把导数性质隐含进去。
-/
def QuadraticRemainderBound (f : ForwardModel n m) (xa x : State n)
    (k : Jacobian n m) (rho : ℝ) : Prop :=
  ‖f.linearizationRemainder xa x k‖ ≤ rho * ‖x - xa‖ ^ 2

/-- 使锚点线性化可以使用 `Problem.predict` 的仿射偏置。 -/
def linearizedOffset (f : ForwardModel n m) (xa : State n)
    (k : Jacobian n m) : Observation m :=
  f.observe xa - k.mulVec xa

@[simp] theorem observe_eq_linearized_add_remainder (f : ForwardModel n m)
    (xa x : State n) (k : Jacobian n m) :
    f.observe x = f.linearizedObserve xa x k + f.linearizationRemainder xa x k := by
  simp [linearizedObserve, linearizationRemainder]

theorem linearizedObserve_eq_offset_add (f : ForwardModel n m) (xa x : State n)
    (k : Jacobian n m) :
    f.linearizedObserve xa x k = f.linearizedOffset xa k + k.mulVec x := by
  simp [linearizedObserve, linearizedOffset]
  rw [Matrix.mulVec_sub]
  abel

theorem linearizedObserve_eq_problem_predict_add_offset (f : ForwardModel n m)
    (xa x : State n) (k : Jacobian n m) (p : Problem n m)
    (hJacobian : p.jacobian = k) :
    f.linearizedObserve xa x k = f.linearizedOffset xa k + p.predict x := by
  rw [f.linearizedObserve_eq_offset_add]
  simp [Problem.predict, hJacobian]

/--
当 `k` 表示 Fréchet 导数时，称 `k` 是 `f` 在 `x` 处的 Jacobian 矩阵。

导数保留为连续线性映射，以便调用者使用 Mathlib 的微积分接口；矩阵等式
固定 OEM 中“行是观测、列是状态”的约定。
-/
def HasJacobianAt (f : ForwardModel n m) (x : State n)
    (k : Jacobian n m) : Prop :=
  ∃ derivative : State n →L[ℝ] Observation m,
    HasFDerivAt f.observe derivative x ∧
      ∀ h, derivative h = k.mulVec h

/-- 打包保存导数及其矩阵表示。 -/
structure JacobianSpec (f : ForwardModel n m) (x : State n) where
  matrix : Jacobian n m
  derivative : State n →L[ℝ] Observation m
  hasFDeriv : HasFDerivAt f.observe derivative x
  matrix_apply : ∀ h, derivative h = matrix.mulVec h

theorem JacobianSpec.hasJacobianAt (spec : JacobianSpec f x) :
    HasJacobianAt f x spec.matrix :=
  ⟨spec.derivative, spec.hasFDeriv, spec.matrix_apply⟩

/-- 在有限函数基下由矩阵表示的连续线性映射。 -/
noncomputable def matrixDerivative (k : Jacobian n m) : State n →L[ℝ] Observation m :=
  (Matrix.toLin' k).toContinuousLinearMap

@[simp] theorem matrixDerivative_apply (k : Jacobian n m) (h : State n) :
    matrixDerivative k h = k.mulVec h := by
  change Matrix.toLin' k h = k.mulVec h
  exact Matrix.toLin'_apply k h

theorem hasJacobianAt_of_hasFDerivAt_matrix (f : ForwardModel n m)
    (x : State n) (k : Jacobian n m)
    (h : HasFDerivAt f.observe (matrixDerivative k) x) :
    HasJacobianAt f x k := by
  exact ⟨matrixDerivative k, h, matrixDerivative_apply k⟩

end ForwardModel

end
end LeanOEM
