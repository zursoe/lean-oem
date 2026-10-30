module

public import LeanOEM.Core.Estimator
public import Mathlib.LinearAlgebra.Matrix.Trace

@[expose] public section

namespace LeanOEM

noncomputable section

/-- 给定增益和 Jacobian 的 degrees of freedom，是 averaging kernel 的矩阵迹。 -/
def dofs {n m : ℕ}
    (g : Matrix (Fin n) (Fin m) ℝ) (k : Jacobian n m) : ℝ :=
  Matrix.trace (averagingKernel g k)

/-- 问题使用其最优增益时的 degrees of freedom。 -/
def Problem.dofs {n m : ℕ} (p : Problem n m) : ℝ :=
  LeanOEM.dofs p.gain p.jacobian

/-- 零增益的 degrees of freedom 为零。 -/
@[simp] theorem dofs_zero_left {n m : ℕ} (k : Jacobian n m) :
    dofs (0 : Matrix (Fin n) (Fin m) ℝ) k = 0 := by
  simp [dofs, averagingKernel]

/-- degrees of freedom 对增益的加法性。 -/
theorem dofs_add_left {n m : ℕ}
    (g₁ g₂ : Matrix (Fin n) (Fin m) ℝ) (k : Jacobian n m) :
    dofs (g₁ + g₂) k = dofs g₁ k + dofs g₂ k := by
  unfold dofs averagingKernel
  rw [Matrix.add_mul, Matrix.trace_add]

/-- degrees of freedom 的定义就是 averaging kernel 的 trace。 -/
theorem dofs_eq_trace_averagingKernel {n m : ℕ}
    (g : Matrix (Fin n) (Fin m) ℝ) (k : Jacobian n m) :
    dofs g k = Matrix.trace (averagingKernel g k) := rfl

end
end LeanOEM
