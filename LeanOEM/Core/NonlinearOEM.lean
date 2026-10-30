module

public import LeanOEM.Core.ForwardModel
public import LeanOEM.Core.Information
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

namespace LeanOEM

noncomputable section

/-- 非线性 OEM 的观测、先验和权重规格。

`observationWeight` 与 `priorWeight` 表示误差协方差的逆或其他显式权重；
本结构不自动声称它们来自正定协方差。
-/
structure NonlinearProblem (n m : ℕ) where
  model : ForwardModel n m
  observation : Observation m
  priorMean : State n
  priorWeight : Square n
  observationWeight : Square m

namespace NonlinearProblem

/-- 非线性观测残差。 -/
def residual (p : NonlinearProblem n m) (x : State n) : Observation m :=
  p.observation - p.model.observe x

/-- 矩阵权重下的二次型。 -/
def quadraticForm {n : ℕ} (weight : Square n) (v : State n) : ℝ :=
  dotProduct v (weight.mulVec v)

/-- 带先验约束的非线性 MAP 目标函数。 -/
def objective (p : NonlinearProblem n m) (x : State n) : ℝ :=
  (1 / 2 : ℝ) * quadraticForm p.observationWeight (p.residual x)
    + (1 / 2 : ℝ) * quadraticForm p.priorWeight (x - p.priorMean)

/-- 当前状态和 Jacobian 下的 Gauss–Newton 正规矩阵。 -/
def normalMatrix (p : NonlinearProblem n m) (_x : State n)
    (k : Jacobian n m) : Square n :=
  k.conjTranspose * p.observationWeight * k + p.priorWeight

/-- 当前状态和 Jacobian 下的 Gauss–Newton 右端项。 -/
def normalRhs (p : NonlinearProblem n m) (x : State n)
    (k : Jacobian n m) : State n :=
  k.conjTranspose.mulVec (p.observationWeight.mulVec (p.residual x))
    - p.priorWeight.mulVec (x - p.priorMean)

/-- 可逆正规矩阵条件下的 Gauss–Newton 状态增量。 -/
def gaussNewtonStep (p : NonlinearProblem n m) (x : State n)
    (k : Jacobian n m) : State n :=
  (p.normalMatrix x k)⁻¹.mulVec (p.normalRhs x k)

/-- 使用全步长增量的 Gauss–Newton 更新。 -/
def gaussNewtonUpdate (p : NonlinearProblem n m) (x : State n)
    (k : Jacobian n m) : State n :=
  x + p.gaussNewtonStep x k

theorem normalMatrix_mulVec_gaussNewtonStep
    (p : NonlinearProblem n m) (x : State n) (k : Jacobian n m)
    (hNormal : IsUnit (p.normalMatrix x k)) :
    (p.normalMatrix x k).mulVec (p.gaussNewtonStep x k) = p.normalRhs x k := by
  unfold gaussNewtonStep
  rw [Matrix.mulVec_mulVec]
  rw [Matrix.mul_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).mp hNormal), Matrix.one_mulVec]

end NonlinearProblem

/-- 将线性 `Problem` 视为一个非线性规格的特例。 -/
def Problem.toNonlinear {n m : ℕ} (p : Problem n m) (y : Observation m) :
    NonlinearProblem n m :=
  { model := { observe := p.predict }
    observation := y
    priorMean := p.priorMean
    priorWeight := p.priorCovariance⁻¹
    observationWeight := p.observationErrorCovariance⁻¹ }

@[simp] theorem Problem.toNonlinear_residual_eq_innovation
    {n m : ℕ} (p : Problem n m) (y : Observation m) (x : State n) :
    (p.toNonlinear y).residual x = p.innovation x y := rfl

theorem Problem.toNonlinear_normalMatrix_eq_informationMatrix
    {n m : ℕ} (p : Problem n m) (y : Observation m) (x : State n) :
    (p.toNonlinear y).normalMatrix x p.jacobian = informationMatrix p := by
  simp [NonlinearProblem.normalMatrix, Problem.toNonlinear, informationMatrix, add_comm]

end
end LeanOEM
