module

public import LeanOEM.Core.LinearModel
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

namespace LeanOEM

noncomputable section

/-- 给定问题和创新协方差逆的总函数形式，定义最优估计增益。

矩阵逆在 Mathlib 中是总函数；实际使用时需要由 `PosDef` 假设保证可逆性。 -/
def Problem.gain {n m : ℕ} (p : Problem n m) : Matrix (Fin n) (Fin m) ℝ :=
  p.priorCovariance * p.jacobian.conjTranspose * p.innovationCovariance⁻¹

/-- 给定任意增益的线性估计器。 -/
def estimateWithGain {n m : ℕ}
    (p : Problem n m) (g : Matrix (Fin n) (Fin m) ℝ) (y : Observation m) : State n :=
  p.priorMean + g.mulVec (p.innovation p.priorMean y)

/-- 使用问题定义的增益进行估计。 -/
def estimate {n m : ℕ} (p : Problem n m) (y : Observation m) : State n :=
  estimateWithGain p p.gain y

/-- 给定增益对应的 averaging kernel。 -/
def averagingKernel {n m : ℕ}
    (g : Matrix (Fin n) (Fin m) ℝ) (k : Jacobian n m) : Square n :=
  g * k

/-- 估计误差，供误差分解定理使用。 -/
def retrievalError {n m : ℕ}
    (p : Problem n m) (g : Matrix (Fin n) (Fin m) ℝ)
    (x : State n) (y : Observation m) : State n :=
  estimateWithGain p g y - x

end
end LeanOEM
