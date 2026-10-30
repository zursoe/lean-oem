module

public import LeanOEM.Core.Types

@[expose] public section

namespace LeanOEM

/-- 有限维、实数、线性观测的最小 OEM 问题规格。

`jacobian` 的行对应观测坐标，列对应状态坐标。当前结构只记录矩阵，
并不把正定性或现实物理来源伪装成结构内建事实。 -/
structure Problem (n m : ℕ) where
  jacobian : Jacobian n m
  priorMean : State n
  priorCovariance : Covariance n
  observationErrorCovariance : Covariance m

/-- 线性观测模型对状态的预测。 -/
def Problem.predict {n m : ℕ} (p : Problem n m) (x : State n) : Observation m :=
  p.jacobian.mulVec x

/-- 给定状态和观测的线性创新（观测减去预测）。 -/
def Problem.innovation {n m : ℕ}
    (p : Problem n m) (x : State n) (y : Observation m) : Observation m :=
  y - p.predict x

/-- 由先验协方差和观测误差协方差得到的创新协方差。

实数情形下 `conjTranspose` 与转置一致；使用 `conjTranspose` 可以直接复用
Mathlib 关于正半定矩阵和合同变换的定理。 -/
def Problem.innovationCovariance {n m : ℕ} (p : Problem n m) : Covariance m :=
  p.jacobian * p.priorCovariance * p.jacobian.conjTranspose
    + p.observationErrorCovariance

end LeanOEM
