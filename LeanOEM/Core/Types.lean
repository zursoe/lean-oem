module

public import Mathlib.LinearAlgebra.Matrix.PosDef

@[expose] public section

namespace LeanOEM

/-- `n` 维状态向量，坐标索引使用 `Fin n`。 -/
abbrev State (n : ℕ) := Fin n → ℝ

/-- `m` 维观测向量，坐标索引使用 `Fin m`。 -/
abbrev Observation (m : ℕ) := Fin m → ℝ

/-- 从 `n` 维状态到 `m` 维观测的线性 Jacobian。 -/
abbrev Jacobian (n m : ℕ) := Matrix (Fin m) (Fin n) ℝ

/-- `n × n` 实矩阵。 -/
abbrev Square (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- 协方差在核心 API 中先表示为矩阵；正定性由定理假设显式给出。 -/
abbrev Covariance (n : ℕ) := Square n

end LeanOEM
