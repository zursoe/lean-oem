module

public import LeanOEM
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic

@[expose] public section

namespace LeanOEM.Tests.Examples

open Matrix
open LeanOEM

noncomputable section

/-- 一维对角矩阵的半正定性证明，仅供精确例子使用。 -/
private lemma diag1_posSemidef (a : ℝ) (ha : 0 ≤ a) :
    (Matrix.diagonal ![a] : Matrix (Fin 1) (Fin 1) ℝ).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · change (Matrix.diagonal ![a]).conjTranspose = Matrix.diagonal ![a]
    rw [Matrix.diagonal_conjTranspose]
    congr 1
  · intro x
    simp [Matrix.mulVec, dotProduct, Matrix.diagonal]
    calc
      0 ≤ a * (x 0) ^ 2 := mul_nonneg ha (sq_nonneg _)
      _ = x 0 * (a * x 0) := by ring

/-- 一维对角矩阵的正定性证明，仅供精确例子使用。 -/
private lemma diag1_posDef (a : ℝ) (ha : 0 < a) :
    (Matrix.diagonal ![a] : Matrix (Fin 1) (Fin 1) ℝ).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  constructor
  · change (Matrix.diagonal ![a]).conjTranspose = Matrix.diagonal ![a]
    rw [Matrix.diagonal_conjTranspose]
    congr 1
  · intro x hx
    have hx0 : x 0 ≠ 0 := by
      intro h
      apply hx
      funext i
      fin_cases i
      exact h
    simp [Matrix.mulVec, dotProduct, Matrix.diagonal]
    nlinarith [sq_pos_of_ne_zero hx0]

/-- 二维对角矩阵的半正定性证明，仅供秩亏例子使用。 -/
private lemma diag2_posSemidef (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (Matrix.diagonal ![a, b] : Matrix (Fin 2) (Fin 2) ℝ).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · change (Matrix.diagonal ![a, b]).conjTranspose = Matrix.diagonal ![a, b]
    rw [Matrix.diagonal_conjTranspose]
    congr 1
  · intro x
    simp [Matrix.mulVec, dotProduct, Matrix.diagonal]
    calc
      0 ≤ a * (x 0) ^ 2 + b * (x 1) ^ 2 := add_nonneg
        (mul_nonneg ha (sq_nonneg _)) (mul_nonneg hb (sq_nonneg _))
      _ = x 0 * (a * x 0) + x 1 * (b * x 1) := by ring

/-- 一维精确 OEM 例子：`K = 2`、`Sₐ = 3`、`Sᵋ = 5`。 -/
private def scalarProblem : Problem 1 1 :=
  { jacobian := !![2]
    priorMean := ![0]
    priorCovariance := Matrix.diagonal ![3]
    observationErrorCovariance := Matrix.diagonal ![5] }

private lemma scalarProblem_prior_posSemidef :
    scalarProblem.priorCovariance.PosSemidef :=
  diag1_posSemidef 3 (by norm_num)

private lemma scalarProblem_observation_posDef :
    scalarProblem.observationErrorCovariance.PosDef :=
  diag1_posDef 5 (by norm_num)

private lemma scalarProblem_innovation_eq :
    scalarProblem.innovationCovariance = Matrix.diagonal ![(17 : ℝ)] := by
  ext i j
  fin_cases i
  fin_cases j
  norm_num [scalarProblem, Problem.innovationCovariance, Matrix.mul_apply,
    Matrix.vecMul, Matrix.vecHead, dotProduct, Matrix.diagonal, Matrix.conjTranspose]

private lemma scalarProblem_gain_eq :
    scalarProblem.gain = !![(6 / 17 : ℝ)] := by
  unfold Problem.gain
  rw [scalarProblem_innovation_eq]
  ext i j
  fin_cases i
  fin_cases j
  norm_num [scalarProblem, Matrix.inv_diagonal, Matrix.mul_apply, Matrix.vecMul,
    Matrix.vecHead, dotProduct, Matrix.diagonal, Matrix.conjTranspose, Ring.inverse]

private lemma scalarProblem_posterior_eq :
    posteriorCovariance scalarProblem = Matrix.diagonal ![(15 / 17 : ℝ)] := by
  unfold posteriorCovariance
  rw [scalarProblem_innovation_eq]
  ext i j
  fin_cases i
  fin_cases j
  norm_num [scalarProblem, Matrix.inv_diagonal, Matrix.mul_apply, Matrix.vecMul,
    Matrix.vecHead, dotProduct, Matrix.diagonal, Matrix.conjTranspose, Ring.inverse]

/-- 精确核对一维创新协方差。 -/
example : scalarProblem.innovationCovariance = !![17] := by
  calc
    scalarProblem.innovationCovariance = Matrix.diagonal ![(17 : ℝ)] :=
      scalarProblem_innovation_eq
    _ = !![17] := Matrix.diagonal_vec1 17

/-- 精确核对一维最优增益。 -/
example : scalarProblem.gain = !![(6 / 17 : ℝ)] := scalarProblem_gain_eq

/-- 精确核对一维后验协方差。 -/
example : posteriorCovariance scalarProblem = !![(15 / 17 : ℝ)] := by
  calc
    posteriorCovariance scalarProblem = Matrix.diagonal ![(15 / 17 : ℝ)] :=
      scalarProblem_posterior_eq
    _ = !![(15 / 17 : ℝ)] := Matrix.diagonal_vec1 _

/-- 一维精确例子满足后验协方差的半正定条件。 -/
example : (posteriorCovariance scalarProblem).PosSemidef :=
  posteriorCovariance_posSemidef scalarProblem
    scalarProblem_prior_posSemidef scalarProblem_observation_posDef

/-- 一维精确例子的 DOFS 为 `12 / 17`。 -/
example : scalarProblem.dofs = (12 / 17 : ℝ) := by
  unfold Problem.dofs dofs averagingKernel
  rw [scalarProblem_gain_eq]
  rw [Matrix.trace_fin_one]
  norm_num [scalarProblem, Matrix.mul_apply, Matrix.vecMul, Matrix.vecHead, dotProduct]

/-- 一维精确例子的信息矩阵为 `17 / 15`。 -/
example : informationMatrix scalarProblem = !![(17 / 15 : ℝ)] := by
  unfold informationMatrix
  ext i j
  fin_cases i
  fin_cases j
  norm_num [scalarProblem, Matrix.inv_diagonal, Matrix.mul_apply, Matrix.vecMul,
    Matrix.vecHead, dotProduct, Matrix.diagonal, Matrix.conjTranspose, Ring.inverse]

/-- 一维精确例子满足信息形式的后验逆恒等式。 -/
example : (posteriorCovariance scalarProblem)⁻¹ = informationMatrix scalarProblem := by
  exact posteriorCovariance_inv_eq_informationMatrix scalarProblem
    (diag1_posDef 3 (by norm_num)) (diag1_posDef 5 (by norm_num))

/-- 一维正定先验例子的后验协方差是正定的。 -/
example : (posteriorCovariance scalarProblem).PosDef := by
  exact posteriorCovariance_posDef scalarProblem
    (diag1_posDef 3 (by norm_num)) (diag1_posDef 5 (by norm_num))

/-- `2 × 1` 秩亏观测例子：第二个状态方向不进入观测。 -/
private def rankDeficientProblem : Problem 2 1 :=
  { jacobian := !![1, 0]
    priorMean := ![0, 0]
    priorCovariance := Matrix.diagonal ![1, 1]
    observationErrorCovariance := Matrix.diagonal ![1] }

private lemma rankDeficientProblem_prior_posSemidef :
    rankDeficientProblem.priorCovariance.PosSemidef :=
  diag2_posSemidef 1 1 (by norm_num) (by norm_num)

private lemma rankDeficientProblem_observation_posDef :
    rankDeficientProblem.observationErrorCovariance.PosDef :=
  diag1_posDef 1 (by norm_num)

private lemma rankDeficientProblem_innovation_eq :
    rankDeficientProblem.innovationCovariance = Matrix.diagonal ![(2 : ℝ)] := by
  ext i j
  fin_cases i
  fin_cases j
  norm_num [rankDeficientProblem, Problem.innovationCovariance, Matrix.mul_apply,
    Fin.sum_univ_succ, Matrix.vecMul, Matrix.vecHead, dotProduct,
    Matrix.diagonal, Matrix.conjTranspose]

/-- 核对秩亏 Jacobian 对第二个状态方向的观测为零。 -/
example :
    rankDeficientProblem.jacobian.mulVec (![0, 1] : State 2) =
      (0 : Observation 1) := by
  funext i
  fin_cases i
  norm_num [rankDeficientProblem, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- 核对秩亏 Jacobian 对第一个状态方向的观测为一。 -/
example :
    rankDeficientProblem.jacobian.mulVec (![1, 0] : State 2) =
      (![1] : Observation 1) := by
  funext i
  fin_cases i
  norm_num [rankDeficientProblem, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- 核对秩亏例子的创新协方差。 -/
example : rankDeficientProblem.innovationCovariance = !![2] := by
  calc
    rankDeficientProblem.innovationCovariance = Matrix.diagonal ![(2 : ℝ)] :=
      rankDeficientProblem_innovation_eq
    _ = !![2] := Matrix.diagonal_vec1 2

/-- 未观测状态方向的后验方差保持为一。 -/
example : posteriorCovariance rankDeficientProblem 1 1 = 1 := by
  unfold posteriorCovariance
  rw [rankDeficientProblem_innovation_eq]
  norm_num [rankDeficientProblem, Matrix.inv_diagonal, Matrix.mul_apply,
    Fin.sum_univ_succ, Matrix.vecMul, Matrix.vecHead, dotProduct,
    Matrix.diagonal, Matrix.conjTranspose, Matrix.transpose, Ring.inverse]

/-- 秩亏例子的后验协方差仍然半正定。 -/
example : (posteriorCovariance rankDeficientProblem).PosSemidef :=
  posteriorCovariance_posSemidef rankDeficientProblem
    rankDeficientProblem_prior_posSemidef rankDeficientProblem_observation_posDef

private def rankDeficientJacobian : Jacobian 2 1 := !![1, 0]

/-- 秩亏 Jacobian 不是静态可辨识的。 -/
example : ¬ Observable rankDeficientJacobian := by
  intro h
  have hinjective : Function.Injective rankDeficientJacobian.mulVec := h
  have hzero :
      rankDeficientJacobian.mulVec (![0, 1] : State 2) =
        rankDeficientJacobian.mulVec (0 : State 2) := by
    funext i
    fin_cases i
    norm_num [rankDeficientJacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  have hx : (![0, 1] : State 2) = 0 := hinjective hzero
  have hcoord := congrFun hx (1 : Fin 2)
  norm_num at hcoord

/-- 单位 Jacobian 是静态可辨识的。 -/
example : Observable (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  change Function.Injective (1 : Matrix (Fin 2) (Fin 2) ℝ).mulVec
  intro x y hxy
  simpa using hxy

/-- 正定观测权重和可辨识 Jacobian 给出正定加权正规矩阵。 -/
example {n m : ℕ} (k : Jacobian n m) (s : Covariance m)
    (hWeight : s.PosDef) (hObservable : Observable k) :
    (weightedNormalMatrix k s).PosDef :=
  weightedNormalMatrix_posDef k s hWeight hObservable

/-- 负定观测误差矩阵不能满足正定观测误差假设。 -/
example :
    ¬ (Matrix.diagonal ![(-1 : ℝ)] : Matrix (Fin 1) (Fin 1) ℝ).PosDef := by
  intro h
  have hi := h.diag_pos (i := (0 : Fin 1))
  norm_num at hi

/-- 零观测误差矩阵不能满足正定观测误差假设。 -/
example :
    ¬ (Matrix.diagonal ![(0 : ℝ)] : Matrix (Fin 1) (Fin 1) ℝ).PosDef := by
  intro h
  have hi := h.diag_pos (i := (0 : Fin 1))
  norm_num at hi

/-- 非对称矩阵不能被当作半正定协方差。 -/
private def asymmetricMatrix : Square 2 := !![1, 1; 0, 1]

example : ¬ asymmetricMatrix.PosSemidef := by
  intro h
  have hHermitian := h.isHermitian
  have hOffDiagonal := congrFun (congrFun hHermitian (0 : Fin 2)) (1 : Fin 2)
  norm_num [asymmetricMatrix, Matrix.conjTranspose, Matrix.transpose] at hOffDiagonal

end
end LeanOEM.Tests.Examples
