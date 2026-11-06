module

public import LeanOEM.Core.SupportWhitening
public import Mathlib.Analysis.InnerProductSpace.Subspace

/-!
# 奇异先验的 canonical 支持坐标

`PriorSqrtFactor.support` 是平方根先验因子的像空间。为了把这个子空间交给
`SupportFactor` 使用，本文件为它选择一个由 Mathlib 提供的正交规范基，并把基向量
组织成一个矩形列矩阵。

本层只固定坐标契约：列矩阵满列秩，且其列空间正好是 canonical support。它不把任意
子空间基误认为先验协方差的 Gram 因子，也不在这里引入 Moore--Penrose 伪逆。
-/

@[expose] public section

namespace LeanOEM

noncomputable section

open scoped MatrixOrder BigOperators

namespace Problem.PriorSqrtFactor

variable {n m : ℕ} {p : Problem n m}

/-! ## 正交规范基和列矩阵 -/

/-! `State n` 使用函数空间的代数表示，而 Mathlib 的欧氏内积位于
`EuclideanSpace ℝ (Fin n) = PiLp 2 (Fin n → ℝ)`。下面的线性等价只负责把支持子空间
搬到这个带内积的表示中；它不改变矩阵 API 的 `State n` 表示。 -/

/-- `State n` 与其 EuclideanSpace 表示之间的线性等价。 -/
def stateEuclideanEquiv (n : ℕ) :
    State n ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
  (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm

/-- canonical support 在 EuclideanSpace 中的像。 -/
def euclideanSupport (f : p.PriorSqrtFactor) :
    Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
  f.support.map (stateEuclideanEquiv n).toLinearMap

theorem euclideanSupport_finrank_eq_support (f : p.PriorSqrtFactor) :
    Module.finrank ℝ f.euclideanSupport = Module.finrank ℝ f.support := by
  change Module.finrank ℝ (f.support.map (stateEuclideanEquiv n).toLinearMap) =
    Module.finrank ℝ f.support
  exact LinearEquiv.finrank_map_eq (stateEuclideanEquiv n) f.support

/-- EuclideanSpace 中的正交规范基；它是 canonical 坐标的几何来源。 -/
def euclideanSupportBasis (f : p.PriorSqrtFactor) :
    OrthonormalBasis (Fin (Module.finrank ℝ f.euclideanSupport)) ℝ f.euclideanSupport :=
  stdOrthonormalBasis ℝ f.euclideanSupport

/-- 将 Euclidean support 基重索引到 `Fin (finrank support)`。 -/
def reindexedEuclideanSupportBasis (f : p.PriorSqrtFactor) :
    OrthonormalBasis (Fin (Module.finrank ℝ f.support)) ℝ f.euclideanSupport :=
  f.euclideanSupportBasis.reindex
    (finCongr f.euclideanSupport_finrank_eq_support)

/-- 支持子空间与 EuclideanSpace 像之间的线性等价。 -/
def supportEuclideanEquiv (f : p.PriorSqrtFactor) :
    f.support ≃ₗ[ℝ] f.euclideanSupport :=
  by
    simpa [euclideanSupport] using (stateEuclideanEquiv n).submoduleMap f.support

/-! `State n` 的既有函数范数不是 Euclidean 范数，因此这里的公共坐标对象是搬回支持
子空间后的 `Basis`；正交性保留在 `euclideanSupportBasis` 中，不能为 `State n` 伪造
一个不相容的 ambient `InnerProductSpace` 实例。 -/

/-- canonical support 的基，已重索引为 `Fin (finrank support)`。 -/
def supportBasis (f : p.PriorSqrtFactor) :
    Module.Basis (Fin (Module.finrank ℝ f.support)) ℝ f.support :=
  f.reindexedEuclideanSupportBasis.toBasis.map
    f.supportEuclideanEquiv.symm

/-- canonical support 坐标的第 `j` 个 ambient 状态向量。 -/
def supportBasisVector (f : p.PriorSqrtFactor)
    (j : Fin (Module.finrank ℝ f.support)) : State n :=
  f.supportBasis j

@[simp]
theorem supportBasisVector_eq_coe (f : p.PriorSqrtFactor)
    (j : Fin (Module.finrank ℝ f.support)) :
    f.supportBasisVector j = (f.supportBasis j : State n) :=
  rfl

/-- 支持基向量搬到 EuclideanSpace 后就是重索引的正交规范基向量。 -/
theorem stateEuclideanEquiv_supportBasisVector (f : p.PriorSqrtFactor)
    (j : Fin (Module.finrank ℝ f.support)) :
    stateEuclideanEquiv n (f.supportBasisVector j) =
      (f.reindexedEuclideanSupportBasis j : EuclideanSpace ℝ (Fin n)) := by
  change stateEuclideanEquiv n
      (↑(f.supportEuclideanEquiv.symm (f.reindexedEuclideanSupportBasis j)) : State n) = _
  have hMap (x : f.support) :
      (f.supportEuclideanEquiv x : EuclideanSpace ℝ (Fin n)) =
        stateEuclideanEquiv n (x : State n) := by
    change stateEuclideanEquiv n (x : State n) = stateEuclideanEquiv n (x : State n)
    rfl
  have hInv :
      (f.supportEuclideanEquiv (f.supportEuclideanEquiv.symm
        (f.reindexedEuclideanSupportBasis j)) : EuclideanSpace ℝ (Fin n)) =
        (f.reindexedEuclideanSupportBasis j : EuclideanSpace ℝ (Fin n)) :=
    congrArg (fun z : f.euclideanSupport =>
      (z : EuclideanSpace ℝ (Fin n)))
    (f.supportEuclideanEquiv.apply_symm_apply (f.reindexedEuclideanSupportBasis j))
  rw [hMap] at hInv
  exact hInv

/-- 把 canonical support 基向量按列写成矩阵。 -/
def supportBasisMatrix (f : p.PriorSqrtFactor) :
    Matrix (Fin n) (Fin (Module.finrank ℝ f.support)) ℝ :=
  fun i j => f.supportBasisVector j i

@[simp]
theorem supportBasisMatrix_apply (f : p.PriorSqrtFactor)
    (i : Fin n) (j : Fin (Module.finrank ℝ f.support)) :
    f.supportBasisMatrix i j = f.supportBasisVector j i :=
  rfl

@[simp]
theorem supportBasisMatrix_col (f : p.PriorSqrtFactor)
    (j : Fin (Module.finrank ℝ f.support)) :
    f.supportBasisMatrix.col j = f.supportBasisVector j := by
  funext i
  rfl

/-- 正交规范基列矩阵的 Gram 矩阵是单位矩阵。 -/
theorem supportBasisMatrix_conjTranspose_mul_self (f : p.PriorSqrtFactor) :
    f.supportBasisMatrix.conjTranspose * f.supportBasisMatrix =
      (1 : Matrix (Fin (Module.finrank ℝ f.support))
        (Fin (Module.finrank ℝ f.support)) ℝ) := by
  ext j k
  have hBasis := f.reindexedEuclideanSupportBasis.inner_eq_ite k j
  have hCoord (j : Fin (Module.finrank ℝ f.support)) (i : Fin n) :
      f.supportBasisVector j i =
        (f.reindexedEuclideanSupportBasis j : EuclideanSpace ℝ (Fin n)) i := by
    have h := congrArg (fun x : EuclideanSpace ℝ (Fin n) => x i)
      (f.stateEuclideanEquiv_supportBasisVector j)
    simpa [stateEuclideanEquiv] using h
  simpa [supportBasisMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
    hCoord, Matrix.one_apply, PiLp.inner_apply, RCLike.inner_apply', eq_comm] using hBasis

/-! ## 从支持投影到 Gram 因子 -/

/--
若列矩阵 `Q` 的 Gram 矩阵为单位矩阵，且其列空间等于一个 Hermitian 矩阵 `A` 的像空间，
则 `A Q` 的 Gram 矩阵与 `A` 的 Gram 矩阵相同。这个引理把“正交规范基张成支持”与
后续的协方差因子恒等式分开。
-/
private theorem mul_basis_gram_eq_of_range_eq
    {r : ℕ} {A : Square n} (Q : Matrix (Fin n) (Fin r) ℝ)
    (hQ : Q.conjTranspose * Q = (1 : Square r))
    (hRange : LinearMap.range Q.mulVecLin = LinearMap.range A.mulVecLin)
    (hA : A.IsHermitian) :
    (A * Q) * (A * Q).conjTranspose = A * A.conjTranspose := by
  let P : Square n := Q * Q.conjTranspose
  have hPA : P * A = A := by
    ext i j
    have hAcol : A.col j ∈ LinearMap.range A.mulVecLin := by
      refine ⟨Pi.single j 1, ?_⟩
      simp
    have hQcol : A.col j ∈ LinearMap.range Q.mulVecLin := by
      rw [hRange]
      exact hAcol
    rcases hQcol with ⟨x, hx⟩
    have hx' : Q.mulVec x = A.col j := by
      simpa only [Matrix.coe_mulVecLin] using hx
    have hProj : P.mulVec (A.col j) = A.col j := by
      calc
        P.mulVec (A.col j) = P.mulVec (Q.mulVec x) := congrArg P.mulVec hx'.symm
        _ = Q.mulVec ((Q.conjTranspose * Q).mulVec x) := by
          rw [show P = Q * Q.conjTranspose from rfl, Matrix.mulVec_mulVec,
            Matrix.mulVec_mulVec, Matrix.mul_assoc]
        _ = Q.mulVec x := by rw [hQ]; simp
        _ = A.col j := hx'
    have hCol : (P * A).col j = A.col j := by
      rw [Matrix.col_mul_eq_mulVec_col]
      exact hProj
    exact congrFun hCol i
  have hAT : A.transpose = A := by
    ext i j
    have hij := congrArg (fun M : Square n => M i j) hA.eq
    simpa [Matrix.conjTranspose, Matrix.transpose, starRingEnd_apply] using hij
  have hP : P.transpose = P := by
    simp [P]
  have hAP : A * P = A := by
    have hTranspose := congrArg Matrix.transpose hPA
    simpa [Matrix.transpose_mul, hP, hAT] using hTranspose
  calc
    (A * Q) * (A * Q).conjTranspose = (A * P) * A.conjTranspose := by
      simp [P, Matrix.mul_assoc]
    _ = A * A.conjTranspose := by rw [hAP]

/-- 基向量作为 ambient 向量族仍然线性无关。 -/
theorem supportBasisVector_linearIndependent (f : p.PriorSqrtFactor) :
    LinearIndependent ℝ f.supportBasisVector := by
  have hSubtype : LinearIndependent ℝ f.supportBasis := f.supportBasis.linearIndependent
  have hMapped := hSubtype.map' f.support.subtype (Submodule.ker_subtype f.support)
  have hVec : f.supportBasisVector = fun j => (f.supportBasis j : State n) := by
    funext j
    rfl
  rw [hVec]
  exact hMapped

/-- 列矩阵的 `mulVec` 是单射，即 canonical 坐标确实是满列秩坐标。 -/
theorem supportBasisMatrix_injective (f : p.PriorSqrtFactor) :
    Function.Injective f.supportBasisMatrix.mulVec := by
  rw [Matrix.mulVec_injective_iff]
  change LinearIndependent ℝ (fun j => f.supportBasisVector j)
  exact f.supportBasisVector_linearIndependent

/-! ## 像空间契约 -/

/-- 列矩阵的线性映射像正是 canonical support。 -/
theorem supportBasisMatrix_range_eq_support (f : p.PriorSqrtFactor) :
    LinearMap.range f.supportBasisMatrix.mulVecLin = f.support := by
  rw [Matrix.range_mulVecLin]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro v ⟨j, rfl⟩
    simp [supportBasisMatrix_col, supportBasisVector]
  · intro v hv
    rcases (f.supportBasis.mem_submodule_iff').mp hv with ⟨c, hc⟩
    rw [hc]
    apply Submodule.sum_mem
    intro j hj
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨j, by simp [supportBasisVector_eq_coe]⟩

/-- canonical support 坐标与平方根因子组合后的协方差 Gram 恒等式。 -/
theorem supportFactorMatrix_gram_eq (f : p.PriorSqrtFactor) :
    (f.matrix * f.supportBasisMatrix) *
        (f.matrix * f.supportBasisMatrix).conjTranspose =
      p.priorCovariance := by
  rw [f.covariance_eq]
  exact mul_basis_gram_eq_of_range_eq f.supportBasisMatrix
    f.supportBasisMatrix_conjTranspose_mul_self
    (by simpa [support] using f.supportBasisMatrix_range_eq_support)
    f.matrix_posSemidef.isHermitian

/-- Gram 等式和先验秩等式共同推出自动支持因子的满列秩。 -/
theorem supportFactorMatrix_injective (f : p.PriorSqrtFactor) :
    Function.Injective
      (f.matrix * f.supportBasisMatrix).mulVec := by
  let L : Matrix (Fin n) (Fin (Module.finrank ℝ f.support)) ℝ :=
    f.matrix * f.supportBasisMatrix
  have hRangeRank :
      Module.finrank ℝ (LinearMap.range L.mulVecLin) =
        Module.finrank ℝ (Fin (Module.finrank ℝ f.support) → ℝ) := by
    calc
      Module.finrank ℝ (LinearMap.range L.mulVecLin) = L.rank := rfl
      _ = (L * L.conjTranspose).rank :=
        (Matrix.rank_self_mul_conjTranspose L).symm
      _ = p.priorCovariance.rank := by
        rw [show L = f.matrix * f.supportBasisMatrix from rfl,
          f.supportFactorMatrix_gram_eq]
      _ = Module.finrank ℝ f.support :=
        f.support_finrank_eq_priorCovariance_rank.symm
      _ = Module.finrank ℝ (Fin (Module.finrank ℝ f.support) → ℝ) := by
        simp
  have hNull := L.mulVecLin.finrank_range_add_finrank_ker
  have hKerFinrank : Module.finrank ℝ (LinearMap.ker L.mulVecLin) = 0 := by
    have hEq :
        Module.finrank ℝ (LinearMap.range L.mulVecLin) +
            Module.finrank ℝ (LinearMap.ker L.mulVecLin) =
          Module.finrank ℝ (LinearMap.range L.mulVecLin) := by
      calc
        Module.finrank ℝ (LinearMap.range L.mulVecLin) +
              Module.finrank ℝ (LinearMap.ker L.mulVecLin) =
            Module.finrank ℝ (Fin (Module.finrank ℝ f.support) → ℝ) := hNull
        _ = Module.finrank ℝ (LinearMap.range L.mulVecLin) := hRangeRank.symm
    have hEq' :
        Module.finrank ℝ (LinearMap.range L.mulVecLin) +
            Module.finrank ℝ (LinearMap.ker L.mulVecLin) =
          Module.finrank ℝ (LinearMap.range L.mulVecLin) + 0 := by
      simpa using hEq
    exact Nat.add_left_cancel hEq'
  have hKer : LinearMap.ker L.mulVecLin = ⊥ :=
    Submodule.finrank_eq_zero.mp hKerFinrank
  have hInjective : Function.Injective L.mulVecLin :=
    LinearMap.ker_eq_bot.mp hKer
  simpa only [L, Matrix.coe_mulVecLin] using hInjective

/-- 从 canonical support 自动构造矩形满列秩 `SupportFactor`。 -/
def toSupportFactor (f : p.PriorSqrtFactor) :
    @Problem.SupportFactor n m (Module.finrank ℝ f.support) p where
  matrix := f.matrix * f.supportBasisMatrix
  injective := f.supportFactorMatrix_injective
  covariance_eq := f.supportFactorMatrix_gram_eq.symm

@[simp]
theorem toSupportFactor_matrix (f : p.PriorSqrtFactor) :
    f.toSupportFactor.matrix = f.matrix * f.supportBasisMatrix :=
  rfl

theorem toSupportFactor_covariance_eq (f : p.PriorSqrtFactor) :
    p.priorCovariance = f.toSupportFactor.matrix * f.toSupportFactor.matrix.conjTranspose :=
  f.toSupportFactor.covariance_eq

/-- 自动支持因子的列空间仍然是 canonical support。 -/
theorem toSupportFactor_range_eq_support (f : p.PriorSqrtFactor) :
    LinearMap.range f.toSupportFactor.matrix.mulVecLin = f.support := by
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro v ⟨x, rfl⟩
    change ∃ y : State n, f.matrix.mulVec y =
      f.toSupportFactor.matrix.mulVec x
    refine ⟨f.supportBasisMatrix.mulVec x, ?_⟩
    simp [toSupportFactor_matrix, Matrix.mulVec_mulVec]
  · calc
      Module.finrank ℝ (LinearMap.range f.toSupportFactor.matrix.mulVecLin) =
          Module.finrank ℝ (Fin (Module.finrank ℝ f.support) → ℝ) :=
        LinearMap.finrank_range_of_inj f.toSupportFactor.injective
      _ = Module.finrank ℝ f.support := by simp

/-- 矩阵列空间的有限维数等于先验协方差的秩。 -/
theorem supportBasisMatrix_range_finrank_eq_priorCovariance_rank
    (f : p.PriorSqrtFactor) :
    Module.finrank ℝ (LinearMap.range f.supportBasisMatrix.mulVecLin) =
      p.priorCovariance.rank := by
  rw [f.supportBasisMatrix_range_eq_support]
  exact f.support_finrank_eq_priorCovariance_rank

/-- 列矩阵的秩等于 canonical support 的维数。 -/
theorem supportBasisMatrix_rank_eq_support_finrank (f : p.PriorSqrtFactor) :
    f.supportBasisMatrix.rank = Module.finrank ℝ f.support := by
  rw [Matrix.rank]
  have hInjective : Function.Injective f.supportBasisMatrix.mulVecLin := by
    simpa only [Matrix.coe_mulVecLin] using f.supportBasisMatrix_injective
  simpa using LinearMap.finrank_range_of_inj hInjective

end Problem.PriorSqrtFactor

namespace Problem.SupportFactor

variable {n m r : ℕ} {p : Problem n m}

/-! ## ambient 与支持矩阵的非零谱关系 -/

/--
支持因子下，ambient averaging kernel 与支持白化矩阵只差一个非方阵因子交换。

这里的 `X` 是支持因子 `L`，`Y` 是
`Lᴴ Kᴴ Sᵧ⁻¹ K`。因此 Mathlib 的矩形特征多项式恒等式可以直接给出非零谱关系，
而不需要在奇异情形下构造完整相似变换。
-/
theorem averagingKernel_charpoly_eq_support_factor
    (f : @Problem.SupportFactor n m r p) :
    (averagingKernel p.gain p.jacobian).charpoly =
      (Polynomial.X : Polynomial ℝ) ^ (n - r) *
        f.whitenedAveragingKernel.charpoly := by
  let Y : Matrix (Fin r) (Fin n) ℝ :=
    f.matrix.conjTranspose * p.jacobian.conjTranspose *
      p.innovationCovariance⁻¹ * p.jacobian
  have hAmbient :
      averagingKernel p.gain p.jacobian = f.matrix * Y := by
    simp [Y, averagingKernel, Problem.gain, f.covariance_eq, Matrix.mul_assoc]
  have hSupport : f.whitenedAveragingKernel = Y * f.matrix := by
    simp [Y, Problem.SupportFactor.whitenedAveragingKernel,
      Problem.SupportFactor.supportJacobian,
      Matrix.mul_assoc]
  have hle : r ≤ n := by
    calc
      r = f.matrix.rank := f.matrix_rank_eq_support_dim.symm
      _ ≤ n := Matrix.rank_le_height f.matrix
  rw [hAmbient, hSupport]
  simpa [Fintype.card_fin] using
    (Matrix.charpoly_mul_comm_of_le f.matrix Y
      (by simpa only [Fintype.card_fin] using hle))

end Problem.SupportFactor

end
end LeanOEM
