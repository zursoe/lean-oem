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
  (f.euclideanSupportBasis.reindex
      (finCongr f.euclideanSupport_finrank_eq_support)).toBasis.map
    f.supportEuclideanEquiv.symm

/-- canonical support 坐标的第 `j` 个 ambient 状态向量。 -/
def supportBasisVector (f : p.PriorSqrtFactor)
    (j : Fin (Module.finrank ℝ f.support)) : State n :=
  f.supportBasis j

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

/-- 基向量作为 ambient 向量族仍然线性无关。 -/
theorem supportBasisVector_linearIndependent (f : p.PriorSqrtFactor) :
    LinearIndependent ℝ f.supportBasisVector := by
  have hSubtype : LinearIndependent ℝ f.supportBasis := f.supportBasis.linearIndependent
  have hMapped := hSubtype.map' f.support.subtype (Submodule.ker_subtype f.support)
  change LinearIndependent ℝ (fun j => (f.supportBasis j : State n))
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
    exact Submodule.subset_span ⟨j, rfl⟩

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

end
end LeanOEM
