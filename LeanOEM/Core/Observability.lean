module

public import LeanOEM.Core.Types

@[expose] public section

namespace LeanOEM

/-- 静态线性可辨识性：Jacobian 的状态到观测映射是单射。 -/
def Observable {n m : ℕ} (k : Jacobian n m) : Prop :=
  Function.Injective k.mulVec

/-- 单射性等价于零观测残差只能来自零状态。 -/
theorem observable_iff_kernel_eq_zero {n m : ℕ} (k : Jacobian n m) :
    Observable k ↔ ∀ x : State n, k.mulVec x = 0 → x = 0 := by
  constructor
  · intro h
    have hinjective : Function.Injective k.mulVec := h
    intro x hx
    exact hinjective (by simpa using hx)
  · intro h
    have hkernel : ∀ x : State n, k.mulVec x = 0 → x = 0 := h
    intro x y hxy
    apply sub_eq_zero.mp
    apply hkernel (x - y)
    simp [Matrix.mulVec_sub, hxy]

/-- 加权正规矩阵 `Kᴴ S K` 的定义。 -/
def weightedNormalMatrix {n m : ℕ}
    (k : Jacobian n m) (s : Covariance m) : Square n :=
  k.conjTranspose * s * k

/-- 正定观测权重和满列秩 Jacobian 给出正定加权正规矩阵。 -/
theorem weightedNormalMatrix_posDef {n m : ℕ}
    (k : Jacobian n m) (s : Covariance m)
    (hWeight : s.PosDef) (hObservable : Observable k) :
    (weightedNormalMatrix k s).PosDef := by
  unfold weightedNormalMatrix
  simpa [Observable] using
    (Matrix.PosDef.conjTranspose_mul_mul_same hWeight hObservable)

end LeanOEM
