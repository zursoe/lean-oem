module

public import LeanOEM.Core.DiscretizationError
public import LeanOEM.Physics.FiniteLayer
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-!
# 两层有限层离散化

本模块把最小有限层递推提升为一个可以接入 OEM 的具体正演模型。
状态是一维的共同层源项，两个层的透过率是模型参数；近似模型只替换透过率，
因此可以同时比较正演输出和 Jacobian。所有误差结果都在精确实数和显式范围假设下成立。
-/

@[expose] public section

namespace LeanOEM.RadiativeTransfer

open LeanOEM
open LeanOEM.NonlinearProblem

noncomputable section

/-- 两层共同源项模型的固定参数。 -/
structure TwoLayerSourceParameters where
  firstTransmissivity : ℝ
  secondTransmissivity : ℝ
  incoming : ℝ

namespace TwoLayerSourceParameters

/-- 两层透过率和源项的物理范围。 -/
structure Valid (parameters : TwoLayerSourceParameters) : Prop where
  first_nonneg : 0 ≤ parameters.firstTransmissivity
  first_le_one : parameters.firstTransmissivity ≤ 1
  second_nonneg : 0 ≤ parameters.secondTransmissivity
  second_le_one : parameters.secondTransmissivity ≤ 1

theorem first_abs_le_one {parameters : TwoLayerSourceParameters}
    (hValid : parameters.Valid) :
    |parameters.firstTransmissivity| ≤ 1 := by
  rw [abs_of_nonneg hValid.first_nonneg]
  exact hValid.first_le_one

theorem second_abs_le_one {parameters : TwoLayerSourceParameters}
    (hValid : parameters.Valid) :
    |parameters.secondTransmissivity| ≤ 1 := by
  rw [abs_of_nonneg hValid.second_nonneg]
  exact hValid.second_le_one

end TwoLayerSourceParameters

/-- 两层共同源项的总源系数。 -/
def twoLayerSourceCoefficient (parameters : TwoLayerSourceParameters) : ℝ :=
  parameters.secondTransmissivity * (1 - parameters.firstTransmissivity)
    + (1 - parameters.secondTransmissivity)

/-- 两层共同源项模型的前向输出，状态空间和观测空间均为一维。 -/
def twoLayerSourceObserve (parameters : TwoLayerSourceParameters)
    (x : State 1) : Observation 1 :=
  ![parameters.secondTransmissivity * parameters.firstTransmissivity
      * parameters.incoming
      + twoLayerSourceCoefficient parameters * x 0]

/-- 两层共同源项模型包装成通用 `ForwardModel`。 -/
def twoLayerSourceModel (parameters : TwoLayerSourceParameters) : ForwardModel 1 1 where
  observe := twoLayerSourceObserve parameters

/-- 两层共同源项模型在状态坐标上的 Jacobian。 -/
def twoLayerSourceJacobian (parameters : TwoLayerSourceParameters) : Jacobian 1 1 :=
  !![twoLayerSourceCoefficient parameters]

@[simp] theorem twoLayerSourceCoefficient_eq_one_sub_product
    (parameters : TwoLayerSourceParameters) :
    twoLayerSourceCoefficient parameters =
      1 - parameters.firstTransmissivity * parameters.secondTransmissivity := by
  unfold twoLayerSourceCoefficient
  ring

theorem twoLayerSourceObserve_eq_propagateTwo
    (parameters : TwoLayerSourceParameters) (x : State 1) :
    twoLayerSourceObserve parameters x =
      ![propagateTwo
        { transmissivity := parameters.firstTransmissivity, source := x 0 }
        { transmissivity := parameters.secondTransmissivity, source := x 0 }
        parameters.incoming] := by
  funext i
  fin_cases i
  simp [twoLayerSourceObserve, propagateTwo, Layer.propagate,
    twoLayerSourceCoefficient]
  ring

/-- 一维状态向量的范数化简。 -/
theorem stateOneNorm (a : ℝ) : ‖(![a] : State 1)‖ = |a| := by
  have h : (![a] : State 1) = fun _ => a := by
    ext i
    fin_cases i
    rfl
  rw [h, pi_norm_const, Real.norm_eq_abs]

/-- 一维观测向量的范数化简。 -/
theorem observationOneNorm (a : ℝ) : ‖(![a] : Observation 1)‖ = |a| := by
  exact stateOneNorm a

/-- 两层模型的精确 Jacobian 契约。 -/
theorem twoLayerSource_hasJacobianAt
    (parameters : TwoLayerSourceParameters) (x : State 1) :
    (twoLayerSourceModel parameters).HasJacobianAt x
      (twoLayerSourceJacobian parameters) := by
  let coefficient := twoLayerSourceCoefficient parameters
  let offset := parameters.secondTransmissivity * parameters.firstTransmissivity
      * parameters.incoming
  let derivative : State 1 →L[ℝ] Observation 1 :=
    ContinuousLinearMap.pi (fun _ =>
      (ContinuousLinearMap.toSpanSingleton ℝ coefficient).comp
        (ContinuousLinearMap.proj (0 : Fin 1)))
  refine ⟨derivative, ?_, ?_⟩
  · rw [hasFDerivAt_pi]
    intro i
    fin_cases i
    have hLinear : HasFDerivAt (fun z : ℝ => coefficient * z)
        (ContinuousLinearMap.toSpanSingleton ℝ coefficient) (x 0) := by
      have hScalar : HasDerivAt (fun z : ℝ => coefficient * z)
          coefficient (x 0) :=
        hasDerivAt_const_mul (x := x 0) coefficient
      exact hScalar.hasFDerivAt
    have hAffine : HasFDerivAt (fun z : ℝ => offset + coefficient * z)
        (ContinuousLinearMap.toSpanSingleton ℝ coefficient) (x 0) := by
      simpa only [Pi.add_apply] using hLinear.const_add offset
    have hApply : HasFDerivAt (fun y : State 1 => y 0)
        (ContinuousLinearMap.proj (0 : Fin 1)) x :=
      hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 1) x
    have hComp := hAffine.comp x hApply
    simpa [twoLayerSourceModel, twoLayerSourceObserve, coefficient, offset,
      Function.comp_def] using hComp
  · intro h
    funext i
    fin_cases i
    simp [derivative, twoLayerSourceJacobian, Matrix.mulVec, dotProduct,
      coefficient]
    ring_nf

/-- 两个参数的透过率乘积误差由逐层误差控制。 -/
theorem transmissivity_product_error_le
    (exact approximate : TwoLayerSourceParameters)
    (hExact : exact.Valid) (hApproximate : approximate.Valid)
    {epsilonFirst epsilonSecond : ℝ}
    (hFirst : |approximate.firstTransmissivity - exact.firstTransmissivity|
      ≤ epsilonFirst)
    (hSecond : |approximate.secondTransmissivity - exact.secondTransmissivity|
      ≤ epsilonSecond) :
    |approximate.firstTransmissivity * approximate.secondTransmissivity
        - exact.firstTransmissivity * exact.secondTransmissivity|
      ≤ epsilonFirst + epsilonSecond := by
  calc
    |approximate.firstTransmissivity * approximate.secondTransmissivity
          - exact.firstTransmissivity * exact.secondTransmissivity| =
        |approximate.secondTransmissivity *
            (approximate.firstTransmissivity - exact.firstTransmissivity)
          + exact.firstTransmissivity *
            (approximate.secondTransmissivity - exact.secondTransmissivity)| := by
      congr 1
      ring
    _ ≤ |approximate.secondTransmissivity *
            (approximate.firstTransmissivity - exact.firstTransmissivity)|
          + |exact.firstTransmissivity *
            (approximate.secondTransmissivity - exact.secondTransmissivity)| :=
      abs_add_le _ _
    _ = |approximate.secondTransmissivity| *
          |approximate.firstTransmissivity - exact.firstTransmissivity|
          + |exact.firstTransmissivity| *
          |approximate.secondTransmissivity - exact.secondTransmissivity| := by
      rw [abs_mul, abs_mul]
    _ ≤ epsilonFirst + epsilonSecond := by
      exact add_le_add
        (calc
          |approximate.secondTransmissivity| *
                |approximate.firstTransmissivity - exact.firstTransmissivity|
              ≤ 1 * epsilonFirst := by
            calc
              |approximate.secondTransmissivity| *
                    |approximate.firstTransmissivity - exact.firstTransmissivity|
                  ≤ 1 *
                      |approximate.firstTransmissivity - exact.firstTransmissivity| :=
                mul_le_mul_of_nonneg_right
                  (TwoLayerSourceParameters.second_abs_le_one hApproximate)
                  (abs_nonneg _)
              _ ≤ 1 * epsilonFirst :=
                mul_le_mul_of_nonneg_left hFirst (by norm_num)
          _ = epsilonFirst := one_mul _)
        (calc
          |exact.firstTransmissivity| *
                |approximate.secondTransmissivity - exact.secondTransmissivity|
              ≤ 1 * epsilonSecond := by
            calc
              |exact.firstTransmissivity| *
                    |approximate.secondTransmissivity - exact.secondTransmissivity|
                  ≤ 1 *
                      |approximate.secondTransmissivity - exact.secondTransmissivity| :=
                mul_le_mul_of_nonneg_right
                  (TwoLayerSourceParameters.first_abs_le_one hExact)
                  (abs_nonneg _)
              _ ≤ 1 * epsilonSecond :=
                mul_le_mul_of_nonneg_left hSecond (by norm_num)
          _ = epsilonSecond := one_mul _)

/-- 透过率离散化误差对两层共同源项 Jacobian 系数的影响。 -/
theorem twoLayerSourceJacobian_coefficient_error_le
    (exact approximate : TwoLayerSourceParameters)
    (hExact : exact.Valid) (hApproximate : approximate.Valid)
    {epsilonFirst epsilonSecond : ℝ}
    (hFirst : |approximate.firstTransmissivity - exact.firstTransmissivity|
      ≤ epsilonFirst)
    (hSecond : |approximate.secondTransmissivity - exact.secondTransmissivity|
      ≤ epsilonSecond) :
    |twoLayerSourceCoefficient approximate - twoLayerSourceCoefficient exact|
      ≤ epsilonFirst + epsilonSecond := by
  rw [twoLayerSourceCoefficient_eq_one_sub_product,
    twoLayerSourceCoefficient_eq_one_sub_product]
  simpa [abs_sub_comm] using
    transmissivity_product_error_le exact approximate hExact hApproximate
      hFirst hSecond

/-- 单位观测权重下，有限层 Jacobian 误差满足 OEM 加权作用界。 -/
theorem twoLayerSource_weightedJacobianErrorBound_unit
    (exact approximate : TwoLayerSourceParameters)
    (hExact : exact.Valid) (hApproximate : approximate.Valid)
    {epsilonFirst epsilonSecond : ℝ}
    (hFirst : |approximate.firstTransmissivity - exact.firstTransmissivity|
      ≤ epsilonFirst)
    (hSecond : |approximate.secondTransmissivity - exact.secondTransmissivity|
      ≤ epsilonSecond) :
    ∀ v : Observation 1,
      ‖(twoLayerSourceJacobian approximate).conjTranspose.mulVec
          ((!![1] : Square 1).mulVec v) -
        (twoLayerSourceJacobian exact).conjTranspose.mulVec
          ((!![1] : Square 1).mulVec v)‖ ≤
        (epsilonFirst + epsilonSecond) * ‖v‖ := by
  intro v
  have hV : v = ![v 0] := by
    ext i
    fin_cases i
    rfl
  rw [hV]
  have hCoefficient := twoLayerSourceJacobian_coefficient_error_le
    exact approximate hExact hApproximate hFirst hSecond
  have hEq :
      (twoLayerSourceJacobian approximate).conjTranspose.mulVec
          ((!![1] : Square 1).mulVec ![v 0]) -
        (twoLayerSourceJacobian exact).conjTranspose.mulVec
          ((!![1] : Square 1).mulVec ![v 0]) =
        ![(twoLayerSourceCoefficient approximate -
          twoLayerSourceCoefficient exact) * v 0] := by
    ext i
    fin_cases i
    simp [twoLayerSourceJacobian, Matrix.conjTranspose, Matrix.transpose,
      Matrix.mulVec, Matrix.vecHead, dotProduct]
    ring_nf
  rw [hEq, stateOneNorm, observationOneNorm, abs_mul]
  exact mul_le_mul_of_nonneg_right hCoefficient (abs_nonneg _)

/-- 将两层模型的单位权重误差提升为 OEM 的 Jacobian 误差契约。 -/
theorem twoLayerSource_weightedJacobianErrorBound_of_unitWeight
    (p : NonlinearProblem 1 1) (hWeight : p.observationWeight = !![1])
    (exact approximate : TwoLayerSourceParameters)
    (hExact : exact.Valid) (hApproximate : approximate.Valid)
    {epsilonFirst epsilonSecond : ℝ}
    (hFirst : |approximate.firstTransmissivity - exact.firstTransmissivity|
      ≤ epsilonFirst)
    (hSecond : |approximate.secondTransmissivity - exact.secondTransmissivity|
      ≤ epsilonSecond) :
    p.WeightedJacobianErrorBound (twoLayerSourceJacobian approximate)
      (twoLayerSourceJacobian exact) (epsilonFirst + epsilonSecond) := by
  unfold WeightedJacobianErrorBound
  intro v
  rw [hWeight]
  exact twoLayerSource_weightedJacobianErrorBound_unit exact approximate
    hExact hApproximate hFirst hSecond v

/-- 有界状态和入射辐亮度下，透过率离散化造成的正演误差界。 -/
theorem twoLayerSource_forward_error_le
    (exact approximate : TwoLayerSourceParameters)
    (hExact : exact.Valid) (hApproximate : approximate.Valid)
    (hIncoming : approximate.incoming = exact.incoming)
    (x : State 1) {epsilonFirst epsilonSecond incomingBound stateBound : ℝ}
    (hEpsilonFirst : 0 ≤ epsilonFirst) (hEpsilonSecond : 0 ≤ epsilonSecond)
    (hFirst : |approximate.firstTransmissivity - exact.firstTransmissivity|
      ≤ epsilonFirst)
    (hSecond : |approximate.secondTransmissivity - exact.secondTransmissivity|
      ≤ epsilonSecond)
    (hIncomingBound : |exact.incoming| ≤ incomingBound)
    (hStateBound : |x 0| ≤ stateBound) :
    ‖twoLayerSourceObserve approximate x - twoLayerSourceObserve exact x‖ ≤
      (epsilonFirst + epsilonSecond) * (incomingBound + stateBound) := by
  have hCoefficient := twoLayerSourceJacobian_coefficient_error_le
    exact approximate hExact hApproximate hFirst hSecond
  have hEq :
      twoLayerSourceObserve approximate x - twoLayerSourceObserve exact x =
        ![(twoLayerSourceCoefficient exact -
          twoLayerSourceCoefficient approximate) *
          (exact.incoming - x 0)] := by
    funext i
    fin_cases i
    dsimp [twoLayerSourceObserve]
    change
      (approximate.secondTransmissivity * approximate.firstTransmissivity *
          approximate.incoming +
        twoLayerSourceCoefficient approximate * x 0) -
        (exact.secondTransmissivity * exact.firstTransmissivity * exact.incoming +
          twoLayerSourceCoefficient exact * x 0) =
        (twoLayerSourceCoefficient exact -
          twoLayerSourceCoefficient approximate) *
          (exact.incoming - x 0)
    rw [hIncoming]
    rw [twoLayerSourceCoefficient_eq_one_sub_product,
      twoLayerSourceCoefficient_eq_one_sub_product]
    ring_nf
  rw [hEq, observationOneNorm, abs_mul]
  have hDifference : |exact.incoming - x 0| ≤ incomingBound + stateBound := by
    calc
      |exact.incoming - x 0| ≤ |exact.incoming| + |x 0| := abs_sub _ _
      _ ≤ incomingBound + stateBound := add_le_add hIncomingBound hStateBound
  have hErrorNonneg : 0 ≤ epsilonFirst + epsilonSecond :=
    add_nonneg hEpsilonFirst hEpsilonSecond
  have hCoefficient' :
      |twoLayerSourceCoefficient exact - twoLayerSourceCoefficient approximate| ≤
        epsilonFirst + epsilonSecond := by
    simpa [abs_sub_comm] using hCoefficient
  calc
    |twoLayerSourceCoefficient exact - twoLayerSourceCoefficient approximate| *
        |exact.incoming - x 0| ≤
      (epsilonFirst + epsilonSecond) *
        |exact.incoming - x 0| :=
      mul_le_mul_of_nonneg_right hCoefficient' (abs_nonneg _)
    _ ≤ (epsilonFirst + epsilonSecond) *
        (incomingBound + stateBound) :=
      mul_le_mul_of_nonneg_left hDifference hErrorNonneg

end
end LeanOEM.RadiativeTransfer
