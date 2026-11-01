module

public import LeanOEM.Core.ForwardModel
public import LeanOEM.Physics.FiniteLayer
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# 两层两状态有限层正演模型

该模块把每个层的归一化源项作为独立状态，形成一个两通道、两状态的
有限层正演模型。透过率和入射辐亮度是固定参数，状态到观测的 Jacobian
可以显式写出。它用于连接有限层递推、ForwardModel 和 OEM 误差契约，
不把源项自动解释为温度、吸收系数或风速。
-/

@[expose] public section

namespace LeanOEM.RadiativeTransfer

open LeanOEM

noncomputable section

/-- 两个通道的两层源项模型参数。 -/
structure TwoLayerStateParameters where
  firstTransmissivity : Fin 2 → ℝ
  secondTransmissivity : Fin 2 → ℝ
  incoming : Fin 2 → ℝ

namespace TwoLayerStateParameters

/-- 每个通道透过率属于物理范围。 -/
structure Valid (parameters : TwoLayerStateParameters) : Prop where
  first_nonneg : ∀ i, 0 ≤ parameters.firstTransmissivity i
  first_le_one : ∀ i, parameters.firstTransmissivity i ≤ 1
  second_nonneg : ∀ i, 0 ≤ parameters.secondTransmissivity i
  second_le_one : ∀ i, parameters.secondTransmissivity i ≤ 1

end TwoLayerStateParameters

/-- 第一层源项在通道输出中的系数。 -/
def twoLayerStateFirstCoefficient (parameters : TwoLayerStateParameters)
    (i : Fin 2) : ℝ :=
  parameters.secondTransmissivity i * (1 - parameters.firstTransmissivity i)

/-- 第二层源项在通道输出中的系数。 -/
def twoLayerStateSecondCoefficient (parameters : TwoLayerStateParameters)
    (i : Fin 2) : ℝ :=
  1 - parameters.secondTransmissivity i

/-- 两层入射项在每个通道中的常数部分。 -/
def twoLayerStateOffset (parameters : TwoLayerStateParameters) : Observation 2 :=
  ![parameters.secondTransmissivity 0 * parameters.firstTransmissivity 0
      * parameters.incoming 0,
    parameters.secondTransmissivity 1 * parameters.firstTransmissivity 1
      * parameters.incoming 1]

/-- 两通道、两状态有限层模型的显式 Jacobian。 -/
def twoLayerStateJacobian (parameters : TwoLayerStateParameters) : Jacobian 2 2 :=
  !![twoLayerStateFirstCoefficient parameters 0,
      twoLayerStateSecondCoefficient parameters 0;
    twoLayerStateFirstCoefficient parameters 1,
      twoLayerStateSecondCoefficient parameters 1]

/-- 两层源项模型的前向输出。 -/
def twoLayerStateObserve (parameters : TwoLayerStateParameters)
    (x : State 2) : Observation 2 :=
  twoLayerStateOffset parameters +
    (twoLayerStateJacobian parameters).mulVec x

/-- 将两层源项模型包装成通用 `ForwardModel`。 -/
def twoLayerStateModel (parameters : TwoLayerStateParameters) : ForwardModel 2 2 where
  observe := twoLayerStateObserve parameters

@[simp] theorem twoLayerStateFirstCoefficient_eq
    (parameters : TwoLayerStateParameters) (i : Fin 2) :
    twoLayerStateFirstCoefficient parameters i =
      parameters.secondTransmissivity i *
        (1 - parameters.firstTransmissivity i) := rfl

@[simp] theorem twoLayerStateSecondCoefficient_eq
    (parameters : TwoLayerStateParameters) (i : Fin 2) :
    twoLayerStateSecondCoefficient parameters i =
      1 - parameters.secondTransmissivity i := rfl

/-- 两层两状态模型的 Jacobian 是其精确 Fréchet 导数。 -/
theorem twoLayerState_hasJacobianAt
    (parameters : TwoLayerStateParameters) (x : State 2) :
    (twoLayerStateModel parameters).HasJacobianAt x
      (twoLayerStateJacobian parameters) := by
  let derivative : State 2 →L[ℝ] Observation 2 :=
    ForwardModel.matrixDerivative (twoLayerStateJacobian parameters)
  refine ⟨derivative, ?_, ?_⟩
  · have hLinear : HasFDerivAt
        (fun z : State 2 => derivative z) derivative x :=
      derivative.hasFDerivAt
    have hAffine := hLinear.const_add (twoLayerStateOffset parameters)
    simpa [twoLayerStateModel, twoLayerStateObserve, derivative,
      ForwardModel.matrixDerivative_apply] using hAffine
  · intro h
    simp [derivative]

end
end LeanOEM.RadiativeTransfer
