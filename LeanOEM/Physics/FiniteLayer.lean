module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic

@[expose] public section

namespace LeanOEM.RadiativeTransfer

/--
单层无散射辐射传输的最小数据。

`transmissivity` 是层透过率，`source` 是层的归一化源项。单位、谱线库和
具体数值算法不属于这个数学模型。
-/
structure Layer where
  transmissivity : ℝ
  source : ℝ

namespace Layer

/-- 单层模型的物理范围假设：透过率在 `[0, 1]`，源项非负。 -/
structure Valid (layer : Layer) : Prop where
  transmissivity_nonneg : 0 ≤ layer.transmissivity
  transmissivity_le_one : layer.transmissivity ≤ 1
  source_nonneg : 0 ≤ layer.source

/--
单层递推：输入辐亮度经过透过率衰减，并加入层源项。

这是有限层无散射模型的归一化形式：
`I_out = τ I_in + (1 - τ) S`。
-/
def propagate (layer : Layer) (incoming : ℝ) : ℝ :=
  layer.transmissivity * incoming
    + (1 - layer.transmissivity) * layer.source

theorem Valid.propagate_nonneg {layer : Layer} (hLayer : layer.Valid)
    {incoming : ℝ} (hIncoming : 0 ≤ incoming) :
    0 ≤ layer.propagate incoming := by
  unfold propagate
  exact add_nonneg
    (mul_nonneg hLayer.transmissivity_nonneg hIncoming)
    (mul_nonneg (sub_nonneg.mpr hLayer.transmissivity_le_one) hLayer.source_nonneg)

theorem Valid.propagate_le_of_le {layer : Layer} (hLayer : layer.Valid)
    {incoming upper : ℝ} (hIncoming : incoming ≤ upper)
    (hSource : layer.source ≤ upper) :
    layer.propagate incoming ≤ upper := by
  unfold propagate
  calc
    layer.transmissivity * incoming
        + (1 - layer.transmissivity) * layer.source
        ≤ layer.transmissivity * upper
          + (1 - layer.transmissivity) * upper := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left hIncoming hLayer.transmissivity_nonneg)
              (mul_le_mul_of_nonneg_left hSource
                (sub_nonneg.mpr hLayer.transmissivity_le_one))
    _ = upper := by ring

end Layer

/-- 按从下到上的顺序依次传播多个有限层。 -/
def propagateLayers : List Layer → ℝ → ℝ
  | [], incoming => incoming
  | layer :: rest, incoming => propagateLayers rest (layer.propagate incoming)

/-- 有限层列表中的每一层都满足 `Layer.Valid`。 -/
def allValid (layers : List Layer) : Prop :=
  ∀ layer ∈ layers, layer.Valid

theorem propagateLayers_nonneg {layers : List Layer} (hLayers : allValid layers)
    {incoming : ℝ} (hIncoming : 0 ≤ incoming) :
    0 ≤ propagateLayers layers incoming := by
  induction layers generalizing incoming with
  | nil => simpa [propagateLayers] using hIncoming
  | cons layer rest ih =>
      have hLayer : layer.Valid := hLayers layer (by simp)
      have hRest : allValid rest := by
        intro layer' hLayer'
        exact hLayers layer' (by simp [hLayer'])
      simpa [propagateLayers] using
        ih hRest (hLayer.propagate_nonneg hIncoming)

theorem propagateLayers_bounds {layers : List Layer} (hLayers : allValid layers)
    {incoming upper : ℝ} (hIncoming : 0 ≤ incoming) (hIncomingUpper : incoming ≤ upper)
    (hSources : ∀ layer ∈ layers, layer.source ≤ upper) :
    0 ≤ propagateLayers layers incoming ∧ propagateLayers layers incoming ≤ upper := by
  induction layers generalizing incoming with
  | nil =>
      simp [propagateLayers, hIncoming, hIncomingUpper]
  | cons layer rest ih =>
      have hLayer : layer.Valid := hLayers layer (by simp)
      have hRest : allValid rest := by
        intro layer' hLayer'
        exact hLayers layer' (by simp [hLayer'])
      have hLayerSource : layer.source ≤ upper := hSources layer (by simp)
      have hAfterNonneg : 0 ≤ layer.propagate incoming :=
        hLayer.propagate_nonneg hIncoming
      have hAfterUpper : layer.propagate incoming ≤ upper :=
        hLayer.propagate_le_of_le hIncomingUpper hLayerSource
      have hRestSources : ∀ layer' ∈ rest, layer'.source ≤ upper := by
        intro layer' hLayer'
        exact hSources layer' (by simp [hLayer'])
      simpa [propagateLayers] using
        ih hRest hAfterNonneg hAfterUpper hRestSources

/-- 两层递推的显式组合公式。 -/
def propagateTwo (first second : Layer) (incoming : ℝ) : ℝ :=
  second.propagate (first.propagate incoming)

theorem propagateTwo_eq (first second : Layer) (incoming : ℝ) :
    propagateTwo first second incoming =
      second.transmissivity * first.transmissivity * incoming
        + second.transmissivity * (1 - first.transmissivity) * first.source
        + (1 - second.transmissivity) * second.source := by
  unfold propagateTwo Layer.propagate
  ring

end LeanOEM.RadiativeTransfer
