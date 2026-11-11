module

public import LeanOEM.Physics.FiniteLayer
public import LeanOEM.Physics.FiniteLayerDiscretization
public import LeanOEM.Physics.ChannelDiscretization
public import LeanOEM.Physics.Spectral
public import LeanOEM.Physics.Discretization
public import LeanOEM.Physics.TwoLayerState

/-!
# 实验性物理模型入口

该入口聚合归一化有限层、谱线/通道响应、有限层状态模型和离散化误差
fixture。参数有效性由显式假设提供；单位系统和外部实现符合性未纳入本模块。
-/
