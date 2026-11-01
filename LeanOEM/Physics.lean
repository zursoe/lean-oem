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
fixture。模块中的参数、单位和 外部实现符合性仍需调用者显式提供。
-/
