module

public import LeanOEM.Core.Types
public import LeanOEM.Core.LinearModel
public import LeanOEM.Core.Estimator
public import LeanOEM.Core.Assumptions
public import LeanOEM.Core.Covariance
public import LeanOEM.Core.Diagnostics
public import LeanOEM.Core.Information
public import LeanOEM.Core.SpectralDiagnostics
public import LeanOEM.Core.PriorWhitening
public import LeanOEM.Core.Observability
public import LeanOEM.Core.Theorems
public import LeanOEM.Core.ForwardModel
public import LeanOEM.Core.NonlinearOEM
public import LeanOEM.Core.Iteration
public import LeanOEM.Core.LocalContraction
public import LeanOEM.Core.DiscretizationError

/-!
# 稳定核心入口

该入口聚合线性 OEM、非线性 Gauss–Newton、协方差、可辨识性、正演契约和
误差传播模块。核心不依赖具体外部工程或数值数据库。
-/
