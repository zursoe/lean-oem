module

-- 测试构建也检查实验聚合入口，保证干净环境下公理审计所需的导入产物存在。
import LeanOEM.Physics

import LeanOEM.Tests.Basic
import LeanOEM.Tests.CoreEntry
import LeanOEM.Tests.PriorWhitening
import LeanOEM.Tests.SupportWhitening
import LeanOEM.Tests.SupportCoordinates
import LeanOEM.Tests.Examples
import LeanOEM.Tests.ForwardModel
import LeanOEM.Tests.FiniteLayer
import LeanOEM.Tests.FiniteLayerDiscretization
import LeanOEM.Tests.ChannelDiscretization
import LeanOEM.Tests.Spectral
import LeanOEM.Tests.Discretization
import LeanOEM.Tests.NonlinearOEM
import LeanOEM.Tests.SemanticBoundaries
import LeanOEM.Tests.Iteration
import LeanOEM.Tests.LocalContraction
import LeanOEM.Tests.DiscretizationError
import LeanOEM.Tests.TwoLayerState
