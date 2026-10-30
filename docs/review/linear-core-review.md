# 远端审查材料：有限维实数矩阵 OEM 核心

建议 PR 标题：`Add finite-dimensional real matrix OEM core`

## 摘要

本分支为 `lean-oem` 建立有限维、实数、矩阵表示的线性 OEM 核心 API。它覆盖创新协方差、最优增益、检索误差、averaging kernel、后验协方差、Joseph 形式、DOFS、静态可辨识性和信息形式，并把正定性、半正定性和可逆性作为显式假设。

## 主要文件

- `LeanOEM/Core/Types.lean`：状态、观测、Jacobian、方阵和协方差别名；
- `LeanOEM/Core/LinearModel.lean`：`Problem`、预测、创新和创新协方差；
- `LeanOEM/Core/Estimator.lean`：增益、估计器、averaging kernel 和检索误差；
- `LeanOEM/Core/Assumptions.lean`：良定性假设、正定性和逆矩阵辅助定理；
- `LeanOEM/Core/Covariance.lean`：后验协方差、Joseph 形式及半正定定理；
- `LeanOEM/Core/Diagnostics.lean`：DOFS trace 定义；
- `LeanOEM/Core/Observability.lean`：静态可辨识性和加权正规矩阵；
- `LeanOEM/Core/Information.lean`：信息矩阵和 Woodbury 恒等式；
- `LeanOEM/Tests/Examples.lean`：精确矩阵示例和失败边界；
- `scripts/run_audit.sh`、`scripts/validate_oem_numeric.py`：自动审计和独立数值核对。

## 验证

```bash
lake build
scripts/run_audit.sh
python3 scripts/validate_oem_numeric.py
```

当前验证通过：Lean 构建、公理审计、占位扫描、编译产物检查、精确一维示例和秩亏二维示例。

## 审查问题

1. `Fin n → ℝ` 和 `Matrix (Fin m) (Fin n) ℝ` 是否适合作为第一版稳定 API？
2. `Problem` 不携带协方差证明、而由 `WellPosed` 和定理参数提供假设，是否符合维护方向？
3. 将观测误差字段命名为 `observationErrorCovariance` 是否足以避免与观测本身协方差混淆？
4. Woodbury 信息形式只要求正定先验和正定观测误差，假设边界是否清晰？
5. DOFS 上下界和谱理论是否应继续作为后续独立模块？

## 明确不包含

本分支不包含 ARTS 数据库、Python 工程代码、实验数据、单位系统、浮点误差界、概率测度或具体场景结论。
