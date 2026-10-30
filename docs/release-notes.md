# lean-oem 0.1.0 候选版本说明

状态：本地候选版本，等待远端审查。当前分支为 `api/linear-core`，尚未推送到 `origin/main`。

核心实现审查基线：`120583e`（2026-10-30）。当前分支还包含发布材料、审计记录和脚本执行位修正提交；远端初始提交为 `8582a46`。

## 本版本内容

- 有限维、实数、矩阵表示的线性 OEM 问题规格；
- 预测、创新、创新协方差、最优增益和任意增益估计器；
- averaging kernel、确定性检索误差分解和 DOFS trace 定义；
- `Problem.WellPosed`、正定性、逆矩阵两侧消去和增益规格；
- 后验协方差、Joseph 形式、半正定性和先验减后验的半正定性；
- 静态可辨识性和正定权重下的加权正规矩阵；
- 信息矩阵、Woodbury 后验公式、后验正定性和后验逆矩阵恒等式；
- 一维、秩亏二维和非法协方差精确示例；
- 独立 `Fraction` 数值交叉验证和自动审计脚本。

## 形式化边界

本版本的定理只对 Lean 定义和显式矩阵假设负责。先验协方差、观测误差协方差、单位、概率模型、非线性前向模型、ARTS 参数和有限精度实现的现实有效性不由这些定理自动推出。

DOFS 上下界、谱半径、条件数、浮点误差界、单位系统、概率测度和 ARTS/Python 运行接口不属于本候选版本的公开核心 API。

## 复现

```bash
lake build
scripts/run_audit.sh
python3 scripts/validate_oem_numeric.py
```

依赖版本由 `lean-toolchain`、`lakefile.toml` 和 `lake-manifest.json` 固定。Mathlib 源码和 `.lake` 编译缓存不进入 Git。

干净 checkout 已重新物化锁定依赖并完成 3166 个构建目标，详细记录见 [`docs/audit/build-report.md`](audit/build-report.md)。

## 审查重点

- 矩阵方向是否始终保持 `K : m × n`、`g : n × m`；
- `observationErrorCovariance` 是否清楚地区分观测误差协方差与观测本身的协方差；
- 所有矩阵逆是否都有正定性或可逆性假设；
- 半正定、正定、静态可辨识性和经验数值证据是否保持语义分离；
- Woodbury 信息形式是否只在正定先验和正定观测误差条件下使用。
