# lean-oem 当前开发基线

状态：`0.1.0` 尚未打 tag，也没有 GitHub Release。本文件描述当前主线的完整范围，
不把早期线性核心审查提交误写成当前版本。

## 当前内容

- 有限维、实数、矩阵表示的线性 OEM 问题规格；
- 预测、创新、创新协方差、增益、后验协方差、Joseph 形式和信息形式；
- averaging kernel、DOFS trace、显式矩阵序条件下的上下界、静态可辨识性和确定性检索误差；
- `ForwardModel`、Jacobian 导数规格、二次余项和局部收缩契约；
- 非线性 Gauss–Newton 轨迹、停止判据和条件误差界；
- Jacobian、有限层和通道离散化误差契约；
- 前向模型/Jacobian 联合误差到正规方程和一步更新误差的传播；
- 带统一加性误差底的 Gauss–Newton 轨迹有限步界和稳态界；
- 归一化有限层、带正线宽参数包的谱线、Doppler、通道响应和两通道两状态有限层 fixture；
- 有限层、Gaussian 线宽、Doppler、Planck 和两层状态参数的非法边界合成反例；
- 显式矩阵序条件下的 DOFS 上下界和 Hermitian 逐特征值 `[0,1]` 界、正定先验/观测误差下最优增益的 `0 ≤ DOFS ≤ n` 定理，
  以及 Gaussian 线宽有效性接口；
- 通道空网格、负误差常数、零步长和有限层参数边界的合成反例；
- 正定先验的平方根因子、白化相似变换、原 averaging kernel 的实谱 `[0,1)` 界、
  特征多项式实数分裂和 DOFS 特征值求和；
- 奇异半正定先验的矩形 `SupportFactor`、支持坐标白化、严格谱界、零谱、秩界和 DOFS 支持维数界；
- 任意半正定先验的精确 `PriorSqrtFactor` 和 `range(sqrt Sₐ)` canonical support；
- canonical support 的 EuclideanSpace 正交规范基、有限坐标列矩阵、满列秩和像空间定理；
- `PriorSqrtFactor.toSupportFactor` 自动构造矩形支持因子，并提供协方差、满列秩和列空间定理；
- 支持因子下 ambient/support 特征多项式乘幂关系；
- 支持因子下 ambient/support 非零谱集合相等、零根代数重数加法，以及支持可辨识时的
  `n-r` 零方向重数；
- `Observable` 下的严格正特征值结论，以及白化 averaging kernel 的 Jacobian 秩上界；
- `LeanOEM.Core` 稳定聚合入口和 `LeanOEM.Physics` 实验聚合入口；
- 精确有理数交叉验证、公理审计和 GitHub Actions CI。

## 形式化边界

定理只对 Lean 定义和显式假设负责。单位、概率测度、浮点舍入、连续频率积分、完整谱线数据库、
真实观测和有限精度程序不属于本库主线。Physics 模块仍属于实验性 API，必须在参数有效性、
合成例子和形式审查完成后再承诺稳定兼容性。

## 复现

```bash
lake build
scripts/run_audit.sh
python3 scripts/validate_oem_numeric.py
```

依赖版本由 `lean-toolchain`、`lakefile.toml` 和 `lake-manifest.json` 固定。Mathlib 源码和
`.lake` 编译缓存不进入 Git。

## 后续发布门槛

下一阶段先完成稳定/实验入口审查、合成例子、形式边界文档和干净 checkout 构建，再决定
`v0.1.0` 是否发布。发布说明和审计文件必须记录实际代码提交号。
