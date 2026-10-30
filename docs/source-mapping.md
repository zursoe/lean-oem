# Lean OEM 定义、定理和外部证据映射

本文档把 Lean 中的形式对象、形式假设、形式定理、独立数值验证和外部科研来源分开记录。外部来源用于说明术语、公式和应用背景，不作为 Lean 内核的证明输入。

## 公式来源

本项目采用的线性 OEM 记号和 averaging kernel、后验协方差、信息形式、DOFS 术语与 Rodgers 的大气反演教材一致：

- Clive D. Rodgers, *Inverse Methods for Atmospheric Sounding: Theory and Practice*, World Scientific, 2000；
- DOI：[`10.1142/3171`](https://doi.org/10.1142/3171)；
- Crossref 元数据现场核对日期：2026-10-30。

该书是术语和模型来源。它没有被导入 Lean，也没有把书中的现实假设自动转化为形式定理。

## 定义映射

- `LeanOEM.Problem.jacobian`：线性观测 Jacobian $K$，形状为观测维度乘状态维度；见 `LeanOEM/Core/LinearModel.lean`。
- `priorMean`：先验状态 $x_a$。
- `priorCovariance`：先验协方差 $S_a$。
- `observationErrorCovariance`：观测误差协方差 $S_\varepsilon$。
- `Problem.predict`：线性预测 $Kx$。
- `Problem.innovation`：观测减预测 $y-Kx$。
- `Problem.innovationCovariance`：

  $$
  S=K S_a K^\mathsf{T}+S_\varepsilon.
  $$

- `Problem.gain`：

  $$
  G=S_aK^\mathsf{T}S^{-1}.
  $$

- `estimateWithGain`：

  $$
  \hat{x}=x_a+G(y-Kx_a).
  $$

- `averagingKernel`：$A=GK$。
- `dofs`：$\operatorname{trace}(A)$。
- `posteriorCovariance`：

  $$
  S_{post}=S_a-S_aK^\mathsf{T}S^{-1}KS_a.
  $$

- `josephCovariance`：

  $$
  (I-GK)S_a(I-GK)^\mathsf{T}+G S_\varepsilon G^\mathsf{T}.
  $$

- `informationMatrix`：

  $$
  \Lambda=S_a^{-1}+K^\mathsf{T}S_\varepsilon^{-1}K.
  $$

- `Observable k`：`k.mulVec` 为单射，表示给定线性模型下的静态可辨识性。

## 形式假设和定理映射

- `Problem.WellPosed` 记录先验半正定和观测误差正定；它不声称现实数据自动满足这些条件。
- `innovationCovariance_posDef`：在先验半正定、观测误差正定时，创新协方差正定。
- `innovationCovariance_inv_mul` 与 `innovationCovariance_mul_inv`：在正定假设下，矩阵总函数逆满足两侧消去。
- `retrievalError_decomposition`：

  $$
  \hat{x}-x=(I-A)(x_a-x)+G\varepsilon.
  $$

- `josephCovariance_posSemidef`：Joseph 形式在两个输入协方差半正定时半正定。
- `posteriorCovariance_eq_josephCovariance`：标准后验公式与最优增益的 Joseph 形式等价。
- `posteriorCovariance_posSemidef`：良定性假设下后验协方差半正定。
- `prior_minus_posterior_posSemidef`：先验减后验为半正定合同变换。
- `informationMatrix_posDef`：先验正定时信息矩阵正定。
- `posteriorCovariance_eq_informationMatrix_inv`：由 Mathlib Woodbury 恒等式得到

  $$
  S_{post}=\Lambda^{-1}.
  $$

- `posteriorCovariance_inv_eq_informationMatrix`：

  $$
  S_{post}^{-1}=\Lambda.
  $$

- `weightedNormalMatrix_posDef`：正定观测权重和可辨识 Jacobian 给出正定 $K^\mathsf{T}SK$。

### 非线性观测模型第一批映射

- `ForwardModel.observe`：ARTS 无关的状态到观测函数 $F$，见 `LeanOEM/Core/ForwardModel.lean`；
- `ForwardModel.linearizedObserve`：锚点线性化模型 $F(x_a)+K(x-x_a)$；
- `ForwardModel.linearizationRemainder`：精确余项 $F(x)-F(x_a)-K(x-x_a)$；
- `ForwardModel.linearizedOffset`：将锚点模型改写为偏置加 `Problem.predict` 的偏置项；
- `ForwardModel.HasJacobianAt`：连续 Fréchet 导数由 `K : m × n` 表示的规格；
- `ForwardModel.JacobianSpec`：把连续线性导数和矩阵表示一起保存的结构；
- `ForwardModel.matrixDerivative`：有限函数基下的矩阵到连续线性映射转换。

第一批只证明代数恒等式和导数表示契约。它没有引入辐射传输方程、单位、ARTS 数据或浮点
误差界；标量平方模型位于 `LeanOEM/Tests/ForwardModel.lean`，用于检查非线性导数和二阶余项。

## 独立数值证据

`scripts/validate_oem_numeric.py` 使用 Python 标准库 `fractions.Fraction` 独立实现小型矩阵运算，避免依赖 Lean、Mathlib、NumPy 或 SciPy。它核对：

- 一维例子 $K=2$、$S_a=3$、$S_\varepsilon=5$；
- 创新协方差 $17$、增益 $6/17$、averaging kernel $12/17$、后验协方差 $15/17$；
- Joseph 形式、信息矩阵 $17/15$、后验逆矩阵和确定性误差分解；
- `2 × 1` 秩亏观测、不可观测状态方向和未收缩后验分量。

运行命令：

```bash
python3 scripts/validate_oem_numeric.py
```

这些结果是独立实现的精确有理数交叉验证，不能替代 Lean 证明，也不能证明 ARTS、观测数据库或有限精度程序满足模型假设。

## 计划中的正演和算法映射

P9 的第一批已经完成：后续形式化仍不把 ARTS 代码直接导入 Lean，而是继续建立独立的数学规格：

- `ForwardModel`：状态到观测的函数 $F : X \to Y$；
- `JacobianSpec`：$K(x)$ 作为 $F$ 的导数矩阵、导数的近似，或带明确误差界的数值构造；
- `linearizationRemainder`：

  $$
  F(x)=F(x_a)+K(x_a)(x-x_a)+r(x);
  $$

- `F_h`、`K_h`：有限层、有限差分、频率求积或通道离散化产生的数值近似；
- `GaussNewtonStep`：在非线性观测模型下使用 $F$、$K$、先验和观测误差的单步更新。

这些对象的形式定理可以证明维度、导数关系、递推性质、线性化余项条件和局部误差结论。ARTS/Python fixture 则记录具体版本、配置、谱线库、单位、数组哈希和数值误差，用来支持“具体 ARTS 输出符合某个形式规格”的工程判断。该判断不会被写成无条件的 Lean 定理。

## 当前边界

- 形式化核心没有单位系统；公式中的每个量默认已经在同一组一致单位下表达。
- 没有把随机变量、概率测度、期望或统计协方差引入核心；当前 `Covariance` 是带正定性假设的矩阵。
- 没有给浮点实现、条件数、舍入误差或迭代求解器建立误差界。
- 没有把 Python、ARTS 代码、运行数据、观测数据库或具体场景输出作为 Lean 依赖。
- 没有把连续辐射传输方程、有限层离散化、Doppler 频移、通道响应或非线性 Gauss–Newton 迭代形式化；这些属于路线 P10–P14。
- DOFS 的上下界、谱半径和特征值结论尚未加入；当前只定义 trace 并验证其代数性质。
- Rodgers 的教材支持术语和公式来源，不自动支持某个现实场景中的参数、先验或误差模型。
