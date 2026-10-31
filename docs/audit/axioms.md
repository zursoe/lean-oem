# 公理审计记录

审计日期：2026-10-31

审计提交：`58fcdf1`

执行命令：

```bash
lake env lean LeanOEM/Tests/Axioms.lean
```

核心定理输出均只依赖以下基础公理：

```text
[propext, Classical.choice, Quot.sound]
```

审计的公开定理包括：

- `innovationCovariance_posDef`；
- `innovationCovariance_isUnit`；
- `innovationCovariance_inv_posDef`；
- `innovationCovariance_inv_mul`；
- `innovationCovariance_mul_inv`；
- `gain_mul_innovationCovariance`；
- `josephCovariance_posSemidef`；
- `posteriorCovariance_eq_josephCovariance`；
- `prior_minus_posterior_eq_gain_covariance_gain_conjTranspose`；
- `prior_minus_posterior_posSemidef`；
- `posteriorCovariance_posSemidef`；
- `dofs_add_left`；
- `observable_iff_kernel_eq_zero`；
- `weightedNormalMatrix_posDef`；
- `informationMatrix_posDef`；
- `posteriorCovariance_eq_informationMatrix_inv`；
- `posteriorCovariance_posDef`；
- `posteriorCovariance_inv_eq_informationMatrix`；
- `retrievalError_decomposition`；
- `ForwardModel.observe_eq_linearized_add_remainder`；
- `ForwardModel.linearizedObserve_eq_offset_add`；
- `ForwardModel.linearizedObserve_eq_problem_predict_add_offset`；
- `ForwardModel.JacobianSpec.hasJacobianAt`；
- `ForwardModel.matrixDerivative_apply`；
- `ForwardModel.hasJacobianAt_of_hasFDerivAt_matrix`；
- `RadiativeTransfer.Layer.Valid.propagate_nonneg`；
- `RadiativeTransfer.Layer.Valid.propagate_le_of_le`；
- `RadiativeTransfer.propagateLayers_nonneg`；
- `RadiativeTransfer.propagateLayers_bounds`；
- `RadiativeTransfer.propagateTwo_eq`；
- `RadiativeTransfer.planckRadiance_pos`；
- `RadiativeTransfer.dopplerShift_zero`；
- `RadiativeTransfer.dopplerShift_expand`；
- `RadiativeTransfer.dopplerShift_pos`；
- `RadiativeTransfer.ChannelResponse.apply_nonneg`；
- `RadiativeTransfer.ChannelResponse.apply_le_of_le`；
- `RadiativeTransfer.ChannelResponse.apply_const`；
- `RadiativeTransfer.gaussianLineProfile_pos`；
- `RadiativeTransfer.gaussianLineProfile_center`；
- `RadiativeTransfer.gaussianLineProfile_symmetric`；
- `RadiativeTransfer.lineResponse_nonneg`；
- `RadiativeTransfer.centralDifference_eq_derivative_add_remainder`；
- `RadiativeTransfer.centralDifference_error_bound`；
- `NonlinearProblem.normalMatrix_mulVec_gaussNewtonStep`；
- `Problem.toNonlinear_residual_eq_innovation`；
- `Problem.toNonlinear_normalMatrix_eq_informationMatrix`；
- `NonlinearProblem.normalMatrix_posDef`；
- `NonlinearProblem.normalMatrix_isUnit`；
- `NonlinearProblem.quadraticForm_add`；
- `NonlinearProblem.quadraticSubproblem_add`；
- `NonlinearProblem.gaussNewtonUpdate_linearizedGradient_eq_zero`；
- `NonlinearProblem.residual_hasFDerivAt_of_hasJacobianAt`；
- `NonlinearProblem.gaussNewtonIterate_zero`；
- `NonlinearProblem.gaussNewtonIterate_succ`；
- `NonlinearProblem.gaussNewtonIterate_succ_sub`；
- `NonlinearProblem.gaussNewtonStep_eq_zero_iff`；
- `NonlinearProblem.gaussNewtonIterate_mem`；
- `NonlinearProblem.contractsTowardAlong_of_lipschitzOn`；
- `NonlinearProblem.gaussNewtonIterate_error_le`；
- `NonlinearProblem.gaussNewtonIterate_tendsto`；
- `NonlinearProblem.error_le_step_div_one_sub`；
- `NonlinearProblem.stoppedAt_error_le`；
- `NonlinearProblem.gaussNewtonIterate_step_le`；
- `NonlinearProblem.eventually_stoppedAt`。

另行执行的源代码扫描没有发现 `sorry`、`admit`、`sorryAx` 或未登记自定义 `axiom`。
