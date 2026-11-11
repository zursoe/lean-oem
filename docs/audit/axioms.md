# 公理审计记录

## 语义边界回归登记（2026-11-11）

本批基于 `88e65c5`，保留原有 195 项 Core/Physics 登记，另导入
[SemanticBoundaries.lean](../../LeanOEM/Tests/SemanticBoundaries.lean)，为五项具名回归增加
`#print axioms`。当前 [Axioms.lean](../../LeanOEM/Tests/Axioms.lean) 共 200 项登记；
Core/Physics 仍为 192 个显式公开定理及 3 个因子构造，回归结果不计作稳定核心 API。

完整构建后执行 `bash scripts/run_audit.sh --no-build`，审计通过。逐项对照登记核实
200/200 项输出，无重复或缺失；全部依赖的并集仍只有 `propext`、`Classical.choice` 和
`Quot.sound`。五项回归各自也只使用这三项基础公理。占位证明扫描和编译产物跟踪检查通过。
本次为基于 `88e65c5` 的本地工作区验证，构建方式及日志见
[构建记录](build-report.md) 的最新条目。

## 首次发布候选复核（2026-11-11）

本轮从 `9bb9f25` 开始，补齐 22 个已有公开辅助定理和 `PriorSqrtFactor.toSupportFactor`
构造的显式审计登记。当时 [Axioms.lean](../../LeanOEM/Tests/Axioms.lean) 共 195 项，覆盖
Core/Physics 中全部 192 个显式公开定理声明及 3 个因子构造。

本地执行 `bash scripts/run_audit.sh --no-build` 成功；逐项核对 195 项输出完整，公理依赖集合
仅为 `propext`、`Classical.choice` 和 `Quot.sound`，部分辅助定理不依赖任何公理。
本轮数学定义和证明项未改动。修正后候选 `ff3ca1d` 在干净 worktree 中重复审计，也完整输出
195 项，依赖集合相同。干净构建与复核结果另记于
[构建记录](build-report.md) 的本轮条目。

## 历史非零谱批次

审计日期：2026-11-07

审计基线：代码提交 `52e36b1`；本批新增构造和公开定理均已纳入。

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
- `dofs_nonneg_of_averagingKernel_posSemidef`；
- `dofs_le_dim_of_complement_posSemidef`；
- `dofs_bounds_of_averagingKernel_posSemidef`；
- `eigenvalues_bounds_of_posSemidef`；
- `trace_mul_nonneg_of_posSemidef`；
- `Problem.dofs_nonneg_of_posDef`；
- `Problem.dofs_le_dim_of_posDef`；
- `Problem.dofs_bounds_of_posDef`；
- `Problem.PriorFactor.ofPosDef`（含因子可逆性和协方差等式的构造）；
- `Problem.PriorFactor.prior_posSemidef`；
- `Problem.PriorFactor.prior_posDef`；
- `Problem.PriorFactor.averagingKernel_mul_factor`；
- `Problem.PriorFactor.whitenedAveragingKernel_eq_conjugate`；
- `Problem.PriorFactor.charpoly_eq`；
- `Problem.PriorFactor.whitenedAveragingKernel_posSemidef`；
- `Problem.PriorFactor.whitenedAveragingKernel_posDef_of_observable`；
- `Problem.PriorFactor.one_sub_whitenedAveragingKernel_posDef`；
- `Problem.PriorFactor.eigenvalues_bounds`；
- `Problem.PriorFactor.eigenvalues_lt_one`；
- `Problem.PriorFactor.eigenvalues_pos_of_observable`；
- `Problem.PriorFactor.whitenedAveragingKernel_rank_le`；
- `Problem.PriorFactor.whitenedAveragingKernel_rank_eq`；
- `Problem.PriorFactor.dofs_le_jacobian_rank`；
- `Problem.PriorFactor.dofs_lt_state_dim`；
- `Problem.PriorFactor.whitenedAveragingKernel_mulVec_eq_zero_iff`；
- `Problem.PriorFactor.whitenedAveragingKernel_mulVec_eq_zero_iff_jacobian`；
- `Problem.PriorFactor.whitenedAveragingKernel_mulVec_injective_iff_observable`；
- `Problem.PriorFactor.whitenedAveragingKernel_zero_mem_spectrum_iff_not_observable`；
- `Problem.PriorFactor.spectrum_eq_range_eigenvalues`；
- `Problem.PriorFactor.charpoly_splits`；
- `Problem.PriorFactor.dofs_eq_sum_eigenvalues`；
- `Problem.averagingKernel_spectrum_subset_Icc`；
- `Problem.averagingKernel_charpoly_splits`；
- `Problem.SupportFactor.prior_posSemidef`；
- `Problem.PriorSqrtFactor.ofPosSemidef`；
- `Problem.PriorSqrtFactor.mem_support_iff`；
- `Problem.PriorSqrtFactor.prior_posSemidef`；
- `Problem.PriorSqrtFactor.support_finrank_eq_priorCovariance_rank`；
- `Problem.PriorSqrtFactor.euclideanSupport_finrank_eq_support`；
- `Problem.PriorSqrtFactor.supportBasisMatrix_conjTranspose_mul_self`；
- `Problem.PriorSqrtFactor.supportFactorMatrix_gram_eq`；
- `Problem.PriorSqrtFactor.supportFactorMatrix_injective`；
- `Problem.PriorSqrtFactor.toSupportFactor_covariance_eq`；
- `Problem.PriorSqrtFactor.toSupportFactor_range_eq_support`；
- `Problem.SupportFactor.averagingKernel_charpoly_eq_support_factor`；
- `Problem.SupportFactor.averagingKernel_nonzeroSpectrum_eq_support_factor`；
- `Problem.SupportFactor.averagingKernel_zero_rootMultiplicity_eq`；
- `Problem.SupportFactor.averagingKernel_zero_rootMultiplicity_eq_dim_sub_support_of_observableOnSupport`；
- `Problem.PriorSqrtFactor.supportBasisVector_linearIndependent`；
- `Problem.PriorSqrtFactor.supportBasisMatrix_injective`；
- `Problem.PriorSqrtFactor.supportBasisMatrix_range_eq_support`；
- `Problem.PriorSqrtFactor.supportBasisMatrix_rank_eq_support_finrank`；
- `Problem.SupportFactor.matrix_rank_eq_support_dim`；
- `Problem.SupportFactor.priorCovariance_rank_eq_support_dim`；
- `Problem.SupportFactor.whitenedAveragingKernel_posSemidef`；
- `Problem.SupportFactor.one_sub_whitenedAveragingKernel_posDef`；
- `Problem.SupportFactor.whitenedAveragingKernel_posDef_of_observableOnSupport`；
- `Problem.SupportFactor.eigenvalues_bounds`；
- `Problem.SupportFactor.eigenvalues_lt_one`；
- `Problem.SupportFactor.eigenvalues_pos_of_observableOnSupport`；
- `Problem.SupportFactor.whitenedAveragingKernel_zero_mem_spectrum_iff_not_observableOnSupport`；
- `Problem.SupportFactor.whitenedAveragingKernel_rank_eq`；
- `Problem.SupportFactor.dofs_eq_support_trace`；
- `Problem.SupportFactor.dofs_eq_sum_eigenvalues`；
- `Problem.SupportFactor.dofs_le_support_dim`；
- `Problem.SupportFactor.dofs_lt_support_dim`；
- `Problem.SupportFactor.dofs_le_support_jacobian_rank`；
- `Problem.SupportFactor.dofs_le_priorCovariance_rank`；
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
- `NonlinearProblem.gaussNewtonIterate_error_le_with_floor`；
- `NonlinearProblem.gaussNewtonIterate_error_le_with_floor_bound`；
- `NonlinearProblem.gaussNewtonIterate_tendsto`；
- `NonlinearProblem.error_le_step_div_one_sub`；
- `NonlinearProblem.stoppedAt_error_le`；
- `NonlinearProblem.gaussNewtonIterate_step_le`；
- `NonlinearProblem.eventually_stoppedAt`；
- `NonlinearProblem.gaussNewtonUpdate_sub_target_eq_inverse_normalDefect`；
- `NonlinearProblem.gaussNewtonUpdate_error_le_of_inverse_and_defect`；
- `NonlinearProblem.normalDefect_eq_weighted_linearizationRemainder`；
- `NonlinearProblem.normalDefectBound_of_quadraticRemainder`；
- `NonlinearProblem.normalDefect_eq_jacobianVariation_add_remainder_add_stationarity`；
- `NonlinearProblem.normalDefect_eq_jacobianVariation_add_remainder_of_stationary`；
- `NonlinearProblem.normalDefectBound_of_stationary_target`；
- `NonlinearProblem.contractsTowardAlong_of_inverse_and_defect`。

P12 新增公开定理：

- `NonlinearProblem.normalDefect_additive_bound_of_stationarity_residual`；
- `NonlinearProblem.gaussNewtonUpdate_error_le_of_inverse_and_additive_defect`；
- `NonlinearProblem.weightedJacobianActionBound_of_error`；
- `NonlinearProblem.normalRhs_norm_le_of_weightedJacobianError`。

P12-C-3 新增公开定理：

- `NonlinearProblem.normalRhsFor_difference_eq`；
- `NonlinearProblem.normalRhsFor_difference_norm_le_of_forward_and_jacobian_error`；
- `NonlinearProblem.normalRhsFor_norm_le_of_forward_and_jacobian_error`；
- `NonlinearProblem.gaussNewtonUpdate_error_le_of_forward_and_jacobian_error`。

P12-C-4 新增公开定理：

- `RadiativeTransfer.twoLayerState_hasJacobianAt`。

P12-B 新增公开定理：

- `RadiativeTransfer.twoLayerSourceCoefficient_eq_one_sub_product`；
- `RadiativeTransfer.twoLayerSourceObserve_eq_propagateTwo`；
- `RadiativeTransfer.twoLayerSource_hasJacobianAt`；
- `RadiativeTransfer.transmissivity_product_error_le`；
- `RadiativeTransfer.twoLayerSourceJacobian_coefficient_error_le`；
- `RadiativeTransfer.twoLayerSource_weightedJacobianErrorBound_unit`；
- `RadiativeTransfer.twoLayerSource_weightedJacobianErrorBound_of_unitWeight`；
- `RadiativeTransfer.twoLayerSource_forward_error_le`。

P12-C 新增公开定理：

- `RadiativeTransfer.ChannelResponse.weightL1Error_self`；
- `RadiativeTransfer.ChannelResponse.apply_error_le_of_weightL1`；
- `RadiativeTransfer.ChannelResponse.apply_error_le_of_value_error`；
- `RadiativeTransfer.ChannelResponse.apply_error_le_of_weight_and_value`；
- `RadiativeTransfer.channelJacobian_coefficient_error_le`；
- `RadiativeTransfer.channelJacobian_weightedErrorBound_unit`；
- `RadiativeTransfer.channelJacobian_weightedErrorBound_of_unitWeight`。

P12-C-2 新增公开定理：

- `RadiativeTransfer.ChannelResponse.apply_error_le_of_valueStepError`；
- `RadiativeTransfer.channelJacobian_coefficient_error_le_of_valueStepError`；
- `RadiativeTransfer.channelJacobian_weightedErrorBound_of_valueStepError`。

另行执行的源代码扫描没有发现 `sorry`、`admit`、`sorryAx` 或未登记自定义 `axiom`。
