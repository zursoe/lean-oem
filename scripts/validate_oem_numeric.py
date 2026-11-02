#!/usr/bin/env python3
"""用精确有理数独立核对 Lean OEM 核心例子。"""

from __future__ import annotations

from fractions import Fraction
from typing import Iterable, Sequence


F = Fraction
Matrix = list[list[Fraction]]
Vector = list[Fraction]


def matrix(rows: Iterable[Iterable[int | Fraction]]) -> Matrix:
    result = [[value if isinstance(value, Fraction) else F(value) for value in row]
              for row in rows]
    if not result or any(len(row) != len(result[0]) for row in result):
        raise ValueError("矩阵必须非空且每行长度一致")
    return result


def identity(size: int) -> Matrix:
    return [[F(int(i == j)) for j in range(size)] for i in range(size)]


def add(left: Matrix, right: Matrix) -> Matrix:
    return [[a + b for a, b in zip(row_a, row_b)]
            for row_a, row_b in zip(left, right)]


def subtract(left: Matrix, right: Matrix) -> Matrix:
    return [[a - b for a, b in zip(row_a, row_b)]
            for row_a, row_b in zip(left, right)]


def multiply(left: Matrix, right: Matrix) -> Matrix:
    if len(left[0]) != len(right):
        raise ValueError("矩阵维度不匹配")
    return [[sum(left[i][k] * right[k][j] for k in range(len(right)))
             for j in range(len(right[0]))]
            for i in range(len(left))]


def transpose(value: Matrix) -> Matrix:
    return [list(column) for column in zip(*value)]


def inverse(value: Matrix) -> Matrix:
    size = len(value)
    if any(len(row) != size for row in value):
        raise ValueError("只有方阵可以求逆")
    augmented = [row[:] + identity(size)[i] for i, row in enumerate(value)]
    for column in range(size):
        pivot = next((row for row in range(column, size)
                      if augmented[row][column] != 0), None)
        if pivot is None:
            raise ValueError("奇异矩阵没有逆")
        augmented[column], augmented[pivot] = augmented[pivot], augmented[column]
        scale = augmented[column][column]
        augmented[column] = [entry / scale for entry in augmented[column]]
        for row in range(size):
            if row == column:
                continue
            scale = augmented[row][column]
            augmented[row] = [a - scale * b
                              for a, b in zip(augmented[row], augmented[column])]
    return [row[size:] for row in augmented]


def matrix_vector(value: Matrix, vector: Vector) -> Vector:
    return [sum(entry * component for entry, component in zip(row, vector))
            for row in value]


def trace(value: Matrix) -> Fraction:
    return sum(value[i][i] for i in range(len(value)))


def assert_matrix(actual: Matrix, expected: Matrix, label: str) -> None:
    if actual != expected:
        raise AssertionError(f"{label} 不一致：实际 {actual}，期望 {expected}")


def assert_vector(actual: Vector, expected: Vector, label: str) -> None:
    if actual != expected:
        raise AssertionError(f"{label} 不一致：实际 {actual}，期望 {expected}")


def scalar_case() -> None:
    jacobian = matrix([[2]])
    prior = matrix([[3]])
    observation_error = matrix([[5]])
    innovation = add(multiply(multiply(jacobian, prior), transpose(jacobian)),
                     observation_error)
    gain = multiply(multiply(prior, transpose(jacobian)), inverse(innovation))
    averaging = multiply(gain, jacobian)
    posterior = subtract(
        prior,
        multiply(multiply(multiply(prior, transpose(jacobian)), inverse(innovation)),
                 multiply(jacobian, prior)),
    )
    joseph = add(
        multiply(
            multiply(subtract(identity(1), averaging), prior),
            transpose(subtract(identity(1), averaging)),
        ),
        multiply(multiply(gain, observation_error), transpose(gain)),
    )
    information = add(
        inverse(prior),
        multiply(multiply(transpose(jacobian), inverse(observation_error)), jacobian),
    )

    assert_matrix(innovation, matrix([[17]]), "一维创新协方差")
    assert_matrix(gain, matrix([[F(6, 17)]]), "一维增益")
    assert_matrix(averaging, matrix([[F(12, 17)]]), "一维 averaging kernel")
    assert_matrix(posterior, matrix([[F(15, 17)]]), "一维后验协方差")
    assert_matrix(joseph, posterior, "一维 Joseph 形式")
    assert_matrix(information, matrix([[F(17, 15)]]), "一维信息矩阵")
    assert_matrix(inverse(posterior), information, "一维后验逆矩阵")

    prior_mean = [F(0)]
    state = [F(4)]
    noise = [F(2)]
    observation = add_vector(matrix_vector(jacobian, state), noise)
    estimate = add_vector(
        prior_mean,
        matrix_vector(gain, subtract_vector(observation, matrix_vector(jacobian, prior_mean))),
    )
    error = subtract_vector(estimate, state)
    decomposition = add_vector(
        matrix_vector(subtract(identity(1), averaging), subtract_vector(prior_mean, state)),
        matrix_vector(gain, noise),
    )
    assert_vector(error, decomposition, "一维确定性误差分解")
    if trace(averaging) != F(12, 17):
        raise AssertionError("一维 DOFS 不一致")


def add_vector(left: Vector, right: Vector) -> Vector:
    return [a + b for a, b in zip(left, right)]


def subtract_vector(left: Vector, right: Vector) -> Vector:
    return [a - b for a, b in zip(left, right)]


def rank_deficient_case() -> None:
    jacobian = matrix([[1, 0]])
    prior = matrix([[1, 0], [0, 1]])
    observation_error = matrix([[1]])
    innovation = add(multiply(multiply(jacobian, prior), transpose(jacobian)),
                     observation_error)
    gain = multiply(multiply(prior, transpose(jacobian)), inverse(innovation))
    averaging = multiply(gain, jacobian)
    posterior = subtract(
        prior,
        multiply(multiply(multiply(prior, transpose(jacobian)), inverse(innovation)),
                 multiply(jacobian, prior)),
    )
    information = add(
        inverse(prior),
        multiply(multiply(transpose(jacobian), inverse(observation_error)), jacobian),
    )

    assert_matrix(innovation, matrix([[2]]), "秩亏创新协方差")
    assert_matrix(gain, matrix([[F(1, 2)], [0]]), "秩亏增益")
    assert_matrix(averaging, matrix([[F(1, 2), 0], [0, 0]]), "秩亏 averaging kernel")
    assert_matrix(posterior, matrix([[F(1, 2), 0], [0, 1]]), "秩亏后验协方差")
    assert_matrix(inverse(posterior), information, "秩亏后验逆矩阵")
    assert_vector(matrix_vector(jacobian, [F(0), F(1)]), [F(0)],
                  "秩亏不可观测方向")
    if posterior[1][1] != 1:
        raise AssertionError("秩亏例子的不可观测方向不应被收缩")


def prior_whitening_case() -> None:
    """复算不对称 averaging kernel 的先验白化与两个精确特征对。"""
    factor = matrix([[1, 1], [0, 1]])
    prior = matrix([[2, 1], [1, 1]])
    jacobian = matrix([[1, 0]])
    observation_error = identity(1)
    assert_matrix(multiply(factor, transpose(factor)), prior, "先验因子化")
    innovation = add(multiply(multiply(jacobian, prior), transpose(jacobian)),
                     observation_error)
    gain = multiply(multiply(prior, transpose(jacobian)), inverse(innovation))
    averaging = multiply(gain, jacobian)
    transformed_jacobian = multiply(jacobian, factor)
    whitened = multiply(multiply(transpose(transformed_jacobian), inverse(innovation)),
                        transformed_jacobian)
    assert_matrix(averaging, matrix([[F(2, 3), 0], [F(1, 3), 0]]),
                  "原坐标 averaging kernel")
    assert_matrix(whitened, matrix([[F(1, 3), F(1, 3)], [F(1, 3), F(1, 3)]]),
                  "白化 averaging kernel")
    assert_matrix(multiply(multiply(inverse(factor), averaging), factor), whitened,
                  "白化相似变换方向")
    if averaging == transpose(averaging):
        raise AssertionError("反例应给出不对称的原 averaging kernel")
    assert_matrix(whitened, transpose(whitened), "白化矩阵对称性")
    for eigenvalue, vector in ((F(0), [F(1), F(-1)]), (F(2, 3), [F(1), F(1)])):
        assert_vector(matrix_vector(whitened, vector),
                      [eigenvalue * component for component in vector], "白化特征对")
        original_vector = matrix_vector(factor, vector)
        assert_vector(matrix_vector(averaging, original_vector),
                      [eigenvalue * component for component in original_vector], "原坐标特征对")
    if trace(averaging) != F(2, 3) or trace(whitened) != F(2, 3):
        raise AssertionError("白化前后的 DOFS 必须等于两个特征值之和")


def iteration_cases() -> None:
    """精确复算状态增量，检查刷新、冻结和零步长停滞。"""
    def update(state: Fraction, prediction: Fraction, jacobian: Fraction) -> Fraction:
        normal = jacobian * jacobian + 1
        rhs = jacobian * (4 - prediction) - state
        return state + rhs / normal

    for initial in (F(-3), F(0), F(7, 2)):
        if update(initial, initial, F(1)) != 2:
            raise AssertionError("线性 OEM 没有一步恢复正则化解")

    refreshed = [F(1)]
    frozen = [F(1)]
    for _ in range(2):
        state = refreshed[-1]
        refreshed.append(update(state, state * state, 2 * state))
        state = frozen[-1]
        frozen.append(update(state, state * state, F(2)))
    assert_vector(refreshed, [F(1), F(2), F(32, 17)], "刷新 Jacobian 的轨迹")
    assert_vector(frozen, [F(1), F(2), F(8, 5)], "冻结 Jacobian 的轨迹")

    stalled = update(F(0), F(0), F(0))
    objective_zero = F(1, 2) * ((4 - 0**2) ** 2 + 0**2)
    objective_two = F(1, 2) * ((4 - 2**2) ** 2 + 2**2)
    if stalled != 0 or not objective_zero > objective_two:
        raise AssertionError("零步长非最优反例未复现")


def local_contraction_case() -> None:
    """独立复算标量平方模型的余项、正规缺陷和局部收缩界。"""
    state = F(1, 2)
    radius = F(1, 2)
    jacobian = 2 * state
    normal = jacobian * jacobian + 1
    remainder = (0 - state * state - jacobian * (0 - state))
    defect = jacobian * remainder
    update_error = defect / normal
    gamma = F(1)
    beta = F(1)
    rho = F(1)
    eta = beta * rho * radius
    q = gamma * eta

    if remainder != state * state:
        raise AssertionError("平方模型线性化余项不一致")
    if defect != 2 * state**3:
        raise AssertionError("平方模型正规缺陷不一致")
    if abs(jacobian) > beta:
        raise AssertionError("局部邻域内的加权 Jacobian 作用界不满足")
    if abs(defect) > eta * abs(state):
        raise AssertionError("平方模型正规缺陷界不满足")
    if abs(update_error) > q * abs(state):
        raise AssertionError("平方模型局部收缩界不满足")
    if not (0 <= q < 1):
        raise AssertionError("平方模型收缩因子不在收敛范围内")

    for _ in range(6):
        if abs(state) > radius:
            raise AssertionError("平方模型轨迹没有保持在局部邻域内")
        state = state + (-state * (2 * state * state + 1)) / (4 * state * state + 1)

    if abs(state) >= radius:
        raise AssertionError("平方模型迭代没有改善初始误差")


def discretization_error_case() -> None:
    """独立复算中心差分误差如何进入目标正规方程残差。"""
    step = F(1, 10)
    derivative = F(3)
    central = ((1 + step) ** 3 - (1 - step) ** 3) / (2 * step)
    jacobian_error = abs(central - derivative)
    target_residual = F(1, 10)
    normal_rhs_error = jacobian_error * target_residual

    if central != F(301, 100):
        raise AssertionError("三次函数中心差分值不一致")
    if jacobian_error != F(1, 100) or jacobian_error > step**2:
        raise AssertionError("中心差分 Jacobian 误差界不满足")
    if normal_rhs_error != F(1, 1000):
        raise AssertionError("离散化 Jacobian 对目标正规方程残差的影响不一致")


def forward_jacobian_joint_error_case() -> None:
    """独立复算前向误差和 Jacobian 误差共同形成的 OEM 更新误差底。"""
    exact_forward = F(1)
    approximate_forward = F(101, 100)
    observation = F(11, 10)
    target_residual = observation - exact_forward
    approximate_residual = observation - approximate_forward
    exact_jacobian = F(3)
    approximate_jacobian = F(301, 100)
    prior_weight = F(3, 10)
    jacobian_error = abs(approximate_jacobian - exact_jacobian)
    forward_error = abs(approximate_forward - exact_forward)
    beta = approximate_jacobian
    sigma = abs(target_residual)
    rhs_exact = exact_jacobian * target_residual - prior_weight
    rhs_approximate = approximate_jacobian * approximate_residual - prior_weight
    error_bound = jacobian_error * sigma + beta * forward_error
    approximate_normal = approximate_jacobian**2 + prior_weight
    update_error = abs(rhs_approximate) / approximate_normal

    if target_residual != F(1, 10) or approximate_residual != F(9, 100):
        raise AssertionError("联合误差 fixture 的残差不一致")
    if jacobian_error != F(1, 100) or forward_error != F(1, 100):
        raise AssertionError("联合误差 fixture 的两类误差不一致")
    if rhs_exact != 0 or abs(rhs_approximate) != F(291, 10000):
        raise AssertionError("联合误差 fixture 的正规右端不一致")
    if error_bound != F(311, 10000) or abs(rhs_approximate) > error_bound:
        raise AssertionError("联合误差正规右端界不满足")
    if approximate_normal != F(93601, 10000):
        raise AssertionError("联合误差 fixture 的正规矩阵不一致")
    if not update_error <= error_bound:
        raise AssertionError("联合误差更新误差底不满足")


def finite_layer_discretization_case() -> None:
    """独立复算两层有限层模型的正演和 Jacobian 离散化误差。"""
    exact_t1 = F(1, 2)
    exact_t2 = F(3, 4)
    approximate_t1 = F(3, 5)
    approximate_t2 = F(7, 10)
    incoming = F(2)
    state = F(1, 2)

    exact_coefficient = 1 - exact_t1 * exact_t2
    approximate_coefficient = 1 - approximate_t1 * approximate_t2
    exact_forward = exact_t2 * exact_t1 * incoming + exact_coefficient * state
    approximate_forward = (
        approximate_t2 * approximate_t1 * incoming
        + approximate_coefficient * state
    )
    first_error = abs(approximate_t1 - exact_t1)
    second_error = abs(approximate_t2 - exact_t2)
    coefficient_error = abs(approximate_coefficient - exact_coefficient)
    epsilon = first_error + second_error

    if exact_coefficient != F(5, 8):
        raise AssertionError("两层有限层精确 Jacobian 系数不一致")
    if approximate_coefficient != F(29, 50):
        raise AssertionError("两层有限层近似 Jacobian 系数不一致")
    if coefficient_error != F(9, 200) or coefficient_error > epsilon:
        raise AssertionError("两层有限层 Jacobian 误差界不满足")
    if exact_forward != F(17, 16) or approximate_forward != F(113, 100):
        raise AssertionError("两层有限层正演值不一致")

    forward_error = abs(approximate_forward - exact_forward)
    forward_bound = epsilon * (abs(incoming) + abs(state))
    if forward_error != F(27, 400) or forward_error > forward_bound:
        raise AssertionError("两层有限层正演误差界不满足")

    target_residual = F(1, 10)
    normal_rhs_error = coefficient_error * target_residual
    normal_rhs_bound = epsilon * target_residual
    if normal_rhs_error != F(9, 2000) or normal_rhs_error > normal_rhs_bound:
        raise AssertionError("两层有限层正规方程误差界不满足")

    approximate_normal = approximate_coefficient**2 + 1
    update_error = normal_rhs_error / approximate_normal
    if update_error > epsilon * target_residual:
        raise AssertionError("两层有限层更新误差底不满足")


def channel_discretization_case() -> None:
    """独立复算两频率通道响应与有限层谱值/Jacobian 的组合误差。"""
    exact_weights = [F(3, 4), F(1, 4)]
    approximate_weights = [F(7, 10), F(3, 10)]
    exact_values = [F(17, 16), F(49, 50)]
    approximate_values = [F(113, 100), F(41, 40)]
    exact_sensitivities = [F(5, 8), F(17, 25)]
    approximate_sensitivities = [F(29, 50), F(13, 20)]

    def apply(weights: Sequence[Fraction], values: Sequence[Fraction]) -> Fraction:
        return sum(weight * value for weight, value in zip(weights, values))

    weight_l1_error = sum(
        abs(approximate - exact)
        for approximate, exact in zip(approximate_weights, exact_weights)
    )
    value_error = [
        abs(approximate - exact)
        for approximate, exact in zip(approximate_values, exact_values)
    ]
    sensitivity_error = [
        abs(approximate - exact)
        for approximate, exact in zip(approximate_sensitivities, exact_sensitivities)
    ]

    exact_output = apply(exact_weights, exact_values)
    approximate_output = apply(approximate_weights, approximate_values)
    output_error = abs(approximate_output - exact_output)
    output_bound = F(6, 5) * weight_l1_error + F(7, 100)

    exact_jacobian = apply(exact_weights, exact_sensitivities)
    approximate_jacobian = apply(approximate_weights, approximate_sensitivities)
    jacobian_error = abs(approximate_jacobian - exact_jacobian)
    jacobian_bound = F(1) * weight_l1_error + F(1, 5)

    if weight_l1_error != F(1, 10):
        raise AssertionError("通道权重 L1 误差不一致")
    if max(value_error) > F(7, 100):
        raise AssertionError("有限层谱值误差预算不满足")
    if max(sensitivity_error) > F(1, 5):
        raise AssertionError("有限层 Jacobian 灵敏度误差预算不满足")
    if exact_output != F(1667, 1600) or approximate_output != F(2197, 2000):
        raise AssertionError("通道输出值不一致")
    if output_error != F(453, 8000) or output_error > output_bound:
        raise AssertionError("通道输出组合误差界不满足")
    if exact_jacobian != F(511, 800) or approximate_jacobian != F(601, 1000):
        raise AssertionError("通道 Jacobian 系数不一致")
    if jacobian_error != F(151, 4000) or jacobian_error > jacobian_bound:
        raise AssertionError("通道 Jacobian 组合误差界不满足")


def channel_step_order_case() -> None:
    """独立复算中心有限差分的 h² 误差如何沿通道 Jacobian 传播。"""
    step = F(1, 10)
    central = ((1 + step) ** 3 - (1 - step) ** 3) / (2 * step)
    exact_sensitivities = [F(3), F(3)]
    approximate_sensitivities = [central, central]
    weights = [F(3, 4), F(1, 4)]

    exact_channel = sum(
        weight * sensitivity
        for weight, sensitivity in zip(weights, exact_sensitivities)
    )
    approximate_channel = sum(
        weight * sensitivity
        for weight, sensitivity in zip(weights, approximate_sensitivities)
    )
    error = abs(approximate_channel - exact_channel)
    bound = F(1) * step**2

    if central != F(301, 100):
        raise AssertionError("通道中心差分值不一致")
    if error != F(1, 100) or error > bound:
        raise AssertionError("通道中心差分 h² 误差界不满足")


def main() -> None:
    scalar_case()
    rank_deficient_case()
    prior_whitening_case()
    iteration_cases()
    local_contraction_case()
    discretization_error_case()
    forward_jacobian_joint_error_case()
    finite_layer_discretization_case()
    channel_discretization_case()
    channel_step_order_case()
    print("一维精确 OEM 交叉验证：通过")
    print("秩亏二维 OEM 交叉验证：通过")
    print("先验白化、相似变换和精确特征对交叉验证：通过")
    print("Gauss–Newton 轨迹与停滞反例交叉验证：通过")
    print("平方模型局部收缩契约交叉验证：通过")
    print("中心差分离散化误差交叉验证：通过")
    print("前向/Jacobian 联合误差交叉验证：通过")
    print("两层有限层离散化误差交叉验证：通过")
    print("通道响应离散化误差交叉验证：通过")
    print("通道中心差分 h² 误差交叉验证：通过")
    print("所有独立有理数交叉验证：通过")


if __name__ == "__main__":
    main()
