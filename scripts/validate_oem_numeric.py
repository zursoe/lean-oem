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


def main() -> None:
    scalar_case()
    rank_deficient_case()
    iteration_cases()
    local_contraction_case()
    discretization_error_case()
    print("一维精确 OEM 交叉验证：通过")
    print("秩亏二维 OEM 交叉验证：通过")
    print("Gauss–Newton 轨迹与停滞反例交叉验证：通过")
    print("平方模型局部收缩契约交叉验证：通过")
    print("中心差分离散化误差交叉验证：通过")
    print("所有独立有理数交叉验证：通过")


if __name__ == "__main__":
    main()
