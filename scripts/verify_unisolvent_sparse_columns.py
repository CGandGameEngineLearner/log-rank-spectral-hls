#!/usr/bin/env python3
"""Exact finite audits for unisolvent sparse-column Log-Rank transfer."""

from __future__ import annotations

from itertools import combinations
from itertools import product
import math
import random


PRIME = 1_000_000_007


def rank_mod(matrix: list[list[int]], prime: int = PRIME) -> int:
    if not matrix:
        return 0
    a = [[x % prime for x in row] for row in matrix]
    rows, cols = len(a), len(a[0])
    rank = 0
    for col in range(cols):
        pivot = next((i for i in range(rank, rows) if a[i][col]), None)
        if pivot is None:
            continue
        a[rank], a[pivot] = a[pivot], a[rank]
        inv = pow(a[rank][col], prime - 2, prime)
        a[rank] = [(x * inv) % prime for x in a[rank]]
        for i in range(rows):
            if i != rank and a[i][col]:
                factor = a[i][col]
                a[i] = [
                    (x - factor * y) % prime for x, y in zip(a[i], a[rank])
                ]
        rank += 1
        if rank == rows:
            break
    return rank


def determinant_bareiss(matrix: list[list[int]]) -> int:
    n = len(matrix)
    if n == 0:
        return 1
    a = [row[:] for row in matrix]
    sign = 1
    previous = 1
    for k in range(n - 1):
        if a[k][k] == 0:
            pivot = next((i for i in range(k + 1, n) if a[i][k]), None)
            if pivot is None:
                return 0
            a[k], a[pivot] = a[pivot], a[k]
            sign = -sign
        pivot_value = a[k][k]
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                a[i][j] = (a[i][j] * pivot_value - a[i][k] * a[k][j]) // previous
        previous = pivot_value
    return sign * a[n - 1][n - 1]


def layer(n: int, k: int) -> list[int]:
    return [sum(1 << i for i in comb) for comb in combinations(range(n), k)]


def monomials(n: int, degree: int) -> list[int]:
    return [
        sum(1 << i for i in comb)
        for size in range(degree + 1)
        for comb in combinations(range(n), size)
    ]


def evaluation_matrix(points: list[int], features: list[int]) -> list[list[int]]:
    return [[int((x & feature) == feature) for feature in features] for x in points]


def check_slice_degree_dimension() -> tuple[int, int]:
    parameter_checks = 0
    evaluated_entries = 0
    for n in range(4, 11):
        for k in range(1, n):
            points = layer(n, k)
            for degree in range(min(3, k, n - k) + 1):
                features = monomials(n, degree)
                matrix = evaluation_matrix(points, features)
                expected = math.comb(n, degree)
                assert rank_mod(matrix) == expected
                parameter_checks += 1
                evaluated_entries += len(points) * len(features)
    return parameter_checks, evaluated_entries


def check_random_sparse_unisolvence() -> tuple[int, int, int]:
    # A middle layer where the matrix-Chernoff sample bound is genuinely
    # smaller than the ambient layer for the degree-one space.
    n, k, degree = 14, 7, 1
    points = layer(n, k)
    features = monomials(n, degree)
    dimension = math.comb(n, degree)
    delta = 1e-4
    sample_size = math.ceil(8 * dimension * math.log(dimension / delta))
    assert sample_size < len(points)

    rng = random.Random(20260826)
    trials = 25
    for _ in range(trials):
        sample = rng.sample(points, sample_size)
        assert rank_mod(evaluation_matrix(sample, features)) == dimension
    return trials, sample_size, len(points)


def check_exact_minimal_unisolvent_sets() -> int:
    # Greedily select evaluation rows increasing the exact modular rank.  The
    # resulting set has precisely dim(V) points and is unisolvent over R.
    checks = 0
    for n, k, degree in ((6, 3, 1), (7, 3, 2), (8, 4, 2), (9, 4, 2)):
        points = layer(n, k)
        features = monomials(n, degree)
        dimension = math.comb(n, degree)
        selected: list[list[int]] = []
        current_rank = 0
        for row in evaluation_matrix(points, features):
            candidate_rank = rank_mod(selected + [row])
            if candidate_rank > current_rank:
                selected.append(row)
                current_rank = candidate_rank
            if current_rank == dimension:
                break
        assert len(selected) == dimension
        assert rank_mod(selected) == dimension
        checks += 1
    return checks


def check_projection_dpp_cauchy_binet() -> tuple[int, int, int]:
    # Degree-one functions on the 2-subsets of [5] have dimension five and
    # are spanned by the five coordinate indicators.
    n, k = 5, 2
    points = layer(n, k)
    matrix = [[int(x >> i & 1) for i in range(n)] for x in points]
    gram = [
        [sum(row[i] * row[j] for row in matrix) for j in range(n)]
        for i in range(n)
    ]
    normalization = determinant_bareiss(gram)
    volume_sum = 0
    support_size = 0
    subsets_checked = 0
    for chosen in combinations(range(len(points)), n):
        square = [matrix[i] for i in chosen]
        det = determinant_bareiss(square)
        volume_sum += det * det
        if det:
            support_size += 1
            assert rank_mod(square) == n
        subsets_checked += 1
    assert volume_sum == normalization
    return subsets_checked, support_size, normalization


def product_points(alphabets: tuple[int, ...]) -> list[tuple[int, ...]]:
    return list(product(*(range(m) for m in alphabets)))


def product_features(
    alphabets: tuple[int, ...], degree: int
) -> list[tuple[tuple[int, int], ...]]:
    features: list[tuple[tuple[int, int], ...]] = []
    for size in range(degree + 1):
        for coordinates in combinations(range(len(alphabets)), size):
            for values in product(*(range(1, alphabets[i]) for i in coordinates)):
                features.append(tuple(zip(coordinates, values)))
    return features


def product_evaluation_matrix(
    points: list[tuple[int, ...]],
    features: list[tuple[tuple[int, int], ...]],
) -> list[list[int]]:
    return [
        [int(all(x[i] == value for i, value in feature)) for feature in features]
        for x in points
    ]


def check_product_degree_dimension_and_dpp() -> tuple[int, int, int, int]:
    dimension_checks = 0
    evaluated_entries = 0
    for alphabets in ((2, 2, 2), (2, 3, 2), (3, 3, 2), (2, 3, 4)):
        points = product_points(alphabets)
        for degree in range(len(alphabets) + 1):
            features = product_features(alphabets, degree)
            matrix = product_evaluation_matrix(points, features)
            expected = sum(
                math.prod(alphabets[i] - 1 for i in chosen)
                for size in range(degree + 1)
                for chosen in combinations(range(len(alphabets)), size)
            )
            assert len(features) == expected
            assert rank_mod(matrix) == expected
            dimension_checks += 1
            evaluated_entries += len(points) * len(features)

    # Exact volume normalization for degree one on [3]^2: dimension 5,
    # ambient size 9, and 126 candidate minimal subsets.
    alphabets = (3, 3)
    points = product_points(alphabets)
    features = product_features(alphabets, 1)
    matrix = product_evaluation_matrix(points, features)
    dimension = len(features)
    gram = [
        [sum(row[i] * row[j] for row in matrix) for j in range(dimension)]
        for i in range(dimension)
    ]
    normalization = determinant_bareiss(gram)
    volume_sum = 0
    positive = 0
    candidates = 0
    for chosen in combinations(range(len(points)), dimension):
        square = [matrix[i] for i in chosen]
        det = determinant_bareiss(square)
        volume_sum += det * det
        positive += int(det != 0)
        candidates += 1
    assert volume_sum == normalization
    return dimension_checks, evaluated_entries, candidates, positive


def greedy_unisolvent_point_indices(
    matrix: list[list[int]], dimension: int
) -> list[int]:
    selected_rows: list[list[int]] = []
    selected_indices: list[int] = []
    current_rank = 0
    for index, row in enumerate(matrix):
        candidate_rank = rank_mod(selected_rows + [row])
        if candidate_rank > current_rank:
            selected_rows.append(row)
            selected_indices.append(index)
            current_rank = candidate_rank
        if current_rank == dimension:
            break
    assert current_rank == dimension
    return selected_indices


def check_sparse_booleanity_certification() -> tuple[int, int, int]:
    # J(6,3), degree <= 2: ambient size 20, dimension C(6,2)=15.
    n, k, degree = 6, 3, 2
    points = layer(n, k)
    features = monomials(n, degree)
    evaluation = evaluation_matrix(points, features)
    dimension = math.comb(n, degree)
    selected = greedy_unisolvent_point_indices(evaluation, dimension)
    sparse_points = [points[i] for i in selected]
    assert len(sparse_points) == dimension

    qualifying_sparse_rows = 0
    full_row_checks = 0
    for row_set in range(1 << n):
        sparse_values = [int((row_set & point).bit_count()) for point in sparse_points]
        if max(sparse_values) - min(sparse_values) > 1:
            continue
        qualifying_sparse_rows += 1
        full_values = [int((row_set & point).bit_count()) for point in points]
        # Degree-two unisolvence must promote sparse adjacent-two-valuedness
        # to the complete Johnson slice.
        assert max(full_values) - min(full_values) <= 1
        assert set(full_values).issubset(
            {min(sparse_values), min(sparse_values) + 1}
        )
        full_row_checks += len(points)
    return len(sparse_points), qualifying_sparse_rows, full_row_checks


def explicit_quadratic_cross(n: int, k: int) -> list[int]:
    inside = set(range(k))
    outside = set(range(k, n))
    fixed_inside = set(sorted(inside)[:2])
    fixed_outside = set(sorted(outside)[:2])
    family: set[int] = set()

    def encode(subset: set[int]) -> int:
        return sum(1 << i for i in subset)

    family.add(encode(inside))
    for i in inside:
        for a in outside:
            family.add(encode((inside - {i}) | {a}))
    for i, j in combinations(inside, 2):
        family.add(encode((inside - {i, j}) | fixed_outside))
    for a, b in combinations(outside, 2):
        family.add(encode((inside - fixed_inside) | {a, b}))
    return sorted(family)


def check_explicit_quadratic_cross() -> tuple[int, int]:
    parameter_checks = 0
    matrix_entries = 0
    for n in range(4, 16):
        pairs = [sum(1 << i for i in pair) for pair in combinations(range(n), 2)]
        dimension = math.comb(n, 2)
        for k in range(2, n - 1):
            family = explicit_quadratic_cross(n, k)
            assert len(family) == dimension
            matrix = evaluation_matrix(family, pairs)
            assert rank_mod(matrix) == dimension
            parameter_checks += 1
            matrix_entries += dimension * dimension
    return parameter_checks, matrix_entries


def explicit_linear_anchor(n: int, k: int) -> list[int]:
    inside = set(range(k))
    outside = set(range(k, n))
    fixed_inside = min(inside)
    fixed_outside = min(outside)

    def encode(subset: set[int]) -> int:
        return sum(1 << i for i in subset)

    family = {encode(inside)}
    for a in outside:
        family.add(encode((inside - {fixed_inside}) | {a}))
    for i in inside - {fixed_inside}:
        family.add(encode((inside - {i}) | {fixed_outside}))
    return sorted(family)


def check_linear_anchor_and_four_fiber() -> tuple[int, int, int, int]:
    anchor_parameters = 0
    fiber_parameters = 0
    row_pair_checks = 0
    incidence_entries = 0
    for n in range(4, 11):
        for k in range(2, n - 1):
            points = layer(n, k)
            anchor = explicit_linear_anchor(n, k)
            coordinate_features = [1 << i for i in range(n)]
            assert len(anchor) == n
            assert rank_mod(evaluation_matrix(anchor, coordinate_features)) == n
            anchor_parameters += 1
            incidence_entries += n * n

            excluded_lower_bound = math.comb(n - 4, k - 2)
            for row_set in range(1 << n):
                size = row_set.bit_count()
                if size < 2 or n - size < 2:
                    continue
                values = [(row_set & point).bit_count() for point in points]
                for a in range(-1, k + 1):
                    bad = sum(value in (a, a + 1) for value in values)
                    assert len(points) - bad >= excluded_lower_bound
                    row_pair_checks += 1
            fiber_parameters += 1
    return anchor_parameters, fiber_parameters, row_pair_checks, incidence_entries


def check_random_linear_detector() -> tuple[int, int, int, int]:
    n, k = 12, 6
    points = layer(n, k)
    gamma = math.comb(n - 4, k - 2) / math.comb(n, k)
    xi = 2 * (min(k, n - k) / n) ** 2 / 5
    theta = max(gamma, xi)
    delta = 1e-6
    sample_size = math.ceil(
        (n * math.log(2) + math.log(n + 2) + math.log(1 / delta)) / theta
    )
    assert sample_size < len(points)
    rng = random.Random(20260828)
    trials = 10
    tested_rows = 0
    for _ in range(trials):
        sample = rng.sample(points, sample_size)
        for row_set in range(1 << n):
            size = row_set.bit_count()
            if size < 2 or n - size < 2:
                continue
            values = [(row_set & point).bit_count() for point in sample]
            assert max(values) - min(values) >= 2
            tested_rows += 1
    return trials, sample_size, len(points), tested_rows


def check_robust_linear_detector() -> tuple[int, int, int, int, int]:
    n, k = 14, 7
    points = layer(n, k)
    gamma = math.comb(n - 4, k - 2) / math.comb(n, k)
    xi = 2 * (min(k, n - k) / n) ** 2 / 5
    theta = max(gamma, xi)
    delta = 1e-6
    sample_size = math.ceil(
        8
        * (n * math.log(2) + math.log(n + 2) + math.log(1 / delta))
        / theta
    )
    assert sample_size < len(points)
    rng = random.Random(20260829)
    sample = rng.sample(points, sample_size)
    target = math.floor(theta * sample_size / 2)
    minimum_witnesses = sample_size
    tested_rows = 0
    for row_set in range(1 << n):
        size = row_set.bit_count()
        if size < 2 or n - size < 2:
            continue
        histogram = [0] * (k + 1)
        for point in sample:
            histogram[(row_set & point).bit_count()] += 1
        most_in_consecutive_pair = max(
            histogram[a] + histogram[a + 1] for a in range(k)
        )
        witnesses = sample_size - most_in_consecutive_pair
        minimum_witnesses = min(minimum_witnesses, witnesses)
        assert witnesses >= target
        tested_rows += 1
    deletion_budget = math.floor(theta * sample_size / 4)
    assert minimum_witnesses > deletion_budget
    return sample_size, len(points), tested_rows, minimum_witnesses, deletion_budget


def check_affine_support_gap() -> tuple[int, int, int]:
    """Exhaust the exact support bound on a dense finite coefficient grid."""
    parameter_checks = 0
    affine_forms = 0
    evaluated_entries = 0
    for n in range(4, 9):
        for k in range(2, n - 1):
            points = layer(n, k)
            lower_bound = math.comb(n - 2, k - 1)
            for weights in product((-1, 0, 1), repeat=n):
                for constant in range(-2, 3):
                    values = [
                        constant
                        + sum(weights[i] for i in range(n) if point >> i & 1)
                        for point in points
                    ]
                    support = sum(value != 0 for value in values)
                    if support:
                        assert support >= lower_bound
                    affine_forms += 1
                    evaluated_entries += len(points)
            parameter_checks += 1
    return parameter_checks, affine_forms, evaluated_entries


def check_quadratic_hypergeometric_gap() -> tuple[
    int, int, int, tuple[int, int, int, int, int, int]
]:
    """Exhaust the claimed quadratic two-consecutive-value escape bound."""
    parameter_checks = 0
    interval_checks = 0
    ambient_counts = 0
    sharpest = (1 << 60, 1, 0, 0, 0, 0)
    equality_cases: list[tuple[int, int, int, int]] = []
    for n in range(4, 81):
        for k in range(2, n - 1):
            denominator = math.comb(n, k)
            short_side = min(k, n - k)
            for marked in range(2, n - 1):
                lower = max(0, k - (n - marked))
                upper = min(k, marked)
                masses = {
                    value: math.comb(marked, value)
                    * math.comb(n - marked, k - value)
                    for value in range(lower, upper + 1)
                }
                for a in range(lower - 1, upper + 1):
                    outside = denominator - masses.get(a, 0) - masses.get(a + 1, 0)
                    assert outside * 16 * n * n >= denominator * short_side * short_side
                    # Track the exact numerator/denominator of the smallest
                    # ratio to the natural quadratic scale.
                    ratio_num = outside * n * n
                    ratio_den = denominator * short_side * short_side
                    if 5 * ratio_num == 2 * ratio_den:
                        equality_cases.append((n, k, marked, a))
                    if ratio_num * sharpest[1] < sharpest[0] * ratio_den:
                        sharpest = (ratio_num, ratio_den, n, k, marked, a)
                    interval_checks += 1
                    ambient_counts += denominator
                parameter_checks += 1
    assert equality_cases == [(6, 3, 3, 1)]
    return parameter_checks, interval_checks, ambient_counts, sharpest


def check_six_coordinate_sharp_gap() -> tuple[int, int, list[tuple[int, int]]]:
    """Verify the global six-coordinate certificate and its unique equality."""
    local_witnesses: list[int] = []
    choose = lambda upper, lower: math.comb(upper, lower) if 0 <= lower <= upper else 0
    for trace_size in range(7):
        masses = [
            math.comb(3, marked) * math.comb(3, trace_size - marked)
            for marked in range(4)
            if 0 <= trace_size - marked <= 3
        ]
        total = math.comb(6, trace_size)
        captured = max(
            (masses[index] if index < len(masses) else 0)
            + (masses[index + 1] if index + 1 < len(masses) else 0)
            for index in range(len(masses))
        )
        local_witnesses.append(total - captured)
    assert local_witnesses == [0, 0, 3, 2, 3, 0, 0]

    parameter_checks = 0
    cleared_checks = 0
    equality_cases: list[tuple[int, int]] = []
    for n in range(6, 501):
        for k in range(2, n - 1):
            short_side = min(k, n - k)
            denominator = math.comb(n, k)
            certificate_numerator = (
                3 * choose(n - 6, k - 2)
                + 2 * choose(n - 6, k - 3)
                + 3 * choose(n - 6, k - 4)
            )
            left = 5 * certificate_numerator * n * n
            right = 2 * denominator * short_side * short_side
            assert left >= right
            if left == right:
                equality_cases.append((n, k))
            parameter_checks += 1
            cleared_checks += left.bit_length() + right.bit_length()

    assert equality_cases == [(6, 3)]
    return parameter_checks, cleared_checks, equality_cases



def sylvester_hadamard(exponent: int) -> list[list[int]]:
    matrix = [[1]]
    for _ in range(exponent):
        matrix = [
            row + row for row in matrix
        ] + [
            row + [-value for value in row] for row in matrix
        ]
    return matrix


def explicit_sylvester_design(exponent: int) -> list[int]:
    hadamard = sylvester_hadamard(exponent)
    order = 1 << exponent
    assert len(hadamard) == order
    assert all(value == 1 for value in hadamard[0])
    assert all(row[0] == 1 for row in hadamard)
    return [
        sum(1 << (column - 1) for column in range(1, order) if row[column] == 1)
        for row in hadamard[1:]
    ]


def check_sylvester_hadamard_designs() -> tuple[int, int, int, int]:
    design_parameters = 0
    pair_checks = 0
    incidence_entries = 0
    exhaustive_rows = 0
    for exponent in range(3, 9):
        blocks = explicit_sylvester_design(exponent)
        n = (1 << exponent) - 1
        u = 1 << (exponent - 2)
        k = 2 * u - 1
        lambda_two = u - 1
        assert len(blocks) == n
        assert len(set(blocks)) == n
        assert all(block.bit_count() == k for block in blocks)
        assert 8 * k * (n - k) * (n - 2) > n * n * (n - 1)

        for first, second in combinations(blocks, 2):
            assert (first & second).bit_count() == lambda_two
            pair_checks += 1

        coordinate_counts = [
            sum(block >> coordinate & 1 for block in blocks)
            for coordinate in range(n)
        ]
        assert coordinate_counts == [k] * n
        for i, j in combinations(range(n), 2):
            assert sum(
                (block >> i & 1) * (block >> j & 1) for block in blocks
            ) == lambda_two
            pair_checks += 1

        incidence = [
            [int(block >> coordinate & 1) for coordinate in range(n)]
            for block in blocks
        ]
        assert rank_mod(incidence) == n
        incidence_entries += n * n
        design_parameters += 1

        if exponent <= 4:
            for row_set in range(1 << n):
                values = [(row_set & block).bit_count() for block in blocks]
                if max(values) - min(values) <= 1:
                    size = row_set.bit_count()
                    assert size <= 1 or n - size <= 1
                exhaustive_rows += 1

    return design_parameters, pair_checks, incidence_entries, exhaustive_rows



def main() -> None:
    parameters, entries = check_slice_degree_dimension()
    trials, sample_size, ambient_size = check_random_sparse_unisolvence()
    minimal_checks = check_exact_minimal_unisolvent_sets()
    dpp_subsets, dpp_support, dpp_normalization = check_projection_dpp_cauchy_binet()
    product_dimensions, product_entries, product_dpp_subsets, product_dpp_positive = (
        check_product_degree_dimension_and_dpp()
    )
    sparse_hls_columns, sparse_hls_rows, sparse_hls_entries = (
        check_sparse_booleanity_certification()
    )
    cross_parameters, cross_entries = check_explicit_quadratic_cross()
    anchor_parameters, fiber_parameters, fiber_rows, anchor_entries = (
        check_linear_anchor_and_four_fiber()
    )
    detector_trials, detector_sample, detector_ambient, detector_rows = (
        check_random_linear_detector()
    )
    (
        robust_sample,
        robust_ambient,
        robust_rows,
        robust_minimum,
        robust_deletion,
    ) = check_robust_linear_detector()
    support_parameters, support_forms, support_entries = check_affine_support_gap()
    hyper_parameters, hyper_intervals, hyper_counts, hyper_sharpest = (
        check_quadratic_hypergeometric_gap()
    )
    six_parameters, six_cleared_bits, six_equalities = (
        check_six_coordinate_sharp_gap()
    )
    design_parameters, design_pairs, design_entries, design_rows = (
        check_sylvester_hadamard_designs()
    )
    print(f"slice degree-dimension parameter checks: {parameters}")
    print(f"slice evaluation entries checked: {entries}")
    print(
        "random sparse unisolvent trials: "
        f"{trials} (sample {sample_size} of {ambient_size})"
    )
    print(f"minimal unisolvent basis checks: {minimal_checks}")
    print(
        "projection-DPP Cauchy-Binet check: "
        f"{dpp_subsets} subsets, {dpp_support} positive, normalization {dpp_normalization}"
    )
    print(
        "bounded-product degree checks: "
        f"{product_dimensions} parameters, {product_entries} entries"
    )
    print(
        "bounded-product projection-DPP check: "
        f"{product_dpp_subsets} subsets, {product_dpp_positive} positive"
    )
    print(
        "sparse adjacent-two-value certification: "
        f"{sparse_hls_rows} rows on {sparse_hls_columns} columns, "
        f"{sparse_hls_entries} ambient entries"
    )
    print(
        "explicit quadratic cross checks: "
        f"{cross_parameters} parameters, {cross_entries} incidence entries"
    )
    print(
        "linear rank-anchor checks: "
        f"{anchor_parameters} parameters, {anchor_entries} entries"
    )
    print(
        "four-coordinate fiber checks: "
        f"{fiber_parameters} parameters, {fiber_rows} row/pair cases"
    )
    print(
        "random linear detector trials: "
        f"{detector_trials}, sample {detector_sample} of {detector_ambient}, "
        f"{detector_rows} nontrivial rows"
    )
    print(
        "robust linear detector check: "
        f"sample {robust_sample} of {robust_ambient}, {robust_rows} rows, "
        f"minimum witnesses {robust_minimum}, deletion budget {robust_deletion}"
    )
    print(
        "affine support-gap checks: "
        f"{support_parameters} parameters, {support_forms} affine forms, "
        f"{support_entries} evaluations"
    )
    print(
        "quadratic hypergeometric-gap checks: "
        f"{hyper_parameters} parameters, {hyper_intervals} adjacent intervals, "
        f"{hyper_counts} ambient column counts, sharpest ratio "
        f"{hyper_sharpest[0]}/{hyper_sharpest[1]} at "
        f"(n,k,m,a)=({hyper_sharpest[2]},{hyper_sharpest[3]},"
        f"{hyper_sharpest[4]},{hyper_sharpest[5]}), "
        "unique 2/5 equality certified"
    )
    print(
        "six-coordinate sharp certificate: "
        f"{six_parameters} parameters, {six_cleared_bits} cleared bit-work, "
        f"unique equality {six_equalities}"
    )
    print(
        "Sylvester-Hadamard spectral designs: "
        f"{design_parameters} parameters, {design_pairs} design pair checks, "
        f"{design_entries} incidence entries, {design_rows} exhaustive rows"
    )

    print("unisolvent sparse-column audit: PASS")


if __name__ == "__main__":
    main()
