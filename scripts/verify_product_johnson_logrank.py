#!/usr/bin/env python3
"""Exhaustive small-parameter audit for the product-Johnson theorem.

For each requested (block size n, block count m), enumerate the complete
product of middle layers and every Boolean row.  Verify:

1. every row whose intersection values are two consecutive integers is at
   Hamming distance at most one from a union of blocks;
2. the error-fiber / coordinate-membership / row-colour extraction constructs
   a monochromatic rectangle of density at least 1/[4(d+1)].
"""

from __future__ import annotations

import itertools
import math
import random
from dataclasses import dataclass


@dataclass(frozen=True)
class AuditResult:
    n: int
    m: int
    d: int
    columns: int
    qualifying_rows: int
    row_column_checks: int
    rank_protocol_checks: int
    worst_constructed_density: float


def subset_mask(items: tuple[int, ...]) -> int:
    return sum(1 << i for i in items)


def rank_mod_prime(rows: list[list[int]], prime: int = 1_000_003) -> int:
    """Return matrix rank over F_prime, a lower bound for real rank."""
    if not rows:
        return 0
    matrix = [[entry % prime for entry in row] for row in rows]
    row_count = len(matrix)
    column_count = len(matrix[0])
    rank = 0
    for column in range(column_count):
        pivot = next(
            (index for index in range(rank, row_count) if matrix[index][column]),
            None,
        )
        if pivot is None:
            continue
        matrix[rank], matrix[pivot] = matrix[pivot], matrix[rank]
        inverse = pow(matrix[rank][column], prime - 2, prime)
        matrix[rank] = [(entry * inverse) % prime for entry in matrix[rank]]
        for index in range(row_count):
            if index == rank or not matrix[index][column]:
                continue
            factor = matrix[index][column]
            matrix[index] = [
                (matrix[index][j] - factor * matrix[rank][j]) % prime
                for j in range(column_count)
            ]
        rank += 1
        if rank == row_count:
            break
    return rank


def audit(n: int, m: int) -> AuditResult:
    if n < 4 or n % 2:
        raise ValueError("n must be even and at least four")
    if m < 1:
        raise ValueError("m must be positive")

    d = n * m
    block_masks = [
        sum(1 << (block * n + j) for j in range(n))
        for block in range(m)
    ]
    local_middle = [
        subset_mask(choice)
        for choice in itertools.combinations(range(n), n // 2)
    ]
    columns: list[int] = []
    for choices in itertools.product(local_middle, repeat=m):
        mask = 0
        for block, local in enumerate(choices):
            mask |= local << (block * n)
        columns.append(mask)

    rows_by_root: dict[int, list[tuple[int, int, int]]] = {}
    qualifying = 0

    for row in range(1 << d):
        values = [(row & col).bit_count() for col in columns]
        low, high = min(values), max(values)
        if high - low > 1:
            continue
        qualifying += 1

        rounded = 0
        for block_mask in block_masks:
            if (row & block_mask).bit_count() > n // 2:
                rounded |= block_mask
        error = row ^ rounded
        assert error.bit_count() <= 1

        for root in {low, high - 1}:
            if root >= 0 and all(value in (root, root + 1) for value in values):
                rows_by_root.setdefault(root, []).append((row, rounded, error))

    worst = 1.0
    rank_protocol_checks = 0
    rng = random.Random(1_000_000 * n + m)
    for root, rows in rows_by_root.items():
        error_fibers: dict[int, list[tuple[int, int, int]]] = {}
        for item in rows:
            error_fibers.setdefault(item[2], []).append(item)
        error, retained_rows = max(
            error_fibers.items(), key=lambda item: len(item[1])
        )

        if error == 0:
            retained_columns = columns
        else:
            coordinate = (error & -error).bit_length() - 1
            absent = [col for col in columns if not ((col >> coordinate) & 1)]
            present = [col for col in columns if (col >> coordinate) & 1]
            retained_columns = absent if len(absent) >= len(present) else present

        colours: dict[int, list[tuple[int, int, int]]] = {0: [], 1: []}
        witness_column = retained_columns[0]
        for item in retained_rows:
            row = item[0]
            value = (row & witness_column).bit_count()
            assert all(
                (row & col).bit_count() == value for col in retained_columns
            )
            colours[int(value == root + 1)].append(item)

        retained_row_count = max(len(colours[0]), len(colours[1]))
        density = (retained_row_count / len(rows)) * (
            len(retained_columns) / len(columns)
        )
        assert density + 1e-12 >= 1 / (4 * (d + 1))
        worst = min(worst, density)

        # Rank-sensitive protocol audit on deterministic random subfamilies.
        for _ in range(50):
            sample = rng.sample(rows, rng.randint(1, len(rows)))
            matrix: list[list[int]] = []
            used_coordinates: set[int] = set()
            for row, rounded, error in sample:
                matrix_row = [
                    int((row & column).bit_count() == root + 1)
                    for column in columns
                ]
                matrix.append(matrix_row)
                if len(set(matrix_row)) > 1:
                    assert error.bit_count() == 1
                    used_coordinates.add((error & -error).bit_length() - 1)
            rank_lower_bound = rank_mod_prime(matrix)
            coordinate_count = len(used_coordinates)
            assert coordinate_count <= n * (rank_lower_bound + 1) / (n - 1)
            message_count = 2 * coordinate_count + 2
            assert math.ceil(math.log2(message_count)) <= (
                math.ceil(math.log2(rank_lower_bound + 1)) + 4
            )
            rank_protocol_checks += 1

    return AuditResult(
        n=n,
        m=m,
        d=d,
        columns=len(columns),
        qualifying_rows=qualifying,
        row_column_checks=(1 << d) * len(columns),
        rank_protocol_checks=rank_protocol_checks,
        worst_constructed_density=worst,
    )


def main() -> None:
    cases = [(4, 1), (4, 2), (4, 3), (6, 1), (6, 2)]
    total_checks = 0
    total_rank_checks = 0
    for n, m in cases:
        result = audit(n, m)
        total_checks += result.row_column_checks
        total_rank_checks += result.rank_protocol_checks
        print(
            f"n={result.n} m={result.m} d={result.d} "
            f"columns={result.columns} "
            f"qualifying_rows={result.qualifying_rows} "
            f"worst_density={result.worst_constructed_density:.8f}"
        )
    print(f"PRODUCT_JOHNSON_ROW_COLUMN_CHECKS={total_checks}")
    print(f"PRODUCT_JOHNSON_RANK_PROTOCOL_CHECKS={total_rank_checks}")


if __name__ == "__main__":
    main()
