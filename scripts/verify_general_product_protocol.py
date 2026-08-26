#!/usr/bin/env python3
"""Finite audit for the general product-layer O(t log rank) protocol."""

from __future__ import annotations

import itertools
import random
from fractions import Fraction


def rank_mod_prime(rows: list[list[int]], prime: int = 1_000_003) -> int:
    if not rows:
        return 0
    matrix = [[entry % prime for entry in row] for row in rows]
    rank = 0
    for column in range(len(matrix[0])):
        pivot = next(
            (i for i in range(rank, len(matrix)) if matrix[i][column]), None
        )
        if pivot is None:
            continue
        matrix[rank], matrix[pivot] = matrix[pivot], matrix[rank]
        inverse = pow(matrix[rank][column], prime - 2, prime)
        matrix[rank] = [(x * inverse) % prime for x in matrix[rank]]
        for i in range(len(matrix)):
            if i == rank or not matrix[i][column]:
                continue
            factor = matrix[i][column]
            matrix[i] = [
                (matrix[i][j] - factor * matrix[rank][j]) % prime
                for j in range(len(matrix[0]))
            ]
        rank += 1
    return rank


def product_columns(params: tuple[tuple[int, int], ...]) -> list[int]:
    local_layers = []
    offset = 0
    for n, k in params:
        local_layers.append(
            [
                sum(1 << (offset + i) for i in choice)
                for choice in itertools.combinations(range(n), k)
            ]
        )
        offset += n
    return [
        sum(choice)
        for choice in itertools.product(*local_layers)
    ]


def tube_radius(params: tuple[tuple[int, int], ...]) -> int:
    best = 0
    ranges = [range(n + 1) for n, _ in params]
    for sizes in itertools.product(*ranges):
        variance = sum(
            Fraction(s * (n - s) * k * (n - k), n * n * (n - 1))
            for s, (n, k) in zip(sizes, params)
        )
        if variance <= Fraction(1, 4):
            best = max(
                best,
                sum(min(s, n - s) for s, (n, _) in zip(sizes, params)),
            )
    return best


def canonical_error(row: int, params: tuple[tuple[int, int], ...]) -> int:
    rounded = 0
    offset = 0
    for n, _ in params:
        block = sum(1 << (offset + i) for i in range(n))
        if (row & block).bit_count() > n // 2:
            rounded |= block
        offset += n
    return row ^ rounded


def audit(params: tuple[tuple[int, int], ...], samples: int = 300) -> int:
    d = sum(n for n, _ in params)
    columns = product_columns(params)
    t = tube_radius(params)
    rows_by_root: dict[int, list[tuple[int, int]]] = {}
    for row in range(1 << d):
        values = [(row & column).bit_count() for column in columns]
        low, high = min(values), max(values)
        for root in {low, high - 1}:
            if root >= 0 and all(v in (root, root + 1) for v in values):
                error = canonical_error(row, params)
                assert error.bit_count() <= t
                rows_by_root.setdefault(root, []).append((row, error))

    rng = random.Random(hash(params) & 0xFFFFFFFF)
    checks = 0
    for root, all_rows in rows_by_root.items():
        for _ in range(samples):
            selected = rng.sample(all_rows, rng.randint(1, len(all_rows)))
            matrix = [
                [
                    int((row & column).bit_count() == root + 1)
                    for column in columns
                ]
                for row, _ in selected
            ]
            rank = rank_mod_prime(matrix)
            used = 0
            for _, error in selected:
                used |= error
            coordinate_count = used.bit_count()
            if t == 0:
                assert coordinate_count == 0
            else:
                assert coordinate_count <= 2 * rank * t
            checks += 1
    print(
        f"params={params} d={d} columns={len(columns)} "
        f"tube_radius={t} checks={checks}"
    )
    return checks


def main() -> None:
    cases = [
        ((3, 1), (4, 2)),
        ((3, 1), (5, 2)),
        ((4, 1), (5, 3)),
        ((2, 1), (3, 1), (4, 2)),
    ]
    total = sum(audit(params) for params in cases)
    print(f"GENERAL_PRODUCT_PROTOCOL_CHECKS={total}")


if __name__ == "__main__":
    main()
