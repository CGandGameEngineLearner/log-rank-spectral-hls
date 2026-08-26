#!/usr/bin/env python3
"""Finite audits for the low-degree rank-pooling transfer theorem.

The published junta, cube-extension, and decision-tree theorems are not
reproved here.  This script checks the two new finite combinatorial interfaces:

1. rank-basis supports pool all cube rows in their span;
2. on every uniform layer, simultaneous S- and T-junta structure collapses
   to S intersection T when an outside coordinate exists.
3. a depth-q decision tree for an S-junta can be canonicalized to use S and
   at most q fixed representative coordinates outside S.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import combinations
import random


def bits(mask: int, n: int) -> tuple[int, ...]:
    return tuple((mask >> i) & 1 for i in range(n))


def relevant_set(values: tuple[int, ...], n: int) -> set[int]:
    relevant: set[int] = set()
    for i in range(n):
        step = 1 << i
        for x in range(1 << n):
            if not x & step and values[x] != values[x | step]:
                relevant.add(i)
                break
    return relevant


def multilinear_degree(values: tuple[int, ...], n: int) -> int:
    coeff = list(values)
    for i in range(n):
        step = 1 << i
        for mask in range(1 << n):
            if mask & step:
                coeff[mask] -= coeff[mask ^ step]
    return max((mask.bit_count() for mask, c in enumerate(coeff) if c), default=0)


def row_basis_indices(rows: list[tuple[int, ...]]) -> list[int]:
    """Return indices of an exact rational row basis."""

    pivots: dict[int, list[Fraction]] = {}
    basis: list[int] = []
    for idx, row in enumerate(rows):
        v = [Fraction(x) for x in row]
        for pivot in sorted(pivots):
            if v[pivot]:
                scale = v[pivot] / pivots[pivot][pivot]
                v = [a - scale * b for a, b in zip(v, pivots[pivot])]
        pivot = next((j for j, x in enumerate(v) if x), None)
        if pivot is None:
            continue
        scale = v[pivot]
        v = [x / scale for x in v]
        for old_pivot, old in list(pivots.items()):
            if old[pivot]:
                factor = old[pivot]
                pivots[old_pivot] = [a - factor * b for a, b in zip(old, v)]
        pivots[pivot] = v
        basis.append(idx)
    return basis


def check_cube_rank_pooling() -> tuple[int, int]:
    n = 4
    functions: list[tuple[int, ...]] = []
    supports: list[set[int]] = []
    for table in range(1 << (1 << n)):
        values = tuple((table >> x) & 1 for x in range(1 << n))
        if multilinear_degree(values, n) <= 2:
            functions.append(values)
            supports.append(relevant_set(values, n))

    rng = random.Random(20260826)
    trials = 2000
    for _ in range(trials):
        chosen = [rng.randrange(len(functions)) for _ in range(rng.randint(1, 20))]
        rows = [functions[i] for i in chosen]
        basis = row_basis_indices(rows)
        pool = set().union(*(supports[chosen[i]] for i in basis))
        rank = len(basis)
        assert len(pool) <= 4 * rank
        for row in rows:
            seen: dict[tuple[int, ...], int] = {}
            for x, value in enumerate(row):
                key = tuple((x >> i) & 1 for i in sorted(pool))
                if key in seen:
                    assert seen[key] == value
                else:
                    seen[key] = value
    return len(functions), trials


class DSU:
    def __init__(self, size: int) -> None:
        self.parent = list(range(size))

    def find(self, x: int) -> int:
        while self.parent[x] != x:
            self.parent[x] = self.parent[self.parent[x]]
            x = self.parent[x]
        return x

    def union(self, x: int, y: int) -> None:
        x, y = self.find(x), self.find(y)
        if x != y:
            self.parent[y] = x


def trace(mask: int, support: int) -> int:
    return mask & support


def check_support_intersection() -> int:
    checks = 0
    for n in range(2, 8):
        universe = (1 << n) - 1
        for k in range(1, n):
            layer = [sum(1 << i for i in comb) for comb in combinations(range(n), k)]
            for support_s in range(1 << n):
                for support_t in range(1 << n):
                    if (support_s | support_t) == universe:
                        continue
                    dsu = DSU(len(layer))
                    for support in (support_s, support_t):
                        first: dict[int, int] = {}
                        for idx, x in enumerate(layer):
                            key = trace(x, support)
                            if key in first:
                                dsu.union(idx, first[key])
                            else:
                                first[key] = idx
                    intersection = support_s & support_t
                    representatives: dict[int, int] = {}
                    for idx, x in enumerate(layer):
                        key = trace(x, intersection)
                        if key in representatives:
                            assert dsu.find(idx) == dsu.find(representatives[key])
                        else:
                            representatives[key] = idx
                    checks += 1
    return checks


def check_boundary_monomials() -> int:
    checks = 0
    for n in range(1, 10):
        for k in range(n + 1):
            layer = [sum(1 << i for i in comb) for comb in combinations(range(n), k)]
            for a in layer:
                for x in layer:
                    product = int((x & a) == a)
                    assert product == int(x == a)
                    checks += 1
    return checks


def is_junta_on_layer(
    layer: list[int], values: tuple[int, ...], support: int
) -> bool:
    seen: dict[int, int] = {}
    for x, value in zip(layer, values):
        key = x & support
        if key in seen and seen[key] != value:
            return False
        seen[key] = value
    return True


def decision_depth(
    layer: list[int], values: tuple[int, ...], allowed: int
) -> int:
    value_by_point = dict(zip(layer, values))
    memo: dict[tuple[tuple[int, ...], int], int] = {}
    impossible = len(layer) + 1

    def solve(points: tuple[int, ...], queries: int) -> int:
        key = (points, queries)
        if key in memo:
            return memo[key]
        point_values = {value_by_point[x] for x in points}
        if len(point_values) <= 1:
            return 0
        best = impossible
        remaining = queries
        while remaining:
            bit = remaining & -remaining
            remaining ^= bit
            zero = tuple(x for x in points if not x & bit)
            one = tuple(x for x in points if x & bit)
            if not zero or not one:
                continue
            candidate = 1 + max(solve(zero, queries ^ bit), solve(one, queries ^ bit))
            best = min(best, candidate)
        memo[key] = best
        return best

    return solve(tuple(layer), allowed)


def check_symmetric_tree_canonicalization() -> int:
    checks = 0
    for n in range(2, 6):
        universe = (1 << n) - 1
        for k in range(1, n):
            layer = [sum(1 << i for i in comb) for comb in combinations(range(n), k)]
            for table in range(1 << len(layer)):
                values = tuple((table >> i) & 1 for i in range(len(layer)))
                depth = decision_depth(layer, values, universe)
                for support in range(1 << n):
                    if not is_junta_on_layer(layer, values, support):
                        continue
                    outside = universe ^ support
                    representative_count = min(depth, outside.bit_count())
                    representatives = 0
                    remaining = outside
                    for _ in range(representative_count):
                        bit = remaining & -remaining
                        remaining ^= bit
                        representatives |= bit
                    restricted_depth = decision_depth(
                        layer, values, support | representatives
                    )
                    assert restricted_depth <= depth
                    checks += 1
    return checks


def multiset_words(counts: tuple[int, ...]) -> list[tuple[int, ...]]:
    words: list[tuple[int, ...]] = []

    def rec(prefix: list[int], remaining: list[int]) -> None:
        if sum(remaining) == 0:
            words.append(tuple(prefix))
            return
        for color, count in enumerate(remaining):
            if count:
                remaining[color] -= 1
                prefix.append(color)
                rec(prefix, remaining)
                prefix.pop()
                remaining[color] += 1

    rec([], list(counts))
    return words


def is_junta_generic(
    domain: list[tuple[int, ...]], values: tuple[int, ...], support: tuple[int, ...]
) -> bool:
    seen: dict[tuple[int, ...], int] = {}
    for x, value in zip(domain, values):
        key = tuple(x[i] for i in support)
        if key in seen and seen[key] != value:
            return False
        seen[key] = value
    return True


def decision_depth_generic(
    domain: list[tuple[int, ...]], values: tuple[int, ...], allowed: tuple[int, ...]
) -> int:
    memo: dict[tuple[tuple[int, ...], tuple[int, ...]], int] = {}
    impossible = len(domain) + 1

    def solve(points: tuple[int, ...], queries: tuple[int, ...]) -> int:
        key = (points, queries)
        if key in memo:
            return memo[key]
        if len({values[p] for p in points}) <= 1:
            return 0
        best = impossible
        for query in queries:
            parts: dict[int, list[int]] = {}
            for p in points:
                parts.setdefault(domain[p][query], []).append(p)
            if len(parts) <= 1:
                continue
            next_queries = tuple(i for i in queries if i != query)
            candidate = 1 + max(
                solve(tuple(part), next_queries) for part in parts.values()
            )
            best = min(best, candidate)
        memo[key] = best
        return best

    return solve(tuple(range(len(domain))), allowed)


def check_bounded_alphabet_tree_transfer() -> tuple[int, int]:
    rng = random.Random(20260827)
    product_checks = 0
    multislice_checks = 0

    # Complete ternary products: an S-junta can be pruned to query only S.
    product_domain = [
        (a, b, c) for a in range(3) for b in range(3) for c in range(3)
    ]
    all_coordinates = (0, 1, 2)
    for _ in range(600):
        support = tuple(i for i in all_coordinates if rng.randrange(2))
        table: dict[tuple[int, ...], int] = {}
        values_list: list[int] = []
        for x in product_domain:
            key = tuple(x[i] for i in support)
            table.setdefault(key, rng.randrange(2))
            values_list.append(table[key])
        values = tuple(values_list)
        full_depth = decision_depth_generic(product_domain, values, all_coordinates)
        support_depth = decision_depth_generic(product_domain, values, support)
        assert support_depth <= full_depth
        product_checks += 1

    # Exhaustive two-color multislice canonicalization on histogram (2,2).
    slice_domain = multiset_words((2, 2))
    n = 4
    all_coordinates = tuple(range(n))
    for table in range(1 << len(slice_domain)):
        values = tuple((table >> i) & 1 for i in range(len(slice_domain)))
        full_depth = decision_depth_generic(slice_domain, values, all_coordinates)
        for support_mask in range(1 << n):
            support = tuple(i for i in range(n) if support_mask >> i & 1)
            if not is_junta_generic(slice_domain, values, support):
                continue
            outside = [i for i in range(n) if not support_mask >> i & 1]
            representatives = tuple(outside[: min(full_depth, len(outside))])
            allowed = tuple(sorted(set(support) | set(representatives)))
            restricted_depth = decision_depth_generic(slice_domain, values, allowed)
            assert restricted_depth <= full_depth
            multislice_checks += 1

    return product_checks, multislice_checks


def main() -> None:
    low_degree_count, pooling_trials = check_cube_rank_pooling()
    intersection_checks = check_support_intersection()
    boundary_checks = check_boundary_monomials()
    canonicalization_checks = check_symmetric_tree_canonicalization()
    product_tree_checks, multislice_tree_checks = check_bounded_alphabet_tree_transfer()
    print(f"cube degree<=2 functions on 4 variables: {low_degree_count}")
    print(f"rank-pooling trials: {pooling_trials}")
    print(f"slice support-intersection parameter checks: {intersection_checks}")
    print(f"boundary monomial checks: {boundary_checks}")
    print(f"symmetric-tree canonicalization checks: {canonicalization_checks}")
    print(f"bounded-alphabet product pruning checks: {product_tree_checks}")
    print(f"multislice multiway canonicalization checks: {multislice_tree_checks}")
    print("low-degree slice protocol audit: PASS")


if __name__ == "__main__":
    main()
