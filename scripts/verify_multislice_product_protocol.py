#!/usr/bin/env python3
"""Finite audit for the product-multislice rank-sensitive protocol."""

from __future__ import annotations

import itertools
import math
import random


def rank_mod_prime(rows: list[list[int]], prime: int = 1_000_003) -> int:
    if not rows:
        return 0
    a = [[x % prime for x in row] for row in rows]
    rank = 0
    for col in range(len(a[0])):
        pivot = next((i for i in range(rank, len(a)) if a[i][col]), None)
        if pivot is None:
            continue
        a[rank], a[pivot] = a[pivot], a[rank]
        inv = pow(a[rank][col], prime - 2, prime)
        a[rank] = [(x * inv) % prime for x in a[rank]]
        for i in range(len(a)):
            if i == rank or not a[i][col]:
                continue
            factor = a[i][col]
            a[i] = [
                (a[i][j] - factor * a[rank][j]) % prime
                for j in range(len(a[0]))
            ]
        rank += 1
    return rank


def multislice(counts: tuple[int, ...]) -> list[tuple[int, ...]]:
    word = tuple(
        color for color, count in enumerate(counts) for _ in range(count)
    )
    return sorted(set(itertools.permutations(word)))


def canonical_color_subsets(alphabet: int) -> list[int]:
    full = (1 << alphabet) - 1
    return [
        mask
        for mask in range(1, full)
        if mask < (full ^ mask)
    ]


def audit(factors: tuple[tuple[int, ...], ...], samples: int = 250) -> int:
    domains = [multislice(counts) for counts in factors]
    columns = list(itertools.product(*domains))
    atoms: list[tuple[int, int, int]] = []
    for factor, counts in enumerate(factors):
        for position in range(sum(counts)):
            for mask in canonical_color_subsets(len(counts)):
                atoms.append((factor, position, mask))

    evaluations = {}
    for atom in atoms:
        factor, position, mask = atom
        evaluations[atom] = [
            int(bool(mask & (1 << column[factor][position])))
            for column in columns
        ]

    rng = random.Random(hash(factors) & 0xFFFFFFFF)
    checks = 0
    max_alphabet = max(map(len, factors))
    for _ in range(samples):
        chosen = rng.sample(atoms, rng.randint(1, len(atoms)))
        rows = []
        used_positions = set()
        for atom in chosen:
            row = evaluations[atom]
            if rng.randrange(2):
                row = [1 - x for x in row]
            rows.append(row)
            used_positions.add(atom[:2])
        rank = rank_mod_prime(rows)
        position_count = len(used_positions)
        atom_count = len(chosen)
        assert position_count <= 2 * (rank + 1)
        assert atom_count <= (1 << (max_alphabet - 1)) * position_count
        message_count = 2 * atom_count + 2
        assert math.ceil(math.log2(message_count)) <= (
            math.ceil(math.log2(rank + 1)) + max_alphabet + 4
        )
        checks += 1

    print(
        f"factors={factors} columns={len(columns)} atoms={len(atoms)} "
        f"checks={checks}"
    )
    return checks


def main() -> None:
    cases = [
        ((2, 2),),
        ((2, 2), (2, 2)),
        ((2, 2, 2),),
        ((2, 2), (2, 2, 2)),
    ]
    total = sum(audit(factors) for factors in cases)
    print(f"MULTISLICE_PRODUCT_PROTOCOL_CHECKS={total}")


if __name__ == "__main__":
    main()
