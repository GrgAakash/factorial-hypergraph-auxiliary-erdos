#!/usr/bin/env python3
"""Independently verify finite factorial-cover certificates using only Python's standard library.

This does not prove an asymptotic covering bound or apply Harman's theorem at these
finite values of L. It verifies primes, residue fibres, full coverage, distinct
prime colours, and exact integer modulus inequalities.

Usage: python verify_covers.py
"""
from __future__ import annotations
import json
import math
from pathlib import Path


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    return all(n % d for d in range(3, math.isqrt(n) + 1, 2))


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def factorial_residues(L: int, q: int) -> list[int]:
    values = [1] * (L + 1)
    for k in range(1, L + 1):
        values[k] = values[k - 1] * k % q
    return values


def verify(path: Path, numerator: int, denominator: int) -> dict:
    certificate = json.loads(path.read_text())
    L = int(certificate['summary']['L'])
    X = math.factorial(L + 1)
    factorial_L = math.factorial(L)
    colours: set[int] = set()
    designated: set[int] = set()
    covered: set[int] = set()
    M = 1
    for q, a, fibre, new in certificate['edges']:
        require(q not in colours, f'L={L}: repeated prime colour {q}')
        require(is_prime(q), f'L={L}: nonprime colour {q}')
        require(L < q < factorial_L, f'L={L}: colour outside admissible range')
        require(q <= L * L, f'L={L}: colour larger than L^2')
        require(0 < a < q, f'L={L}: nonunit or unnormalized residue')
        values = factorial_residues(L, q)
        true_fibre = [k for k in range(2, L + 1) if values[k] == a]
        require(fibre == true_fibre, f'L={L}: incorrect complete fibre for q={q}')
        require(len(new) == len(set(new)) and bool(new), 'Invalid designated subset')
        require(set(new) <= set(fibre), 'Designated indices not in fibre')
        require(not designated.intersection(new), 'Repeated designated index')
        colours.add(q)
        designated.update(new)
        covered.update(fibre)
        M *= q
    for k, q in certificate['singletons']:
        require(q not in colours and is_prime(q), 'Invalid singleton prime')
        require(L < q < factorial_L and q <= L * L, 'Singleton colour outside range')
        require(2 <= k <= L and k not in designated, 'Invalid singleton index')
        a = factorial_residues(L, q)[k]
        require(a != 0, 'Nonunit singleton residue')
        colours.add(q)
        designated.add(k)
        covered.add(k)
        M *= q
    require(designated == set(range(2, L + 1)), 'Designated sets do not partition all indices')
    require(covered == set(range(2, L + 1)), 'Not a full factorial cover')
    require(pow(M, denominator) < pow(X, numerator), 'Exact modulus bound failed')
    return {'L': L, 'prime_colours': len(colours),
            'approx_logM_over_logX': math.log(M)/math.log(X),
            'exact_verified_bound': f'M^{denominator} < X^{numerator}',
            'covers_every_index_2_through_L': True,
            'prime_bound_L_squared': True}


def main() -> None:
    root = Path(__file__).resolve().parent
    results = [verify(root/f'greedy_cover_{L}.json', a, b)
               for L, a, b in [(300, 46, 100), (1000, 39, 100), (3000, 17, 50)]]
    print(json.dumps(results, indent=2))


if __name__ == '__main__':
    main()
