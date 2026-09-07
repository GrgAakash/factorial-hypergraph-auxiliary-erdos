#!/usr/bin/env python3
"""Finite checks for the expanded factorial-cover manuscript.

These are exact sanity checks, NOT proofs of the asymptotic theorems.
Only Python's standard library is used. Resultant checks are provided
separately in verify_short_gap.py and require SymPy.
"""
from __future__ import annotations
from collections import Counter
from fractions import Fraction
from itertools import permutations
from math import factorial, gcd, isqrt, prod
from pathlib import Path
import argparse
import json
import random


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def prime(n: int) -> bool:
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def permutation_checks(rng: random.Random) -> int:
    cases = 0
    for s in range(1, 9):
        maps_cases = [
            [[0] * s for _ in range(s)],
            [list(range(s)) for _ in range(s)],
        ]
        for _ in range(12):
            maps_cases.append([[rng.randrange(rng.randint(1, s)) for _ in range(s)]
                               for _ in range(s)])
        for maps in maps_cases:
            energies = [sum(v*v for v in Counter(row).values()) for row in maps]
            outputs = {tuple(maps[j][p[j]] for j in range(s))
                       for p in permutations(range(s))}
            require(len(outputs) * prod(energies) >= factorial(s) * s**s,
                    f'Permutation-image failure at s={s}')
            cases += 1
    return cases


def energy_checks(rng: random.Random) -> int:
    cases = 0
    for L in range(1, 101):
        primes = [q for q in range(L+1, 3*L+20) if prime(q)][:12]
        F = min((L+h-1)//h + h*(h-1)//2 for h in range(1, L+1))
        for q in primes:
            values=[]
            v=1
            for k in range(1, L+1):
                v=v*k % q
                values.append(v)
            counts=Counter(values)
            require(max(counts.values()) <= F, f'Fiber bound failed at {(L,q)}')
            for U in [list(range(L)), list(range(0,L,2)),
                      [j for j in range(L) if rng.randrange(2)]]:
                E=sum(n*n for n in Counter(values[j] for j in U).values())
                require(E*E <= 36*L**3, f'Energy failure at {(L,q)}')
                for h in [1, max(1,isqrt(L)), L]:
                    rhs=((L+h-1)//h)*(len(U)+h*(h-1))
                    require(E <= rhs, f'Finite block bound failed at {(L,q,h)}')
                cases += 1
    return cases


def progression_checks(rng: random.Random) -> int:
    cases=0
    for _ in range(400):
        L=rng.randrange(2,16)
        ps=[q for q in range(2,L+1) if prime(q)]
        larger=[q for q in range(L+1,5*L+10) if prime(q)]
        M=prod(rng.sample(larger, rng.randint(1,min(2,len(larger)))))
        ds=[d for d in range(1,30) if gcd(d,M)==1]
        d=rng.choice(ds)
        A=rng.choice([a for a in range(1,M+1) if gcd(a,M)==1])
        b=rng.choice([b for b in range(d) if gcd(b,d)==1])
        u=Fraction(rng.randrange(-20,100),2)
        v=u+Fraction(rng.randrange(1,600),2)
        W=prod(ps)
        actual=sum(n%M==A%M and n%d==b and gcd(n,W)==1
                   for n in range(u.numerator//u.denominator+1,
                                  v.numerator//v.denominator+1))
        pfree=[q for q in ps if d%q]
        density=prod((Fraction(q-1,q) for q in pfree), start=Fraction(1))
        main=(v-u)*density/(M*d)
        require(abs(Fraction(actual)-main) <= 2**len(pfree),
                f'Progression-count failure at {(L,M,d,A,b,u,v)}')
        cases+=1
    return cases


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path('extension_checks.json'))
    args=parser.parse_args()
    rng=random.Random(1059)
    result={
        'scope':'Finite exact checks only; not formal verification or an asymptotic proof.',
        'permutation_image_cases':permutation_checks(rng),
        'factorial_energy_and_fiber_cases':energy_checks(rng),
        'prescribed_progression_cases':progression_checks(rng),
        'status':'PASS',
    }
    require(all(factorial(k)%337==70 for k in [17,81,87,176,198,293]),
            'Displayed six-index fiber is wrong')
    result['displayed_fiber_mod_337']='PASS'
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':
    main()
