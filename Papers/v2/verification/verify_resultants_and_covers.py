#!/usr/bin/env python3
"""Finite exact checks for the short-span factorial-triple bound.

Requires Python 3.10+ and SymPy. Finite tests are NOT a proof of the
asymptotic theorem or of infinitude in Erdos 1059.

Run:
    python verify_short_gap.py --certificates ../certificates --output results.json
"""
from __future__ import annotations
import argparse
import importlib.util
import json
import math
from pathlib import Path
import sympy as sp


def require(value: bool, message: str) -> None:
    if not value:
        raise ValueError(message)


def resultant_checks(max_gap: int = 10) -> list[dict]:
    x = sp.Symbol('x')
    polys = {d: sp.Poly(sp.prod(x+j for j in range(1,d+1))-1, x)
             for d in range(1,max_gap+1)}
    out: list[dict] = []
    for b in range(4,max_gap+1):
        for a in range(2,b-1):
            R = abs(int(sp.resultant(polys[a],polys[b],x)))
            require(R != 0, f'Zero resultant for {(a,b)}')
            require(R <= 2**a * b**(a*(b-a)), f'Height bound for {(a,b)}')
            factors = {int(p):int(e) for p,e in sp.factorint(R).items()}
            require(math.prod(p**e for p,e in factors.items()) == R,
                    'Factorization reconstruction failed')
            records=[]
            for q,e in sorted(factors.items()):
                require(bool(sp.isprime(q)), 'Uncertified factor')
                # Polynomial gcd degree bounds the number of distinct roots.
                fa=sp.Poly(polys[a].as_expr(),x, modulus=q)
                fb=sp.Poly(polys[b].as_expr(),x, modulus=q)
                degree=int(sp.gcd(fa,fb).degree())
                require(degree <= e, f'GCD/valuation failure for {(a,b,q)}')
                records.append({'q':q,'v_q_resultant':e,'gcd_degree_mod_q':degree})
            out.append({'a':a,'b':b,'abs_resultant':str(R),
                        'height_bound_exact':True,'prime_factors':records})
    return out


def witness_checks(resultants: list[dict], max_gap: int = 10) -> list[dict]:
    """Enumerate starts for all possible q by factoring the resultants first."""
    out=[]
    for L in [12,20,50,100,300]:
        D=min(max_gap,L)
        total=0
        valuation_budget=0
        height_product=1
        resultant_product=1
        for rec in resultants:
            a,b=rec['a'],rec['b']
            if b>D:
                continue
            R=int(rec['abs_resultant'])
            height_product *= 2**a * b**(a*(b-a))
            resultant_product *= R
            for factor in rec['prime_factors']:
                q,e=factor['q'],factor['v_q_resultant']
                if q<=L:
                    continue
                starts=[]
                for i in range(2,L-b+1):
                    pa=(math.prod(range(i+1,i+a+1))-1)%q
                    pb=(math.prod(range(i+1,i+b+1))-1)%q
                    if pa==0 and pb==0:
                        require(math.factorial(i)%q == math.factorial(i+a)%q
                                == math.factorial(i+b)%q,
                                'Collision criterion disagreement')
                        starts.append(i)
                require(len(starts)<=e,'Starts exceed resultant valuation')
                total+=len(starts)
                valuation_budget+=e
        require(total<=valuation_budget,'Total count bound failed')
        require((L+1)**valuation_budget<=resultant_product,
                'Product versus valuation count failed')
        require(resultant_product<=height_product,'Total height bound failed')
        out.append({'L':L,'D':D,'prime_labelled_triples':total,
                    'sum_large_prime_valuations':valuation_budget,
                    'exact_product_inequalities_verified':True})
    return out


def certificate_checks(root: Path) -> list[dict]:
    verifier=root/'verify_covers.py'
    spec=importlib.util.spec_from_file_location('original_cover_verifier',verifier)
    if spec is None or spec.loader is None:
        raise ValueError('Could not load original verifier')
    module=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    rows=[]
    for L,a,b in [(300,46,100),(1000,39,100),(3000,17,50)]:
        path=root/f'greedy_cover_{L}.json'
        verified=module.verify(path,a,b)
        cert=json.loads(path.read_text())
        D=math.isqrt(math.isqrt(L))
        spans=[]
        for q,residue,fibre,designated in cert['edges']:
            B=sorted(designated)
            spans.extend(B[j+2]-B[j] for j in range(len(B)-2))
        rows.append({**verified,'floor_L_quarter_power':D,
                    'consecutive_triple_witnesses':len(spans),
                    'minimum_span':min(spans),
                    'spans_at_most_quarter_power':sum(d<=D for d in spans)})
    return rows


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--certificates',type=Path,required=True)
    parser.add_argument('--output',type=Path,default=Path('results.json'))
    args=parser.parse_args()
    resultants=resultant_checks()
    output={
        'scope':'Finite verification only; not a proof of infinitude or asymptotic compression.',
        'resultant_cases':resultants,
        'short_triple_checks':witness_checks(resultants),
        'existing_cover_certificates':certificate_checks(args.certificates),
    }
    args.output.write_text(json.dumps(output,indent=2)+'\n')
    print(json.dumps({k:v for k,v in output.items() if k!='resultant_cases'},indent=2))


if __name__=='__main__':
    main()
