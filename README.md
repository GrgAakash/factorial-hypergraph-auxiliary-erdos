# Factorial-residue hypergraphs and an auxiliary problem of Erdos

This repository contains the Lean 4 formalization accompanying Aakash
Gurung's manuscript *Factorial-residue hypergraphs and an auxiliary problem
of Erdos*.

## Current working draft

**Working draft — exposition and mathematical review in progress.**
Last updated: 7 September 2026.

The expanded manuscript, *Factorial-residue hypergraphs and covering
congruences*, is available as a
[PDF](paper/working-draft/factorial_residue_covers_expanded.pdf) and
[TeX source](paper/working-draft/factorial_residue_covers_expanded.tex).
It has no author byline while exposition and review continue; the AI
disclosure is retained. The accompanying
[finite examples and checkers](paper/working-draft/README.md) are also included.

The expanded draft contains additional results beyond the registered
formalization. Palomar v1 covers the original quantitative auxiliary theorem,
conditional on the explicitly stated standard upper-bound sieve theorem;
it does not certify all results in this expanded manuscript. The original
manuscript referenced by the formalization remains at
[`paper/factorial_residue_hypergraphs.tex`](paper/factorial_residue_hypergraphs.tex).
Updating this working draft does not change the registered commit.

## Result submitted to Palomar

For a positive integer `L`, call `n` **`L`-rough** when every prime divisor of
`n` is greater than `L`.  Let `goodSet L` consist of the integers `n` satisfying

```text
2 L! < n <= (L+1)!,
n is L-rough,
n - k! is composite for every 1 <= k <= L.
```

The compared Lean declaration proves, conditional on the explicitly stated
standard dimension-one upper-bound sieve `UpperBoundSieveDimOne`, that there
are constants `eta > 0` and `L0` such that

```text
((L+1)!)^eta / (100 log L) <= #(goodSet L)
```

for every `L >= L0`.

This gives a quantitative form of an auxiliary question that Erdos suggested
alongside Problem 1059.  It is not the original prime problem: the constructed
integer `n` need not be prime.  The original question asking for infinitely
many prime `p` such that every relevant `p-k!` is composite remains open.

## Exact formal status

The Palomar theorem is

```lean
FactorialHypergraph.Palomar.quantitative_auxiliary_erdos
```

and has an explicit hypothesis

```lean
hs : FactorialHypergraph.UpperBoundSieveDimOne
```

The fundamental lemma of sieve theory is not proved in Lean in this project.
The finite weighted interface used here was matched, hypothesis by hypothesis,
to Koukoulopoulos, *The Distribution of Prime Numbers*, Theorem 18.11(a), at
sieve dimension one and `u = 10`; see
[`docs/SIEVE_SOURCE_AUDIT.md`](docs/SIEVE_SOURCE_AUDIT.md).

All problem-specific steps for the registered auxiliary theorem after that
classical theorem are formalized. In
particular, the quadratic root counts, Mertens estimates needed by the
application, the large-prime-factor estimate, the factorial-collision cover,
the CRT construction, and the final transference argument are represented in
Lean.  The final proof uses a `1/40` threshold in one intermediate
large-prime-factor lemma rather than the manuscript's sharper `1/8`; this only
changes how large `L` must be and leaves the compared conclusion unchanged.

The Lean transference theorem obtains an intermediate count with exponent
`eta/2`, whereas the manuscript obtains exponent `eta`: Lean uses the
elementary bound `W <= 4^L` instead of Mertens's product estimate.  Because the
compared theorem asserts only the existence of some absolute positive
exponent, this rescaling does not change its statement.  An unused singleton
baseline lemma also has constant `21` instead of the manuscript's `20`, solely
to absorb an integer ceiling; it is not in the final dependency chain.

The manuscript assigns `kappa(L) = +infinity` if no rainbow cover exists;
Lean's real-valued `sInf` convention gives zero for an empty cover family.
Every theorem used in the compared result constructs a cover explicitly, so
the empty-family convention is never used and has no effect on the result.

The source tree contains no `sorry`, `admit`, custom axiom, or unsafe
declaration outside the deliberate `sorry` in `Challenge.lean`.  The proved
result uses only `propext`, `Classical.choice`, and `Quot.sound`.

## Repository map

- [`Challenge.lean`](Challenge.lean) is the short Mathlib-only statement
  surface audited by Palomar.  It defines the sieve hypothesis, roughness, and
  the counted set directly and leaves the compared theorem as the deliberate
  Challenge hole.
- [`Solution.lean`](Solution.lean) connects that statement to the completed
  proof.
- [`FactorialHypergraph/`](FactorialHypergraph/) contains the substantive proof
  development.
- [`comparator.json`](comparator.json) selects the single quantitative theorem
  and the three permitted axioms.
- [`formalization.yaml`](formalization.yaml) records provenance, scope,
  automation, fidelity, classifications, and review status.
- [`paper/factorial_residue_hypergraphs.tex`](paper/factorial_residue_hypergraphs.tex)
  is the mathematical manuscript formalized here.
- [`docs/VERIFICATION.md`](docs/VERIFICATION.md) records the independent archive
  and build audit.
- [`docs/PRESUBMISSION_REFEREE_AUDIT.md`](docs/PRESUBMISSION_REFEREE_AUDIT.md)
  reconciles three independent agent reviews of mathematical fidelity, Lean
  integrity, and Palomar compliance.

## Build

The project pins Lean 4.33.0 and Mathlib commit
`db584cd6d46c92f209a44c0f1c829460d327499d`.

```bash
lake exe cache get
lake build
ruby scripts/validate-formalization.rb
```

On Linux with Git, Go, Ruby, Rust/Cargo, Python 3, and Landlock support, run
the complete local Comparator and NanoDa replay with

```bash
./scripts/verify-comparator.sh
```

GitHub Actions runs the metadata, licence, Lean build, and Comparator checks.

## Formal verification

This formalization is registered in the Palomar Registry as
[PALOMAR-2026-08-27-000003 v1](https://palomar-registry.org/entry.html?id=PALOMAR-2026-08-27-000003&version=1).
The registered record pins commit
`67b4088fc84422c84f7e5e205552757c3c0c9a71`; its Lean, Comparator, and
NanoDa checks succeeded.

Palomar is a registry of machine-checked results, not a journal or a substitute
for expert mathematical peer review.
New formalizations can be submitted through the
[Palomar submission form](https://submit.palomar-registry.org/).

## Authorship, automation, and review

Aakash Gurung directed the project and takes responsibility for the
mathematical result.  Mathematical exploration, manuscript preparation, and
Lean formalization were AI-assisted using OpenAI ChatGPT, Codex, and Aristotle
(Harmonic).  The resulting formalization was rebuilt and audited for
compilation, theorem scope, and assumptions.  No independent human expert Lean
review has yet been conducted.

## Licence

The submitted repository snapshot is licensed under Apache-2.0; see
[`LICENSE`](LICENSE).  Cited books, web pages, Mathlib, and other dependencies
retain their own licences.
