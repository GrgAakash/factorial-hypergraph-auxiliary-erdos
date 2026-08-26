# Verification record

## Supplied artifact

The substantive development was supplied as
`695331b0-ddba-4240-86c9-0cfb0ee68249-aristotle.tar.gz` with SHA-256

```text
024aa695fcedeeb0ebca0e65f8fb809f4ae95b7177c928079248ee6e2472460e
```

The archive contained Lean source, the pinned toolchain and manifest, reports,
and the accompanying manuscript.  It contained no Git metadata, so claims in
the supplied prose that work had been committed or pushed were not independently
verifiable from the archive.

## Independent clean build

The archive was extracted into a fresh temporary directory.  The official
Mathlib binary cache for the pinned revision was downloaded, after which

```text
lake build
```

completed successfully with 8056 jobs under:

```text
Lean:    leanprover/lean4:v4.28.0
Mathlib: 8f9d9cff6bd728b17a24e163c9402775d9e6a365
```

The original archive emitted fifteen nonfatal style-linter warnings.  They
concerned unused variables or tactics and did not affect proof correctness.
The Palomar package removes those warnings.

## Palomar package build

The reorganized package was then built from its declared targets.  The
following commands all completed successfully with the pinned toolchain and
manifest:

```text
lake build Challenge
lake build Solution
lake build
```

The full build completed 8059 jobs.  `Challenge.lean` emitted the single
expected warning for its deliberate theorem hole; the proof development and
`Solution.lean` emitted no style-linter warnings.  The concrete check in
`FactorialHypergraph/Example329.lean` was included in the successful full
build.

The current Palomar metadata loader accepted `formalization.yaml`, the bundled
Ruby validator accepted it with no template sentinels, and the current Palomar
comparator-config loader accepted `comparator.json`.  The sandboxed
Comparator/NanoDa job itself is intended to run in the Linux GitHub Actions
workflow after the repository is published; it was not run locally on macOS.

## Claim and dependency audit

The final quantitative result has the explicit parameter

```lean
hs : UpperBoundSieveDimOne
```

and therefore does not hide the one classical theorem that remains outside the
Lean development.  The final theorem concerns `L`-rough integers and does not
assert that those integers are prime.  It does not prove Erdos Problem 1059.

The downstream large-prime-factor argument is unconditional in Lean at the
threshold `(i log i)/40`; the optional `(i log i)/8` version remains conditional
on a sharper prime-counting estimate and is not used by the compared theorem.
Wiener-Ikehara is likewise absent from the dependency chain of the compared
theorem.

The Lean transference theorem uses the elementary primorial estimate `W <=
4^L` and consequently produces an intermediate exponent `eta/2` in place of
the manuscript's `eta`.  The final result quantifies existentially over a
positive exponent, so this rescaling does not alter the compared statement.
An unused singleton-baseline lemma absorbs an integer ceiling by using `21`
where the manuscript writes `20`; it is not referenced by the final proof.
The manuscript's convention `kappa(L) = +infinity` for an empty cover family
is represented in Lean by real `sInf`, which is zero on the empty set.  The
selected theorem constructs covers explicitly and never uses this empty case.

The detailed external-source comparison for `UpperBoundSieveDimOne` is in
[`SIEVE_SOURCE_AUDIT.md`](SIEVE_SOURCE_AUDIT.md).  That document explains the
one paper-level conversion from the Lean interval density condition to the
book's product-form sieve axiom; the fundamental lemma itself is not formalized
in Lean.

## Axiom and placeholder audit

The original source was searched for `sorry`, `admit`, `unsafe`, `opaque`, and
user-defined `axiom` declarations.  Matches occurred only in explanatory prose.
The `#print axioms` output for the final exported theorem reported exactly

```text
[propext, Classical.choice, Quot.sound]
```

In this Palomar package, `Challenge.lean` contains one deliberate `sorry` for
the compared theorem, as required by the Challenge/Solution protocol.  It is
excluded from `status.sorry_count`; Comparator verifies that the Solution proof
does not depend on `sorryAx`.
