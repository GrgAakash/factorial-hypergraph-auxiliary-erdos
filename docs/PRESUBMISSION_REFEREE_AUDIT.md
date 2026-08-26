# Presubmission referee audit

Date: 2026-08-26

Three independent OpenAI Codex agents reviewed the package as hostile
presubmission referees.  They were assigned different criteria and did not edit
the files they reviewed.  These are agent reviews, not independent human expert
peer review.

## Consensus verdict after corrections

**PASS AT THE EXPLICITLY CONDITIONAL, ADAPTED SCOPE.**

No mathematical, kernel-level, or packaging defect was found in the selected
declaration.  The Lean theorem faithfully matches the quantitative conclusion
of Theorem 1.2 of the manuscript after unfolding `goodSet`, but it has the
explicit additional hypothesis `hs : UpperBoundSieveDimOne`.  The fundamental
lemma represented by that proposition is source-matched but is not itself
formalized in this project.  The package must not be described as an
unconditional or complete Lean proof of the manuscript theorem, and it does not
solve the original prime form of Erdos Problem 1059.

## Referee 1: mathematical fidelity

Verdict: **PASS**.

The referee checked the quantifier order, positive exponent, factorial scale,
lower bound, interval endpoints, roughness condition, factorial index range,
and compositeness predicate.  Each agrees with the manuscript:

| Clause | Manuscript | Lean |
|---|---|---|
| Quantifiers | `exists eta > 0, exists L0, forall L >= L0` | exact |
| Scale | `X = (L+1)!` | exact |
| Count | `X^eta / (100 log L)` | exact |
| Interval | `2L! < n <= (L+1)!` | `Finset.Ioc`, exact |
| Roughness | every prime divisor of `n` exceeds `L` | `IsRough`, exact |
| Indices | `1 <= k <= L` | exact |
| Composite | greater than one and not prime | exact over `Nat` |

Natural subtraction cannot truncate in the constructed set: `n > 2L!` and
`k! <= L!`.  The proof treats `k = 1` by parity and `2 <= k <= L` by an
explicit proper divisor.  The referee also independently checked that
Koukoulopoulos, Theorem 18.11(a), supplies the stated type of dimension-one
upper-bound sieve estimate without Axiom 3.

## Referee 2: Lean integrity

Verdict before the documentation correction: **PASS WITH REQUIRED FIX**;
verdict after correction: **PASS**, subject to the external Linux replay below.

The referee found:

- `Challenge.lean` imports only Mathlib and contains exactly one deliberate
  `sorry`, in the selected theorem.
- `Solution.lean` proves the identically typed theorem directly from
  `main_quantitative_of_sieve_theorem hs`.
- The Challenge and Solution versions of `sieveDivisors`,
  `UpperBoundSieveDimOne`, `IsRough`, and `goodSet` agree; binder-name changes
  are immaterial.  Comparator follows their declaration closure.
- No `admit`, custom axiom, unsafe declaration, placeholder opaque declaration,
  dependency cycle, or kernel-bypass metaprogram was found.
- The final declaration and its audited dependencies use only `propext`,
  `Classical.choice`, and `Quot.sound`.
- `UpperBoundSieveDimOne` is a general finite weighted sieve proposition, not
  the desired factorial conclusion in disguise.

This referee identified the empty-cover convention for `kappa` as a fidelity
divergence that had appeared only in a Lean docstring.  It is now disclosed in
`formalization.yaml`, the README, and the verification report.

## Referee 3: Palomar compliance and provenance

Verdict before the documentation correction: **PASS WITH REQUIRED FIXES**;
verdict after the local correction: **PASS**, subject to publication and the
external Linux replay below.

The referee confirmed the current metadata schema, toolchain minimum,
Challenge size and imports, manifest pins, Apache-2.0 licence, comparator
configuration, NanoDa setting, provenance disclosure, archive cleanliness, and
public-repository requirements.  The referee identified two previously omitted
but conclusion-preserving divergences: the transference exponent is halved by
the elementary primorial bound, and an unused baseline lemma uses `21` instead
of `20`.  Both are now disclosed throughout the public documentation.

## Complete known fidelity divergences

The public metadata now records all divergences found in the three reviews:

1. `UpperBoundSieveDimOne` is an explicit hypothesis rather than a theorem
   proved in Lean.
2. An intermediate large-prime-factor threshold is `(i log i)/40` rather than
   the manuscript's `(i log i)/8`; only the sufficiently-large threshold
   changes.
3. The Lean transference theorem gives `X^(eta/2)` instead of `X^eta`, using
   `W <= 4^L` instead of Mertens's product estimate.  The final theorem merely
   asserts existence of a positive exponent, so its statement is unchanged.
4. An unused singleton-baseline lemma uses `21` instead of `20` to absorb an
   integer ceiling.
5. The manuscript assigns `kappa(L) = +infinity` if the cover family is empty;
   Lean uses real `sInf`, which is zero on an empty family.  The selected proof
   constructs covers explicitly and never uses the empty case.

## Remaining external gate

The package is locally ready to publish, but it is not yet ready to send to the
Palomar form.  Publish this directory as the root of a standalone public GitHub
repository and require every Linux GitHub Actions job, especially
Comparator/NanoDa, to pass at the exact submitted commit.  The full
40-character commit SHA, rather than the local archive, is the object submitted
to Palomar.
