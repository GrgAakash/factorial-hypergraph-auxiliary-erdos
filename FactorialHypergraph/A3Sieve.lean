/-
# A conventional dimension-one upper-bound sieve

This file contains **no** problem-specific statement.  It isolates, as a single `Prop`, the
standard *fundamental lemma of sieve theory* in its dimension-one upper-bound form, as it is
stated in the literature (Halberstam–Richert, *Sieve Methods*, Theorem 2.2; Koukoulopoulos,
*The distribution of prime numbers*, Theorem 18.11(a), with `κ = 1` and `u = 10`;
Friedlander–Iwaniec, *Opera de Cribro*, Theorem 6.9).

The pinned mathlib revision (see `REPORT_A3.md`) contains only the *framework* of the Selberg
sieve (`Mathlib/NumberTheory/SelbergSieve.lean`: `BoundingSieve`, `SelbergSieve`,
`IsUpperMoebius`, `siftedSum_le_mainSum_errSum_of_upperMoebius`).  It contains **no** theorem
producing a dimension-one upper bound for the sifted sum, i.e. no fundamental lemma and no
diagonalisation of the Selberg quadratic form.  Consequently the estimate below cannot be
derived from mathlib, and it is carried as an explicit hypothesis, in the same way as
`WienerIkeharaTheorem` in `FactorialHypergraph/PrimeCountingUpper.lean`.  It is a `Prop`-valued
argument of the theorems that use it, never an axiom.

The statement below is *strictly more general* than any use made of it here: it quantifies
over an arbitrary finite weighted set, an arbitrary finite set of primes, an arbitrary local
density, and arbitrary parameters; the constant produced depends only on the three absolute
constants `C₁` (dimension), `k` (bound for the local density) and `ε` (local
non-degeneracy).  Nothing about the quadratic `f(t) = t² + 3t + 1`, about `rootCount`, or
about the sets `E_α(L)` of the manuscript occurs in it.

**Audit note (sieve-interface audit, `REPORT_SIEVE_INTERFACE_AUDIT.md`).**  The dimension
hypothesis is stated in *two* forms, both of which the application verifies unconditionally:

* the *anchored* form `∑_{ℓ ∈ P, ℓ ≤ w} g(ℓ) log ℓ ≤ log w + C₁` for `w ≥ 2`, and
* the *interval* form `∑_{ℓ ∈ P, w₁ < ℓ ≤ w₂} g(ℓ) log ℓ ≤ log (w₂/w₁) + C₁` for
  `2 ≤ w₁ ≤ w₂`,

where `g(ℓ) = rho ℓ / ℓ`.  Only the interval form controls the *local* dimension of the
sieve, and it is the form that the cited sources use (their Axiom 2/2′, resp. their
condition on `∏_{w₁ ≤ p < w₂} (1 - g(p))⁻¹`).  The anchored form alone does **not** imply
it: a density equal to `2/ℓ` on `(√z, z]` and `0` below satisfies the anchored bound with
`κ = 1` while having local dimension `2` on `(√z, z]`.  Assuming both keeps the interface
no stronger than the cited theorem.

**Source-match note (external-source audit, `REPORT_SIEVE_INTERFACE_AUDIT.md`).**  The
statement below has been matched, hypothesis by hypothesis, against Koukoulopoulos,
*The Distribution of Prime Numbers* (author-hosted preliminary version, made available with
permission of the AMS), Axioms 1 and 2 (printed pp. 185, 187) and Theorem 18.11(a) (printed
p. 190), specialised to `κ = 1` and the fixed value `u = 10`.  Theorem 18.11(a), unlike part
(b), does not use Axiom 3, so no level-of-distribution estimate — and in particular nothing
resembling (A3) — is hidden in the hypotheses.  The interval hypothesis below implies the
book's Axiom 2 with `κ = 1` and a constant depending only on `(C₁, k, ε)`; the anchored
hypothesis is *redundant* (`dim_anchored_of_interval`,
`upperBoundSieveDimOne_iff_interval` in `FactorialHypergraph/A3SieveAudit.lean`), and the case of
an empty prime set, for which the book's `y = max P` is undefined, is proved outright
(`sieve_conclusion_of_empty`).  The fundamental lemma itself is **not** formalized here.
-/
import Mathlib

namespace FactorialHypergraph

open Finset

/-- The set of squarefree numbers that are products of primes of `P`, i.e. the divisors of
`∏_{ℓ ∈ P} ℓ`. -/
def sieveDivisors (P : Finset ℕ) : Finset ℕ := P.powerset.image (fun t => ∏ ℓ ∈ t, ℓ)

open scoped Classical in
/-- **The dimension-one upper-bound sieve (fundamental lemma).**

For all absolute constants `C₁ ≥ 0`, `k ≥ 1` and `0 < ε < 1` there is an absolute constant
`C > 0` with the following property.  Let

* `A` be a finite set of positive integers weighted by `a : ℕ → ℝ` with `a ≥ 0`, vanishing off
  `A`, of total mass `X = ∑_{n ∈ A} a n`;
* `P` a finite set of primes, all at most `z ≥ 2`;
* `rho : ℕ → ℝ` a local density which is multiplicative on the squarefree products of primes
  of `P` and satisfies `0 ≤ rho ℓ ≤ k`, `rho ℓ / ℓ ≤ 1 - ε` for `ℓ ∈ P`;
* the *dimension-one conditions* (anchored and interval form)
  `∑_{ℓ ∈ P, ℓ ≤ w} rho ℓ · log ℓ / ℓ ≤ log w + C₁` for all `w ≥ 2` and
  `∑_{ℓ ∈ P, w₁ < ℓ ≤ w₂} rho ℓ · log ℓ / ℓ ≤ log (w₂/w₁) + C₁` for all `2 ≤ w₁ ≤ w₂`;
* `D ≥ z ^ 10` a level of distribution.

Then the sifted sum is bounded by `C` times the main term `X · ∏_{ℓ ∈ P} (1 - rho ℓ / ℓ)` plus
the remainder sum `∑_{d ≤ D, d | ∏ P} |∑_{n ∈ A, d | n} a n - X · rho d / d|`. -/
def UpperBoundSieveDimOne : Prop :=
  ∀ C₁ k ε : ℝ, 0 ≤ C₁ → 1 ≤ k → 0 < ε → ε < 1 →
    ∃ C : ℝ, 0 < C ∧
      ∀ (A : Finset ℕ) (a : ℕ → ℝ) (P : Finset ℕ) (rho : ℕ → ℝ) (X z D : ℝ),
        (∀ n ∈ A, 0 < n) →
        (∀ n, 0 ≤ a n) →
        (∀ n, n ∉ A → a n = 0) →
        X = ∑ n ∈ A, a n →
        (∀ ℓ ∈ P, Nat.Prime ℓ) →
        (∀ ℓ ∈ P, (ℓ : ℝ) ≤ z) →
        (2 : ℝ) ≤ z →
        (∀ ℓ ∈ P, 0 ≤ rho ℓ) →
        (∀ ℓ ∈ P, rho ℓ ≤ k) →
        (∀ ℓ ∈ P, rho ℓ / (ℓ : ℝ) ≤ 1 - ε) →
        (∀ t ⊆ P, rho (∏ ℓ ∈ t, ℓ) = ∏ ℓ ∈ t, rho ℓ) →
        (∀ w : ℝ, 2 ≤ w →
          ∑ ℓ ∈ P with (((ℓ : ℕ) : ℝ) ≤ w), rho ℓ * Real.log ℓ / (ℓ : ℝ) ≤ Real.log w + C₁) →
        (∀ w₁ w₂ : ℝ, 2 ≤ w₁ → w₁ ≤ w₂ →
          ∑ ℓ ∈ P with (w₁ < ((ℓ : ℕ) : ℝ) ∧ ((ℓ : ℕ) : ℝ) ≤ w₂),
              rho ℓ * Real.log ℓ / (ℓ : ℝ)
            ≤ Real.log (w₂ / w₁) + C₁) →
        z ^ (10 : ℕ) ≤ D →
        ∑ n ∈ A with (∀ ℓ ∈ P, ¬ (ℓ ∣ n)), a n
          ≤ C * (X * ∏ ℓ ∈ P, (1 - rho ℓ / (ℓ : ℝ))
              + ∑ d ∈ sieveDivisors P with (((d : ℕ) : ℝ) ≤ D),
                  |(∑ n ∈ A with (d ∣ n), a n) - X * rho d / (d : ℝ)|)

end FactorialHypergraph
