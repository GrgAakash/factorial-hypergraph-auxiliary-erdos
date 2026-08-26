import Mathlib

/-!
# Quantitative form of an auxiliary problem of Erdos

Erdos asked whether there are infinitely many primes `p` for which `p - k!`
is composite whenever `k! < p`.  The theorem recorded here concerns a
different, weaker problem that Erdos suggested alongside it.  For every
sufficiently large `L`, it produces many integers `n` between `2 * L!` and
`(L+1)!` such that every prime factor of `n` is greater than `L` and every
`n - k!`, for `1 <= k <= L`, is composite.

The conclusion is conditional in Lean on `UpperBoundSieveDimOne`, an explicit
finite weighted form of the standard dimension-one upper-bound sieve.  The
source match with Koukoulopoulos, *The Distribution of Prime Numbers*,
Theorem 18.11(a), is documented in `docs/SIEVE_SOURCE_AUDIT.md`.  The
fundamental lemma itself is not formalized in this project.

Nothing here asserts that `n` is prime.  In particular, this statement does
not solve the original Erdos prime problem (Erdos Problem 1059).
-/

namespace FactorialHypergraph

open Finset

/-- The squarefree products of primes belonging to `P`. -/
def sieveDivisors (P : Finset ℕ) : Finset ℕ :=
  P.powerset.image (fun t => ∏ l ∈ t, l)

open scoped Classical in
/--
The dimension-one upper-bound sieve used by the proof.

For constants `C1 >= 0`, `k >= 1`, and `0 < epsilon < 1`, this asserts a
uniform upper bound for a finite nonnegative weighted sifted set.  The local
density `rho` is multiplicative on squarefree products of the selected primes,
satisfies the displayed dimension-one estimates, and is nondegenerate.  At
level `D >= z^10`, the sifted mass is bounded by a constant times its expected
main term plus the sum of the absolute remainder terms.
-/
def UpperBoundSieveDimOne : Prop :=
  ∀ C1 k epsilon : ℝ, 0 ≤ C1 → 1 ≤ k → 0 < epsilon → epsilon < 1 →
    ∃ C : ℝ, 0 < C ∧
      ∀ (A : Finset ℕ) (a : ℕ → ℝ) (P : Finset ℕ) (rho : ℕ → ℝ) (X z D : ℝ),
        (∀ n ∈ A, 0 < n) →
        (∀ n, 0 ≤ a n) →
        (∀ n, n ∉ A → a n = 0) →
        X = ∑ n ∈ A, a n →
        (∀ l ∈ P, Nat.Prime l) →
        (∀ l ∈ P, (l : ℝ) ≤ z) →
        (2 : ℝ) ≤ z →
        (∀ l ∈ P, 0 ≤ rho l) →
        (∀ l ∈ P, rho l ≤ k) →
        (∀ l ∈ P, rho l / (l : ℝ) ≤ 1 - epsilon) →
        (∀ t ⊆ P, rho (∏ l ∈ t, l) = ∏ l ∈ t, rho l) →
        (∀ w : ℝ, 2 ≤ w →
          ∑ l ∈ P with (((l : ℕ) : ℝ) ≤ w),
              rho l * Real.log l / (l : ℝ) ≤ Real.log w + C1) →
        (∀ w1 w2 : ℝ, 2 ≤ w1 → w1 ≤ w2 →
          ∑ l ∈ P with (w1 < ((l : ℕ) : ℝ) ∧ ((l : ℕ) : ℝ) ≤ w2),
              rho l * Real.log l / (l : ℝ)
            ≤ Real.log (w2 / w1) + C1) →
        z ^ (10 : ℕ) ≤ D →
        ∑ n ∈ A with (∀ l ∈ P, ¬ (l ∣ n)), a n
          ≤ C * (X * ∏ l ∈ P, (1 - rho l / (l : ℝ))
              + ∑ d ∈ sieveDivisors P with (((d : ℕ) : ℝ) ≤ D),
                  |(∑ n ∈ A with (d ∣ n), a n) - X * rho d / (d : ℝ)|)

/-- `n` is `L`-rough: every prime divisor of `n` is greater than `L`. -/
def IsRough (L n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → L < p

open scoped Classical in
/--
The finite set counted in the theorem.  It consists of the integers
`n` in `(2 * L!, (L+1)!]` that are `L`-rough and for which every difference
`n - k!`, `1 <= k <= L`, is a composite integer greater than one.
-/
noncomputable def goodSet (L : ℕ) : Finset ℕ :=
  (Finset.Ioc (2 * L.factorial) ((L + 1).factorial)).filter
    (fun n => IsRough L n ∧
      ∀ k, 1 ≤ k → k ≤ L → ¬ (n - k.factorial).Prime ∧ 1 < n - k.factorial)

namespace Palomar

/--
Assuming the standard dimension-one upper-bound sieve, there is an absolute
`eta > 0` such that, for every sufficiently large `L`, at least

`((L+1)!)^eta / (100 * log L)`

integers belong to `goodSet L`.
-/
theorem quantitative_auxiliary_erdos (hs : UpperBoundSieveDimOne) :
    ∃ eta : ℝ, 0 < eta ∧ ∃ L0 : ℕ, ∀ L : ℕ, L0 ≤ L →
      ((L + 1).factorial : ℝ) ^ eta / (100 * Real.log L)
        ≤ ((goodSet L).card : ℝ) := by
  sorry

end Palomar
end FactorialHypergraph
