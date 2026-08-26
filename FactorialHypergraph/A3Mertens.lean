/-
# Mertens' second theorem in arithmetic progressions

This file isolates, as a single `Prop`, the classical estimate

  `∑_{p ≤ N, p ≡ r (q)} 1/p = (log log N)/φ(q) + O_q(1)`,

**Mertens' second theorem for arithmetic progressions**, and derives from it the only
consequence needed for the sieve estimate (A3), namely the two-sided bound

  `∑_{p ≤ N, χ₅(p) = 1} 1/p = (log log N)/2 + O(1)`.

The file `FactorialHypergraph/MertensRoots.lean` proves *unconditionally* the one-sided,
logarithmically weighted estimate

  `∑_{p ≤ N} ρ(p) log p/(p-1) ≤ log N + C`

(`mertensRoots_unconditional`).  That estimate does **not** imply the reciprocal-prime
asymptotic above: it is one-sided, and the weight `log p` cannot be removed by partial
summation without a two-sided input.  It is used below only where a one-sided weighted bound
suffices (the dimension condition of the sieve).

The pinned mathlib revision contains Mertens' estimates only in the weighted, unrestricted
form (`Mathlib/NumberTheory/Chebyshev.lean`, `Mathlib/NumberTheory/VonMangoldt.lean`); it has
no Mertens theorem for arithmetic progressions and no `∑_{p ≤ x} 1/p` asymptotic.  See
`REPORT_A3.md` for the search record.
-/
import FactorialHypergraph.MertensSecond

namespace FactorialHypergraph

open Finset

/-- **Mertens' second theorem for arithmetic progressions.**  For every modulus `q ≥ 1` and
every residue `r` coprime to `q` there is a constant `C = C(q, r)` with

  `|∑_{p ≤ N, p ≡ r (mod q)} 1/p - (log log N)/φ(q)| ≤ C`  for all `N ≥ 3`.

(Classical; a standard consequence of the prime number theorem for arithmetic progressions,
or of Dirichlet's theorem together with partial summation.  Absent from the pinned mathlib
revision.) -/
def MertensProgressions : Prop :=
  ∀ q r : ℕ, 0 < q → Nat.Coprime r q →
    ∃ C : ℝ, ∀ N : ℕ, 3 ≤ N →
      |(∑ p ∈ Finset.Icc 1 N with (Nat.Prime p ∧ p % q = r % q), (1 : ℝ) / p)
        - Real.log (Real.log N) / (q.totient : ℝ)| ≤ C

/-- The primes counted by `χ₅ = 1` are exactly those in the two residue classes `±1 (mod 5)`. -/
theorem chi5_eq_one_iff (n : ℕ) : chi5 n = 1 ↔ (n % 5 = 1 ∨ n % 5 = 4) := by
  unfold chi5
  have h : n % 5 < 5 := Nat.mod_lt _ (by norm_num)
  interval_cases h5 : (n % 5) <;> norm_num

/-- Every prime `p` with `χ₅(p) = 1` satisfies `p ≥ 11`. -/
theorem eleven_le_of_chi5_eq_one {p : ℕ} (hp : p.Prime) (h : chi5 p = 1) : 11 ≤ p := by
  by_contra hlt
  push_neg at hlt
  interval_cases p <;> simp_all (config := { decide := true }) [chi5_eq_one_iff]

/-- **The Mertens input in the form used below.**  Conditional on `MertensProgressions`, the
sum of the reciprocals of the primes `p ≤ N` with `χ₅(p) = 1` is `(log log N)/2 + O(1)`. -/
theorem sum_inv_primes_chi5_of_progressions (h : MertensProgressions) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 3 ≤ N →
      |(∑ p ∈ Finset.Icc 1 N with (Nat.Prime p ∧ chi5 p = 1), (1 : ℝ) / p)
        - Real.log (Real.log N) / 2| ≤ C := by
  classical
  obtain ⟨C1, h1⟩ := h 5 1 (by norm_num) (by decide)
  obtain ⟨C4, h4⟩ := h 5 4 (by norm_num) (by decide)
  refine ⟨|C1| + |C4|, by positivity, ?_⟩
  intro N hN
  have hsplit : (∑ p ∈ Finset.Icc 1 N with (Nat.Prime p ∧ chi5 p = 1), (1 : ℝ) / p)
      = (∑ p ∈ Finset.Icc 1 N with (Nat.Prime p ∧ p % 5 = 1 % 5), (1 : ℝ) / p)
      + (∑ p ∈ Finset.Icc 1 N with (Nat.Prime p ∧ p % 5 = 4 % 5), (1 : ℝ) / p) := by
    simp only [Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    have hc := chi5_eq_one_iff p
    by_cases hp : Nat.Prime p
    · simp only [hp, true_and]
      norm_num
      by_cases h1' : p % 5 = 1
      · rw [if_pos (hc.mpr (Or.inl h1')), if_pos h1', if_neg (by omega)]
        ring
      · by_cases h4' : p % 5 = 4
        · rw [if_pos (hc.mpr (Or.inr h4')), if_neg h1', if_pos h4']
          ring
        · rw [if_neg (fun hcon => by rcases hc.mp hcon with h | h <;> omega), if_neg h1',
            if_neg h4']
          ring
    · simp [hp]
  have ht : (5:ℕ).totient = 4 := by decide
  have e1 := h1 N hN
  have e4 := h4 N hN
  rw [ht] at e1 e4
  rw [hsplit, abs_le]
  have hhalf : Real.log (Real.log N) / (4:ℝ) + Real.log (Real.log N) / 4
      = Real.log (Real.log N) / 2 := by ring
  constructor
  · have a1 := (abs_le.mp e1).1
    have a4 := (abs_le.mp e4).1
    have b1 : -|C1| ≤ -C1 := by simp [neg_le_neg_iff, le_abs_self]
    have b4 : -|C4| ≤ -C4 := by simp [neg_le_neg_iff, le_abs_self]
    linarith
  · have a1 := (abs_le.mp e1).2
    have a4 := (abs_le.mp e4).2
    have b1 : C1 ≤ |C1| := le_abs_self C1
    have b4 : C4 ≤ |C4| := le_abs_self C4
    linarith

/-- **The Mertens input is unconditional.**  `FactorialHypergraph/MertensSecond.lean` proves
`sum_inv_primes_chi5_unconditional`, i.e. exactly the statement above with no hypothesis, by
an elementary argument (Mertens' first theorem in both directions, the elementary bound
`|∑_{n ≤ N} χ₅(n)Λ(n)/n| ≤ C`, and summation by parts).  Consequently the hypothesis
`MertensProgressions` is **no longer used anywhere** in the development: it is kept only as a
record of what the manuscript's proof appeals to, and the sieve estimate (A3) now depends on
the sieve theorem `UpperBoundSieveDimOne` alone. -/
theorem sum_inv_primes_chi5 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 3 ≤ N →
      |(∑ p ∈ Finset.Icc 1 N with (Nat.Prime p ∧ chi5 p = 1), (1 : ℝ) / p)
        - Real.log (Real.log N) / 2| ≤ C :=
  sum_inv_primes_chi5_unconditional

end FactorialHypergraph
