/-
# A Chebyshev-type lower bound and the prime supply input (A1)

This file discharges the first analytic input `AnalyticInputs.primeSupply` of
`AnalyticInputs.lean` **unconditionally**.

The manuscript deduces the supply of primes in `(L, 20 L log L]` from the prime number
theorem, which is not available in mathlib.  Mathlib provides only the Chebyshev *upper*
bound `Chebyshev.eventually_primeCounting_le` for the prime counting function, so the
required lower bound is proved here from scratch by the elementary central binomial
coefficient argument:

* `centralBinom_le_pow`: `C(2n, n) ≤ (2n)^{π(2n)}`, since every prime power exactly
  dividing `C(2n, n)` is at most `2n` (mathlib's `Nat.pow_factorization_choose_le`);
* combined with mathlib's `Nat.four_pow_lt_mul_centralBinom` (`4^n < n · C(2n,n)`) this
  gives `n log 4 < log n + π(2n) log (2n)`, i.e. a Chebyshev lower bound
  `π(x) ≫ x / log x`;
* `prime_supply`: at least `2L` primes lie in `(L, ⌈20 L log L⌉]` for all large `L`.

No analytic input beyond mathlib is used, and no axioms are introduced.
-/
import FactorialHypergraph.AnalyticInputs

namespace FactorialHypergraph

open Finset

/-- `π(B)`, the number of primes not exceeding `B`. -/
def piCard (B : ℕ) : ℕ := ((Finset.range (B + 1)).filter Nat.Prime).card

/-! ## The central binomial coefficient bound -/

/-- `C(2n, n) ≤ (2n)^{π(2n)}`: the central binomial coefficient is the product of its
prime power divisors, each of which is at most `2n`. -/
theorem centralBinom_le_pow (n : ℕ) (hn : 0 < n) :
    n.centralBinom ≤ (2 * n) ^ piCard (2 * n) := by
  classical
  set S := (Finset.range (2 * n + 1)).filter
    (fun p => (n.centralBinom).factorization p ≠ 0) with hS
  have hsub : S ⊆ Finset.range (2 * n + 1) := by rw [hS]; exact Finset.filter_subset _ _
  have h1 : (∏ p ∈ S, p ^ (n.centralBinom).factorization p) = n.centralBinom := by
    refine Eq.trans ?_ (Nat.prod_pow_factorization_centralBinom n)
    refine Finset.prod_subset hsub ?_
    intro p hp hpS
    simp only [hS, Finset.mem_filter, not_and, not_not] at hpS
    rw [hpS hp, pow_zero]
  have h2 : ∀ p ∈ S, p ^ (n.centralBinom).factorization p ≤ 2 * n := by
    intro p _
    have := Nat.pow_factorization_choose_le (p := p) (n := 2 * n) (k := n) (by omega)
    simpa [Nat.centralBinom] using this
  have h3 : S ⊆ (Finset.range (2 * n + 1)).filter Nat.Prime := by
    intro p hp
    simp only [hS, Finset.mem_filter, Finset.mem_range] at hp ⊢
    refine ⟨hp.1, ?_⟩
    by_contra hnp
    exact hp.2 (Nat.factorization_eq_zero_of_not_prime _ hnp)
  calc n.centralBinom = ∏ p ∈ S, p ^ (n.centralBinom).factorization p := h1.symm
    _ ≤ ∏ _p ∈ S, (2 * n) := Finset.prod_le_prod' h2
    _ = (2 * n) ^ S.card := by rw [Finset.prod_const]
    _ ≤ (2 * n) ^ piCard (2 * n) :=
        Nat.pow_le_pow_right (by omega) (Finset.card_le_card h3)

/-- **Chebyshev-type lower bound**, logarithmic form:
`n log 4 < log n + π(2n) log(2n)` for `n ≥ 4`. -/
theorem chebyshev_log_lower {n : ℕ} (hn : 4 ≤ n) :
    (n : ℝ) * Real.log 4 < Real.log n + (piCard (2 * n) : ℝ) * Real.log ((2 * n : ℕ) : ℝ) := by
  have hcb : n.centralBinom ≤ (2 * n) ^ piCard (2 * n) := centralBinom_le_pow n (by omega)
  have h1 : 4 ^ n < n * n.centralBinom := Nat.four_pow_lt_mul_centralBinom n hn
  have h3 : (4 : ℕ) ^ n < n * (2 * n) ^ piCard (2 * n) :=
    lt_of_lt_of_le h1 (Nat.mul_le_mul_left n hcb)
  have h4 : ((4 : ℝ)) ^ n < (n : ℝ) * ((2 * n : ℕ) : ℝ) ^ piCard (2 * n) := by
    exact_mod_cast h3
  have h5 := Real.log_lt_log (by positivity) h4
  rw [Real.log_pow] at h5
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : (0 : ℕ) < n := by omega
    exact_mod_cast this
  have h6 : Real.log ((n : ℝ) * ((2 * n : ℕ) : ℝ) ^ piCard (2 * n))
      = Real.log n + (piCard (2 * n) : ℝ) * Real.log ((2 * n : ℕ) : ℝ) := by
    rw [Real.log_mul (ne_of_gt hnpos) (by positivity), Real.log_pow]
  rw [h6] at h5
  push_cast at h5 ⊢
  linarith

/-! ## Counting the primes in an interval -/

/-- All primes up to `B` are either at most `L` or lie in `(L, B]`. -/
theorem piCard_le_add_primesIn (L B : ℕ) : piCard B ≤ (L + 1) + (primesIn L B).card := by
  classical
  have hsub : (Finset.range (B + 1)).filter Nat.Prime
      ⊆ Finset.range (L + 1) ∪ primesIn L B := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_range] at hp
    rcases Nat.lt_or_ge L p with hlt | hle
    · exact Finset.mem_union_right _ (mem_primesIn.mpr ⟨⟨hlt, by omega⟩, hp.2⟩)
    · exact Finset.mem_union_left _ (Finset.mem_range.mpr (by omega))
  calc piCard B ≤ (Finset.range (L + 1) ∪ primesIn L B).card := Finset.card_le_card hsub
    _ ≤ (Finset.range (L + 1)).card + (primesIn L B).card := Finset.card_union_le _ _
    _ = (L + 1) + (primesIn L B).card := by rw [Finset.card_range]

/-- `π` is monotone. -/
theorem piCard_mono {a b : ℕ} (hab : a ≤ b) : piCard a ≤ piCard b := by
  refine Finset.card_le_card ?_
  intro p hp
  rw [Finset.mem_filter, Finset.mem_range] at hp ⊢
  exact ⟨by omega, hp.2⟩

/-! ## The prime supply input (A1), unconditionally -/

set_option maxHeartbeats 1000000 in
/-- **The analytic input (A1) of the manuscript, proved unconditionally.**
For all sufficiently large `L` there are at least `2L` primes in `(L, ⌈20 L log L⌉]`.

The manuscript deduces this from the prime number theorem; the proof given here uses only
the elementary Chebyshev-type lower bound `chebyshev_log_lower`. -/
theorem prime_supply :
    ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L →
      2 * L ≤ (primesIn L ⌈20 * (L : ℝ) * Real.log L⌉₊).card := by
  refine ⟨⌈Real.exp 100⌉₊, ?_⟩
  intro L hL
  have hexpL : Real.exp 100 ≤ (L : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hL)
  have hLpos : (0 : ℝ) < (L : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hexpL
  have hlogL : (100 : ℝ) ≤ Real.log L := by
    have := Real.log_le_log (Real.exp_pos _) hexpL
    rwa [Real.log_exp] at this
  have hL100 : (100 : ℝ) ≤ (L : ℝ) := by
    have h1 : (100 : ℝ) ≤ Real.exp 100 := by
      have := Real.add_one_le_exp (100 : ℝ)
      linarith
    linarith
  set t : ℝ := Real.log L with ht
  set B : ℕ := ⌈20 * (L : ℝ) * t⌉₊ with hB
  have hBlow : 20 * (L : ℝ) * t ≤ (B : ℝ) := Nat.le_ceil _
  have hBup : (B : ℝ) < 20 * (L : ℝ) * t + 1 := Nat.ceil_lt_add_one (by positivity)
  have hLt : (10000 : ℝ) ≤ (L : ℝ) * t := by nlinarith
  have hBbig : (200000 : ℝ) ≤ (B : ℝ) := by nlinarith
  have hBnat : 8 ≤ B := by
    by_contra hcon
    push_neg at hcon
    have : (B : ℝ) < 8 := by exact_mod_cast hcon
    linarith
  set n : ℕ := B / 2 with hn
  have hn2 : 2 * n ≤ B := by omega
  have hn2' : B ≤ 2 * n + 1 := by omega
  have hn4 : 4 ≤ n := by omega
  have hnR : (10 : ℝ) * (L : ℝ) * t - 1 ≤ (n : ℝ) := by
    have h1 : ((2 * n : ℕ) : ℝ) ≥ (B : ℝ) - 1 := by
      have : (B : ℕ) ≤ 2 * n + 1 := hn2'
      have hcast : ((B : ℕ) : ℝ) ≤ ((2 * n : ℕ) : ℝ) + 1 := by exact_mod_cast this
      linarith
    push_cast at h1
    linarith
  have h2nup : ((2 * n : ℕ) : ℝ) ≤ 21 * (L : ℝ) * t := by
    have h1 : ((2 * n : ℕ) : ℝ) ≤ (B : ℝ) := by exact_mod_cast hn2
    nlinarith
  have h2npos : (0 : ℝ) < ((2 * n : ℕ) : ℝ) := by
    have : (0 : ℕ) < 2 * n := by omega
    exact_mod_cast this
  -- `log (2n) ≤ 3 log L`
  have hlog21 : Real.log 21 ≤ 20 := by
    have := Real.log_le_sub_one_of_pos (x := (21 : ℝ)) (by norm_num)
    linarith
  have hloglog : Real.log t ≤ 2 * Real.sqrt t := log_le_two_sqrt (by linarith)
  have hsqrt : Real.sqrt t ≤ t / 10 := by
    have hts : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt (by linarith)
    have h100 : Real.sqrt 100 = 10 := by
      rw [show (100 : ℝ) = 10 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    have h10 : (10 : ℝ) ≤ Real.sqrt t := by
      have := Real.sqrt_le_sqrt (show (100 : ℝ) ≤ t by linarith)
      rwa [h100] at this
    nlinarith [hts, h10]
  have hlog2n : Real.log ((2 * n : ℕ) : ℝ) ≤ 3 * t := by
    have h1 : Real.log ((2 * n : ℕ) : ℝ) ≤ Real.log (21 * (L : ℝ) * t) :=
      Real.log_le_log h2npos h2nup
    have h2 : Real.log (21 * (L : ℝ) * t) = Real.log 21 + t + Real.log t := by
      rw [Real.log_mul (by positivity) (by linarith), Real.log_mul (by norm_num) (ne_of_gt hLpos)]
    linarith
  have hlog2npos : (0 : ℝ) < Real.log ((2 * n : ℕ) : ℝ) := by
    refine Real.log_pos ?_
    have : (2 : ℝ) ≤ ((2 * n : ℕ) : ℝ) := by
      have : (2 : ℕ) ≤ 2 * n := by omega
      exact_mod_cast this
    linarith
  have hlogn : Real.log (n : ℝ) ≤ 3 * t := by
    have h1 : (n : ℝ) ≤ ((2 * n : ℕ) : ℝ) := by
      have : n ≤ 2 * n := by omega
      exact_mod_cast this
    have hnpos : (0 : ℝ) < (n : ℝ) := by
      have : (0 : ℕ) < n := by omega
      exact_mod_cast this
    exact le_trans (Real.log_le_log hnpos h1) hlog2n
  -- the Chebyshev bound
  have hchev := chebyshev_log_lower hn4
  have hlog4 : (1.38 : ℝ) ≤ Real.log 4 := by
    have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast; ring
    linarith
  set P : ℕ := piCard (2 * n) with hP
  have hPnn : (0 : ℝ) ≤ (P : ℝ) := by positivity
  -- `P > 3L + 1`
  have hkey : (3 * (L : ℝ) + 1) * (3 * t) < (n : ℝ) * Real.log 4 - Real.log n := by
    have h1 : (10 * (L : ℝ) * t - 1) * 1.38 ≤ (n : ℝ) * Real.log 4 := by
      have hnpos : (0 : ℝ) ≤ (n : ℝ) := by positivity
      nlinarith [hnR, hlog4]
    nlinarith [hLt, hlogL, hL100]
  have hPbig : (3 * (L : ℝ) + 1) < (P : ℝ) := by
    have h1 : (P : ℝ) * Real.log ((2 * n : ℕ) : ℝ) > (n : ℝ) * Real.log 4 - Real.log n := by
      linarith [hchev]
    have h2 : (P : ℝ) * Real.log ((2 * n : ℕ) : ℝ) ≤ (P : ℝ) * (3 * t) :=
      mul_le_mul_of_nonneg_left hlog2n hPnn
    have h3 : (3 * (L : ℝ) + 1) * (3 * t) < (P : ℝ) * (3 * t) := by linarith
    have h4 : (0 : ℝ) < 3 * t := by linarith
    exact lt_of_mul_lt_mul_right (by linarith [h3]) (le_of_lt h4)
  have hPnat : 3 * L + 1 ≤ P := by
    have : ((3 * L + 1 : ℕ) : ℝ) < (P : ℝ) := by push_cast; linarith
    exact_mod_cast le_of_lt this
  -- conclude
  have hmono : P ≤ piCard B := piCard_mono hn2
  have hcount := piCard_le_add_primesIn L B
  omega

/-- Since the prime supply (A1) is now proved unconditionally, a bundle of analytic inputs
only requires the two remaining inputs (A2) and (A3). -/
theorem AnalyticInputs.of_two
    (h2 : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → (N : ℝ) / 5 ≤ ((largePrimeFactorSet N).card : ℝ))
    (h3 : ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∃ L₀ : ℕ, ∀ α : ℝ, 0 < α → α ≤ 1 / 2 →
      ∀ L : ℕ, L₀ ≤ L →
        ((smallCofactorSet α L).card : ℝ)
          ≤ C₀ * (α * L + (L : ℝ) / Real.log L + (L : ℝ) ^ ((1 + α) / 2) * (Real.log L) ^ 2)) :
    AnalyticInputs :=
  ⟨prime_supply, h2, h3⟩

end FactorialHypergraph
