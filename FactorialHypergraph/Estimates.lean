/-
# Elementary estimates

Elementary real-analytic estimates used in several places.  Everything in this file is
proved from scratch (or directly from mathlib); no analytic number theory is used.
-/
import Mathlib

namespace FactorialHypergraph

open Finset

/-! ## A Stirling-type lower bound for factorials -/

/-- `nⁿ / eⁿ ≤ n!`, an elementary consequence of `nⁿ/n! ≤ eⁿ`. -/
theorem pow_div_exp_le_factorial (n : ℕ) :
    ((n : ℝ) ^ n) / Real.exp n ≤ (n.factorial : ℝ) := by
  have hsum : ∑ i ∈ Finset.range (n + 1), ((n : ℝ) ^ i / (i.factorial : ℝ)) ≤ Real.exp n :=
    Real.sum_le_exp_of_nonneg (by positivity) (n + 1)
  have hterm : ((n : ℝ) ^ n / (n.factorial : ℝ))
      ≤ ∑ i ∈ Finset.range (n + 1), ((n : ℝ) ^ i / (i.factorial : ℝ)) := by
    refine Finset.single_le_sum (f := fun i => ((n : ℝ) ^ i / (i.factorial : ℝ))) ?_ ?_
    · intro i _
      positivity
    · simp
  have h : ((n : ℝ) ^ n / (n.factorial : ℝ)) ≤ Real.exp n := le_trans hterm hsum
  have hfac : (0 : ℝ) < (n.factorial : ℝ) := by
    exact_mod_cast n.factorial_pos
  rw [div_le_iff₀ (Real.exp_pos _)]
  rw [div_le_iff₀ hfac] at h
  linarith [h]

/-- `log (n!) ≥ n log n - n`. -/
theorem log_factorial_ge (n : ℕ) :
    (n : ℝ) * Real.log n - n ≤ Real.log (n.factorial : ℝ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := pow_div_exp_le_factorial n
  have hpos : (0 : ℝ) < ((n : ℝ) ^ n) / Real.exp n := by positivity
  have := Real.log_le_log hpos h
  calc (n : ℝ) * Real.log n - n
      = Real.log (((n : ℝ) ^ n) / Real.exp n) := by
        rw [Real.log_div (by positivity) (Real.exp_ne_zero _), Real.log_pow, Real.log_exp]
    _ ≤ Real.log (n.factorial : ℝ) := this

/-- `log ((L+1)!) ≥ L log L - 2L` for `L ≥ 1`. -/
theorem log_factorial_succ_ge {L : ℕ} (hL : 1 ≤ L) :
    (L : ℝ) * Real.log L - 2 * L ≤ Real.log (((L + 1).factorial : ℝ)) := by
  have h := log_factorial_ge (L + 1)
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hmono : (L : ℝ) * Real.log L ≤ ((L : ℝ) + 1) * Real.log ((L : ℝ) + 1) := by
    have h1 : Real.log (L : ℝ) ≤ Real.log ((L : ℝ) + 1) :=
      Real.log_le_log (by linarith) (by linarith)
    have h2 : (0 : ℝ) ≤ Real.log ((L : ℝ) + 1) := Real.log_nonneg (by linarith)
    nlinarith
  push_cast at h
  linarith

/-- `2 L³ ≤ L!` for `L ≥ 8`; used to check that the primes selected by the construction
are smaller than `L!`, as required by the definition of a rainbow edge cover. -/
theorem two_mul_cube_le_factorial {L : ℕ} (hL : 8 ≤ L) : 2 * L ^ 3 ≤ L.factorial := by
  induction L with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge n 8 with hn | hn
    · have hn7 : n = 7 := by omega
      subst hn7
      norm_num [Nat.factorial]
    · have h := ih (by omega)
      rw [Nat.factorial_succ]
      have hkey : (n + 1) ^ 2 ≤ n ^ 3 := by nlinarith
      have hcube : 2 * (n + 1) ^ 3 ≤ (n + 1) * (2 * n ^ 3) := by nlinarith
      exact le_trans hcube (Nat.mul_le_mul_left _ h)

/-! ## Logarithm bounds -/

/-- `log t ≤ 2 √t` for `t > 0`. -/
theorem log_le_two_sqrt {t : ℝ} (ht : 0 < t) : Real.log t ≤ 2 * Real.sqrt t := by
  have hsq : Real.sqrt t > 0 := Real.sqrt_pos.mpr ht
  have h1 : Real.log (Real.sqrt t) ≤ Real.sqrt t - 1 := Real.log_le_sub_one_of_pos hsq
  have h2 : Real.log (Real.sqrt t) = Real.log t / 2 := Real.log_sqrt (le_of_lt ht)
  linarith

/-- The elementary threshold inequality used in the weight bookkeeping of Proposition 5.1:
once `t ≥ (1840/a)²` one has `log 2 + log 21 + log t ≤ (a/80) t`. -/
theorem log_threshold_bound {a t : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (ht : (1840 / a) ^ 2 ≤ t) :
    Real.log 2 + Real.log 21 + Real.log t ≤ a / 80 * t := by
  have h1840 : 0 < 1840 / a := by positivity
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht
  set s := Real.sqrt t with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr ht0
  have hss : s ^ 2 = t := Real.sq_sqrt ht0.le
  have hsge : 1840 / a ≤ s := by
    have h := Real.sqrt_le_sqrt ht
    rwa [Real.sqrt_sq h1840.le] at h
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (x := (2 : ℝ)) (by norm_num)
    linarith
  have hlog21 : Real.log 21 ≤ 20 := by
    have := Real.log_le_sub_one_of_pos (x := (21 : ℝ)) (by norm_num)
    linarith
  have hlogt : Real.log t ≤ 2 * s := log_le_two_sqrt ht0
  have hbig : (1840 : ℝ) ≤ 1840 / a := by
    rw [le_div_iff₀ ha]; nlinarith
  have hs1 : (1840 : ℝ) ≤ s := le_trans hbig hsge
  have has : 1840 ≤ a * s := by
    rw [div_le_iff₀ ha] at hsge; linarith
  have hkey : 23 * s ≤ a / 80 * t := by
    rw [← hss]; nlinarith
  linarith

/-- `log (log x) ≤ 2 √(log x)` for `x > 1`. -/
theorem log_log_le_two_sqrt_log {x : ℝ} (hx : 1 < x) :
    Real.log (Real.log x) ≤ 2 * Real.sqrt (Real.log x) :=
  log_le_two_sqrt (Real.log_pos hx)

end FactorialHypergraph
