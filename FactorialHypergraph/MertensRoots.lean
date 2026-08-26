/-
# The field `LargePrimeInputs.mertensRoots`, proved unconditionally

This file discharges the first field of the structure `LargePrimeInputs` of
`FactorialHypergraph/LargePrimeFactors.lean`, verbatim and with no extra hypothesis:

```
mertensRoots : ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
    ∑ p ∈ primesLE N, (rootCount p : ℝ) * Real.log p / ((p : ℝ) - 1) ≤ Real.log N + C
```

The proof combines:

* the identity `ρ(p) = 1 + χ₅(p)` for **every** prime `p` (`rootCount_eq_one_add_chi5`;
  the exceptional prime `p = 2` (`ρ = 0 = 1 + χ₅(2)`) is checked by direct computation, the
  remaining ones — including `p = 5`, where `ρ = 1` and `χ₅(5) = 0` — come from
  `card_rootsMod_eq_one_add_chi` of `QuadraticRoots.lean` together with
  `legendreSym 5 p = χ₅(p)`);
* the untwisted Mertens estimate `∑_{n ≤ N} Λ(n)/n ≤ log N + (log 4 + 4)`
  (`sum_vonMangoldt_div_le`, elementary, in `MertensAux.lean`);
* the character-twisted Mertens estimate `|∑_{n ≤ N} χ₅(n)Λ(n)/n| ≤ C`
  (`abs_U_le`, elementary, in `MertensCharacter.lean`);
* the convergent correction `∑_{p ≤ N} log p /(p(p-1)) ≤ C` (`sum_log_div_mul_pred_bounded`).

Note that only an *upper* bound is required and `1 + χ₅ ≥ 0`, so the prime-power terms of
the von Mangoldt sums may simply be discarded.
-/
import FactorialHypergraph.MertensCharacter

namespace FactorialHypergraph

open Finset

/-! ## `ρ(p) = 1 + χ₅(p)` -/

/-- `rootCount p` counts the roots of `f` in `ZMod p`. -/
theorem rootCount_eq_card_rootsMod (p : ℕ) [Fact p.Prime] :
    rootCount p = (rootsMod p).card := by
  classical
  have hp : 0 < p := (Fact.out : p.Prime).pos
  refine Finset.card_bij (fun a _ => (a : ZMod p)) ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_range] at ha
    simp only [rootsMod, Finset.mem_filter, Finset.mem_univ, true_and]
    have h0 : ((fq a : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr ha.2
    rw [fq] at h0
    push_cast at h0
    linear_combination h0
  · intro a ha b hb hab
    simp only [Finset.mem_filter, Finset.mem_range] at ha hb
    have h := (ZMod.natCast_eq_natCast_iff' a b p).mp hab
    rwa [Nat.mod_eq_of_lt ha.1, Nat.mod_eq_of_lt hb.1] at h
  · intro x hx
    simp only [rootsMod, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    refine ⟨x.val, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_range]
      refine ⟨ZMod.val_lt x, ?_⟩
      have hzero : ((fq x.val : ℕ) : ZMod p) = 0 := by
        rw [fq]
        push_cast
        rw [ZMod.natCast_val, ZMod.cast_id]
        linear_combination hx
      exact (ZMod.natCast_eq_zero_iff _ _).mp hzero
    · simp [ZMod.natCast_val, ZMod.cast_id]

/-- The Legendre symbol `(n/5)`, as a real number, is `χ₅(n)`. -/
theorem legendreSym_five_eq_chi5 (n : ℕ) : ((legendreSym 5 n : ℤ) : ℝ) = chi5 n := by
  have hmod : legendreSym 5 (n : ℤ) = legendreSym 5 ((n % 5 : ℕ) : ℤ) := by
    rw [legendreSym.mod 5 (n : ℤ)]
    norm_num [Int.natCast_mod]
  have h5 : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by omega
  rw [hmod]
  rcases h5 with h | h | h | h | h <;> rw [h] <;> norm_num [chi5, h]

/-- **Equation (3.5) for every prime.**  `ρ(p) = 1 + χ₅(p)`, including `p = 2` (`ρ = 0`)
and `p = 5` (`ρ = 1`). -/
theorem rootCount_eq_one_add_chi5 {p : ℕ} (hp : p.Prime) :
    (rootCount p : ℝ) = 1 + chi5 p := by
  rcases eq_or_ne p 2 with rfl | hp2
  · rw [show rootCount 2 = 0 by decide]
    norm_num [chi5]
  · haveI : Fact p.Prime := ⟨hp⟩
    have h := card_rootsMod_eq_one_add_chi p hp2
    have hR : (((rootsMod p).card : ℤ) : ℝ) = ((1 + legendreSym 5 p : ℤ) : ℝ) := by
      exact_mod_cast congrArg (fun k : ℤ => (k : ℝ)) h
    rw [rootCount_eq_card_rootsMod p]
    push_cast at hR ⊢
    rw [hR, legendreSym_five_eq_chi5 p]

/-! ## The estimate -/

/-- **The field `LargePrimeInputs.mertensRoots`, verbatim, proved unconditionally.** -/
theorem mertensRoots_unconditional :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
      ∑ p ∈ primesLE N, (rootCount p : ℝ) * Real.log p / ((p : ℝ) - 1)
        ≤ Real.log N + C := by
  obtain ⟨C₂, hC₂0, hC₂⟩ := sum_log_div_mul_pred_bounded
  have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  refine ⟨(Real.log 4 + 4) + 12 * (2 + 2 * (Real.log 4 + 4)) + 2 * C₂, by nlinarith, ?_⟩
  intro N hN
  -- split each term into the main part and the correction
  have hsplit : ∑ p ∈ primesLE N, (rootCount p : ℝ) * Real.log p / ((p : ℝ) - 1)
      = (∑ p ∈ primesLE N, (1 + chi5 p) * (Real.log p / p))
        + ∑ p ∈ primesLE N, (1 + chi5 p) * (Real.log p / ((p : ℝ) * ((p : ℝ) - 1))) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    obtain ⟨hpN, hpp⟩ := mem_primesLE.mp hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hp0 : (0 : ℝ) < p := by linarith
    have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    rw [rootCount_eq_one_add_chi5 hpp]
    field_simp
    ring
  -- the correction is bounded
  have hcorr : ∑ p ∈ primesLE N, (1 + chi5 p) * (Real.log p / ((p : ℝ) * ((p : ℝ) - 1)))
      ≤ 2 * C₂ := by
    have hle : ∀ p ∈ primesLE N,
        (1 + chi5 p) * (Real.log p / ((p : ℝ) * ((p : ℝ) - 1)))
          ≤ 2 * (Real.log p / ((p : ℝ) * ((p : ℝ) - 1))) := by
      intro p hp
      obtain ⟨hpN, hpp⟩ := mem_primesLE.mp hp
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
      have hnn : 0 ≤ Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) := by
        have h1 : (0 : ℝ) ≤ Real.log p := Real.log_nonneg (by linarith)
        have h2 : (0 : ℝ) < (p : ℝ) * ((p : ℝ) - 1) := by nlinarith
        positivity
      exact mul_le_mul_of_nonneg_right (chi5_one_add_le_two p) hnn
    calc ∑ p ∈ primesLE N, (1 + chi5 p) * (Real.log p / ((p : ℝ) * ((p : ℝ) - 1)))
        ≤ ∑ p ∈ primesLE N, 2 * (Real.log p / ((p : ℝ) * ((p : ℝ) - 1))) :=
          Finset.sum_le_sum hle
      _ = 2 * ∑ p ∈ primesLE N, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) := by
          rw [Finset.mul_sum]
      _ ≤ 2 * C₂ := by linarith [hC₂ N]
  -- the main part is dominated by the von Mangoldt sum
  have hsub : primesLE N ⊆ Finset.Icc 1 N := by
    intro p hp
    obtain ⟨hpN, hpp⟩ := mem_primesLE.mp hp
    exact Finset.mem_Icc.mpr ⟨hpp.one_lt.le.trans' (by norm_num), hpN⟩
  have hmain : ∑ p ∈ primesLE N, (1 + chi5 p) * (Real.log p / p)
      ≤ ∑ n ∈ Finset.Icc 1 N, (1 + chi5 n) * (ArithmeticFunction.vonMangoldt n / n) := by
    have heq : ∑ p ∈ primesLE N, (1 + chi5 p) * (Real.log p / p)
        = ∑ p ∈ primesLE N, (1 + chi5 p) * (ArithmeticFunction.vonMangoldt p / p) := by
      refine Finset.sum_congr rfl fun p hp => ?_
      obtain ⟨hpN, hpp⟩ := mem_primesLE.mp hp
      rw [ArithmeticFunction.vonMangoldt_apply_prime hpp]
    rw [heq]
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => ?_
    have h1 : 0 ≤ 1 + chi5 n := chi5_nonneg_one_add n
    have h2 : 0 ≤ ArithmeticFunction.vonMangoldt n / n := by
      have := ArithmeticFunction.vonMangoldt_nonneg (n := n)
      positivity
    exact mul_nonneg h1 h2
  -- expand the von Mangoldt sum
  have hexp : ∑ n ∈ Finset.Icc 1 N, (1 + chi5 n) * (ArithmeticFunction.vonMangoldt n / n)
      = (∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n / n) + U N := by
    rw [U, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  have hU : U N ≤ 12 * (2 + 2 * (Real.log 4 + 4)) :=
    le_trans (le_abs_self _) (abs_U_le N)
  have hmertens := sum_vonMangoldt_div_le (N := N) (by omega)
  rw [hsplit]
  linarith [hmain, hexp ▸ hmain, hcorr, hU, hmertens]

/-- **CONDITIONAL on the Chebyshev-type bound `π(y) ≤ 1.02 y / log y`** (the remaining
field `primeCountingUpper`), the whole structure `LargePrimeInputs` is available: the
field `mertensRoots` is now unconditional. -/
theorem largePrimeInputs_of_primeCountingUpper
    (h : ∃ y₀ : ℕ, ∀ y : ℕ, y₀ ≤ y → ((primesLE y).card : ℝ) ≤ 1.02 * (y : ℝ) / Real.log y) :
    LargePrimeInputs :=
  { mertensRoots := mertensRoots_unconditional
    primeCountingUpper := h }

end FactorialHypergraph

/-! ## Axiom audit -/

#print axioms FactorialHypergraph.rootCount_eq_card_rootsMod
#print axioms FactorialHypergraph.legendreSym_five_eq_chi5
#print axioms FactorialHypergraph.rootCount_eq_one_add_chi5
#print axioms FactorialHypergraph.mertensRoots_unconditional
#print axioms FactorialHypergraph.largePrimeInputs_of_primeCountingUpper
