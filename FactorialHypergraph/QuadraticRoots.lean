/-
# The root structure of the quadratic `f(t) = t² + 3t + 1`

This file formalizes the elementary (purely algebraic) part of Section 3.1 of the
manuscript, namely everything that is stated there about the roots of

  `f(t) = t² + 3t + 1`

modulo primes and prime powers.  All results in this file are **unconditional**; none of
them uses an analytic input.

* `four_mul_fq_add_five` / `four_mul_fq_add_five_int` — the discriminant identity
  `(2t+3)² = 4 f(t) + 5` (equation (3.4) of the manuscript);
* `two_not_dvd_fq` — `f` has no root modulo `2`;
* `five_dvd_fq_iff` — `5 ∣ f(i)` exactly when `i ≡ 1 (mod 5)`;
* `fq_one_add_five_mul` and `not_twentyfive_dvd_fq` — equation (3.6),
  `f(1+5t) = 5(1+5t+5t²)`, and the consequence that the root modulo `5` does not lift to
  a root modulo `25`;
* `card_rootsMod` and `card_rootsMod_eq_one_add_chi` — the root count
  `ρ(p) = 1 + (5/p) = 1 + χ₅(p)` (equation (3.5)), obtained from the discriminant
  identity, mathlib's `quadraticChar_card_sqrts` and quadratic reciprocity;
* `card_rootsMod_eq_two_iff` — `ρ(p) = 2` exactly for `p ≡ ±1 (mod 5)`, so that
  `ρ(p) ∈ {0, 2}` for `p ≠ 2, 5`;
* `not_dvd_deriv_of_dvd_fq` — every root of `f` modulo a prime `p ≠ 5` is simple;
* `fq_unique_lift` — the Hensel step in the form used by the manuscript: a root of `f`
  modulo `p ≠ 5` has at most one lift to a root modulo `pᵃ`.
-/
import FactorialHypergraph.Definitions

namespace FactorialHypergraph

open Finset

instance fact_prime_five : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-! ## The discriminant identity -/

/-- **Equation (3.4)**: `(2i+3)² = 4 f(i) + 5`, over `ℕ`. -/
theorem four_mul_fq_add_five (i : ℕ) : 4 * fq i + 5 = (2 * i + 3) ^ 2 := by
  simp only [fq]; ring

/-- **Equation (3.4)** over `ℤ`. -/
theorem four_mul_fq_add_five_int (t : ℤ) : 4 * (t ^ 2 + 3 * t + 1) + 5 = (2 * t + 3) ^ 2 := by
  ring

/-- The value of `f` viewed in `ℤ`. -/
theorem fq_cast (i : ℕ) : ((fq i : ℕ) : ℤ) = (i : ℤ) ^ 2 + 3 * (i : ℤ) + 1 := by
  simp only [fq]; push_cast; ring

/-! ## The primes `2` and `5` -/

/-- `f` has no root modulo `2`: `f(i)` is always odd. -/
theorem two_not_dvd_fq (i : ℕ) : ¬ (2 ∣ fq i) := by
  intro h
  have h0 : ((fq i : ℕ) : ZMod 2) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h
  rw [fq] at h0
  push_cast at h0
  revert h0
  generalize ((i : ℕ) : ZMod 2) = x
  revert x
  decide

/-- `5 ∣ f(i)` if and only if `i ≡ 1 (mod 5)`. -/
theorem five_dvd_fq_iff (i : ℕ) : 5 ∣ fq i ↔ i % 5 = 1 := by
  constructor
  · intro h
    have h0 : ((fq i : ℕ) : ZMod 5) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h
    rw [fq] at h0
    push_cast at h0
    have hx : ((i : ℕ) : ZMod 5) = ((1 : ℕ) : ZMod 5) := by
      revert h0
      generalize ((i : ℕ) : ZMod 5) = x
      revert x
      decide
    have := (ZMod.natCast_eq_natCast_iff' i 1 5).mp hx
    simpa using this
  · intro h
    have hx : ((i : ℕ) : ZMod 5) = ((1 : ℕ) : ZMod 5) :=
      (ZMod.natCast_eq_natCast_iff' i 1 5).mpr (by simp [h])
    have h0 : ((fq i : ℕ) : ZMod 5) = 0 := by
      rw [fq]
      push_cast
      rw [hx]
      decide
    exact (ZMod.natCast_eq_zero_iff _ _).mp h0

/-- **Equation (3.6)**: `f(1 + 5t) = 5(1 + 5t + 5t²)`. -/
theorem fq_one_add_five_mul (t : ℕ) : fq (1 + 5 * t) = 5 * (1 + 5 * t + 5 * t ^ 2) := by
  simp only [fq]; ring

/-- The root of `f` modulo `5` does not lift to a root modulo `25`. -/
theorem not_twentyfive_dvd_fq (i : ℕ) : ¬ (25 ∣ fq i) := by
  intro h
  have h5 : (5 : ℕ) ∣ fq i := dvd_trans (by norm_num) h
  obtain ⟨t, ht⟩ : ∃ t, i = 1 + 5 * t := by
    have := (five_dvd_fq_iff i).mp h5
    exact ⟨i / 5, by omega⟩
  subst ht
  rw [fq_one_add_five_mul] at h
  have h' : (5 : ℕ) ∣ 1 + 5 * t + 5 * t ^ 2 := by
    have h25 : 5 * 5 ∣ 5 * (1 + 5 * t + 5 * t ^ 2) := by simpa using h
    exact (mul_dvd_mul_iff_left (by norm_num : (5 : ℕ) ≠ 0)).mp h25
  omega

/-! ## Simple roots and the Hensel step -/

/-- Every root of `f` modulo a prime `p ≠ 5` is simple: `p ∤ f'(i) = 2i + 3`. -/
theorem not_dvd_deriv_of_dvd_fq {p i : ℕ} (hp : p.Prime) (hp5 : p ≠ 5) (h : p ∣ fq i) :
    ¬ p ∣ (2 * i + 3) := by
  intro hd
  have hsq : p ∣ (2 * i + 3) ^ 2 := dvd_pow hd (by norm_num)
  rw [← four_mul_fq_add_five] at hsq
  have h4 : p ∣ 4 * fq i := Dvd.dvd.mul_left h 4
  have h5 : p ∣ 5 := by
    have := Nat.dvd_sub hsq h4
    simpa using this
  exact hp5 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h5)

/-- Auxiliary form of the Hensel step, with the two indices ordered. -/
theorem fq_unique_lift_aux {p a i j : ℕ} (hp : p.Prime) (hp5 : p ≠ 5) (ha : 1 ≤ a)
    (hji : j ≤ i) (hi : p ^ a ∣ fq i) (hj : p ^ a ∣ fq j) (hij : i ≡ j [MOD p]) :
    i ≡ j [MOD p ^ a] := by
  have hpi : p ∣ fq i := dvd_trans (dvd_pow_self p (by omega)) hi
  have hnd : ¬ p ∣ (i + j + 3) := by
    intro hd
    refine not_dvd_deriv_of_dvd_fq hp hp5 hpi ?_
    have hmod : i + j + 3 ≡ i + i + 3 [MOD p] :=
      Nat.ModEq.add_right 3 (Nat.ModEq.add_left i hij.symm)
    have h0 : i + i + 3 ≡ 0 [MOD p] := hmod.symm.trans ((Nat.modEq_zero_iff_dvd).mpr hd)
    have hdvd := (Nat.modEq_zero_iff_dvd).mp h0
    have he : 2 * i + 3 = i + i + 3 := by ring
    rw [he]
    exact hdvd
  have hfac : fq i - fq j = (i - j) * (i + j + 3) := by
    have h1 : fq i = fq j + (i - j) * (i + j + 3) := by
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hji
      simp only [fq]
      have hd : j + d - j = d := by omega
      rw [hd]; ring
    omega
  have hdvd : p ^ a ∣ (i - j) * (i + j + 3) := by
    rw [← hfac]; exact Nat.dvd_sub hi hj
  have hcop : Nat.Coprime (p ^ a) (i + j + 3) :=
    Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnd)
  have hres : p ^ a ∣ (i - j) := hcop.dvd_of_dvd_mul_right hdvd
  exact ((Nat.modEq_iff_dvd' hji).mpr hres).symm

/-- **The Hensel step.**  A root of `f` modulo a prime `p ≠ 5` has at most one lift to a
root modulo `pᵃ`: if `pᵃ` divides both `f(i)` and `f(j)` and `i ≡ j (mod p)`, then already
`i ≡ j (mod pᵃ)`.  Together with `card_rootsMod_eq_one_add_chi` this is the statement
that `f` has exactly `ρ(p)` root classes modulo every power `pᵃ`, `p ≠ 2, 5`. -/
theorem fq_unique_lift {p a i j : ℕ} (hp : p.Prime) (hp5 : p ≠ 5) (ha : 1 ≤ a)
    (hi : p ^ a ∣ fq i) (hj : p ^ a ∣ fq j) (hij : i ≡ j [MOD p]) : i ≡ j [MOD p ^ a] := by
  rcases le_total j i with h | h
  · exact fq_unique_lift_aux hp hp5 ha h hi hj hij
  · exact (fq_unique_lift_aux hp hp5 ha h hj hi hij.symm).symm

/-! ## The number of roots modulo a prime -/

open scoped Classical in
/-- The set of roots of `f` in `ZMod p`; its cardinality is the quantity `ρ(p)` of the
manuscript. -/
noncomputable def rootsMod (p : ℕ) [NeZero p] : Finset (ZMod p) :=
  Finset.univ.filter (fun x : ZMod p => x ^ 2 + 3 * x + 1 = 0)

/-- **Equation (3.5)**, first form: for an odd prime `p`, the number of roots of `f`
modulo `p` is `1 + (5/p)`, where `(5/p)` is the Legendre symbol. -/
theorem card_rootsMod (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    ((rootsMod p).card : ℤ) = legendreSym p 5 + 1 := by
  classical
  have hp' : Nat.Prime p := Fact.out
  have hchar : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  have h2 : (2 : ZMod p) ≠ 0 := by
    have h : ((2 : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hd
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp' Nat.prime_two).mp hd)
    simpa using h
  have h4 : (4 : ZMod p) ≠ 0 := by
    intro h
    apply h2
    have h' : (2 : ZMod p) * 2 = 0 := by linear_combination h
    rcases mul_eq_zero.mp h' with h'' | h'' <;> exact h''
  have key : ∀ x : ZMod p, (x ^ 2 + 3 * x + 1 = 0 ↔ (2 * x + 3) ^ 2 = 5) := by
    intro x
    constructor
    · intro h; linear_combination 4 * h
    · intro h
      have h0 : (4 : ZMod p) * (x ^ 2 + 3 * x + 1) = 0 := by linear_combination h
      exact (mul_eq_zero.mp h0).resolve_left h4
  have hbij : (rootsMod p).card = ({x : ZMod p | x ^ 2 = 5}.toFinset).card := by
    apply Finset.card_bij (fun x _ => 2 * x + 3)
    · intro x hx
      simp only [rootsMod, Finset.mem_filter] at hx
      simpa [Set.mem_toFinset] using (key x).mp hx.2
    · intro x _ y _ hxy
      have h : (2 : ZMod p) * x = 2 * y := by linear_combination hxy
      exact mul_left_cancel₀ h2 h
    · intro y hy
      simp only [Set.mem_toFinset, Set.mem_setOf_eq] at hy
      refine ⟨(y - 3) / 2, ?_, ?_⟩
      · simp only [rootsMod, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [key, mul_div_cancel₀ _ h2]
        simpa using hy
      · rw [mul_div_cancel₀ _ h2]; ring
  rw [hbij]
  have hq := quadraticChar_card_sqrts hchar (5 : ZMod p)
  rw [hq, legendreSym]
  norm_num

/-- **Equation (3.5)**: `ρ(p) = 1 + χ₅(p)` for every odd prime `p`, where
`χ₅(p) = (p/5)` is the quadratic residue character modulo `5`; it equals `(5/p)` by
quadratic reciprocity, since `5 ≡ 1 (mod 4)`. -/
theorem card_rootsMod_eq_one_add_chi (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    ((rootsMod p).card : ℤ) = 1 + legendreSym 5 p := by
  have hr : legendreSym p ((5 : ℕ) : ℤ) = legendreSym 5 ((p : ℕ) : ℤ) :=
    legendreSym.quadratic_reciprocity_one_mod_four (by norm_num) hp2
  push_cast at hr
  rw [card_rootsMod p hp2, hr]
  ring

/-- `ρ(p) = 2` exactly for the primes `p ≡ ±1 (mod 5)`; for the remaining primes
`p ≠ 2, 5` one has `ρ(p) = 0`, so `ρ(p) ∈ {0, 2}`. -/
theorem card_rootsMod_eq_two_iff (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    (rootsMod p).card = 2 ↔ (p % 5 = 1 ∨ p % 5 = 4) := by
  have hp' : Nat.Prime p := Fact.out
  have hmod : legendreSym 5 (p : ℤ) = legendreSym 5 ((p % 5 : ℕ) : ℤ) := by
    rw [legendreSym.mod 5 (p : ℤ)]
    norm_num [Int.natCast_mod]
  have hne0 : p % 5 ≠ 0 := by
    intro h
    exact hp5 ((Nat.prime_dvd_prime_iff_eq (by norm_num) hp').mp (Nat.dvd_of_mod_eq_zero h)).symm
  have hlt : p % 5 < 5 := Nat.mod_lt _ (by norm_num)
  have hcard := card_rootsMod_eq_one_add_chi p hp2
  constructor
  · intro h
    rw [h] at hcard
    have hchi : legendreSym 5 (p : ℤ) = 1 := by omega
    rw [hmod] at hchi
    interval_cases h5 : (p % 5)
    · omega
    · simp
    · exact absurd hchi (by norm_num)
    · exact absurd hchi (by norm_num)
    · simp
  · intro h
    have hchi : legendreSym 5 (p : ℤ) = 1 := by
      rw [hmod]
      rcases h with h | h <;> rw [h] <;> norm_num
    rw [hchi] at hcard
    omega

/-- `ρ(p) ∈ {0, 2}` for every prime `p ≠ 2, 5`. -/
theorem card_rootsMod_eq_zero_or_two (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    (rootsMod p).card = 0 ∨ (rootsMod p).card = 2 := by
  by_cases h : p % 5 = 1 ∨ p % 5 = 4
  · exact Or.inr ((card_rootsMod_eq_two_iff p hp2 hp5).mpr h)
  · left
    have hp' : Nat.Prime p := Fact.out
    have hne0 : p % 5 ≠ 0 := by
      intro h0
      exact hp5 ((Nat.prime_dvd_prime_iff_eq (by norm_num) hp').mp
        (Nat.dvd_of_mod_eq_zero h0)).symm
    have hlt : p % 5 < 5 := Nat.mod_lt _ (by norm_num)
    have hmod : legendreSym 5 (p : ℤ) = legendreSym 5 ((p % 5 : ℕ) : ℤ) := by
      rw [legendreSym.mod 5 (p : ℤ)]
      norm_num [Int.natCast_mod]
    have hcard := card_rootsMod_eq_one_add_chi p hp2
    have hchi : legendreSym 5 (p : ℤ) = -1 := by
      rw [hmod]
      push_neg at h
      interval_cases h5 : (p % 5) <;> simp_all <;> norm_num
    rw [hchi] at hcard
    omega

/-! ## Counting the indices `i ≤ N` with `pᵃ ∣ f(i)`

The elementary counting step of the proof of Lemma 3.2: since `f` has at most `ρ(p) ≤ 2`
root classes modulo `pᵃ` (by `card_rootsMod_eq_zero_or_two` together with the Hensel step
`fq_unique_lift`), at most `2(N/pᵃ + 1)` indices `i ≤ N` satisfy `pᵃ ∣ f(i)`. -/

/-- `f` respects congruences. -/
theorem fq_modEq {m i j : ℕ} (h : i ≡ j [MOD m]) : fq i ≡ fq j [MOD m] := by
  simp only [fq]
  exact ((h.pow 2).add ((Nat.ModEq.refl 3).mul h)).add (Nat.ModEq.refl 1)

/-- A set of pairwise incongruent (modulo `pᵃ`) roots of `f` modulo `pᵃ` injects into the
set of roots of `f` modulo `p`. -/
theorem card_le_card_rootsMod {p a : ℕ} [Fact p.Prime] (hp5 : p ≠ 5) (ha : 1 ≤ a)
    (s : Finset ℕ) (hincong : ∀ i ∈ s, ∀ j ∈ s, i ≡ j [MOD p ^ a] → i = j)
    (hdvd : ∀ i ∈ s, p ^ a ∣ fq i) : s.card ≤ (rootsMod p).card := by
  classical
  have hp' : Nat.Prime p := Fact.out
  refine Finset.card_le_card_of_injOn (t := rootsMod p) (fun i : ℕ => (i : ZMod p)) ?_ ?_
  · intro i hi
    have hi' : i ∈ s := Finset.mem_coe.mp hi
    have hpi : p ∣ fq i := dvd_trans (dvd_pow_self p (by omega)) (hdvd i hi')
    have h0 : ((fq i : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hpi
    rw [fq] at h0
    push_cast at h0
    simp only [Finset.mem_coe, rootsMod, Finset.mem_filter, Finset.mem_univ, true_and]
    linear_combination h0
  · intro i hi j hj hij
    have hi' : i ∈ s := Finset.mem_coe.mp hi
    have hj' : j ∈ s := Finset.mem_coe.mp hj
    have h1 : i ≡ j [MOD p] := (ZMod.natCast_eq_natCast_iff _ _ _).mp hij
    exact hincong i hi' j hj' (fq_unique_lift hp' hp5 ha (hdvd i hi') (hdvd j hj') h1)

/-- The number of indices `1 ≤ i ≤ N` in a fixed residue class modulo `M`. -/
theorem card_filter_mod_le (M N r : ℕ) :
    ((Finset.Icc 1 N).filter (fun i => i % M = r)).card ≤ N / M + 1 := by
  classical
  have h : ((Finset.Icc 1 N).filter (fun i => i % M = r)).card ≤ (Finset.Icc 0 (N / M)).card := by
    apply Finset.card_le_card_of_injOn (fun i => i / M)
    · intro i hi
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Icc] at hi
      simp only [Finset.coe_Icc, Set.mem_Icc]
      exact ⟨Nat.zero_le _, Nat.div_le_div_right hi.1.2⟩
    · intro i hi j hj hij
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Icc] at hi hj
      have h1 := Nat.div_add_mod i M
      have h2 := Nat.div_add_mod j M
      rw [hi.2] at h1
      rw [hj.2] at h2
      simp only at hij
      rw [hij] at h1
      omega
  simpa [Nat.card_Icc] using h

/-- **The counting step of Lemma 3.2.**  For a prime `p ≠ 2, 5` and `a ≥ 1`, at most
`ρ(p)·(N/pᵃ + 1) ≤ 2(N/pᵃ + 1)` indices `1 ≤ i ≤ N` satisfy `pᵃ ∣ f(i)`. -/
theorem card_dvd_fq_le {p a : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp5 : p ≠ 5) (ha : 1 ≤ a)
    (N : ℕ) : ((Finset.Icc 1 N).filter (fun i => p ^ a ∣ fq i)).card ≤ (N / p ^ a + 1) * 2 := by
  classical
  have hp' : Nat.Prime p := Fact.out
  set M : ℕ := p ^ a with hM
  have hMpos : 0 < M := pow_pos hp'.pos a
  set s : Finset ℕ := (Finset.Icc 1 N).filter (fun i => M ∣ fq i) with hs
  have hfiber : ∀ b ∈ Finset.image (fun i => i % M) s, {i ∈ s | i % M = b}.card ≤ N / M + 1 := by
    intro b _
    refine le_trans (Finset.card_le_card ?_) (card_filter_mod_le M N b)
    intro i hi
    simp only [Finset.mem_filter, hs] at hi ⊢
    exact ⟨hi.1.1, hi.2⟩
  have hmain := Finset.card_le_mul_card_image s (N / M + 1) hfiber
  have himage : (Finset.image (fun i => i % M) s).card ≤ 2 := by
    have hle : (Finset.image (fun i => i % M) s).card ≤ (rootsMod p).card := by
      refine card_le_card_rootsMod hp5 ha _ ?_ ?_
      · intro r hr r' hr' hrr'
        simp only [Finset.mem_image, hs] at hr hr'
        obtain ⟨i, -, rfl⟩ := hr
        obtain ⟨j, -, rfl⟩ := hr'
        have h1 : i % M < M := Nat.mod_lt _ hMpos
        have h2 : j % M < M := Nat.mod_lt _ hMpos
        unfold Nat.ModEq at hrr'
        rwa [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hrr'
      · intro r hr
        simp only [Finset.mem_image, hs, Finset.mem_filter] at hr
        obtain ⟨i, hi, rfl⟩ := hr
        have hcong : fq (i % M) ≡ fq i [MOD M] := fq_modEq (Nat.mod_modEq i M)
        have h0 : fq i ≡ 0 [MOD M] := (Nat.modEq_zero_iff_dvd).mpr hi.2
        exact (Nat.modEq_zero_iff_dvd).mp (hcong.trans h0)
    rcases card_rootsMod_eq_zero_or_two p hp2 hp5 with h | h <;> omega
  calc s.card ≤ (N / M + 1) * (Finset.image (fun i => i % M) s).card := hmain
    _ ≤ (N / M + 1) * 2 := Nat.mul_le_mul_left _ himage

/-! ## At most two indices below `q` are roots of `f` modulo a prime `q`

and the resulting bound for the number of indices whose largest prime factor is small
(the "discard step" in the proof of Lemma 3.2). -/

/-- For every prime `q`, at most two indices `i < q` satisfy `q ∣ f(i)`. -/
theorem card_le_two_of_dvd_fq_lt {q : ℕ} (hq : q.Prime) (s : Finset ℕ)
    (hs : ∀ i ∈ s, i < q) (hdvd : ∀ i ∈ s, q ∣ fq i) : s.card ≤ 2 := by
  classical
  by_cases hq2 : q = 2
  · have hempty : s = ∅ := by
      refine Finset.eq_empty_iff_forall_notMem.mpr ?_
      intro i hi
      exact two_not_dvd_fq i (hq2 ▸ hdvd i hi)
    simp [hempty]
  by_cases hq5 : q = 5
  · have hsub : s ⊆ {1} := by
      intro i hi
      have h1 : (5 : ℕ) ∣ fq i := hq5 ▸ hdvd i hi
      have h2 : i % 5 = 1 := (five_dvd_fq_iff i).mp h1
      have h3 : i < 5 := hq5 ▸ hs i hi
      have h4 : i = 1 := by omega
      simp [h4]
    exact le_trans (Finset.card_le_card hsub) (by simp)
  haveI := Fact.mk hq
  have hle : s.card ≤ (rootsMod q).card := by
    refine card_le_card_rootsMod hq5 (le_refl 1) s ?_ ?_
    · intro i hi j hj hij
      change i % (q ^ 1) = j % (q ^ 1) at hij
      have h1 : i % q = j % q := by simpa only [pow_one] using hij
      rwa [Nat.mod_eq_of_lt (hs i hi), Nat.mod_eq_of_lt (hs j hj)] at h1
    · intro i hi
      simpa [pow_one] using hdvd i hi
  rcases card_rootsMod_eq_zero_or_two q hq2 hq5 with h | h <;> omega

open scoped Classical in
/-- **The discard step of Lemma 3.2.**  The number of indices `1 ≤ i ≤ N` for which `f(i)`
has a prime factor `q` with `i < q ≤ y` is at most `2π(y)`. -/
theorem card_small_largest_prime_factor_le (N y : ℕ) :
    ((Finset.Icc 1 N).filter
        (fun i => ∃ q : ℕ, q.Prime ∧ q ∣ fq i ∧ i < q ∧ q ≤ y)).card
      ≤ 2 * ((Finset.range (y + 1)).filter Nat.Prime).card := by
  classical
  set s : Finset ℕ :=
    (Finset.Icc 1 N).filter (fun i => ∃ q : ℕ, q.Prime ∧ q ∣ fq i ∧ i < q ∧ q ≤ y) with hs
  set g : ℕ → ℕ := fun i =>
    if h : ∃ q : ℕ, q.Prime ∧ q ∣ fq i ∧ i < q ∧ q ≤ y then h.choose else 0 with hg
  have hgspec : ∀ i ∈ s, (g i).Prime ∧ g i ∣ fq i ∧ i < g i ∧ g i ≤ y := by
    intro i hi
    have h : ∃ q : ℕ, q.Prime ∧ q ∣ fq i ∧ i < q ∧ q ≤ y := by
      simp only [hs, Finset.mem_filter] at hi
      exact hi.2
    simp only [hg, dif_pos h]
    exact h.choose_spec
  have hfiber : ∀ b ∈ Finset.image g s, {i ∈ s | g i = b}.card ≤ 2 := by
    intro b hb
    obtain ⟨i₀, hi₀, rfl⟩ := Finset.mem_image.mp hb
    refine card_le_two_of_dvd_fq_lt (hgspec i₀ hi₀).1 _ ?_ ?_
    · intro i hi
      simp only [Finset.mem_filter] at hi
      have h := (hgspec i hi.1).2.2.1
      rw [hi.2] at h
      exact h
    · intro i hi
      simp only [Finset.mem_filter] at hi
      have h := (hgspec i hi.1).2.1
      rw [hi.2] at h
      exact h
  have hmain := Finset.card_le_mul_card_image s 2 hfiber
  have himage : (Finset.image g s).card ≤ ((Finset.range (y + 1)).filter Nat.Prime).card := by
    refine Finset.card_le_card ?_
    intro b hb
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hb
    have h := hgspec i hi
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, h.1⟩
  calc s.card ≤ 2 * (Finset.image g s).card := hmain
    _ ≤ 2 * ((Finset.range (y + 1)).filter Nat.Prime).card := Nat.mul_le_mul_left _ himage

end FactorialHypergraph
