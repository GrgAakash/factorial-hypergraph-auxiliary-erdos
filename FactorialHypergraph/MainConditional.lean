/-
# The conditional main theorems

Assuming `h : AnalyticInputs` (the three analytic number-theoretic inputs isolated in
`AnalyticInputs.lean`, none of which is available in mathlib), we prove:

* `cover_cost` — Theorem 1.1 of the manuscript: `κ(L) ≤ (1-δ) L log L`;
* `main_quantitative` — Theorem 1.2 of the manuscript, as a cardinality statement for a
  filtered `Finset`;
* `auxiliary_erdos_problem` — the qualitative auxiliary problem of Erdős.

**All results in this file are CONDITIONAL on `h : AnalyticInputs`.**  They do *not*
settle Erdős Problem 1059 (the original prime problem), which is not addressed here.
-/
import FactorialHypergraph.AnalyticInputs
import FactorialHypergraph.CollisionCriterion
import FactorialHypergraph.ConflictGraph
import FactorialHypergraph.CRTCover
import FactorialHypergraph.Transference
import FactorialHypergraph.PrimeSupply
import FactorialHypergraph.QuadraticRoots

namespace FactorialHypergraph

open Finset

/-! ## Step 1: many usable indices -/

/-- CONDITIONAL.  Combining the large-prime-factor input (A2) with the sieve corollary,
at least `9L/100` indices `i` with `2 ≤ i ≤ L - 2` carry a prime `q i ∣ f(i)` with
`L < q i < 2 L^{2-α₀}`. -/
theorem exists_good_indices (h : AnalyticInputs) {α₀ : ℝ} (hα0 : 0 < α₀) (hα1 : α₀ ≤ 1 / 2)
    (hsieve : ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L → ((smallCofactorSet α₀ L).card : ℝ) ≤ (L : ℝ) / 500) :
    ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L → ∃ (S : Finset ℕ) (q : ℕ → ℕ),
      9 * (L : ℝ) / 100 ≤ (S.card : ℝ) ∧
      ∀ i ∈ S, 2 ≤ i ∧ i + 2 ≤ L ∧ (q i).Prime ∧ q i ∣ fq i ∧ L < q i ∧
        (q i : ℝ) < 2 * (L : ℝ) ^ (2 - α₀) := by
  classical
  obtain ⟨N₀, hN₀⟩ := h.largePrimeFactor
  obtain ⟨L₁, hL₁⟩ := hsieve
  refine ⟨max (max N₀ L₁) (max 250 ⌈Real.exp 500⌉₊), ?_⟩
  intro L hL
  have hN₀L : N₀ ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL
  have hL₁L : L₁ ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL
  have hL250 : 250 ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL
  have hceil : ⌈Real.exp 500⌉₊ ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hL
  have hexpL : Real.exp 500 ≤ (L : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hceil)
  have hLpos : (0 : ℝ) < (L : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hexpL
  have hlogL : (500 : ℝ) ≤ Real.log L := by
    have := Real.log_le_log (Real.exp_pos _) hexpL
    rwa [Real.log_exp] at this
  have hL250R : (250 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL250
  -- the three sets involved
  set A : Finset ℕ := largePrimeFactorSet L with hA
  set E : Finset ℕ := smallCofactorSet α₀ L with hE
  set D : Finset ℕ := (Finset.Icc 1 L).filter (fun i => ¬ (L ≤ 10 * i ∧ i + 2 ≤ L)) with hD
  set S : Finset ℕ := A \ (D ∪ E) with hSdef
  -- the discarded indices are few
  have hDcard : (D.card : ℝ) ≤ (L : ℝ) / 10 + 2 := by
    have hsub : D ⊆ Finset.Icc 1 (L / 10) ∪ ({L - 1, L} : Finset ℕ) := by
      intro i hi
      rw [hD, Finset.mem_filter, Finset.mem_Icc] at hi
      obtain ⟨⟨hi1, hi2⟩, hi3⟩ := hi
      rcases Nat.lt_or_ge (10 * i) L with hlt | hge
      · refine Finset.mem_union_left _ (Finset.mem_Icc.mpr ⟨hi1, ?_⟩)
        omega
      · refine Finset.mem_union_right _ ?_
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega
    have hcard1 : (Finset.Icc 1 (L / 10) ∪ ({L - 1, L} : Finset ℕ)).card ≤ L / 10 + 2 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      have h1 : (Finset.Icc 1 (L / 10)).card = L / 10 := by simp
      have h2 : ({L - 1, L} : Finset ℕ).card ≤ 2 :=
        le_trans (Finset.card_insert_le _ _) (by simp)
      omega
    have hnat : D.card ≤ L / 10 + 2 := le_trans (Finset.card_le_card hsub) hcard1
    have hdiv : ((L / 10 : ℕ) : ℝ) ≤ (L : ℝ) / 10 := by
      have := Nat.cast_div_le (α := ℝ) (m := L) (n := 10)
      simpa using this
    have hcast : (D.card : ℝ) ≤ ((L / 10 : ℕ) : ℝ) + 2 := by exact_mod_cast hnat
    linarith
  have hEcard : (E.card : ℝ) ≤ (L : ℝ) / 500 := hL₁ L hL₁L
  have hAcard : (L : ℝ) / 5 ≤ (A.card : ℝ) := hN₀ L hN₀L
  have hcards : A.card ≤ S.card + D.card + E.card := by
    have h1 : A.card ≤ S.card + (D ∪ E).card := by
      rw [hSdef]; exact Finset.card_le_card_sdiff_add_card
    have h2 : (D ∪ E).card ≤ D.card + E.card := Finset.card_union_le _ _
    omega
  have hScard : 9 * (L : ℝ) / 100 ≤ (S.card : ℝ) := by
    have hcast : (A.card : ℝ) ≤ (S.card : ℝ) + (D.card : ℝ) + (E.card : ℝ) := by
      exact_mod_cast hcards
    linarith
  -- basic membership facts for the surviving indices
  have hmem : ∀ i ∈ S, (1 ≤ i ∧ i ≤ L) ∧ (L ≤ 10 * i ∧ i + 2 ≤ L) ∧ i ∉ E ∧
      ∃ p : ℕ, p.Prime ∧ p ∣ fq i ∧ (i : ℝ) * Real.log i / 40 < p := by
    intro i hi
    rw [hSdef, Finset.mem_sdiff, Finset.mem_union] at hi
    obtain ⟨hiA, hiDE⟩ := hi
    push_neg at hiDE
    rw [hA, mem_largePrimeFactorSet] at hiA
    obtain ⟨⟨hi1, hi2⟩, hex⟩ := hiA
    refine ⟨⟨hi1, hi2⟩, ?_, hiDE.2, hex⟩
    by_contra hcon
    exact hiDE.1 (by rw [hD, Finset.mem_filter, Finset.mem_Icc]; exact ⟨⟨hi1, hi2⟩, hcon⟩)
  -- choose a large prime factor for each index
  have hchoice : ∀ i : ℕ, ∃ p : ℕ,
      i ∈ S → (p.Prime ∧ p ∣ fq i ∧ (i : ℝ) * Real.log i / 40 < p) := by
    intro i
    by_cases hi : i ∈ S
    · obtain ⟨-, -, -, p, hp⟩ := hmem i hi
      exact ⟨p, fun _ => hp⟩
    · exact ⟨2, fun hcon => absurd hcon hi⟩
  choose q hq using hchoice
  refine ⟨S, q, hScard, ?_⟩
  intro i hi
  obtain ⟨⟨hi1, hi2⟩, ⟨hi10, hi2L⟩, hiE, -⟩ := hmem i hi
  obtain ⟨hqp, hqd, hqlarge⟩ := hq i hi
  have hiR : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hi1
  have hi10R : (L : ℝ) ≤ 10 * (i : ℝ) := by exact_mod_cast hi10
  -- `log i ≥ 400`
  have hlogi : (400 : ℝ) ≤ Real.log i := by
    have h10 : Real.log 10 ≤ 9 := by
      have := Real.log_le_sub_one_of_pos (x := (10 : ℝ)) (by norm_num)
      linarith
    have hmul : Real.log (10 * (i : ℝ)) = Real.log 10 + Real.log i :=
      Real.log_mul (by norm_num) (ne_of_gt hiR)
    have hmono : Real.log L ≤ Real.log (10 * (i : ℝ)) := Real.log_le_log hLpos hi10R
    linarith
  -- `L < q i`
  have hqL : (L : ℝ) < (q i : ℝ) := by
    have hkey : (L : ℝ) ≤ (i : ℝ) * Real.log i / 40 := by
      have h1 : (L : ℝ) / 10 ≤ (i : ℝ) := by linarith
      nlinarith
    linarith
  have hqLnat : L < q i := by exact_mod_cast hqL
  refine ⟨by omega, hi2L, hqp, hqd, hqLnat, ?_⟩
  -- the complementary factor is large, hence `q i` is small
  obtain ⟨m, hm⟩ := hqd
  have hmbig : (L : ℝ) ^ α₀ < (m : ℝ) := by
    by_contra hcon
    push_neg at hcon
    refine hiE (?_)
    rw [hE, mem_smallCofactorSet]
    exact ⟨⟨hi1, hi2⟩, m, q i, hqp, by rw [hm]; ring, hcon, hqLnat⟩
  have hfqle : (fq i : ℝ) ≤ 2 * (L : ℝ) ^ 2 := by
    have hnat : fq i ≤ 2 * L ^ 2 := by
      have hle : i ^ 2 ≤ L ^ 2 := Nat.pow_le_pow_left hi2 2
      have hLsq : 3 * L + 1 ≤ L ^ 2 := by nlinarith
      simp only [fq]
      omega
    exact_mod_cast hnat
  have hrpow : (L : ℝ) ^ (2 - α₀) * (L : ℝ) ^ α₀ = (L : ℝ) ^ 2 := by
    rw [← Real.rpow_add hLpos]
    norm_num
  have hpowpos : (0 : ℝ) < (L : ℝ) ^ α₀ := Real.rpow_pos_of_pos hLpos _
  have hqpos : (0 : ℝ) < (q i : ℝ) := by
    have := hqp.pos
    exact_mod_cast this
  have hfq : (fq i : ℝ) = (q i : ℝ) * (m : ℝ) := by exact_mod_cast congrArg (fun t : ℕ => (t : ℝ)) hm
  have hprod : (q i : ℝ) * (L : ℝ) ^ α₀ < (2 * (L : ℝ) ^ (2 - α₀)) * (L : ℝ) ^ α₀ := by
    have h1 : (q i : ℝ) * (L : ℝ) ^ α₀ < (q i : ℝ) * (m : ℝ) :=
      mul_lt_mul_of_pos_left hmbig hqpos
    have h2 : (2 * (L : ℝ) ^ (2 - α₀)) * (L : ℝ) ^ α₀ = 2 * (L : ℝ) ^ 2 := by
      rw [mul_assoc, hrpow]
    rw [h2]
    calc (q i : ℝ) * (L : ℝ) ^ α₀ < (q i : ℝ) * (m : ℝ) := h1
      _ = (fq i : ℝ) := hfq.symm
      _ ≤ 2 * (L : ℝ) ^ 2 := hfqle
  exact lt_of_mul_lt_mul_right hprod (le_of_lt hpowpos)

/-! ## Step 2: selecting disjoint pairs with distinct colours -/

/-- The independent-set step of Proposition 5.1: the auxiliary conflict graph on the good
indices has maximum degree at most `3`, so a quarter of them can be selected with pairwise
distinct primes and pairwise disjoint designated pairs `{i, i+2}`. -/
theorem exists_disjoint_pairs {L : ℕ} (S : Finset ℕ) (q : ℕ → ℕ)
    (hS : ∀ i ∈ S, 2 ≤ i ∧ i + 2 ≤ L ∧ (q i).Prime ∧ q i ∣ fq i ∧ L < q i) (_hL : 5 < L) :
    ∃ I ⊆ S, (S.card : ℝ) ≤ 4 * (I.card : ℝ) ∧
      (∀ i ∈ I, ∀ j ∈ I, i ≠ j → q i ≠ q j) ∧
      (∀ i ∈ I, ∀ j ∈ I, i ≠ j → i + 2 ≠ j ∧ j + 2 ≠ i) := by
  classical
  set col : {x // x ∈ S} → ℕ := fun v => q v.1 with hcoldef
  set Bs : {x // x ∈ S} → Finset ℕ := fun v => ({v.1, v.1 + 2} : Finset ℕ) with hBsdef
  -- the conflict graph has maximum degree at most `3`
  have hdeg : ∀ v : {x // x ∈ S}, (conflictGraph col Bs).degree v ≤ 3 := by
    intro v
    have hsub : (conflictGraph col Bs).neighborFinset v ⊆
        (Finset.univ.filter (fun w : {x // x ∈ S} => w ≠ v ∧ col w = col v)) ∪
        (Finset.univ.filter (fun w : {x // x ∈ S} => w.1 + 2 = v.1 ∨ v.1 + 2 = w.1)) := by
      intro w hw
      rw [SimpleGraph.mem_neighborFinset] at hw
      obtain ⟨hne, hor⟩ := hw
      have hval : v.1 ≠ w.1 := fun h => hne (Subtype.ext h)
      rcases hor with h | ⟨z, hz⟩
      · exact Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Ne.symm hne, h.symm⟩)
      · refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)
        simp only [hBsdef, Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hz
        obtain ⟨h1, h2⟩ := hz
        rcases h1 with rfl | rfl <;> rcases h2 with h | h <;> omega
    -- at most one neighbour of the same colour
    have hc1 : (Finset.univ.filter (fun w : {x // x ∈ S} => w ≠ v ∧ col w = col v)).card ≤ 1 := by
      obtain ⟨hv2, hvL, hvp, hvd, hvq⟩ := hS v.1 v.2
      have hcard2 : (S.filter (fun j => q j = q v.1)).card ≤ 2 := by
        refine card_le_two_of_dvd_fq_lt hvp _ ?_ ?_
        · intro j hj
          rw [Finset.mem_filter] at hj
          obtain ⟨hj2, hjL, _, _, _⟩ := hS j hj.1
          omega
        · intro j hj
          rw [Finset.mem_filter] at hj
          obtain ⟨_, _, _, hjd, _⟩ := hS j hj.1
          rw [← hj.2]
          exact hjd
      have hvmem : v.1 ∈ S.filter (fun j => q j = q v.1) := Finset.mem_filter.mpr ⟨v.2, rfl⟩
      have himg :
          (Finset.univ.filter (fun w : {x // x ∈ S} => w ≠ v ∧ col w = col v)).image Subtype.val
            ⊆ (S.filter (fun j => q j = q v.1)).erase v.1 := by
        intro x hx
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx
        rw [Finset.mem_filter] at hw
        obtain ⟨-, hwv, hwcol⟩ := hw
        refine Finset.mem_erase.mpr ⟨fun h => hwv (Subtype.ext h), ?_⟩
        exact Finset.mem_filter.mpr ⟨w.2, hwcol⟩
      have hcarderase : ((S.filter (fun j => q j = q v.1)).erase v.1).card ≤ 1 := by
        rw [Finset.card_erase_of_mem hvmem]
        omega
      calc (Finset.univ.filter (fun w : {x // x ∈ S} => w ≠ v ∧ col w = col v)).card
          = ((Finset.univ.filter
              (fun w : {x // x ∈ S} => w ≠ v ∧ col w = col v)).image Subtype.val).card :=
            (Finset.card_image_of_injective _ Subtype.val_injective).symm
        _ ≤ ((S.filter (fun j => q j = q v.1)).erase v.1).card := Finset.card_le_card himg
        _ ≤ 1 := hcarderase
    -- at most two neighbours whose designated pair overlaps
    have hc2 : (Finset.univ.filter
        (fun w : {x // x ∈ S} => w.1 + 2 = v.1 ∨ v.1 + 2 = w.1)).card ≤ 2 := by
      have himg : (Finset.univ.filter
          (fun w : {x // x ∈ S} => w.1 + 2 = v.1 ∨ v.1 + 2 = w.1)).image Subtype.val
            ⊆ ({v.1 - 2, v.1 + 2} : Finset ℕ) := by
        intro x hx
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx
        rw [Finset.mem_filter] at hw
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rcases hw.2 with h | h <;> omega
      calc (Finset.univ.filter (fun w : {x // x ∈ S} => w.1 + 2 = v.1 ∨ v.1 + 2 = w.1)).card
          = ((Finset.univ.filter
              (fun w : {x // x ∈ S} => w.1 + 2 = v.1 ∨ v.1 + 2 = w.1)).image Subtype.val).card :=
            (Finset.card_image_of_injective _ Subtype.val_injective).symm
        _ ≤ ({v.1 - 2, v.1 + 2} : Finset ℕ).card := Finset.card_le_card himg
        _ ≤ 2 := Finset.card_insert_le _ _ |>.trans (by simp)
    have := Finset.card_le_card hsub
    have hunion := Finset.card_union_le
      (Finset.univ.filter (fun w : {x // x ∈ S} => w ≠ v ∧ col w = col v))
      (Finset.univ.filter (fun w : {x // x ∈ S} => w.1 + 2 = v.1 ∨ v.1 + 2 = w.1))
    unfold SimpleGraph.degree
    omega
  obtain ⟨s, hs, hcard⟩ := exists_indepSet_card (conflictGraph col Bs) 3 hdeg
  obtain ⟨hcolne, hBdisj⟩ := indepSet_conflictGraph col Bs s hs
  refine ⟨s.image Subtype.val, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hx
    exact w.2
  · have himgcard : (s.image Subtype.val).card = s.card :=
      Finset.card_image_of_injective _ Subtype.val_injective
    have hFin : (Fintype.card {x // x ∈ S} : ℝ) = (S.card : ℝ) := by
      simp [Fintype.card_coe]
    rw [himgcard]
    rw [hFin] at hcard
    push_cast at hcard ⊢
    linarith
  · intro i hi j hj hij
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hj
    exact hcolne v hv w hw (fun h => hij (congrArg Subtype.val h))
  · intro i hi j hj hij
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hj
    have hne : v ≠ w := fun h => hij (congrArg Subtype.val h)
    have hd := hBdisj v hv w hw hne
    rw [Finset.disjoint_left] at hd
    constructor
    · intro hcon
      have h1 : (v.1 + 2) ∈ Bs v := by simp [hBsdef]
      have h2 : (v.1 + 2) ∈ Bs w := by
        simp only [hBsdef, Finset.mem_insert, Finset.mem_singleton]; omega
      exact hd h1 h2
    · intro hcon
      have h1 : (v.1 : ℕ) ∈ Bs v := by simp [hBsdef]
      have h2 : (v.1 : ℕ) ∈ Bs w := by
        simp only [hBsdef, Finset.mem_insert, Finset.mem_singleton]; omega
      exact hd h1 h2

/-! ## Step 3: assigning primes to the uncovered indices -/

/-- The complement of the selected pairs inside `V_L` has exactly `L - 1 - 2|I|`
elements. -/
theorem card_complement_pairs {L : ℕ} (I : Finset ℕ)
    (hI : ∀ i ∈ I, 2 ≤ i ∧ i + 2 ≤ L)
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → i + 2 ≠ j ∧ j + 2 ≠ i) :
    ((V L) \ (I.biUnion (fun i => ({i, i + 2} : Finset ℕ)))).card + 2 * I.card = L - 1 := by
  classical
  set B : Finset ℕ := I.biUnion (fun i => ({i, i + 2} : Finset ℕ)) with hB
  have hsub : B ⊆ V L := by
    intro x hx
    rw [hB, Finset.mem_biUnion] at hx
    obtain ⟨i, hi, hx⟩ := hx
    obtain ⟨h1, h2⟩ := hI i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> exact mem_V.mpr (by omega)
  have hcardB : B.card = 2 * I.card := by
    rw [hB, Finset.card_biUnion]
    · rw [Finset.sum_congr rfl (fun i _ => by
        rw [Finset.card_insert_of_notMem (by simp), Finset.card_singleton])]
      simp [Finset.sum_const, mul_comm]
    · intro i hi j hj hij
      obtain ⟨h1, h2⟩ := hdisj i hi j hj hij
      simp only [Finset.disjoint_left, Finset.mem_insert, Finset.mem_singleton]
      rintro a (rfl | rfl) <;> push_neg <;> omega
  have hVcard : (V L).card = L - 1 := by simp [V, Nat.card_Icc]
  have hadd := Finset.card_sdiff_add_card_eq_card hsub
  rw [hVcard, hcardB] at hadd
  omega

/-- CONDITIONAL (via the prime-supply input (A1)).  Distinct primes in
`(L, 20 L log L]`, avoiding a prescribed set `T` of at most `L` primes, can be assigned
injectively to any set `U` of at most `L` indices. -/
theorem exists_prime_assignment {L : ℕ} (U T : Finset ℕ)
    (hsupply : 2 * L ≤ (primesIn L ⌈20 * (L : ℝ) * Real.log L⌉₊).card)
    (hT : T.card ≤ L) (hU : U.card ≤ L) :
    ∃ r : ℕ → ℕ, (∀ k ∈ U, ∀ l ∈ U, k ≠ l → r k ≠ r l) ∧
      ∀ k ∈ U, r k ∈ primesIn L ⌈20 * (L : ℝ) * Real.log L⌉₊ ∧ r k ∉ T := by
  classical
  set P : Finset ℕ := primesIn L ⌈20 * (L : ℝ) * Real.log L⌉₊ with hPdef
  have hsub : U.card ≤ (P \ T).card := by
    have h := Finset.le_card_sdiff T P
    omega
  obtain ⟨W, hWsub, hWcard⟩ := Finset.exists_subset_card_eq hsub
  have hUW : U.card = W.card := hWcard.symm
  set e := Finset.equivOfCardEq hUW with he
  refine ⟨fun k => if h : k ∈ U then ((e ⟨k, h⟩ : {x // x ∈ W}) : ℕ) else 0, ?_, ?_⟩
  · intro k hk l hl hkl hcon
    simp only [dif_pos hk, dif_pos hl] at hcon
    exact hkl (congrArg Subtype.val (e.injective (Subtype.ext hcon)))
  · intro k hk
    have hmem : ((e ⟨k, hk⟩ : {x // x ∈ W}) : ℕ) ∈ W := (e ⟨k, hk⟩).2
    have hmem' := hWsub hmem
    rw [Finset.mem_sdiff] at hmem'
    simp only [dif_pos hk]
    exact ⟨hmem'.1, hmem'.2⟩

/-! ## Step 4: assembling the rainbow edge cover -/

/-- Assembling a rainbow edge cover out of the selected pairs and the individual primes. -/
theorem exists_cover_from_data {L : ℕ} (I : Finset ℕ) (q : ℕ → ℕ) (U : Finset ℕ) (r : ℕ → ℕ)
    (hI : ∀ i ∈ I, 2 ≤ i ∧ i + 2 ≤ L ∧ (q i).Prime ∧ q i ∣ fq i ∧ L < q i ∧ q i < L.factorial)
    (hqinj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → q i ≠ q j)
    (hU : U = (V L) \ (I.biUnion (fun i => ({i, i + 2} : Finset ℕ))))
    (hr : ∀ k ∈ U, (r k).Prime ∧ L < r k ∧ r k < L.factorial)
    (hrinj : ∀ k ∈ U, ∀ l ∈ U, k ≠ l → r k ≠ r l)
    (hqr : ∀ i ∈ I, ∀ k ∈ U, q i ≠ r k) :
    ∃ C : RainbowCover L,
      C.weight = (∑ i ∈ I, Real.log (q i)) + (∑ k ∈ U, Real.log (r k)) := by
  classical
  set B : Finset ℕ := I.biUnion (fun i => ({i, i + 2} : Finset ℕ)) with hB
  have hUV : U ⊆ V L := by rw [hU]; exact Finset.sdiff_subset
  -- the residue attached to each colour
  set res : ℕ → ℕ := fun p =>
    (∑ i ∈ I.filter (fun i => q i = p), i.factorial)
      + (∑ k ∈ U.filter (fun k => r k = p), k.factorial) with hres
  have hresq : ∀ i ∈ I, res (q i) = i.factorial := by
    intro i hi
    have h1 : I.filter (fun j => q j = q i) = {i} := by
      refine Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_filter.mpr ⟨hi, rfl⟩, ?_⟩
      intro j hj
      rw [Finset.mem_filter] at hj
      by_contra hne
      exact hqinj j hj.1 i hi hne hj.2
    have h2 : U.filter (fun k => r k = q i) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr ?_
      intro k hk hcon
      exact hqr i hi k hk hcon.symm
    simp [hres, h1, h2]
  have hresr : ∀ k ∈ U, res (r k) = k.factorial := by
    intro k hk
    have h1 : I.filter (fun i => q i = r k) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr ?_
      intro i hi hcon
      exact hqr i hi k hk hcon
    have h2 : U.filter (fun l => r l = r k) = {k} := by
      refine Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_filter.mpr ⟨hk, rfl⟩, ?_⟩
      intro l hl
      rw [Finset.mem_filter] at hl
      by_contra hne
      exact hrinj l hl.1 k hk hne hl.2
    simp [hres, h1, h2]
  -- the two families of colours are disjoint
  have hdisj : Disjoint (I.image q) (U.image r) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨k, hk, hik⟩ := Finset.mem_image.mp hx'
    exact hqr i hi k hk hik.symm
  set Q : Finset ℕ := I.image q ∪ U.image r with hQ
  have hQmem : ∀ p ∈ Q, (∃ i ∈ I, q i = p) ∨ (∃ k ∈ U, r k = p) := by
    intro p hp
    rcases Finset.mem_union.mp hp with h | h
    · exact Or.inl (Finset.mem_image.mp h)
    · exact Or.inr (Finset.mem_image.mp h)
  refine ⟨⟨Q, res, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro p hp
    rcases hQmem p hp with ⟨i, hi, rfl⟩ | ⟨k, hk, rfl⟩
    · exact (hI i hi).2.2.1
    · exact (hr k hk).1
  · intro p hp
    rcases hQmem p hp with ⟨i, hi, rfl⟩ | ⟨k, hk, rfl⟩
    · exact (hI i hi).2.2.2.2.1
    · exact (hr k hk).2.1
  · intro p hp
    rcases hQmem p hp with ⟨i, hi, rfl⟩ | ⟨k, hk, rfl⟩
    · exact (hI i hi).2.2.2.2.2
    · exact (hr k hk).2.2
  · intro p hp
    rcases hQmem p hp with ⟨i, hi, rfl⟩ | ⟨k, hk, rfl⟩
    · obtain ⟨hi2, hiL, _, hdvd, _⟩ := hI i hi
      refine ⟨i, ?_⟩
      rw [hresq i hi]
      exact (pair_mem_fiber hdvd hi2 hiL).1
    · refine ⟨k, ?_⟩
      rw [hresr k hk]
      exact mem_fiber.mpr ⟨hUV hk, Nat.ModEq.refl _⟩
  · intro x hx
    by_cases hxB : x ∈ B
    · rw [hB, Finset.mem_biUnion] at hxB
      obtain ⟨i, hi, hxi⟩ := hxB
      obtain ⟨hi2, hiL, _, hdvd, _⟩ := hI i hi
      refine ⟨q i, Finset.mem_union_left _ (Finset.mem_image_of_mem q hi), ?_⟩
      rw [hresq i hi]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxi
      rcases hxi with rfl | rfl
      · exact (pair_mem_fiber hdvd hi2 hiL).1
      · exact (pair_mem_fiber hdvd hi2 hiL).2
    · have hxU : x ∈ U := by rw [hU]; exact Finset.mem_sdiff.mpr ⟨hx, hxB⟩
      refine ⟨r x, Finset.mem_union_right _ (Finset.mem_image_of_mem r hxU), ?_⟩
      rw [hresr x hxU]
      exact mem_fiber.mpr ⟨hx, Nat.ModEq.refl _⟩
  · show ∑ p ∈ Q, Real.log p = _
    rw [hQ, Finset.sum_union hdisj,
      Finset.sum_image (fun i hi j hj hij => by
        by_contra hne; exact hqinj i hi j hj hne hij),
      Finset.sum_image (fun k hk l hl hkl => by
        by_contra hne; exact hrinj k hk l hl hne hkl)]

/-! ## The singleton baseline (Proposition 2.6) -/

set_option maxHeartbeats 1000000 in
/-- UNCONDITIONAL.  **Proposition 2.6** of the manuscript, the singleton baseline
`κ(L) ≤ (L-1) log(20 L log L)`.

The manuscript deduces the required supply of primes in `(L, 20 L log L]` from the prime
number theorem; here it is supplied by the unconditional Chebyshev-type bound
`prime_supply` of `PrimeSupply.lean`, so this proposition does not depend on
`AnalyticInputs`.

The manuscript writes the bound with the real number `20 L log L`; since the prime supply
is stated for the integer ceiling `⌈20 L log L⌉`, the constant obtained here is `21`
instead of `20`.  This is the only deviation, and it does not affect any later statement:
Proposition 2.6 is not used in the proof of Theorem 1.1. -/
theorem baseline_cover_cost :
    ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L →
      kappa L ≤ ((L : ℝ) - 1) * Real.log (21 * (L : ℝ) * Real.log L) := by
  classical
  obtain ⟨L₃, hsupply⟩ := prime_supply
  refine ⟨max L₃ 11, ?_⟩
  intro L hL
  have hL₃ : L₃ ≤ L := le_trans (le_max_left _ _) hL
  have hL11 : 11 ≤ L := le_trans (le_max_right _ _) hL
  have hL11R : (11 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL11
  have hLpos : (0 : ℝ) < (L : ℝ) := by linarith
  have hlogone : (1 : ℝ) ≤ Real.log L := by
    have h1 : Real.exp 1 ≤ (L : ℝ) := le_trans (le_of_lt (Real.exp_one_lt_d9.trans (by norm_num)))
      hL11R
    have := Real.log_le_log (Real.exp_pos 1) h1
    rwa [Real.log_exp] at this
  have hlogpos : (0 : ℝ) < Real.log L := by linarith
  have hlogle : Real.log L ≤ (L : ℝ) := by
    have := Real.log_le_sub_one_of_pos hLpos
    linarith
  have hfacbig : 2 * L ^ 3 ≤ L.factorial := two_mul_cube_le_factorial (by omega)
  -- the whole vertex set is covered by individual primes
  set U : Finset ℕ :=
    (V L) \ ((∅ : Finset ℕ).biUnion (fun i => ({i, i + 2} : Finset ℕ))) with hUdef
  have hUV : U = V L := by simp [hUdef]
  have hUcard : U.card = L - 1 := by rw [hUV]; simp [V, Nat.card_Icc]
  have hUle : U.card ≤ L := by omega
  obtain ⟨r, hrinj, hrmem⟩ :=
    exists_prime_assignment U (∅ : Finset ℕ) (hsupply L hL₃) (by simp) hUle
  have hrbound : ∀ k ∈ U, (r k : ℝ) ≤ 21 * (L : ℝ) * Real.log L := by
    intro k hk
    obtain ⟨hmem, -⟩ := hrmem k hk
    rw [mem_primesIn] at hmem
    have hle : (r k : ℝ) ≤ ((⌈20 * (L : ℝ) * Real.log L⌉₊ : ℕ) : ℝ) := by
      exact_mod_cast hmem.1.2
    have hceil2 : ((⌈20 * (L : ℝ) * Real.log L⌉₊ : ℕ) : ℝ) < 20 * (L : ℝ) * Real.log L + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have hone : (1 : ℝ) ≤ (L : ℝ) * Real.log L := by nlinarith
    linarith
  have hrfac : ∀ k ∈ U, (r k).Prime ∧ L < r k ∧ r k < L.factorial := by
    intro k hk
    obtain ⟨hmem, -⟩ := hrmem k hk
    rw [mem_primesIn] at hmem
    refine ⟨hmem.2, hmem.1.1, ?_⟩
    have h1 : (r k : ℝ) ≤ 21 * (L : ℝ) * Real.log L := hrbound k hk
    have hA : (L : ℝ) * Real.log L ≤ (L : ℝ) * (L : ℝ) :=
      mul_le_mul_of_nonneg_left hlogle hLpos.le
    have hB : 21 * ((L : ℝ) * (L : ℝ)) < 2 * (L : ℝ) ^ 3 := by nlinarith [hL11R, hLpos]
    have h2 : (r k : ℝ) < 2 * (L : ℝ) ^ 3 := by nlinarith [h1, hA, hB]
    have h3 : r k < 2 * L ^ 3 := by exact_mod_cast h2
    omega
  obtain ⟨C, hCw⟩ :=
    exists_cover_from_data (∅ : Finset ℕ) (fun _ => 0) U r (by simp) (by simp) hUdef
      hrfac hrinj (by simp)
  have hsum : ∑ k ∈ U, Real.log (r k)
      ≤ (U.card : ℝ) * Real.log (21 * (L : ℝ) * Real.log L) := by
    have hpt : ∀ k ∈ U, Real.log (r k) ≤ Real.log (21 * (L : ℝ) * Real.log L) := by
      intro k hk
      have hrpos : (0 : ℝ) < (r k : ℝ) := by
        have := (hrfac k hk).1.pos
        exact_mod_cast this
      exact Real.log_le_log hrpos (hrbound k hk)
    have := Finset.sum_le_card_nsmul U (fun k => Real.log (r k))
      (Real.log (21 * (L : ℝ) * Real.log L)) hpt
    simpa [nsmul_eq_mul] using this
  have hcardR : ((U.card : ℕ) : ℝ) = (L : ℝ) - 1 := by
    have : (U.card : ℕ) + 1 = L := by omega
    have hc : ((U.card + 1 : ℕ) : ℝ) = (L : ℝ) := by exact_mod_cast this
    push_cast at hc
    linarith
  have hkappa : kappa L ≤ C.weight := by
    have := kappa_le_of_cover C
    rwa [C.log_modulus_eq_weight] at this
  rw [hCw] at hkappa
  simp only [Finset.sum_empty, zero_add] at hkappa
  rw [hcardR] at hsum
  linarith

set_option maxHeartbeats 1000000 in
/-- CONDITIONAL.  Proposition 5.1 of the manuscript: for a fixed `δ > 0` and all large `L`
there is a rainbow edge cover of weight at most `(1-δ) L log L`. -/
theorem exists_lowweight_cover (h : AnalyticInputs) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L →
      ∃ C : RainbowCover L, C.weight ≤ (1 - δ) * L * Real.log L := by
  classical
  obtain ⟨α₀, hα0, hα1, Lsieve, hsieve⟩ := sieve_corollary h
  obtain ⟨L₂, hgood⟩ := exists_good_indices h hα0 hα1 ⟨Lsieve, hsieve⟩
  obtain ⟨L₃, hsupply⟩ := prime_supply
  refine ⟨α₀ / 100, by positivity, by linarith,
    max (max L₂ L₃) (max 11 ⌈Real.exp ((1840 / α₀) ^ 2)⌉₊), ?_⟩
  intro L hL
  have hL₂ : L₂ ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL
  have hL₃ : L₃ ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL
  have hL11 : 11 ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL
  have hceil : ⌈Real.exp ((1840 / α₀) ^ 2)⌉₊ ≤ L :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hL
  have hexpL : Real.exp ((1840 / α₀) ^ 2) ≤ (L : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hceil)
  have hLpos : (0 : ℝ) < (L : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hexpL
  have hLone : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast Nat.one_le_of_lt hL11
  have hL11R : (11 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL11
  have hlogL : (1840 / α₀) ^ 2 ≤ Real.log L := by
    have := Real.log_le_log (Real.exp_pos _) hexpL
    rwa [Real.log_exp] at this
  have hthrpos : (0 : ℝ) < (1840 / α₀) ^ 2 := by positivity
  have hlogpos : (0 : ℝ) < Real.log L := lt_of_lt_of_le hthrpos hlogL
  have hlogone : (1 : ℝ) ≤ Real.log L := by
    have : (1 : ℝ) ≤ (1840 / α₀) ^ 2 := by
      have h1 : (1 : ℝ) ≤ 1840 / α₀ := by
        rw [le_div_iff₀ hα0]; linarith
      nlinarith
    linarith
  -- Step 1
  obtain ⟨S, q, hScard, hSprop⟩ := hgood L hL₂
  -- Step 2
  obtain ⟨I, hIS, hIcard, hqinj, hpairs⟩ :=
    exists_disjoint_pairs S q
      (fun i hi => ⟨(hSprop i hi).1, (hSprop i hi).2.1, (hSprop i hi).2.2.1,
        (hSprop i hi).2.2.2.1, (hSprop i hi).2.2.2.2.1⟩) (by omega)
  have hIprop : ∀ i ∈ I, 2 ≤ i ∧ i + 2 ≤ L ∧ (q i).Prime ∧ q i ∣ fq i ∧ L < q i ∧
      (q i : ℝ) < 2 * (L : ℝ) ^ (2 - α₀) := fun i hi => hSprop i (hIS hi)
  set U : Finset ℕ := (V L) \ (I.biUnion (fun i => ({i, i + 2} : Finset ℕ))) with hUdef
  have hcompl : U.card + 2 * I.card = L - 1 :=
    card_complement_pairs I (fun i hi => ⟨(hIprop i hi).1, (hIprop i hi).2.1⟩) hpairs
  have hcompl' : U.card + 2 * I.card + 1 = L := by omega
  have hIle : I.card ≤ L := by omega
  have hUle : U.card ≤ L := by omega
  -- Step 3
  obtain ⟨r, hrinj, hrmem⟩ :=
    exists_prime_assignment U (I.image q) (hsupply L hL₃)
      (le_trans Finset.card_image_le hIle) hUle
  have hqr : ∀ i ∈ I, ∀ k ∈ U, q i ≠ r k := by
    intro i hi k hk hcon
    exact (hrmem k hk).2 (Finset.mem_image.mpr ⟨i, hi, hcon⟩)
  -- the selected primes are smaller than `L!`
  have hfacbig : 2 * L ^ 3 ≤ L.factorial := two_mul_cube_le_factorial (by omega)
  have hLsqR : ((L : ℝ)) ^ (2 - α₀) ≤ (L : ℝ) ^ 2 :=
    calc ((L : ℝ)) ^ (2 - α₀) ≤ (L : ℝ) ^ (((2 : ℕ) : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le hLone (by push_cast; linarith)
      _ = (L : ℝ) ^ (2 : ℕ) := Real.rpow_natCast _ 2
  have hqfac : ∀ i ∈ I, q i < L.factorial := by
    intro i hi
    have h1 : (q i : ℝ) < 2 * (L : ℝ) ^ (2 - α₀) := (hIprop i hi).2.2.2.2.2
    have h4 : (q i : ℝ) < 2 * (L : ℝ) ^ 2 := by linarith
    have h5 : q i < 2 * L ^ 2 := by exact_mod_cast h4
    have h6 : 2 * L ^ 2 ≤ 2 * L ^ 3 := by nlinarith
    omega
  have hlogle : Real.log L ≤ (L : ℝ) := by
    have := Real.log_le_sub_one_of_pos hLpos
    linarith
  have hrbound : ∀ k ∈ U, (r k : ℝ) ≤ 21 * (L : ℝ) * Real.log L := by
    intro k hk
    obtain ⟨hmem, -⟩ := hrmem k hk
    rw [mem_primesIn] at hmem
    have hle : (r k : ℝ) ≤ ((⌈20 * (L : ℝ) * Real.log L⌉₊ : ℕ) : ℝ) := by
      exact_mod_cast hmem.1.2
    have hceil2 : ((⌈20 * (L : ℝ) * Real.log L⌉₊ : ℕ) : ℝ) < 20 * (L : ℝ) * Real.log L + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have hone : (1 : ℝ) ≤ (L : ℝ) * Real.log L := by nlinarith
    linarith
  have hrfac : ∀ k ∈ U, (r k).Prime ∧ L < r k ∧ r k < L.factorial := by
    intro k hk
    obtain ⟨hmem, -⟩ := hrmem k hk
    rw [mem_primesIn] at hmem
    refine ⟨hmem.2, hmem.1.1, ?_⟩
    have h1 : (r k : ℝ) ≤ 21 * (L : ℝ) * Real.log L := hrbound k hk
    have hA : (L : ℝ) * Real.log L ≤ (L : ℝ) * (L : ℝ) :=
      mul_le_mul_of_nonneg_left hlogle hLpos.le
    have hB : 21 * ((L : ℝ) * (L : ℝ)) < 2 * (L : ℝ) ^ 3 := by nlinarith [hL11R, hLpos]
    have h2 : (r k : ℝ) < 2 * (L : ℝ) ^ 3 := by nlinarith [h1, hA, hB]
    have h3 : r k < 2 * L ^ 3 := by exact_mod_cast h2
    omega
  -- Step 4
  obtain ⟨C, hCw⟩ :=
    exists_cover_from_data I q U r
      (fun i hi => ⟨(hIprop i hi).1, (hIprop i hi).2.1, (hIprop i hi).2.2.1,
        (hIprop i hi).2.2.2.1, (hIprop i hi).2.2.2.2.1, hqfac i hi⟩)
      hqinj hUdef hrfac hrinj hqr
  refine ⟨C, ?_⟩
  -- Step 5: the weight bookkeeping
  have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog21 : (0 : ℝ) ≤ Real.log 21 := Real.log_nonneg (by norm_num)
  have hloglog : (0 : ℝ) ≤ Real.log (Real.log L) := Real.log_nonneg hlogone
  have hsum1 : ∑ i ∈ I, Real.log (q i)
      ≤ (I.card : ℝ) * Real.log 2 + (I.card : ℝ) * ((2 - α₀) * Real.log L) := by
    have hpt : ∀ i ∈ I, Real.log (q i) ≤ Real.log 2 + (2 - α₀) * Real.log L := by
      intro i hi
      have h1 : (q i : ℝ) < 2 * (L : ℝ) ^ (2 - α₀) := (hIprop i hi).2.2.2.2.2
      have hqpos : (0 : ℝ) < (q i : ℝ) := by
        have := (hIprop i hi).2.2.1.pos
        exact_mod_cast this
      have h2 : Real.log (q i) ≤ Real.log (2 * (L : ℝ) ^ (2 - α₀)) :=
        Real.log_le_log hqpos (le_of_lt h1)
      have h3 : Real.log (2 * (L : ℝ) ^ (2 - α₀)) = Real.log 2 + (2 - α₀) * Real.log L := by
        rw [Real.log_mul (by norm_num) (ne_of_gt (Real.rpow_pos_of_pos hLpos _)),
          Real.log_rpow hLpos]
      linarith [h2, h3.le, h3.ge]
    have := Finset.sum_le_card_nsmul I (fun i => Real.log (q i))
      (Real.log 2 + (2 - α₀) * Real.log L) hpt
    simpa [nsmul_eq_mul] using this
  have hsum2 : ∑ k ∈ U, Real.log (r k)
      ≤ (U.card : ℝ) * Real.log 21 + (U.card : ℝ) * Real.log L
        + (U.card : ℝ) * Real.log (Real.log L) := by
    have hpt : ∀ k ∈ U, Real.log (r k) ≤ Real.log 21 + Real.log L + Real.log (Real.log L) := by
      intro k hk
      have h1 : (r k : ℝ) ≤ 21 * (L : ℝ) * Real.log L := hrbound k hk
      have hrpos : (0 : ℝ) < (r k : ℝ) := by
        have := (hrfac k hk).1.pos
        exact_mod_cast this
      have h2 : Real.log (r k) ≤ Real.log (21 * (L : ℝ) * Real.log L) := Real.log_le_log hrpos h1
      have h3 : Real.log (21 * (L : ℝ) * Real.log L)
          = Real.log 21 + Real.log L + Real.log (Real.log L) := by
        rw [Real.log_mul (by positivity) (ne_of_gt hlogpos),
          Real.log_mul (by norm_num) (ne_of_gt hLpos)]
      linarith [h2, h3.le, h3.ge]
    have := Finset.sum_le_card_nsmul U (fun k => Real.log (r k))
      (Real.log 21 + Real.log L + Real.log (Real.log L)) hpt
    simpa [nsmul_eq_mul] using this
  -- cardinality relations, in ℝ
  have hcards : (U.card : ℝ) + 2 * (I.card : ℝ) = (L : ℝ) - 1 := by
    have : ((U.card + 2 * I.card + 1 : ℕ) : ℝ) = (L : ℝ) := by exact_mod_cast hcompl'
    push_cast at this
    linarith
  have hIbig : 9 * (L : ℝ) / 400 ≤ (I.card : ℝ) := by linarith
  have hIleR : (I.card : ℝ) ≤ (L : ℝ) := by exact_mod_cast hIle
  have hUleR : (U.card : ℝ) ≤ (L : ℝ) := by exact_mod_cast hUle
  -- the analytic threshold
  have hthr : Real.log 2 + Real.log 21 + Real.log (Real.log L) ≤ α₀ / 80 * Real.log L :=
    log_threshold_bound hα0 (by linarith) hlogL
  -- assemble
  have e4 : (I.card : ℝ) * Real.log 2 ≤ (L : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_right hIleR hlog2
  have e5 : (9 * (L : ℝ) / 400) * (α₀ * Real.log L)
      ≤ (I.card : ℝ) * (α₀ * Real.log L) :=
    mul_le_mul_of_nonneg_right hIbig (by positivity)
  have e2 : (U.card : ℝ) * (Real.log 21 + Real.log (Real.log L))
      ≤ (L : ℝ) * (Real.log 21 + Real.log (Real.log L)) :=
    mul_le_mul_of_nonneg_right hUleR (by linarith)
  have hC : ((U.card : ℝ) + 2 * (I.card : ℝ)) * Real.log L = ((L : ℝ) - 1) * Real.log L := by
    rw [hcards]
  have hD : (L : ℝ) * (Real.log 2 + Real.log 21 + Real.log (Real.log L))
      ≤ (L : ℝ) * (α₀ / 80 * Real.log L) :=
    mul_le_mul_of_nonneg_left hthr (le_of_lt hLpos)
  rw [hCw]
  nlinarith [hsum1, hsum2, e4, e5, e2, hC, hD, hlogpos, hLpos]

/-- CONDITIONAL.  **Theorem 1.1** of the manuscript: `κ(L) ≤ (1-δ) L log L` for an
absolute `δ > 0` and all sufficiently large `L`. -/
theorem cover_cost (h : AnalyticInputs) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L → kappa L ≤ (1 - δ) * L * Real.log L := by
  obtain ⟨δ, hδ0, hδ1, L₀, hL₀⟩ := exists_lowweight_cover h
  refine ⟨δ, hδ0, L₀, ?_⟩
  intro L hL
  obtain ⟨C, hC⟩ := hL₀ L hL
  have h1 : kappa L ≤ Real.log (C.modulus : ℝ) := kappa_le_of_cover C
  rw [C.log_modulus_eq_weight] at h1
  linarith

/-! ## Step 6: from the low-weight cover to a small modulus -/

/-- A cover of weight at most `(1-δ) L log L` has modulus at most `((L+1)!)^{1-δ/2}`
once `log L ≥ 4/δ` (and `L ≥ 1`). -/
theorem modulus_le_of_weight {L : ℕ} (C : RainbowCover L) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hL1 : 1 ≤ L) (hlog : 4 / δ ≤ Real.log L)
    (hw : C.weight ≤ (1 - δ) * L * Real.log L) :
    (C.modulus : ℝ) ≤ ((L + 1).factorial : ℝ) ^ (1 - δ / 2) := by
  have hXpos : (0 : ℝ) < ((L + 1).factorial : ℝ) := by exact_mod_cast (L + 1).factorial_pos
  have hMpos : (0 : ℝ) < (C.modulus : ℝ) := by exact_mod_cast C.modulus_pos
  rw [Real.le_rpow_iff_log_le hMpos hXpos, C.log_modulus_eq_weight]
  have hfac : (L : ℝ) * Real.log L - 2 * L ≤ Real.log (((L + 1).factorial : ℝ)) :=
    log_factorial_succ_ge hL1
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL1
  have hlogpos : (0 : ℝ) < Real.log L := by
    have : (0 : ℝ) < 4 / δ := by positivity
    linarith
  have hkey : δ * Real.log L ≥ 4 := by
    rw [ge_iff_le, ← div_le_iff₀' hδ0]
    exact hlog
  -- `(1 - δ/2) log X ≥ (1 - δ/2)(L log L - 2L) ≥ (1 - δ) L log L ≥ weight`
  have h1 : (1 - δ / 2) * ((L : ℝ) * Real.log L - 2 * L)
      ≤ (1 - δ / 2) * Real.log (((L + 1).factorial : ℝ)) := by
    apply mul_le_mul_of_nonneg_left hfac (by linarith)
  have h2 : (1 - δ) * L * Real.log L ≤ (1 - δ / 2) * ((L : ℝ) * Real.log L - 2 * L) := by
    nlinarith [mul_le_mul_of_nonneg_left hkey (le_of_lt hLpos)]
  linarith

/-! ## The main conditional theorems -/

/-- CONDITIONAL.  **Theorem 1.2** of the manuscript (quantitative form of the auxiliary
problem), as a cardinality statement for the filtered `Finset` `goodSet L`:  for an
absolute `η > 0` and all large `L`, at least `X^η / (100 log L)` integers
`n ∈ (2·L!, X]`, `X = (L+1)!`, are `L`-rough and have `n - k!` composite for all
`1 ≤ k ≤ L`. -/
theorem main_quantitative (h : AnalyticInputs) :
    ∃ η : ℝ, 0 < η ∧ ∃ L₁ : ℕ, ∀ L : ℕ, L₁ ≤ L →
      ((L + 1).factorial : ℝ) ^ η / (100 * Real.log L) ≤ ((goodSet L).card : ℝ) := by
  obtain ⟨δ, hδ0, hδ1, L₀, hL₀⟩ := exists_lowweight_cover h
  obtain ⟨L₁, hL₁⟩ := transference (δ / 2) (by positivity) (by linarith)
  refine ⟨δ / 4, by positivity, max (max L₀ L₁) (max 1 ⌈Real.exp (4 / δ)⌉₊), ?_⟩
  intro L hL
  have hL₀' : L₀ ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL
  have hL₁' : L₁ ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL
  have hLone : 1 ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL
  have hLceil : ⌈Real.exp (4 / δ)⌉₊ ≤ L :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hL
  have hexp : Real.exp (4 / δ) ≤ (L : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hLceil)
  have hlog : 4 / δ ≤ Real.log L := by
    have := Real.log_le_log (Real.exp_pos _) hexp
    rwa [Real.log_exp] at this
  obtain ⟨C, hC⟩ := hL₀ L hL₀'
  have hmod := modulus_le_of_weight C hδ0 hδ1 hLone hlog hC
  have hfin := hL₁ L hL₁' C hmod
  have hexpeq : δ / 2 / 2 = δ / 4 := by ring
  rwa [hexpeq] at hfin

/-- CONDITIONAL.  The qualitative auxiliary problem of Erdős: for every sufficiently
large `L` there is an integer `n ∈ (L!, (L+1)!]`, all of whose prime factors exceed `L`,
such that `n - k!` is composite for every `1 ≤ k ≤ L`.

This is *not* Erdős Problem 1059: nothing is claimed about `n` being prime. -/
theorem auxiliary_erdos_problem (h : AnalyticInputs) :
    ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L → ∃ n : ℕ,
      L.factorial < n ∧
      n ≤ (L + 1).factorial ∧
      (∀ p : ℕ, p.Prime → p ∣ n → L < p) ∧
      ∀ k : ℕ, 1 ≤ k → k ≤ L → ¬ (n - k.factorial).Prime ∧ 1 < n - k.factorial := by
  obtain ⟨η, hη, L₁, hL₁⟩ := main_quantitative h
  refine ⟨max L₁ 2, ?_⟩
  intro L hL
  have hL₁' : L₁ ≤ L := le_trans (le_max_left _ _) hL
  have hL2 : 2 ≤ L := le_trans (le_max_right _ _) hL
  have hLR : (2 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL2
  have hlogpos : 0 < Real.log L := Real.log_pos (by linarith)
  have hXpos : (0 : ℝ) < ((L + 1).factorial : ℝ) := by
    exact_mod_cast (L + 1).factorial_pos
  have hpos : 0 < ((L + 1).factorial : ℝ) ^ η / (100 * Real.log L) := by
    apply div_pos (Real.rpow_pos_of_pos hXpos _)
    positivity
  have hcard : 0 < ((goodSet L).card : ℝ) := lt_of_lt_of_le hpos (hL₁ L hL₁')
  have hne : (goodSet L).Nonempty := by
    rw [← Finset.card_pos]
    exact_mod_cast hcard
  obtain ⟨n, hn⟩ := hne
  rw [mem_goodSet] at hn
  obtain ⟨⟨hn1, hn2⟩, hrough, hdiff⟩ := hn
  refine ⟨n, ?_, hn2, hrough, hdiff⟩
  have : 0 < L.factorial := L.factorial_pos
  omega

end FactorialHypergraph
