/-
# Assembly of the small-complementary-factor sieve estimate (A3)

Layer 5.  The layers

* `FactorialHypergraph/A3Roots.lean`   (root counts `R(m)`, the factor `h(m)` and its majorant),
* `FactorialHypergraph/A3Local.lean`   (the polynomial `G_{a,m}` and the local counting formula),
* `FactorialHypergraph/A3Product.lean` (the dimension condition and the sieve product),
* `FactorialHypergraph/A3Euler.lean`   (the two sums over the complementary factors),
* `FactorialHypergraph/A3Apply.lean`   (the application of the sieve to `G_{a,m}`)

are combined here into the analytic input (A3), i.e. the field
`AnalyticInputs.smallCofactorSieve`, stated **verbatim**.

The result is CONDITIONAL on exactly one conventional external analytic theorem, stated in
full generality and with all hypotheses explicit:

* `UpperBoundSieveDimOne` (the dimension-one upper-bound sieve).

It does not mention the quadratic `f(t) = t² + 3t + 1` and is not a renaming of (A3).
(The Mertens input for arithmetic progressions that the manuscript also appeals to is
**not** assumed: the consequence actually needed, `∑_{p ≤ N, χ₅(p) = 1} 1/p
= (log log N)/2 + O(1)`, is proved unconditionally in
`FactorialHypergraph/MertensSecond.lean`.)
-/
import FactorialHypergraph.A3Apply

namespace FactorialHypergraph

open Finset

/-! ## The union bound over complementary factors and roots -/

open scoped Classical in
theorem card_smallCofactorSet_le_sum (α : ℝ) (L Y : ℕ)
    (hY : ∀ m : ℕ, 1 ≤ m → (m : ℝ) ≤ (L : ℝ) ^ α → m ≤ Y) :
    (smallCofactorSet α L).card
      ≤ ∑ m ∈ Finset.Icc 1 Y, ∑ a ∈ (Finset.range m).filter (fun a => m ∣ fq a),
          ((Tset L m a).filter
            (fun t => Nat.Prime (Gpoly m a t) ∧ L < Gpoly m a t)).card := by
  classical
  have hsub : smallCofactorSet α L ⊆
      (Finset.Icc 1 Y).biUnion (fun m =>
        ((Finset.range m).filter (fun a => m ∣ fq a)).biUnion (fun a =>
          ((Tset L m a).filter
            (fun t => Nat.Prime (Gpoly m a t) ∧ L < Gpoly m a t)).image
              (fun t => a + m * t))) := by
    intro i hi
    obtain ⟨⟨hi1, hiL⟩, m, q, hq, hfi, hmL, hLq⟩ := mem_smallCofactorSet.mp hi
    have hfqpos : 0 < fq i := by unfold fq; positivity
    have hm0 : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · rw [h] at hfi; simp at hfi; omega
      · exact h
    have hmY : m ≤ Y := hY m hm0 hmL
    set a := i % m with ha
    set t := i / m with ht
    have hia : i = a + m * t := (Nat.mod_add_div i m).symm
    have ham : a < m := Nat.mod_lt _ hm0
    have hdvd : m ∣ fq a := by
      have hcong : a ≡ i [MOD m] := Nat.mod_modEq i m
      exact (dvd_fq_congr hcong).mpr ⟨q, hfi⟩
    have hG : Gpoly m a t = q := by
      have hval : fq (a + m * t) = m * q := by rw [← hia]; exact hfi
      unfold Gpoly
      rw [hval, Nat.mul_div_cancel_left _ hm0]
    refine Finset.mem_biUnion.mpr ⟨m, Finset.mem_Icc.mpr ⟨hm0, hmY⟩, ?_⟩
    refine Finset.mem_biUnion.mpr ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ham, hdvd⟩, ?_⟩
    refine Finset.mem_image.mpr ⟨t, ?_, hia.symm⟩
    refine Finset.mem_filter.mpr ⟨(mem_Tset hm0).mpr ⟨by omega, by omega⟩, ?_⟩
    rw [hG]
    exact ⟨hq, hLq⟩
  calc (smallCofactorSet α L).card ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ m ∈ Finset.Icc 1 Y, (((Finset.range m).filter (fun a => m ∣ fq a)).biUnion (fun a =>
          ((Tset L m a).filter
            (fun t => Nat.Prime (Gpoly m a t) ∧ L < Gpoly m a t)).image
              (fun t => a + m * t))).card := Finset.card_biUnion_le
    _ ≤ ∑ m ∈ Finset.Icc 1 Y, ∑ a ∈ (Finset.range m).filter (fun a => m ∣ fq a),
          ((Tset L m a).filter
            (fun t => Nat.Prime (Gpoly m a t) ∧ L < Gpoly m a t)).card := by
        refine Finset.sum_le_sum (fun m _ => ?_)
        exact le_trans Finset.card_biUnion_le (Finset.sum_le_sum (fun a _ => Finset.card_image_le))

open scoped Classical in
theorem smallCofactorSieve_of_inputs (hs : UpperBoundSieveDimOne) :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∃ L₀ : ℕ, ∀ α : ℝ, 0 < α → α ≤ 1 / 2 →
      ∀ L : ℕ, L₀ ≤ L →
        ((smallCofactorSet α L).card : ℝ)
          ≤ C₀ * (α * L + (L : ℝ) / Real.log L + (L : ℝ) ^ ((1 + α) / 2) * (Real.log L) ^ 2) := by
  classical
  obtain ⟨C, hC, Lc, hcard⟩ := card_prime_values_le hs
  obtain ⟨C₃, hC₃, hsum1⟩ := sum_gMaj_div_le
  refine ⟨max 1 (C * C₃ + 3 * C), le_max_left _ _, max Lc 8, ?_⟩
  intro α hα hα2 L hL
  set C₀ := max 1 (C * C₃ + 3 * C) with hC₀def
  have hLc : Lc ≤ L := le_trans (le_max_left _ _) hL
  have hL8 : 8 ≤ L := le_trans (le_max_right _ _) hL
  have hLR8 : (8:ℝ) ≤ (L:ℝ) := by exact_mod_cast hL8
  have hL0 : (0:ℝ) < (L:ℝ) := by linarith
  have hL1 : (1:ℝ) ≤ (L:ℝ) := by linarith
  have hlogL1 : (1:ℝ) ≤ Real.log L := by
    have h := Real.log_le_log (by norm_num : (0:ℝ) < 8) hLR8
    rw [show (8:ℝ) = 2^(3:ℕ) by norm_num, Real.log_pow] at h
    have h2 := Real.log_two_gt_d9
    push_cast at h
    linarith
  have hlogL0 : (0:ℝ) < Real.log L := by linarith
  -- the range of complementary factors
  set Y := ⌊(L:ℝ)^α⌋₊ with hYdef
  have hLa1 : (1:ℝ) ≤ (L:ℝ)^α := Real.one_le_rpow hL1 hα.le
  have hY1 : 1 ≤ Y := Nat.le_floor (by exact_mod_cast hLa1)
  have hY0 : (0:ℝ) < (Y:ℝ) := by exact_mod_cast hY1
  have hYle : (Y:ℝ) ≤ (L:ℝ)^α := Nat.floor_le (by positivity)
  have hYsqrt : (Y:ℝ) ≤ Real.sqrt L := by
    have h : (L:ℝ)^α ≤ (L:ℝ)^((1:ℝ)/2) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
    rw [Real.sqrt_eq_rpow]
    linarith
  have hlogY : Real.log Y ≤ α * Real.log L := by
    have h := Real.log_le_log hY0 hYle
    rwa [Real.log_rpow hL0] at h
  have hlogY0 : (0:ℝ) ≤ Real.log Y := Real.log_nonneg (by exact_mod_cast hY1)
  -- the union bound
  have hub := card_smallCofactorSet_le_sum α L Y (fun m _ h => Nat.le_floor h)
  have hubR : ((smallCofactorSet α L).card : ℝ)
      ≤ ∑ m ∈ Finset.Icc 1 Y, ∑ a ∈ (Finset.range m).filter (fun a => m ∣ fq a),
          (((Tset L m a).filter
            (fun t => Nat.Prime (Gpoly m a t) ∧ L < Gpoly m a t)).card : ℝ) := by
    exact_mod_cast hub
  -- the bound for a single modulus `m`
  have hper : ∀ m ∈ Finset.Icc 1 Y,
      (∑ a ∈ (Finset.range m).filter (fun a => m ∣ fq a),
        (((Tset L m a).filter
          (fun t => Nat.Prime (Gpoly m a t) ∧ L < Gpoly m a t)).card : ℝ))
      ≤ C * ((L:ℝ)/Real.log L) * (gMaj m / (m:ℝ))
        + C * Real.log L * Real.sqrt L * ((rootCount m : ℝ) / Real.sqrt m) := by
    intro m hm
    obtain ⟨hm1, hmY⟩ := Finset.mem_Icc.mp hm
    have hm0 : 0 < m := hm1
    have hmR1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm1
    have hmR0 : (0:ℝ) < (m:ℝ) := by linarith
    have hmsq : (m:ℝ) ≤ Real.sqrt L := le_trans (by exact_mod_cast hmY) hYsqrt
    have hbound : ∀ a ∈ (Finset.range m).filter (fun a => m ∣ fq a),
        (((Tset L m a).filter
          (fun t => Nat.Prime (Gpoly m a t) ∧ L < Gpoly m a t)).card : ℝ)
        ≤ C * ((L : ℝ) * hFactor m / ((m : ℝ) * Real.log L)
              + Real.sqrt ((L : ℝ) / (m : ℝ)) * Real.log L) := by
      intro a ha
      obtain ⟨ha1, ha2⟩ := Finset.mem_filter.mp ha
      exact hcard L hLc m hm0 hmsq a (Finset.mem_range.mp ha1) ha2
    have hsum := Finset.sum_le_sum hbound
    rw [Finset.sum_const, nsmul_eq_mul] at hsum
    have hcardeq : (((Finset.range m).filter (fun a => m ∣ fq a)).card : ℝ)
        = (rootCount m : ℝ) := by
      norm_cast
    rw [hcardeq] at hsum
    refine hsum.trans ?_
    have hsqdiv : Real.sqrt ((L:ℝ)/(m:ℝ)) = Real.sqrt L / Real.sqrt m := by
      exact Real.sqrt_div hL0.le _
    rw [hsqdiv]
    have hexpand : (rootCount m : ℝ) * (C * ((L : ℝ) * hFactor m / ((m : ℝ) * Real.log L)
          + Real.sqrt L / Real.sqrt m * Real.log L))
        = C * ((L:ℝ)/Real.log L) * (((rootCount m : ℝ) * hFactor m) / (m:ℝ))
          + C * Real.log L * Real.sqrt L * ((rootCount m : ℝ) / Real.sqrt m) := by
      field_simp
    rw [hexpand]
    have hmaj : (rootCount m : ℝ) * hFactor m ≤ gMaj m := rootCount_mul_hFactor_le (by omega)
    have hfac : (0:ℝ) ≤ C * ((L:ℝ)/Real.log L) := by positivity
    have : C * ((L:ℝ)/Real.log L) * (((rootCount m : ℝ) * hFactor m) / (m:ℝ))
        ≤ C * ((L:ℝ)/Real.log L) * (gMaj m / (m:ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ hfac
      gcongr
    linarith
  have hstep := le_trans hubR (Finset.sum_le_sum hper)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hstep
  -- the two sums over complementary factors
  have hS1 := hsum1 Y hY1
  have hS2 := sum_rootCount_div_sqrt_le Y
  have hterm1 : C * ((L:ℝ)/Real.log L) * (∑ m ∈ Finset.Icc 1 Y, gMaj m / (m:ℝ))
      ≤ C * C₃ * (α * (L:ℝ) + (L:ℝ)/Real.log L) := by
    have h1 : C * ((L:ℝ)/Real.log L) * (∑ m ∈ Finset.Icc 1 Y, gMaj m / (m:ℝ))
        ≤ C * ((L:ℝ)/Real.log L) * (C₃ * (1 + Real.log Y)) :=
      mul_le_mul_of_nonneg_left hS1 (by positivity)
    have h2 : C * ((L:ℝ)/Real.log L) * (C₃ * (1 + Real.log Y))
        ≤ C * ((L:ℝ)/Real.log L) * (C₃ * (1 + α * Real.log L)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ hC₃.le
      linarith
    have h3 : C * ((L:ℝ)/Real.log L) * (C₃ * (1 + α * Real.log L))
        = C * C₃ * (α * (L:ℝ) + (L:ℝ)/Real.log L) := by
      field_simp
      ring
    linarith
  have hterm2 : C * Real.log L * Real.sqrt L
        * (∑ m ∈ Finset.Icc 1 Y, (rootCount m : ℝ) / Real.sqrt m)
      ≤ 3 * C * ((L:ℝ)^((1+α)/2) * (Real.log L)^2) := by
    have h1 : C * Real.log L * Real.sqrt L
          * (∑ m ∈ Finset.Icc 1 Y, (rootCount m : ℝ) / Real.sqrt m)
        ≤ C * Real.log L * Real.sqrt L * (2 * Real.sqrt Y * (1 + Real.log Y)) :=
      mul_le_mul_of_nonneg_left hS2 (by positivity)
    have hprod : Real.sqrt L * Real.sqrt Y ≤ (L:ℝ)^((1+α)/2) := by
      have h2 : Real.sqrt (Y:ℝ) ≤ (L:ℝ)^(α/2) := by
        have h3 : Real.sqrt (Y:ℝ) ≤ Real.sqrt ((L:ℝ)^α) := Real.sqrt_le_sqrt hYle
        have hrw : Real.sqrt ((L:ℝ)^α) = (L:ℝ)^(α/2) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hL0.le]
          ring_nf
        rwa [hrw] at h3
      have h4 : Real.sqrt (L:ℝ) = (L:ℝ)^((1:ℝ)/2) := Real.sqrt_eq_rpow _
      rw [h4]
      calc (L:ℝ)^((1:ℝ)/2) * Real.sqrt Y ≤ (L:ℝ)^((1:ℝ)/2) * (L:ℝ)^(α/2) := by
            apply mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = (L:ℝ)^((1+α)/2) := by
            rw [← Real.rpow_add hL0]; ring_nf
    have hlogfac : (1 + Real.log Y) * Real.log L ≤ (3/2) * (Real.log L)^2 := by
      nlinarith [hlogY, hlogL1, hα2, hα, Real.log_nonneg (by exact_mod_cast hY1 : (1:ℝ) ≤ (Y:ℝ))]
    have h5 : C * Real.log L * Real.sqrt L * (2 * Real.sqrt Y * (1 + Real.log Y))
        = 2 * C * (Real.sqrt L * Real.sqrt Y) * ((1 + Real.log Y) * Real.log L) := by ring
    have h6 : 2 * C * (Real.sqrt L * Real.sqrt Y) * ((1 + Real.log Y) * Real.log L)
        ≤ 2 * C * ((L:ℝ)^((1+α)/2)) * ((3/2) * (Real.log L)^2) := by
      have hA : (0:ℝ) ≤ Real.sqrt L * Real.sqrt Y := by positivity
      have hB : (0:ℝ) ≤ (1 + Real.log Y) * Real.log L := by positivity
      have hC2 : (0:ℝ) ≤ 2 * C := by linarith
      have hstep : (Real.sqrt L * Real.sqrt Y) * ((1 + Real.log Y) * Real.log L)
          ≤ (L:ℝ)^((1+α)/2) * ((3/2) * (Real.log L)^2) :=
        mul_le_mul hprod hlogfac hB (Real.rpow_nonneg hL0.le _)
      calc 2 * C * (Real.sqrt L * Real.sqrt Y) * ((1 + Real.log Y) * Real.log L)
          = 2 * C * ((Real.sqrt L * Real.sqrt Y) * ((1 + Real.log Y) * Real.log L)) := by ring
        _ ≤ 2 * C * ((L:ℝ)^((1+α)/2) * ((3/2) * (Real.log L)^2)) :=
            mul_le_mul_of_nonneg_left hstep hC2
        _ = 2 * C * ((L:ℝ)^((1+α)/2)) * ((3/2) * (Real.log L)^2) := by ring
    have h7 : 2 * C * ((L:ℝ)^((1+α)/2)) * ((3/2) * (Real.log L)^2)
        = 3 * C * ((L:ℝ)^((1+α)/2) * (Real.log L)^2) := by ring
    linarith
  -- final combination
  have hX1 : (0:ℝ) ≤ α * (L:ℝ) := by positivity
  have hX2 : (0:ℝ) ≤ (L:ℝ)/Real.log L := by positivity
  have hX3 : (0:ℝ) ≤ (L:ℝ)^((1+α)/2) * (Real.log L)^2 := by positivity
  have hle1 : C * C₃ ≤ C₀ := le_trans (by linarith) (le_max_right 1 (C * C₃ + 3 * C))
  have hle2 : 3 * C ≤ C₀ := le_trans (by nlinarith) (le_max_right 1 (C * C₃ + 3 * C))
  have e1 : C * C₃ * (α * (L:ℝ) + (L:ℝ)/Real.log L)
      ≤ C₀ * (α * (L:ℝ) + (L:ℝ)/Real.log L) :=
    mul_le_mul_of_nonneg_right hle1 (by linarith)
  have e2 : 3 * C * ((L:ℝ)^((1+α)/2) * (Real.log L)^2)
      ≤ C₀ * ((L:ℝ)^((1+α)/2) * (Real.log L)^2) :=
    mul_le_mul_of_nonneg_right hle2 hX3
  have e3 : C₀ * (α * (L:ℝ) + (L:ℝ)/Real.log L)
        + C₀ * ((L:ℝ)^((1+α)/2) * (Real.log L)^2)
      = C₀ * (α * (L:ℝ) + (L:ℝ)/Real.log L + (L:ℝ)^((1+α)/2) * (Real.log L)^2) := by ring
  linarith

end FactorialHypergraph
