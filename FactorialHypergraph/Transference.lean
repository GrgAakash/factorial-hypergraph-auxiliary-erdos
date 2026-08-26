/-
# The transference theorem

Formalization of Theorem 6.1 of the manuscript (transference theorem): a rainbow edge
cover whose modulus is at most `X^{1-η}` (with `X = (L+1)!`) produces many `L`-rough
integers `n ∈ (2·L!, X]` all of whose factorial differences `n - k!` (`1 ≤ k ≤ L`) are
composite.

**Deviation from the manuscript (explicitly recorded).**  The manuscript counts the
integers in the progression that are coprime to the primorial `W = ∏_{p ≤ L} p` by
Mertens' third theorem, `φ(W)/W ≥ 1/(4 log L)`, which is not available in mathlib.  We
replace it by the completely elementary bound `W ≤ 4^L` (`primorial_le_4_pow` in
mathlib; the statement was named `Nat.primorial_le_four_pow` in the request) together
with `φ(W) ≥ 1`.  This costs a factor `4^L` in the count, which is absorbed by halving
the exponent: we obtain

  `X^{η/2} / (100 log L) ≤ #(goodSet L)`      (instead of `X^{η}/(100 log L)`).

Since the exponent `η > 0` in the application is an unspecified absolute constant, this
exponent loss does not change the validity of either the qualitative auxiliary theorem
or the quantitative theorem `∃ η > 0, …`; it only changes the numerical value of the
admissible `η`.
-/
import FactorialHypergraph.CRTCover
import FactorialHypergraph.Estimates

namespace FactorialHypergraph

open Finset

/-! ## Compositeness from a proper divisor -/

theorem not_prime_of_proper_divisor {N d : ℕ} (hd : d ∣ N) (h1 : 1 < d) (h2 : d < N) :
    ¬ N.Prime := by
  intro hN
  rcases (Nat.Prime.eq_one_or_self_of_dvd hN d hd) with h | h <;> omega

/-! ## The arithmetic core of the transference argument -/

variable {L : ℕ}

/-- Every prime dividing the modulus of a rainbow edge cover exceeds `L`, so the modulus
is coprime to the primorial `W = ∏_{p ≤ L} p`. -/
theorem coprime_modulus_primorial (C : RainbowCover L) :
    Nat.Coprime C.modulus (primorial L) := by
  rw [RainbowCover.modulus_eq_prod]
  refine Nat.Coprime.prod_left ?_
  intro q hq
  have hqp : Nat.Prime q := C.prime_mem q hq
  have hqL : L < q := C.lt_mem q hq
  rw [Nat.Prime.coprime_iff_not_dvd hqp]
  intro hdvd
  obtain ⟨p, hp, hpq⟩ := (Nat.prime_iff.mp hqp).exists_mem_finset_dvd hdvd
  simp only [Finset.mem_filter, Finset.mem_range] at hp
  have : q ≤ p := Nat.le_of_dvd hp.2.pos hpq
  omega

/-- In any residue class modulo `P > 0` there is a representative just above a given
threshold `c`, namely inside `(c, c + 2P]`. -/
theorem exists_base {c P : ℕ} (hP : 0 < P) (r : ℕ) :
    ∃ base : ℕ, c < base ∧ base ≤ c + 2 * P ∧ base % P = r % P := by
  refine ⟨P * (c / P) + P + r % P, ?_, ?_, ?_⟩
  · have h1 := Nat.div_add_mod c P
    have h2 : c % P < P := Nat.mod_lt _ hP
    omega
  · have h1 := Nat.div_add_mod c P
    have h2 : r % P < P := Nat.mod_lt _ hP
    omega
  · have hrw : P * (c / P) + P + r % P = r % P + (c / P + 1) * P := by ring
    rw [hrw, Nat.add_mul_mod_self_right, Nat.mod_mod]

/-- **Arithmetic core.**  For `L ≥ 3` and a rainbow edge cover `C`, all the integers in a
single arithmetic progression of modulus `P = M(C)·W` starting just above `2·L!` are
`L`-rough and have all their factorial differences composite. -/
theorem exists_progression (hL : 3 ≤ L) (C : RainbowCover L) :
    ∃ base : ℕ, 2 * L.factorial < base ∧
      base ≤ 2 * L.factorial + 2 * (C.modulus * primorial L) ∧
      ∀ j : ℕ, base + j * (C.modulus * primorial L) ≤ (L + 1).factorial →
        base + j * (C.modulus * primorial L) ∈ goodSet L := by
  classical
  obtain ⟨A, hA, -⟩ := C.exists_crt_class
  set W : ℕ := primorial L with hWdef
  set M : ℕ := C.modulus with hMdef
  have hWpos : 0 < W := primorial_pos L
  have hMpos : 0 < M := C.modulus_pos
  have hcop : Nat.Coprime M W := coprime_modulus_primorial C
  obtain ⟨n₀, hn₀M, hn₀W⟩ := Nat.chineseRemainder hcop A 1
  set P : ℕ := M * W with hPdef
  have hPpos : 0 < P := Nat.mul_pos hMpos hWpos
  obtain ⟨base, hbase1, hbase2, hbase3⟩ := exists_base (c := 2 * L.factorial) hPpos n₀
  refine ⟨base, hbase1, hbase2, ?_⟩
  intro j hjX
  set n : ℕ := base + j * P with hn
  -- basic size facts
  have hfac_pos : 0 < L.factorial := L.factorial_pos
  have hlow : 2 * L.factorial < n := by
    simp only [hn]; omega
  -- `n ≡ n₀ (mod P)`
  have hnP : n ≡ n₀ [MOD P] := by
    show n % P = n₀ % P
    simp only [hn, Nat.add_mul_mod_self_right]
    exact hbase3
  have hnM : n ≡ A [MOD M] :=
    (Nat.ModEq.of_dvd ⟨W, rfl⟩ hnP).trans hn₀M
  have hnW : n ≡ 1 [MOD W] :=
    (Nat.ModEq.of_dvd ⟨M, by rw [hPdef]; ring⟩ hnP).trans hn₀W
  -- membership in the good set
  rw [mem_goodSet]
  refine ⟨⟨hlow, hjX⟩, ?_, ?_⟩
  · -- `L`-roughness
    intro p hp hpn
    by_contra hpL
    push_neg at hpL
    have hpW : p ∣ W := by
      rw [hWdef, primorial]
      exact Finset.dvd_prod_of_mem _ (by
        simp only [Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, hp⟩)
    have h1 : n ≡ 1 [MOD p] := Nat.ModEq.of_dvd hpW hnW
    have h2 : p ∣ n - 1 := (Nat.modEq_iff_dvd' (by omega)).mp h1.symm
    have h3 : p ∣ n - (n - 1) := Nat.dvd_sub hpn h2
    have h4 : n - (n - 1) = 1 := by omega
    rw [h4] at h3
    have := Nat.le_of_dvd one_pos h3
    have := hp.two_le
    omega
  · intro k hk1 hkL
    rcases Nat.lt_or_ge k 2 with hk | hk
    · -- `k = 1`: parity
      have hk1' : k = 1 := by omega
      subst hk1'
      have h2W : (2 : ℕ) ∣ W := by
        rw [hWdef, primorial]
        exact Finset.dvd_prod_of_mem _ (by
          simp only [Finset.mem_filter, Finset.mem_range]
          exact ⟨by omega, Nat.prime_two⟩)
      have h1 : n ≡ 1 [MOD 2] := Nat.ModEq.of_dvd h2W hnW
      have h2 : (2 : ℕ) ∣ n - 1 := (Nat.modEq_iff_dvd' (by omega)).mp h1.symm
      have hbig : 12 ≤ n := by
        have : 6 ≤ L.factorial := by
          calc 6 = Nat.factorial 3 := by norm_num
          _ ≤ L.factorial := Nat.factorial_le hL
        omega
      simp only [Nat.factorial_one]
      exact ⟨not_prime_of_proper_divisor h2 (by omega) (by omega), by omega⟩
    · -- `2 ≤ k ≤ L`: use the cover
      obtain ⟨q, hqQ, hqk⟩ := C.covers k (mem_V.mpr ⟨hk, hkL⟩)
      rw [mem_fiber] at hqk
      have hqM : q ∣ M := by
        rw [hMdef, RainbowCover.modulus_eq_prod]
        exact Finset.dvd_prod_of_mem _ hqQ
      have hnq : n ≡ k.factorial [MOD q] :=
        ((Nat.ModEq.of_dvd hqM hnM).trans (hA q hqQ)).trans hqk.2.symm
      have hkfac : k.factorial ≤ L.factorial := Nat.factorial_le hkL
      have hqdvd : q ∣ n - k.factorial :=
        (Nat.modEq_iff_dvd' (by omega)).mp hnq.symm
      have hqlt : q < L.factorial := C.mem_lt_factorial q hqQ
      have hq2 : 2 ≤ q := (C.prime_mem q hqQ).two_le
      exact ⟨not_prime_of_proper_divisor hqdvd (by omega) (by omega), by omega⟩


/-! ## Counting the resulting integers -/

/-- Every arithmetic progression of modulus `P = M(C)·W` inside `(2·L!, (L+1)!]` supplies
`m` distinct elements of `goodSet L`. -/
theorem card_goodSet_ge (hL : 3 ≤ L) (C : RainbowCover L) (m : ℕ)
    (hm : 2 * L.factorial + 2 * (C.modulus * primorial L)
        + m * (C.modulus * primorial L) ≤ (L + 1).factorial) :
    m ≤ (goodSet L).card := by
  classical
  obtain ⟨base, hb1, hb2, hb3⟩ := exists_progression hL C
  set P : ℕ := C.modulus * primorial L with hP
  have hPpos : 0 < P := Nat.mul_pos C.modulus_pos (primorial_pos L)
  have := Finset.card_le_card_of_injOn (f := fun j => base + j * P)
    (s := Finset.range m) (t := goodSet L) ?_ ?_
  · simpa using this
  · intro j hj
    refine hb3 j ?_
    have hjm : j ≤ m := le_of_lt (Finset.mem_range.mp hj)
    have hjP : j * P ≤ m * P := Nat.mul_le_mul_right _ hjm
    calc base + j * P ≤ (2 * L.factorial + 2 * P) + m * P :=
          Nat.add_le_add hb2 hjP
      _ ≤ (L + 1).factorial := hm
  · intro x _ y _ hxy
    simp only at hxy
    have hxy' : x * P = y * P := Nat.add_left_cancel hxy
    exact Nat.eq_of_mul_eq_mul_right hPpos hxy'

/-! ## The transference theorem -/

set_option maxHeartbeats 1000000 in
/-- **Transference theorem** (Theorem 6.1, with the explicitly recorded exponent loss
`η ↦ η/2` coming from the elementary replacement of Mertens' theorem by
`W ≤ 4^L`).  Any rainbow edge cover with modulus at most `X^{1-η}`, `X = (L+1)!`,
produces at least `X^{η/2}/(100 log L)` integers of `goodSet L`. -/
theorem transference (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) :
    ∃ L₀ : ℕ, ∀ L, L₀ ≤ L → ∀ C : RainbowCover L,
      (C.modulus : ℝ) ≤ ((L + 1).factorial : ℝ) ^ (1 - η) →
      ((L + 1).factorial : ℝ) ^ (η / 2) / (100 * Real.log L) ≤ ((goodSet L).card : ℝ) := by
  refine ⟨max 8 ⌈Real.exp (2 + 6 / η)⌉₊, ?_⟩
  intro L hL C hM
  have hL8 : 8 ≤ L := le_trans (le_max_left _ _) hL
  have hLexp : Real.exp (2 + 6 / η) ≤ (L : ℝ) := by
    have h1 : (⌈Real.exp (2 + 6 / η)⌉₊ : ℝ) ≤ (L : ℝ) := by
      exact_mod_cast le_trans (le_max_right _ _) hL
    exact le_trans (Nat.le_ceil _) h1
  have hLpos : (0 : ℝ) < (L : ℝ) := by positivity
  have hlogL : 2 + 6 / η ≤ Real.log L := by
    have := Real.log_le_log (Real.exp_pos _) hLexp
    rwa [Real.log_exp] at this
  have hlogL1 : (1 : ℝ) ≤ Real.log L := by
    have : (0 : ℝ) < 6 / η := by positivity
    linarith
  -- notation
  set Xn : ℕ := (L + 1).factorial with hXn
  set X : ℝ := (Xn : ℝ) with hX
  have hXnpos : 0 < Xn := (L+1).factorial_pos
  have hXpos : (0 : ℝ) < X := by rw [hX]; exact_mod_cast hXnpos
  have hLR : (8:ℝ) ≤ (L:ℝ) := by exact_mod_cast hL8
  -- the modulus of the auxiliary progression
  set P : ℕ := C.modulus * primorial L with hPdef
  have hPpos : 0 < P := Nat.mul_pos C.modulus_pos (primorial_pos L)
  have hW4 : ((primorial L : ℕ) : ℝ) ≤ 4 ^ L := by exact_mod_cast primorial_le_4_pow L
  have hPle : (P : ℝ) ≤ X ^ (1 - η) * 4 ^ L := by
    have hcast : ((P : ℕ) : ℝ) = (C.modulus : ℝ) * ((primorial L : ℕ) : ℝ) := by
      rw [hPdef]; push_cast; ring
    rw [hcast]
    exact mul_le_mul hM hW4 (by positivity) (by positivity)
  -- a lower bound for log X
  have hlogX : (L:ℝ) * Real.log L - 2 * L ≤ Real.log X := by
    rw [hX, hXn]; exact log_factorial_succ_ge (by omega)
  -- the key exponential inequality `4^(L+1) ≤ X^(η/2)`
  have hlog4 : Real.log 4 < 1.4 := by
    have h2 := Real.log_two_lt_d9
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; push_cast; ring
    rw [h4]; linarith
  have hkey : (4:ℝ) ^ (L+1) ≤ X ^ (η/2) := by
    have h4 : (4:ℝ)^(L+1) = Real.exp (Real.log 4 * ((L:ℝ)+1)) := by
      rw [← Real.rpow_natCast (4:ℝ) (L+1), Real.rpow_def_of_pos (by norm_num)]
      push_cast; ring_nf
    have hXr : X ^ (η/2) = Real.exp (Real.log X * (η/2)) := Real.rpow_def_of_pos hXpos _
    rw [h4, hXr, Real.exp_le_exp]
    have h6 : (6/η : ℝ) ≤ Real.log L - 2 := by linarith
    have hmul : (L:ℝ) * (6/η) ≤ (L:ℝ) * (Real.log L - 2) :=
      mul_le_mul_of_nonneg_left h6 (by linarith)
    have hLX : (L:ℝ) * (6/η) ≤ Real.log X := by nlinarith
    have hhalf : (0:ℝ) < η/2 := by linarith
    have hstep : (L:ℝ) * (6/η) * (η/2) ≤ Real.log X * (η/2) :=
      mul_le_mul_of_nonneg_right hLX (le_of_lt hhalf)
    have hval : (L:ℝ) * (6/η) * (η/2) = 3 * L := by field_simp; ring
    nlinarith
  -- consequently `P ≤ X/4`
  have hXhalf : X ^ (1 - η) * X ^ (η/2) = X ^ (1 - η/2) := by
    rw [← Real.rpow_add hXpos]; ring_nf
  have hPX : (P:ℝ) * 4 ≤ X := by
    have h1 : (P:ℝ) * 4 ≤ X ^ (1 - η) * 4 ^ L * 4 := by linarith
    have h2 : (4:ℝ) ^ L * 4 = 4 ^ (L+1) := by ring
    have h3 : X ^ (1 - η) * (4 ^ L * 4) ≤ X ^ (1 - η) * X ^ (η/2) := by
      apply mul_le_mul_of_nonneg_left (by rw [h2]; exact hkey) (le_of_lt (Real.rpow_pos_of_pos hXpos _))
    have h4 : X ^ (1 - η/2) ≤ X := by
      have hX1 : (1:ℝ) ≤ X := by
        rw [hX]; exact_mod_cast hXnpos
      calc X ^ (1 - η/2) ≤ X ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
        _ = X := Real.rpow_one X
    nlinarith [hXhalf]
  -- the number of usable terms of the progression
  have hXn4 : 4 * L.factorial ≤ Xn := by
    rw [hXn, Nat.factorial_succ]
    exact Nat.mul_le_mul_right _ (by omega)
  set D : ℕ := Xn - 2 * L.factorial with hD
  have hcastD : (D:ℝ) = X - 2 * (L.factorial : ℝ) := by
    rw [hD, hX]
    push_cast [Nat.cast_sub (by omega : 2 * L.factorial ≤ Xn)]
    ring
  have hfacX : 4 * (L.factorial : ℝ) ≤ X := by
    rw [hX]; exact_mod_cast hXn4
  have hDX : X / 2 ≤ (D:ℝ) := by rw [hcastD]; linarith
  have h2PDR : 2 * (P:ℝ) ≤ (D:ℝ) := by linarith
  have h2PD : 2 * P ≤ D := by exact_mod_cast h2PDR
  have hdiv2 : 2 ≤ D / P := (Nat.le_div_iff_mul_le hPpos).mpr (by omega)
  set m : ℕ := D / P - 2 with hm
  have hmP : m * P ≤ D - 2 * P := by
    have h1 : m * P = (D / P) * P - 2 * P := by rw [hm, Nat.sub_mul]
    have h2 : (D / P) * P ≤ D := Nat.div_mul_le_self _ _
    omega
  have hmbound : 2 * L.factorial + 2 * P + m * P ≤ Xn := by omega
  have hcard : m ≤ (goodSet L).card := card_goodSet_ge (by omega) C m hmbound
  -- the resulting lower bound
  have hPbound : (P:ℝ) * 4 ≤ X ^ (1 - η/2) := by
    have h2 : (4:ℝ) ^ L * 4 = 4 ^ (L+1) := by ring
    have h3 : X ^ (1 - η) * (4 ^ L * 4) ≤ X ^ (1 - η) * X ^ (η/2) :=
      mul_le_mul_of_nonneg_left (by rw [h2]; exact hkey)
        (le_of_lt (Real.rpow_pos_of_pos hXpos _))
    nlinarith [hXhalf]
  have hXsplit : X ^ (1 - η/2) * X ^ (η/2) = X := by
    rw [← Real.rpow_add hXpos]; norm_num
  have hSpos : (0:ℝ) < X ^ (η/2) := Real.rpow_pos_of_pos hXpos _
  have hbig : 2 * X ^ (η/2) * (P:ℝ) ≤ (D:ℝ) := by
    have e1 : 2 * X ^ (η/2) * (P:ℝ) = ((P:ℝ) * 4) * (X ^ (η/2) / 2) := by ring
    have e2 : X ^ (1 - η/2) * (X ^ (η/2) / 2) = X / 2 := by linear_combination hXsplit / 2
    have step : ((P:ℝ) * 4) * (X ^ (η/2) / 2) ≤ X ^ (1 - η/2) * (X ^ (η/2) / 2) :=
      mul_le_mul_of_nonneg_right hPbound (by positivity)
    rw [e1]
    linarith
  have hdivR : (D:ℝ)/(P:ℝ) - 1 ≤ ((D / P : ℕ) : ℝ) := by
    have hlt : D < (D / P + 1) * P := by
      have h1 := Nat.div_add_mod D P
      have h2 : D % P < P := Nat.mod_lt _ hPpos
      have h3 : (D / P + 1) * P = P * (D / P) + P := by ring
      omega
    have hPR : (0:ℝ) < (P:ℝ) := by exact_mod_cast hPpos
    have hltR : (D:ℝ) < (((D / P : ℕ) : ℝ) + 1) * (P:ℝ) := by exact_mod_cast hlt
    rw [sub_le_iff_le_add, div_le_iff₀ hPR]
    linarith
  have hmR : X ^ (η/2) ≤ (m:ℝ) := by
    have hPR : (0:ℝ) < (P:ℝ) := by exact_mod_cast hPpos
    have hcastm : (m:ℝ) = ((D / P : ℕ) : ℝ) - 2 := by
      rw [hm]; push_cast [Nat.cast_sub hdiv2]; ring
    have hdd : 2 * X ^ (η/2) ≤ (D:ℝ)/(P:ℝ) := by
      rw [le_div_iff₀ hPR]; linarith
    have h4le : (4:ℝ) ≤ 4 ^ (L+1) := by
      calc (4:ℝ) = 4 ^ 1 := by norm_num
        _ ≤ 4 ^ (L+1) := by
            apply pow_le_pow_right₀ (by norm_num) (by omega)
    linarith [hkey, hdivR, hcastm]
  have hlogpos : (1:ℝ) ≤ 100 * Real.log L := by linarith
  calc X ^ (η/2) / (100 * Real.log L) ≤ X ^ (η/2) := by
        apply div_le_self (le_of_lt hSpos) hlogpos
    _ ≤ (m:ℝ) := hmR
    _ ≤ ((goodSet L).card : ℝ) := Nat.cast_le.mpr hcard

end FactorialHypergraph
