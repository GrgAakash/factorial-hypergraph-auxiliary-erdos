/-
# Applying the upper-bound sieve to the polynomial `G_{a,m}`

Layer 2 of the sieve estimate (A3): the *application* of the conventional dimension-one
upper-bound sieve `UpperBoundSieveDimOne` (see `FactorialHypergraph/A3Sieve.lean`) to the
sequence of values `G_{a,m}(t)`, `t ∈ T_{a,m}`.

All hypotheses of the sieve theorem are verified explicitly here:

* the weighted set `A` is the multiset of values of `G_{a,m}` (multiplicities are carried by
  the weight `w n = #{t ∈ T : G(t) = n}`), whose members are positive and whose total mass is
  `H = #T`;
* the sifting range is the finite set `P = sievePrimes m z` of primes `ℓ ≤ z` with `ℓ ∤ 10m`;
* the local density is the root count `ρ`, which is `≤ 2`, satisfies `ρ(ℓ)/ℓ ≤ 1/2` on `P`,
  and is multiplicative on the squarefree products of primes of `P`;
* the dimension-one condition is verified in both the anchored and the interval form, by the
  unconditional `dimension_condition` and `dimension_condition_interval`;
* the remainders are controlled by the local counting formula `abs_card_dvd_Gpoly_sub_le`;
* an index `t` with `G(t)` prime and `> L` survives the sieve because `z < L`.
-/
import FactorialHypergraph.A3Local
import FactorialHypergraph.A3Product
import FactorialHypergraph.A3Sieve

namespace FactorialHypergraph

open Finset

/-! ## Auxiliary counting lemmas -/

/-- `∑_{d ≤ M} τ(d) ≤ M (1 + log M)`. -/
theorem sum_card_divisors_le (M : ℕ) :
    ∑ d ∈ Finset.Icc 1 M, ((d.divisors.card : ℕ) : ℝ) ≤ (M : ℝ) * (1 + Real.log M) := by
  classical
  have hswap := sum_Icc_divisors_swap M (fun _ _ => (1 : ℝ))
  have hL : ∑ n ∈ Finset.Icc 1 M, ∑ d ∈ n.divisors, (1 : ℝ)
      = ∑ d ∈ Finset.Icc 1 M, ((d.divisors.card : ℕ) : ℝ) := by
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hR : ∑ d ∈ Finset.Icc 1 M, ∑ _m ∈ Finset.Icc 1 (M / d), (1 : ℝ)
      = ∑ d ∈ Finset.Icc 1 M, ((M / d : ℕ) : ℝ) := by
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.card_Icc]
    simp
  rw [hL, hR] at hswap
  rw [hswap]
  calc ∑ d ∈ Finset.Icc 1 M, ((M / d : ℕ) : ℝ)
      ≤ ∑ d ∈ Finset.Icc 1 M, (M : ℝ) * (1 / (d : ℝ)) := by
        refine Finset.sum_le_sum (fun d hd => ?_)
        simp only [Finset.mem_Icc] at hd
        have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd.1
        rw [mul_one_div, le_div_iff₀ hd0]
        exact_mod_cast Nat.div_mul_le_self M d
    _ = (M : ℝ) * ∑ d ∈ Finset.Icc 1 M, (1 : ℝ) / (d : ℝ) := by rw [Finset.mul_sum]
    _ ≤ (M : ℝ) * (1 + Real.log M) :=
        mul_le_mul_of_nonneg_left (sum_inv_le_one_add_log M) (by positivity)

/-- The root count is multiplicative on squarefree products of distinct primes. -/
theorem rootCount_prod_primes (S : Finset ℕ) (hS : ∀ ℓ ∈ S, Nat.Prime ℓ) :
    rootCount (∏ ℓ ∈ S, ℓ) = ∏ ℓ ∈ S, rootCount ℓ := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [rootCount_one]
  | insert p S hpS ih =>
    have hp : p.Prime := hS p (Finset.mem_insert_self p S)
    have hS' : ∀ ℓ ∈ S, Nat.Prime ℓ := fun ℓ hl => hS ℓ (Finset.mem_insert_of_mem hl)
    have hcop : Nat.Coprime p (∏ ℓ ∈ S, ℓ) := by
      refine Nat.Coprime.prod_right ?_
      intro ℓ hl
      exact (Nat.coprime_primes hp (hS' ℓ hl)).mpr (fun hcon => hpS (hcon ▸ hl))
    rw [Finset.prod_insert hpS, Finset.prod_insert hpS,
      rootCount_mul_of_coprime hp.ne_zero (Finset.prod_pos (fun ℓ hl => (hS' ℓ hl).pos)).ne' hcop,
      ih hS']

/-- Counting fibrewise: `#{t ∈ s : Q (f t)} = ∑_{n ∈ f(s), Q n} #{t ∈ s : f t = n}`. -/
theorem card_filter_comp_eq_sum (s : Finset ℕ) (f : ℕ → ℕ) (Q : ℕ → Prop) [DecidablePred Q] :
    ((s.filter (fun t => Q (f t))).card : ℝ)
      = ∑ n ∈ (s.image f).filter Q, ((s.filter (fun t => f t = n)).card : ℝ) := by
  classical
  have hmem : Set.MapsTo f ↑(s.filter (fun t => Q (f t))) ↑((s.image f).filter Q) := by
    intro t ht
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_image] at ht ⊢
    exact ⟨⟨t, ht.1, rfl⟩, ht.2⟩
  rw [← Nat.cast_sum, Finset.card_eq_sum_card_fiberwise hmem]
  congr 1
  refine Finset.sum_congr rfl (fun n hn => ?_)
  congr 1
  ext t
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨⟨ht, -⟩, hft⟩; exact ⟨ht, hft⟩
  · rintro ⟨ht, hft⟩
    refine ⟨⟨ht, ?_⟩, hft⟩
    have := (Finset.mem_filter.mp hn).2
    rwa [← hft] at this

/-! ## Coprimality of the sieve divisors -/

/-- Every divisor of `∏ P` is coprime to `m`. -/
theorem coprime_of_mem_sieveDivisors {m d : ℕ} {z : ℝ}
    (hd : d ∈ sieveDivisors (sievePrimes m z)) : Nat.Coprime d m ∧ 0 < d := by
  classical
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hd
  have hSsub : S ⊆ sievePrimes m z := Finset.mem_powerset.mp hS
  constructor
  · refine Nat.Coprime.prod_left ?_
    intro ℓ hl
    obtain ⟨-, hp, h10⟩ := mem_sievePrimes.mp (hSsub hl)
    refine (Nat.Prime.coprime_iff_not_dvd hp).mpr ?_
    intro hdvd
    exact h10 (Dvd.dvd.mul_left hdvd 10)
  · refine Finset.prod_pos (fun ℓ hl => ?_)
    exact (mem_sievePrimes.mp (hSsub hl)).2.1.pos

/-! ## The sieve bound for one pair `(a, m)` -/

open scoped Classical in
/-- **CONDITIONAL** (on `UpperBoundSieveDimOne`).  The sifted-set estimate for the values of
`G_{a,m}` on `T_{a,m}`: with `P = sievePrimes m z` and any level `D ≥ z^10`,

  `#{t ∈ T : G(t) prime, G(t) > L} ≤ C (H · V_m(z) + ∑_{d ∣ ∏P, d ≤ D} ρ(d))`.

The constant `C` is absolute (it depends only on the three absolute constants fed to the
sieve theorem). -/
theorem sieve_bound_single (hs : UpperBoundSieveDimOne) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L m a : ℕ) (z D : ℝ), 0 < m → a < m → m ∣ fq a →
      2 ≤ z → z ≤ (L : ℝ) → z ^ (10 : ℕ) ≤ D →
      (((Tset L m a).filter (fun t => Nat.Prime (Gpoly m a t) ∧ L < Gpoly m a t)).card : ℝ)
        ≤ C * (((Tset L m a).card : ℝ) * sieveProduct m z
            + ∑ d ∈ sieveDivisors (sievePrimes m z) with (((d : ℕ) : ℝ) ≤ D),
                (rootCount d : ℝ)) := by
  classical
  obtain ⟨C₁a, hC₁a0, hC₁a⟩ := dimension_condition
  obtain ⟨C₁b, hC₁b0, hC₁b⟩ := dimension_condition_interval
  set C₁ := max C₁a C₁b with hC₁def
  have hC₁0 : 0 ≤ C₁ := le_trans hC₁a0 (le_max_left _ _)
  obtain ⟨C, hCpos, hmain⟩ := hs C₁ 2 (1 / 2) hC₁0 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨C, hCpos, ?_⟩
  intro L m a z D hm ham hdvd hz2 hzL hD
  set T := Tset L m a with hT
  set G := Gpoly m a with hG
  set A := T.image G with hA
  set w : ℕ → ℝ := fun n => ((T.filter (fun t => G t = n)).card : ℝ) with hw
  set P := sievePrimes m z with hP
  set rho : ℕ → ℝ := fun n => (rootCount n : ℝ) with hrho
  have hz0 : (0 : ℝ) ≤ z := by linarith
  -- hypotheses of the sieve theorem
  have hApos : ∀ n ∈ A, 0 < n := by
    intro n hn
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hn
    exact Gpoly_pos hm hdvd t
  have hwnonneg : ∀ n, 0 ≤ w n := fun n => by positivity
  have hwsupp : ∀ n, n ∉ A → w n = 0 := by
    intro n hn
    simp only [hw, Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro t ht hcon
    exact hn (Finset.mem_image.mpr ⟨t, ht, hcon⟩)
  have hX : ((T.card : ℝ)) = ∑ n ∈ A, w n := by
    simp only [hA, hw]
    have h := card_filter_comp_eq_sum T G (fun _ => True)
    simpa using h
  have hPprime : ∀ ℓ ∈ P, Nat.Prime ℓ := fun ℓ hl => (mem_sievePrimes.mp hl).2.1
  have hPle : ∀ ℓ ∈ P, (ℓ : ℝ) ≤ z := by
    intro ℓ hl
    have := (mem_sievePrimes.mp hl).1
    calc (ℓ : ℝ) ≤ (⌊z⌋₊ : ℝ) := by exact_mod_cast this
      _ ≤ z := Nat.floor_le hz0
  have hrho0 : ∀ ℓ ∈ P, 0 ≤ rho ℓ := fun ℓ _ => by positivity
  have hrhok : ∀ ℓ ∈ P, rho ℓ ≤ 2 := by
    intro ℓ hl
    have := rootCount_le_two (hPprime ℓ hl)
    simp only [hrho]
    exact_mod_cast this
  have hrhoeps : ∀ ℓ ∈ P, rho ℓ / (ℓ : ℝ) ≤ 1 - 1 / 2 := by
    intro ℓ hl
    have hp := hPprime ℓ hl
    have hfac := (sieveProduct_factor_mem hl).1
    have hpos : (0 : ℝ) < (ℓ : ℝ) := by
      have : (2 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hp.two_le
      linarith
    have h := rootCount_of_mem_sievePrimes hl
    split_ifs at h with hchi
    · have h11 : (11 : ℕ) ≤ ℓ := eleven_le_of_chi5_eq_one hp ((chi5_eq_one_iff ℓ).mpr hchi)
      have h11' : (11 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast h11
      simp only [hrho, h]
      rw [div_le_iff₀ hpos]
      push_cast
      linarith
    · simp only [hrho, h]
      norm_num
  have hrhomul : ∀ S ⊆ P, rho (∏ ℓ ∈ S, ℓ) = ∏ ℓ ∈ S, rho ℓ := by
    intro S hSP
    simp only [hrho]
    rw [rootCount_prod_primes S (fun ℓ hl => hPprime ℓ (hSP hl)), Nat.cast_prod]
  have hdim : ∀ ww : ℝ, 2 ≤ ww →
      ∑ ℓ ∈ P with (((ℓ : ℕ) : ℝ) ≤ ww), rho ℓ * Real.log ℓ / (ℓ : ℝ) ≤ Real.log ww + C₁ :=
    fun ww hww => le_trans (hC₁a P hPprime ww hww) (by
      have hle : C₁a ≤ C₁ := le_max_left _ _
      linarith)
  have hdimI : ∀ w₁ w₂ : ℝ, 2 ≤ w₁ → w₁ ≤ w₂ →
      ∑ ℓ ∈ P with (w₁ < ((ℓ : ℕ) : ℝ) ∧ ((ℓ : ℕ) : ℝ) ≤ w₂), rho ℓ * Real.log ℓ / (ℓ : ℝ)
        ≤ Real.log (w₂ / w₁) + C₁ :=
    fun w₁ w₂ h1 h2 => le_trans (hC₁b P hPprime w₁ w₂ h1 h2) (by
      have hle : C₁b ≤ C₁ := le_max_right _ _
      linarith)
  have hconc := hmain A w P rho ((T.card : ℝ)) z D hApos hwnonneg hwsupp hX hPprime hPle hz2
    hrho0 hrhok hrhoeps hrhomul hdim hdimI hD
  -- the sifted sum dominates the count of prime values `> L`
  have hsift : (((Tset L m a).filter
      (fun t => Nat.Prime (Gpoly m a t) ∧ L < Gpoly m a t)).card : ℝ)
      ≤ ∑ n ∈ A with (∀ ℓ ∈ P, ¬ (ℓ ∣ n)), w n := by
    simp only [hA, hw]
    rw [← card_filter_comp_eq_sum T G (fun n => ∀ ℓ ∈ P, ¬ (ℓ ∣ n))]
    have hsub : (Tset L m a).filter (fun t => Nat.Prime (Gpoly m a t) ∧ L < Gpoly m a t)
        ⊆ T.filter (fun t => ∀ ℓ ∈ P, ¬ (ℓ ∣ G t)) := by
      intro t ht
      simp only [Finset.mem_filter] at ht ⊢
      refine ⟨ht.1, ?_⟩
      intro ℓ hl hdv
      have hp := hPprime ℓ hl
      have hq : Nat.Prime (G t) := ht.2.1
      have : ℓ = G t := ((Nat.prime_dvd_prime_iff_eq hp hq).mp hdv)
      have hlz : (ℓ : ℝ) ≤ z := hPle ℓ hl
      have hgt : (L : ℝ) < (G t : ℝ) := by exact_mod_cast ht.2.2
      rw [this] at hlz
      linarith
    exact_mod_cast Finset.card_le_card hsub
  -- the remainder terms
  have hrem : ∀ d ∈ (sieveDivisors P).filter (fun d => ((d : ℕ) : ℝ) ≤ D),
      |(∑ n ∈ A with (d ∣ n), w n) - ((T.card : ℝ)) * rho d / (d : ℝ)| ≤ rho d := by
    intro d hd
    obtain ⟨hcop, hdpos⟩ := coprime_of_mem_sieveDivisors (Finset.mem_filter.mp hd).1
    simp only [hA, hw]
    rw [← card_filter_comp_eq_sum T G (fun n => d ∣ n)]
    simpa [hrho, hT, hG, mul_div_assoc] using
      abs_card_dvd_Gpoly_sub_le (L := L) hm hdvd hdpos hcop
  have hremsum : (∑ d ∈ sieveDivisors P with (((d : ℕ) : ℝ) ≤ D),
        |(∑ n ∈ A with (d ∣ n), w n) - ((T.card : ℝ)) * rho d / (d : ℝ)|)
      ≤ ∑ d ∈ sieveDivisors P with (((d : ℕ) : ℝ) ≤ D), (rootCount d : ℝ) :=
    Finset.sum_le_sum hrem
  have hVeq : ∏ ℓ ∈ P, (1 - rho ℓ / (ℓ : ℝ)) = sieveProduct m z := rfl
  calc (((Tset L m a).filter
        (fun t => Nat.Prime (Gpoly m a t) ∧ L < Gpoly m a t)).card : ℝ)
      ≤ ∑ n ∈ A with (∀ ℓ ∈ P, ¬ (ℓ ∣ n)), w n := hsift
    _ ≤ C * (((T.card : ℝ)) * ∏ ℓ ∈ P, (1 - rho ℓ / (ℓ : ℝ))
          + ∑ d ∈ sieveDivisors P with (((d : ℕ) : ℝ) ≤ D),
              |(∑ n ∈ A with (d ∣ n), w n) - ((T.card : ℝ)) * rho d / (d : ℝ)|) := hconc
    _ ≤ C * (((Tset L m a).card : ℝ) * sieveProduct m z
          + ∑ d ∈ sieveDivisors (sievePrimes m z) with (((d : ℕ) : ℝ) ≤ D),
              (rootCount d : ℝ)) := by
        rw [hVeq]
        exact mul_le_mul_of_nonneg_left (by linarith) hCpos.le


/-! ## Summing the remainders -/

/-- `∑_{d ∣ ∏P, d ≤ D} ρ(d) ≤ D (1 + log D)`, using `ρ(d) ≤ τ(d)` and `∑_{d ≤ M} τ(d) ≤ M(1+log M)`. -/
theorem sum_rootCount_sieveDivisors_le (m : ℕ) (z D : ℝ) (hD : 1 ≤ D) :
    ∑ d ∈ sieveDivisors (sievePrimes m z) with (((d : ℕ) : ℝ) ≤ D), (rootCount d : ℝ)
      ≤ D * (1 + Real.log D) := by
  classical
  set M := ⌊D⌋₊ with hM
  have hM1 : 1 ≤ M := Nat.le_floor (by exact_mod_cast hD)
  have hsub : (sieveDivisors (sievePrimes m z)).filter (fun d => ((d : ℕ) : ℝ) ≤ D)
      ⊆ Finset.Icc 1 M := by
    intro d hd
    obtain ⟨hd1, hd2⟩ := Finset.mem_filter.mp hd
    obtain ⟨-, hpos⟩ := coprime_of_mem_sieveDivisors hd1
    exact Finset.mem_Icc.mpr ⟨hpos, Nat.le_floor hd2⟩
  calc ∑ d ∈ sieveDivisors (sievePrimes m z) with (((d : ℕ) : ℝ) ≤ D), (rootCount d : ℝ)
      ≤ ∑ d ∈ Finset.Icc 1 M, (rootCount d : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)
    _ ≤ ∑ d ∈ Finset.Icc 1 M, ((d.divisors.card : ℕ) : ℝ) := by
        refine Finset.sum_le_sum (fun d hd => ?_)
        have hd1 : d ≠ 0 := by have := (Finset.mem_Icc.mp hd).1; omega
        exact_mod_cast rootCount_le_card_divisors hd1
    _ ≤ (M : ℝ) * (1 + Real.log M) := sum_card_divisors_le M
    _ ≤ D * (1 + Real.log D) := by
        have hM0 : (1:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM1
        have hMD : (M : ℝ) ≤ D := Nat.floor_le (by linarith)
        have hlog : Real.log M ≤ Real.log D := Real.log_le_log (by linarith) hMD
        have hlogD : 0 ≤ Real.log D := Real.log_nonneg hD
        nlinarith


/-! ### Elementary real-analytic auxiliaries -/

/-- `H / log H ≤ 8 L /(m log L)` when `H ≤ 2L/m` and `log L / 4 ≤ log H`. -/
theorem div_log_le_aux {L m HR : ℝ} (hL0 : 0 < L) (hmR0 : 0 < m)
    (hHR2 : HR ≤ 2 * L / m) (hlogL100 : (100:ℝ) ≤ Real.log L)
    (hlogHRlow : Real.log L / 4 ≤ Real.log HR) (hlogHRpos : 0 < Real.log HR) :
    HR / Real.log HR ≤ 8 * (L / (m * Real.log L)) := by
  have hmlog : (0:ℝ) < m * Real.log L := by positivity
  rw [div_le_iff₀ hlogHRpos]
  have heq : 8 * (L / (m * Real.log L)) * Real.log HR
      = (8 * L * Real.log HR) / (m * Real.log L) := by ring
  rw [heq, le_div_iff₀ hmlog]
  have hHRm : HR * m ≤ 2 * L := (le_div_iff₀ hmR0).mp hHR2
  nlinarith [hHRm, hlogHRlow, hL0, hlogL100, hlogHRpos]

/-- Combining a main term and a remainder term into a single constant. -/
theorem combine_terms_aux {A B X Y C : ℝ} (hA : A ≤ 160 * C * X) (hB : B ≤ 4 * Y)
    (hX0 : 0 ≤ X) (hY0 : 0 ≤ Y) (hC : 0 < C) : A + B ≤ (160 * C + 4) * (X + Y) := by
  nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 160) hC.le) hY0,
    mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hX0]

/-! ## The sieve estimate for one pair `(a, m)`, in the manuscript's shape -/

open scoped Classical in
/-- **CONDITIONAL** (on `UpperBoundSieveDimOne` only).

The manuscript's estimate `S_{a,m} ≪ H h(m)/log L + H^{1/2} log L` with `H ≍ L/m`, uniformly
for `1 ≤ m ≤ √L` and every root `a` of `f` modulo `m`.  The sieve is applied with
`z = H^{1/20}` and `D = H^{1/2}` exactly as in the manuscript. -/
theorem card_prime_values_le (hs : UpperBoundSieveDimOne) :
    ∃ C : ℝ, 0 < C ∧ ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L → ∀ m : ℕ, 0 < m → (m : ℝ) ≤ Real.sqrt L →
      ∀ a : ℕ, a < m → m ∣ fq a →
        (((Tset L m a).filter (fun t => Nat.Prime (Gpoly m a t) ∧ L < Gpoly m a t)).card : ℝ)
          ≤ C * ((L : ℝ) * hFactor m / ((m : ℝ) * Real.log L)
                + Real.sqrt ((L : ℝ) / (m : ℝ)) * Real.log L) := by
  classical
  obtain ⟨Cs, hCs, hsieve⟩ := sieve_bound_single hs
  obtain ⟨C₂, hC₂, hV⟩ := sieveProduct_le
  refine ⟨Cs * (160 * C₂ + 4), by positivity, 2 ^ 170, ?_⟩
  intro L hL m hm hmsq a ham hdvd
  have hLR : (2:ℝ)^(170:ℕ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hL0 : (0:ℝ) < (L:ℝ) := lt_of_lt_of_le (by positivity) hLR
  have hmR1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hmR0 : (0:ℝ) < (m:ℝ) := by linarith
  have hsq85 : (2:ℝ)^(85:ℕ) ≤ Real.sqrt L := by
    rw [show ((2:ℝ)^(85:ℕ)) = Real.sqrt ((2:ℝ)^(170:ℕ)) by
      rw [show ((2:ℝ)^(170:ℕ)) = ((2:ℝ)^(85:ℕ))^2 by ring, Real.sqrt_sq (by positivity)]]
    exact Real.sqrt_le_sqrt hLR
  have hsqle : Real.sqrt L ≤ (L:ℝ)/(m:ℝ) := by
    have := div_le_div_of_nonneg_left hL0.le hmR0 hmsq
    rwa [Real.div_sqrt] at this
  have h285 : (2:ℝ) ≤ (2:ℝ)^(85:ℕ) := by norm_num
  set HR := ((Tset L m a).card : ℝ) with hHRdef
  have hHRlow : Real.sqrt L - 1 ≤ HR := by
    have := le_card_Tset L m a hm ham
    linarith
  have hHRhigh : HR ≤ (L:ℝ)/(m:ℝ) + 1 := card_Tset_le L m a hm
  have hHR2 : HR ≤ 2 * (L:ℝ) / (m:ℝ) := by
    have h1 : (2:ℝ) ≤ (L:ℝ)/(m:ℝ) := by linarith
    have : (2:ℝ) * (L:ℝ) / (m:ℝ) = 2 * ((L:ℝ)/(m:ℝ)) := by ring
    rw [this]; linarith
  have hHR80 : (2:ℝ)^(80:ℕ) ≤ HR := by
    have h : (2:ℝ)^(80:ℕ) ≤ (2:ℝ)^(85:ℕ) - 1 := by norm_num
    linarith
  have hHR0 : (0:ℝ) < HR := lt_of_lt_of_le (by positivity) hHR80
  have hHR1 : (1:ℝ) ≤ HR := by
    have : (1:ℝ) ≤ (2:ℝ)^(80:ℕ) := by norm_num
    linarith
  -- the sieve parameters
  set z := HR ^ ((1:ℝ)/20) with hzdef
  set D := HR ^ ((1:ℝ)/2) with hDdef
  have hz16 : (16:ℝ) ≤ z := by
    have h1 : ((2:ℝ)^(80:ℕ)) ^ ((1:ℝ)/20) = 16 := by
      rw [← Real.rpow_natCast (2:ℝ) 80, ← Real.rpow_mul (by norm_num)]
      norm_num
    calc (16:ℝ) = ((2:ℝ)^(80:ℕ)) ^ ((1:ℝ)/20) := h1.symm
      _ ≤ z := Real.rpow_le_rpow (by positivity) hHR80 (by norm_num)
  have hz2 : (2:ℝ) ≤ z := by linarith
  have hLge2 : (2:ℝ) ≤ (L:ℝ) := by nlinarith [hLR]
  have hLmL : (L:ℝ)/(m:ℝ) ≤ (L:ℝ) := by rw [div_le_iff₀ hmR0]; nlinarith
  have hHRL : HR ≤ 2 * (L:ℝ) := by
    have : (2:ℝ) * (L:ℝ) / (m:ℝ) = 2 * ((L:ℝ)/(m:ℝ)) := by ring
    rw [this] at hHR2; linarith
  have hzL : z ≤ (L:ℝ) := by
    have h19 : (2:ℝ) ≤ (L:ℝ)^(19:ℕ) := by
      calc (2:ℝ) ≤ (2:ℝ)^(19:ℕ) := by norm_num
        _ ≤ (L:ℝ)^(19:ℕ) := by gcongr
    have hHRle : HR ≤ (L:ℝ)^(20:ℕ) := by nlinarith
    have heq : ((L:ℝ)^(20:ℕ)) ^ ((1:ℝ)/20) = (L:ℝ) := by
      rw [← Real.rpow_natCast (L:ℝ) 20, ← Real.rpow_mul hL0.le]
      norm_num
    calc z ≤ ((L:ℝ)^(20:ℕ)) ^ ((1:ℝ)/20) := Real.rpow_le_rpow hHR0.le hHRle (by norm_num)
      _ = (L:ℝ) := heq
  have hzD : z ^ (10:ℕ) = D := by
    rw [hzdef, hDdef, ← Real.rpow_natCast _ 10, ← Real.rpow_mul hHR0.le]
    norm_num
  have hDsqrt : D = Real.sqrt HR := by rw [hDdef, Real.sqrt_eq_rpow]
  have hD1 : (1:ℝ) ≤ D := by rw [hDsqrt]; exact Real.one_le_sqrt.mpr hHR1
  have hlogz : Real.log z = Real.log HR / 20 := by rw [hzdef, Real.log_rpow hHR0]; ring
  have hlogD : Real.log D = Real.log HR / 2 := by rw [hDdef, Real.log_rpow hHR0]; ring
  -- logarithmic estimates
  have hlogL100 : (100:ℝ) ≤ Real.log L := by
    have h := Real.log_le_log (by positivity : (0:ℝ) < (2:ℝ)^(170:ℕ)) hLR
    rw [Real.log_pow] at h
    have h2 := Real.log_two_gt_d9
    push_cast at h
    nlinarith
  have hlog2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
  have hhalf : Real.sqrt L / 2 ≤ HR := by
    have h2s : (2:ℝ) ≤ Real.sqrt L := by linarith
    linarith
  have hlogHRlow : Real.log L / 4 ≤ Real.log HR := by
    have h1 : Real.log (Real.sqrt L / 2) ≤ Real.log HR :=
      Real.log_le_log (by positivity) hhalf
    rw [Real.log_div (by positivity) (by norm_num), Real.log_sqrt hL0.le] at h1
    linarith
  have hlogHRpos : (0:ℝ) < Real.log HR := by linarith
  have hlogHRnn : (0:ℝ) ≤ Real.log HR := hlogHRpos.le
  have hlogHRub : Real.log HR ≤ Real.log 2 + Real.log L := by
    have h := Real.log_le_log hHR0 hHRL
    rwa [Real.log_mul (by norm_num) (by positivity)] at h
  -- the sieve bound
  have hmain := hsieve L m a z D hm ham hdvd hz2 hzL (le_of_eq hzD)
  have hVb : sieveProduct m z ≤ C₂ * hFactor m / Real.log z := hV m hm z hz16
  have hrem := sum_rootCount_sieveDivisors_le m z D hD1
  -- main term
  have hkey : HR / Real.log HR ≤ 8 * ((L:ℝ)/((m:ℝ) * Real.log L)) :=
    div_log_le_aux hL0 hmR0 hHR2 hlogL100 hlogHRlow hlogHRpos
  have hhF : (0:ℝ) ≤ hFactor m := hFactor_nonneg
  have hmainterm : HR * sieveProduct m z
      ≤ 160 * C₂ * ((L:ℝ) * hFactor m / ((m:ℝ) * Real.log L)) := by
    have h1 : HR * sieveProduct m z ≤ HR * (C₂ * hFactor m / Real.log z) :=
      mul_le_mul_of_nonneg_left hVb hHR0.le
    have h2 : HR * (C₂ * hFactor m / Real.log z)
        = 20 * C₂ * hFactor m * (HR / Real.log HR) := by
      rw [hlogz]; field_simp
    have h3 : 20 * C₂ * hFactor m * (HR / Real.log HR)
        ≤ 20 * C₂ * hFactor m * (8 * ((L:ℝ)/((m:ℝ) * Real.log L))) :=
      mul_le_mul_of_nonneg_left hkey (by positivity)
    have h4 : 20 * C₂ * hFactor m * (8 * ((L:ℝ)/((m:ℝ) * Real.log L)))
        = 160 * C₂ * ((L:ℝ) * hFactor m / ((m:ℝ) * Real.log L)) := by ring
    linarith [h1, h2.le, h2.ge, h3, h4.le, h4.ge]
  -- remainder term
  have hremterm : D * (1 + Real.log D) ≤ 4 * (Real.sqrt ((L:ℝ)/(m:ℝ)) * Real.log L) := by
    have hDle : D ≤ 2 * Real.sqrt ((L:ℝ)/(m:ℝ)) := by
      rw [hDsqrt]
      have h1 : Real.sqrt HR ≤ Real.sqrt (4 * ((L:ℝ)/(m:ℝ))) := by
        refine Real.sqrt_le_sqrt ?_
        have hh : (0:ℝ) ≤ (L:ℝ)/(m:ℝ) := by positivity
        have : (2:ℝ) * (L:ℝ) / (m:ℝ) = 2 * ((L:ℝ)/(m:ℝ)) := by ring
        rw [this] at hHR2
        linarith
      have h2 : Real.sqrt (4 * ((L:ℝ)/(m:ℝ))) = 2 * Real.sqrt ((L:ℝ)/(m:ℝ)) := by
        rw [show (4:ℝ) * ((L:ℝ)/(m:ℝ)) = 2^2 * ((L:ℝ)/(m:ℝ)) by ring,
          Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
      linarith [h1, h2.le, h2.ge]
    have hlogDub : 1 + Real.log D ≤ 2 * Real.log L := by rw [hlogD]; linarith
    have h1 : (0:ℝ) ≤ 1 + Real.log D := by rw [hlogD]; linarith
    calc D * (1 + Real.log D) ≤ (2 * Real.sqrt ((L:ℝ)/(m:ℝ))) * (2 * Real.log L) :=
          mul_le_mul hDle hlogDub h1 (by positivity)
      _ = 4 * (Real.sqrt ((L:ℝ)/(m:ℝ)) * Real.log L) := by ring
  -- combine
  set X := (L:ℝ) * hFactor m / ((m:ℝ) * Real.log L) with hX
  set Y := Real.sqrt ((L:ℝ)/(m:ℝ)) * Real.log L with hY
  have hX0 : (0:ℝ) ≤ X := by rw [hX]; positivity
  have hY0 : (0:ℝ) ≤ Y := by rw [hY]; positivity
  have hfin : HR * sieveProduct m z
      + ∑ d ∈ sieveDivisors (sievePrimes m z) with (((d : ℕ) : ℝ) ≤ D), (rootCount d : ℝ)
      ≤ (160 * C₂ + 4) * (X + Y) := by
    exact combine_terms_aux hmainterm (hrem.trans hremterm) hX0 hY0 hC₂
  calc (((Tset L m a).filter (fun t => Nat.Prime (Gpoly m a t) ∧ L < Gpoly m a t)).card : ℝ)
      ≤ Cs * (HR * sieveProduct m z
          + ∑ d ∈ sieveDivisors (sievePrimes m z) with (((d : ℕ) : ℝ) ≤ D),
              (rootCount d : ℝ)) := hmain
    _ ≤ Cs * ((160 * C₂ + 4) * (X + Y)) := mul_le_mul_of_nonneg_left hfin hCs.le
    _ = Cs * (160 * C₂ + 4) * (X + Y) := by ring

end FactorialHypergraph
