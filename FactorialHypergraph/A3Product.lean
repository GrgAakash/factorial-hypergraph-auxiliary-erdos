/-
# The sieve product and the dimension condition

Layer 3 of the sieve estimate (A3).

* `dimension_condition` — **unconditional**: for every finite set `P` of primes and every
  `w ≥ 2`,  `∑_{ℓ ∈ P, ℓ ≤ w} ρ(ℓ) log ℓ / ℓ ≤ log w + C₁`, with an absolute `C₁`.  This is
  the hypothesis of the sieve theorem (`UpperBoundSieveDimOne`) and it follows from the
  unconditional estimate `mertensRoots_unconditional` of `FactorialHypergraph/MertensRoots.lean`
  (a one-sided, logarithmically weighted bound is exactly what is needed here).
* `sieveProduct_le` — **unconditional** (it uses the Mertens estimate `sum_inv_primes_chi5`,
  proved in `FactorialHypergraph/MertensSecond.lean`):
  `V_m(z) = ∏_{ℓ ≤ z, ℓ ∤ 10m} (1 - ρ(ℓ)/ℓ) ≪ h(m)/log z`, uniformly in `m` and `z`.
-/
import FactorialHypergraph.A3Euler
import FactorialHypergraph.MertensLower
import FactorialHypergraph.MertensRoots

namespace FactorialHypergraph

open Finset

/-! ## The dimension condition -/

open scoped Classical in
/-- **Unconditional dimension condition (κ = 1).**  Uniformly for every finite set `P` of
primes and every `w ≥ 2`. -/
theorem dimension_condition :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ P : Finset ℕ, (∀ ℓ ∈ P, Nat.Prime ℓ) → ∀ w : ℝ, 2 ≤ w →
      ∑ ℓ ∈ P with (((ℓ : ℕ) : ℝ) ≤ w), (rootCount ℓ : ℝ) * Real.log ℓ / (ℓ : ℝ)
        ≤ Real.log w + C₁ := by
  obtain ⟨C, hC0, hC⟩ := mertensRoots_unconditional
  refine ⟨C, hC0, ?_⟩
  intro P hP w hw
  have hw0 : (0 : ℝ) < w := by linarith
  set W := ⌊w⌋₊ with hW
  have hW2 : 2 ≤ W := by
    rw [hW]
    exact Nat.le_floor (by exact_mod_cast hw)
  -- termwise comparison and inclusion into `primesLE W`
  have hsub : (P.filter (fun ℓ => ((ℓ : ℕ) : ℝ) ≤ w)) ⊆ primesLE W := by
    intro ℓ hl
    simp only [Finset.mem_filter] at hl
    refine mem_primesLE.mpr ⟨?_, hP ℓ hl.1⟩
    exact Nat.le_floor hl.2
  have hterm : ∀ ℓ ∈ P.filter (fun ℓ => ((ℓ : ℕ) : ℝ) ≤ w),
      (rootCount ℓ : ℝ) * Real.log ℓ / (ℓ : ℝ)
        ≤ (rootCount ℓ : ℝ) * Real.log ℓ / ((ℓ : ℝ) - 1) := by
    intro ℓ hl
    have hp : ℓ.Prime := hP ℓ (Finset.mem_filter.mp hl).1
    have h2 : (2 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hp.two_le
    have hnum : 0 ≤ (rootCount ℓ : ℝ) * Real.log ℓ :=
      mul_nonneg (by positivity) (Real.log_natCast_nonneg ℓ)
    gcongr <;> linarith
  have hnonneg : ∀ ℓ ∈ primesLE W, 0 ≤ (rootCount ℓ : ℝ) * Real.log ℓ / ((ℓ : ℝ) - 1) := by
    intro ℓ hl
    have hp : ℓ.Prime := (mem_primesLE.mp hl).2
    have h2 : (2 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hp.two_le
    exact div_nonneg (mul_nonneg (by positivity) (Real.log_natCast_nonneg ℓ)) (by linarith)
  have hlogW : Real.log W ≤ Real.log w := by
    apply Real.log_le_log
    · have : (2 : ℝ) ≤ (W : ℝ) := by exact_mod_cast hW2
      linarith
    · exact Nat.floor_le hw0.le
  calc ∑ ℓ ∈ P with (((ℓ : ℕ) : ℝ) ≤ w), (rootCount ℓ : ℝ) * Real.log ℓ / (ℓ : ℝ)
      ≤ ∑ ℓ ∈ P with (((ℓ : ℕ) : ℝ) ≤ w), (rootCount ℓ : ℝ) * Real.log ℓ / ((ℓ : ℝ) - 1) :=
        Finset.sum_le_sum hterm
    _ ≤ ∑ ℓ ∈ primesLE W, (rootCount ℓ : ℝ) * Real.log ℓ / ((ℓ : ℝ) - 1) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i hi _ => hnonneg i hi)
    _ ≤ Real.log W + C := hC W hW2
    _ ≤ Real.log w + C := by linarith

open scoped Classical in
/-- **Unconditional dimension condition (κ = 1), interval form** — the conventional
Axiom 2′ of the sieve literature.  Uniformly for every finite set `P` of primes and all
`2 ≤ w₁ ≤ w₂`,

  `∑_{ℓ ∈ P, w₁ < ℓ ≤ w₂} ρ(ℓ) log ℓ / ℓ ≤ log (w₂/w₁) + C₁`.

Unlike the anchored form `dimension_condition` (its special case `w₁ = 2`, up to the value
of the constant), this bounds the *local* dimension of the sieve on every dyadic range, and
it is what the fundamental lemma of sieve theory actually assumes.  Its proof needs the
two-sided Mertens estimate: the upper bound `mertensRoots_upper_div_p` at `w₂` and the
lower bound `mertensRoots_lower` at `w₁`, both unconditional. -/
theorem dimension_condition_interval :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ P : Finset ℕ, (∀ ℓ ∈ P, Nat.Prime ℓ) → ∀ w₁ w₂ : ℝ, 2 ≤ w₁ → w₁ ≤ w₂ →
      ∑ ℓ ∈ P with (w₁ < ((ℓ : ℕ) : ℝ) ∧ ((ℓ : ℕ) : ℝ) ≤ w₂),
          (rootCount ℓ : ℝ) * Real.log ℓ / (ℓ : ℝ)
        ≤ Real.log (w₂ / w₁) + C₁ := by
  classical
  obtain ⟨Cu, hCu0, hCu⟩ := mertensRoots_upper_div_p
  obtain ⟨Cl, hCl0, hCl⟩ := mertensRoots_lower
  refine ⟨Cu + Cl + Real.log 2, by positivity, ?_⟩
  intro P hP w₁ w₂ hw₁ hw₁₂
  have hw₁0 : (0 : ℝ) < w₁ := by linarith
  have hw₂0 : (0 : ℝ) < w₂ := by linarith
  set W₁ := ⌊w₁⌋₊ with hW₁
  set W₂ := ⌊w₂⌋₊ with hW₂
  have hW₁2 : 2 ≤ W₁ := Nat.le_floor (by exact_mod_cast hw₁)
  have hW₂2 : 2 ≤ W₂ := Nat.le_floor (by exact_mod_cast (le_trans hw₁ hw₁₂))
  have hW₁₂ : W₁ ≤ W₂ := Nat.floor_le_floor hw₁₂
  -- the terms are nonnegative
  have hterm_nonneg : ∀ ℓ : ℕ, ℓ.Prime → 0 ≤ (rootCount ℓ : ℝ) * Real.log ℓ / (ℓ : ℝ) := by
    intro ℓ hℓ
    have h2 : (2 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ.two_le
    have : (0 : ℝ) ≤ Real.log ℓ := Real.log_natCast_nonneg ℓ
    positivity
  -- the filtered set sits inside `primesLE W₂ \ primesLE W₁`
  have hsub : (P.filter (fun ℓ => w₁ < ((ℓ : ℕ) : ℝ) ∧ ((ℓ : ℕ) : ℝ) ≤ w₂))
      ⊆ primesLE W₂ \ primesLE W₁ := by
    intro ℓ hl
    simp only [Finset.mem_filter] at hl
    obtain ⟨hlP, hl1, hl2⟩ := hl
    have hp : ℓ.Prime := hP ℓ hlP
    have hle : ℓ ≤ W₂ := Nat.le_floor hl2
    have hgt : W₁ < ℓ := by
      have hfl : (W₁ : ℝ) ≤ w₁ := Nat.floor_le hw₁0.le
      exact_mod_cast lt_of_le_of_lt hfl hl1
    refine Finset.mem_sdiff.mpr ⟨mem_primesLE.mpr ⟨hle, hp⟩, ?_⟩
    intro hcon
    exact absurd (mem_primesLE.mp hcon).1 (by omega)
  have hsubW : primesLE W₁ ⊆ primesLE W₂ := by
    intro p hp
    obtain ⟨h1, h2⟩ := mem_primesLE.mp hp
    exact mem_primesLE.mpr ⟨le_trans h1 hW₁₂, h2⟩
  have hsplit : ∑ p ∈ primesLE W₂ \ primesLE W₁, (rootCount p : ℝ) * Real.log p / (p : ℝ)
      = (∑ p ∈ primesLE W₂, (rootCount p : ℝ) * Real.log p / (p : ℝ))
        - ∑ p ∈ primesLE W₁, (rootCount p : ℝ) * Real.log p / (p : ℝ) := by
    rw [eq_sub_iff_add_eq, Finset.sum_sdiff hsubW]
  -- the two Mertens estimates
  have hupper := hCu W₂ hW₂2
  have hlower := hCl W₁ (by omega)
  have hlogW₂ : Real.log W₂ ≤ Real.log w₂ :=
    Real.log_le_log (by positivity) (Nat.floor_le hw₂0.le)
  have hlogW₁ : Real.log w₁ - Real.log 2 ≤ Real.log W₁ := by
    have hhalf : w₁ / 2 ≤ (W₁ : ℝ) := by
      have h1 : w₁ - 1 ≤ (W₁ : ℝ) := by
        have := Nat.sub_one_lt_floor w₁
        linarith
      linarith
    have h2 : Real.log (w₁ / 2) ≤ Real.log W₁ := Real.log_le_log (by positivity) hhalf
    rwa [Real.log_div hw₁0.ne' (by norm_num)] at h2
  have hlogdiv : Real.log (w₂ / w₁) = Real.log w₂ - Real.log w₁ :=
    Real.log_div hw₂0.ne' hw₁0.ne'
  calc ∑ ℓ ∈ P with (w₁ < ((ℓ : ℕ) : ℝ) ∧ ((ℓ : ℕ) : ℝ) ≤ w₂),
        (rootCount ℓ : ℝ) * Real.log ℓ / (ℓ : ℝ)
      ≤ ∑ p ∈ primesLE W₂ \ primesLE W₁, (rootCount p : ℝ) * Real.log p / (p : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun p hp _ => hterm_nonneg p (mem_primesLE.mp (Finset.mem_sdiff.mp hp).1).2)
    _ = (∑ p ∈ primesLE W₂, (rootCount p : ℝ) * Real.log p / (p : ℝ))
          - ∑ p ∈ primesLE W₁, (rootCount p : ℝ) * Real.log p / (p : ℝ) := hsplit
    _ ≤ Real.log (w₂ / w₁) + (Cu + Cl + Real.log 2) := by rw [hlogdiv]; linarith

/-! ## The sieve prime set and the sieve product -/

/-- `Q_{m,z} = {ℓ ≤ z : ℓ prime, ℓ ∤ 10 m}`, the primes sifted out. -/
noncomputable def sievePrimes (m : ℕ) (z : ℝ) : Finset ℕ :=
  (Finset.range (⌊z⌋₊ + 1)).filter (fun ℓ => Nat.Prime ℓ ∧ ¬ (ℓ ∣ 10 * m))

theorem mem_sievePrimes {m ℓ : ℕ} {z : ℝ} :
    ℓ ∈ sievePrimes m z ↔ ℓ ≤ ⌊z⌋₊ ∧ Nat.Prime ℓ ∧ ¬ (ℓ ∣ 10 * m) := by
  simp [sievePrimes, Finset.mem_filter, Finset.mem_range]

/-- A prime not dividing `10 m` is neither `2` nor `5`. -/
theorem ne_two_five_of_mem_sievePrimes {m ℓ : ℕ} {z : ℝ} (h : ℓ ∈ sievePrimes m z) :
    ℓ ≠ 2 ∧ ℓ ≠ 5 := by
  obtain ⟨-, -, h10⟩ := mem_sievePrimes.mp h
  constructor
  · rintro rfl; exact h10 (Dvd.dvd.mul_right (by norm_num) m)
  · rintro rfl; exact h10 (Dvd.dvd.mul_right (by norm_num) m)

/-- The root count of a prime in the sieve set is `2` when `χ₅ = 1` and `0` otherwise. -/
theorem rootCount_of_mem_sievePrimes {m ℓ : ℕ} {z : ℝ} (h : ℓ ∈ sievePrimes m z) :
    (if ℓ % 5 = 1 ∨ ℓ % 5 = 4 then rootCount ℓ = 2 else rootCount ℓ = 0) := by
  obtain ⟨-, hp, -⟩ := mem_sievePrimes.mp h
  obtain ⟨-, h5⟩ := ne_two_five_of_mem_sievePrimes h
  split_ifs with hchi
  · exact rootCount_prime_eq_two hp ((chi5_eq_one_iff ℓ).mpr hchi)
  · have := rootCount_prime_pow_eq_zero hp h5 (by simpa [chi5_eq_one_iff] using hchi) le_rfl
    simpa using this

/-- `V_m(z) = ∏_{ℓ ∈ Q_{m,z}} (1 - ρ(ℓ)/ℓ)`. -/
noncomputable def sieveProduct (m : ℕ) (z : ℝ) : ℝ :=
  ∏ ℓ ∈ sievePrimes m z, (1 - (rootCount ℓ : ℝ) / (ℓ : ℝ))

open scoped Classical in
/-- Only the primes with `χ₅ = 1` contribute to the sieve product. -/
theorem sieveProduct_eq_chi (m : ℕ) (z : ℝ) :
    sieveProduct m z = ∏ ℓ ∈ sievePrimes m z with (ℓ % 5 = 1 ∨ ℓ % 5 = 4),
      (1 - 2 / (ℓ : ℝ)) := by
  rw [sieveProduct, Finset.prod_filter]
  refine Finset.prod_congr rfl (fun ℓ hl => ?_)
  have h := rootCount_of_mem_sievePrimes hl
  split_ifs at h ⊢ with hchi
  · rw [h]; norm_num
  · rw [h]; norm_num

/-- Each factor of the sieve product lies in `(0, 1]`. -/
theorem sieveProduct_factor_mem {m ℓ : ℕ} {z : ℝ} (hℓ : ℓ ∈ sievePrimes m z) :
    0 < 1 - (rootCount ℓ : ℝ) / (ℓ : ℝ) ∧ 1 - (rootCount ℓ : ℝ) / (ℓ : ℝ) ≤ 1 := by
  obtain ⟨-, hp, -⟩ := mem_sievePrimes.mp hℓ
  have h := rootCount_of_mem_sievePrimes hℓ
  have hpos : (0 : ℝ) < (ℓ : ℝ) := by
    have : (2 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hp.two_le
    linarith
  split_ifs at h with hchi
  · have h11 : (11 : ℕ) ≤ ℓ := eleven_le_of_chi5_eq_one hp ((chi5_eq_one_iff ℓ).mpr hchi)
    have h11' : (11 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast h11
    rw [h]
    constructor
    · have : (2 : ℝ) / (ℓ : ℝ) ≤ 2 / 11 := by gcongr
      push_cast
      linarith
    · have : (0 : ℝ) ≤ (2 : ℕ) / (ℓ : ℝ) := by positivity
      linarith
  · rw [h]; norm_num

theorem sieveProduct_pos {m : ℕ} {z : ℝ} : 0 < sieveProduct m z :=
  Finset.prod_pos (fun _l hl => (sieveProduct_factor_mem hl).1)

theorem sieveProduct_le_one {m : ℕ} {z : ℝ} : sieveProduct m z ≤ 1 := by
  calc sieveProduct m z ≤ ∏ _ℓ ∈ sievePrimes m z, (1 : ℝ) :=
        Finset.prod_le_prod (fun ℓ hl => (sieveProduct_factor_mem hl).1.le)
          (fun ℓ hl => (sieveProduct_factor_mem hl).2)
    _ = 1 := Finset.prod_const_one

open scoped Classical in
/-- Deleting from the sieve product the primes dividing `m` costs at most a factor `h(m)`. -/
theorem sieveProduct_le_mul_hFactor (m : ℕ) (hm : 0 < m) (z : ℝ) :
    sieveProduct m z ≤ sieveProduct 1 z * hFactor m := by
  set Q1 := (sievePrimes 1 z).filter (fun ℓ => ℓ % 5 = 1 ∨ ℓ % 5 = 4) with hQ1
  set Qm := (sievePrimes m z).filter (fun ℓ => ℓ % 5 = 1 ∨ ℓ % 5 = 4) with hQm
  have hsub : Qm ⊆ Q1 := by
    intro ℓ hl
    simp only [hQm, hQ1, Finset.mem_filter] at hl ⊢
    obtain ⟨hlm, hchi⟩ := hl
    obtain ⟨hle, hp, h10m⟩ := mem_sievePrimes.mp hlm
    refine ⟨mem_sievePrimes.mpr ⟨hle, hp, ?_⟩, hchi⟩
    intro hdvd
    exact h10m (dvd_trans hdvd (by simp))
  have hfac : ∀ ℓ ∈ Q1, (0 : ℝ) < 1 - 2 / (ℓ : ℝ) := by
    intro ℓ hl
    simp only [hQ1, Finset.mem_filter] at hl
    obtain ⟨-, hp, -⟩ := mem_sievePrimes.mp hl.1
    have h11 : (11 : ℕ) ≤ ℓ := eleven_le_of_chi5_eq_one hp ((chi5_eq_one_iff ℓ).mpr hl.2)
    have h11' : (11 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast h11
    have : (2 : ℝ) / (ℓ : ℝ) ≤ 2 / 11 := by gcongr
    linarith
  -- split the product over `Q1`
  have hsplit : ∏ ℓ ∈ Q1, (1 - 2 / (ℓ : ℝ))
      = (∏ ℓ ∈ Qm, (1 - 2 / (ℓ : ℝ))) * ∏ ℓ ∈ Q1 \ Qm, (1 - 2 / (ℓ : ℝ)) := by
    rw [mul_comm]
    exact (Finset.prod_sdiff hsub).symm
  have hposQm : (0 : ℝ) < ∏ ℓ ∈ Qm, (1 - 2 / (ℓ : ℝ)) :=
    Finset.prod_pos (fun ℓ hl => hfac ℓ (hsub hl))
  have hposD : (0 : ℝ) < ∏ ℓ ∈ Q1 \ Qm, (1 - 2 / (ℓ : ℝ)) :=
    Finset.prod_pos (fun ℓ hl => hfac ℓ (Finset.mem_sdiff.mp hl).1)
  -- the deleted primes divide `m`
  have hdel : Q1 \ Qm ⊆ m.primeFactors.filter (fun p => p % 5 = 1 ∨ p % 5 = 4) := by
    intro ℓ hl
    rw [Finset.mem_sdiff] at hl
    obtain ⟨hl1, hl2⟩ := hl
    simp only [hQ1, Finset.mem_filter] at hl1
    obtain ⟨hle, hp, h10⟩ := mem_sievePrimes.mp hl1.1
    have hdvdm : ℓ ∣ m := by
      by_contra hcon
      exact hl2 (by
        simp only [hQm, Finset.mem_filter]
        refine ⟨mem_sievePrimes.mpr ⟨hle, hp, ?_⟩, hl1.2⟩
        intro hdvd
        rcases (Nat.Prime.dvd_mul hp).mp hdvd with h | h
        · exact h10 (by simpa using h)
        · exact hcon h)
    exact Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hp, hdvdm, hm.ne'⟩, hl1.2⟩
  have hone : ∀ p ∈ m.primeFactors.filter (fun p => p % 5 = 1 ∨ p % 5 = 4),
      (1 : ℝ) ≤ (1 - 2 / (p : ℝ))⁻¹ := by
    intro p hp
    simp only [Finset.mem_filter] at hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp.1
    have h11 : (11 : ℕ) ≤ p := eleven_le_of_chi5_eq_one hpp ((chi5_eq_one_iff p).mpr hp.2)
    have h11' : (11 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h11
    have hd : (2 : ℝ) / (p : ℝ) ≤ 2 / 11 := by gcongr
    have hpos : (0 : ℝ) < 1 - 2 / (p : ℝ) := by linarith
    have hle1 : 1 - 2 / (p : ℝ) ≤ 1 := by
      have : (0 : ℝ) ≤ 2 / (p : ℝ) := by positivity
      linarith
    exact (one_le_inv₀ hpos).mpr hle1
  have hinv : (∏ ℓ ∈ Q1 \ Qm, (1 - 2 / (ℓ : ℝ)))⁻¹ ≤ hFactor m := by
    rw [← Finset.prod_inv_distrib]
    have hsplit2 : hFactor m
        = (∏ ℓ ∈ Q1 \ Qm, (1 - 2 / (ℓ : ℝ))⁻¹)
          * ∏ p ∈ (m.primeFactors.filter (fun p => p % 5 = 1 ∨ p % 5 = 4)) \ (Q1 \ Qm),
              (1 - 2 / (p : ℝ))⁻¹ := by
      rw [hFactor, mul_comm]
      exact (Finset.prod_sdiff hdel).symm
    have hDpos : (0 : ℝ) < ∏ ℓ ∈ Q1 \ Qm, (1 - 2 / (ℓ : ℝ))⁻¹ :=
      Finset.prod_pos (fun ℓ hl => inv_pos.mpr (hfac ℓ (Finset.mem_sdiff.mp hl).1))
    have hrest : (1 : ℝ)
        ≤ ∏ p ∈ (m.primeFactors.filter (fun p => p % 5 = 1 ∨ p % 5 = 4)) \ (Q1 \ Qm),
            (1 - 2 / (p : ℝ))⁻¹ := by
      calc (1 : ℝ)
          = ∏ _p ∈ (m.primeFactors.filter (fun p => p % 5 = 1 ∨ p % 5 = 4)) \ (Q1 \ Qm),
              (1 : ℝ) := by simp
        _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one)
              (fun p hp => hone p (Finset.mem_sdiff.mp hp).1)
    rw [hsplit2]
    nlinarith
  rw [sieveProduct_eq_chi, sieveProduct_eq_chi, ← hQm, ← hQ1]
  have hkey : ∏ ℓ ∈ Qm, (1 - 2 / (ℓ : ℝ))
      = (∏ ℓ ∈ Q1, (1 - 2 / (ℓ : ℝ))) * (∏ ℓ ∈ Q1 \ Qm, (1 - 2 / (ℓ : ℝ)))⁻¹ := by
    rw [hsplit]
    field_simp
  rw [hkey]
  have hQ1pos : (0 : ℝ) ≤ ∏ ℓ ∈ Q1, (1 - 2 / (ℓ : ℝ)) :=
    Finset.prod_nonneg (fun ℓ hl => (hfac ℓ hl).le)
  exact mul_le_mul_of_nonneg_left hinv hQ1pos

open scoped Classical in
/-- **UNCONDITIONAL.**  (The Mertens/`χ₅` input it uses, `sum_inv_primes_chi5`, is proved
unconditionally in `FactorialHypergraph/MertensSecond.lean`; this docstring previously said
"CONDITIONAL", which was stale.)
`V_1(z) ≤ C / log z` for `z ≥ 16`. -/
theorem sieveProduct_one_le :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℝ, 16 ≤ z → sieveProduct 1 z ≤ C / Real.log z := by
  obtain ⟨C, hC0, hCN⟩ := sum_inv_primes_chi5
  refine ⟨2 * Real.exp (2 * C), by positivity, ?_⟩
  intro z hz
  set W := ⌊z⌋₊ with hW
  have hz0 : (0 : ℝ) < z := by linarith
  have hW16 : 16 ≤ W := Nat.le_floor (by exact_mod_cast hz)
  have hW3 : 3 ≤ W := by omega
  -- the sieve product is at most `exp (-2 ∑ 1/ℓ)`
  have hbound : sieveProduct 1 z
      ≤ Real.exp (-(2 * ∑ p ∈ Finset.Icc 1 W with (Nat.Prime p ∧ chi5 p = 1), (1 : ℝ) / p)) := by
    rw [sieveProduct_eq_chi]
    have hsubset : ((sievePrimes 1 z).filter (fun ℓ => ℓ % 5 = 1 ∨ ℓ % 5 = 4))
        = (Finset.Icc 1 W).filter (fun p => Nat.Prime p ∧ chi5 p = 1) := by
      ext ℓ
      simp only [Finset.mem_filter, Finset.mem_Icc, mem_sievePrimes]
      constructor
      · rintro ⟨⟨hle, hp, -⟩, hchi⟩
        exact ⟨⟨hp.one_lt.le, hle⟩, hp, (chi5_eq_one_iff ℓ).mpr hchi⟩
      · rintro ⟨⟨-, hle⟩, hp, hchi⟩
        have hchi' := (chi5_eq_one_iff ℓ).mp hchi
        refine ⟨⟨hle, hp, ?_⟩, hchi'⟩
        intro hdvd
        have h11 : (11 : ℕ) ≤ ℓ := eleven_le_of_chi5_eq_one hp hchi
        have hle10 : ℓ ≤ 10 := Nat.le_of_dvd (by norm_num) (by simpa using hdvd)
        omega
    rw [hsubset]
    have hstep : ∏ p ∈ Finset.Icc 1 W with (Nat.Prime p ∧ chi5 p = 1), (1 - 2 / (p : ℝ))
        ≤ ∏ p ∈ Finset.Icc 1 W with (Nat.Prime p ∧ chi5 p = 1),
            Real.exp (-(2 * ((1 : ℝ) / p))) := by
      refine Finset.prod_le_prod ?_ ?_
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_Icc] at hp
        have h11 : (11 : ℕ) ≤ p := eleven_le_of_chi5_eq_one hp.2.1 hp.2.2
        have h11' : (11 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h11
        have : (2 : ℝ) / (p : ℝ) ≤ 2 / 11 := by gcongr
        linarith
      · intro p _
        have hle := Real.add_one_le_exp (-(2 * ((1 : ℝ) / p)))
        have heq : -(2 * ((1 : ℝ) / p)) + 1 = 1 - 2 / (p : ℝ) := by ring
        rw [heq] at hle
        exact hle
    refine le_trans hstep (le_of_eq ?_)
    rw [← Real.exp_sum]
    congr 1
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  -- the Mertens lower bound
  have hCW := hCN W hW3
  have hlow : Real.log (Real.log W) / 2 - C
      ≤ ∑ p ∈ Finset.Icc 1 W with (Nat.Prime p ∧ chi5 p = 1), (1 : ℝ) / p := by
    have := (abs_le.mp hCW).1
    linarith
  have hWz : (Real.log z) / 2 ≤ Real.log W := by
    have hfl : (z : ℝ) - 1 ≤ (W : ℝ) := by
      have := Nat.sub_one_lt_floor z
      linarith
    have hWpos : (0 : ℝ) < (W : ℝ) := by
      have : (16 : ℝ) ≤ (W : ℝ) := by exact_mod_cast hW16
      linarith
    have hhalf : z / 2 ≤ (W : ℝ) := by linarith
    have h1 : Real.log (z / 2) ≤ Real.log W := Real.log_le_log (by linarith) hhalf
    have h2 : Real.log (z / 2) = Real.log z - Real.log 2 := by
      rw [Real.log_div (by linarith) (by norm_num)]
    have h3 : Real.log 2 ≤ Real.log z / 2 := by
      have hlz : Real.log 16 ≤ Real.log z := Real.log_le_log (by norm_num) hz
      have h16 : Real.log 16 = 4 * Real.log 2 := by
        rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]
        push_cast; ring
      rw [h16] at hlz
      have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
      linarith
    linarith
  have hlogz : (0 : ℝ) < Real.log z := by
    have : Real.log 16 ≤ Real.log z := Real.log_le_log (by norm_num) hz
    have : (0 : ℝ) < Real.log 16 := Real.log_pos (by norm_num)
    linarith
  have hlogW : (0 : ℝ) < Real.log W := by linarith
  -- combine
  calc sieveProduct 1 z
      ≤ Real.exp (-(2 * ∑ p ∈ Finset.Icc 1 W with (Nat.Prime p ∧ chi5 p = 1), (1 : ℝ) / p)) :=
        hbound
    _ ≤ Real.exp (-(2 * (Real.log (Real.log W) / 2 - C))) := by
        apply Real.exp_le_exp.mpr
        linarith
    _ = Real.exp (2 * C) / Real.log W := by
        rw [show -(2 * (Real.log (Real.log W) / 2 - C)) = 2 * C + (-Real.log (Real.log W)) by ring,
          Real.exp_add, Real.exp_neg, Real.exp_log hlogW]
        rw [div_eq_mul_inv]
    _ ≤ Real.exp (2 * C) / (Real.log z / 2) :=
        div_le_div_of_nonneg_left (by positivity) (by linarith) hWz
    _ = 2 * Real.exp (2 * C) / Real.log z := by
        rw [div_div_eq_mul_div]; ring
  
open scoped Classical in
/-- **UNCONDITIONAL.**  (The Mertens/`χ₅` input it uses, `sum_inv_primes_chi5`, is proved
unconditionally in `FactorialHypergraph/MertensSecond.lean`; this docstring previously said
"CONDITIONAL", which was stale.)
`V_m(z) ≤ C h(m)/log z`, uniformly in `m ≥ 1` and `z ≥ 16`. -/
theorem sieveProduct_le :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 0 < m → ∀ z : ℝ, 16 ≤ z →
      sieveProduct m z ≤ C * hFactor m / Real.log z := by
  obtain ⟨C, hC0, hC⟩ := sieveProduct_one_le
  refine ⟨C, hC0, ?_⟩
  intro m hm z hz
  have hlogz : (0 : ℝ) < Real.log z := by
    have h1 : Real.log 16 ≤ Real.log z := Real.log_le_log (by norm_num) hz
    have h2 : (0 : ℝ) < Real.log 16 := Real.log_pos (by norm_num)
    linarith
  calc sieveProduct m z ≤ sieveProduct 1 z * hFactor m := sieveProduct_le_mul_hFactor m hm z
    _ ≤ (C / Real.log z) * hFactor m :=
        mul_le_mul_of_nonneg_right (hC z hz) hFactor_nonneg
    _ = C * hFactor m / Real.log z := by ring

end FactorialHypergraph
