/-
# Roots of `f(t) = t² + 3t + 1` modulo an arbitrary integer

Layer 1 of the sieve estimate (A3).  Here we study

  `R(m) = #{a mod m : f(a) ≡ 0 (mod m)}`,

which is the function `rootCount` of `FactorialHypergraph/LargePrimeFactors.lean`, evaluated at an
arbitrary modulus (its definition `#{a < m : m ∣ f(a)}` makes sense for every `m`).

We prove:
* `rootCount_mul` — multiplicativity (Chinese remainder theorem);
* the prime-power classification of the manuscript, including the two exceptional primes
  `2` and `5`:  `R(2^e) = 0`, `R(5) = 1`, `R(5^e) = 0` for `e ≥ 2`, and
  `R(p^e) ≤ R(p) = 1 + χ₅(p) ∈ {0, 2}` for `p ≠ 2, 5` (only the upper bound is needed for the
  sieve estimate, and it is what the Hensel step of `QuadraticRoots.lean` gives);
* `rootCount_le_card_divisors` — `R(m) ≤ τ(m)`;
* the multiplicative majorant `gMaj` of `m ↦ R(m) h(m)`, where `h` is the correction factor
  `h(m) = ∏_{p ∣ m, χ₅(p) = 1} (1 - 2/p)⁻¹` of the manuscript.

Note that `R` is the *base* root-count function; it is **not** identified with the local
density used in the sieve after the primes dividing `m` have been deleted (that density is
`R` restricted to the primes of `P_m`; see `FactorialHypergraph/A3Local.lean`).
-/
import FactorialHypergraph.A3Mertens
import FactorialHypergraph.QuadraticRoots
import FactorialHypergraph.MertensRoots

namespace FactorialHypergraph

open Finset

/-! ## Basic values and multiplicativity of `R = rootCount` -/

theorem rootCount_one : rootCount 1 = 1 := by decide

theorem rootCount_zero : rootCount 0 = 0 := by decide

/-- Divisibility of `f` only depends on the residue class. -/
theorem dvd_fq_congr {d i j : ℕ} (h : i ≡ j [MOD d]) : d ∣ fq i ↔ d ∣ fq j := by
  constructor <;> intro hd
  · exact Nat.modEq_zero_iff_dvd.mp (((fq_modEq h).symm).trans (Nat.modEq_zero_iff_dvd.mpr hd))
  · exact Nat.modEq_zero_iff_dvd.mp ((fq_modEq h).trans (Nat.modEq_zero_iff_dvd.mpr hd))

/-- **Multiplicativity of the root count** (Chinese remainder theorem). -/
theorem rootCount_mul_of_coprime {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (h : Nat.Coprime m n) :
    rootCount (m * n) = rootCount m * rootCount n := by
  classical
  unfold rootCount
  rw [← Finset.card_product]
  refine Finset.card_bij (fun x _ => (x % m, x % n)) ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_range] at hx
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_range]
    refine ⟨⟨Nat.mod_lt _ (Nat.pos_of_ne_zero hm), ?_⟩, ⟨Nat.mod_lt _ (Nat.pos_of_ne_zero hn), ?_⟩⟩
    · exact (dvd_fq_congr (Nat.mod_modEq x m)).mpr (dvd_trans ⟨n, rfl⟩ hx.2)
    · exact (dvd_fq_congr (Nat.mod_modEq x n)).mpr (dvd_trans ⟨m, by ring⟩ hx.2)
  · intro x hx y hy hxy
    simp only [Finset.mem_filter, Finset.mem_range] at hx hy
    simp only [Prod.mk.injEq] at hxy
    exact Nat.ModEq.eq_of_lt_of_lt
      ((Nat.modEq_and_modEq_iff_modEq_mul h).mp ⟨hxy.1, hxy.2⟩) hx.1 hy.1
  · intro b hb
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_range] at hb
    obtain ⟨⟨hb1, hb2⟩, ⟨hb3, hb4⟩⟩ := hb
    obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder h b.1 b.2
    have hkm : k % (m * n) ≡ k [MOD m] := (Nat.mod_modEq k (m * n)).of_dvd ⟨n, rfl⟩
    have hkn : k % (m * n) ≡ k [MOD n] := (Nat.mod_modEq k (m * n)).of_dvd ⟨m, by ring⟩
    have e1 : k % (m * n) % m = b.1 := by
      have h' : k % (m * n) ≡ b.1 [MOD m] := hkm.trans hk1
      unfold Nat.ModEq at h'
      rwa [Nat.mod_eq_of_lt hb1] at h'
    have e2 : k % (m * n) % n = b.2 := by
      have h' : k % (m * n) ≡ b.2 [MOD n] := hkn.trans hk2
      unfold Nat.ModEq at h'
      rwa [Nat.mod_eq_of_lt hb3] at h'
    refine ⟨k % (m * n), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_range]
      refine ⟨Nat.mod_lt _ (by positivity), h.mul_dvd_of_dvd_of_dvd ?_ ?_⟩
      · exact (dvd_fq_congr (hkm.trans hk1)).mpr hb2
      · exact (dvd_fq_congr (hkn.trans hk2)).mpr hb4
    · simp [e1, e2]

/-- Multiplicativity of `R`, in the form required by `Nat.multiplicative_factorization`
(the degenerate cases involving `0` are covered as well). -/
theorem rootCount_mul (x y : ℕ) (h : Nat.Coprime x y) :
    rootCount (x * y) = rootCount x * rootCount y := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · have : y = 1 := by simpa [Nat.Coprime] using h
    subst this; simp [rootCount_zero, rootCount_one]
  rcases Nat.eq_zero_or_pos y with rfl | hy
  · have : x = 1 := by simpa [Nat.Coprime] using h
    subst this; simp [rootCount_zero, rootCount_one]
  exact rootCount_mul_of_coprime hx.ne' hy.ne' h

/-! ## Prime powers -/

/-- `R(2^e) = 0` for `e ≥ 1`: `f` has no root modulo `2`. -/
theorem rootCount_two_pow {e : ℕ} (he : 1 ≤ e) : rootCount (2 ^ e) = 0 := by
  classical
  unfold rootCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro a _ hcon
  exact two_not_dvd_fq a (dvd_trans (dvd_pow_self 2 (by omega)) hcon)

/-- `R(5) = 1`. -/
theorem rootCount_five : rootCount 5 = 1 := by decide

/-- `R(5^e) = 0` for `e ≥ 2`: the root modulo `5` does not lift to `25`. -/
theorem rootCount_five_pow {e : ℕ} (he : 2 ≤ e) : rootCount (5 ^ e) = 0 := by
  classical
  unfold rootCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro a _ hcon
  refine not_twentyfive_dvd_fq a (dvd_trans ?_ hcon)
  have : (25 : ℕ) = 5 ^ 2 := by norm_num
  rw [this]
  exact pow_dvd_pow 5 he

/-- **Hensel's step.**  For `p ≠ 5` the number of roots modulo `p^e` is at most the number of
roots modulo `p`. -/
theorem rootCount_prime_pow_le {p e : ℕ} (hp : p.Prime) (hp5 : p ≠ 5) (he : 1 ≤ e) :
    rootCount (p ^ e) ≤ rootCount p := by
  classical
  refine card_le_rootCount hp hp5 he _ ?_ ?_
  · intro i hi j hj hij
    simp only [Finset.mem_filter, Finset.mem_range] at hi hj
    exact Nat.ModEq.eq_of_lt_of_lt hij hi.1 hj.1
  · intro i hi
    exact (Finset.mem_filter.mp hi).2

/-- `R(p^e) ≤ 2` for every prime `p` and every `e ≥ 1`. -/
theorem rootCount_prime_pow_le_two {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) :
    rootCount (p ^ e) ≤ 2 := by
  by_cases hp5 : p = 5
  · subst hp5
    rcases Nat.lt_or_ge e 2 with h | h
    · have : e = 1 := by omega
      subst this; simp [rootCount_five]
    · simp [rootCount_five_pow h]
  · exact le_trans (rootCount_prime_pow_le hp hp5 he) (rootCount_le_two hp)

/-- For a prime `p ≠ 5` with `χ₅(p) ≠ 1` there is no root modulo `p^e`. -/
theorem rootCount_prime_pow_eq_zero {p e : ℕ} (hp : p.Prime) (hp5 : p ≠ 5)
    (hchi : chi5 p ≠ 1) (he : 1 ≤ e) : rootCount (p ^ e) = 0 := by
  have hzero : rootCount p = 0 := by
    have h := rootCount_eq_one_add_chi5 hp
    have h5 : p % 5 ≠ 0 := by
      intro hcon
      exact hp5 ((Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp (Nat.dvd_of_mod_eq_zero hcon)).symm
    have : chi5 p = -1 := by
      unfold chi5 at hchi ⊢
      have : p % 5 < 5 := Nat.mod_lt _ (by norm_num)
      interval_cases h : (p % 5) <;> simp_all
    rw [this] at h
    have : (rootCount p : ℝ) = 0 := by linarith
    exact_mod_cast this
  have := rootCount_prime_pow_le hp hp5 he
  omega

/-- For a prime `p` with `χ₅(p) = 1` we have `R(p) = 2`. -/
theorem rootCount_prime_eq_two {p : ℕ} (hp : p.Prime) (hchi : chi5 p = 1) :
    rootCount p = 2 := by
  have h := rootCount_eq_one_add_chi5 hp
  rw [hchi] at h
  have : (rootCount p : ℝ) = 2 := by linarith
  exact_mod_cast this

/-- The factorisation of the root count into prime-power contributions. -/
theorem rootCount_eq_factorization_prod {m : ℕ} (hm : m ≠ 0) :
    rootCount m = m.factorization.prod (fun p k => rootCount (p ^ k)) :=
  Nat.multiplicative_factorization rootCount rootCount_mul rootCount_one hm

/-- **`R(m) ≤ τ(m)`.** -/
theorem rootCount_le_card_divisors {m : ℕ} (hm : m ≠ 0) :
    rootCount m ≤ m.divisors.card := by
  classical
  rw [rootCount_eq_factorization_prod hm, Nat.card_divisors hm, Finsupp.prod,
    Nat.support_factorization]
  refine Finset.prod_le_prod' ?_
  intro p hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hk : 1 ≤ m.factorization p := (Nat.Prime.factorization_pos_of_dvd hpp hm
    (Nat.dvd_of_mem_primeFactors hp))
  exact le_trans (rootCount_prime_pow_le_two hpp hk) (by omega)

/-! ## The correction factor `h` and its multiplicative majorant -/

/-- `h(m) = ∏_{p ∣ m, χ₅(p) = 1} (1 - 2/p)⁻¹`, the cost of deleting from the sieve product the
primes dividing `m`.  (The condition `χ₅(p) = 1` is spelled out as `p % 5 ∈ {1, 4}`, which is
decidable and equivalent by `chi5_eq_one_iff`.) -/
noncomputable def hFactor (m : ℕ) : ℝ :=
  ∏ p ∈ m.primeFactors with (p % 5 = 1 ∨ p % 5 = 4), (1 - 2 / (p : ℝ))⁻¹

/-- The local factor of the multiplicative majorant of `m ↦ R(m) h(m)`. -/
noncomputable def gLoc (p : ℕ) : ℝ :=
  if p % 5 = 1 ∨ p % 5 = 4 then 2 * (p : ℝ) / ((p : ℝ) - 2) else if p = 5 then 1 else 0

/-- The multiplicative majorant `gMaj(m) = ∏_{p ∣ m} gLoc p ≥ R(m) h(m)`. -/
noncomputable def gMaj (m : ℕ) : ℝ := ∏ p ∈ m.primeFactors, gLoc p

theorem gLoc_nonneg {p : ℕ} (hp : p.Prime) : 0 ≤ gLoc p := by
  unfold gLoc
  split_ifs with h1 h2
  · have : (11 : ℕ) ≤ p := eleven_le_of_chi5_eq_one hp ((chi5_eq_one_iff p).mpr h1)
    have : (11 : ℝ) ≤ (p : ℝ) := by exact_mod_cast this
    have h2 : (0 : ℝ) < (p : ℝ) - 2 := by linarith
    positivity
  · norm_num
  · norm_num

theorem gMaj_nonneg (m : ℕ) : 0 ≤ gMaj m :=
  Finset.prod_nonneg (fun _p hp => gLoc_nonneg (Nat.prime_of_mem_primeFactors hp))

theorem gMaj_one : gMaj 1 = 1 := by simp [gMaj]

theorem gMaj_mul_of_coprime {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (h : Nat.Coprime m n) :
    gMaj (m * n) = gMaj m * gMaj n := by
  unfold gMaj
  rw [Nat.primeFactors_mul hm hn, Finset.prod_union (Nat.Coprime.disjoint_primeFactors h)]

theorem gMaj_prime_pow {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) : gMaj (p ^ e) = gLoc p := by
  unfold gMaj
  rw [Nat.primeFactors_pow p (by omega), hp.primeFactors, Finset.prod_singleton]

/-- Each factor of `h` is at least `1`. -/
theorem one_le_hFactor {m : ℕ} : 1 ≤ hFactor m := by
  classical
  have key : ∀ p ∈ m.primeFactors.filter (fun p => p % 5 = 1 ∨ p % 5 = 4),
      (1 : ℝ) ≤ (1 - 2 / (p : ℝ))⁻¹ := by
    intro p hp
    simp only [Finset.mem_filter] at hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp.1
    have h11 : (11 : ℕ) ≤ p := eleven_le_of_chi5_eq_one hpp ((chi5_eq_one_iff p).mpr hp.2)
    have h11' : (11 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h11
    have hd : 2 / (p : ℝ) ≤ 2 / 11 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) h11'
    have hpos : (0 : ℝ) < 1 - 2 / (p : ℝ) := by linarith
    have hle : 1 - 2 / (p : ℝ) ≤ 1 := by
      have : 0 ≤ 2 / (p : ℝ) := by positivity
      linarith
    exact (one_le_inv₀ hpos).mpr hle
  calc (1 : ℝ) = ∏ _p ∈ m.primeFactors with (_p % 5 = 1 ∨ _p % 5 = 4), (1 : ℝ) := by simp
    _ ≤ hFactor m := Finset.prod_le_prod (fun _ _ => zero_le_one) key

theorem hFactor_nonneg {m : ℕ} : 0 ≤ hFactor m := le_trans zero_le_one one_le_hFactor

/-- **The majorant property.**  `R(m) · h(m) ≤ gMaj(m)` for every `m ≥ 1`. -/
theorem rootCount_mul_hFactor_le {m : ℕ} (hm : m ≠ 0) :
    (rootCount m : ℝ) * hFactor m ≤ gMaj m := by
  classical
  have hR : (rootCount m : ℝ)
      = ∏ p ∈ m.primeFactors, (rootCount (p ^ m.factorization p) : ℝ) := by
    rw [rootCount_eq_factorization_prod hm, Finsupp.prod, Nat.support_factorization]
    push_cast
    rfl
  have hH : hFactor m
      = ∏ p ∈ m.primeFactors, (if p % 5 = 1 ∨ p % 5 = 4 then (1 - 2 / (p : ℝ))⁻¹ else 1) := by
    rw [hFactor, Finset.prod_filter]
  rw [hR, hH, ← Finset.prod_mul_distrib, gMaj]
  refine Finset.prod_le_prod ?_ ?_
  · intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have : (0 : ℝ) ≤ (if p % 5 = 1 ∨ p % 5 = 4 then (1 - 2 / (p : ℝ))⁻¹ else 1) := by
      split_ifs with h1
      · have h11 : (11 : ℕ) ≤ p := eleven_le_of_chi5_eq_one hpp ((chi5_eq_one_iff p).mpr h1)
        have h11' : (11 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h11
        have hd : 2 / (p : ℝ) ≤ 2 / 11 :=
          div_le_div_of_nonneg_left (by norm_num) (by norm_num) h11'
        have hpos : (0 : ℝ) < 1 - 2 / (p : ℝ) := by linarith
        exact le_of_lt (inv_pos.mpr hpos)
      · norm_num
    exact mul_nonneg (by positivity) this
  · intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hk : 1 ≤ m.factorization p :=
      Nat.Prime.factorization_pos_of_dvd hpp hm (Nat.dvd_of_mem_primeFactors hp)
    by_cases h1 : p % 5 = 1 ∨ p % 5 = 4
    · have h11 : (11 : ℕ) ≤ p := eleven_le_of_chi5_eq_one hpp ((chi5_eq_one_iff p).mpr h1)
      have h11' : (11 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h11
      have hp2 : (0 : ℝ) < (p : ℝ) - 2 := by linarith
      have hfac : (1 - 2 / (p : ℝ))⁻¹ = (p : ℝ) / ((p : ℝ) - 2) := by
        rw [show (1 : ℝ) - 2 / (p : ℝ) = ((p : ℝ) - 2) / (p : ℝ) by field_simp]
        rw [inv_div]
      have hRle : (rootCount (p ^ m.factorization p) : ℝ) ≤ 2 := by
        exact_mod_cast rootCount_prime_pow_le_two hpp hk
      have hpos : (0 : ℝ) < (p : ℝ) / ((p : ℝ) - 2) := by positivity
      simp only [gLoc, if_pos h1, hfac]
      calc (rootCount (p ^ m.factorization p) : ℝ) * ((p : ℝ) / ((p : ℝ) - 2))
          ≤ 2 * ((p : ℝ) / ((p : ℝ) - 2)) := by
            exact mul_le_mul_of_nonneg_right hRle (le_of_lt hpos)
        _ = 2 * (p : ℝ) / ((p : ℝ) - 2) := by ring
    · simp only [gLoc, if_neg h1, mul_one]
      by_cases h5 : p = 5
      · subst h5
        rw [if_pos rfl]
        rcases Nat.lt_or_ge (m.factorization 5) 2 with hlt | hge
        · have : m.factorization 5 = 1 := by omega
          rw [this]
          simp [rootCount_five]
        · rw [rootCount_five_pow hge]
          norm_num
      · rw [if_neg h5]
        have hchi : chi5 p ≠ 1 := by
          simp only [ne_eq, chi5_eq_one_iff]
          exact h1
        rw [rootCount_prime_pow_eq_zero hpp h5 hchi hk]
        norm_num

end FactorialHypergraph
