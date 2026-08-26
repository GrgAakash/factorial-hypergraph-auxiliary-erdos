/-
# Mertens' second theorem, and the reciprocal sum over the primes with `χ₅(p) = 1`

This file removes the last classical hypothesis of the sieve estimate (A3) other than the
sieve theorem itself.  It proves **unconditionally**

* `abs_sum_inv_primes_sub_loglog_le` — Mertens' second theorem
  `∑_{p ≤ N} 1/p = log log N + O(1)`;
* `abs_sum_chi5_div_primes_le` — the twisted analogue `∑_{p ≤ N} χ₅(p)/p = O(1)`;
* `sum_inv_primes_chi5_unconditional` — the statement previously carried as the hypothesis
  `MertensProgressions` of `FactorialHypergraph/A3Mertens.lean`, in the only form used by the
  sieve estimate:  `∑_{p ≤ N, χ₅(p) = 1} 1/p = (log log N)/2 + O(1)`.

Everything is elementary.  The ingredients are:

* Mertens' first theorem, two-sided, in von Mangoldt form: the upper bound
  `sum_vonMangoldt_div_le` of `MertensAux.lean` (from Chebyshev's `ψ(x) ≤ (log 4 + 4) x`) and
  the lower bound `sum_vonMangoldt_div_ge` proved here from `log N! ≥ N log N - N`
  (`log_factorial_ge` of `Estimates.lean`) and the identity
  `∑_{n ≤ N} log n = ∑_{d ≤ N} Λ(d) ⌊N/d⌋`;
* the passage from von Mangoldt sums to sums over primes, whose error is the convergent
  series `∑_p log p/(p(p-1))` (`sum_log_div_mul_pred_bounded`);
* the character-twisted Mertens estimate `|∑_{n ≤ N} χ₅(n) Λ(n)/n| ≤ C` (`abs_U_le` of
  `MertensCharacter.lean`, an elementary Shapiro argument);
* summation by parts (`sum_Ioc_by_parts`, `abs_sum_mul_le_of_antitone`) against the weight
  `1/log n`, together with the elementary comparison
  `(log(n+1) - log n)/log(n+1) ≤ log log (n+1) - log log n
      ≤ (log(n+1) - log n)/log(n+1) + (log(n+1) - log n)²/(log n log (n+1))`,
  which replaces the usual integral comparison.

No prime number theorem, no Dirichlet L-function and no Tauberian theorem is used.
-/
import FactorialHypergraph.MertensCharacter

namespace FactorialHypergraph

open Finset ArithmeticFunction

/-! ## Mertens' first theorem, two-sided -/

/-- `∑_{n ≤ N} log n = log N!`. -/
theorem sum_log_eq_log_factorial (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, Real.log n = Real.log (N.factorial : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Nat.factorial_succ]
    have h1 : (0 : ℝ) < (N.factorial : ℝ) := by exact_mod_cast N.factorial_pos
    push_cast
    rw [Real.log_mul (by positivity) (by positivity)]
    ring

/-- **Mertens' first theorem, lower bound.**  `∑_{n ≤ N} Λ(n)/n ≥ log N - 1`. -/
theorem sum_vonMangoldt_div_ge {N : ℕ} (hN : 1 ≤ N) :
    Real.log N - 1 ≤ ∑ n ∈ Finset.Icc 1 N, vonMangoldt n / n := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hlow : (N : ℝ) * Real.log N - N ≤ ∑ n ∈ Finset.Icc 1 N, Real.log n := by
    rw [sum_log_eq_log_factorial N]
    exact log_factorial_ge N
  have hup : ∑ n ∈ Finset.Icc 1 N, Real.log n
      ≤ (N : ℝ) * ∑ n ∈ Finset.Icc 1 N, vonMangoldt n / n := by
    rw [sum_log_eq_sum_vonMangoldt_mul_floor N, Finset.mul_sum]
    refine Finset.sum_le_sum fun d hd => ?_
    simp only [Finset.mem_Icc] at hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd.1
    have hΛ : 0 ≤ vonMangoldt d := vonMangoldt_nonneg
    have hfloor : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / d := by
      rw [le_div_iff₀ hd0]
      have h : (N / d : ℕ) * d ≤ N := by
        simpa [Nat.mul_comm] using Nat.div_mul_le_self N d
      exact_mod_cast h
    calc vonMangoldt d * ((N / d : ℕ) : ℝ)
        ≤ vonMangoldt d * ((N : ℝ) / d) := mul_le_mul_of_nonneg_left hfloor hΛ
      _ = (N : ℝ) * (vonMangoldt d / d) := by ring
  have key : (N : ℝ) * (Real.log N - 1)
      ≤ (N : ℝ) * ∑ n ∈ Finset.Icc 1 N, vonMangoldt n / n := by nlinarith
  exact le_of_mul_le_mul_left key hN0

/-! ## From von Mangoldt sums to sums over the primes -/

/-- Geometric series bound: `∑_{i < n} r^i ≤ 1/(1-r)` for `0 ≤ r < 1`. -/
theorem geom_range_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    ∑ i ∈ Finset.range n, r ^ i ≤ 1 / (1 - r) := by
  have hpos : 0 < 1 - r := by linarith
  rw [geom_sum_eq (by linarith : r ≠ 1)]
  have heq : (r ^ n - 1) / (r - 1) = (1 - r ^ n) / (1 - r) := by
    rw [div_eq_div_iff (by linarith) (by linarith)]; ring
  rw [heq, div_le_div_iff_of_pos_right hpos]
  nlinarith [pow_nonneg hr0 n]

theorem one_add_le_one_div {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) : 1 + r ≤ 1 / (1 - r) := by
  rw [le_div_iff₀ (by linarith)]
  nlinarith

/-- Geometric tail bound: `∑_{k = 2}^{M} r^k ≤ r²/(1-r)` for `0 ≤ r < 1`. -/
theorem geom_tail_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (M : ℕ) :
    ∑ k ∈ Finset.Icc 2 M, r ^ k ≤ r ^ 2 / (1 - r) := by
  have hpos : 0 < 1 - r := by linarith
  have key : ∑ k ∈ Finset.Icc 2 M, r ^ k + 1 + r ≤ 1 / (1 - r) := by
    rcases le_or_gt 2 M with h | h
    · have hrange : Finset.range (M + 1) = Finset.Icc 0 M := by
        ext x; simp [Finset.mem_Icc, Finset.mem_range]
      have hsplit : ∑ k ∈ Finset.range (M + 1), r ^ k
          = 1 + r + ∑ k ∈ Finset.Icc 2 M, r ^ k := by
        rw [hrange, show Finset.Icc 0 M = insert 0 (insert 1 (Finset.Icc 2 M)) by
          ext x; simp [Finset.mem_Icc, Finset.mem_insert]; omega]
        rw [Finset.sum_insert (by simp), Finset.sum_insert (by simp)]
        simp
        ring
      have h1 := geom_range_le hr0 hr1 (M + 1)
      rw [hsplit] at h1
      linarith
    · have hempty : Finset.Icc 2 M = ∅ := Finset.Icc_eq_empty (by omega)
      rw [hempty]
      simpa using one_add_le_one_div hr0 hr1
  have heq : (1 : ℝ) / (1 - r) - 1 - r = r ^ 2 / (1 - r) := by
    field_simp; ring
  linarith

/-- `∑_{p ≤ N} log p / p`, the logarithmically weighted prime sum of Mertens' theorems. -/
noncomputable def primeLogSum (N : ℕ) : ℝ := ∑ p ∈ primesLE N, Real.log p / p

/-- The `χ₅`-twisted prime sum `∑_{p ≤ N} χ₅(p) log p / p`. -/
noncomputable def primeChiLogSum (N : ℕ) : ℝ := ∑ p ∈ primesLE N, chi5 p * Real.log p / p

lemma primesLE_subset_Icc (N : ℕ) : primesLE N ⊆ Finset.Icc 1 N := by
  intro p hp
  obtain ⟨hpN, hpp⟩ := mem_primesLE.mp hp
  exact Finset.mem_Icc.mpr ⟨hpp.one_lt.le.trans' (by norm_num), hpN⟩

/-- The contribution of the proper prime powers `p^k`, `k ≥ 2`, to `∑_{n ≤ N} Λ(n)/n`. -/
theorem sum_sdiff_vonMangoldt_div_le (N : ℕ) :
    ∑ n ∈ (Finset.Icc 1 N) \ primesLE N, vonMangoldt n / n
      ≤ ∑ p ∈ primesLE N, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) := by
  classical
  set s : Finset ℕ := (Finset.Icc 1 N) \ primesLE N with hs
  set s' : Finset ℕ := s.filter (fun n => vonMangoldt n ≠ 0) with hs'
  have hrestrict : ∑ n ∈ s, vonMangoldt n / n = ∑ n ∈ s', vonMangoldt n / n := by
    rw [hs']
    refine (Finset.sum_filter_of_ne ?_).symm
    intro n _ hne h0
    exact hne (by rw [h0]; simp)
  rw [hrestrict]
  have hmaps : ∀ n ∈ s', n.minFac ∈ primesLE N := by
    intro n hn
    simp only [hs', hs, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_Icc] at hn
    obtain ⟨⟨⟨_, hN⟩, _⟩, hΛ⟩ := hn
    obtain ⟨p, k, hp, hk, hpk⟩ := (isPrimePow_nat_iff n).mp (vonMangoldt_ne_zero_iff.mp hΛ)
    have hn2 : 2 ≤ n := by
      subst hpk
      calc 2 ≤ p := hp.two_le
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk
    exact mem_primesLE.mpr
      ⟨le_trans (Nat.minFac_le (by omega)) hN, Nat.minFac_prime (by omega : n ≠ 1)⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_le_sum fun p hp => ?_
  obtain ⟨hpN, hpp⟩ := mem_primesLE.mp hp
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hfib : (s'.filter (fun n => n.minFac = p)) ⊆ (Finset.Icc 2 N).image (fun k => p ^ k) := by
    intro n hn
    simp only [hs', hs, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_Icc] at hn
    obtain ⟨⟨⟨⟨_, hN⟩, hnp⟩, hΛ⟩, hmin⟩ := hn
    obtain ⟨q, k, hq, hk, hqk⟩ := (isPrimePow_nat_iff n).mp (vonMangoldt_ne_zero_iff.mp hΛ)
    have hqp : q = p := by rw [← hmin, ← hqk, hq.pow_minFac (by omega)]
    subst hqp
    have hk2 : 2 ≤ k := by
      rcases Nat.lt_or_ge k 2 with h | h
      · exfalso
        have hk1 : k = 1 := by omega
        subst hk1
        rw [pow_one] at hqk
        exact hnp (mem_primesLE.mpr ⟨by omega, hqk ▸ hq⟩)
      · exact h
    have hkN : k ≤ N := by
      have h1 : k < 2 ^ k := Nat.lt_two_pow_self
      have h2 : (2 : ℕ) ^ k ≤ q ^ k := Nat.pow_le_pow_left hq.two_le k
      omega
    exact Finset.mem_image.mpr ⟨k, Finset.mem_Icc.mpr ⟨hk2, hkN⟩, hqk⟩
  have hnonneg : ∀ n : ℕ, 0 ≤ vonMangoldt n / (n : ℝ) := by
    intro n
    have := vonMangoldt_nonneg (n := n)
    positivity
  have hstep : ∑ n ∈ s'.filter (fun n => n.minFac = p), vonMangoldt n / n
      ≤ ∑ n ∈ (Finset.Icc 2 N).image (fun k => p ^ k), vonMangoldt n / n :=
    Finset.sum_le_sum_of_subset_of_nonneg hfib fun n _ _ => hnonneg n
  have himg : ∑ n ∈ (Finset.Icc 2 N).image (fun k => p ^ k), vonMangoldt n / (n : ℝ)
      = ∑ k ∈ Finset.Icc 2 N, Real.log p * (1 / (p : ℝ)) ^ k := by
    rw [Finset.sum_image (by
      intro a _ b _ hab
      exact Nat.pow_right_injective hpp.two_le hab)]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk0 : k ≠ 0 := by simp only [Finset.mem_Icc] at hk; omega
    rw [vonMangoldt_apply_pow hk0, vonMangoldt_apply_prime hpp, div_pow, one_pow]
    push_cast
    field_simp
  refine le_trans (hstep.trans_eq himg) ?_
  rw [← Finset.mul_sum]
  have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  have hgeom := geom_tail_le (r := 1 / (p : ℝ)) (by positivity) (by rw [div_lt_one hp0]; linarith) N
  calc Real.log p * ∑ k ∈ Finset.Icc 2 N, (1 / (p : ℝ)) ^ k
      ≤ Real.log p * ((1 / (p : ℝ)) ^ 2 / (1 - 1 / (p : ℝ))) :=
        mul_le_mul_of_nonneg_left hgeom hlogp
    _ = Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) := by field_simp

/-- Splitting the von Mangoldt sum into its prime part and its prime-power part. -/
theorem vonMangoldt_sum_split (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, vonMangoldt n / n
      = primeLogSum N + ∑ n ∈ (Finset.Icc 1 N) \ primesLE N, vonMangoldt n / n := by
  classical
  have heq : primeLogSum N = ∑ p ∈ primesLE N, vonMangoldt p / p :=
    Finset.sum_congr rfl fun p hp => by rw [vonMangoldt_apply_prime (mem_primesLE.mp hp).2]
  rw [heq, Finset.sum_sdiff_eq_sub (primesLE_subset_Icc N)]
  ring

/-- Splitting the twisted von Mangoldt sum into its prime part and its prime-power part. -/
theorem chi5_vonMangoldt_sum_split (N : ℕ) :
    U N = primeChiLogSum N + ∑ n ∈ (Finset.Icc 1 N) \ primesLE N, chi5 n * vonMangoldt n / n := by
  classical
  have heq : primeChiLogSum N = ∑ p ∈ primesLE N, chi5 p * vonMangoldt p / p :=
    Finset.sum_congr rfl fun p hp => by rw [vonMangoldt_apply_prime (mem_primesLE.mp hp).2]
  rw [U, heq, Finset.sum_sdiff_eq_sub (primesLE_subset_Icc N)]
  ring

/-- **Mertens' first theorem for primes, two-sided.**  `∑_{p ≤ N} log p/p = log N + O(1)`. -/
theorem abs_primeLogSum_sub_log_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N → |primeLogSum N - Real.log N| ≤ C := by
  obtain ⟨C₂, hC₂0, hC₂⟩ := sum_log_div_mul_pred_bounded
  have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  refine ⟨1 + C₂ + Real.log 4 + 4, by linarith, ?_⟩
  intro N hN
  have hsplit := vonMangoldt_sum_split N
  have hlow := sum_vonMangoldt_div_ge hN
  have hup := sum_vonMangoldt_div_le hN
  have htail := sum_sdiff_vonMangoldt_div_le N
  have hC := hC₂ N
  have htail0 : 0 ≤ ∑ n ∈ (Finset.Icc 1 N) \ primesLE N, vonMangoldt n / n := by
    refine Finset.sum_nonneg fun n _ => ?_
    have := vonMangoldt_nonneg (n := n)
    positivity
  rw [abs_le]
  constructor <;> linarith

/-- **Mertens' theorem for `χ₅`, prime form.**  `∑_{p ≤ N} χ₅(p) log p/p = O(1)`. -/
theorem abs_primeChiLogSum_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, |primeChiLogSum N| ≤ C := by
  obtain ⟨C₂, hC₂0, hC₂⟩ := sum_log_div_mul_pred_bounded
  refine ⟨12 * (2 + 2 * (Real.log 4 + 4)) + C₂, by
    have : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    nlinarith, ?_⟩
  intro N
  have hsplit := chi5_vonMangoldt_sum_split N
  have hU := abs_U_le N
  have htail : |∑ n ∈ (Finset.Icc 1 N) \ primesLE N, chi5 n * vonMangoldt n / n| ≤ C₂ := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hb : ∀ n ∈ (Finset.Icc 1 N) \ primesLE N,
        |chi5 n * vonMangoldt n / n| ≤ vonMangoldt n / n := by
      intro n _
      have h0 : (0 : ℝ) ≤ vonMangoldt n / n := by
        have := vonMangoldt_nonneg (n := n)
        positivity
      have hrw : |chi5 n * vonMangoldt n / n| = |chi5 n| * (vonMangoldt n / n) := by
        rw [show chi5 n * vonMangoldt n / n = chi5 n * (vonMangoldt n / n) by ring, abs_mul,
          abs_of_nonneg h0]
      rw [hrw]
      nlinarith [abs_chi5_le_one n, abs_nonneg (chi5 n)]
    exact le_trans (Finset.sum_le_sum hb) (le_trans (sum_sdiff_vonMangoldt_div_le N) (hC₂ N))
  have : primeChiLogSum N
      = U N - ∑ n ∈ (Finset.Icc 1 N) \ primesLE N, chi5 n * vonMangoldt n / n := by
    rw [hsplit]; ring
  rw [this]
  exact le_trans (abs_sub _ _) (add_le_add hU htail)

/-! ## Summation by parts against the weight `1/log n` -/

/-- The weight `n ↦ 1/log n` of the partial summation. -/
noncomputable def invLog (n : ℕ) : ℝ := 1 / Real.log n

/-- The coefficient sequence `log p / p` supported on the primes. -/
noncomputable def cPrime (n : ℕ) : ℝ := if n.Prime then Real.log n / n else 0

/-- The twisted coefficient sequence `χ₅(p) log p / p` supported on the primes. -/
noncomputable def cChi (n : ℕ) : ℝ := if n.Prime then chi5 n * Real.log n / n else 0

lemma filter_prime_Ioc (n : ℕ) : (Finset.Ioc 1 n).filter Nat.Prime = primesLE n := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_Ioc, mem_primesLE]
  constructor
  · rintro ⟨⟨_, h2⟩, hp⟩; exact ⟨h2, hp⟩
  · rintro ⟨h1, hp⟩; exact ⟨⟨hp.one_lt, h1⟩, hp⟩

lemma sum_cPrime (n : ℕ) : ∑ k ∈ Finset.Ioc 1 n, cPrime k = primeLogSum n := by
  classical
  rw [primeLogSum, ← filter_prime_Ioc n, Finset.sum_filter]
  rfl

lemma sum_cChi (n : ℕ) : ∑ k ∈ Finset.Ioc 1 n, cChi k = primeChiLogSum n := by
  classical
  rw [primeChiLogSum, ← filter_prime_Ioc n, Finset.sum_filter]
  rfl

lemma log_pos_of_two_le {n : ℕ} (hn : 2 ≤ n) : 0 < Real.log n :=
  Real.log_pos (by exact_mod_cast hn)

lemma log_two_le_log {n : ℕ} (hn : 2 ≤ n) : Real.log 2 ≤ Real.log n :=
  Real.log_le_log (by norm_num) (by exact_mod_cast hn)

lemma invLog_nonneg {n : ℕ} (_hn : 2 ≤ n) : 0 ≤ invLog n := by
  rw [invLog]
  positivity

lemma invLog_antitone {n : ℕ} (hn : 2 ≤ n) : invLog (n + 1) ≤ invLog n := by
  have h1 : 0 < Real.log n := log_pos_of_two_le hn
  have h2 : Real.log n ≤ Real.log (n + 1 : ℕ) := by
    apply Real.log_le_log (by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_two hn)
    exact_mod_cast Nat.le_succ n
  rw [invLog, invLog]
  exact one_div_le_one_div_of_le h1 h2

lemma sum_cPrime_invLog (N : ℕ) :
    ∑ n ∈ Finset.Ioc 1 N, cPrime n * invLog n = ∑ p ∈ primesLE N, (1 : ℝ) / p := by
  classical
  rw [← filter_prime_Ioc N, Finset.sum_filter]
  refine Finset.sum_congr rfl fun n hn => ?_
  simp only [Finset.mem_Ioc] at hn
  by_cases hp : n.Prime
  · have hn2 : 2 ≤ n := hp.two_le
    have hlog : Real.log n ≠ 0 := (log_pos_of_two_le hn2).ne'
    have hn0 : (n : ℝ) ≠ 0 := by
      have : 0 < n := by omega
      positivity
    simp only [cPrime, invLog, hp, if_true]
    field_simp
  · simp [cPrime, hp]

lemma sum_cChi_invLog (N : ℕ) :
    ∑ n ∈ Finset.Ioc 1 N, cChi n * invLog n = ∑ p ∈ primesLE N, chi5 p / p := by
  classical
  rw [← filter_prime_Ioc N, Finset.sum_filter]
  refine Finset.sum_congr rfl fun n hn => ?_
  simp only [Finset.mem_Ioc] at hn
  by_cases hp : n.Prime
  · have hn2 : 2 ≤ n := hp.two_le
    have hlog : Real.log n ≠ 0 := (log_pos_of_two_le hn2).ne'
    have hn0 : (n : ℝ) ≠ 0 := by
      have : 0 < n := by omega
      positivity
    simp only [cChi, invLog, hp, if_true]
    field_simp
  · simp [cChi, hp]

/-! ## The twisted sum `∑_{p ≤ N} χ₅(p)/p` is bounded -/

/-- **`∑_{p ≤ N} χ₅(p)/p = O(1)`**, unconditionally. -/
theorem abs_sum_chi5_div_primes_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, |∑ p ∈ primesLE N, chi5 p / p| ≤ C := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := abs_primeChiLogSum_le
  refine ⟨C₁ * invLog 2, by
    have : (0 : ℝ) ≤ invLog 2 := invLog_nonneg (le_refl 2)
    positivity, ?_⟩
  intro N
  rw [← sum_cChi_invLog N]
  refine abs_sum_mul_le_of_antitone (B := C₁) ?_ ?_ ?_
  · intro m
    rw [sum_cChi m]
    exact hC₁ m
  · intro n hn
    exact invLog_nonneg (by omega)
  · intro n hn
    exact invLog_antitone (by omega)

/-! ## Mertens' second theorem -/

/-- The elementary two-sided comparison `(b-a)/b ≤ log b - log a ≤ (b-a)/a`. -/
lemma log_sub_log_bounds {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (b - a) / b ≤ Real.log b - Real.log a ∧ Real.log b - Real.log a ≤ (b - a) / a := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  constructor
  · have h := Real.log_le_sub_one_of_pos (x := a / b) (by positivity)
    rw [Real.log_div ha.ne' hb.ne'] at h
    have hrw : a / b - 1 = -((b - a) / b) := by field_simp; ring
    rw [hrw] at h
    linarith
  · have h := Real.log_le_sub_one_of_pos (x := b / a) (by positivity)
    rw [Real.log_div hb.ne' ha.ne'] at h
    have hrw : b / a - 1 = (b - a) / a := by field_simp
    rw [hrw] at h
    linarith

/-- The successive differences of `log log` are bounded below by the summation-by-parts
terms. -/
lemma term_le_loglog_diff {n : ℕ} (hn : 2 ≤ n) :
    Real.log n * (invLog n - invLog (n + 1))
      ≤ Real.log (Real.log (n + 1 : ℕ)) - Real.log (Real.log n) := by
  have ha : 0 < Real.log n := log_pos_of_two_le hn
  have hab : Real.log n ≤ Real.log (n + 1 : ℕ) := by
    apply Real.log_le_log (by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_two hn)
    exact_mod_cast Nat.le_succ n
  have hb : 0 < Real.log (n + 1 : ℕ) := lt_of_lt_of_le ha hab
  have hid : Real.log n * (invLog n - invLog (n + 1))
      = (Real.log (n + 1 : ℕ) - Real.log n) / Real.log (n + 1 : ℕ) := by
    rw [invLog, invLog]
    field_simp
  rw [hid]
  exact (log_sub_log_bounds ha hab).1

/-- ... and above, with an error which is summable. -/
lemma loglog_diff_le_term {n : ℕ} (hn : 2 ≤ n) :
    Real.log (Real.log (n + 1 : ℕ)) - Real.log (Real.log n)
      ≤ Real.log n * (invLog n - invLog (n + 1))
        + (1 / (n : ℝ) ^ 2) / (Real.log 2) ^ 2 := by
  have hn0 : (0 : ℝ) < n := by
    have : 0 < n := by omega
    exact_mod_cast this
  have ha : 0 < Real.log n := log_pos_of_two_le hn
  have hab : Real.log n ≤ Real.log (n + 1 : ℕ) := by
    apply Real.log_le_log (by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_two hn)
    exact_mod_cast Nat.le_succ n
  have hb : 0 < Real.log (n + 1 : ℕ) := lt_of_lt_of_le ha hab
  have hid : Real.log n * (invLog n - invLog (n + 1))
      = (Real.log (n + 1 : ℕ) - Real.log n) / Real.log (n + 1 : ℕ) := by
    rw [invLog, invLog]
    field_simp
  set a := Real.log n with hadef
  set b := Real.log (n + 1 : ℕ) with hbdef
  -- the difference of the two comparisons
  have hupper : Real.log b - Real.log a ≤ (b - a) / a := (log_sub_log_bounds ha hab).2
  have hgap : (b - a) / a - (b - a) / b = (b - a) ^ 2 / (a * b) := by
    field_simp
  -- `b - a ≤ 1/n`
  have hstep : b - a ≤ 1 / (n : ℝ) := by
    have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    have h := Real.log_le_sub_one_of_pos (x := ((n : ℝ) + 1) / (n : ℝ)) (by positivity)
    rw [Real.log_div (by positivity) (by positivity)] at h
    have hrw : ((n : ℝ) + 1) / (n : ℝ) - 1 = 1 / (n : ℝ) := by field_simp; ring
    rw [hrw] at h
    rw [hbdef, hadef, hcast]
    linarith
  have hba : 0 ≤ b - a := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hab2 : (Real.log 2) ^ 2 ≤ a * b := by
    have h1 : Real.log 2 ≤ a := log_two_le_log hn
    nlinarith
  have hsq : (b - a) ^ 2 ≤ (1 / (n : ℝ)) ^ 2 := by nlinarith
  have hfrac : (b - a) ^ 2 / (a * b) ≤ (1 / (n : ℝ) ^ 2) / (Real.log 2) ^ 2 := by
    have hab0 : 0 < a * b := by positivity
    have hlog20 : (0 : ℝ) < (Real.log 2) ^ 2 := by positivity
    rw [div_le_div_iff₀ hab0 hlog20]
    have h1 : (1 / (n : ℝ)) ^ 2 = 1 / (n : ℝ) ^ 2 := by rw [div_pow]; norm_num
    nlinarith [sq_nonneg (b - a), div_nonneg (le_of_lt (by positivity : (0:ℝ) < 1)) (le_of_lt (by positivity : (0:ℝ) < (n:ℝ)^2))]
  rw [hid]
  have := (log_sub_log_bounds ha hab).2
  linarith [hgap, hfrac]

/-- `∑_{2 ≤ n < N} 1/n² ≤ 1`. -/
lemma sum_inv_sq_Ico_le (N : ℕ) : ∑ n ∈ Finset.Ico 2 N, (1 : ℝ) / (n : ℝ) ^ 2 ≤ 1 := by
  rcases le_or_gt 2 N with hN | hN
  · have key : ∀ n ∈ Finset.Ico 2 N,
        (1 : ℝ) / (n : ℝ) ^ 2 ≤ (fun m : ℕ => 1 / ((m : ℝ) - 1)) n
          - (fun m : ℕ => 1 / ((m : ℝ) - 1)) (n + 1) := by
      intro n hn
      simp only [Finset.mem_Ico] at hn
      have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
      have hcast : ((n + 1 : ℕ) : ℝ) - 1 = (n : ℝ) := by push_cast; ring
      simp only [hcast]
      rw [div_sub_div _ _ (by linarith) (by linarith), div_le_div_iff₀ (by positivity) (by nlinarith)]
      nlinarith
    refine le_trans (Finset.sum_le_sum key) ?_
    rw [sum_Ico_sub_succ (fun m : ℕ => 1 / ((m : ℝ) - 1)) hN]
    have h1 : (0 : ℝ) ≤ 1 / ((N : ℝ) - 1) := by
      have h2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      apply div_nonneg (by norm_num)
      linarith
    norm_num
    linarith
  · have : Finset.Ico 2 N = ∅ := Finset.Ico_eq_empty (by omega)
    rw [this]
    norm_num

/-- **Mertens' second theorem.**  `∑_{p ≤ N} 1/p = log log N + O(1)`, unconditionally. -/
theorem abs_sum_inv_primes_sub_loglog_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
      |(∑ p ∈ primesLE N, (1 : ℝ) / p) - Real.log (Real.log N)| ≤ C := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := abs_primeLogSum_sub_log_le
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨1 + 2 * C₁ / Real.log 2 + |Real.log (Real.log 2)| + 1 / (Real.log 2) ^ 2, by positivity,
    ?_⟩
  intro N hN
  have hN1 : 1 ≤ N := by omega
  have hlogN : 0 < Real.log N := log_pos_of_two_le hN
  have hlogN2 : Real.log 2 ≤ Real.log N := log_two_le_log hN
  -- summation by parts
  have hparts := sum_Ioc_by_parts cPrime invLog 1 hN1
  rw [sum_cPrime_invLog N, sum_cPrime N] at hparts
  have hparts' : (∑ p ∈ primesLE N, (1 : ℝ) / p)
      = primeLogSum N * invLog N
        + ∑ n ∈ Finset.Ico 2 N, primeLogSum n * (invLog n - invLog (n + 1)) := by
    have hidx : Finset.Ico (1 + 1) N = Finset.Ico 2 N := by norm_num
    rw [hparts, hidx]
    congr 1
    exact Finset.sum_congr rfl fun n _ => by rw [sum_cPrime n]
  -- the boundary term
  have hbound : |primeLogSum N * invLog N - 1| ≤ C₁ / Real.log 2 := by
    have h1 := hC₁ N hN1
    have hrw : primeLogSum N * invLog N - 1 = (primeLogSum N - Real.log N) / Real.log N := by
      rw [invLog]
      field_simp
    rw [hrw, abs_div, abs_of_pos hlogN, div_le_div_iff₀ hlogN hlog2]
    nlinarith [abs_nonneg (primeLogSum N - Real.log N)]
  -- split the main sum
  have hsplit : ∑ n ∈ Finset.Ico 2 N, primeLogSum n * (invLog n - invLog (n + 1))
      = ∑ n ∈ Finset.Ico 2 N, Real.log n * (invLog n - invLog (n + 1))
        + ∑ n ∈ Finset.Ico 2 N,
            (primeLogSum n - Real.log n) * (invLog n - invLog (n + 1)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  -- the error sum
  have hE : |∑ n ∈ Finset.Ico 2 N,
      (primeLogSum n - Real.log n) * (invLog n - invLog (n + 1))| ≤ C₁ / Real.log 2 := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hb : ∀ n ∈ Finset.Ico 2 N,
        |(primeLogSum n - Real.log n) * (invLog n - invLog (n + 1))|
          ≤ C₁ * (invLog n - invLog (n + 1)) := by
      intro n hn
      simp only [Finset.mem_Ico] at hn
      have hd : (0 : ℝ) ≤ invLog n - invLog (n + 1) := by
        linarith [invLog_antitone (show 2 ≤ n from hn.1)]
      rw [abs_mul, abs_of_nonneg hd]
      exact mul_le_mul_of_nonneg_right (hC₁ n (by omega)) hd
    refine le_trans (Finset.sum_le_sum hb) ?_
    rw [← Finset.mul_sum, sum_Ico_sub_succ invLog hN]
    have hIN : 0 ≤ invLog N := invLog_nonneg hN
    have hI2 : invLog 2 = 1 / Real.log 2 := by rw [invLog]; norm_num
    rw [hI2]
    have : C₁ * (1 / Real.log 2 - invLog N) ≤ C₁ * (1 / Real.log 2) :=
      mul_le_mul_of_nonneg_left (by linarith) hC₁0
    calc C₁ * (1 / Real.log 2 - invLog N) ≤ C₁ * (1 / Real.log 2) := this
      _ = C₁ / Real.log 2 := by ring
  -- the telescoping main term
  have htel : ∑ n ∈ Finset.Ico 2 N,
      (Real.log (Real.log ((n + 1 : ℕ) : ℝ)) - Real.log (Real.log n))
        = Real.log (Real.log N) - Real.log (Real.log 2) := by
    have h := sum_Ico_sub_succ (fun m : ℕ => -Real.log (Real.log m)) hN
    calc ∑ n ∈ Finset.Ico 2 N, (Real.log (Real.log ((n + 1 : ℕ) : ℝ)) - Real.log (Real.log n))
        = ∑ n ∈ Finset.Ico 2 N,
            ((fun m : ℕ => -Real.log (Real.log m)) n
              - (fun m : ℕ => -Real.log (Real.log m)) (n + 1)) :=
          Finset.sum_congr rfl fun n _ => by simp; ring
      _ = -Real.log (Real.log 2) - -Real.log (Real.log N) := h
      _ = Real.log (Real.log N) - Real.log (Real.log 2) := by
          norm_num
          ring
  have hM1 : ∑ n ∈ Finset.Ico 2 N, Real.log n * (invLog n - invLog (n + 1))
      ≤ Real.log (Real.log N) - Real.log (Real.log 2) := by
    rw [← htel]
    exact Finset.sum_le_sum fun n hn => term_le_loglog_diff (Finset.mem_Ico.mp hn).1
  have hM2 : Real.log (Real.log N) - Real.log (Real.log 2) - 1 / (Real.log 2) ^ 2
      ≤ ∑ n ∈ Finset.Ico 2 N, Real.log n * (invLog n - invLog (n + 1)) := by
    have h := Finset.sum_le_sum
      (fun n (hn : n ∈ Finset.Ico 2 N) => loglog_diff_le_term (Finset.mem_Ico.mp hn).1)
    rw [Finset.sum_add_distrib, htel] at h
    have herr : ∑ n ∈ Finset.Ico 2 N, (1 / (n : ℝ) ^ 2) / (Real.log 2) ^ 2
        ≤ 1 / (Real.log 2) ^ 2 := by
      have hrw : ∑ n ∈ Finset.Ico 2 N, (1 / (n : ℝ) ^ 2) / (Real.log 2) ^ 2
          = (∑ n ∈ Finset.Ico 2 N, (1 / (n : ℝ) ^ 2)) / (Real.log 2) ^ 2 := by
        rw [Finset.sum_div]
      rw [hrw]
      have hden : (0 : ℝ) < (Real.log 2) ^ 2 := by positivity
      rw [div_le_div_iff₀ hden hden]
      nlinarith [sum_inv_sq_Ico_le N]
    linarith
  -- combine
  rw [hparts', hsplit, abs_le]
  have h1 := abs_le.mp hbound
  have h2 := abs_le.mp hE
  have h3 : -|Real.log (Real.log 2)| ≤ Real.log (Real.log 2) := neg_abs_le _
  have h4 : Real.log (Real.log 2) ≤ |Real.log (Real.log 2)| := le_abs_self _
  have h5 : (0 : ℝ) ≤ 1 / (Real.log 2) ^ 2 := by positivity
  have hdouble : 2 * C₁ / Real.log 2 = C₁ / Real.log 2 + C₁ / Real.log 2 := by ring
  constructor <;> linarith

/-! ## The reciprocal sum over the primes with `χ₅(p) = 1` -/

lemma chi5_values (n : ℕ) : chi5 n = 1 ∨ chi5 n = -1 ∨ chi5 n = 0 := by
  unfold chi5
  split_ifs <;> simp

lemma eq_five_of_chi5_eq_zero {p : ℕ} (hp : p.Prime) (h : chi5 p = 0) : p = 5 := by
  have hmod : p % 5 = 0 := by
    unfold chi5 at h
    split_ifs at h with h1 h2
    · norm_num at h
    · norm_num at h
    · omega
  have hdvd : (5 : ℕ) ∣ p := Nat.dvd_of_mod_eq_zero hmod
  exact ((Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp hdvd).symm

lemma chi5_five : chi5 5 = 0 := by unfold chi5; norm_num

/-- **The Mertens input of the sieve estimate, proved unconditionally.**  This is the
statement previously carried as a consequence of the hypothesis `MertensProgressions`:
`∑_{p ≤ N, χ₅(p) = 1} 1/p = (log log N)/2 + O(1)`. -/
theorem sum_inv_primes_chi5_unconditional :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 3 ≤ N →
      |(∑ p ∈ Finset.Icc 1 N with (Nat.Prime p ∧ chi5 p = 1), (1 : ℝ) / p)
        - Real.log (Real.log N) / 2| ≤ C := by
  classical
  obtain ⟨C₁, hC₁0, hC₁⟩ := abs_sum_inv_primes_sub_loglog_le
  obtain ⟨C₂, hC₂0, hC₂⟩ := abs_sum_chi5_div_primes_le
  refine ⟨C₁ / 2 + C₂ / 2 + 1 / 10, by positivity, ?_⟩
  intro N hN
  have hfilter : (Finset.Icc 1 N).filter (fun p => Nat.Prime p ∧ chi5 p = 1)
      = (primesLE N).filter (fun p => chi5 p = 1) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc, mem_primesLE]
    constructor
    · rintro ⟨⟨_, h2⟩, hp, hchi⟩; exact ⟨⟨h2, hp⟩, hchi⟩
    · rintro ⟨⟨h1, hp⟩, hchi⟩; exact ⟨⟨hp.one_lt.le.trans' (by norm_num), h1⟩, hp, hchi⟩
  rw [hfilter, Finset.sum_filter]
  have hpt : ∀ p ∈ primesLE N, (if chi5 p = 1 then (1 : ℝ) / p else 0)
      = 1 / 2 * ((1 : ℝ) / p) + 1 / 2 * (chi5 p / p) - (if p = 5 then (1 : ℝ) / 10 else 0) := by
    intro p hp
    obtain ⟨hpN, hpp⟩ := mem_primesLE.mp hp
    rcases chi5_values p with h | h | h
    · have hp5 : p ≠ 5 := by
        intro h5; rw [h5, chi5_five] at h; norm_num at h
      rw [if_pos h, if_neg hp5, h]
      ring
    · have hp5 : p ≠ 5 := by
        intro h5; rw [h5, chi5_five] at h; norm_num at h
      rw [if_neg (by rw [h]; norm_num), if_neg hp5, h]
      ring
    · have hp5 : p = 5 := eq_five_of_chi5_eq_zero hpp h
      rw [if_neg (by rw [h]; norm_num), if_pos hp5, h, hp5]
      norm_num
  rw [Finset.sum_congr rfl hpt, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum]
  have hδ : ∑ p ∈ primesLE N, (if p = 5 then (1 : ℝ) / 10 else 0)
      = if 5 ∈ primesLE N then (1 : ℝ) / 10 else 0 := by
    simp
  have hδ0 : 0 ≤ ∑ p ∈ primesLE N, (if p = 5 then (1 : ℝ) / 10 else 0) := by
    rw [hδ]; split_ifs <;> norm_num
  have hδ1 : ∑ p ∈ primesLE N, (if p = 5 then (1 : ℝ) / 10 else 0) ≤ 1 / 10 := by
    rw [hδ]; split_ifs <;> norm_num
  have h1 := abs_le.mp (hC₁ N (by omega))
  have h2 := abs_le.mp (hC₂ N)
  have hchi : ∑ p ∈ primesLE N, chi5 p / (p : ℝ) = ∑ p ∈ primesLE N, chi5 p / p := rfl
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

end FactorialHypergraph
