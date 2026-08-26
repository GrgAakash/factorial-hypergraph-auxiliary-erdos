/-
# Mertens' first theorem: the lower bound, and the interval form of the dimension condition

This file supplies the *lower* half of Mertens' first theorem, weighted by the root counts
of `f(t) = t² + 3t + 1`, which is what is needed to verify the conventional
(interval) form of the sieve dimension condition — Axiom 2′ of the sieve literature —

  `∑_{w₁ < ℓ ≤ w₂} ρ(ℓ) log ℓ / ℓ ≤ log (w₂/w₁) + C₁`   (`2 ≤ w₁ ≤ w₂`),

rather than only its anchored special case `w₁ = 2`.  (The anchored upper bound alone does
*not* imply the interval bound: a density supported on `(√z, z]` with `ρ = 2` there
satisfies the anchored bound with `κ = 1` but has local dimension `2`.)

Everything here is unconditional and elementary:

* `sum_log_ge` : `N log N - N ≤ ∑_{n ≤ N} log n` (induction, using `log x ≤ x - 1`);
* `sum_vonMangoldt_div_ge` : `log N - 1 ≤ ∑_{n ≤ N} Λ(n)/n`  (from the divisor identity
  `∑_{n≤N} log n = ∑_{d≤N} Λ(d) ⌊N/d⌋` of `MertensAux.lean` and `⌊N/d⌋ ≤ N/d`);
* `sum_vonMangoldt_nonprime_le` : the prime-power part `∑_{n ≤ N, n not prime} Λ(n)/n` is
  bounded (it is at most `∑_{p} log p /(p(p-1))`);
* `sum_log_div_prime_ge` : `log N - C ≤ ∑_{p ≤ N} log p / p`;
* `mertensRoots_lower` : `log N - C ≤ ∑_{p ≤ N} ρ(p) log p / p`, using `ρ = 1 + χ₅` and the
  unconditional character-sum bound of `MertensCharacter.lean`;
* `mertensRoots_upper_div_p` : the matching upper bound in the `1/p` normalisation.
-/
import FactorialHypergraph.MertensRoots

namespace FactorialHypergraph

open Finset

/-! ## `∑_{n ≤ N} log n ≥ N log N - N` -/

/-- `N log N - N ≤ ∑_{n ≤ N} log n`, by induction, using `log (1 + 1/N) ≤ 1/N`. -/
theorem sum_log_ge (N : ℕ) :
    (N : ℝ) * Real.log N - N ≤ ∑ n ∈ Finset.Icc 1 N, Real.log n := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · norm_num
    · have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
      have hlog : Real.log ((N : ℝ) + 1) - Real.log N ≤ 1 / (N : ℝ) := by
        have h := Real.log_le_sub_one_of_pos
          (show (0 : ℝ) < ((N : ℝ) + 1) / (N : ℝ) by positivity)
        rw [Real.log_div (by positivity) (by positivity)] at h
        have h2 : ((N : ℝ) + 1) / (N : ℝ) - 1 = 1 / (N : ℝ) := by field_simp; ring
        rw [h2] at h
        exact h
      have hmul : (N : ℝ) * (Real.log ((N : ℝ) + 1) - Real.log N) ≤ 1 := by
        have h3 := mul_le_mul_of_nonneg_left hlog hN0.le
        rwa [mul_one_div, div_self hN0.ne'] at h3
      have hstep : ((N : ℝ) + 1) * Real.log ((N : ℝ) + 1) - ((N : ℝ) + 1)
          ≤ ((N : ℝ) * Real.log N - N) + Real.log ((N : ℝ) + 1) := by nlinarith
      calc ((N + 1 : ℕ) : ℝ) * Real.log ((N + 1 : ℕ) : ℝ) - ((N + 1 : ℕ) : ℝ)
          = ((N : ℝ) + 1) * Real.log ((N : ℝ) + 1) - ((N : ℝ) + 1) := by push_cast; ring
        _ ≤ ((N : ℝ) * Real.log N - N) + Real.log ((N : ℝ) + 1) := hstep
        _ ≤ (∑ n ∈ Finset.Icc 1 N, Real.log n) + Real.log ((N + 1 : ℕ) : ℝ) := by
            push_cast; linarith

/-! ## Mertens' first theorem, lower bound, von Mangoldt form -/

/-- **Mertens' first theorem (lower bound).**  `log N - 1 ≤ ∑_{n ≤ N} Λ(n)/n`. -/
theorem sum_vonMangoldt_div_ge {N : ℕ} (hN : 1 ≤ N) :
    Real.log N - 1 ≤ ∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n / n := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hupper : ∑ n ∈ Finset.Icc 1 N, Real.log n
      ≤ (N : ℝ) * ∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n / n := by
    rw [sum_log_eq_sum_vonMangoldt_mul_floor N, Finset.mul_sum]
    refine Finset.sum_le_sum fun d hd => ?_
    simp only [Finset.mem_Icc] at hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd.1
    have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt d := ArithmeticFunction.vonMangoldt_nonneg
    have hfloor : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / d := by
      rw [le_div_iff₀ hd0]
      exact_mod_cast Nat.div_mul_le_self N d
    calc ArithmeticFunction.vonMangoldt d * ((N / d : ℕ) : ℝ)
        ≤ ArithmeticFunction.vonMangoldt d * ((N : ℝ) / d) :=
          mul_le_mul_of_nonneg_left hfloor hΛ
      _ = (N : ℝ) * (ArithmeticFunction.vonMangoldt d / d) := by ring
  have hlow := sum_log_ge N
  have key : (N : ℝ) * (Real.log N - 1)
      ≤ (N : ℝ) * ∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n / n := by
    nlinarith
  exact le_of_mul_le_mul_left key hN0

/-! ## A geometric tail -/

/-- `∑_{k = 2}^{M} x^{-k} ≤ 1/(x(x-1))` for `x ≥ 2`. -/
theorem sum_inv_pow_Icc_le {x : ℝ} (hx : 2 ≤ x) (M : ℕ) :
    ∑ k ∈ Finset.Icc 2 M, (x ^ k)⁻¹ ≤ (x * (x - 1))⁻¹ := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hx1 : (0 : ℝ) < x - 1 := by linarith
  have key : ∀ M : ℕ, 1 ≤ M →
      ∑ k ∈ Finset.Icc 2 M, (x ^ k)⁻¹ ≤ (x * (x - 1))⁻¹ - (x ^ M * (x - 1))⁻¹ := by
    intro M hM
    induction M, hM using Nat.le_induction with
    | base => simp
    | succ M hM ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ M + 1)]
      have hpM : (0 : ℝ) < x ^ M := by positivity
      have hstep : (x ^ (M + 1))⁻¹ = (x ^ M * (x - 1))⁻¹ - (x ^ (M + 1) * (x - 1))⁻¹ := by
        field_simp
        ring
      linarith
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp
    positivity
  · have h := key M hM
    have h2 : (0 : ℝ) ≤ (x ^ M * (x - 1))⁻¹ := by positivity
    linarith

/-! ## The prime-power part is bounded -/

open scoped Classical in
/-- The contribution of the proper prime powers, `∑_{n ≤ N, n not prime} Λ(n)/n`, is bounded
uniformly in `N`: it is at most `∑_{p ≤ N} log p/(p(p-1))`. -/
theorem sum_vonMangoldt_nonprime_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      ∑ n ∈ (Finset.Icc 1 N).filter (fun n => ¬ Nat.Prime n),
          ArithmeticFunction.vonMangoldt n / n ≤ C := by
  classical
  obtain ⟨C₂, hC₂0, hC₂⟩ := sum_log_div_mul_pred_bounded
  refine ⟨C₂, hC₂0, fun N => ?_⟩
  -- restrict to the prime powers
  set T := (Finset.Icc 1 N).filter (fun n => ¬ Nat.Prime n ∧ IsPrimePow n) with hT
  have hzero : ∑ n ∈ (Finset.Icc 1 N).filter (fun n => ¬ Nat.Prime n),
      ArithmeticFunction.vonMangoldt n / n
      = ∑ n ∈ T, ArithmeticFunction.vonMangoldt n / n := by
    rw [hT, show (Finset.Icc 1 N).filter (fun n => ¬ Nat.Prime n ∧ IsPrimePow n)
        = ((Finset.Icc 1 N).filter (fun n => ¬ Nat.Prime n)).filter (fun n => IsPrimePow n) by
      rw [Finset.filter_filter]]
    refine (Finset.sum_filter_of_ne ?_).symm
    intro n _ hne
    by_contra hpp
    rw [ArithmeticFunction.vonMangoldt_apply, if_neg hpp] at hne
    simp at hne
  rw [hzero]
  -- the injection `n ↦ (minFac n, v_{minFac n}(n))`
  set g : ℕ → ℕ × ℕ := fun n => (n.minFac, n.factorization n.minFac) with hg
  have hpow : ∀ n ∈ T, n.minFac ^ (n.factorization n.minFac) = n := by
    intro n hn
    simp only [hT, Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨-, -, hpp⟩ := hn
    obtain ⟨p, k, hp, hk, rfl⟩ := hpp
    have hp' : Nat.Prime p := hp.nat_prime
    rw [Nat.pow_minFac (by omega : k ≠ 0), Nat.Prime.minFac_eq hp',
      Nat.Prime.factorization_pow hp']
    simp
  have hinj : Set.InjOn g ↑T := by
    intro x hx y hy hxy
    have hx' := hpow x (by simpa using hx)
    have hy' := hpow y (by simpa using hy)
    simp only [hg, Prod.mk.injEq] at hxy
    calc x = x.minFac ^ (x.factorization x.minFac) := hx'.symm
      _ = y.minFac ^ (y.factorization y.minFac) := by rw [hxy.2, hxy.1]
      _ = y := hy'
  have hmapsto : T.image g ⊆ (primesLE N) ×ˢ (Finset.Icc 2 N) := by
    intro q hq
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hq
    have hn' := hn
    simp only [hT, Finset.mem_filter, Finset.mem_Icc] at hn'
    obtain ⟨⟨hn1, hnN⟩, hnp, hpp⟩ := hn'
    obtain ⟨p, k, hp, hk, rfl⟩ := hpp
    have hp' : Nat.Prime p := hp.nat_prime
    have hmf : (p ^ k).minFac = p := by
      rw [Nat.pow_minFac (by omega : k ≠ 0), Nat.Prime.minFac_eq hp']
    have hfac : (p ^ k).factorization p = k := by
      rw [Nat.Prime.factorization_pow hp']; simp
    have hk2 : 2 ≤ k := by
      rcases Nat.lt_or_ge k 2 with h | h
      · have hk1 : k = 1 := by omega
        subst hk1
        rw [pow_one] at hnp
        exact absurd hp' hnp
      · exact h
    have hpn : p ≤ p ^ k :=
      le_trans (le_of_eq (pow_one p).symm) (Nat.pow_le_pow_right hp'.pos (by omega))
    have hkn : k ≤ p ^ k :=
      le_trans (le_of_lt Nat.lt_two_pow_self) (Nat.pow_le_pow_left hp'.two_le k)
    simp only [hg, Finset.mem_product, Finset.mem_Icc, hmf, hfac]
    exact ⟨mem_primesLE.mpr ⟨le_trans hpn hnN, hp'⟩, ⟨hk2, le_trans hkn hnN⟩⟩
  -- rewrite the sum as a sum over pairs `(p, k)`
  have hterm : ∀ n ∈ T, ArithmeticFunction.vonMangoldt n / n
      = Real.log ((g n).1) / (((g n).1 : ℝ) ^ ((g n).2)) := by
    intro n hn
    have hn' := hn
    simp only [hT, Finset.mem_filter] at hn'
    have hpp := hn'.2.2
    have hrec := hpow n hn
    rw [ArithmeticFunction.vonMangoldt_apply, if_pos hpp]
    simp only [hg]
    rw [show ((n.minFac : ℝ) ^ (n.factorization n.minFac))
        = ((n.minFac ^ (n.factorization n.minFac) : ℕ) : ℝ) by push_cast; ring, hrec]
  have hstep1 : ∑ n ∈ T, ArithmeticFunction.vonMangoldt n / n
      = ∑ q ∈ T.image g, Real.log (q.1) / ((q.1 : ℝ) ^ q.2) := by
    rw [Finset.sum_image hinj]
    exact Finset.sum_congr rfl hterm
  have hnonneg : ∀ q ∈ (primesLE N) ×ˢ (Finset.Icc 2 N),
      0 ≤ Real.log (q.1) / ((q.1 : ℝ) ^ q.2) := by
    intro q hq
    simp only [Finset.mem_product] at hq
    have hp := (mem_primesLE.mp hq.1).2
    have h1 : (1 : ℝ) ≤ (q.1 : ℝ) := by exact_mod_cast hp.one_lt.le
    have h2 : (0 : ℝ) ≤ Real.log q.1 := Real.log_nonneg h1
    positivity
  have hstep2 : ∑ q ∈ T.image g, Real.log (q.1) / ((q.1 : ℝ) ^ q.2)
      ≤ ∑ q ∈ (primesLE N) ×ˢ (Finset.Icc 2 N), Real.log (q.1) / ((q.1 : ℝ) ^ q.2) :=
    Finset.sum_le_sum_of_subset_of_nonneg hmapsto (fun q hq _ => hnonneg q hq)
  have hstep3 : ∑ q ∈ (primesLE N) ×ˢ (Finset.Icc 2 N), Real.log (q.1) / ((q.1 : ℝ) ^ q.2)
      ≤ ∑ p ∈ primesLE N, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) := by
    rw [Finset.sum_product]
    refine Finset.sum_le_sum fun p hp => ?_
    have hpp := (mem_primesLE.mp hp).2
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hlogp : (0 : ℝ) ≤ Real.log p := Real.log_nonneg (by linarith)
    have hgeo := sum_inv_pow_Icc_le hp2 N
    calc ∑ k ∈ Finset.Icc 2 N, Real.log (p) / ((p : ℝ) ^ k)
        = Real.log p * ∑ k ∈ Finset.Icc 2 N, ((p : ℝ) ^ k)⁻¹ := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun k _ => by rw [div_eq_mul_inv])
      _ ≤ Real.log p * ((p : ℝ) * ((p : ℝ) - 1))⁻¹ := mul_le_mul_of_nonneg_left hgeo hlogp
      _ = Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) := by rw [div_eq_mul_inv]
  calc ∑ n ∈ T, ArithmeticFunction.vonMangoldt n / n
      = ∑ q ∈ T.image g, Real.log (q.1) / ((q.1 : ℝ) ^ q.2) := hstep1
    _ ≤ ∑ q ∈ (primesLE N) ×ˢ (Finset.Icc 2 N), Real.log (q.1) / ((q.1 : ℝ) ^ q.2) := hstep2
    _ ≤ ∑ p ∈ primesLE N, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) := hstep3
    _ ≤ C₂ := hC₂ N

/-! ## Mertens' first theorem, lower bound, prime form -/

open scoped Classical in
/-- The primes up to `N`, as a filter of `Icc 1 N`. -/
theorem filter_prime_Icc_eq (N : ℕ) :
    (Finset.Icc 1 N).filter (fun n => Nat.Prime n) = primesLE N := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_Icc, mem_primesLE]
  constructor
  · rintro ⟨⟨-, h2⟩, h3⟩; exact ⟨h2, h3⟩
  · rintro ⟨h1, h2⟩; exact ⟨⟨h2.one_lt.le.trans' (by norm_num), h1⟩, h2⟩

open scoped Classical in
/-- Splitting the von Mangoldt sum into its prime part and its prime-power part. -/
theorem sum_vonMangoldt_split (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n / n
      = (∑ p ∈ primesLE N, Real.log p / p)
        + ∑ n ∈ (Finset.Icc 1 N).filter (fun n => ¬ Nat.Prime n),
            ArithmeticFunction.vonMangoldt n / n := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 N) (fun n => Nat.Prime n)]
  congr 1
  rw [filter_prime_Icc_eq N]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [ArithmeticFunction.vonMangoldt_apply_prime (mem_primesLE.mp hp).2]

/-- **Mertens' first theorem, prime form, lower bound.**
`log N - C ≤ ∑_{p ≤ N} log p / p`, with an absolute `C`. -/
theorem sum_log_div_prime_ge :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
      Real.log N - C ≤ ∑ p ∈ primesLE N, Real.log p / p := by
  classical
  obtain ⟨C₃, hC₃0, hC₃⟩ := sum_vonMangoldt_nonprime_le
  refine ⟨1 + C₃, by linarith, fun N hN => ?_⟩
  have h1 := sum_vonMangoldt_div_ge hN
  have h2 := sum_vonMangoldt_split N
  have h3 := hC₃ N
  rw [h2] at h1
  linarith

/-! ## The root-weighted Mertens estimates in the `1/p` normalisation -/

open scoped Classical in
/-- The character-twisted prime sum `∑_{p ≤ N} χ₅(p) log p / p` is bounded. -/
theorem chi5_prime_sum_bounded :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      |∑ p ∈ primesLE N, chi5 p * Real.log p / p| ≤ C := by
  classical
  obtain ⟨C₁, hC₁0, hC₁⟩ := chi5_vonMangoldt_sum_bounded
  obtain ⟨C₃, hC₃0, hC₃⟩ := sum_vonMangoldt_nonprime_le
  refine ⟨C₁ + C₃, by linarith, fun N => ?_⟩
  set A := ∑ p ∈ primesLE N, chi5 p * Real.log p / p with hA
  set B := ∑ n ∈ (Finset.Icc 1 N).filter (fun n => ¬ Nat.Prime n),
      chi5 n * ArithmeticFunction.vonMangoldt n / n with hB
  have hsplit : ∑ n ∈ Finset.Icc 1 N, chi5 n * ArithmeticFunction.vonMangoldt n / n = A + B := by
    rw [hA, hB, ← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 N) (fun n => Nat.Prime n)]
    congr 1
    rw [filter_prime_Icc_eq N]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [ArithmeticFunction.vonMangoldt_apply_prime (mem_primesLE.mp hp).2]
  have htail : |B| ≤ C₃ := by
    rw [hB]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_sum (fun n _ => ?_)) (hC₃ N)
    have hnn : (0 : ℝ) ≤ ArithmeticFunction.vonMangoldt n / n :=
      div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg n)
    calc |chi5 n * ArithmeticFunction.vonMangoldt n / n|
        = |chi5 n| * (ArithmeticFunction.vonMangoldt n / n) := by
          rw [mul_div_assoc, abs_mul, abs_of_nonneg hnn]
      _ ≤ 1 * (ArithmeticFunction.vonMangoldt n / n) :=
          mul_le_mul_of_nonneg_right (abs_chi5_le_one n) hnn
      _ = ArithmeticFunction.vonMangoldt n / n := one_mul _
  have h1 := hC₁ N
  rw [hsplit] at h1
  have hAeq : A = (A + B) - B := by ring
  have hb : |(A + B) - B| ≤ |A + B| + |B| := abs_sub (A + B) B
  rw [hAeq]
  linarith

/-- **The root-weighted Mertens lower bound.**
`log N - C ≤ ∑_{p ≤ N} ρ(p) log p / p`, with an absolute `C`; here `ρ = rootCount` is the
number of roots of `f(t) = t² + 3t + 1` modulo `p`, and `ρ(p) = 1 + χ₅(p)`. -/
theorem mertensRoots_lower :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
      Real.log N - C ≤ ∑ p ∈ primesLE N, (rootCount p : ℝ) * Real.log p / p := by
  classical
  obtain ⟨C₄, hC₄0, hC₄⟩ := sum_log_div_prime_ge
  obtain ⟨C₅, hC₅0, hC₅⟩ := chi5_prime_sum_bounded
  refine ⟨C₄ + C₅, by linarith, fun N hN => ?_⟩
  have hsplit : ∑ p ∈ primesLE N, (rootCount p : ℝ) * Real.log p / p
      = (∑ p ∈ primesLE N, Real.log p / p) + ∑ p ∈ primesLE N, chi5 p * Real.log p / p := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hpp := (mem_primesLE.mp hp).2
    rw [rootCount_eq_one_add_chi5 hpp]
    ring
  have h1 := hC₄ N hN
  have h2 := neg_abs_le (∑ p ∈ primesLE N, chi5 p * Real.log p / p)
  have h3 := hC₅ N
  rw [hsplit]
  linarith

/-- The root-weighted Mertens **upper** bound in the `1/p` normalisation (a weakening of
`mertensRoots_unconditional`, which is stated with `1/(p-1)`). -/
theorem mertensRoots_upper_div_p :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
      ∑ p ∈ primesLE N, (rootCount p : ℝ) * Real.log p / p ≤ Real.log N + C := by
  obtain ⟨C, hC0, hC⟩ := mertensRoots_unconditional
  refine ⟨C, hC0, fun N hN => ?_⟩
  refine le_trans (Finset.sum_le_sum fun p hp => ?_) (hC N hN)
  have hpp := (mem_primesLE.mp hp).2
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
  have hnum : 0 ≤ (rootCount p : ℝ) * Real.log p :=
    mul_nonneg (by positivity) (Real.log_natCast_nonneg p)
  gcongr <;> linarith

end FactorialHypergraph

/-! ## Axiom audit -/

#print axioms FactorialHypergraph.sum_log_ge
#print axioms FactorialHypergraph.sum_vonMangoldt_div_ge
#print axioms FactorialHypergraph.sum_vonMangoldt_nonprime_le
#print axioms FactorialHypergraph.sum_log_div_prime_ge
#print axioms FactorialHypergraph.chi5_prime_sum_bounded
#print axioms FactorialHypergraph.mertensRoots_lower
#print axioms FactorialHypergraph.mertensRoots_upper_div_p
