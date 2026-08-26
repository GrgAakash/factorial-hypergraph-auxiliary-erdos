/-
# Elementary auxiliary estimates for Mertens-type sums

This file collects the *unconditional, elementary* ingredients used in
`FactorialHypergraph/MertensCharacter.lean` and `FactorialHypergraph/MertensRoots.lean` to prove the
field `LargePrimeInputs.mertensRoots`.  Nothing here is problem-specific: all statements
are standard, reusable facts.

* `sum_Icc_divisors_swap` — the Dirichlet divisor-swap identity
  `∑_{n ≤ N} ∑_{d ∣ n} g d (n/d) = ∑_{d ≤ N} ∑_{m ≤ N/d} g d m`;
* `sum_log_eq_sum_vonMangoldt_mul_floor` — `∑_{n ≤ N} log n = ∑_{d ≤ N} Λ(d) ⌊N/d⌋`;
* `sum_vonMangoldt_div_le` — **Mertens' first theorem, upper bound**, in the von Mangoldt
  form `∑_{n ≤ N} Λ(n)/n ≤ log N + (log 4 + 4)`;
* `sum_Ioc_by_parts` and `abs_sum_mul_le_of_antitone` — summation by parts and the discrete
  **Dirichlet test** `|∑_{M < n ≤ N} c(n) f(n)| ≤ B · f(M+1)` for antitone nonnegative `f`
  whose companion `c` has partial sums bounded by `B`;
* `sum_log_div_mul_pred_bounded` — `∑_{p ≤ N} log p /(p(p-1)) ≤ C`, uniformly in `N`.

The only external input is Chebyshev's elementary bound `ψ(x) ≤ (log 4 + 4) x`
(`Chebyshev.psi_le_const_mul_self` in mathlib).
-/
import FactorialHypergraph.LargePrimeFactors

namespace FactorialHypergraph

open Finset

/-! ## The divisor swap -/

/-- **Dirichlet's divisor swap.**  For any `g : ℕ → ℕ → ℝ`,
`∑_{n ≤ N} ∑_{d ∣ n} g d (n/d) = ∑_{d ≤ N} ∑_{m ≤ N/d} g d m`. -/
theorem sum_Icc_divisors_swap (N : ℕ) (g : ℕ → ℕ → ℝ) :
    ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors, g d (n / d)
      = ∑ d ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 (N / d), g d m := by
  classical
  have hL : ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors, g d (n / d)
      = ∑ x ∈ (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter (fun x => x.2 ∣ x.1),
          g x.2 (x.1 / x.2) := by
    rw [Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun n hn => ?_
    simp only [Finset.mem_Icc] at hn
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ (fun d _ => rfl)
    ext d
    simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hd, hn0⟩
      exact ⟨⟨Nat.one_le_iff_ne_zero.mpr (by rintro rfl; simp at hd; omega),
        le_trans (Nat.le_of_dvd (by omega) hd) hn.2⟩, hd⟩
    · rintro ⟨-, hd⟩
      exact ⟨hd, by omega⟩
  have hR : ∑ d ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 (N / d), g d m
      = ∑ x ∈ (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter (fun x => x.1 * x.2 ≤ N),
          g x.1 x.2 := by
    rw [Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun d hd => ?_
    simp only [Finset.mem_Icc] at hd
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ (fun m _ => rfl)
    ext m
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hm1, hm2⟩
      exact ⟨⟨hm1, le_trans hm2 (Nat.div_le_self _ _)⟩, by
        simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le (show 0 < d by omega)).mp hm2⟩
    · rintro ⟨⟨hm1, -⟩, hle⟩
      exact ⟨hm1, (Nat.le_div_iff_mul_le (show 0 < d by omega)).mpr (by
        simpa [Nat.mul_comm] using hle)⟩
  rw [hL, hR]
  refine Finset.sum_nbij' (i := fun x => (x.2, x.1 / x.2)) (j := fun y => (y.1 * y.2, y.1))
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨n, d⟩ hx
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hx ⊢
    obtain ⟨⟨⟨hn1, hnN⟩, hd1, hdN⟩, hdvd⟩ := hx
    obtain ⟨k, rfl⟩ := hdvd
    have hd0 : 0 < d := by omega
    rw [Nat.mul_div_cancel_left _ hd0]
    refine ⟨⟨⟨hd1, hdN⟩, ⟨?_, ?_⟩⟩, ?_⟩ <;> nlinarith [hn1, hnN]
  · rintro ⟨d, m⟩ hy
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hy ⊢
    obtain ⟨⟨⟨hd1, hdN⟩, hm1, hmN⟩, hle⟩ := hy
    refine ⟨⟨⟨?_, hle⟩, hd1, hdN⟩, ⟨m, rfl⟩⟩
    nlinarith
  · rintro ⟨n, d⟩ hx
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hx
    obtain ⟨⟨⟨hn1, hnN⟩, hd1, hdN⟩, hdvd⟩ := hx
    have hd0 : 0 < d := by omega
    simp [Nat.mul_div_cancel' hdvd]
  · rintro ⟨d, m⟩ hy
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hy
    obtain ⟨⟨⟨hd1, hdN⟩, hm1, hmN⟩, hle⟩ := hy
    have hd0 : 0 < d := by omega
    simp [Nat.mul_div_cancel_left _ hd0]
  · rintro ⟨n, d⟩ _
    rfl

/-! ## Mertens' first theorem (upper bound), von Mangoldt form -/

/-- `∑_{n ≤ N} log n = ∑_{d ≤ N} Λ(d) ⌊N/d⌋`. -/
theorem sum_log_eq_sum_vonMangoldt_mul_floor (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, Real.log n
      = ∑ d ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt d * ((N / d : ℕ) : ℝ) := by
  have h := sum_Icc_divisors_swap N (fun d _ => (ArithmeticFunction.vonMangoldt d : ℝ))
  simp only [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel] at h
  rw [show (∑ n ∈ Finset.Icc 1 N, Real.log n)
      = ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors, ArithmeticFunction.vonMangoldt d from
    Finset.sum_congr rfl fun n _ => ArithmeticFunction.vonMangoldt_sum.symm, h]
  exact Finset.sum_congr rfl fun d _ => mul_comm _ _

/-- Chebyshev's upper bound in the form `∑_{n ≤ N} Λ(n) ≤ (log 4 + 4) N`. -/
theorem sum_vonMangoldt_le (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n ≤ (Real.log 4 + 4) * N := by
  have h := Chebyshev.psi_le_const_mul_self (x := (N : ℝ)) (by positivity)
  rw [Chebyshev.psi] at h
  simpa [Nat.floor_natCast, show Finset.Ioc 0 N = Finset.Icc 1 N from rfl] using h

/-- **Mertens' first theorem (upper bound).**  `∑_{n ≤ N} Λ(n)/n ≤ log N + (log 4 + 4)`.
This is elementary: it uses only `∑_{n ≤ N} log n ≤ N log N`, the identity
`∑_{n ≤ N} log n = ∑_{d ≤ N} Λ(d) ⌊N/d⌋` and Chebyshev's bound. -/
theorem sum_vonMangoldt_div_le {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n / n
      ≤ Real.log N + (Real.log 4 + 4) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hup : ∑ n ∈ Finset.Icc 1 N, Real.log n ≤ (N : ℝ) * Real.log N := by
    calc ∑ n ∈ Finset.Icc 1 N, Real.log n ≤ ∑ _n ∈ Finset.Icc 1 N, Real.log N := by
          refine Finset.sum_le_sum fun n hn => ?_
          simp only [Finset.mem_Icc] at hn
          exact Real.log_le_log (by exact_mod_cast hn.1) (by exact_mod_cast hn.2)
      _ = (N : ℝ) * Real.log N := by simp [Nat.card_Icc]
  have hlow : (N : ℝ) * (∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n / n)
      - (∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n)
      ≤ ∑ n ∈ Finset.Icc 1 N, Real.log n := by
    rw [sum_log_eq_sum_vonMangoldt_mul_floor N, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun d hd => ?_
    simp only [Finset.mem_Icc] at hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd.1
    have hnat : N < d * (N / d) + d := by
      have h1 := Nat.div_add_mod N d
      have h2 : N % d < d := Nat.mod_lt _ (by omega)
      omega
    have hlt : (N : ℝ) < (d : ℝ) * ((N / d : ℕ) : ℝ) + d := by exact_mod_cast hnat
    have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt d := ArithmeticFunction.vonMangoldt_nonneg
    have hkey : (N : ℝ) / d - 1 ≤ ((N / d : ℕ) : ℝ) := by
      rw [div_sub_one hd0.ne', div_le_iff₀ hd0]; nlinarith
    have hmul := mul_le_mul_of_nonneg_left hkey hΛ
    calc (N : ℝ) * (ArithmeticFunction.vonMangoldt d / d) - ArithmeticFunction.vonMangoldt d
        = ArithmeticFunction.vonMangoldt d * ((N : ℝ) / d - 1) := by field_simp
      _ ≤ ArithmeticFunction.vonMangoldt d * ((N / d : ℕ) : ℝ) := hmul
  have hc := sum_vonMangoldt_le N
  have key : (N : ℝ) * (∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n / n)
      ≤ (N : ℝ) * (Real.log N + (Real.log 4 + 4)) := by nlinarith
  exact le_of_mul_le_mul_left key hN0

/-! ## The discrete Dirichlet test -/

/-- Telescoping sum. -/
theorem sum_Ico_sub_succ (f : ℕ → ℝ) {a b : ℕ} (h : a ≤ b) :
    ∑ n ∈ Finset.Ico a b, (f n - f (n + 1)) = f a - f b := by
  induction b, h using Nat.le_induction with
  | base => simp
  | succ b hab ih => rw [Finset.sum_Ico_succ_top (by omega), ih]; ring

/-- Summation by parts on `Ioc M N`. -/
theorem sum_Ioc_by_parts (c f : ℕ → ℝ) (M : ℕ) {N : ℕ} (hMN : M ≤ N) :
    ∑ n ∈ Finset.Ioc M N, c n * f n
      = (∑ n ∈ Finset.Ioc M N, c n) * f N
        + ∑ n ∈ Finset.Ico (M + 1) N, (∑ k ∈ Finset.Ioc M n, c k) * (f n - f (n + 1)) := by
  induction N, hMN using Nat.le_induction with
  | base => simp
  | succ N hMN ih =>
    rw [Finset.sum_Ioc_succ_top (by omega), Finset.sum_Ioc_succ_top (by omega), ih]
    rcases eq_or_lt_of_le hMN with h | h
    · subst h; simp
    · rw [Finset.sum_Ico_succ_top (by omega)]; ring

/-- **Discrete Dirichlet test.**  If all partial sums `∑_{M < n ≤ m} c n` are bounded in
absolute value by `B`, and `f` is nonnegative and antitone on `(M, ∞)`, then
`|∑_{M < n ≤ N} c n f n| ≤ B · f (M+1)`. -/
theorem abs_sum_mul_le_of_antitone {c f : ℕ → ℝ} {B : ℝ} {M N : ℕ}
    (hpart : ∀ m, |∑ n ∈ Finset.Ioc M m, c n| ≤ B)
    (hf0 : ∀ n, M < n → 0 ≤ f n) (hanti : ∀ n, M < n → f (n + 1) ≤ f n) :
    |∑ n ∈ Finset.Ioc M N, c n * f n| ≤ B * f (M + 1) := by
  have hB : 0 ≤ B := by have := hpart M; simpa using this
  rcases le_or_gt N M with hNM | hNM
  · rw [Finset.Ioc_eq_empty (by omega)]
    simpa using mul_nonneg hB (hf0 (M + 1) (by omega))
  · have hMN : M ≤ N := le_of_lt hNM
    rw [sum_Ioc_by_parts c f M hMN]
    have h1 : |(∑ n ∈ Finset.Ioc M N, c n) * f N| ≤ B * f N := by
      rw [abs_mul, abs_of_nonneg (hf0 N hNM)]
      exact mul_le_mul_of_nonneg_right (hpart N) (hf0 N hNM)
    have h2 : |∑ n ∈ Finset.Ico (M + 1) N, (∑ k ∈ Finset.Ioc M n, c k) * (f n - f (n + 1))|
        ≤ B * (f (M + 1) - f N) := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      have hb : ∀ n ∈ Finset.Ico (M + 1) N,
          |(∑ k ∈ Finset.Ioc M n, c k) * (f n - f (n + 1))| ≤ B * (f n - f (n + 1)) := by
        intro n hn
        simp only [Finset.mem_Ico] at hn
        have hd : (0 : ℝ) ≤ f n - f (n + 1) := by linarith [hanti n (by omega : M < n)]
        rw [abs_mul, abs_of_nonneg hd]
        exact mul_le_mul_of_nonneg_right (hpart n) hd
      refine le_trans (Finset.sum_le_sum hb) ?_
      rw [← Finset.mul_sum, sum_Ico_sub_succ f (show M + 1 ≤ N by omega)]
    calc |(∑ n ∈ Finset.Ioc M N, c n) * f N
            + ∑ n ∈ Finset.Ico (M + 1) N, (∑ k ∈ Finset.Ioc M n, c k) * (f n - f (n + 1))|
        ≤ B * f N + B * (f (M + 1) - f N) := le_trans (abs_add_le _ _) (add_le_add h1 h2)
      _ = B * f (M + 1) := by ring

/-! ## A convergent correction series -/

/-- `∑_{p ≤ N} log p /(p (p-1))` is bounded uniformly in `N`. -/
theorem sum_log_div_mul_pred_bounded :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      ∑ p ∈ primesLE N, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) ≤ C := by
  classical
  set g : ℕ → ℝ := fun n => Real.log n / ((n : ℝ) * ((n : ℝ) - 1)) with hg
  have hg0 : ∀ n, 0 ≤ g n := by
    intro n
    match n with
    | 0 => simp [hg]
    | 1 => simp [hg]
    | (k + 2) =>
      have h1 : (0 : ℝ) ≤ Real.log (k + 2) := Real.log_nonneg (by linarith)
      simp only [hg]
      push_cast
      have h2 : (0 : ℝ) ≤ ((k : ℝ) + 2) * (((k : ℝ) + 2) - 1) := by
        nlinarith [Nat.cast_nonneg (α := ℝ) k]
      positivity
  have key : ∀ n : ℕ, 4 * (1 / (n : ℝ) ^ (3 / 2 : ℝ)) = 4 / ((n : ℝ) * Real.sqrt n) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · norm_num
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hn0, Real.rpow_one,
        Real.sqrt_eq_rpow]
      ring
  have hsum : Summable g := by
    have h4 : Summable (fun n : ℕ => 4 / ((n : ℝ) * Real.sqrt n)) := by
      have h : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (3 / 2 : ℝ)) := by
        rw [Real.summable_one_div_nat_rpow]; norm_num
      exact (h.mul_left 4).congr key
    refine Summable.of_nonneg_of_le hg0 ?_ h4
    intro n
    match n with
    | 0 => simp [hg]
    | 1 => norm_num [hg]
    | (k + 2) =>
      have hpos : (0 : ℝ) < (k : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) k]
      have hlog : Real.log ((k : ℝ) + 2) ≤ 2 * Real.sqrt ((k : ℝ) + 2) := log_le_two_sqrt hpos
      have hsq : Real.sqrt ((k : ℝ) + 2) * Real.sqrt ((k : ℝ) + 2) = (k : ℝ) + 2 :=
        Real.mul_self_sqrt (by linarith)
      simp only [hg]
      push_cast
      rw [div_le_div_iff₀ (by nlinarith) (by positivity)]
      have h1 : Real.log ((k : ℝ) + 2) * (((k : ℝ) + 2) * Real.sqrt ((k : ℝ) + 2))
          ≤ (2 * Real.sqrt ((k : ℝ) + 2)) * (((k : ℝ) + 2) * Real.sqrt ((k : ℝ) + 2)) :=
        mul_le_mul_of_nonneg_right hlog (by positivity)
      have h2 : (2 * Real.sqrt ((k : ℝ) + 2)) * (((k : ℝ) + 2) * Real.sqrt ((k : ℝ) + 2))
          = 2 * ((k : ℝ) + 2) * ((k : ℝ) + 2) := by nlinarith [hsq]
      nlinarith [h1, h2]
  refine ⟨∑' n, g n, tsum_nonneg hg0, fun N => ?_⟩
  calc ∑ p ∈ primesLE N, g p ≤ ∑ n ∈ Finset.range (N + 1), g n :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun n _ _ => hg0 n)
    _ ≤ ∑' n, g n := hsum.sum_le_tsum _ (fun n _ => hg0 n)

end FactorialHypergraph

/-! ## Axiom audit -/

#print axioms FactorialHypergraph.sum_Icc_divisors_swap
#print axioms FactorialHypergraph.sum_log_eq_sum_vonMangoldt_mul_floor
#print axioms FactorialHypergraph.sum_vonMangoldt_le
#print axioms FactorialHypergraph.sum_vonMangoldt_div_le
#print axioms FactorialHypergraph.sum_Ico_sub_succ
#print axioms FactorialHypergraph.sum_Ioc_by_parts
#print axioms FactorialHypergraph.abs_sum_mul_le_of_antitone
#print axioms FactorialHypergraph.sum_log_div_mul_pred_bounded
