/-
# Mertens' theorem for the quadratic character modulo 5

This file proves, **unconditionally and elementarily**, the character-twisted half of the
estimate `LargePrimeInputs.mertensRoots`, namely that

  `∑_{n ≤ N} χ₅(n) Λ(n) / n`   is bounded uniformly in `N`,

where `χ₅` is the quadratic Dirichlet character modulo `5` (`chi5` below) and `Λ` is the
von Mangoldt function.  The proof is the classical elementary (Shapiro-type) argument:

1. `chi5` is completely multiplicative (`chi5_mul`) and its partial sums are bounded
   (`abs_sum_chi5_le`, `abs_sum_chi5_Ioc_le`);
2. hence, by the discrete Dirichlet test `abs_sum_mul_le_of_antitone`, the partial sums
   `S N = ∑_{n ≤ N} χ₅(n)/n` satisfy `|S N - S M| ≤ 2/(M+1)` (`abs_S_sub_S_le`), and
   `T N = ∑_{n ≤ N} χ₅(n) log n / n` is bounded (`abs_T_le`);
3. `S N ≥ 1/12` for `N ≥ 5` (`S_ge`): an elementary and *explicit* substitute for the
   non-vanishing `L(1, χ₅) ≠ 0`.  Indeed `S 5 = 5/12` and the tail bound of step 2 controls
   the rest.  (Conceptually: the partial sums of `∑ χ₅(n)/n` group into blocks
   `1/(5j+1) - 1/(5j+2) - 1/(5j+3) + 1/(5j+4)`, positive by convexity of `1/x`.)
4. the divisor identity `T N = ∑_{d ≤ N} (χ₅(d)Λ(d)/d) · S(N/d)` (`T_eq_sum`), which after
   replacing `S(N/d)` by `S N` — with total error `O(ψ(N)/N) = O(1)` — gives
   `S N · U N = T N + O(1)`, whence `|U N| ≤ C` (`abs_U_le`).

No analytic input beyond Chebyshev's elementary bound `ψ(x) ≪ x` (mathlib) is used; in
particular neither the prime number theorem nor any Tauberian theorem, and no property of
Dirichlet `L`-functions.
-/
import FactorialHypergraph.MertensAux

namespace FactorialHypergraph

open Finset

/-! ## The character -/

/-- The quadratic Dirichlet character modulo `5`, as a function `ℕ → ℝ`:
`χ₅(n) = 1` if `n ≡ ±1 (mod 5)`, `-1` if `n ≡ ±2 (mod 5)`, and `0` if `5 ∣ n`. -/
def chi5 (n : ℕ) : ℝ :=
  if n % 5 = 1 ∨ n % 5 = 4 then 1 else if n % 5 = 2 ∨ n % 5 = 3 then -1 else 0

lemma chi5_congr {m n : ℕ} (h : m % 5 = n % 5) : chi5 m = chi5 n := by
  simp only [chi5, h]

lemma abs_chi5_le_one (n : ℕ) : |chi5 n| ≤ 1 := by
  simp only [chi5]
  split_ifs <;> simp

lemma chi5_nonneg_one_add (n : ℕ) : 0 ≤ 1 + chi5 n := by
  simp only [chi5]
  split_ifs <;> norm_num

lemma chi5_one_add_le_two (n : ℕ) : 1 + chi5 n ≤ 2 := by
  simp only [chi5]
  split_ifs <;> norm_num

/-- `χ₅` is completely multiplicative. -/
theorem chi5_mul (m n : ℕ) : chi5 (m * n) = chi5 m * chi5 n := by
  have e1 : chi5 m = chi5 (m % 5) := chi5_congr (by omega)
  have e2 : chi5 n = chi5 (n % 5) := chi5_congr (by omega)
  have e3 : chi5 (m * n) = chi5 ((m % 5) * (n % 5)) := chi5_congr (Nat.mul_mod m n 5)
  have hm : m % 5 < 5 := Nat.mod_lt _ (by norm_num)
  have hn : n % 5 < 5 := Nat.mod_lt _ (by norm_num)
  rw [e1, e2, e3]
  interval_cases h1 : (m % 5) <;> interval_cases h2 : (n % 5) <;> norm_num [chi5]

/-- The exact value of the partial sums of `χ₅`. -/
theorem sum_chi5_eq (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, chi5 n = if N % 5 = 1 then 1 else if N % 5 = 3 then -1 else 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    have h : chi5 (N + 1) = chi5 ((N + 1) % 5) := chi5_congr (by omega)
    have h5 : N % 5 = 0 ∨ N % 5 = 1 ∨ N % 5 = 2 ∨ N % 5 = 3 ∨ N % 5 = 4 := by omega
    rcases h5 with h5 | h5 | h5 | h5 | h5 <;>
      · have hs : (N + 1) % 5 = (N % 5 + 1) % 5 := by omega
        rw [h, hs, h5]
        norm_num [chi5]
        try omega

/-- The partial sums of `χ₅` are bounded by `1`. -/
theorem abs_sum_chi5_le (N : ℕ) : |∑ n ∈ Finset.Icc 1 N, chi5 n| ≤ 1 := by
  rw [sum_chi5_eq]
  split_ifs <;> norm_num

/-- The sums of `χ₅` over an interval are bounded by `2`. -/
theorem abs_sum_chi5_Ioc_le (M N : ℕ) : |∑ n ∈ Finset.Ioc M N, chi5 n| ≤ 2 := by
  rcases le_or_gt M N with h | h
  · have hcons := Finset.sum_Ioc_consecutive (fun n => chi5 n) (Nat.zero_le M) h
    have h1 : ∑ n ∈ Finset.Ioc M N, chi5 n
        = (∑ n ∈ Finset.Icc 1 N, chi5 n) - ∑ n ∈ Finset.Icc 1 M, chi5 n := by
      have e : ∀ k : ℕ, Finset.Ioc 0 k = Finset.Icc 1 k := fun _ => rfl
      rw [e, e] at hcons
      linarith [hcons]
    rw [h1]
    calc |(∑ n ∈ Finset.Icc 1 N, chi5 n) - ∑ n ∈ Finset.Icc 1 M, chi5 n|
        ≤ |∑ n ∈ Finset.Icc 1 N, chi5 n| + |∑ n ∈ Finset.Icc 1 M, chi5 n| := abs_sub _ _
      _ ≤ 2 := by linarith [abs_sum_chi5_le N, abs_sum_chi5_le M]
  · rw [Finset.Ioc_eq_empty (by omega)]
    norm_num

/-! ## The three partial sums -/

/-- `S N = ∑_{n ≤ N} χ₅(n)/n`. -/
noncomputable def S (N : ℕ) : ℝ := ∑ n ∈ Finset.Icc 1 N, chi5 n / n

/-- `T N = ∑_{n ≤ N} χ₅(n) log n / n`. -/
noncomputable def T (N : ℕ) : ℝ := ∑ n ∈ Finset.Icc 1 N, chi5 n * Real.log n / n

/-- `U N = ∑_{n ≤ N} χ₅(n) Λ(n) / n`. -/
noncomputable def U (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, chi5 n * ArithmeticFunction.vonMangoldt n / n

/-- Tail estimate for `S`, by the Dirichlet test. -/
theorem abs_S_sub_S_le {M N : ℕ} (hM : 1 ≤ M) (hMN : M ≤ N) :
    |S N - S M| ≤ 2 / (M + 1) := by
  have hIcc : ∀ k : ℕ, Finset.Icc 1 k = Finset.Ioc 0 k := fun _ => rfl
  have hsplit : S N - S M = ∑ n ∈ Finset.Ioc M N, chi5 n * (1 / (n : ℝ)) := by
    rw [S, S, hIcc N, hIcc M, ← Finset.sum_Ioc_consecutive (fun n => chi5 n / (n : ℝ))
      (Nat.zero_le M) hMN]
    simp only [mul_one_div]
    ring
  rw [hsplit]
  have h := abs_sum_mul_le_of_antitone (c := chi5) (f := fun n : ℕ => 1 / (n : ℝ))
    (B := 2) (M := M) (N := N) (fun m => abs_sum_chi5_Ioc_le M m)
    (fun n _ => by positivity)
    (fun n hn => by
      have hn0 : (0 : ℝ) < n := by
        have : 0 < n := by omega
        exact_mod_cast this
      push_cast
      rw [div_le_div_iff₀ (by linarith) hn0]
      linarith)
  simpa only [div_eq_mul_inv, one_mul, Nat.cast_add, Nat.cast_one] using h

/-- `T` is bounded. -/
theorem abs_T_le (N : ℕ) : |T N| ≤ 2 := by
  have hIcc : ∀ k : ℕ, Finset.Icc 1 k = Finset.Ioc 0 k := fun _ => rfl
  have hanti : ∀ n : ℕ, 2 < n → Real.log ((n : ℝ) + 1) / ((n : ℝ) + 1) ≤ Real.log n / n := by
    intro n hn
    have h3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have he : Real.exp 1 ≤ (n : ℝ) :=
      le_trans (le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))) h3
    exact Real.log_div_self_antitoneOn (Set.mem_setOf.mpr he)
      (Set.mem_setOf.mpr (by linarith)) (by linarith)
  have hlog3 : Real.log 3 ≤ 1.4 := by
    have h1 : Real.log 3 ≤ Real.log 4 := Real.log_le_log (by norm_num) (by norm_num)
    have h2 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    nlinarith [Real.log_two_lt_d9]
  rcases le_or_gt N 2 with hN | hN
  · interval_cases N <;> simp [T, chi5, Finset.sum_Icc_succ_top] ;
      rw [abs_le] ; constructor <;> nlinarith [Real.log_two_lt_d9, Real.log_two_gt_d9]
  · have hsplit : T N = (∑ n ∈ Finset.Icc 1 2, chi5 n * Real.log n / n)
        + ∑ n ∈ Finset.Ioc 2 N, chi5 n * (Real.log n / n) := by
      rw [T, hIcc N, hIcc 2, ← Finset.sum_Ioc_consecutive (fun n => chi5 n * Real.log n / n)
        (Nat.zero_le 2) (le_of_lt hN)]
      simp only [mul_div_assoc]
    have h1 : |∑ n ∈ Finset.Icc 1 2, chi5 n * Real.log n / n| ≤ 1 := by
      norm_num [chi5, Finset.sum_Icc_succ_top, abs_le]
      constructor <;> nlinarith [Real.log_two_lt_d9, Real.log_two_gt_d9]
    have h2 : |∑ n ∈ Finset.Ioc 2 N, chi5 n * (Real.log n / n)| ≤ 2 * (Real.log 3 / 3) := by
      have h := abs_sum_mul_le_of_antitone (c := chi5) (f := fun n : ℕ => Real.log n / n)
        (B := 2) (M := 2) (N := N) (fun m => abs_sum_chi5_Ioc_le 2 m)
        (fun n _ => by positivity)
        (fun n hn => by push_cast; exact hanti n hn)
      simpa using h
    have hfin : |T N| ≤ 1 + 2 * (Real.log 3 / 3) := by
      rw [hsplit]; exact le_trans (abs_add_le _ _) (add_le_add h1 h2)
    linarith

/-- **Explicit positivity of `L(1, χ₅)` at the level of partial sums.**
For `N ≥ 5` one has `S N ≥ 1/12`; here `S 5 = 5/12` and the tail is at most `1/3`. -/
theorem S_ge {N : ℕ} (hN : 5 ≤ N) : (1 : ℝ) / 12 ≤ S N := by
  have h5 : S 5 = 5 / 12 := by norm_num [S, chi5, Finset.sum_Icc_succ_top]
  have h := abs_S_sub_S_le (M := 5) (N := N) (by norm_num) hN
  rw [h5] at h
  have := abs_le.mp h
  norm_num at this ⊢
  linarith [this.1]

/-! ## The Shapiro argument -/

/-- The divisor identity `T N = ∑_{d ≤ N} (χ₅(d) Λ(d)/d) · S(N/d)`. -/
theorem T_eq_sum (N : ℕ) :
    T N = ∑ d ∈ Finset.Icc 1 N,
      (chi5 d * ArithmeticFunction.vonMangoldt d / d) * S (N / d) := by
  have h := sum_Icc_divisors_swap N
    (fun d m => (chi5 d * ArithmeticFunction.vonMangoldt d / d) * (chi5 m / m))
  rw [show (∑ d ∈ Finset.Icc 1 N,
      (chi5 d * ArithmeticFunction.vonMangoldt d / d) * S (N / d))
      = ∑ d ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 (N / d),
        (chi5 d * ArithmeticFunction.vonMangoldt d / d) * (chi5 m / m) from
    Finset.sum_congr rfl fun d _ => by rw [S, Finset.mul_sum], ← h, T]
  refine Finset.sum_congr rfl fun n hn => ?_
  simp only [Finset.mem_Icc] at hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.1
  have hterm : ∀ d ∈ n.divisors,
      (chi5 d * ArithmeticFunction.vonMangoldt d / d) * (chi5 (n / d) / ((n / d : ℕ) : ℝ))
        = (chi5 n / n) * ArithmeticFunction.vonMangoldt d := by
    intro d hd
    rw [Nat.mem_divisors] at hd
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd.1 (by omega)
    have hmul : d * (n / d) = n := Nat.mul_div_cancel' hd.1
    have hchi : chi5 d * chi5 (n / d) = chi5 n := by rw [← chi5_mul, hmul]
    have hcast : (d : ℝ) * ((n / d : ℕ) : ℝ) = (n : ℝ) := by
      exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) hmul
    have hd0' : (0 : ℝ) < d := by exact_mod_cast hd0
    have hnd0 : (0 : ℝ) < ((n / d : ℕ) : ℝ) := by
      have : 0 < n / d := Nat.div_pos (Nat.le_of_dvd (by omega) hd.1) hd0
      exact_mod_cast this
    field_simp
    linear_combination (ArithmeticFunction.vonMangoldt d * (n : ℝ)) * hchi
      - (ArithmeticFunction.vonMangoldt d * chi5 n) * hcast
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ArithmeticFunction.vonMangoldt_sum]
  ring

/-- **Mertens' theorem for `χ₅`, von Mangoldt form.**  The twisted sums
`∑_{n ≤ N} χ₅(n) Λ(n)/n` are bounded uniformly in `N`. -/
theorem abs_U_le (N : ℕ) : |U N| ≤ 12 * (2 + 2 * (Real.log 4 + 4)) := by
  have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hlog4' : Real.log 4 ≤ 1.4 := by
    have h2 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    nlinarith [Real.log_two_lt_d9]
  rcases lt_or_ge N 5 with hN | hN
  · -- small `N`: a crude bound suffices
    have h0 : |U N| ≤ ∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n / n := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun n hn => ?_)
      simp only [Finset.mem_Icc] at hn
      have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.1
      rw [abs_div, abs_mul, abs_of_nonneg hΛ, abs_of_nonneg hn0.le]
      gcongr
      nlinarith [abs_chi5_le_one n]
    rcases Nat.eq_zero_or_pos N with rfl | hN1
    · simp only [U, Nat.Icc_eq_range']
      norm_num
      positivity
    · have hm := sum_vonMangoldt_div_le hN1
      have hlogN : Real.log N ≤ Real.log 4 := by
        refine Real.log_le_log (by exact_mod_cast hN1) ?_
        have : (N : ℝ) ≤ 4 := by exact_mod_cast Nat.lt_succ_iff.mp hN
        exact this
      linarith
  · have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hkey : T N - S N * U N
        = ∑ d ∈ Finset.Icc 1 N,
            (chi5 d * ArithmeticFunction.vonMangoldt d / d) * (S (N / d) - S N) := by
      rw [T_eq_sum N, U, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun d _ => by ring
    have hE : |∑ d ∈ Finset.Icc 1 N,
        (chi5 d * ArithmeticFunction.vonMangoldt d / d) * (S (N / d) - S N)|
        ≤ 2 * (Real.log 4 + 4) := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      have hterm : ∀ d ∈ Finset.Icc 1 N,
          |(chi5 d * ArithmeticFunction.vonMangoldt d / d) * (S (N / d) - S N)|
            ≤ 2 * ArithmeticFunction.vonMangoldt d / N := by
        intro d hd
        simp only [Finset.mem_Icc] at hd
        have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
        have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt d := ArithmeticFunction.vonMangoldt_nonneg
        have hND : 1 ≤ N / d := (Nat.one_le_div_iff (by omega)).mpr hd.2
        have h1 : |S (N / d) - S N| ≤ 2 / ((N / d : ℕ) + 1) := by
          rw [abs_sub_comm]
          exact abs_S_sub_S_le hND (Nat.div_le_self _ _)
        have hlt : (N : ℝ) < (d : ℝ) * (((N / d : ℕ) : ℝ) + 1) := by
          have e1 := Nat.div_add_mod N d
          have e2 : N % d < d := Nat.mod_lt _ (by omega)
          have e3 : d * (N / d + 1) = d * (N / d) + d := by ring
          have : N < d * (N / d + 1) := by omega
          exact_mod_cast this
        have h2 : (2 : ℝ) / (((N / d : ℕ) : ℝ) + 1) ≤ 2 * d / N := by
          rw [div_le_div_iff₀ (by positivity) hN0]
          nlinarith
        have habs : |chi5 d * ArithmeticFunction.vonMangoldt d / d|
            ≤ ArithmeticFunction.vonMangoldt d / d := by
          rw [abs_div, abs_mul, abs_of_nonneg hΛ, abs_of_nonneg hd0.le]
          gcongr
          nlinarith [abs_chi5_le_one d]
        calc |(chi5 d * ArithmeticFunction.vonMangoldt d / d) * (S (N / d) - S N)|
            = |chi5 d * ArithmeticFunction.vonMangoldt d / d| * |S (N / d) - S N| := abs_mul _ _
          _ ≤ (ArithmeticFunction.vonMangoldt d / d) * (2 * d / N) :=
              mul_le_mul habs (le_trans h1 h2) (abs_nonneg _) (by positivity)
          _ = 2 * ArithmeticFunction.vonMangoldt d / N := by field_simp
      refine le_trans (Finset.sum_le_sum hterm) ?_
      have hrw : ∑ d ∈ Finset.Icc 1 N, 2 * ArithmeticFunction.vonMangoldt d / N
          = (2 / N) * ∑ d ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt d := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun d _ => by ring
      rw [hrw]
      calc (2 / (N : ℝ)) * ∑ d ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt d
          ≤ (2 / (N : ℝ)) * ((Real.log 4 + 4) * N) :=
            mul_le_mul_of_nonneg_left (sum_vonMangoldt_le N) (by positivity)
        _ = 2 * (Real.log 4 + 4) := by field_simp
    have hSU : |S N * U N| ≤ 2 + 2 * (Real.log 4 + 4) := by
      have he : S N * U N = T N - (T N - S N * U N) := by ring
      rw [he]
      calc |T N - (T N - S N * U N)| ≤ |T N| + |T N - S N * U N| := abs_sub _ _
        _ ≤ 2 + 2 * (Real.log 4 + 4) := by rw [hkey]; exact add_le_add (abs_T_le N) hE
    have hS := S_ge hN
    have hSpos : (0 : ℝ) < S N := by linarith
    have hprod : S N * |U N| = |S N * U N| := by rw [abs_mul, abs_of_pos hSpos]
    nlinarith [abs_nonneg (U N), hSU, hprod, hS]

/-- The conclusion in the form used later. -/
theorem chi5_vonMangoldt_sum_bounded :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      |∑ n ∈ Finset.Icc 1 N, chi5 n * ArithmeticFunction.vonMangoldt n / n| ≤ C :=
  ⟨12 * (2 + 2 * (Real.log 4 + 4)), by
    have h : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    nlinarith, fun N => abs_U_le N⟩

end FactorialHypergraph

/-! ## Axiom audit -/

#print axioms FactorialHypergraph.chi5_mul
#print axioms FactorialHypergraph.sum_chi5_eq
#print axioms FactorialHypergraph.abs_sum_chi5_le
#print axioms FactorialHypergraph.abs_sum_chi5_Ioc_le
#print axioms FactorialHypergraph.abs_S_sub_S_le
#print axioms FactorialHypergraph.abs_T_le
#print axioms FactorialHypergraph.S_ge
#print axioms FactorialHypergraph.T_eq_sum
#print axioms FactorialHypergraph.abs_U_le
#print axioms FactorialHypergraph.chi5_vonMangoldt_sum_bounded
