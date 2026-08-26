/-
# Summation over the complementary factors

Layer 4 of the sieve estimate (A3).  Two sums over the complementary factor `m ≤ Y` are
needed:

* `sum_gMaj_div_le` :  `∑_{m ≤ Y} R(m) h(m)/m ≪ log(2Y)`  (unconditional, via the Mertens
  estimate `sum_inv_primes_chi5` of `FactorialHypergraph/MertensSecond.lean`),
* `sum_rootCount_div_sqrt_le` :  `∑_{m ≤ Y} R(m)/√m ≪ √Y log(2Y)`  (unconditional).

The first rests on the general, reusable comparison of a sum of a nonnegative multiplicative
function with its Euler product (`sum_smooth_le_prod`, `sum_Icc_le_prod_primesBelow`), the
second on the Dirichlet divisor swap (`sum_Icc_divisors_swap`) together with `R(m) ≤ τ(m)`.
-/
import FactorialHypergraph.A3Roots
import FactorialHypergraph.MertensAux

namespace FactorialHypergraph

open Finset

/-! ## A general Euler-product upper bound -/

open scoped Classical in
/-- **Euler-product majorisation, smooth form.**  For a nonnegative multiplicative `f` with
`f 1 = 1`, the sum of `f` over those `1 ≤ m ≤ N` all of whose prime factors lie in a finite
set `P` of primes is at most the product over `p ∈ P` of the truncated local sums
`∑_{e ≤ E} f(p^e)`, provided `N < 2^(E+1)` (so that every prime power dividing some `m ≤ N`
has exponent at most `E`). -/
theorem sum_smooth_le_prod (f : ℕ → ℝ) (hf0 : ∀ n, 0 ≤ f n) (hf1 : f 1 = 1)
    (hmul : ∀ m n : ℕ, Nat.Coprime m n → f (m * n) = f m * f n) (N E : ℕ)
    (hE : N < 2 ^ (E + 1)) :
    ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) →
      ∑ m ∈ (Finset.Icc 1 N).filter (fun m => ∀ q ∈ m.primeFactors, q ∈ P), f m
        ≤ ∏ p ∈ P, ∑ e ∈ Finset.range (E + 1), f (p ^ e) := by
  intro P
  induction P using Finset.induction_on with
  | empty =>
    intro _
    rw [Finset.prod_empty]
    have hsub : (Finset.Icc 1 N).filter (fun m => ∀ q ∈ m.primeFactors, q ∈ (∅ : Finset ℕ))
        ⊆ {1} := by
      intro m hm
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.notMem_empty] at hm
      have hpf : m.primeFactors = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro q hq; exact hm.2 q hq
      rcases Nat.primeFactors_eq_empty.mp hpf with h | h
      · omega
      · simp [h]
    calc ∑ m ∈ (Finset.Icc 1 N).filter (fun m => ∀ q ∈ m.primeFactors, q ∈ (∅ : Finset ℕ)), f m
        ≤ ∑ m ∈ ({1} : Finset ℕ), f m :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hf0 i)
      _ = 1 := by simp [hf1]
  | insert p P hpP ih =>
    intro hprime
    have hp : p.Prime := hprime p (Finset.mem_insert_self p P)
    have hP : ∀ q ∈ P, q.Prime := fun q hq => hprime q (Finset.mem_insert_of_mem hq)
    have ihP := ih hP
    set B := (Finset.Icc 1 N).filter (fun m => ∀ q ∈ m.primeFactors, q ∈ P) with hB
    set A := (Finset.Icc 1 N).filter (fun m => ∀ q ∈ m.primeFactors, q ∈ insert p P) with hA
    set ι : ℕ → ℕ × ℕ := fun m => (m.factorization p, m / p ^ m.factorization p) with hι
    set F : ℕ × ℕ → ℝ := fun x => f (p ^ x.1) * f x.2 with hF
    have hkey : ∀ m ∈ A, ι m ∈ Finset.range (E + 1) ×ˢ B ∧ F (ι m) = f m := by
      intro m hm
      simp only [hA, Finset.mem_filter, Finset.mem_Icc] at hm
      obtain ⟨⟨hm1, hmN⟩, hmp⟩ := hm
      have hm0 : m ≠ 0 := by omega
      set e := m.factorization p with he
      have hsplit : p ^ e * (m / p ^ e) = m := Nat.ordProj_mul_ordCompl_eq_self m p
      have hcop : Nat.Coprime (p ^ e) (m / p ^ e) :=
        Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hp hm0)
      have hfm : f m = f (p ^ e) * f (m / p ^ e) := by
        conv_lhs => rw [← hsplit]
        exact hmul _ _ hcop
      have hple : p ^ e ≤ m := Nat.ordProj_le p hm0
      have h2e : 2 ^ e ≤ p ^ e := Nat.pow_le_pow_left hp.two_le e
      have heE : e < E + 1 := by
        have h1 : (2 : ℕ) ^ e < 2 ^ (E + 1) :=
          lt_of_le_of_lt (le_trans h2e (le_trans hple hmN)) hE
        exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp h1
      have hmc0 : m / p ^ e ≠ 0 := (Nat.ordCompl_pos p hm0).ne'
      have hmcdvd : m / p ^ e ∣ m := Nat.ordCompl_dvd m p
      have hmcN : m / p ^ e ≤ N :=
        le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hmcdvd) hmN
      have hmcB : m / p ^ e ∈ B := by
        simp only [hB, Finset.mem_filter, Finset.mem_Icc]
        refine ⟨⟨Nat.one_le_iff_ne_zero.mpr hmc0, hmcN⟩, ?_⟩
        intro q hq
        have hqm : q ∈ m.primeFactors := Nat.primeFactors_mono hmcdvd hm0 hq
        rcases Finset.mem_insert.mp (hmp q hqm) with rfl | h
        · exact absurd (Nat.dvd_of_mem_primeFactors hq) (Nat.not_dvd_ordCompl hp hm0)
        · exact h
      exact ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr heE, hmcB⟩, hfm.symm⟩
    have hinj : Set.InjOn ι ↑A := by
      intro x _ y _ hxy
      have e1 : p ^ x.factorization p * (x / p ^ x.factorization p) = x :=
        Nat.ordProj_mul_ordCompl_eq_self x p
      have e2 : p ^ y.factorization p * (y / p ^ y.factorization p) = y :=
        Nat.ordProj_mul_ordCompl_eq_self y p
      simp only [hι, Prod.mk.injEq] at hxy
      obtain ⟨h1, h2⟩ := hxy
      rw [h1] at h2
      calc x = p ^ y.factorization p * (x / p ^ y.factorization p) := by rw [← h1]; exact e1.symm
        _ = p ^ y.factorization p * (y / p ^ y.factorization p) := by rw [h2]
        _ = y := e2
    calc ∑ m ∈ A, f m = ∑ m ∈ A, F (ι m) := Finset.sum_congr rfl (fun m hm => (hkey m hm).2.symm)
      _ = ∑ x ∈ A.image ι, F x := (Finset.sum_image hinj).symm
      _ ≤ ∑ x ∈ Finset.range (E + 1) ×ˢ B, F x := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun x _ _ => mul_nonneg (hf0 _) (hf0 _))
          intro x hx
          obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hx
          exact (hkey m hm).1
      _ = (∑ e ∈ Finset.range (E + 1), f (p ^ e)) * ∑ m ∈ B, f m := by
          rw [Finset.sum_product, Finset.sum_mul]
          refine Finset.sum_congr rfl (fun e _ => ?_)
          simp only [hF]
          rw [Finset.mul_sum]
      _ ≤ (∑ e ∈ Finset.range (E + 1), f (p ^ e))
            * ∏ q ∈ P, ∑ e ∈ Finset.range (E + 1), f (q ^ e) :=
          mul_le_mul_of_nonneg_left ihP (Finset.sum_nonneg (fun e _ => hf0 _))
      _ = ∏ q ∈ insert p P, ∑ e ∈ Finset.range (E + 1), f (q ^ e) := by
          rw [Finset.prod_insert hpP]

/-- **Euler-product majorisation.**  For a nonnegative multiplicative `f` with `f 1 = 1`,
the sum of `f` over `1 ≤ m ≤ N` is at most the product over the primes `p ≤ N` of the
truncated local sums `∑_{e ≤ E} f(p^e)`, provided `N < 2^(E+1)`. -/
theorem sum_Icc_le_prod_primesBelow (f : ℕ → ℝ) (hf0 : ∀ n, 0 ≤ f n) (hf1 : f 1 = 1)
    (hmul : ∀ m n : ℕ, Nat.Coprime m n → f (m * n) = f m * f n) (N E : ℕ)
    (hE : N < 2 ^ (E + 1)) :
    ∑ m ∈ Finset.Icc 1 N, f m
      ≤ ∏ p ∈ Nat.primesBelow (N + 1), ∑ e ∈ Finset.range (E + 1), f (p ^ e) := by
  classical
  have hprime : ∀ p ∈ Nat.primesBelow (N + 1), p.Prime :=
    fun p hp => (Nat.mem_primesBelow.mp hp).2
  have hfilter :
      (Finset.Icc 1 N).filter (fun m => ∀ q ∈ m.primeFactors, q ∈ Nat.primesBelow (N + 1))
        = Finset.Icc 1 N := by
    refine Finset.filter_true_of_mem ?_
    intro m hm q hq
    simp only [Finset.mem_Icc] at hm
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
    have hqm : q ≤ m := Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hq)
    exact Nat.mem_primesBelow.mpr ⟨by omega, hqp⟩
  have := sum_smooth_le_prod f hf0 hf1 hmul N E hE (Nat.primesBelow (N + 1)) hprime
  rwa [hfilter] at this

/-! ## The first sum -/

/-- The local sum of the majorant at a prime is at most `1 + gLoc p/(p-1)`. -/
theorem local_sum_gMaj_le {p : ℕ} (hp : p.Prime) (E : ℕ) :
    ∑ e ∈ Finset.range (E + 1), gMaj (p ^ e) / (p ^ e : ℝ) ≤ 1 + gLoc p / ((p : ℝ) - 1) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hppos : (0 : ℝ) < (p : ℝ) := by linarith
  rw [Finset.sum_range_succ']
  have h0 : gMaj (p ^ 0) / ((p : ℝ) ^ 0) = 1 := by simp [gMaj_one]
  rw [h0]
  set x : ℝ := 1 / (p : ℝ) with hxdef
  have hx0 : 0 < x := by positivity
  have hx1 : x < 1 := by rw [hxdef, div_lt_one hppos]; linarith
  have hterm : ∀ i ∈ Finset.range E,
      gMaj (p ^ (i + 1)) / ((p : ℝ) ^ (i + 1)) = gLoc p * x ^ (i + 1) := by
    intro i _
    rw [gMaj_prime_pow hp (by omega), hxdef, div_pow, one_pow, mul_one_div]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hgeo : ∑ i ∈ Finset.range E, x ^ (i + 1) ≤ 1 / ((p : ℝ) - 1) := by
    have hsum : ∑ i ∈ Finset.range E, x ^ (i + 1) = x * ∑ i ∈ Finset.range E, x ^ i := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring)
    have hg : ∑ i ∈ Finset.range E, x ^ i ≤ (1 - x)⁻¹ := by
      rw [geom_sum_eq (by linarith) E]
      have hrw : (x ^ E - 1) / (x - 1) = (1 - x ^ E) / (1 - x) := by
        rw [div_eq_div_iff (by linarith) (by linarith)]; ring
      rw [hrw, inv_eq_one_div, div_le_div_iff_of_pos_right (by linarith)]
      nlinarith [pow_nonneg hx0.le E]
    rw [hsum]
    calc x * ∑ i ∈ Finset.range E, x ^ i ≤ x * (1 - x)⁻¹ := by nlinarith
      _ = 1 / ((p : ℝ) - 1) := by rw [hxdef]; field_simp
  have hgl : 0 ≤ gLoc p := gLoc_nonneg hp
  have hfin : gLoc p * ∑ i ∈ Finset.range E, x ^ (i + 1) ≤ gLoc p * (1 / ((p : ℝ) - 1)) :=
    mul_le_mul_of_nonneg_left hgeo hgl
  rw [mul_one_div] at hfin
  linarith

/-- `gLoc p/(p-1) ≤ 2/p + 9/p²` for every prime `p` with `χ₅(p) = 1` (all such primes are
`≥ 11`). -/
theorem gLoc_div_le {p : ℕ} (hp : p.Prime) (hchi : p % 5 = 1 ∨ p % 5 = 4) :
    gLoc p / ((p : ℝ) - 1) ≤ 2 / (p : ℝ) + 9 / (p : ℝ) ^ 2 := by
  have h11 : (11 : ℕ) ≤ p := eleven_le_of_chi5_eq_one hp ((chi5_eq_one_iff p).mpr hchi)
  have hR : (11 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h11
  unfold gLoc
  rw [if_pos hchi, div_div, div_le_iff₀ (by nlinarith)]
  have e : (2 : ℝ) / (p : ℝ) + 9 / (p : ℝ) ^ 2 = (2 * (p : ℝ) + 9) / (p : ℝ) ^ 2 := by field_simp
  rw [e, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg ((p : ℝ) - 11)]

/-- `∑_{2 ≤ n ≤ N} 1/n² ≤ 1`. -/
theorem sum_inv_sq_Icc_le (N : ℕ) : ∑ n ∈ Finset.Icc 2 N, (1 : ℝ) / (n : ℝ) ^ 2 ≤ 1 := by
  have key : ∀ M : ℕ, 1 ≤ M → ∑ n ∈ Finset.Icc 2 M, (1 : ℝ) / (n : ℝ) ^ 2 ≤ 1 - 1 / (M : ℝ) := by
    intro M hM
    induction M with
    | zero => omega
    | succ k ih =>
      rcases Nat.lt_or_ge k 1 with hk | hk
      · interval_cases k
        norm_num
      · rw [Finset.sum_Icc_succ_top (by omega)]
        have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
        have hih := ih hk
        have hstep : (1 : ℝ) / ((k : ℝ) + 1) ^ 2 ≤ 1 / (k : ℝ) - 1 / ((k : ℝ) + 1) := by
          rw [div_sub_div _ _ (by linarith) (by linarith),
            div_le_div_iff₀ (by positivity) (by positivity)]
          ring_nf
          nlinarith
        push_cast
        push_cast at hih
        linarith
  rcases Nat.lt_or_ge N 1 with hN | hN
  · interval_cases N
    norm_num
  · have h2 := key N hN
    have hpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
    linarith

/-- `∑_{p ≤ N} 1/p² ≤ 1`. -/
theorem sum_inv_sq_primes_le (N : ℕ) :
    ∑ p ∈ Nat.primesBelow (N + 1), (1 : ℝ) / (p : ℝ) ^ 2 ≤ 1 := by
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) (sum_inv_sq_Icc_le N)
  · intro p hp
    rw [Nat.mem_primesBelow] at hp
    exact Finset.mem_Icc.mpr ⟨hp.2.two_le, by omega⟩
  · intro i _ _; positivity

open scoped Classical in
/-- The sum of the local weights over all primes `p ≤ N`, reduced to the reciprocal sum over
the primes with `χ₅(p) = 1`. -/
theorem sum_gLoc_div_le (N : ℕ) :
    ∑ p ∈ Nat.primesBelow (N + 1), gLoc p / ((p : ℝ) - 1)
      ≤ 2 * (∑ p ∈ Finset.Icc 1 N with (Nat.Prime p ∧ chi5 p = 1), (1 : ℝ) / p) + 10 := by
  have hterm : ∀ p ∈ Nat.primesBelow (N + 1), gLoc p / ((p : ℝ) - 1)
      ≤ (if p % 5 = 1 ∨ p % 5 = 4 then 2 / (p : ℝ) else 0) + 9 / (p : ℝ) ^ 2
        + (if p = 5 then (1 : ℝ) / 4 else 0) := by
    intro p hp
    rw [Nat.mem_primesBelow] at hp
    have hpp : p.Prime := hp.2
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    by_cases hchi : p % 5 = 1 ∨ p % 5 = 4
    · have hne5 : p ≠ 5 := by rintro rfl; omega
      rw [if_pos hchi, if_neg hne5]
      have := gLoc_div_le hpp hchi
      linarith
    · rw [if_neg hchi]
      by_cases h5 : p = 5
      · subst h5
        rw [if_pos rfl]
        have hg : gLoc 5 = 1 := by norm_num [gLoc]
        rw [hg]
        norm_num
      · rw [if_neg h5]
        have hg : gLoc p = 0 := by simp [gLoc, hchi, h5]
        rw [hg]
        have : (0 : ℝ) ≤ 9 / (p : ℝ) ^ 2 := by positivity
        simp only [zero_div]
        linarith
  calc ∑ p ∈ Nat.primesBelow (N + 1), gLoc p / ((p : ℝ) - 1)
      ≤ ∑ p ∈ Nat.primesBelow (N + 1), ((if p % 5 = 1 ∨ p % 5 = 4 then 2 / (p : ℝ) else 0)
          + 9 / (p : ℝ) ^ 2 + (if p = 5 then (1 : ℝ) / 4 else 0)) := Finset.sum_le_sum hterm
    _ = (∑ p ∈ Nat.primesBelow (N + 1), (if p % 5 = 1 ∨ p % 5 = 4 then 2 / (p : ℝ) else 0))
        + 9 * (∑ p ∈ Nat.primesBelow (N + 1), 1 / (p : ℝ) ^ 2)
        + (∑ p ∈ Nat.primesBelow (N + 1), (if p = 5 then (1 : ℝ) / 4 else 0)) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]
        congr 2
        exact Finset.sum_congr rfl (fun p _ => by ring)
    _ ≤ 2 * (∑ p ∈ Finset.Icc 1 N with (Nat.Prime p ∧ chi5 p = 1), (1 : ℝ) / p) + 10 := by
        have h1 : (∑ p ∈ Nat.primesBelow (N + 1),
              (if p % 5 = 1 ∨ p % 5 = 4 then 2 / (p : ℝ) else 0))
            = 2 * (∑ p ∈ Finset.Icc 1 N with (Nat.Prime p ∧ chi5 p = 1), (1 : ℝ) / p) := by
          rw [← Finset.sum_filter, Finset.mul_sum]
          refine Finset.sum_nbij' (fun p => p) (fun p => p) ?_ ?_ ?_ ?_ ?_
          · intro p hp
            simp only [Finset.mem_filter, Nat.mem_primesBelow] at hp
            simp only [Finset.mem_filter, Finset.mem_Icc]
            exact ⟨⟨hp.1.2.one_lt.le, by omega⟩, hp.1.2, (chi5_eq_one_iff p).mpr hp.2⟩
          · intro p hp
            simp only [Finset.mem_filter, Finset.mem_Icc] at hp
            simp only [Finset.mem_filter, Nat.mem_primesBelow]
            exact ⟨⟨by omega, hp.2.1⟩, (chi5_eq_one_iff p).mp hp.2.2⟩
          · intro p _; rfl
          · intro p _; rfl
          · intro p _; rw [mul_one_div]
        have h2 : (∑ p ∈ Nat.primesBelow (N + 1), (if p = 5 then (1 : ℝ) / 4 else 0)) ≤ 1 / 4 := by
          rw [Finset.sum_ite_eq' (Nat.primesBelow (N + 1)) 5 (fun _ => (1 : ℝ) / 4)]
          split_ifs <;> norm_num
        have h3 := sum_inv_sq_primes_le N
        rw [h1]
        linarith

open scoped Classical in
/-- **UNCONDITIONAL.**  (The Mertens/`χ₅` input it uses, `sum_inv_primes_chi5`, is proved
unconditionally in `FactorialHypergraph/MertensSecond.lean`; this docstring previously said
"CONDITIONAL", which was stale.)
`∑_{m ≤ N} R(m) h(m)/m ≪ 1 + log N`, uniformly in `N ≥ 1`. -/
theorem sum_gMaj_div_le :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      ∑ m ∈ Finset.Icc 1 N, gMaj m / (m : ℝ) ≤ C * (1 + Real.log N) := by
  obtain ⟨C, hC0, hCN⟩ := sum_inv_primes_chi5
  refine ⟨max (Real.exp (2 * C + 10)) 1, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro N hN
  set K := max (Real.exp (2 * C + 10)) 1 with hK
  have hK1 : (1 : ℝ) ≤ K := le_max_right _ _
  have hlogN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  rcases Nat.lt_or_ge N 3 with hsmall | hbig
  · interval_cases N
    · simp [gMaj_one]
      linarith
    · rw [show Finset.Icc 1 2 = {1, 2} from rfl, Finset.sum_insert (by norm_num),
        Finset.sum_singleton]
      have h2 : gMaj 2 = 0 := by
        rw [gMaj, Nat.Prime.primeFactors Nat.prime_two, Finset.prod_singleton]
        norm_num [gLoc]
      rw [h2, gMaj_one]
      norm_num
      have hl2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      nlinarith
  · have hf0 : ∀ n : ℕ, 0 ≤ gMaj n / (n : ℝ) :=
      fun n => div_nonneg (gMaj_nonneg n) (by positivity)
    have hf1 : gMaj 1 / ((1 : ℕ) : ℝ) = 1 := by simp [gMaj_one]
    have hmul : ∀ x y : ℕ, Nat.Coprime x y →
        gMaj (x * y) / ((x * y : ℕ) : ℝ) = (gMaj x / (x : ℝ)) * (gMaj y / (y : ℝ)) := by
      intro x y hxy
      rcases Nat.eq_zero_or_pos x with rfl | hx
      · have : y = 1 := by simpa [Nat.Coprime] using hxy
        subst this; simp
      rcases Nat.eq_zero_or_pos y with rfl | hy
      · have : x = 1 := by simpa [Nat.Coprime] using hxy
        subst this; simp
      rw [gMaj_mul_of_coprime hx.ne' hy.ne' hxy]
      push_cast
      field_simp
    have hE : N < 2 ^ (N + 1) :=
      lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) (by omega))
    have stepA := sum_Icc_le_prod_primesBelow (fun m => gMaj m / (m : ℝ)) hf0 hf1 hmul N N hE
    have stepB : ∏ p ∈ Nat.primesBelow (N + 1),
          ∑ e ∈ Finset.range (N + 1), gMaj (p ^ e) / ((p ^ e : ℕ) : ℝ)
        ≤ ∏ p ∈ Nat.primesBelow (N + 1), (1 + gLoc p / ((p : ℝ) - 1)) := by
      refine Finset.prod_le_prod (fun p _ => Finset.sum_nonneg (fun e _ => hf0 _)) ?_
      intro p hp
      have hpp : p.Prime := (Nat.mem_primesBelow.mp hp).2
      have hloc := local_sum_gMaj_le hpp N
      push_cast at hloc ⊢
      exact hloc
    have stepC : ∏ p ∈ Nat.primesBelow (N + 1), (1 + gLoc p / ((p : ℝ) - 1))
        ≤ Real.exp (∑ p ∈ Nat.primesBelow (N + 1), gLoc p / ((p : ℝ) - 1)) := by
      rw [Real.exp_sum]
      refine Finset.prod_le_prod ?_ ?_
      · intro p hp
        have hpp : p.Prime := (Nat.mem_primesBelow.mp hp).2
        have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
        have : 0 ≤ gLoc p / ((p : ℝ) - 1) := div_nonneg (gLoc_nonneg hpp) (by linarith)
        linarith
      · intro p _
        rw [add_comm]
        exact Real.add_one_le_exp _
    have stepD := sum_gLoc_div_le N
    have hCNN := hCN N hbig
    have hS : (∑ p ∈ Finset.Icc 1 N with (Nat.Prime p ∧ chi5 p = 1), (1 : ℝ) / p)
        ≤ Real.log (Real.log N) / 2 + C := by
      have := (abs_le.mp hCNN).2
      linarith
    have hfinal : Real.exp (∑ p ∈ Nat.primesBelow (N + 1), gLoc p / ((p : ℝ) - 1))
        ≤ Real.exp (2 * C + 10) * Real.log N := by
      have hle : (∑ p ∈ Nat.primesBelow (N + 1), gLoc p / ((p : ℝ) - 1))
          ≤ Real.log (Real.log N) + (2 * C + 10) := by linarith
      calc Real.exp (∑ p ∈ Nat.primesBelow (N + 1), gLoc p / ((p : ℝ) - 1))
          ≤ Real.exp (Real.log (Real.log N) + (2 * C + 10)) := Real.exp_le_exp.mpr hle
        _ = Real.log N * Real.exp (2 * C + 10) := by
            rw [Real.exp_add, Real.exp_log]
            have h3 : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hbig
            have := Real.log_lt_log (by norm_num : (0 : ℝ) < 1) (by linarith : (1 : ℝ) < (N : ℝ))
            simpa using this
        _ = Real.exp (2 * C + 10) * Real.log N := by ring
    have hKge : Real.exp (2 * C + 10) ≤ K := le_max_left _ _
    calc ∑ m ∈ Finset.Icc 1 N, gMaj m / (m : ℝ) ≤ _ := stepA
      _ ≤ _ := stepB
      _ ≤ _ := stepC
      _ ≤ Real.exp (2 * C + 10) * Real.log N := hfinal
      _ ≤ K * (1 + Real.log N) := by nlinarith

/-! ## The second sum -/

/-- `∑_{b ≤ B} 1/√b ≤ 2 √B`. -/
theorem sum_inv_sqrt_le (B : ℕ) :
    ∑ b ∈ Finset.Icc 1 B, 1 / Real.sqrt b ≤ 2 * Real.sqrt B := by
  induction B with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have h1 : Real.sqrt n ≤ Real.sqrt (n + 1) := Real.sqrt_le_sqrt (by norm_num)
    have h2 : (0 : ℝ) < Real.sqrt (n + 1) := Real.sqrt_pos.mpr (by positivity)
    have key : 1 / Real.sqrt ((n : ℝ) + 1) ≤ 2 * Real.sqrt ((n : ℝ) + 1) - 2 * Real.sqrt n := by
      rw [div_le_iff₀ h2]
      have e1 : Real.sqrt ((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1) = (n : ℝ) + 1 :=
        Real.mul_self_sqrt (by positivity)
      have e2 : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := Real.mul_self_sqrt (by positivity)
      nlinarith [Real.sqrt_nonneg ((n : ℝ) + 1), Real.sqrt_nonneg (n : ℝ)]
    push_cast
    push_cast at ih
    linarith

/-- `∑_{a ≤ N} 1/a ≤ 1 + log N`. -/
theorem sum_inv_le_one_add_log (N : ℕ) :
    ∑ a ∈ Finset.Icc 1 N, (1 : ℝ) / a ≤ 1 + Real.log N := by
  have h := harmonic_le_one_add_log N
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  simpa [one_div] using h

/-- **Unconditional.**  `∑_{m ≤ N} R(m)/√m ≤ 2 √N (1 + log N)`. -/
theorem sum_rootCount_div_sqrt_le (N : ℕ) :
    ∑ m ∈ Finset.Icc 1 N, (rootCount m : ℝ) / Real.sqrt m
      ≤ 2 * Real.sqrt N * (1 + Real.log N) := by
  classical
  set g : ℕ → ℕ → ℝ := fun d m => 1 / (Real.sqrt d * Real.sqrt m) with hg
  have hstep1 : ∀ n ∈ Finset.Icc 1 N, (rootCount n : ℝ) / Real.sqrt n
      ≤ ∑ d ∈ n.divisors, g d (n / d) := by
    intro n hn
    simp only [Finset.mem_Icc] at hn
    have hn0 : n ≠ 0 := by omega
    have hterm : ∀ d ∈ n.divisors, g d (n / d) = 1 / Real.sqrt n := by
      intro d hd
      rw [Nat.mem_divisors] at hd
      have hdd : (d : ℝ) * ((n / d : ℕ) : ℝ) = (n : ℝ) := by
        rw [← Nat.cast_mul, Nat.mul_div_cancel' hd.1]
      rw [hg]
      simp only
      rw [← Real.sqrt_mul (by positivity), hdd]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul,
      div_le_iff₀ (Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero hn0)),
      mul_one_div, div_mul_cancel₀]
    · exact_mod_cast rootCount_le_card_divisors hn0
    · exact (Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero hn0)).ne'
  calc ∑ m ∈ Finset.Icc 1 N, (rootCount m : ℝ) / Real.sqrt m
      ≤ ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors, g d (n / d) := Finset.sum_le_sum hstep1
    _ = ∑ d ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 (N / d), g d m := sum_Icc_divisors_swap N g
    _ ≤ ∑ d ∈ Finset.Icc 1 N, 2 * Real.sqrt N * (1 / (d : ℝ)) := by
        refine Finset.sum_le_sum ?_
        intro d hd
        simp only [Finset.mem_Icc] at hd
        have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd.1
        have hsd : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.mpr hd0
        have he : ∑ m ∈ Finset.Icc 1 (N / d), g d m
            = (1 / Real.sqrt d) * ∑ m ∈ Finset.Icc 1 (N / d), 1 / Real.sqrt m := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun m _ => ?_)
          rw [hg]; simp only; rw [one_div, one_div, one_div, mul_inv]
        have h1 : ∑ m ∈ Finset.Icc 1 (N / d), 1 / Real.sqrt m ≤ 2 * Real.sqrt ((N / d : ℕ)) :=
          sum_inv_sqrt_le (N / d)
        have h2 : Real.sqrt ((N / d : ℕ)) ≤ Real.sqrt N / Real.sqrt d := by
          rw [← Real.sqrt_div (by positivity)]
          exact Real.sqrt_le_sqrt Nat.cast_div_le
        have hdd : Real.sqrt (d : ℝ) ^ 2 = (d : ℝ) := Real.sq_sqrt hd0.le
        have hsdne : Real.sqrt (d : ℝ) ≠ 0 := ne_of_gt hsd
        rw [he]
        calc (1 / Real.sqrt d) * ∑ m ∈ Finset.Icc 1 (N / d), 1 / Real.sqrt m
            ≤ (1 / Real.sqrt d) * (2 * Real.sqrt ((N / d : ℕ))) := by
              exact mul_le_mul_of_nonneg_left h1 (by positivity)
          _ ≤ (1 / Real.sqrt d) * (2 * (Real.sqrt N / Real.sqrt d)) := by
              have : (0 : ℝ) ≤ 1 / Real.sqrt d := by positivity
              nlinarith
          _ = 2 * Real.sqrt N * (1 / (d : ℝ)) := by
              field_simp
              linear_combination (-Real.sqrt (N : ℝ)) * hdd
    _ = 2 * Real.sqrt N * ∑ d ∈ Finset.Icc 1 N, (1 : ℝ) / (d : ℝ) := by rw [Finset.mul_sum]
    _ ≤ 2 * Real.sqrt N * (1 + Real.log N) :=
        mul_le_mul_of_nonneg_left (sum_inv_le_one_add_log N) (by positivity)

end FactorialHypergraph
