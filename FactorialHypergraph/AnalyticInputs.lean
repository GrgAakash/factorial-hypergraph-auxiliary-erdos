/-
# Analytic inputs

This file isolates **every** analytic number-theoretic ingredient of the manuscript that
is *not* available in mathlib.  Following the request, these are packaged as fields of an
explicit structure `AnalyticInputs`; **no global axioms are introduced**.  Any theorem
depending on them takes `h : AnalyticInputs` as an explicit hypothesis and is labelled
CONDITIONAL.

The three audited inputs are:

1. `primeSupply` — the supply of at least `2L` primes in `(L, 20 L log L]`
   (Proposition 2.5 and the corresponding step of Proposition 5.1; the manuscript
   invokes the prime number theorem).
2. `largePrimeFactor` — Lemma 3.2 of the manuscript: for at least `N/5` of the indices
   `i ≤ N` the quadratic `f(i) = i² + 3i + 1` has a prime factor exceeding
   `(1/40)·i·log i`.  (Manuscript proof: Mertens' estimates, Siegel–Walfisz for the fixed
   modulus 5, and a product argument; the manuscript's threshold is `(1/8)·i·log i`, see
   the docstring of `largePrimeFactorSet` for the explicitly recorded deviation.)  This
   field is **no longer conditional**: it is proved in Lean, unconditionally, by
   `largePrimeFactor_unconditional` in `FactorialHypergraph/A2Assembly.lean`.
3. `smallCofactorSieve` — Lemma 4.2 of the manuscript: a uniform upper-bound sieve
   estimate for the number of `i ≤ L` for which `f(i) = m q` with `q > L` prime and a
   small complementary factor `m ≤ L^α`.  (Manuscript proof: the fundamental lemma of
   sieve theory.)

Of these, (A1) and (A2) are by now proved in Lean unconditionally; only (A3) remains an
assumption, and it is itself derived from a single conventional sieve theorem
(`UpperBoundSieveDimOne`, `FactorialHypergraph/A3Sieve.lean`).  Everything else in this
development is proved unconditionally.
-/
import FactorialHypergraph.Definitions
import FactorialHypergraph.Estimates

namespace FactorialHypergraph

open Finset

/-! ## Finite sets occurring in the analytic statements -/

/-- The primes in the interval `(a, b]`. -/
def primesIn (a b : ℕ) : Finset ℕ := (Finset.Ioc a b).filter Nat.Prime

lemma mem_primesIn {a b q : ℕ} : q ∈ primesIn a b ↔ (a < q ∧ q ≤ b) ∧ q.Prime := by
  simp [primesIn, Finset.mem_filter, Finset.mem_Ioc, and_assoc]

open scoped Classical in
/-- `{ i ≤ N : P⁺(f(i)) > i·log i / c }`, the set counted in Lemma 3.2, with the threshold
constant `c` left as a parameter.  The manuscript states Lemma 3.2 with `c = 8`. -/
noncomputable def largePrimeFactorSetC (c : ℝ) (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter
    (fun i => ∃ q : ℕ, q.Prime ∧ q ∣ fq i ∧ (i : ℝ) * Real.log i / c < q)

open scoped Classical in
/-- `{ i ≤ N : P⁺(f(i)) > (1/40)·i·log i }`, the set counted in the version of Lemma 3.2
used in this development.

**Deviation from the manuscript, stated explicitly.**  The manuscript uses the threshold
`(1/8) i log i`; here the weaker threshold `(1/40) i log i` is used, i.e.
`largePrimeFactorSetC 40`.  The reason is quantitative and is recorded in
`FactorialHypergraph/LargePrimeFactors.lean`: with the threshold constant `c`, the discard step
of the proof of Lemma 3.2 removes `2κ/c · N` indices, where `κ` is the constant in an upper
bound `π(y) ≤ κ y / log y`.  With `c = 8` one needs `κ ≤ 1.08`, which is beyond what
mathlib supplies: its Chebyshev input is `θ(x) ≤ (log 4) x`, and the passage to `π` gives
only `π(y) ≤ (log 4 + ε) y / log y`, so no `κ` below `1.3863` is available here.  With
`c = 40` the safe explicit value `κ = 2` (`primeCountingUpper_two`) suffices
(`2·2/40 = 0.1 ≤ 0.27`), and Lemma 3.2 becomes **unconditional**
(`largePrimeFactor_fortieth`).  The manuscript's own statement, with `c = 8`, is retained
and proved (conditionally on the sharper `π`-bound) as `largePrimeFactor_eighth`.

The weakening is harmless downstream: the only property of the threshold used in
Proposition 5.1 is that `i log i / c > L` when `L/10 ≤ i ≤ L` and `L` is large, which holds
for every fixed `c`.  Consequently every final statement of the development is unchanged. -/
noncomputable def largePrimeFactorSet (N : ℕ) : Finset ℕ := largePrimeFactorSetC 40 N

open scoped Classical in
/-- `E_α(L) = #{ i ≤ L : f(i) = m q with q > L prime and m ≤ L^α }`, the set counted in
Lemma 4.2. -/
noncomputable def smallCofactorSet (α : ℝ) (L : ℕ) : Finset ℕ :=
  (Finset.Icc 1 L).filter
    (fun i => ∃ m q : ℕ, q.Prime ∧ fq i = m * q ∧ (m : ℝ) ≤ (L : ℝ) ^ α ∧ L < q)

open scoped Classical in
lemma mem_largePrimeFactorSetC {c : ℝ} {N i : ℕ} :
    i ∈ largePrimeFactorSetC c N ↔
      (1 ≤ i ∧ i ≤ N) ∧ ∃ q : ℕ, q.Prime ∧ q ∣ fq i ∧ (i : ℝ) * Real.log i / c < q := by
  simp [largePrimeFactorSetC, Finset.mem_filter, Finset.mem_Icc, and_assoc]

open scoped Classical in
lemma mem_largePrimeFactorSet {N i : ℕ} :
    i ∈ largePrimeFactorSet N ↔
      (1 ≤ i ∧ i ≤ N) ∧ ∃ q : ℕ, q.Prime ∧ q ∣ fq i ∧ (i : ℝ) * Real.log i / 40 < q :=
  mem_largePrimeFactorSetC

/-- Raising the threshold constant enlarges the set: a prime factor exceeding
`i log i / c` also exceeds `i log i / c'` when `c ≤ c'`. -/
lemma largePrimeFactorSetC_subset {c c' : ℝ} (hc : 0 < c) (hcc : c ≤ c') (N : ℕ) :
    largePrimeFactorSetC c N ⊆ largePrimeFactorSetC c' N := by
  classical
  intro i hi
  rw [mem_largePrimeFactorSetC] at hi ⊢
  obtain ⟨⟨hi1, hiN⟩, q, hqp, hqd, hq⟩ := hi
  refine ⟨⟨hi1, hiN⟩, q, hqp, hqd, lt_of_le_of_lt ?_ hq⟩
  have hlog : (0 : ℝ) ≤ Real.log i := Real.log_nonneg (by exact_mod_cast hi1)
  have hi0 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
  gcongr

/-- The manuscript's threshold implies the one used here. -/
lemma largePrimeFactorSet8_subset (N : ℕ) :
    largePrimeFactorSetC 8 N ⊆ largePrimeFactorSet N :=
  largePrimeFactorSetC_subset (by norm_num) (by norm_num) N

open scoped Classical in
lemma mem_smallCofactorSet {α : ℝ} {L i : ℕ} :
    i ∈ smallCofactorSet α L ↔
      (1 ≤ i ∧ i ≤ L) ∧
        ∃ m q : ℕ, q.Prime ∧ fq i = m * q ∧ (m : ℝ) ≤ (L : ℝ) ^ α ∧ L < q := by
  simp [smallCofactorSet, Finset.mem_filter, Finset.mem_Icc, and_assoc]

/-! ## The structure of analytic inputs -/

/-- The analytic number-theoretic inputs of the manuscript which are not available in
mathlib.  Each field is stated exactly as the corresponding manuscript statement. -/
structure AnalyticInputs : Prop where
  /-- **(A1) Prime supply.**  For all large `L` there are more than `2L` primes in
  `(L, 20 L log L]`.  (Manuscript: prime number theorem.) -/
  primeSupply : ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L →
    2 * L ≤ (primesIn L ⌈20 * (L : ℝ) * Real.log L⌉₊).card
  /-- **(A2) Large prime factors of the quadratic** (Lemma 3.2, with the threshold constant
  `40`; proved unconditionally by `largePrimeFactor_fortieth`, see `FactorialHypergraph/A2Assembly.lean`.
  The manuscript's own constant `8` is `largePrimeFactor_eighth`, which stays conditional). -/
  largePrimeFactor : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    (N : ℝ) / 5 ≤ ((largePrimeFactorSet N).card : ℝ)
  /-- **(A3) Uniform small-complementary-factor sieve estimate** (Lemma 4.2). -/
  smallCofactorSieve : ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∃ L₀ : ℕ, ∀ α : ℝ, 0 < α → α ≤ 1 / 2 →
    ∀ L : ℕ, L₀ ≤ L →
      ((smallCofactorSet α L).card : ℝ)
        ≤ C₀ * (α * L + (L : ℝ) / Real.log L + (L : ℝ) ^ ((1 + α) / 2) * (Real.log L) ^ 2)

/-! ## The form of the sieve estimate that is actually used

Proposition 5.1 of the manuscript only uses the following consequence of (A3), obtained
by choosing `α₀ = 1/(1000 C₀)` and letting `L` be large. -/

/-- CONDITIONAL (on `AnalyticInputs`).  The corollary of the sieve estimate used in the
construction of the low-weight cover: for some fixed `α₀ ∈ (0, 1/2]` the exceptional set
`E_{α₀}(L)` has at most `L/500` elements once `L` is large. -/
theorem sieve_corollary (h : AnalyticInputs) :
    ∃ α₀ : ℝ, 0 < α₀ ∧ α₀ ≤ 1 / 2 ∧ ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L →
      ((smallCofactorSet α₀ L).card : ℝ) ≤ (L : ℝ) / 500 := by
  obtain ⟨C₀, hC₀, L₀, hL₀⟩ := h.smallCofactorSieve
  have hC₀pos : (0 : ℝ) < C₀ := lt_of_lt_of_le zero_lt_one hC₀
  have hhalf : 1 / (1000 * C₀) ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num)
    nlinarith
  refine ⟨1 / (1000 * C₀), by positivity, hhalf, ?_⟩
  classical
  set α₀ : ℝ := 1 / (1000 * C₀) with hα₀
  have hα₀pos : 0 < α₀ := by rw [hα₀]; positivity
  have hα₀small : α₀ ≤ 1 / 1000 := by
    rw [hα₀]
    apply one_div_le_one_div_of_le (by norm_num)
    nlinarith
  refine ⟨max L₀ (max ⌈Real.exp (2000 * C₀)⌉₊ ⌈(200000 * C₀) ^ (4 : ℕ)⌉₊), ?_⟩
  intro L hL
  have hLL₀ : L₀ ≤ L := le_trans (le_max_left _ _) hL
  have hL1 : ⌈Real.exp (2000 * C₀)⌉₊ ≤ L :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL
  have hL2 : ⌈(200000 * C₀) ^ (4 : ℕ)⌉₊ ≤ L :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hL
  -- basic size facts about `L`
  have hexp : Real.exp (2000 * C₀) ≤ (L : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hL1)
  have hpow : ((200000 * C₀) ^ (4 : ℕ) : ℝ) ≤ (L : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hL2)
  have hLpos : (0 : ℝ) < (L : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hexp
  have hlogL : 2000 * C₀ ≤ Real.log L := by
    have := Real.log_le_log (Real.exp_pos _) hexp
    rwa [Real.log_exp] at this
  have hlogpos : (0 : ℝ) < Real.log L := lt_of_lt_of_le (by positivity) hlogL
  have hmain := hL₀ α₀ hα₀pos (by linarith) L hLL₀
  -- estimate the three terms
  have hterm1 : C₀ * (α₀ * L) = (L : ℝ) / 1000 := by
    rw [hα₀]; field_simp
  have hterm2 : C₀ * ((L : ℝ) / Real.log L) ≤ (L : ℝ) / 2000 := by
    have hrw : C₀ * ((L : ℝ) / Real.log L) = (C₀ * L) / Real.log L := by ring
    rw [hrw, div_le_iff₀ hlogpos]
    nlinarith
  have hterm3 : C₀ * ((L : ℝ) ^ ((1 + α₀) / 2) * (Real.log L) ^ 2) ≤ (L : ℝ) / 2000 := by
    -- `log L ≤ 10 L^{1/10}` and `L^{(1+α₀)/2} ≤ L^{0.51}`
    have hL1' : (1 : ℝ) ≤ (L : ℝ) := le_trans (Real.one_le_exp (by positivity)) hexp
    have hlogbound : Real.log L ≤ 10 * (L : ℝ) ^ (1 / 10 : ℝ) := by
      have := Real.log_le_rpow_div (le_of_lt hLpos) (by norm_num : (0:ℝ) < 1/10)
      calc Real.log L ≤ (L : ℝ) ^ (1/10 : ℝ) / (1/10 : ℝ) := this
        _ = 10 * (L : ℝ) ^ (1/10 : ℝ) := by ring
    have hexpmono : (L : ℝ) ^ ((1 + α₀) / 2) ≤ (L : ℝ) ^ (51 / 100 : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le hL1'
      linarith
    have hsq : (Real.log L) ^ 2 ≤ 100 * (L : ℝ) ^ (1 / 5 : ℝ) := by
      have h0 : (0 : ℝ) ≤ Real.log L := le_of_lt hlogpos
      have h1 : (Real.log L) ^ 2 ≤ (10 * (L : ℝ) ^ (1/10 : ℝ)) ^ 2 := by
        apply pow_le_pow_left₀ h0 hlogbound
      have hpow2 : ((L : ℝ) ^ (1/10 : ℝ)) ^ (2 : ℕ) = (L : ℝ) ^ (1/5 : ℝ) := by
        rw [← Real.rpow_natCast ((L : ℝ) ^ (1/10 : ℝ)) 2, ← Real.rpow_mul (le_of_lt hLpos)]
        norm_num
      have h2 : (10 * (L : ℝ) ^ (1/10 : ℝ)) ^ 2 = 100 * (L : ℝ) ^ (1/5 : ℝ) := by
        rw [mul_pow, hpow2]; norm_num
      linarith [h1, h2]
    have hprod : (L : ℝ) ^ ((1 + α₀) / 2) * (Real.log L) ^ 2
        ≤ 100 * (L : ℝ) ^ (71 / 100 : ℝ) := by
      have hnn1 : (0 : ℝ) ≤ (L : ℝ) ^ ((1 + α₀) / 2) := le_of_lt (Real.rpow_pos_of_pos hLpos _)
      have hnn2 : (0 : ℝ) ≤ (Real.log L) ^ 2 := sq_nonneg _
      have step : (L : ℝ) ^ ((1 + α₀) / 2) * (Real.log L) ^ 2
          ≤ (L : ℝ) ^ (51/100 : ℝ) * (100 * (L : ℝ) ^ (1/5 : ℝ)) := by
        apply mul_le_mul hexpmono hsq hnn2 (le_of_lt (Real.rpow_pos_of_pos hLpos _))
      have hcomb : (L : ℝ) ^ (51/100 : ℝ) * (100 * (L : ℝ) ^ (1/5 : ℝ))
          = 100 * (L : ℝ) ^ (71/100 : ℝ) := by
        rw [show (100 : ℝ) * (L : ℝ) ^ (1/5 : ℝ) = (L : ℝ) ^ (1/5 : ℝ) * 100 by ring,
          ← mul_assoc, ← Real.rpow_add hLpos]
        norm_num
        ring
      linarith
    -- and `100 C₀ L^{0.71} ≤ L/2000`
    have hfinal : 100 * C₀ * (L : ℝ) ^ (71 / 100 : ℝ) ≤ (L : ℝ) / 2000 := by
      have hsplit : (L : ℝ) = (L : ℝ) ^ (71/100 : ℝ) * (L : ℝ) ^ (29/100 : ℝ) := by
        rw [← Real.rpow_add hLpos]; norm_num
      have hbig : 200000 * C₀ ≤ (L : ℝ) ^ (29 / 100 : ℝ) := by
        have h4 : ((200000 * C₀) ^ (4 : ℕ) : ℝ) ^ (29 / 100 : ℝ) ≤ (L : ℝ) ^ (29/100 : ℝ) :=
          Real.rpow_le_rpow (by positivity) hpow (by norm_num)
        have h5 : (200000 * C₀) ≤ ((200000 * C₀) ^ (4 : ℕ) : ℝ) ^ (29 / 100 : ℝ) := by
          rw [← Real.rpow_natCast (200000 * C₀) 4, ← Real.rpow_mul (by positivity)]
          nth_rewrite 1 [show (200000 * C₀ : ℝ) = (200000 * C₀) ^ (1 : ℝ) by
            rw [Real.rpow_one]]
          apply Real.rpow_le_rpow_of_exponent_le
          · nlinarith
          · norm_num
        linarith
      have hpos71 : (0 : ℝ) < (L : ℝ) ^ (71/100 : ℝ) := Real.rpow_pos_of_pos hLpos _
      nlinarith
    nlinarith [Real.rpow_pos_of_pos hLpos (71/100 : ℝ)]
  have hexpand : C₀ * (α₀ * L + (L : ℝ) / Real.log L + (L : ℝ) ^ ((1 + α₀) / 2) * (Real.log L) ^ 2)
      = C₀ * (α₀ * L) + C₀ * ((L : ℝ) / Real.log L)
        + C₀ * ((L : ℝ) ^ ((1 + α₀) / 2) * (Real.log L) ^ 2) := by ring
  rw [hexpand] at hmain
  linarith

end FactorialHypergraph
