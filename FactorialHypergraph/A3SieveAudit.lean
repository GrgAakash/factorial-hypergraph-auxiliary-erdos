/-
# Machine-checked side conditions of the sieve-interface source audit

This file contains **no** new mathematical input.  It collects the elementary facts that the
external-source audit of the interface `UpperBoundSieveDimOne`
(`FactorialHypergraph/A3Sieve.lean`, report `REPORT_SIEVE_INTERFACE_AUDIT.md`) needs to be able to
assert, so that they are machine-checked rather than asserted in prose:

* `mem_sieveDivisors_iff` — the Lean index set of the remainder sum is *exactly* the set of
  `d` with `d ∣ ∏_{ℓ ∈ P} ℓ`, i.e. the source's `d | P` (squarefree `d` supported on the
  finite sieving-prime set);
* `dim_anchored_of_interval` — the *anchored* dimension hypothesis of the interface is
  **redundant**: it follows from the interval hypothesis together with the local bound
  `rho ℓ / ℓ ≤ 1`;
* `upperBoundSieveDimOne_iff_interval` — consequently the interface is *equivalent* to the
  version `UpperBoundSieveDimOneInterval` that drops the anchored hypothesis;
* `interval_condition_of_bounded_range` — the interval hypothesis for all `2 ≤ w₁ ≤ w₂` is
  no stronger than its restriction to `w₂ ≤ y` (the source's range `y₂ ≤ max P`);
* `sieve_conclusion_of_empty` — the conclusion of the interface holds unconditionally when
  the sieving-prime set is empty (the case in which the source's `y = max P` is undefined);
* `level_max_pow_le`, `remainder_sum_mono` — the `u = 10` specialisation: `y = max P ≤ z`
  gives `y ^ 10 ≤ z ^ 10 ≤ D`, and the source remainder sum (over `d ≤ y ^ 10`) is therefore
  dominated by the Lean remainder sum (over `d ≤ D`);
* `total_mass_nonneg`, `sieve_product_nonneg`, `remainder_sum_nonneg` — the nonnegativity of
  `X`, of `V = ∏_{ℓ ∈ P} (1 - rho ℓ / ℓ)` and of the remainder sum;
* `one_sided_of_asymptotic`, `u_ten_error` — the extraction of a one-sided bound with an
  explicit constant from the source's asymptotic equality at the fixed value `u = 10`.
-/
import FactorialHypergraph.A3Sieve

namespace FactorialHypergraph

open Finset

/-! ## The index set of the remainder sum -/

/-- A product of distinct primes is squarefree. -/
theorem squarefree_prod_primes {P : Finset ℕ} (hP : ∀ ℓ ∈ P, Nat.Prime ℓ) :
    Squarefree (∏ ℓ ∈ P, ℓ) := by
  classical
  induction P using Finset.induction_on with
  | empty => simp
  | insert p S hpS ih =>
    have hp : p.Prime := hP p (Finset.mem_insert_self p S)
    have hS : ∀ ℓ ∈ S, Nat.Prime ℓ := fun ℓ hl => hP ℓ (Finset.mem_insert_of_mem hl)
    rw [Finset.prod_insert hpS]
    refine (Nat.squarefree_mul_iff).mpr ⟨?_, hp.squarefree, ih hS⟩
    refine Nat.Coprime.prod_right ?_
    intro ℓ hl
    exact (Nat.coprime_primes hp (hS ℓ hl)).mpr (fun h => hpS (h ▸ hl))

/-- **`d ∣ P` in the sense of the source.**  For a finite set `P` of primes, the Lean index
set `sieveDivisors P` of the remainder sum is exactly the set of divisors of `∏_{ℓ ∈ P} ℓ`,
i.e. the set of squarefree numbers all of whose prime factors lie in `P`. -/
theorem mem_sieveDivisors_iff {P : Finset ℕ} (hP : ∀ ℓ ∈ P, Nat.Prime ℓ) (d : ℕ) :
    d ∈ sieveDivisors P ↔ d ∣ ∏ ℓ ∈ P, ℓ := by
  classical
  constructor
  · intro hd
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hd
    exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.mem_powerset.mp ht)
  · intro hd
    have hprodpos : 0 < ∏ ℓ ∈ P, ℓ := Finset.prod_pos (fun ℓ hl => (hP ℓ hl).pos)
    have hsq : Squarefree d := (squarefree_prod_primes hP).squarefree_of_dvd hd
    have hsub : d.primeFactors ⊆ P := by
      have h1 : d.primeFactors ⊆ (∏ ℓ ∈ P, ℓ).primeFactors :=
        Nat.primeFactors_mono hd hprodpos.ne'
      rw [Nat.primeFactors_prod hP] at h1
      exact h1
    refine Finset.mem_image.mpr ⟨d.primeFactors, Finset.mem_powerset.mpr hsub, ?_⟩
    exact Nat.prod_primeFactors_of_squarefree hsq

/-! ## Redundancy of the anchored dimension hypothesis -/

/-- **The anchored dimension hypothesis is redundant.**  For a finite set `P` of primes and a
local density with `rho ℓ / ℓ ≤ 1`, the interval form of the dimension-one condition implies
the anchored form, with the *same* constant `C₁`. -/
theorem dim_anchored_of_interval {P : Finset ℕ} {rho : ℕ → ℝ} {C₁ : ℝ}
    (hP : ∀ ℓ ∈ P, Nat.Prime ℓ) (hloc : ∀ ℓ ∈ P, rho ℓ / (ℓ : ℝ) ≤ 1)
    (hI : ∀ w₁ w₂ : ℝ, 2 ≤ w₁ → w₁ ≤ w₂ →
      ∑ ℓ ∈ P with (w₁ < ((ℓ : ℕ) : ℝ) ∧ ((ℓ : ℕ) : ℝ) ≤ w₂),
          rho ℓ * Real.log ℓ / (ℓ : ℝ) ≤ Real.log (w₂ / w₁) + C₁) :
    ∀ w : ℝ, 2 ≤ w →
      ∑ ℓ ∈ P with (((ℓ : ℕ) : ℝ) ≤ w), rho ℓ * Real.log ℓ / (ℓ : ℝ) ≤ Real.log w + C₁ := by
  classical
  intro w hw
  have hw0 : (0 : ℝ) < w := by linarith
  set s := P.filter (fun ℓ => ((ℓ : ℕ) : ℝ) ≤ w) with hs
  have hsplit :
      ∑ ℓ ∈ s, rho ℓ * Real.log ℓ / (ℓ : ℝ)
        = (∑ ℓ ∈ s with (2 < ((ℓ : ℕ) : ℝ)), rho ℓ * Real.log ℓ / (ℓ : ℝ))
          + ∑ ℓ ∈ s with ¬ (2 < ((ℓ : ℕ) : ℝ)), rho ℓ * Real.log ℓ / (ℓ : ℝ) :=
    (Finset.sum_filter_add_sum_filter_not s _ _).symm
  -- the part `2 < ℓ ≤ w` is exactly the interval sum with `w₁ = 2`, `w₂ = w`
  have hbig : (s.filter (fun ℓ => 2 < ((ℓ : ℕ) : ℝ)))
      = P.filter (fun ℓ => 2 < ((ℓ : ℕ) : ℝ) ∧ ((ℓ : ℕ) : ℝ) ≤ w) := by
    rw [hs, Finset.filter_filter]
    exact Finset.filter_congr (fun ℓ _ => by constructor <;> (intro h; exact ⟨h.2, h.1⟩))
  have h1 : ∑ ℓ ∈ s with (2 < ((ℓ : ℕ) : ℝ)), rho ℓ * Real.log ℓ / (ℓ : ℝ)
      ≤ Real.log (w / 2) + C₁ := by
    rw [hbig]; exact hI 2 w le_rfl hw
  -- the remaining part consists of the single prime `2` (if present) and is `≤ log 2`
  have hsmallsub : (s.filter (fun ℓ => ¬ (2 < ((ℓ : ℕ) : ℝ)))) ⊆ {2} := by
    intro ℓ hl
    have hlP : ℓ ∈ P := Finset.mem_filter.mp (Finset.mem_filter.mp hl).1 |>.1
    have hle : ((ℓ : ℕ) : ℝ) ≤ 2 := not_lt.mp (Finset.mem_filter.mp hl).2
    have h2 : (2 : ℕ) ≤ ℓ := (hP ℓ hlP).two_le
    have h2' : (2 : ℝ) ≤ ((ℓ : ℕ) : ℝ) := by exact_mod_cast h2
    have : ((ℓ : ℕ) : ℝ) = 2 := le_antisymm hle h2'
    have : ℓ = 2 := by exact_mod_cast this
    simp [this]
  have hterm : ∀ ℓ ∈ s.filter (fun ℓ => ¬ (2 < ((ℓ : ℕ) : ℝ))),
      rho ℓ * Real.log ℓ / (ℓ : ℝ) ≤ Real.log 2 := by
    intro ℓ hl
    have hlP : ℓ ∈ P := Finset.mem_filter.mp (Finset.mem_filter.mp hl).1 |>.1
    have hle : ((ℓ : ℕ) : ℝ) ≤ 2 := not_lt.mp (Finset.mem_filter.mp hl).2
    have h2 : (2 : ℕ) ≤ ℓ := (hP ℓ hlP).two_le
    have h2' : (2 : ℝ) ≤ ((ℓ : ℕ) : ℝ) := by exact_mod_cast h2
    have heq : ((ℓ : ℕ) : ℝ) = 2 := le_antisymm hle h2'
    have hlogeq : Real.log ℓ = Real.log 2 := by rw [heq]
    have hdiv : rho ℓ / (ℓ : ℝ) ≤ 1 := hloc ℓ hlP
    have hsplit : rho ℓ * Real.log ℓ / (ℓ : ℝ) = (rho ℓ / (ℓ : ℝ)) * Real.log ℓ := by ring
    have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    rw [hsplit, hlogeq]
    nlinarith
  have h2 : ∑ ℓ ∈ s with ¬ (2 < ((ℓ : ℕ) : ℝ)), rho ℓ * Real.log ℓ / (ℓ : ℝ) ≤ Real.log 2 := by
    have hcard : (s.filter (fun ℓ => ¬ (2 < ((ℓ : ℕ) : ℝ)))).card ≤ 1 := by
      have := Finset.card_le_card hsmallsub
      simpa using this
    calc ∑ ℓ ∈ s with ¬ (2 < ((ℓ : ℕ) : ℝ)), rho ℓ * Real.log ℓ / (ℓ : ℝ)
        ≤ ∑ _ℓ ∈ s.filter (fun ℓ => ¬ (2 < ((ℓ : ℕ) : ℝ))), Real.log 2 :=
          Finset.sum_le_sum hterm
      _ = (s.filter (fun ℓ => ¬ (2 < ((ℓ : ℕ) : ℝ)))).card * Real.log 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 1 * Real.log 2 := by
          have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
          have : ((s.filter (fun ℓ => ¬ (2 < ((ℓ : ℕ) : ℝ)))).card : ℝ) ≤ 1 := by
            exact_mod_cast hcard
          exact mul_le_mul_of_nonneg_right this hlog2
      _ = Real.log 2 := one_mul _
  have hlogdiv : Real.log (w / 2) = Real.log w - Real.log 2 :=
    Real.log_div hw0.ne' (by norm_num)
  rw [hsplit]
  linarith [h1, h2, hlogdiv.le, hlogdiv.ge]

/-! ## The interface without the anchored hypothesis, and its equivalence -/

open scoped Classical in
/-- The interface `UpperBoundSieveDimOne` with the (redundant) anchored dimension hypothesis
removed.  Only the interval form — the source's Axiom 2 / Axiom 2′ shape — is assumed. -/
def UpperBoundSieveDimOneInterval : Prop :=
  ∀ C₁ k ε : ℝ, 0 ≤ C₁ → 1 ≤ k → 0 < ε → ε < 1 →
    ∃ C : ℝ, 0 < C ∧
      ∀ (A : Finset ℕ) (a : ℕ → ℝ) (P : Finset ℕ) (rho : ℕ → ℝ) (X z D : ℝ),
        (∀ n ∈ A, 0 < n) →
        (∀ n, 0 ≤ a n) →
        (∀ n, n ∉ A → a n = 0) →
        X = ∑ n ∈ A, a n →
        (∀ ℓ ∈ P, Nat.Prime ℓ) →
        (∀ ℓ ∈ P, (ℓ : ℝ) ≤ z) →
        (2 : ℝ) ≤ z →
        (∀ ℓ ∈ P, 0 ≤ rho ℓ) →
        (∀ ℓ ∈ P, rho ℓ ≤ k) →
        (∀ ℓ ∈ P, rho ℓ / (ℓ : ℝ) ≤ 1 - ε) →
        (∀ t ⊆ P, rho (∏ ℓ ∈ t, ℓ) = ∏ ℓ ∈ t, rho ℓ) →
        (∀ w₁ w₂ : ℝ, 2 ≤ w₁ → w₁ ≤ w₂ →
          ∑ ℓ ∈ P with (w₁ < ((ℓ : ℕ) : ℝ) ∧ ((ℓ : ℕ) : ℝ) ≤ w₂),
              rho ℓ * Real.log ℓ / (ℓ : ℝ)
            ≤ Real.log (w₂ / w₁) + C₁) →
        z ^ (10 : ℕ) ≤ D →
        ∑ n ∈ A with (∀ ℓ ∈ P, ¬ (ℓ ∣ n)), a n
          ≤ C * (X * ∏ ℓ ∈ P, (1 - rho ℓ / (ℓ : ℝ))
              + ∑ d ∈ sieveDivisors P with (((d : ℕ) : ℝ) ≤ D),
                  |(∑ n ∈ A with (d ∣ n), a n) - X * rho d / (d : ℝ)|)

/-- **The anchored hypothesis carries no strength.**  The interface actually used in the
project is *equivalent* to the interface that assumes only the interval (Axiom 2′-shaped)
dimension condition. -/
theorem upperBoundSieveDimOne_iff_interval :
    UpperBoundSieveDimOne ↔ UpperBoundSieveDimOneInterval := by
  classical
  constructor
  · intro h C₁ k ε hC₁ hk hε hε1
    obtain ⟨C, hC, hmain⟩ := h C₁ k ε hC₁ hk hε hε1
    refine ⟨C, hC, ?_⟩
    intro A a P rho X z D hApos ha0 hasupp hX hPp hPz hz hr0 hrk hrε hrmul hI hD
    refine hmain A a P rho X z D hApos ha0 hasupp hX hPp hPz hz hr0 hrk hrε hrmul ?_ hI hD
    refine dim_anchored_of_interval hPp (fun ℓ hl => ?_) hI
    have := hrε ℓ hl
    linarith
  · intro h C₁ k ε hC₁ hk hε hε1
    obtain ⟨C, hC, hmain⟩ := h C₁ k ε hC₁ hk hε hε1
    refine ⟨C, hC, ?_⟩
    intro A a P rho X z D hApos ha0 hasupp hX hPp hPz hz hr0 hrk hrε hrmul _hA hI hD
    exact hmain A a P rho X z D hApos ha0 hasupp hX hPp hPz hz hr0 hrk hrε hrmul hI hD

/-! ## The range of the interval condition -/

/-- **The range `w₂ ≤ max P` of the source is not a restriction.**  If the interval condition
holds for `2 ≤ w₁ ≤ w₂ ≤ y` and all primes of `P` are `≤ y`, then it holds for all
`2 ≤ w₁ ≤ w₂`. -/
theorem interval_condition_of_bounded_range {P : Finset ℕ} {rho : ℕ → ℝ} {C₁ y : ℝ}
    (hC₁ : 0 ≤ C₁) (hPy : ∀ ℓ ∈ P, ((ℓ : ℕ) : ℝ) ≤ y)
    (h : ∀ w₁ w₂ : ℝ, 2 ≤ w₁ → w₁ ≤ w₂ → w₂ ≤ y →
      ∑ ℓ ∈ P with (w₁ < ((ℓ : ℕ) : ℝ) ∧ ((ℓ : ℕ) : ℝ) ≤ w₂),
          rho ℓ * Real.log ℓ / (ℓ : ℝ) ≤ Real.log (w₂ / w₁) + C₁) :
    ∀ w₁ w₂ : ℝ, 2 ≤ w₁ → w₁ ≤ w₂ →
      ∑ ℓ ∈ P with (w₁ < ((ℓ : ℕ) : ℝ) ∧ ((ℓ : ℕ) : ℝ) ≤ w₂),
          rho ℓ * Real.log ℓ / (ℓ : ℝ) ≤ Real.log (w₂ / w₁) + C₁ := by
  classical
  intro w₁ w₂ hw₁ hw₁₂
  have hw₁0 : (0 : ℝ) < w₁ := by linarith
  have hlognn : 0 ≤ Real.log (w₂ / w₁) :=
    Real.log_nonneg ((one_le_div hw₁0).mpr hw₁₂)
  rcases le_or_gt w₂ y with hy | hy
  · exact h w₁ w₂ hw₁ hw₁₂ hy
  · rcases le_or_gt w₁ y with hwy | hwy
    · -- `w₁ ≤ y < w₂`: the sum over `(w₁, w₂]` equals the sum over `(w₁, y]`
      have hset : P.filter (fun ℓ => w₁ < ((ℓ : ℕ) : ℝ) ∧ ((ℓ : ℕ) : ℝ) ≤ w₂)
          = P.filter (fun ℓ => w₁ < ((ℓ : ℕ) : ℝ) ∧ ((ℓ : ℕ) : ℝ) ≤ y) := by
        refine Finset.filter_congr (fun ℓ hl => ?_)
        constructor
        · rintro ⟨h1, -⟩; exact ⟨h1, hPy ℓ hl⟩
        · rintro ⟨h1, h2⟩; exact ⟨h1, le_trans h2 hy.le⟩
      rw [hset]
      refine le_trans (h w₁ y hw₁ hwy le_rfl) ?_
      have hy0 : (0 : ℝ) < y := lt_of_lt_of_le hw₁0 hwy
      have hmono : Real.log (y / w₁) ≤ Real.log (w₂ / w₁) := by
        refine Real.log_le_log (by positivity) ?_
        gcongr
      linarith
    · -- `y < w₁`: the sum is empty
      have hempty : P.filter (fun ℓ => w₁ < ((ℓ : ℕ) : ℝ) ∧ ((ℓ : ℕ) : ℝ) ≤ w₂) = ∅ := by
        refine Finset.filter_eq_empty_iff.mpr (fun ℓ hl => ?_)
        rintro ⟨h1, -⟩
        exact absurd (lt_of_lt_of_le h1 (hPy ℓ hl)) (not_lt.mpr hwy.le)
      rw [hempty, Finset.sum_empty]
      linarith

/-! ## Nonnegativity of the ingredients -/

theorem total_mass_nonneg {A : Finset ℕ} {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) :
    0 ≤ ∑ n ∈ A, a n := Finset.sum_nonneg (fun n _ => ha n)

/-- `V = ∏_{ℓ ∈ P} (1 - rho ℓ / ℓ)` is nonnegative (indeed each factor is `≥ ε > 0`). -/
theorem sieve_product_nonneg {P : Finset ℕ} {rho : ℕ → ℝ} {ε : ℝ} (hε : 0 < ε)
    (h : ∀ ℓ ∈ P, rho ℓ / (ℓ : ℝ) ≤ 1 - ε) :
    0 ≤ ∏ ℓ ∈ P, (1 - rho ℓ / (ℓ : ℝ)) := by
  refine Finset.prod_nonneg (fun ℓ hl => ?_)
  have := h ℓ hl
  linarith

theorem remainder_sum_nonneg (P : Finset ℕ) (A : Finset ℕ) (a : ℕ → ℝ) (rho : ℕ → ℝ) (X D : ℝ) :
    0 ≤ ∑ d ∈ sieveDivisors P with (((d : ℕ) : ℝ) ≤ D),
        |(∑ n ∈ A with (d ∣ n), a n) - X * rho d / (d : ℝ)| := by
  classical
  exact Finset.sum_nonneg (fun d _ => abs_nonneg _)

/-! ## The empty sieving-prime set -/

open scoped Classical in
/-- **The empty prime set, for which the source's `y = max P` is undefined, needs no external
input.**  When `P = ∅` the conclusion of the interface holds outright for every `C ≥ 1`. -/
theorem sieve_conclusion_of_empty (A : Finset ℕ) (a : ℕ → ℝ) (rho : ℕ → ℝ) (X D C : ℝ)
    (ha : ∀ n, 0 ≤ a n) (hX : X = ∑ n ∈ A, a n) (hC : 1 ≤ C) :
    ∑ n ∈ A with (∀ ℓ ∈ (∅ : Finset ℕ), ¬ (ℓ ∣ n)), a n
      ≤ C * (X * ∏ ℓ ∈ (∅ : Finset ℕ), (1 - rho ℓ / (ℓ : ℝ))
          + ∑ d ∈ sieveDivisors (∅ : Finset ℕ) with (((d : ℕ) : ℝ) ≤ D),
              |(∑ n ∈ A with (d ∣ n), a n) - X * rho d / (d : ℝ)|) := by
  classical
  have hX0 : 0 ≤ X := by rw [hX]; exact total_mass_nonneg ha
  have hleft : ∑ n ∈ A with (∀ ℓ ∈ (∅ : Finset ℕ), ¬ (ℓ ∣ n)), a n = X := by
    simp [hX]
  have hR : 0 ≤ ∑ d ∈ sieveDivisors (∅ : Finset ℕ) with (((d : ℕ) : ℝ) ≤ D),
      |(∑ n ∈ A with (d ∣ n), a n) - X * rho d / (d : ℝ)| :=
    remainder_sum_nonneg _ _ _ _ _ _
  rw [hleft, Finset.prod_empty, mul_one]
  nlinarith

/-! ## The sifted sum -/

open scoped Classical in
/-- **The Lean sifted sum is exactly `S(A, P) = ∑_{(n, P) = 1} a_n`.**  For a finite set `P` of
primes, "no prime of `P` divides `n`" is the same condition as `(n, ∏_{ℓ ∈ P} ℓ) = 1`. -/
theorem sifted_sum_eq_coprime_sum {P : Finset ℕ} (hP : ∀ ℓ ∈ P, Nat.Prime ℓ)
    (A : Finset ℕ) (a : ℕ → ℝ) :
    ∑ n ∈ A with (∀ ℓ ∈ P, ¬ (ℓ ∣ n)), a n
      = ∑ n ∈ A with Nat.Coprime n (∏ ℓ ∈ P, ℓ), a n := by
  classical
  refine Finset.sum_congr (Finset.filter_congr (fun n _ => ?_)) (fun _ _ => rfl)
  constructor
  · intro h
    refine Nat.Coprime.prod_right (fun ℓ hl => ?_)
    exact ((hP ℓ hl).coprime_iff_not_dvd.mpr (h ℓ hl)).symm
  · intro h ℓ hl hdvd
    have h1 : ℓ ∣ Nat.gcd n (∏ ℓ ∈ P, ℓ) :=
      Nat.dvd_gcd hdvd (Finset.dvd_prod_of_mem _ hl)
    rw [Nat.Coprime] at h
    rw [h] at h1
    exact (hP ℓ hl).one_lt.ne' (Nat.dvd_one.mp h1)

/-! ## The `u = 10` specialisation -/

/-- `u = 10`: `y = max P ≤ z` gives `y ^ 10 ≤ z ^ 10 ≤ D`, so the source's remainder range
`d ≤ y ^ u` is contained in the Lean remainder range `d ≤ D`. -/
theorem level_max_pow_le {P : Finset ℕ} (hne : P.Nonempty) {z D : ℝ}
    (hPle : ∀ ℓ ∈ P, ((ℓ : ℕ) : ℝ) ≤ z) (hD : z ^ (10 : ℕ) ≤ D) :
    ((P.max' hne : ℕ) : ℝ) ^ (10 : ℕ) ≤ z ^ (10 : ℕ) ∧
      ((P.max' hne : ℕ) : ℝ) ^ (10 : ℕ) ≤ D := by
  have hy : ((P.max' hne : ℕ) : ℝ) ≤ z := hPle _ (P.max'_mem hne)
  have hy0 : (0 : ℝ) ≤ ((P.max' hne : ℕ) : ℝ) := by positivity
  have h1 : ((P.max' hne : ℕ) : ℝ) ^ (10 : ℕ) ≤ z ^ (10 : ℕ) := by gcongr
  exact ⟨h1, le_trans h1 hD⟩

/-- Monotonicity of the remainder sum in the level: the source remainder sum, truncated at
`y ^ 10`, is bounded by the Lean remainder sum, truncated at `D ≥ y ^ 10`. -/
theorem remainder_sum_mono (P : Finset ℕ) (f : ℕ → ℝ) (hf : ∀ d, 0 ≤ f d) {D₁ D₂ : ℝ}
    (h : D₁ ≤ D₂) :
    ∑ d ∈ sieveDivisors P with (((d : ℕ) : ℝ) ≤ D₁), f d
      ≤ ∑ d ∈ sieveDivisors P with (((d : ℕ) : ℝ) ≤ D₂), f d := by
  classical
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun d _ _ => hf d)
  intro d hd
  obtain ⟨hd1, hd2⟩ := Finset.mem_filter.mp hd
  exact Finset.mem_filter.mpr ⟨hd1, le_trans hd2 h⟩

/-- The error factor of Theorem 18.11(a) at the fixed value `u = 10`:
`u ^ (-u/2) = 10 ^ (-5) = 1/100000`. -/
theorem u_ten_error : (10 : ℝ) ^ (-(10 : ℝ) / 2) = 1 / 100000 := by
  rw [show (-(10 : ℝ) / 2) = ((-5 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
  norm_num

/-- **From an asymptotic equality to a one-sided bound with an explicit constant.**  If
`S ≤ (1 + θ) M + c R` with `M, R ≥ 0` — the shape produced by Theorem 18.11(a) with
`u = 10`, where `θ` is the implied constant times `10 ^ (-5)` and `c` is the implied constant
of the remainder term — then `S ≤ max (1 + θ) c · (M + R)`. -/
theorem one_sided_of_asymptotic {S M R θ c : ℝ} (hM : 0 ≤ M) (hR : 0 ≤ R)
    (h : S ≤ (1 + θ) * M + c * R) :
    S ≤ max (1 + θ) c * (M + R) := by
  have h1 : (1 + θ) * M ≤ max (1 + θ) c * M :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hM
  have h2 : c * R ≤ max (1 + θ) c * R :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) hR
  nlinarith

/-- The sieve parameters of the application: with `z = H ^ (1/20)` and `D = H ^ (1/2)` one has
`z ^ 10 = D` exactly, so `u = 10` is admissible with equality. -/
theorem level_eq_of_application {H : ℝ} (hH : 0 < H) :
    (H ^ ((1 : ℝ) / 20)) ^ (10 : ℕ) = H ^ ((1 : ℝ) / 2) := by
  rw [← Real.rpow_natCast (H ^ ((1 : ℝ) / 20)) 10, ← Real.rpow_mul hH.le]
  norm_num

/-! ## Axiom audit for this file -/

#print axioms squarefree_prod_primes
#print axioms mem_sieveDivisors_iff
#print axioms dim_anchored_of_interval
#print axioms upperBoundSieveDimOne_iff_interval
#print axioms interval_condition_of_bounded_range
#print axioms total_mass_nonneg
#print axioms sieve_product_nonneg
#print axioms remainder_sum_nonneg
#print axioms sieve_conclusion_of_empty
#print axioms sifted_sum_eq_coprime_sum
#print axioms level_max_pow_le
#print axioms remainder_sum_mono
#print axioms u_ten_error
#print axioms one_sided_of_asymptotic
#print axioms level_eq_of_application

end FactorialHypergraph
