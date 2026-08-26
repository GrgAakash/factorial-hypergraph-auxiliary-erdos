/-
# The analytic input (A2) (Lemma 3.2 of the manuscript)

**STATUS OF (A2): PROVED IN LEAN, UNCONDITIONALLY** — with the threshold constant `40` in
place of the manuscript's `8`; see below and `A2Assembly.lean`
(`largePrimeFactor_unconditional`).  The manuscript's own statement, with the constant `8`,
is also proved here, conditionally on the sharper prime-counting bound
`π(y) ≤ 1.02 y / log y` (`largePrimeFactor_of_inputs_eight`).  No axiom is introduced
anywhere.

## The statement under discussion

Lemma 3.2 of the manuscript reads

  for all sufficiently large `N`,  `#{1 ≤ i ≤ N : P⁺(f(i)) > (1/c) i log i} ≥ N/5`,

with `c = 8`, where `f(i) = i² + 3i + 1`.  It is rendered by the finite set
`largePrimeFactorSetC c N` of `AnalyticInputs.lean`,

```
largePrimeFactorSetC (c : ℝ) (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter
    (fun i => ∃ q : ℕ, q.Prime ∧ q ∣ fq i ∧ (i : ℝ) * Real.log i / c < q)
```

quantifier by quantifier:

* "for all sufficiently large `N`" ↦ `∃ N₀, ∀ N, N₀ ≤ N → …`;
* "`1 ≤ i ≤ N`" ↦ the ambient finset `Finset.Icc 1 N`;
* "`P⁺(f(i)) > (1/c) i log i`" ↦ `∃ q, q.Prime ∧ q ∣ fq i ∧ (i:ℝ) * Real.log i / c < q`
  (the largest prime factor exceeds a bound iff *some* prime factor does, so this is a
  faithful rendering that avoids introducing `P⁺` itself);
* "`≥ N/5`" ↦ `(N : ℝ) / 5 ≤ (card : ℝ)`, over the reals, with `N/5` *not* rounded.

## The threshold constant, and why it is `40` downstream

The proof below is carried out with the threshold constant `c` and with the constant `κ` of
a prime-counting bound `π(y) ≤ κ y / log y` as parameters
(`largePrimeFactor_of_estimates`).  The three discarded families of indices contribute

  `0.01 N` (small indices) + `0.52 N` (smooth indices) + `(2κ/c) N` (discard step),

so the lemma holds as soon as `2κ/c ≤ 0.27`.

* With the manuscript's `c = 8` one needs `κ ≤ 1.08`, which is beyond the Chebyshev bound
  `κ = log 4 = 1.386…` available in mathlib.  This instance,
  `largePrimeFactor_of_inputs_eight`, is therefore **conditional** on the field
  `LargePrimeInputs.primeCountingUpper` (`π(y) ≤ 1.02 y/log y`).
* With `c = 40` one needs only `κ ≤ 5.4`, so mathlib's Chebyshev bound suffices and the
  lemma is **unconditional**.  This is the instance used by the rest of the development
  (`largePrimeFactorSet = largePrimeFactorSetC 40`), and the deviation is recorded in the
  docstring of `largePrimeFactorSet`.  It is harmless: Proposition 5.1 only needs
  `i log i / c > L` for `L/10 ≤ i ≤ L` and large `L`, which holds for every fixed `c`.

## What is proved here, unconditionally

* the product upper bound `log Q_N ≤ N log N + O(N)` (`logProd_upper`), via the
  prime-power multiplicity count of §3.1 and Legendre's `Nat.geom_sum_Ico_le`;
* the product lower bound `log Q_N ≥ |E_N| (2 log N - 2 log log N)` (`logProd_lower`);
* the resulting bound `|E_N| ≤ 0.52 N` (`card_smoothSet_le`);
* the discard step `2 π(N log N / c) ≤ (2κ/c) N` (`card_discard_le`), using
  `card_small_largest_prime_factor_le`;
* the bound for the excluded small indices (`card_small_indices_le`);
* the final combination (`largePrimeFactor_of_estimates`).

## The structure `LargePrimeInputs`

It is retained because it is exactly what the manuscript's own constant `8` requires.  Its
two fields are:

1. `mertensRoots` — the Mertens-type estimate
   `∑_{p ≤ N} ρ(p) log p / (p-1) ≤ log N + C`, where `ρ(p)` is the number of roots of
   `f` modulo `p`.  **PROVED IN LEAN, unconditionally** (`mertensRoots_unconditional`,
   `MertensRoots.lean`), since `ρ(p) = 1 + χ₅(p)`.
2. `primeCountingUpper` — a Chebyshev-type upper bound `π(y) ≤ 1.02 · y / log y` for all
   large `y`.  This is *weaker* than the prime number theorem (any constant `≤ 1.08` would
   do for the constant `c = 8`), but stronger than mathlib's Chebyshev constant
   `log 4 = 1.386…`.  It is reduced inside Lean to the Wiener–Ikehara Tauberian theorem
   (`PrimeCountingUpper.lean`), and it is needed **only** for the manuscript's constant `8`;
   no theorem outside this file and `A2Assembly.lean` depends on it.
-/
import FactorialHypergraph.QuadraticRoots
import FactorialHypergraph.AnalyticInputs
import FactorialHypergraph.Estimates
import FactorialHypergraph.PrimeSupply

namespace FactorialHypergraph

open Finset

/-! ## The two analytic estimates, isolated -/

/-- The primes `≤ n`. -/
def primesLE (n : ℕ) : Finset ℕ := (Finset.range (n + 1)).filter Nat.Prime

lemma mem_primesLE {n p : ℕ} : p ∈ primesLE n ↔ p ≤ n ∧ p.Prime := by
  simp [primesLE, Finset.mem_filter, Finset.mem_range]

/-- `ρ(p)`, the number of roots of `f(t) = t² + 3t + 1` modulo `p`, in elementary form. -/
def rootCount (p : ℕ) : ℕ := ((Finset.range p).filter (fun a => p ∣ fq a)).card

/-- The **only** analytic estimates that the proof of Lemma 3.2 below still needs.
They are packaged as fields of an explicit structure; no global axiom is introduced. -/
structure LargePrimeInputs : Prop where
  /-- **Mertens' estimate weighted by the root counts of `f`.**  Since
  `ρ(p) = 1 + χ₅(p)`, this is Mertens' second theorem `∑_{p≤N} log p/(p-1) = log N + O(1)`
  together with the bound `∑_{p≤N} χ₅(p) log p/(p-1) = O(1)` coming from
  `L(1, χ₅) ≠ 0` (prime equidistribution modulo `5`). -/
  mertensRoots : ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
    ∑ p ∈ primesLE N, (rootCount p : ℝ) * Real.log p / ((p : ℝ) - 1) ≤ Real.log N + C
  /-- **A Chebyshev-type upper bound for `π` with a constant below `1.08`.**
  `π(y) ≤ 1.02 · y / log y` for all large `y`.  This is weaker than the prime number
  theorem (any constant `≤ 1.08` would do for the bookkeeping below), but it is stronger
  than the Chebyshev bound available in mathlib, whose constant is `log 4 = 1.386…`. -/
  primeCountingUpper : ∃ y₀ : ℕ, ∀ y : ℕ, y₀ ≤ y →
    ((primesLE y).card : ℝ) ≤ 1.02 * (y : ℝ) / Real.log y

/-! ## The set `E_N` of smooth indices -/

open scoped Classical in
/-- `E_N = { i : N/log N < i ≤ N, P⁺(f(i)) ≤ i }`, the set of "smooth" indices in the
manuscript's proof of Lemma 3.2. -/
noncomputable def smoothSet (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter
    (fun i => (N : ℝ) / Real.log N < (i : ℝ) ∧ ∀ q : ℕ, q.Prime → q ∣ fq i → q ≤ i)

open scoped Classical in
lemma mem_smoothSet {N i : ℕ} :
    i ∈ smoothSet N ↔
      (1 ≤ i ∧ i ≤ N) ∧ (N : ℝ) / Real.log N < (i : ℝ) ∧
        ∀ q : ℕ, q.Prime → q ∣ fq i → q ≤ i := by
  simp [smoothSet, Finset.mem_filter, Finset.mem_Icc, and_assoc]

lemma smoothSet_subset (N : ℕ) : smoothSet N ⊆ Finset.Icc 1 N := by
  classical
  intro i hi
  exact Finset.mem_Icc.mpr (mem_smoothSet.mp hi).1

/-! ## Elementary facts about `fq` -/

lemma fq_pos (i : ℕ) : 0 < fq i := by
  simp only [fq]; positivity

lemma fq_ne_zero (i : ℕ) : fq i ≠ 0 := (fq_pos i).ne'

lemma fq_mono {i j : ℕ} (h : i ≤ j) : fq i ≤ fq j := by
  simp only [fq]
  have : i ^ 2 ≤ j ^ 2 := Nat.pow_le_pow_left h 2
  omega

lemma sq_le_fq (i : ℕ) : i ^ 2 ≤ fq i := by simp only [fq]; omega

lemma fq_le_cube {N : ℕ} (hN : 4 ≤ N) : fq N ≤ N ^ 3 := by
  simp only [fq]
  nlinarith [hN, sq_nonneg N]

/-! ## Root counting -/

/-- `ρ(p) ≤ 2` for every prime `p`. -/
theorem rootCount_le_two {p : ℕ} (hp : p.Prime) : rootCount p ≤ 2 := by
  classical
  refine card_le_two_of_dvd_fq_lt hp _ ?_ ?_ <;>
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_range] at hi
      tauto

/-- A set of pairwise incongruent (modulo `pᵃ`) roots of `f` modulo `pᵃ` injects into the
set of roots of `f` modulo `p`; hence it has at most `ρ(p)` elements. -/
theorem card_le_rootCount {p a : ℕ} (hp : p.Prime) (hp5 : p ≠ 5) (ha : 1 ≤ a)
    (s : Finset ℕ) (hincong : ∀ i ∈ s, ∀ j ∈ s, i ≡ j [MOD p ^ a] → i = j)
    (hdvd : ∀ i ∈ s, p ^ a ∣ fq i) : s.card ≤ rootCount p := by
  classical
  refine Finset.card_le_card_of_injOn (t := (Finset.range p).filter (fun a => p ∣ fq a))
    (fun i => i % p) ?_ ?_
  · intro i hi
    have hi' : i ∈ s := Finset.mem_coe.mp hi
    have hpi : p ∣ fq i := dvd_trans (dvd_pow_self p (by omega)) (hdvd i hi')
    have hcong : fq (i % p) ≡ fq i [MOD p] := fq_modEq (Nat.mod_modEq i p)
    have h0 : fq i ≡ 0 [MOD p] := (Nat.modEq_zero_iff_dvd).mpr hpi
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range]
    exact ⟨Nat.mod_lt _ hp.pos, (Nat.modEq_zero_iff_dvd).mp (hcong.trans h0)⟩
  · intro i hi j hj hij
    have hi' : i ∈ s := Finset.mem_coe.mp hi
    have hj' : j ∈ s := Finset.mem_coe.mp hj
    have h1 : i ≡ j [MOD p] := hij
    exact hincong i hi' j hj' (fq_unique_lift hp hp5 ha (hdvd i hi') (hdvd j hj') h1)

/-- The counting step of Lemma 3.2, in the sharp form with `ρ(p)`:
at most `(N/pᵃ + 1)·ρ(p)` indices `1 ≤ i ≤ N` satisfy `pᵃ ∣ f(i)`. -/
theorem card_dvd_fq_le_rootCount {p a : ℕ} (hp : p.Prime) (hp5 : p ≠ 5) (ha : 1 ≤ a)
    (N : ℕ) (E : Finset ℕ) (hE : E ⊆ Finset.Icc 1 N) :
    (E.filter (fun i => p ^ a ∣ fq i)).card ≤ (N / p ^ a + 1) * rootCount p := by
  classical
  set M : ℕ := p ^ a with hM
  have hMpos : 0 < M := pow_pos hp.pos a
  set s : Finset ℕ := E.filter (fun i => M ∣ fq i) with hs
  have hfiber : ∀ b ∈ Finset.image (fun i => i % M) s, {i ∈ s | i % M = b}.card ≤ N / M + 1 := by
    intro b _
    refine le_trans (Finset.card_le_card ?_) (card_filter_mod_le M N b)
    intro i hi
    simp only [Finset.mem_filter, hs] at hi ⊢
    exact ⟨hE hi.1.1, hi.2⟩
  have hmain := Finset.card_le_mul_card_image s (N / M + 1) hfiber
  have himage : (Finset.image (fun i => i % M) s).card ≤ rootCount p := by
    refine card_le_rootCount hp hp5 ha _ ?_ ?_
    · intro r hr r' hr' hrr'
      simp only [Finset.mem_image, hs] at hr hr'
      obtain ⟨i, -, rfl⟩ := hr
      obtain ⟨j, -, rfl⟩ := hr'
      have h1 : i % M < M := Nat.mod_lt _ hMpos
      have h2 : j % M < M := Nat.mod_lt _ hMpos
      unfold Nat.ModEq at hrr'
      rwa [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hrr'
    · intro r hr
      simp only [Finset.mem_image, hs, Finset.mem_filter] at hr
      obtain ⟨i, hi, rfl⟩ := hr
      have hcong : fq (i % M) ≡ fq i [MOD M] := fq_modEq (Nat.mod_modEq i M)
      have h0 : fq i ≡ 0 [MOD M] := (Nat.modEq_zero_iff_dvd).mpr hi.2
      exact (Nat.modEq_zero_iff_dvd).mp (hcong.trans h0)
  calc s.card ≤ (N / M + 1) * (Finset.image (fun i => i % M) s).card := hmain
    _ ≤ (N / M + 1) * rootCount p := Nat.mul_le_mul_left _ himage

/-! ## The multiplicity bound -/

/-- For a prime `p ≠ 5`, the total multiplicity of `p` in `∏_{i ∈ E} f(i)`, for any set of
indices `E ⊆ [1,N]`, is at most `ρ(p)·(N/(p-1) + log_p f(N))`. -/
theorem sum_factorization_le {p : ℕ} (hp : p.Prime) (hp5 : p ≠ 5) (N : ℕ) (E : Finset ℕ)
    (hE : E ⊆ Finset.Icc 1 N) :
    ∑ i ∈ E, (fq i).factorization p ≤ rootCount p * (N / (p - 1) + Nat.log p (fq N)) := by
  classical
  set b : ℕ := Nat.log p (fq N) + 1 with hb
  have hcard : ∀ i ∈ E,
      (fq i).factorization p = ((Finset.Ico 1 b).filter (fun a => p ^ a ∣ fq i)).card := by
    intro i hi
    have hiN : i ≤ N := (Finset.mem_Icc.mp (hE hi)).2
    have hlt : fq i < p ^ b :=
      lt_of_le_of_lt (fq_mono hiN) (Nat.lt_pow_succ_log_self hp.one_lt (fq N))
    exact Nat.factorization_eq_card_pow_dvd_of_lt hp (fq_pos i) hlt
  rw [Finset.sum_congr rfl hcard]
  have hswap : ∑ i ∈ E, ((Finset.Ico 1 b).filter (fun a => p ^ a ∣ fq i)).card
      = ∑ a ∈ Finset.Ico 1 b, (E.filter (fun i => p ^ a ∣ fq i)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  rw [hswap, mul_comm]
  calc ∑ a ∈ Finset.Ico 1 b, (E.filter (fun i => p ^ a ∣ fq i)).card
      ≤ ∑ a ∈ Finset.Ico 1 b, (N / p ^ a + 1) * rootCount p :=
        Finset.sum_le_sum fun a ha =>
          card_dvd_fq_le_rootCount hp hp5 (Finset.mem_Ico.mp ha).1 N E hE
    _ = ((∑ a ∈ Finset.Ico 1 b, N / p ^ a) + Nat.log p (fq N)) * rootCount p := by
        rw [← Finset.sum_mul]
        congr 1
        rw [Finset.sum_add_distrib]
        simp [hb, Nat.card_Ico]
    _ ≤ (N / (p - 1) + Nat.log p (fq N)) * rootCount p := by
        have := Nat.geom_sum_Ico_le hp.two_le N b
        exact Nat.mul_le_mul_right _ (by omega)

/-- `25 ∤ f(i)`, so the multiplicity of `5` in `∏_{i ∈ E} f(i)` is at most `#E`. -/
theorem sum_factorization_five_le (E : Finset ℕ) :
    ∑ i ∈ E, (fq i).factorization 5 ≤ E.card := by
  classical
  calc ∑ i ∈ E, (fq i).factorization 5 ≤ ∑ _i ∈ E, 1 := by
        refine Finset.sum_le_sum fun i _ => ?_
        by_contra hcon
        have h2 : 2 ≤ (fq i).factorization 5 := by omega
        have hdvd : (5 : ℕ) ^ 2 ∣ fq i :=
          (Nat.Prime.pow_dvd_iff_le_factorization (by norm_num) (fq_ne_zero i)).mpr h2
        exact not_twentyfive_dvd_fq i (by norm_num at hdvd ⊢; exact hdvd)
    _ = E.card := by simp

/-! ## `log n` as a sum over primes -/

/-- `log n = ∑_{p ∈ S} v_p(n) log p` for any finset `S` containing the prime factors. -/
theorem log_eq_sum_factorization {n : ℕ} (hn : n ≠ 0) {S : Finset ℕ}
    (hSp : ∀ p ∈ S, p.Prime) (hS : n.primeFactors ⊆ S) :
    Real.log n = ∑ p ∈ S, ((n.factorization p : ℕ) : ℝ) * Real.log p := by
  classical
  have hnat : n = ∏ p ∈ S, p ^ (n.factorization p) := by
    conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hn]
    exact Finsupp.prod_of_support_subset _ (by simpa [Nat.support_factorization] using hS) _
      (fun p _ => pow_zero p)
  have hreal : (n : ℝ) = ∏ p ∈ S, (p : ℝ) ^ (n.factorization p) := by
    exact_mod_cast congrArg (fun m : ℕ => (m : ℝ)) hnat
  rw [hreal, Real.log_prod]
  · exact Finset.sum_congr rfl fun p _ => by rw [Real.log_pow]
  · intro p hp
    have hp2 : (2 : ℕ) ≤ p := (hSp p hp).two_le
    have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast lt_of_lt_of_le (by norm_num) hp2
    positivity

lemma primeFactors_fq_subset {N i : ℕ} (hi : i ∈ smoothSet N) :
    (fq i).primeFactors ⊆ primesLE N := by
  classical
  intro q hq
  have hq' : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hdvd : q ∣ fq i := Nat.dvd_of_mem_primeFactors hq
  obtain ⟨⟨-, hiN⟩, -, hsm⟩ := mem_smoothSet.mp hi
  exact mem_primesLE.mpr ⟨le_trans (hsm q hq' hdvd) hiN, hq'⟩

/-! ## The product upper bound -/

/-- The elementary bound `log_p f(N) · log p ≤ 3 log N`. -/
lemma natLog_mul_log_le {p N : ℕ} (hp : p.Prime) (hN : 4 ≤ N) :
    ((Nat.log p (fq N) : ℕ) : ℝ) * Real.log p ≤ 3 * Real.log N := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : (0 : ℕ) < N := by omega
    exact_mod_cast this
  have h1 : (p : ℝ) ^ (Nat.log p (fq N)) ≤ (fq N : ℝ) := by
    have := Nat.pow_log_le_self p (fq_ne_zero N)
    exact_mod_cast this
  have hppos : (0 : ℝ) < (p : ℝ) := by
    have : (0 : ℕ) < p := hp.pos
    exact_mod_cast this
  have h2 : ((Nat.log p (fq N) : ℕ) : ℝ) * Real.log p = Real.log ((p : ℝ) ^ (Nat.log p (fq N))) := by
    rw [Real.log_pow]
  have h3 : Real.log ((p : ℝ) ^ (Nat.log p (fq N))) ≤ Real.log (fq N : ℝ) :=
    Real.log_le_log (by positivity) h1
  have h4 : (fq N : ℝ) ≤ (N : ℝ) ^ 3 := by exact_mod_cast fq_le_cube hN
  have h5 : Real.log (fq N : ℝ) ≤ Real.log ((N : ℝ) ^ 3) := by
    refine Real.log_le_log ?_ h4
    have : (0 : ℕ) < fq N := fq_pos N
    exact_mod_cast this
  rw [Real.log_pow] at h5
  push_cast at h5
  linarith

/-- **Upper bound for `log Q_N`.**  `log ∏_{i ∈ E_N} f(i) ≤ N log N + (C+16) N`. -/
theorem logProd_upper {C : ℝ}
    (hC : ∀ N : ℕ, 2 ≤ N →
      ∑ p ∈ primesLE N, (rootCount p : ℝ) * Real.log p / ((p : ℝ) - 1) ≤ Real.log N + C)
    {N : ℕ} (hN : 4 ≤ N) (hlog : 1 ≤ Real.log N)
    (hpi : ((primesLE N).card : ℝ) ≤ 2 * (N : ℝ) / Real.log N) :
    ∑ i ∈ smoothSet N, Real.log (fq i) ≤ (N : ℝ) * Real.log N + (C + 16) * N := by
  classical
  set E : Finset ℕ := smoothSet N with hEdef
  have hEsub : E ⊆ Finset.Icc 1 N := smoothSet_subset N
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : (0 : ℕ) < N := by omega
    exact_mod_cast this
  have hlogpos : (0 : ℝ) < Real.log N := by linarith
  have hEcard : (E.card : ℝ) ≤ (N : ℝ) := by
    have h1 := Finset.card_le_card hEsub
    rw [Nat.card_Icc] at h1
    have h2 : E.card ≤ N := by omega
    exact_mod_cast h2
  -- Step 1: decompose the logarithms over the primes `≤ N`
  have hsplit : ∑ i ∈ E, Real.log (fq i)
      = ∑ p ∈ primesLE N, ((∑ i ∈ E, (fq i).factorization p : ℕ) : ℝ) * Real.log p := by
    have h1 : ∀ i ∈ E, Real.log (fq i)
        = ∑ p ∈ primesLE N, (((fq i).factorization p : ℕ) : ℝ) * Real.log p := by
      intro i hi
      exact log_eq_sum_factorization (fq_ne_zero i) (fun p hp => (mem_primesLE.mp hp).2)
        (primeFactors_fq_subset hi)
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.sum_mul]
    push_cast
    ring
  -- Step 2: the pointwise bound for each prime
  have hpt : ∀ p ∈ primesLE N,
      ((∑ i ∈ E, (fq i).factorization p : ℕ) : ℝ) * Real.log p
        ≤ (rootCount p : ℝ) * (N : ℝ) * Real.log p / ((p : ℝ) - 1) + 6 * Real.log N
          + (if p = 5 then 4 * (N : ℝ) else 0) := by
    intro p hp
    obtain ⟨hpN, hpp⟩ := mem_primesLE.mp hp
    have hp2 : (2 : ℕ) ≤ p := hpp.two_le
    have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    have hlogp : (0 : ℝ) ≤ Real.log p := Real.log_nonneg (by linarith)
    have hrho : (0 : ℝ) ≤ (rootCount p : ℝ) := by positivity
    have hterm1 : (0 : ℝ) ≤ (rootCount p : ℝ) * (N : ℝ) * Real.log p / ((p : ℝ) - 1) := by
      have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      positivity
    by_cases hp5 : p = 5
    · subst hp5
      have hS : (∑ i ∈ E, (fq i).factorization 5) ≤ E.card := sum_factorization_five_le E
      have hSR : ((∑ i ∈ E, (fq i).factorization 5 : ℕ) : ℝ) ≤ (N : ℝ) :=
        le_trans (by exact_mod_cast hS) hEcard
      have hlog5' : Real.log ((5 : ℕ) : ℝ) ≤ 4 := by
        have h := Real.log_le_sub_one_of_pos (x := (((5 : ℕ) : ℝ))) (by norm_num)
        norm_num at h ⊢
        linarith
      have hlog5nn : (0 : ℝ) ≤ Real.log ((5 : ℕ) : ℝ) := Real.log_nonneg (by norm_num)
      have hmul : ((∑ i ∈ E, (fq i).factorization 5 : ℕ) : ℝ) * Real.log ((5 : ℕ) : ℝ)
          ≤ (N : ℝ) * 4 :=
        mul_le_mul hSR hlog5' hlog5nn (by positivity)
      have hif : (if (5 : ℕ) = 5 then 4 * (N : ℝ) else 0) = 4 * (N : ℝ) := by norm_num
      rw [hif]
      refine le_trans hmul ?_
      have h6 : (6 : ℝ) ≤ 6 * Real.log N := by linarith
      linarith [hterm1, h6]
    · have hS : (∑ i ∈ E, (fq i).factorization p)
          ≤ rootCount p * (N / (p - 1) + Nat.log p (fq N)) :=
        sum_factorization_le hpp hp5 N E hEsub
      have hdiv : (((N / (p - 1) : ℕ)) : ℝ) ≤ (N : ℝ) / ((p : ℝ) - 1) := by
        have h1 : (((N / (p - 1) : ℕ)) : ℝ) ≤ (N : ℝ) / ((p - 1 : ℕ) : ℝ) := Nat.cast_div_le
        have h2 : (((p - 1 : ℕ)) : ℝ) = (p : ℝ) - 1 := by
          have h1p : (1 : ℕ) ≤ p := by omega
          push_cast [Nat.cast_sub h1p]
          ring_nf
        rwa [h2] at h1
      have hSR : ((∑ i ∈ E, (fq i).factorization p : ℕ) : ℝ)
          ≤ (rootCount p : ℝ) * ((N : ℝ) / ((p : ℝ) - 1) + ((Nat.log p (fq N) : ℕ) : ℝ)) := by
        have h1 : ((∑ i ∈ E, (fq i).factorization p : ℕ) : ℝ)
            ≤ ((rootCount p * (N / (p - 1) + Nat.log p (fq N)) : ℕ) : ℝ) := by
          exact_mod_cast hS
        refine le_trans h1 ?_
        push_cast
        have : (0 : ℝ) ≤ (rootCount p : ℝ) := hrho
        nlinarith [hdiv]
      have hAlog := natLog_mul_log_le (p := p) hpp hN
      have hrho2 : (rootCount p : ℝ) ≤ 2 := by exact_mod_cast rootCount_le_two hpp
      have hexp : ((∑ i ∈ E, (fq i).factorization p : ℕ) : ℝ) * Real.log p
          ≤ (rootCount p : ℝ) * ((N : ℝ) / ((p : ℝ) - 1)) * Real.log p
            + (rootCount p : ℝ) * (((Nat.log p (fq N) : ℕ) : ℝ) * Real.log p) := by
        have := mul_le_mul_of_nonneg_right hSR hlogp
        nlinarith [this]
      have hsecond : (rootCount p : ℝ) * (((Nat.log p (fq N) : ℕ) : ℝ) * Real.log p)
          ≤ 6 * Real.log N := by
        have h0 : (0 : ℝ) ≤ ((Nat.log p (fq N) : ℕ) : ℝ) * Real.log p := by positivity
        nlinarith [hAlog, hrho2, hrho]
      have hfirst : (rootCount p : ℝ) * ((N : ℝ) / ((p : ℝ) - 1)) * Real.log p
          = (rootCount p : ℝ) * (N : ℝ) * Real.log p / ((p : ℝ) - 1) := by
        field_simp
      simp only [if_neg hp5]
      linarith [hexp, hsecond, hfirst ▸ hexp]
  -- Step 3: sum the pointwise bounds
  have hsum := Finset.sum_le_sum hpt
  rw [← hsplit] at hsum
  refine le_trans hsum ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hA : ∑ p ∈ primesLE N, (rootCount p : ℝ) * (N : ℝ) * Real.log p / ((p : ℝ) - 1)
      ≤ (N : ℝ) * (Real.log N + C) := by
    have hrw : ∀ p ∈ primesLE N,
        (rootCount p : ℝ) * (N : ℝ) * Real.log p / ((p : ℝ) - 1)
          = (N : ℝ) * ((rootCount p : ℝ) * Real.log p / ((p : ℝ) - 1)) := by
      intro p _
      field_simp
    rw [Finset.sum_congr rfl hrw, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hC N (by omega)) (le_of_lt hNpos)
  have hB : ∑ _p ∈ primesLE N, 6 * Real.log N ≤ 12 * (N : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul]
    have h1 : ((primesLE N).card : ℝ) * (6 * Real.log N)
        ≤ (2 * (N : ℝ) / Real.log N) * (6 * Real.log N) := by
      refine mul_le_mul_of_nonneg_right hpi (by positivity)
    have h2 : (2 * (N : ℝ) / Real.log N) * (6 * Real.log N) = 12 * (N : ℝ) := by
      field_simp
      ring
    linarith
  have hD : ∑ p ∈ primesLE N, (if p = 5 then 4 * (N : ℝ) else 0) ≤ 4 * (N : ℝ) := by
    rw [Finset.sum_ite_eq' (primesLE N) 5 (fun _ => 4 * (N : ℝ))]
    split_ifs with h
    · exact le_refl _
    · positivity
  nlinarith [hA, hB, hD]

/-! ## The product lower bound -/

/-- **Lower bound for `log Q_N`.**  Each `i ∈ E_N` exceeds `N / log N`, so
`log f(i) ≥ 2 log N - 2 log log N`. -/
theorem logProd_lower {N : ℕ} (hN : 2 ≤ N) (hlog : 0 < Real.log N) :
    ((smoothSet N).card : ℝ) * (2 * Real.log N - 2 * Real.log (Real.log N))
      ≤ ∑ i ∈ smoothSet N, Real.log (fq i) := by
  classical
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : (0 : ℕ) < N := by omega
    exact_mod_cast this
  have hkey : ∀ i ∈ smoothSet N,
      2 * Real.log N - 2 * Real.log (Real.log N) ≤ Real.log (fq i) := by
    intro i hi
    obtain ⟨⟨hi1, hiN⟩, hlt, -⟩ := mem_smoothSet.mp hi
    have hdivpos : (0 : ℝ) < (N : ℝ) / Real.log N := div_pos hNpos hlog
    have hipos : (0 : ℝ) < (i : ℝ) := lt_trans hdivpos hlt
    have h1 : Real.log ((N : ℝ) / Real.log N) ≤ Real.log i :=
      Real.log_le_log hdivpos (le_of_lt hlt)
    have h2 : Real.log ((N : ℝ) / Real.log N) = Real.log N - Real.log (Real.log N) :=
      Real.log_div (ne_of_gt hNpos) (ne_of_gt hlog)
    have hsq : ((i : ℝ)) ^ 2 ≤ (fq i : ℝ) := by exact_mod_cast sq_le_fq i
    have h3 : Real.log ((i : ℝ) ^ 2) ≤ Real.log (fq i) :=
      Real.log_le_log (by positivity) hsq
    rw [Real.log_pow] at h3
    push_cast at h3
    linarith
  calc ((smoothSet N).card : ℝ) * (2 * Real.log N - 2 * Real.log (Real.log N))
      = ∑ _i ∈ smoothSet N, (2 * Real.log N - 2 * Real.log (Real.log N)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ i ∈ smoothSet N, Real.log (fq i) := Finset.sum_le_sum hkey

/-- Comparing the two bounds: the smooth set has at most `0.52 N` elements. -/
theorem card_smoothSet_le {C₃ : ℝ} {N : ℕ} (hC₃ : 0 ≤ C₃) (hN : 2 ≤ N)
    (hlogbig : 50 * C₃ + 20000 ≤ Real.log N)
    (hupper : ∑ i ∈ smoothSet N, Real.log (fq i) ≤ (N : ℝ) * Real.log N + C₃ * N) :
    ((smoothSet N).card : ℝ) ≤ 0.52 * (N : ℝ) := by
  classical
  set t : ℝ := Real.log N with ht
  have ht0 : (20000 : ℝ) ≤ t := by linarith
  have htpos : (0 : ℝ) < t := by linarith
  set s : ℝ := Real.sqrt t with hs
  have hss : s * s = t := Real.mul_self_sqrt (le_of_lt htpos)
  have hs141 : (141 : ℝ) ≤ s := by
    have h1 : Real.sqrt 19881 ≤ Real.sqrt t := Real.sqrt_le_sqrt (by linarith)
    have h2 : Real.sqrt 19881 = 141 := by
      rw [show (19881 : ℝ) = 141 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    linarith [h1, h2 ▸ h1]
  have hlogt : Real.log t ≤ 2 * s := log_le_two_sqrt htpos
  have hkey : C₃ + 1.04 * Real.log t ≤ 0.04 * t := by nlinarith
  have hD : (0 : ℝ) < 2 * t - 2 * Real.log t := by nlinarith
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : (0 : ℕ) < N := by omega
    exact_mod_cast this
  have hlower := logProd_lower hN htpos
  have hstep : ((smoothSet N).card : ℝ) * (2 * t - 2 * Real.log t)
      ≤ 0.52 * (N : ℝ) * (2 * t - 2 * Real.log t) := by
    have h1 : ((smoothSet N).card : ℝ) * (2 * t - 2 * Real.log t)
        ≤ (N : ℝ) * t + C₃ * N := le_trans hlower hupper
    nlinarith
  exact le_of_mul_le_mul_right (by linarith [hstep]) hD

/-! ## The discard step -/

open scoped Classical in
/-- The indices discarded in the last step of the proof of Lemma 3.2. -/
noncomputable def discardSet (N y : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun i => ∃ q : ℕ, q.Prime ∧ q ∣ fq i ∧ i < q ∧ q ≤ y)

/-- **The discard step**, with the threshold constant `c` and the constant `κ` of the
prime-counting bound left as parameters: at most `(2κ/c)·N` indices are discarded. -/
theorem card_discard_le {N y : ℕ} {c kap : ℝ} (hc : 8 ≤ c) (hkap : 0 ≤ kap)
    (hlogN : 9 ≤ Real.log N) (hNy : N ≤ y)
    (hy : (y : ℝ) ≤ (N : ℝ) * Real.log N / c)
    (hpi : ((primesLE y).card : ℝ) ≤ kap * (y : ℝ) / Real.log y) :
    ((discardSet N y).card : ℝ) ≤ (2 * kap / c) * (N : ℝ) := by
  classical
  have hcpos : (0 : ℝ) < c := by linarith
  have hN10 : (10 : ℝ) ≤ (N : ℝ) := by
    rcases Nat.eq_zero_or_pos N with h | h
    · rw [h] at hlogN; simp at hlogN; linarith
    · have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast h
      have := Real.log_le_sub_one_of_pos hNpos
      linarith
  have hNposR : (0 : ℝ) < (N : ℝ) := by linarith
  have hyR : (N : ℝ) ≤ (y : ℝ) := by exact_mod_cast hNy
  have hypos : (0 : ℝ) < (y : ℝ) := by linarith
  have hlogy : Real.log N ≤ Real.log y := Real.log_le_log hNposR hyR
  have hlogypos : (0 : ℝ) < Real.log y := by linarith
  have hnat : (discardSet N y).card ≤ 2 * (primesLE y).card :=
    card_small_largest_prime_factor_le N y
  have hcast : ((discardSet N y).card : ℝ) ≤ 2 * ((primesLE y).card : ℝ) := by
    exact_mod_cast hnat
  have hratio : (y : ℝ) / Real.log y ≤ (N : ℝ) / c := by
    have h1 : (y : ℝ) / Real.log y ≤ (y : ℝ) / Real.log N :=
      div_le_div_of_nonneg_left (le_of_lt hypos) (by linarith) hlogy
    have h2 : (y : ℝ) / Real.log N ≤ ((N : ℝ) * Real.log N / c) / Real.log N := by
      gcongr
    have h3 : ((N : ℝ) * Real.log N / c) / Real.log N = (N : ℝ) / c := by
      field_simp
    linarith
  have hfinal : ((primesLE y).card : ℝ) ≤ kap * ((N : ℝ) / c) := by
    refine le_trans hpi ?_
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hratio hkap
  have heq : (2 * kap / c) * (N : ℝ) = 2 * (kap * ((N : ℝ) / c)) := by
    field_simp
  linarith

/-! ## The set of small indices -/

open scoped Classical in
/-- The indices `i ≤ N/log N`, which are excluded at the start of the argument. -/
theorem card_small_indices_le {N : ℕ} (hlog : 100 ≤ Real.log N) :
    (((Finset.Icc 1 N).filter (fun i : ℕ => ¬ ((N : ℝ) / Real.log N < (i : ℝ)))).card : ℝ)
      ≤ 0.01 * (N : ℝ) := by
  classical
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    rcases Nat.eq_zero_or_pos N with h | h
    · rw [h] at hlog; simp at hlog; linarith
    · exact_mod_cast h
  have hlogpos : (0 : ℝ) < Real.log N := by linarith
  have hqpos : (0 : ℝ) ≤ (N : ℝ) / Real.log N := by positivity
  set K : ℕ := ⌊(N : ℝ) / Real.log N⌋₊ with hK
  have hsub : ((Finset.Icc 1 N).filter (fun i : ℕ => ¬ ((N : ℝ) / Real.log N < (i : ℝ))))
      ⊆ (Finset.Icc 1 K : Finset ℕ) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_Icc, not_lt] at hi
    exact Finset.mem_Icc.mpr ⟨hi.1.1, Nat.le_floor hi.2⟩
  have hcard : (((Finset.Icc 1 N).filter
      (fun i : ℕ => ¬ ((N : ℝ) / Real.log N < (i : ℝ)))).card : ℝ) ≤ (K : ℝ) := by
    have h1 := Finset.card_le_card hsub
    rw [Nat.card_Icc] at h1
    have h2 : ((Finset.Icc 1 N).filter
        (fun i : ℕ => ¬ ((N : ℝ) / Real.log N < (i : ℝ)))).card ≤ K := by omega
    exact_mod_cast h2
  have hfloor : (K : ℝ) ≤ (N : ℝ) / Real.log N := Nat.floor_le hqpos
  have hdiv : (N : ℝ) / Real.log N ≤ 0.01 * (N : ℝ) := by
    rw [div_le_iff₀ hlogpos]
    nlinarith
  linarith

/-! ## The main theorem of this file -/

/-- **The proof of Lemma 3.2, with all constants left as parameters.**

From
* the Mertens-type estimate weighted by the root counts of `f`,
* an upper bound `π(y) ≤ κ y / log y` valid for large `y`, with `1 ≤ κ ≤ 2`,
* a threshold constant `c ∈ [8, 1000]` satisfying the bookkeeping inequality
  `2κ/c ≤ 0.27`,

one gets `#{1 ≤ i ≤ N : P⁺(f(i)) > i log i / c} ≥ N/5` for all large `N`.

The three excluded families of indices contribute `0.01 N` (small indices), `0.52 N`
(smooth indices) and `(2κ/c) N ≤ 0.27 N` (the discard step), and
`1 - 0.01 - 0.52 - 0.27 = 0.2`. -/
theorem largePrimeFactor_of_estimates {c kap : ℝ} (hc : 8 ≤ c) (hc' : c ≤ 1000)
    (hkap1 : 1 ≤ kap) (hkap2 : kap ≤ 2) (hnum : 2 * kap / c ≤ 0.27)
    (hmert : ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
      ∑ p ∈ primesLE N, (rootCount p : ℝ) * Real.log p / ((p : ℝ) - 1) ≤ Real.log N + C)
    (hpicount : ∃ y₀ : ℕ, ∀ y : ℕ, y₀ ≤ y →
      ((primesLE y).card : ℝ) ≤ kap * (y : ℝ) / Real.log y) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → (N : ℝ) / 5 ≤ ((largePrimeFactorSetC c N).card : ℝ) := by
  classical
  obtain ⟨C, hC0, hC⟩ := hmert
  obtain ⟨y₁, hy₁⟩ := hpicount
  have hcpos : (0 : ℝ) < c := by linarith
  set T : ℝ := 50 * (C + 16) + 20000 with hT
  refine ⟨max y₁ (⌈Real.exp T⌉₊ + 4), ?_⟩
  intro N hN
  have hNy₁ : y₁ ≤ N := le_trans (le_max_left _ _) hN
  have hNexp : ⌈Real.exp T⌉₊ + 4 ≤ N := le_trans (le_max_right _ _) hN
  have hN4 : 4 ≤ N := by omega
  have hexpN : Real.exp T ≤ (N : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast (by omega : ⌈Real.exp T⌉₊ ≤ N))
  have hNpos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hexpN
  have hlogT : T ≤ Real.log N := by
    have := Real.log_le_log (Real.exp_pos T) hexpN
    rwa [Real.log_exp] at this
  have hT0 : (20000 : ℝ) ≤ T := by rw [hT]; linarith
  have hlogN : (20000 : ℝ) ≤ Real.log N := le_trans hT0 hlogT
  -- the prime counting bounds
  have hpi1 : ((primesLE N).card : ℝ) ≤ 2 * (N : ℝ) / Real.log N := by
    refine le_trans (hy₁ N hNy₁) ?_
    rw [div_le_div_iff_of_pos_right (by linarith : (0:ℝ) < Real.log N)]
    nlinarith
  -- the smooth set
  have hupper := logProd_upper hC hN4 (by linarith) hpi1
  have hsmooth : ((smoothSet N).card : ℝ) ≤ 0.52 * (N : ℝ) :=
    card_smoothSet_le (by linarith) (by omega) (by rw [← hT] at *; linarith) hupper
  -- the small indices
  have hsmall := card_small_indices_le (N := N) (by linarith)
  -- the discarded indices
  set y : ℕ := ⌊(N : ℝ) * Real.log N / c⌋₊ with hy
  have hyN : N ≤ y := by
    refine Nat.le_floor ?_
    rw [le_div_iff₀ hcpos]
    nlinarith
  have hyle : (y : ℝ) ≤ (N : ℝ) * Real.log N / c := Nat.floor_le (by positivity)
  have hdisc0 : ((discardSet N y).card : ℝ) ≤ (2 * kap / c) * (N : ℝ) :=
    card_discard_le hc (by linarith) (by linarith) hyN hyle (hy₁ y (le_trans hNy₁ hyN))
  have hdisc : ((discardSet N y).card : ℝ) ≤ 0.27 * (N : ℝ) :=
    le_trans hdisc0 (by nlinarith)
  -- the covering of `[1, N]`
  set B₁ : Finset ℕ :=
    (Finset.Icc 1 N).filter (fun i : ℕ => ¬ ((N : ℝ) / Real.log N < (i : ℝ))) with hB₁
  have hcover : Finset.Icc 1 N ⊆
      largePrimeFactorSetC c N ∪ B₁ ∪ smoothSet N ∪ discardSet N y := by
    intro i hi
    by_contra hcon
    simp only [Finset.mem_union, not_or] at hcon
    obtain ⟨⟨⟨hA, hb₁⟩, hb₂⟩, hb₃⟩ := hcon
    obtain ⟨hi1, hiN⟩ := Finset.mem_Icc.mp hi
    have hbig : (N : ℝ) / Real.log N < (i : ℝ) := by
      by_contra hle
      exact hb₁ (Finset.mem_filter.mpr ⟨hi, hle⟩)
    have hex : ∃ q : ℕ, q.Prime ∧ q ∣ fq i ∧ i < q := by
      by_contra hno
      push_neg at hno
      exact hb₂ (mem_smoothSet.mpr ⟨⟨hi1, hiN⟩, hbig, hno⟩)
    obtain ⟨q, hqp, hqd, hqi⟩ := hex
    have hqy : y < q := by
      by_contra hle
      push_neg at hle
      exact hb₃ (Finset.mem_filter.mpr ⟨hi, ⟨q, hqp, hqd, hqi, hle⟩⟩)
    refine hA (mem_largePrimeFactorSetC.mpr ⟨⟨hi1, hiN⟩, q, hqp, hqd, ?_⟩)
    have h1 : (N : ℝ) * Real.log N / c < (y : ℝ) + 1 := Nat.lt_floor_add_one _
    have h2 : ((y : ℝ) + 1) ≤ (q : ℝ) := by exact_mod_cast hqy
    have hiR : (i : ℝ) ≤ (N : ℝ) := by exact_mod_cast hiN
    have hi1R : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi1
    have hlogi : Real.log i ≤ Real.log N := Real.log_le_log (by linarith) hiR
    have hlogi0 : (0 : ℝ) ≤ Real.log i := Real.log_nonneg hi1R
    have h3 : (i : ℝ) * Real.log i ≤ (N : ℝ) * Real.log N := by nlinarith
    have h4 : (i : ℝ) * Real.log i / c ≤ (N : ℝ) * Real.log N / c := by gcongr
    linarith
  -- counting
  have hcards : N ≤ (largePrimeFactorSetC c N).card + B₁.card + (smoothSet N).card
      + (discardSet N y).card := by
    have h1 := Finset.card_le_card hcover
    rw [Nat.card_Icc] at h1
    have h2 := Finset.card_union_le (largePrimeFactorSetC c N ∪ B₁ ∪ smoothSet N)
      (discardSet N y)
    have h3 := Finset.card_union_le (largePrimeFactorSetC c N ∪ B₁) (smoothSet N)
    have h4 := Finset.card_union_le (largePrimeFactorSetC c N) B₁
    omega
  have hcardsR : (N : ℝ) ≤ ((largePrimeFactorSetC c N).card : ℝ) + (B₁.card : ℝ)
      + ((smoothSet N).card : ℝ) + ((discardSet N y).card : ℝ) := by
    exact_mod_cast hcards
  linarith [hsmall, hsmooth, hdisc]

/-- **CONDITIONAL on `LargePrimeInputs`.**  Lemma 3.2 of the manuscript **with the
manuscript's own threshold constant** `1/8`:
`#{1 ≤ i ≤ N : P⁺(f(i)) > (1/8) i log i} ≥ N/5` for all large `N`.

This is the exact statement of the manuscript.  It needs the sharper prime-counting bound
`π(y) ≤ 1.02 y/log y` (the field `LargePrimeInputs.primeCountingUpper`), because with the
threshold constant `8` the discard step removes `2κ/8 · N` indices, and `0.27` requires
`κ ≤ 1.08`. -/
theorem largePrimeFactor_of_inputs_eight (h : LargePrimeInputs) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → (N : ℝ) / 5 ≤ ((largePrimeFactorSetC 8 N).card : ℝ) :=
  largePrimeFactor_of_estimates (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) h.mertensRoots h.primeCountingUpper

/-- **CONDITIONAL on `LargePrimeInputs`.**  The analytic input (A2), i.e. the field
`AnalyticInputs.largePrimeFactor`, in the form used in this development (threshold
constant `40`; see `largePrimeFactorSet`).  It follows from the manuscript's own form,
since raising the threshold constant only enlarges the counted set. -/
theorem largePrimeFactor_of_inputs (h : LargePrimeInputs) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → (N : ℝ) / 5 ≤ ((largePrimeFactorSet N).card : ℝ) := by
  obtain ⟨N₀, hN₀⟩ := largePrimeFactor_of_inputs_eight h
  refine ⟨N₀, fun N hN => le_trans (hN₀ N hN) ?_⟩
  exact_mod_cast Nat.cast_le.mpr (Finset.card_le_card (largePrimeFactorSet8_subset N))

/-- Since (A1) is proved in `PrimeSupply.lean` and (A2) follows from `LargePrimeInputs`,
a bundle of analytic inputs now only needs `LargePrimeInputs` and (A3). -/
theorem AnalyticInputs.of_largePrimeInputs (h : LargePrimeInputs)
    (h3 : ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∃ L₀ : ℕ, ∀ α : ℝ, 0 < α → α ≤ 1 / 2 →
      ∀ L : ℕ, L₀ ≤ L →
        ((smallCofactorSet α L).card : ℝ)
          ≤ C₀ * (α * L + (L : ℝ) / Real.log L + (L : ℝ) ^ ((1 + α) / 2) * (Real.log L) ^ 2)) :
    AnalyticInputs :=
  AnalyticInputs.of_two (largePrimeFactor_of_inputs h) h3

end FactorialHypergraph
