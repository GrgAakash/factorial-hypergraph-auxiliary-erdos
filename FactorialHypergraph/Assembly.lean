/-
# Final assembly: the manuscript's theorems from one named classical theorem

This file collects the reductions proved in the rest of the project into a single place.
Recall the three analytic inputs of the manuscript, packaged as the fields of the structure
`AnalyticInputs` (no global axiom is ever introduced):

* **(A1)** the supply of primes in `(L, 20 L log L]` — **PROVED IN LEAN, unconditionally**
  (`prime_supply`, `PrimeSupply.lean`);
* **(A2)** the large-prime-factor estimate for `f(i) = i² + 3i + 1` (Lemma 3.2) —
  **PROVED IN LEAN, unconditionally** (`largePrimeFactor_unconditional`, `A2Assembly.lean`),
  with the threshold constant `40` in place of the manuscript's `8`; see the docstring of
  `largePrimeFactorSet` for that explicitly recorded deviation, and
  `largePrimeFactor_of_inputs_eight` for the manuscript's own constant, which remains
  conditional on the sharper bound `π(y) ≤ 1.02 y/log y`;
* **(A3)** the uniform small-complementary-factor sieve estimate (Lemma 4.2) — proved in Lean
  from the dimension-one upper-bound sieve `UpperBoundSieveDimOne` alone
  (`smallCofactorSieve_of_inputs`, `A3Main.lean`); the Mertens input it needs,
  `∑_{p ≤ N, χ₅(p) = 1} 1/p = (log log N)/2 + O(1)`, is proved unconditionally in
  `MertensSecond.lean`.

Hence all the manuscript's conclusions follow, **inside Lean**, from the single classical
theorem

    UpperBoundSieveDimOne,

which is not available in the pinned mathlib revision and which is carried as an explicit
`Prop`-valued hypothesis (never as an axiom).  Every theorem in this file is therefore
**CONDITIONAL**, as its name and docstring record.

Nothing here claims Erdős Problem 1059 (the original prime problem); the manuscript, and this
formalization, treat only the auxiliary problem suggested by Erdős.
-/
import FactorialHypergraph.A2Assembly
import FactorialHypergraph.A3Main
import FactorialHypergraph.MainConditional

namespace FactorialHypergraph

/-! ## (A3) from the sieve theorem -/

/-- **(A3), CONDITIONAL** on the dimension-one upper-bound sieve, and on nothing else.
The statement is the field `AnalyticInputs.smallCofactorSieve`, verbatim. -/
theorem smallCofactorSieve_conditional (hs : UpperBoundSieveDimOne) :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∃ L₀ : ℕ, ∀ α : ℝ, 0 < α → α ≤ 1 / 2 →
      ∀ L : ℕ, L₀ ≤ L →
        ((smallCofactorSet α L).card : ℝ)
          ≤ C₀ * (α * L + (L : ℝ) / Real.log L + (L : ℝ) ^ ((1 + α) / 2) * (Real.log L) ^ 2) :=
  smallCofactorSieve_of_inputs hs

/-! ## The full bundle of analytic inputs -/

/-- **CONDITIONAL** on the dimension-one upper-bound sieve alone: the whole structure
`AnalyticInputs`.  (A1) and (A2) contribute no hypothesis, both being proved in Lean. -/
theorem AnalyticInputs.of_sieve_theorem (hs : UpperBoundSieveDimOne) : AnalyticInputs :=
  AnalyticInputs.of_smallCofactorSieve (smallCofactorSieve_of_inputs hs)

/-! ## The manuscript's theorems, conditional on the sieve theorem -/

/-- **Theorem 1.1 (cover cost), CONDITIONAL** on the dimension-one upper-bound sieve:
`κ(L) ≤ (1 - δ) L log L` for some fixed `δ > 0` and all large `L`. -/
theorem cover_cost_of_sieve_theorem (hs : UpperBoundSieveDimOne) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L → kappa L ≤ (1 - δ) * L * Real.log L :=
  cover_cost (AnalyticInputs.of_sieve_theorem hs)

/-- **Theorem 1.2 (quantitative auxiliary theorem), CONDITIONAL** on the dimension-one
upper-bound sieve: for some `η > 0` and all large `L`,
`#(goodSet L) ≥ ((L+1)!)^η / (100 log L)`. -/
theorem main_quantitative_of_sieve_theorem (hs : UpperBoundSieveDimOne) :
    ∃ η : ℝ, 0 < η ∧ ∃ L₁ : ℕ, ∀ L : ℕ, L₁ ≤ L →
      ((L + 1).factorial : ℝ) ^ η / (100 * Real.log L) ≤ ((goodSet L).card : ℝ) :=
  main_quantitative (AnalyticInputs.of_sieve_theorem hs)

/-- **The auxiliary problem suggested by Erdős, CONDITIONAL** on the dimension-one
upper-bound sieve: for every large `L` there is an `L`-rough integer `n ∈ (L!, (L+1)!]` such
that `n - k!` is a composite number `> 1` for every `1 ≤ k ≤ L`.

This is **not** Erdős Problem 1059: no primality of `n` is asserted. -/
theorem auxiliary_erdos_problem_of_sieve_theorem (hs : UpperBoundSieveDimOne) :
    ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L → ∃ n : ℕ,
      L.factorial < n ∧
      n ≤ (L + 1).factorial ∧
      (∀ p : ℕ, p.Prime → p ∣ n → L < p) ∧
      ∀ k : ℕ, 1 ≤ k → k ≤ L → ¬ (n - k.factorial).Prime ∧ 1 < n - k.factorial :=
  auxiliary_erdos_problem (AnalyticInputs.of_sieve_theorem hs)

end FactorialHypergraph

/-! ## Axiom audit -/

#print axioms FactorialHypergraph.smallCofactorSieve_conditional
#print axioms FactorialHypergraph.AnalyticInputs.of_sieve_theorem
#print axioms FactorialHypergraph.cover_cost_of_sieve_theorem
#print axioms FactorialHypergraph.main_quantitative_of_sieve_theorem
#print axioms FactorialHypergraph.auxiliary_erdos_problem_of_sieve_theorem
