/-
# Assembly: the analytic input (A2), and what the manuscript's own constant costs

**Status.**  The analytic input (A2), i.e. the field `AnalyticInputs.largePrimeFactor`, is
**PROVED IN LEAN, UNCONDITIONALLY** (`largePrimeFactor_fortieth` below).  Both
ingredients are available:

| ingredient | status |
| --- | --- |
| `mertensRoots` (`∑_{p≤N} ρ(p) log p/(p-1) ≤ log N + C`) | **PROVED IN LEAN, unconditionally** (`mertensRoots_unconditional`) |
| a prime-counting bound `π(y) ≤ κ y/log y` with the safe explicit value `κ = 2` | **PROVED FROM MATHLIB** (`primeCountingUpper_two`, from `Chebyshev.theta_le_log4_mul_x`; mathlib gives `θ(x) ≤ (log 4) x`, hence `π(y) ≤ (log 4 + ε) y/log y` for every `ε > 0`, and `2` is a safe round value) |

This uses the threshold constant `40` of `largePrimeFactorSet`; with the manuscript's own
constant `8` one needs `κ ≤ 1.08`, i.e. the field `LargePrimeInputs.primeCountingUpper`
(`π(y) ≤ 1.02 y/log y`), which is strictly stronger than anything in the pinned mathlib
revision.  That version, `largePrimeFactor_eighth` (`= largePrimeFactor_of_inputs_eight`), therefore remains conditional,
and the implications recorded in this file — from Wiener–Ikehara, from the prime number
theorem in any of its usual forms, or from `θ(x) ≤ c x` with `c < 1.02` — are what it costs.

The interface `FactorialHypergraph.WienerIkeharaTheorem` (in `PrimeCountingUpper.lean`) is
an explicit hypothesis of the theorems below, not a global axiom: it appears as a
`Prop`-valued argument, so `#print axioms` correctly reports no custom axiom.
-/
import FactorialHypergraph.MertensRoots
import FactorialHypergraph.PrimeCountingUpper

namespace FactorialHypergraph

/-- **CONDITIONAL on the Wiener–Ikehara Tauberian theorem** (and on nothing else): the
structure `LargePrimeInputs`.  Its field `mertensRoots` is unconditional
(`mertensRoots_unconditional`); only `primeCountingUpper` uses the hypothesis. -/
theorem largePrimeInputs_of_wienerIkehara (hWI : WienerIkeharaTheorem) : LargePrimeInputs :=
  largePrimeInputs_of_primeCountingUpper (primeCountingUpper_of_wienerIkehara hWI)

/-- **CONDITIONAL on the Wiener–Ikehara Tauberian theorem**: the analytic input (A2),
i.e. Lemma 3.2 of the manuscript, verbatim as the field
`AnalyticInputs.largePrimeFactor`. -/
theorem largePrimeFactor_of_wienerIkehara (hWI : WienerIkeharaTheorem) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → (N : ℝ) / 5 ≤ ((largePrimeFactorSet N).card : ℝ) :=
  largePrimeFactor_of_inputs (largePrimeInputs_of_wienerIkehara hWI)

/-- **CONDITIONAL on the prime number theorem in the `ψ`-form**: the analytic input (A2). -/
theorem largePrimeFactor_of_pnt_psi
    (h : Filter.Tendsto (fun x : ℝ => Chebyshev.psi x / x) Filter.atTop (nhds 1)) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → (N : ℝ) / 5 ≤ ((largePrimeFactorSet N).card : ℝ) :=
  largePrimeFactor_of_inputs
    (largePrimeInputs_of_primeCountingUpper (primeCountingUpper_of_pnt_psi h))

/-- **CONDITIONAL on the Chebyshev-type bound `θ(x) ≤ c x` with some `c < 1.02`**: the
analytic input (A2).  This is the weakest hypothesis under which (A2) is currently
available. -/
theorem largePrimeFactor_of_theta_le {c : ℝ} (hc : c < 1.02)
    (hθ : ∀ᶠ x : ℝ in Filter.atTop, Chebyshev.theta x ≤ c * x) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → (N : ℝ) / 5 ≤ ((largePrimeFactorSet N).card : ℝ) :=
  largePrimeFactor_of_inputs
    (largePrimeInputs_of_primeCountingUpper (primeCountingUpper_of_theta_le hc hθ))

/-- **CONDITIONAL on Wiener–Ikehara and on the sieve estimate (A3)**: the full bundle
`AnalyticInputs`.  (A1) is unconditional (`PrimeSupply.lean`), (A2) needs only the
`π`-bound, and (A3) is untouched by this file. -/
theorem AnalyticInputs.of_wienerIkehara (hWI : WienerIkeharaTheorem)
    (h3 : ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∃ L₀ : ℕ, ∀ α : ℝ, 0 < α → α ≤ 1 / 2 →
      ∀ L : ℕ, L₀ ≤ L →
        ((smallCofactorSet α L).card : ℝ)
          ≤ C₀ * (α * L + (L : ℝ) / Real.log L + (L : ℝ) ^ ((1 + α) / 2) * (Real.log L) ^ 2)) :
    AnalyticInputs :=
  AnalyticInputs.of_largePrimeInputs (largePrimeInputs_of_wienerIkehara hWI) h3

/-! ## (A2) is unconditional — with the threshold constant `40`, not the manuscript's `8`

The two versions of Lemma 3.2 are kept strictly apart, under unambiguous names:

| name | threshold | status |
| --- | --- | --- |
| `largePrimeFactor_eighth` | `(1/8) i log i` (the manuscript's own) | CONDITIONAL on `LargePrimeInputs`, i.e. on `π(y) ≤ 1.02 y/log y` |
| `largePrimeFactor_fortieth` | `(1/40) i log i` (used downstream) | UNCONDITIONAL |

With the threshold constant `c` the discard step of the proof removes `2κ/c · N` indices,
where `κ` is any constant with `π(y) ≤ κ y/log y` for large `y`, and the bookkeeping needs
`2κ/c ≤ 0.27`.  With `c = 40` the safe explicit value `κ = 2` (`primeCountingUpper_two`,
unconditional) suffices: `2·2/40 = 0.1 ≤ 0.27`.  With `c = 8` one would need `κ ≤ 1.08`,
which is *not* available: mathlib's Chebyshev input is `θ(x) ≤ (log 4) x`, and the passage
to `π` gives only `π(y) ≤ (log 4 + ε) y/log y` for an arbitrary `ε > 0` — no exact
coefficient `log 4` for `π` is claimed anywhere in this development. -/

/-- **UNCONDITIONAL.**  The analytic input (A2) in the form used downstream, i.e. the field
`AnalyticInputs.largePrimeFactor`, with the threshold constant `40`:
`#{1 ≤ i ≤ N : P⁺(f(i)) > (1/40) i log i} ≥ N/5` for all large `N`.

Only the unconditional prime-counting bound `π(y) ≤ 2 y/log y` (`primeCountingUpper_two`,
from mathlib's `θ(x) ≤ (log 4) x`) and the project's unconditional Mertens estimate
`mertensRoots_unconditional` are used; no Tauberian theorem and no form of the prime number
theorem.  The numerical check is `2κ/c = 2·2/40 = 0.1 ≤ 0.27`. -/
theorem largePrimeFactor_fortieth :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → (N : ℝ) / 5 ≤ ((largePrimeFactorSet N).card : ℝ) := by
  have h := largePrimeFactor_of_estimates (c := 40) (kap := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    mertensRoots_unconditional primeCountingUpper_two
  simpa [largePrimeFactorSet] using h

/-- **CONDITIONAL on `LargePrimeInputs`** (i.e. on `π(y) ≤ 1.02 y/log y`).  Lemma 3.2 with
the manuscript's own threshold constant `8`.  This statement is *not* unconditional; see
`largePrimeFactor_fortieth` for the unconditional weakening actually used downstream. -/
theorem largePrimeFactor_eighth (h : LargePrimeInputs) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → (N : ℝ) / 5 ≤ ((largePrimeFactorSetC 8 N).card : ℝ) :=
  largePrimeFactor_of_inputs_eight h

/-- Retained name for `largePrimeFactor_fortieth` (the threshold constant is `40`). -/
theorem largePrimeFactor_unconditional :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → (N : ℝ) / 5 ≤ ((largePrimeFactorSet N).card : ℝ) :=
  largePrimeFactor_fortieth

/-- **UNCONDITIONAL in (A1) and (A2).**  The bundle `AnalyticInputs` needs only the sieve
estimate (A3): the prime supply (A1) is proved in `PrimeSupply.lean` and the large
prime factor estimate (A2) is `largePrimeFactor_fortieth`. -/
theorem AnalyticInputs.of_smallCofactorSieve
    (h3 : ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∃ L₀ : ℕ, ∀ α : ℝ, 0 < α → α ≤ 1 / 2 →
      ∀ L : ℕ, L₀ ≤ L →
        ((smallCofactorSet α L).card : ℝ)
          ≤ C₀ * (α * L + (L : ℝ) / Real.log L + (L : ℝ) ^ ((1 + α) / 2) * (Real.log L) ^ 2)) :
    AnalyticInputs :=
  AnalyticInputs.of_two largePrimeFactor_fortieth h3

end FactorialHypergraph

/-! ## Axiom audit -/

#print axioms FactorialHypergraph.largePrimeInputs_of_wienerIkehara
#print axioms FactorialHypergraph.largePrimeFactor_of_wienerIkehara
#print axioms FactorialHypergraph.largePrimeFactor_of_pnt_psi
#print axioms FactorialHypergraph.largePrimeFactor_of_theta_le
#print axioms FactorialHypergraph.AnalyticInputs.of_wienerIkehara
#print axioms FactorialHypergraph.largePrimeFactor_fortieth
#print axioms FactorialHypergraph.largePrimeFactor_eighth
#print axioms FactorialHypergraph.largePrimeFactor_unconditional
#print axioms FactorialHypergraph.AnalyticInputs.of_smallCofactorSieve
