/-
# `LargePrimeInputs.primeCountingUpper`: status and the exact missing theorem

**STATUS: CONDITIONAL ON [the Wiener–Ikehara Tauberian theorem, i.e. the hypothesis
`WienerIkeharaTheorem` below: for `f ≥ 0` whose `L`-series converges on `Re s > 1`, if
`LSeries f - A/(s-1)` extends continuously to `Re s ≥ 1` then
`(∑_{n < x} f n)/x → A`].**

Every implication from that theorem down to the field `primeCountingUpper` is proved here
unconditionally:

```
Wiener–Ikehara  ⟹  ∑_{n<x} Λ n ∼ x  ⟹  ψ x ∼ x  ⟹  (∃ c < 1.02) θ x ≤ c x eventually
                ⟹  π(x) ≤ 1.02 x / log x  ⟹  primeCountingUpper
```

(`vonMangoldt_sum_div_tendsto_one_of_wienerIkehara`, `psi_div_tendsto_one_of_wienerIkehara`,
`theta_le_of_pnt_psi`, `eventually_primeCounting_le_of_theta_le`,
`primeCountingUpper_of_theta_le`, assembled in `primeCountingUpper_of_wienerIkehara`).

This file works exclusively on the field

```
LargePrimeInputs.primeCountingUpper : ∃ y₀ : ℕ, ∀ y : ℕ, y₀ ≤ y →
  ((primesLE y).card : ℝ) ≤ 1.02 * (y : ℝ) / Real.log y
```

of `FactorialHypergraph/LargePrimeFactors.lean`.  Nothing else is modified: the statement of
(A2), the structure `LargePrimeInputs`, and every numerical constant are untouched, and
no `sorry`, `admit`, opaque placeholder or user-defined axiom is introduced.

## 1. What the pinned mathlib revision contains

Lean `4.28.0`, mathlib rev `8f9d9cff6bd728b17a24e163c9402775d9e6a365`.  An exhaustive
search of that revision for prime-counting / prime-number-theorem material yields exactly
the following declarations (file `Mathlib/NumberTheory/Chebyshev.lean`, plus
`Mathlib/NumberTheory/PrimeCounting.lean`):

* `Chebyshev.theta_le_log4_mul_x : 0 ≤ x → θ x ≤ Real.log 4 * x`;
* `Chebyshev.psi_le_const_mul_self`;
* `Chebyshev.primeCounting_eq_theta_div_log_add_integral :
     2 ≤ x → (π ⌊x⌋₊ : ℝ) = θ x / log x + ∫ t in 2..x, θ t / (t * log t ^ 2)`
  (Abel summation);
* `Chebyshev.integral_theta_div_log_sq_isLittleO :
     (fun x => ∫ t in 2..x, θ t / (t * log t ^ 2)) =o[atTop] (fun x => x / log x)`;
* `Chebyshev.eventually_primeCounting_le : 0 < ε → ∀ᶠ x in atTop,
     (π ⌊x⌋₊ : ℝ) ≤ (Real.log 4 + ε) * x / log x`;
* `Nat.primeCounting'_add_le` (a Legendre-sieve bound, of quality `x / log log x`);
* `Nat.primorial_le_4_pow`, `Nat.nth_prime`-type results, Bertrand's postulate.

`Chebyshev.eventually_primeCounting_le` is the strongest prime-counting upper bound in
mathlib, and its constant is `log 4 + ε = 1.3862…`, which does **not** imply the required
`1.02`.  There is **no** prime number theorem in mathlib: the only file mentioning it is
`Mathlib/NumberTheory/LSeries/Nonvanishing.lean`, which proves the non-vanishing of
Dirichlet `L`-functions on `Re s = 1` and states in its module docstring that these
results *are prerequisites for* the Prime Number Theorem.  No Tauberian theorem
(Wiener–Ikehara, Newman, Ingham) exists in the revision — the string appears only in a
docstring of `Mathlib/NumberTheory/LSeries/PrimesInAP.lean` describing an auxiliary
function "used, e.g., with the Wiener–Ikehara Theorem".  Consequently no specialization
of an existing mathlib theorem can give the constant `1.02`.

## 2. The earliest exact missing theorem

The earliest theorem of the chain that mathlib does not contain is the **Wiener–Ikehara
Tauberian theorem** (`WienerIkeharaTheorem` below).  Everything after it is proved here.
In particular the analytic continuation input that the Tauberian theorem is applied to
*is* in mathlib: `ArithmeticFunction.vonMangoldt.eqOn_LFunctionResidueClassAux` and
`ArithmeticFunction.vonMangoldt.continuousOn_LFunctionResidueClassAux` say that
`LSeries Λ (s) - 1/(s-1)` (case `q = 1`) extends continuously to `Re s ≥ 1`, resting on
`Mathlib/NumberTheory/LSeries/Nonvanishing.lean`.  What is absent is the Tauberian step
itself; mathlib's own docstring for `LFunctionResidueClassAux` describes it as "the
auxiliary function used, e.g., with the Wiener–Ikehara Theorem", which is not formalised
in the revision.

The intermediate statement through which the chain passes is:

> **(M)**  There is a constant `c < 1.02` with `θ x ≤ c * x` for all sufficiently large
> `x`, where `θ = Chebyshev.theta`.

In Lean: the hypothesis `hθ : ∀ᶠ x : ℝ in atTop, Chebyshev.theta x ≤ c * x` of
`theorem primeCountingUpper_of_theta_le` below.  It is also recorded separately because
it is much weaker than the Prime Number Theorem, yet still out of reach of the
elementary methods:

* mathlib proves (M) only with `c = log 4 = 1.3862…` (`Chebyshev.theta_le_log4_mul_x`),
  which is far above `1.02`.
* Chebyshev's own method (the combination `T(x) − T(x/2) − T(x/3) − T(x/5) + T(x/30)`)
  gives `limsup ψ(x)/x ≤ (6/5)·A = 1.10555…`, with
  `A = log 2/2 + log 3/3 + log 5/5 − log 30/30 = 0.92129…`; Sylvester's refinement of the
  same method reaches `1.04423…`.  Both are still above `1.02`, so no finite
  Chebyshev–Sylvester combination of the classical kind supplies (M); Diamond and Erdős
  showed that constants arbitrarily close to `1` *are* reachable by elementary
  combinations, but their argument is non-constructive and itself invokes the Prime
  Number Theorem.  The classical explicit bound `θ(x) < 1.01624 x` (Rosser–Schoenfeld)
  rests on large-scale numerical verification together with zero-free-region input.
* Hence, in practice, (M) is obtained from the **Prime Number Theorem**
  `Tendsto (fun x => θ x / x) atTop (𝓝 1)`, which mathlib does not have, and the Prime
  Number Theorem in turn from Wiener–Ikehara.  Both chains `PNT ⟹ (M) ⟹
  primeCountingUpper` and `Wiener–Ikehara ⟹ PNT` are proved in this file
  (`theta_le_of_pnt_theta`, `theta_le_of_pnt_psi`, `primeCountingUpper_of_theta_le`,
  `primeCountingUpper_of_pnt_theta`, `primeCountingUpper_of_pnt_psi`,
  `primeCountingUpper_of_pnt_primeCounting`, `psi_div_tendsto_one_of_wienerIkehara`).

## 3. What is proved unconditionally here

* `card_primesLE_eq_primeCounting`: the project's `primesLE` counting function is
  mathlib's `Nat.primeCounting` (so the conventions and coercions of
  `LargePrimeFactors.lean` are matched exactly).
* `eventually_primeCounting_le_of_theta_le` : the real-variable form,
  `(π ⌊x⌋₊ : ℝ) ≤ 1.02 * x / log x` eventually, from (M).
* `primeCountingUpper_of_theta_le` : the exact statement of the field
  `LargePrimeInputs.primeCountingUpper`, from (M).
* `primeCountingUpper_log4` : **unconditionally**, the same bound with the constant
  `1.3863` (`= log 4`), i.e. exactly the strength mathlib supplies today.
* `theta_le_of_pnt_theta`, `theta_le_of_pnt_psi`: (M) from either standard form of PNT.
* `primeCountingUpper_of_pnt_theta`, `primeCountingUpper_of_pnt_psi`,
  `primeCountingUpper_of_pnt_primeCounting`: the field, from PNT in the `θ`, `ψ` and `π`
  forms respectively.
* `vonMangoldt_sum_div_tendsto_one_of_wienerIkehara`,
  `psi_div_tendsto_one_of_wienerIkehara`: the Prime Number Theorem from Wiener–Ikehara,
  using mathlib's analytic continuation of `-ζ'/ζ`.
* `primeCountingUpper_of_wienerIkehara` (and `primeCountingUpper_of_wienerIkehara'`, with
  the hypothesis spelled out inline): the field, from Wiener–Ikehara alone.

No new field, structure or axiom is introduced, and `LargePrimeInputs` is *not* assumed
anywhere in this file.
-/
import FactorialHypergraph.LargePrimeFactors
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.PrimesInAP

namespace FactorialHypergraph

open Filter Chebyshev

/-! ## Matching the conventions of `LargePrimeFactors.lean` -/

/-- The project's counting function `#{p ≤ n : p prime}` is mathlib's `Nat.primeCounting`. -/
lemma card_primesLE_eq_primeCounting (n : ℕ) : (primesLE n).card = Nat.primeCounting n := by
  simp [primesLE, Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]

/-! ## From a Chebyshev `θ`-bound with constant `< 1.02` to the required `π`-bound -/

/-- **Real-variable form, general constant.**  If `θ x ≤ c x` eventually and `c < b`,
then `π(x) ≤ b x / log x` for all large real `x`.

The proof is Abel summation (`Chebyshev.primeCounting_eq_theta_div_log_add_integral`)
together with the mathlib estimate `Chebyshev.integral_theta_div_log_sq_isLittleO`,
which shows that the secondary term is `o(x / log x)`. -/
theorem eventually_primeCounting_le_of_theta_le' {b c : ℝ} (hc : c < b)
    (hθ : ∀ᶠ x : ℝ in atTop, θ x ≤ c * x) :
    ∀ᶠ x : ℝ in atTop, ((⌊x⌋₊.primeCounting : ℝ)) ≤ b * x / Real.log x := by
  set ε : ℝ := (b - c) / 2 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  have hI := Chebyshev.integral_theta_div_log_sq_isLittleO.bound hεpos
  filter_upwards [eventually_ge_atTop (2 : ℝ), hθ, hI] with x hx hθx hIx
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hx0 : (0 : ℝ) < x := by linarith
  rw [Real.norm_of_nonneg (show (0 : ℝ) ≤ x / Real.log x by positivity)] at hIx
  rw [Chebyshev.primeCounting_eq_theta_div_log_add_integral hx]
  have h1 : θ x / Real.log x ≤ c * x / Real.log x := by gcongr
  have h2 : (∫ t in (2 : ℝ)..x, θ t / (t * Real.log t ^ 2)) ≤ ε * (x / Real.log x) :=
    le_trans (Real.le_norm_self _) hIx
  have h3 : c * x / Real.log x + ε * (x / Real.log x) = (c + ε) * x / Real.log x := by
    field_simp
  have h4 : (c + ε) * x / Real.log x ≤ b * x / Real.log x := by
    gcongr
    rw [hε]; linarith
  linarith

/-- **Real-variable form** with the constant `1.02` required by the field. -/
theorem eventually_primeCounting_le_of_theta_le {c : ℝ} (hc : c < 1.02)
    (hθ : ∀ᶠ x : ℝ in atTop, θ x ≤ c * x) :
    ∀ᶠ x : ℝ in atTop, ((⌊x⌋₊.primeCounting : ℝ)) ≤ 1.02 * x / Real.log x :=
  eventually_primeCounting_le_of_theta_le' hc hθ

/-- **Natural-number form, general constant.**  If `θ x ≤ c x` eventually and `c < b`,
then `#{p ≤ y : p prime} ≤ b y / log y` for all large natural `y`. -/
theorem primeCountingUpper_const_of_theta_le {b c : ℝ} (hc : c < b)
    (hθ : ∀ᶠ x : ℝ in atTop, θ x ≤ c * x) :
    ∃ y₀ : ℕ, ∀ y : ℕ, y₀ ≤ y →
      ((primesLE y).card : ℝ) ≤ b * (y : ℝ) / Real.log y := by
  obtain ⟨X, hX⟩ := (eventually_primeCounting_le_of_theta_le' hc hθ).exists_forall_of_atTop
  refine ⟨⌈X⌉₊, fun y hy => ?_⟩
  have hXy : X ≤ (y : ℝ) := le_trans (Nat.le_ceil X) (by exact_mod_cast hy)
  have hy' := hX (y : ℝ) hXy
  rw [Nat.floor_natCast] at hy'
  rwa [card_primesLE_eq_primeCounting]

/-- **The field `LargePrimeInputs.primeCountingUpper`, verbatim, from the missing
estimate (M).**  Everything except the hypothesis `hθ` is proved unconditionally. -/
theorem primeCountingUpper_of_theta_le {c : ℝ} (hc : c < 1.02)
    (hθ : ∀ᶠ x : ℝ in atTop, θ x ≤ c * x) :
    ∃ y₀ : ℕ, ∀ y : ℕ, y₀ ≤ y →
      ((primesLE y).card : ℝ) ≤ 1.02 * (y : ℝ) / Real.log y :=
  primeCountingUpper_const_of_theta_le hc hθ

/-! ## What is unconditional today: the same bound with the constant `log 4 + ε`

This is the exact strength that the pinned mathlib revision supplies, recorded here in
the conventions of `LargePrimeFactors.lean` so that the size of the gap is explicit:
`1.3863 > 1.02`. -/

/-- **UNCONDITIONAL.**  `#{p ≤ y : p prime} ≤ 1.3863 · y / log y` for all large `y`.
The constant `1.3863` is a value *strictly greater* than `log 4 = 1.38629…`; mathlib's
Chebyshev input is `θ(x) ≤ (log 4) x`, and the passage from `θ` to `π` yields only
`log 4 + ε` for an arbitrary `ε > 0`, so the exact coefficient `log 4` is **not** claimed
for `π`.  In any case the constant is *not* below `1.02`, which is precisely why the
manuscript's constant `8` in Lemma 3.2 remains conditional. -/
theorem primeCountingUpper_log4 :
    ∃ y₀ : ℕ, ∀ y : ℕ, y₀ ≤ y →
      ((primesLE y).card : ℝ) ≤ 1.3863 * (y : ℝ) / Real.log y := by
  refine primeCountingUpper_const_of_theta_le (c := Real.log 4) ?_ ?_
  · have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    rw [h4]
    have := Real.log_two_lt_d9
    linarith
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    exact Chebyshev.theta_le_log4_mul_x hx

/-- **UNCONDITIONAL, with a safe explicit constant.**  `#{p ≤ y : p prime} ≤ 2 · y / log y`
for all large `y`.

This is the form used downstream (see `largePrimeFactor_fortieth`).  It is deliberately
stated with the round constant `κ = 2` rather than with `log 4 = 1.38629…`: mathlib's
Chebyshev input is `θ(x) ≤ (log 4) x`, and the passage from `θ` to `π` costs an
arbitrarily small but positive amount, so no *exact* coefficient `log 4` is claimed for
`π`; any constant `> log 4` is available, and `2` leaves a wide margin. -/
theorem primeCountingUpper_two :
    ∃ y₀ : ℕ, ∀ y : ℕ, y₀ ≤ y →
      ((primesLE y).card : ℝ) ≤ 2 * (y : ℝ) / Real.log y := by
  refine primeCountingUpper_const_of_theta_le (c := Real.log 4) ?_ ?_
  · have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    rw [h4]
    have := Real.log_two_lt_d9
    linarith
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    exact Chebyshev.theta_le_log4_mul_x hx

/-! ## The missing estimate (M) from the Prime Number Theorem -/

/-- The Prime Number Theorem in the form `θ x / x → 1` implies the missing estimate (M)
with the constant `c = 1.01 < 1.02`. -/
theorem theta_le_of_pnt_theta (h : Tendsto (fun x : ℝ => θ x / x) atTop (nhds 1)) :
    ∀ᶠ x : ℝ in atTop, θ x ≤ 1.01 * x := by
  have hlt : ∀ᶠ x : ℝ in atTop, θ x / x < 1.01 :=
    h.eventually_lt_const (by norm_num)
  filter_upwards [eventually_gt_atTop (0 : ℝ), hlt] with x hx hxlt
  rw [div_lt_iff₀ hx] at hxlt
  nlinarith

/-- The Prime Number Theorem in the form `ψ x / x → 1` implies the missing estimate (M)
with the constant `c = 1.01 < 1.02` (using `Chebyshev.theta_le_psi`). -/
theorem theta_le_of_pnt_psi (h : Tendsto (fun x : ℝ => ψ x / x) atTop (nhds 1)) :
    ∀ᶠ x : ℝ in atTop, θ x ≤ 1.01 * x := by
  have hlt : ∀ᶠ x : ℝ in atTop, ψ x / x < 1.01 :=
    h.eventually_lt_const (by norm_num)
  filter_upwards [eventually_gt_atTop (0 : ℝ), hlt] with x hx hxlt
  rw [div_lt_iff₀ hx] at hxlt
  nlinarith [Chebyshev.theta_le_psi x]

/-! ## The Prime Number Theorem from the Wiener–Ikehara Tauberian theorem

This is the last link of the chain, and it is what pins the *earliest* missing theorem
down to the Wiener–Ikehara Tauberian theorem: mathlib already contains the analytic
continuation input (the continuity, on `Re s ≥ 1`, of `-ζ'/ζ (s) - 1/(s-1)`, in the form
`ArithmeticFunction.vonMangoldt.continuousOn_LFunctionResidueClassAux` together with
`ArithmeticFunction.vonMangoldt.eqOn_LFunctionResidueClassAux`, which rest on the
non-vanishing results of `Mathlib/NumberTheory/LSeries/Nonvanishing.lean`), but it
contains no Tauberian theorem. -/

/-- **The Wiener–Ikehara Tauberian theorem**, stated as a hypothesis (this is the
earliest theorem of the chain that the pinned mathlib revision does not contain):
if `f ≥ 0`, its `L`-series converges on `Re s > 1`, and that `L`-series minus the
principal part `A/(s-1)` of its pole at `s = 1` extends continuously to `Re s ≥ 1`, then
`∑_{n < x} f n ∼ A x`.

The convergence hypothesis is not decorative: mathlib defines `LSeries` as a `tsum`,
whose value is `0` when the series diverges, so without it the statement would be *false*
(take `f n = 2 ^ n`, `A = 0`, `F = 0`: the `L`-series diverges for every `s`, hence is
identically `0` on `Re s > 1`, while `(∑_{n < x} 2 ^ n) / x → ∞`).  With it, this is the
classical Wiener–Ikehara theorem. -/
def WienerIkeharaTheorem : Prop :=
  ∀ (f : ℕ → ℝ) (A : ℝ) (F : ℂ → ℂ), (∀ n, 0 ≤ f n) →
    (∀ s : ℂ, 1 < s.re → LSeriesSummable (fun n => (f n : ℂ)) s) →
    Set.EqOn F (fun s => LSeries (fun n => (f n : ℂ)) s - (A : ℂ) / (s - 1)) {s | 1 < s.re} →
    ContinuousOn F {s | 1 ≤ s.re} →
    Filter.Tendsto (fun x : ℝ => (∑ n ∈ Finset.range ⌊x⌋₊, f n) / x) atTop (nhds A)

/-- Wiener–Ikehara applied to the von Mangoldt function (via mathlib's analytic
continuation of `-ζ'/ζ` past `s = 1`) gives `∑_{n < x} Λ n ∼ x`. -/
theorem vonMangoldt_sum_div_tendsto_one_of_wienerIkehara (hWI : WienerIkeharaTheorem) :
    Tendsto (fun x : ℝ => (∑ n ∈ Finset.range ⌊x⌋₊, ArithmeticFunction.vonMangoldt n) / x)
      atTop (nhds 1) := by
  have hres : (fun n : ℕ => ArithmeticFunction.vonMangoldt.residueClass (0 : ZMod 1) n)
      = fun n : ℕ => ArithmeticFunction.vonMangoldt n := by
    funext n
    simp [ArithmeticFunction.vonMangoldt.residueClass,
      Subsingleton.elim ((n : ZMod 1)) (0 : ZMod 1)]
  refine hWI (fun n => ArithmeticFunction.vonMangoldt n) 1
    (ArithmeticFunction.vonMangoldt.LFunctionResidueClassAux (0 : ZMod 1))
    (fun _ => ArithmeticFunction.vonMangoldt_nonneg)
    (fun s hs => ArithmeticFunction.LSeriesSummable_vonMangoldt hs) ?_
    (ArithmeticFunction.vonMangoldt.continuousOn_LFunctionResidueClassAux _)
  have h := ArithmeticFunction.vonMangoldt.eqOn_LFunctionResidueClassAux
    (q := 1) (a := (0 : ZMod 1)) (isUnit_of_subsingleton _)
  intro s hs
  simpa [hres] using h hs

/-- **The Prime Number Theorem in the `ψ`-form, from Wiener–Ikehara.** -/
theorem psi_div_tendsto_one_of_wienerIkehara (hWI : WienerIkeharaTheorem) :
    Tendsto (fun x : ℝ => ψ x / x) atTop (nhds 1) := by
  have h1 := vonMangoldt_sum_div_tendsto_one_of_wienerIkehara hWI
  have hlog : Tendsto (fun x : ℝ => Real.log x / x) atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have h2 : Tendsto (fun x : ℝ => ArithmeticFunction.vonMangoldt ⌊x⌋₊ / x) atTop (nhds 0) := by
    refine squeeze_zero' ?_ ?_ hlog
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg hx.le
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      have hx0 : (0 : ℝ) < x := by linarith
      have hfl : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
      have hfl' : (1 : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hfl
      have h3 : ArithmeticFunction.vonMangoldt ⌊x⌋₊ ≤ Real.log x :=
        le_trans ArithmeticFunction.vonMangoldt_le_log
          (Real.log_le_log (by linarith) (Nat.floor_le hx0.le))
      gcongr
  have h4 := h1.add h2
  rw [add_zero] at h4
  refine h4.congr fun x => ?_
  rw [Chebyshev.psi_eq_sum_Icc, ← Nat.range_succ_eq_Icc_zero, Finset.sum_range_succ, add_div]

/-! ## The conditional versions of the field -/

/-- **CONDITIONAL** on the Wiener–Ikehara Tauberian theorem — and on nothing else: the
field `LargePrimeInputs.primeCountingUpper`,
`∃ y₀, ∀ y ≥ y₀, #{p ≤ y : p prime} ≤ 1.02 · y / log y`. -/
theorem primeCountingUpper_of_wienerIkehara (hWI : WienerIkeharaTheorem) :
    ∃ y₀ : ℕ, ∀ y : ℕ, y₀ ≤ y →
      ((primesLE y).card : ℝ) ≤ 1.02 * (y : ℝ) / Real.log y :=
  primeCountingUpper_of_theta_le (by norm_num)
    (theta_le_of_pnt_psi (psi_div_tendsto_one_of_wienerIkehara hWI))

/-- The same statement as `primeCountingUpper_of_wienerIkehara`, with the Wiener–Ikehara
hypothesis written out inline rather than through the abbreviation
`WienerIkeharaTheorem`. -/
theorem primeCountingUpper_of_wienerIkehara'
    (hWI : ∀ (f : ℕ → ℝ) (A : ℝ) (F : ℂ → ℂ), (∀ n, 0 ≤ f n) →
      (∀ s : ℂ, 1 < s.re → LSeriesSummable (fun n => (f n : ℂ)) s) →
      Set.EqOn F (fun s => LSeries (fun n => (f n : ℂ)) s - (A : ℂ) / (s - 1)) {s | 1 < s.re} →
      ContinuousOn F {s | 1 ≤ s.re} →
      Filter.Tendsto (fun x : ℝ => (∑ n ∈ Finset.range ⌊x⌋₊, f n) / x) atTop (nhds A)) :
    ∃ y₀ : ℕ, ∀ y : ℕ, y₀ ≤ y →
      ((primesLE y).card : ℝ) ≤ 1.02 * (y : ℝ) / Real.log y :=
  primeCountingUpper_of_wienerIkehara hWI

/-- **CONDITIONAL** on the Prime Number Theorem in the `θ`-form: the field
`LargePrimeInputs.primeCountingUpper`. -/
theorem primeCountingUpper_of_pnt_theta (h : Tendsto (fun x : ℝ => θ x / x) atTop (nhds 1)) :
    ∃ y₀ : ℕ, ∀ y : ℕ, y₀ ≤ y →
      ((primesLE y).card : ℝ) ≤ 1.02 * (y : ℝ) / Real.log y :=
  primeCountingUpper_of_theta_le (by norm_num) (theta_le_of_pnt_theta h)

/-- **CONDITIONAL** on the Prime Number Theorem in the `ψ`-form: the field
`LargePrimeInputs.primeCountingUpper`. -/
theorem primeCountingUpper_of_pnt_psi (h : Tendsto (fun x : ℝ => ψ x / x) atTop (nhds 1)) :
    ∃ y₀ : ℕ, ∀ y : ℕ, y₀ ≤ y →
      ((primesLE y).card : ℝ) ≤ 1.02 * (y : ℝ) / Real.log y :=
  primeCountingUpper_of_theta_le (by norm_num) (theta_le_of_pnt_psi h)

/-- **CONDITIONAL** on the Prime Number Theorem in the `π`-form
`π(x) log x / x → 1`: the field `LargePrimeInputs.primeCountingUpper`.  (Here no
Chebyshev function is needed at all.) -/
theorem primeCountingUpper_of_pnt_primeCounting
    (h : Tendsto (fun x : ℝ => (⌊x⌋₊.primeCounting : ℝ) * Real.log x / x) atTop (nhds 1)) :
    ∃ y₀ : ℕ, ∀ y : ℕ, y₀ ≤ y →
      ((primesLE y).card : ℝ) ≤ 1.02 * (y : ℝ) / Real.log y := by
  have hlt : ∀ᶠ x : ℝ in atTop, (⌊x⌋₊.primeCounting : ℝ) * Real.log x / x < 1.02 :=
    h.eventually_lt_const (by norm_num)
  obtain ⟨X, hX⟩ :=
    ((eventually_gt_atTop (2 : ℝ)).and hlt).exists_forall_of_atTop
  refine ⟨⌈X⌉₊, fun y hy => ?_⟩
  have hXy : X ≤ (y : ℝ) := le_trans (Nat.le_ceil X) (by exact_mod_cast hy)
  obtain ⟨hy2, hylt⟩ := hX (y : ℝ) hXy
  have hlog : 0 < Real.log (y : ℝ) := Real.log_pos (by linarith)
  rw [div_lt_iff₀ (by linarith : (0:ℝ) < (y : ℝ))] at hylt
  rw [card_primesLE_eq_primeCounting, le_div_iff₀ hlog]
  rw [Nat.floor_natCast] at hylt
  linarith

end FactorialHypergraph

/-! ## Axiom audit for the theorems exported by this file -/

#print axioms FactorialHypergraph.card_primesLE_eq_primeCounting
#print axioms FactorialHypergraph.eventually_primeCounting_le_of_theta_le'
#print axioms FactorialHypergraph.eventually_primeCounting_le_of_theta_le
#print axioms FactorialHypergraph.primeCountingUpper_const_of_theta_le
#print axioms FactorialHypergraph.primeCountingUpper_of_theta_le
#print axioms FactorialHypergraph.primeCountingUpper_log4
#print axioms FactorialHypergraph.primeCountingUpper_two
#print axioms FactorialHypergraph.theta_le_of_pnt_theta
#print axioms FactorialHypergraph.theta_le_of_pnt_psi
#print axioms FactorialHypergraph.primeCountingUpper_of_pnt_theta
#print axioms FactorialHypergraph.primeCountingUpper_of_pnt_psi
#print axioms FactorialHypergraph.primeCountingUpper_of_pnt_primeCounting
#print axioms FactorialHypergraph.vonMangoldt_sum_div_tendsto_one_of_wienerIkehara
#print axioms FactorialHypergraph.psi_div_tendsto_one_of_wienerIkehara
#print axioms FactorialHypergraph.primeCountingUpper_of_wienerIkehara
#print axioms FactorialHypergraph.primeCountingUpper_of_wienerIkehara'
