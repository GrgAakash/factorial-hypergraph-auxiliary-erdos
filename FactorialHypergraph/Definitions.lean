/-
# Definitions

Basic definitions for the formalization of the manuscript

  *Factorial-residue hypergraphs and an auxiliary problem of Erdős*

**Important scope remark.**  The manuscript proves the *auxiliary* problem
suggested by Erdős (existence of many pairs `(L, n)` with `L! < n ≤ (L+1)!`,
`n` being `L`-rough and `n - k!` composite for `1 ≤ k ≤ L`).  It does **not**
prove Erdős Problem 1059 (infinitely many primes `p` with `p - k!` composite
for all `1 ≤ k! < p`).  Nothing in this development claims the latter.
-/
import Mathlib

namespace FactorialHypergraph

open Finset

/-! ## The vertex set -/

/-- The vertex set `V_L = {2, 3, …, L}` of the factorial-residue hypergraph. -/
def V (L : ℕ) : Finset ℕ := Finset.Icc 2 L

lemma mem_V {L k : ℕ} : k ∈ V L ↔ 2 ≤ k ∧ k ≤ L := by
  simp [V, Finset.mem_Icc]

/-! ## Factorial-residue edges (fibres) -/

/-- The fibre `E_{q,a} = {k ∈ V_L : k! ≡ a (mod q)}`, i.e. the vertex set incident
to the factorial-residue edge `e_{q,a}` of colour `q`. -/
def fiber (L q a : ℕ) : Finset ℕ := (V L).filter (fun k => k.factorial ≡ a [MOD q])

lemma mem_fiber {L q a k : ℕ} :
    k ∈ fiber L q a ↔ k ∈ V L ∧ k.factorial ≡ a [MOD q] := by
  simp [fiber, Finset.mem_filter]

/-! ## Rainbow edge covers -/

/-- A *rainbow edge cover* of the factorial-residue hypergraph `H_L`: a finite set `Q`
of distinct primes `L < q < L!`, one residue `res q` for each `q ∈ Q` whose fibre is
nonempty, such that the fibres cover the vertex set `V_L`.

Distinctness of the colours is automatic since `Q` is a `Finset` of primes and exactly
one residue is chosen for each colour. -/
structure RainbowCover (L : ℕ) where
  /-- The set of colours (primes) used by the cover. -/
  Q : Finset ℕ
  /-- The residue selected for each colour. -/
  res : ℕ → ℕ
  prime_mem : ∀ q ∈ Q, Nat.Prime q
  lt_mem : ∀ q ∈ Q, L < q
  mem_lt_factorial : ∀ q ∈ Q, q < L.factorial
  fiber_nonempty : ∀ q ∈ Q, (fiber L q (res q)).Nonempty
  covers : ∀ k ∈ V L, ∃ q ∈ Q, k ∈ fiber L q (res q)

namespace RainbowCover

variable {L : ℕ}

/-- The modulus `M(C) = ∏_{q ∈ Q} q` associated with a rainbow edge cover. -/
def modulus (C : RainbowCover L) : ℕ := ∏ q ∈ C.Q, q

/-- The weight `w(C) = ∑_{q ∈ Q} log q` of a rainbow edge cover. -/
noncomputable def weight (C : RainbowCover L) : ℝ := ∑ q ∈ C.Q, Real.log q

end RainbowCover

/-- The set of weights of rainbow edge covers of `H_L`. -/
noncomputable def coverWeights (L : ℕ) : Set ℝ := {w | ∃ C : RainbowCover L, C.weight = w}

/-- `κ(L)`, the minimal weight of a rainbow edge cover of `H_L`
(`sInf` of the empty set is `0` in Lean; all statements below only use the
upper bound `κ(L) ≤ w(C)` for an explicitly constructed cover `C`). -/
noncomputable def kappa (L : ℕ) : ℝ := sInf (coverWeights L)

/-! ## Rough integers -/

/-- `n` is *`L`-rough* if every prime factor of `n` exceeds `L`, i.e. `P⁻(n) > L`. -/
def IsRough (L n : ℕ) : Prop := ∀ p : ℕ, p.Prime → p ∣ n → L < p

/-! ## The integers counted by the quantitative theorem -/

open scoped Classical in
/-- The finite set of integers counted in the quantitative theorem: those
`n ∈ (2·L!, (L+1)!]` that are `L`-rough and for which `n - k!` is composite
(i.e. `1 < n - k!` and `n - k!` is not prime) for every `1 ≤ k ≤ L`.

Natural subtraction is harmless here because `n > 2·L! ≥ 2·k!` for `k ≤ L`;
the conjunct `1 < n - k!` is part of the definition of compositeness and is
recorded explicitly. -/
noncomputable def goodSet (L : ℕ) : Finset ℕ :=
  (Finset.Ioc (2 * L.factorial) ((L + 1).factorial)).filter
    (fun n => IsRough L n ∧ ∀ k, 1 ≤ k → k ≤ L → ¬ (n - k.factorial).Prime ∧ 1 < n - k.factorial)

open scoped Classical in
lemma mem_goodSet {L n : ℕ} :
    n ∈ goodSet L ↔
      (2 * L.factorial < n ∧ n ≤ (L + 1).factorial) ∧
      IsRough L n ∧
      ∀ k, 1 ≤ k → k ≤ L → ¬ (n - k.factorial).Prime ∧ 1 < n - k.factorial := by
  simp [goodSet, Finset.mem_filter, Finset.mem_Ioc, and_assoc]

/-- `L`-roughness follows from a lower bound on the least prime factor. -/
lemma isRough_of_lt_minFac {L n : ℕ} (h : L < n.minFac) : IsRough L n := by
  intro p hp hpn
  exact lt_of_lt_of_le h (Nat.minFac_le_of_dvd hp.two_le hpn)

/-! ## The quadratic `f(t) = t² + 3t + 1` -/

/-- The quadratic `f(i) = i² + 3i + 1` appearing in the key identity
`(i+2)! - i! = i!·(i² + 3i + 1)`. -/
def fq (i : ℕ) : ℕ := i ^ 2 + 3 * i + 1

end FactorialHypergraph
