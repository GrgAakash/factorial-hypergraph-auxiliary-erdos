/-
# The factorial collision criterion

Formalization of Proposition 2.4 ("collision criterion") of the manuscript together
with the key identity

  `(i+2)! - i! = i!·(i² + 3i + 1)`

and its modular consequences.
-/
import FactorialHypergraph.Definitions

namespace FactorialHypergraph

open Finset

/-! ## Ascending products of consecutive integers -/

/-- `i! · ∏_{r = i+1}^{j} r = j!` for `i ≤ j`. -/
lemma factorial_mul_prod_Ioc {i j : ℕ} (h : i ≤ j) :
    i.factorial * ∏ r ∈ Finset.Ioc i j, r = j.factorial := by
  induction j with
  | zero => simp_all
  | succ n ih =>
      rcases Nat.lt_or_ge i (n + 1) with h' | h'
      · have hin : i ≤ n := Nat.lt_succ_iff.mp h'
        rw [show Finset.Ioc i (n + 1) = insert (n + 1) (Finset.Ioc i n) from
              (Finset.insert_Ioc_right_eq_Ioc_add_one hin).symm]
        rw [Finset.prod_insert (by simp)]
        rw [← mul_assoc, mul_comm (i.factorial) (n + 1), mul_assoc, ih hin,
          Nat.factorial_succ]
      · have : i = n + 1 := le_antisymm h h'
        subst this
        simp

/-! ## The key identity -/

/-- The key identity `(i+2)! - i! = i!·(i² + 3i + 1)` of the manuscript, over `ℕ`
(natural subtraction is harmless since `i! ≤ (i+2)!`). -/
theorem factorial_add_two_sub_factorial (i : ℕ) :
    (i + 2).factorial - i.factorial = i.factorial * fq i := by
  have h : (i + 2).factorial = i.factorial * (i ^ 2 + 3 * i + 2) := by
    simp [Nat.factorial_succ]; ring
  rw [h, fq]
  have : i.factorial * (i ^ 2 + 3 * i + 2) = i.factorial * (i ^ 2 + 3 * i + 1) + i.factorial := by
    ring
  omega

/-- The key identity over `ℤ`, free of truncated subtraction. -/
theorem factorial_add_two_sub_factorial_int (i : ℕ) :
    ((i + 2).factorial : ℤ) - (i.factorial : ℤ) = (i.factorial : ℤ) * (i ^ 2 + 3 * i + 1) := by
  have h : ((i + 2).factorial : ℤ) = (i.factorial : ℤ) * (i ^ 2 + 3 * i + 2) := by
    push_cast [Nat.factorial_succ]
    ring
  rw [h]; ring

/-! ## The collision criterion -/

/-- **Collision criterion** (Proposition 2.4).  For `2 ≤ i ≤ j ≤ L` and a prime `q > L`,
the factorials `i!` and `j!` collide modulo `q` exactly when the ascending product
`∏_{r=i+1}^{j} r` is `1` modulo `q`, equivalently when `q` divides that product minus one. -/
theorem collision_criterion {L i j q : ℕ} (hq : q.Prime) (hqL : L < q)
    (hij : i ≤ j) (hjL : j ≤ L) :
    (i.factorial ≡ j.factorial [MOD q] ↔ (∏ r ∈ Finset.Ioc i j, r) ≡ 1 [MOD q]) ∧
    ((∏ r ∈ Finset.Ioc i j, r) ≡ 1 [MOD q] ↔
      (q : ℤ) ∣ ((∏ r ∈ Finset.Ioc i j, r : ℕ) : ℤ) - 1) := by
  have hiL : i ≤ L := le_trans hij hjL
  -- `q` does not divide `i!`
  have hcop : Nat.Coprime q i.factorial := by
    rw [Nat.Prime.coprime_iff_not_dvd hq]
    intro hdvd
    obtain ⟨p, hp, hple, hpdvd⟩ : ∃ p, p.Prime ∧ p ≤ i ∧ p ∣ i.factorial := by
      exact ⟨q, hq, (Nat.Prime.dvd_factorial hq).mp hdvd, hdvd⟩
    have := (Nat.Prime.dvd_factorial hq).mp hdvd
    omega
  set P : ℕ := ∏ r ∈ Finset.Ioc i j, r with hP
  have hfac : (j.factorial : ℤ) = (i.factorial : ℤ) * (P : ℤ) := by
    rw [hP, ← factorial_mul_prod_Ioc hij]; push_cast; ring
  have hqi : ¬ ((q : ℤ) ∣ (i.factorial : ℤ)) := by
    intro hdvd
    exact (Nat.Prime.coprime_iff_not_dvd hq).mp hcop
      (Int.ofNat_dvd.mp (by exact_mod_cast hdvd))
  have hqp : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  constructor
  · rw [Nat.modEq_iff_dvd, Nat.modEq_iff_dvd, hfac]
    have hrw : (i.factorial : ℤ) * (P : ℤ) - (i.factorial : ℤ)
        = -((i.factorial : ℤ) * ((1 : ℤ) - (P : ℤ))) := by ring
    rw [hrw, dvd_neg]
    constructor
    · intro h
      rcases hqp.dvd_mul.mp h with h1 | h2
      · exact absurd h1 hqi
      · exact h2
    · intro h
      exact Dvd.dvd.mul_left h _
  · rw [Nat.modEq_iff_dvd]
    push_cast
    exact (dvd_sub_comm)

/-- A prime dividing `f(i) = i² + 3i + 1` forces the collision `i! ≡ (i+2)! (mod q)`. -/
theorem factorial_modEq_of_dvd_fq {i q : ℕ} (h : q ∣ fq i) :
    i.factorial ≡ (i + 2).factorial [MOD q] := by
  rw [Nat.modEq_iff_dvd, factorial_add_two_sub_factorial_int]
  have : (q : ℤ) ∣ ((fq i : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr h
  simp only [fq] at this
  push_cast at this ⊢
  exact Dvd.dvd.mul_left this _

/-- Consequently, both `i` and `i+2` lie in the fibre `E_{q, i!}` whenever
`q ∣ f(i)` and `2 ≤ i`, `i + 2 ≤ L`. -/
theorem pair_mem_fiber {L i q : ℕ} (h : q ∣ fq i) (hi : 2 ≤ i) (hiL : i + 2 ≤ L) :
    i ∈ fiber L q i.factorial ∧ (i + 2) ∈ fiber L q i.factorial := by
  refine ⟨?_, ?_⟩
  · exact mem_fiber.mpr ⟨mem_V.mpr ⟨hi, by omega⟩, Nat.ModEq.refl _⟩
  · exact mem_fiber.mpr ⟨mem_V.mpr ⟨by omega, hiL⟩, (factorial_modEq_of_dvd_fq h).symm⟩

end FactorialHypergraph
