/-
# Rainbow edge covers and covering congruences

Formalization of Proposition 2.7 of the manuscript: the correspondence between rainbow
edge covers of the factorial-residue hypergraph and compatible systems of covering
congruences, together with the fact that the modulus attached to a rainbow edge cover
is the product of the selected primes and that its logarithm is the weight of the cover.
-/
import FactorialHypergraph.Definitions

namespace FactorialHypergraph

open Finset

variable {L : ℕ}

namespace RainbowCover

/-- The modulus of a rainbow edge cover is the product of the selected primes. -/
theorem modulus_eq_prod (C : RainbowCover L) : C.modulus = ∏ q ∈ C.Q, q := rfl

theorem modulus_pos (C : RainbowCover L) : 0 < C.modulus := by
  refine Finset.prod_pos ?_
  intro q hq
  exact (C.prime_mem q hq).pos

/-- The logarithm of the modulus of a rainbow edge cover equals its weight. -/
theorem log_modulus_eq_weight (C : RainbowCover L) :
    Real.log (C.modulus : ℝ) = C.weight := by
  rw [modulus_eq_prod, weight]
  push_cast
  exact Real.log_prod (fun q hq => by
    exact_mod_cast Nat.cast_ne_zero.mpr (C.prime_mem q hq).pos.ne')

/-- The selected residues are nonzero modulo their colour. -/
theorem not_dvd_res (C : RainbowCover L) {q : ℕ} (hq : q ∈ C.Q) : ¬ (q ∣ C.res q) := by
  obtain ⟨k, hk⟩ := C.fiber_nonempty q hq
  rw [mem_fiber] at hk
  obtain ⟨hkV, hkmod⟩ := hk
  rw [mem_V] at hkV
  intro hdvd
  have hqk : q ∣ k.factorial := (Nat.modEq_zero_iff_dvd).mp
    (hkmod.trans ((Nat.modEq_zero_iff_dvd).mpr hdvd))
  have := (Nat.Prime.dvd_factorial (C.prime_mem q hq)).mp hqk
  have := C.lt_mem q hq
  omega

/-- The primes of a rainbow edge cover are pairwise coprime. -/
theorem pairwise_coprime (C : RainbowCover L) :
    (↑C.Q : Set ℕ).Pairwise (Function.onFun Nat.Coprime id) := by
  intro x hx y hy hxy
  exact (Nat.coprime_primes (C.prime_mem x hx) (C.prime_mem y hy)).mpr hxy

/-- **Chinese remainder theorem for a rainbow edge cover.**  There is a residue class
`A` modulo `M(C)`, coprime to `M(C)`, with `A ≡ res q (mod q)` for every colour `q`. -/
theorem exists_crt_class (C : RainbowCover L) :
    ∃ A : ℕ, (∀ q ∈ C.Q, A ≡ C.res q [MOD q]) ∧ Nat.Coprime A C.modulus := by
  obtain ⟨A, hA⟩ := Nat.chineseRemainderOfFinset C.res id C.Q
    (fun q hq => (C.prime_mem q hq).pos.ne') C.pairwise_coprime
  refine ⟨A, hA, ?_⟩
  rw [modulus_eq_prod, Nat.coprime_prod_right_iff]
  intro q hq
  have hp := C.prime_mem q hq
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
  intro hdvd
  refine C.not_dvd_res hq ?_
  have h0 : A ≡ 0 [MOD q] := (Nat.modEq_zero_iff_dvd).mpr hdvd
  exact (Nat.modEq_zero_iff_dvd).mp ((hA q hq).symm.trans h0)

end RainbowCover

/-! ## Compatible systems of covering congruences -/

/-- A *compatible system of covering congruences* of the shape considered in the
manuscript: a squarefree modulus `M = ∏_{q ∈ Q} q` built from primes `L < q < L!`
together with a residue `A` coprime to `M` such that

* every prime `q ∣ M` carries some `k ∈ V_L` with `A ≡ k! (mod q)`, and
* every `k ∈ V_L` is caught by some prime `q ∣ M`. -/
structure CoveringSystem (L : ℕ) where
  /-- The primes making up the (squarefree) modulus. -/
  Q : Finset ℕ
  /-- The common residue class. -/
  A : ℕ
  prime_mem : ∀ q ∈ Q, Nat.Prime q
  lt_mem : ∀ q ∈ Q, L < q
  mem_lt_factorial : ∀ q ∈ Q, q < L.factorial
  coprime : Nat.Coprime A (∏ q ∈ Q, q)
  hits : ∀ q ∈ Q, ∃ k ∈ V L, A ≡ k.factorial [MOD q]
  covered : ∀ k ∈ V L, ∃ q ∈ Q, A ≡ k.factorial [MOD q]

namespace CoveringSystem

/-- The modulus `M = ∏_{q ∈ Q} q` of a covering system. -/
def modulus (S : CoveringSystem L) : ℕ := ∏ q ∈ S.Q, q

end CoveringSystem

/-- **From rainbow edge covers to covering congruences** (first half of Proposition 2.7).
A rainbow edge cover yields a compatible system of covering congruences with the same
prime set, hence with the same modulus `M(C) = ∏_{q ∈ Q} q` and
`log M = w(C)`. -/
theorem exists_coveringSystem_of_cover (C : RainbowCover L) :
    ∃ S : CoveringSystem L, S.Q = C.Q ∧ S.modulus = C.modulus ∧
      Real.log (S.modulus : ℝ) = C.weight := by
  obtain ⟨A, hA, hcop⟩ := C.exists_crt_class
  refine ⟨{ Q := C.Q, A := A
            prime_mem := C.prime_mem
            lt_mem := C.lt_mem
            mem_lt_factorial := C.mem_lt_factorial
            coprime := hcop
            hits := ?_
            covered := ?_ }, rfl, rfl, C.log_modulus_eq_weight⟩
  · intro q hq
    obtain ⟨k, hk⟩ := C.fiber_nonempty q hq
    rw [mem_fiber] at hk
    exact ⟨k, hk.1, (hA q hq).trans hk.2.symm⟩
  · intro k hk
    obtain ⟨q, hq, hkq⟩ := C.covers k hk
    rw [mem_fiber] at hkq
    exact ⟨q, hq, (hA q hq).trans hkq.2.symm⟩

/-- **From covering congruences to rainbow edge covers** (second half of Proposition 2.7).
A compatible system of covering congruences yields a rainbow edge cover with the same
prime set, hence of weight `log M`. -/
theorem exists_cover_of_coveringSystem (S : CoveringSystem L) :
    ∃ C : RainbowCover L, C.Q = S.Q ∧ C.modulus = S.modulus ∧
      C.weight = Real.log (S.modulus : ℝ) := by
  refine ⟨{ Q := S.Q, res := fun _ => S.A
            prime_mem := S.prime_mem
            lt_mem := S.lt_mem
            mem_lt_factorial := S.mem_lt_factorial
            fiber_nonempty := ?_
            covers := ?_ }, rfl, rfl, ?_⟩
  · intro q hq
    obtain ⟨k, hkV, hk⟩ := S.hits q hq
    exact ⟨k, mem_fiber.mpr ⟨hkV, hk.symm⟩⟩
  · intro k hk
    obtain ⟨q, hq, hkq⟩ := S.covered k hk
    exact ⟨q, hq, mem_fiber.mpr ⟨hk, hkq.symm⟩⟩
  · exact (RainbowCover.log_modulus_eq_weight _).symm

/-! ## `κ(L)` as the logarithm of the least covering modulus -/

/-- The set of moduli of compatible systems of covering congruences. -/
def coveringModuli (L : ℕ) : Set ℕ := {M | ∃ S : CoveringSystem L, S.modulus = M}

/-- `M_min(L)`, the least modulus of a compatible system of covering congruences
(equal to `0` if there is none). -/
noncomputable def Mmin (L : ℕ) : ℕ := sInf (coveringModuli L)

theorem coverWeights_eq_image (L : ℕ) :
    coverWeights L = (fun M : ℕ => Real.log (M : ℝ)) '' (coveringModuli L) := by
  ext w
  constructor
  · rintro ⟨C, rfl⟩
    obtain ⟨S, -, hM, hlog⟩ := exists_coveringSystem_of_cover C
    exact ⟨S.modulus, ⟨S, rfl⟩, hlog⟩
  · rintro ⟨M, ⟨S, rfl⟩, rfl⟩
    obtain ⟨C, -, -, hw⟩ := exists_cover_of_coveringSystem S
    exact ⟨C, hw⟩

/-- The modulus of a compatible system of covering congruences is positive. -/
theorem CoveringSystem.modulus_pos (S : CoveringSystem L) : 0 < S.modulus := by
  refine Finset.prod_pos ?_
  intro q hq
  exact (S.prime_mem q hq).pos

/-- **Proposition 2.7 (equivalence with covering congruences), quantitative form.**
Whenever a compatible system of covering congruences exists, `κ(L) = log M_min(L)`. -/
theorem kappa_eq_log_Mmin (hne : (coveringModuli L).Nonempty) :
    kappa L = Real.log ((Mmin L : ℕ) : ℝ) := by
  have hmem : Mmin L ∈ coveringModuli L := Nat.sInf_mem hne
  have hpos : ∀ M ∈ coveringModuli L, 0 < M := by
    rintro M ⟨S, rfl⟩
    exact S.modulus_pos
  have hle : ∀ M ∈ coveringModuli L, Mmin L ≤ M := fun M hM => Nat.sInf_le hM
  rw [kappa, coverWeights_eq_image]
  refine le_antisymm ?_ ?_
  · refine csInf_le ⟨0, ?_⟩ ⟨Mmin L, hmem, rfl⟩
    rintro w ⟨M, hM, rfl⟩
    exact Real.log_nonneg (by exact_mod_cast (hpos M hM))
  · refine le_csInf ⟨Real.log ((Mmin L : ℕ) : ℝ), Mmin L, hmem, rfl⟩ ?_
    rintro w ⟨M, hM, rfl⟩
    exact Real.log_le_log (by exact_mod_cast hpos _ hmem) (by exact_mod_cast hle M hM)

/-- `κ(L) ≤ log M(C)` for every rainbow edge cover `C`: the weight of any cover is an
upper bound for the minimum weight. -/
theorem kappa_le_of_cover (C : RainbowCover L) : kappa L ≤ Real.log (C.modulus : ℝ) := by
  rw [C.log_modulus_eq_weight]
  refine csInf_le ⟨0, ?_⟩ ⟨C, rfl⟩
  rintro w ⟨C', rfl⟩
  exact Finset.sum_nonneg fun q hq =>
    Real.log_nonneg (by exact_mod_cast (C'.prime_mem q hq).one_lt.le)

end FactorialHypergraph
