/-
# The auxiliary conflict graph and the weighted independent-set lemma

Formalization of the auxiliary conflict graph `G_F` of the manuscript and of
Proposition 2.8 (weighted independent-set lemma).

The proof follows the manuscript: a finite graph of maximum degree at most `D`
has a proper colouring with `D + 1` colours (greedy colouring), the colour classes
are independent sets partitioning the vertex set, and one of them carries at least
the average weight.
-/
import FactorialHypergraph.Definitions

namespace FactorialHypergraph

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ## Greedy proper colouring -/

/-- **Greedy colouring.**  A finite graph in which every vertex has degree at most `D`
admits a proper colouring with `D + 1` colours. -/
theorem exists_proper_coloring (G : SimpleGraph α) [DecidableRel G.Adj] (D : ℕ)
    (hdeg : ∀ v, G.degree v ≤ D) :
    ∃ c : α → Fin (D + 1), ∀ x y, G.Adj x y → c x ≠ c y := by
  suffices H : ∀ s : Finset α, ∃ c : α → Fin (D + 1),
      ∀ x ∈ s, ∀ y ∈ s, G.Adj x y → c x ≠ c y by
    obtain ⟨c, hc⟩ := H Finset.univ
    exact ⟨c, fun x y hxy => hc x (Finset.mem_univ x) y (Finset.mem_univ y) hxy⟩
  intro s
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ => 0, by simp⟩
  | insert v t hv ih =>
      obtain ⟨c, hc⟩ := ih
      -- the colours used by the already-coloured neighbours of `v`
      set N : Finset α := t.filter (fun y => G.Adj v y) with hN
      have hNcard : N.card ≤ D := by
        refine le_trans (Finset.card_le_card ?_) (hdeg v)
        intro y hy
        simp only [hN, Finset.mem_filter] at hy
        exact (SimpleGraph.mem_neighborFinset G v y).mpr hy.2
      have hlt : (N.image c).card < Fintype.card (Fin (D + 1)) := by
        have : (N.image c).card ≤ N.card := Finset.card_image_le
        simp only [Fintype.card_fin]
        omega
      obtain ⟨col, hcol⟩ : ∃ col : Fin (D + 1), col ∉ N.image c := by
        by_contra hcon
        push_neg at hcon
        have : (Finset.univ : Finset (Fin (D + 1))) ⊆ N.image c := fun x _ => hcon x
        have := Finset.card_le_card this
        simp only [Finset.card_univ] at this
        omega
      refine ⟨Function.update c v col, ?_⟩
      intro x hx y hy hxy
      have hne : x ≠ y := G.ne_of_adj hxy
      simp only [Finset.mem_insert] at hx hy
      rcases hx with rfl | hx
      · rcases hy with rfl | hy
        · exact absurd rfl hne
        · have hyv : y ≠ x := fun h => hv (h ▸ hy)
          rw [Function.update_self, Function.update_of_ne hyv]
          intro hcolc
          exact hcol (Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr ⟨hy, hxy⟩, hcolc.symm⟩)
      · rcases hy with rfl | hy
        · have hxv : x ≠ y := fun h => hv (h ▸ hx)
          rw [Function.update_self, Function.update_of_ne hxv]
          intro hcolc
          refine hcol (Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hxy.symm⟩, hcolc⟩)
        · have hxv : x ≠ v := fun h => hv (h ▸ hx)
          have hyv : y ≠ v := fun h => hv (h ▸ hy)
          rw [Function.update_of_ne hxv, Function.update_of_ne hyv]
          exact hc x hx y hy hxy

/-! ## The weighted independent-set lemma -/

/-- **Weighted independent-set lemma** (Proposition 2.8).  If the conflict graph has
maximum degree at most `D` and all weights are nonnegative, then some independent set
carries at least a `1/(D+1)` fraction of the total weight. -/
theorem exists_indepSet_weight (G : SimpleGraph α) [DecidableRel G.Adj] (D : ℕ)
    (hdeg : ∀ v, G.degree v ≤ D) (w : α → ℝ) :
    ∃ s : Finset α, (∀ x ∈ s, ∀ y ∈ s, ¬ G.Adj x y) ∧
      ∑ v : α, w v ≤ (D + 1) * ∑ v ∈ s, w v := by
  obtain ⟨c, hc⟩ := exists_proper_coloring G D hdeg
  -- the colour classes partition the vertex set
  have hsum : ∑ j : Fin (D + 1), ∑ v ∈ Finset.univ.filter (fun v => c v = j), w v
      = ∑ v : α, w v := by
    exact Finset.sum_fiberwise Finset.univ c w
  -- one colour class has at least the average weight
  by_contra hcon
  push_neg at hcon
  have hlt : ∀ j : Fin (D + 1),
      ∑ v ∈ Finset.univ.filter (fun v => c v = j), w v < (∑ v : α, w v) / (D + 1) := by
    intro j
    have hj := hcon (Finset.univ.filter (fun v => c v = j))
      (by
        intro x hx y hy hadj
        simp only [Finset.mem_filter] at hx hy
        exact hc x y hadj (hx.2.trans hy.2.symm))
    have hD : (0 : ℝ) < (D : ℝ) + 1 := by positivity
    rw [lt_div_iff₀ hD]
    linarith [hj]
  have := Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty (α := Fin (D + 1))) (fun j _ => hlt j)
  rw [hsum] at this
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  have hD : (0 : ℝ) < (D : ℝ) + 1 := by positivity
  push_cast at this
  rw [mul_comm, div_mul_cancel₀ _ (ne_of_gt hD)] at this
  exact lt_irrefl _ this

/-- Unit-weight form of the independent-set lemma. -/
theorem exists_indepSet_card (G : SimpleGraph α) [DecidableRel G.Adj] (D : ℕ)
    (hdeg : ∀ v, G.degree v ≤ D) :
    ∃ s : Finset α, (∀ x ∈ s, ∀ y ∈ s, ¬ G.Adj x y) ∧
      (Fintype.card α : ℝ) ≤ (D + 1) * s.card := by
  obtain ⟨s, hs, hsum⟩ := exists_indepSet_weight G D hdeg (fun _ => (1 : ℝ))
  refine ⟨s, hs, ?_⟩
  simpa using hsum

/-! ## The auxiliary conflict graph of the manuscript -/

/-- The auxiliary conflict graph `G_F` on a family of triples `F = (q, a, B_F)`:
two distinct members are joined when they have the same prime colour or when their
designated subsets meet. -/
def conflictGraph {ι : Type*} (col : ι → ℕ) (B : ι → Finset ℕ) : SimpleGraph ι where
  Adj x y := x ≠ y ∧ (col x = col y ∨ (B x ∩ B y).Nonempty)
  symm := by
    rintro x y ⟨hne, h⟩
    refine ⟨hne.symm, ?_⟩
    rcases h with h | ⟨z, hz⟩
    · exact Or.inl h.symm
    · exact Or.inr ⟨z, by simp only [Finset.mem_inter] at hz ⊢; exact ⟨hz.2, hz.1⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- An independent set of the conflict graph consists of members with pairwise distinct
colours and pairwise disjoint designated subsets. -/
theorem indepSet_conflictGraph {ι : Type*} [DecidableEq ι] (col : ι → ℕ) (B : ι → Finset ℕ)
    (s : Finset ι) (hs : ∀ x ∈ s, ∀ y ∈ s, ¬ (conflictGraph col B).Adj x y) :
    (∀ x ∈ s, ∀ y ∈ s, x ≠ y → col x ≠ col y) ∧
    (∀ x ∈ s, ∀ y ∈ s, x ≠ y → Disjoint (B x) (B y)) := by
  constructor
  · intro x hx y hy hne hcol
    exact hs x hx y hy ⟨hne, Or.inl hcol⟩
  · intro x hx y hy hne
    rw [Finset.disjoint_iff_inter_eq_empty]
    by_contra hcon
    exact hs x hx y hy ⟨hne, Or.inr (Finset.nonempty_of_ne_empty hcon)⟩

end FactorialHypergraph
