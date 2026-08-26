/-
# The example `L = 5`, `n = 329`

A completely explicit example of the auxiliary problem: `329 = 7 · 47` lies in
`(2·5!, 6!] = (240, 720]`, is `5`-rough, and `329 - k!` is composite for `1 ≤ k ≤ 5`:

  `329 - 1 = 328 = 2^3 · 41`,  `329 - 2 = 327 = 3 · 109`,  `329 - 6 = 323 = 17 · 19`,
  `329 - 24 = 305 = 5 · 61`,  `329 - 120 = 209 = 11 · 19`.

All statements here are verified by computation (`decide` kernel evaluation for the
divisibility and comparison checks, `norm_num` for the primality checks).
-/
import FactorialHypergraph.Definitions

namespace FactorialHypergraph

/-- `329` is `5`-rough: none of the primes `2, 3, 5` divides `329 = 7 · 47`. -/
theorem isRough_five_329 : IsRough 5 329 := by
  intro p hp hpd
  by_contra hcon
  push_neg at hcon
  have h2 := hp.two_le
  interval_cases p <;> revert hpd <;> decide

/-- The factorial differences `329 - k!`, `1 ≤ k ≤ 5`, are all composite. -/
theorem factorial_differences_329 :
    ∀ k, 1 ≤ k → k ≤ 5 → ¬ (329 - k.factorial).Prime ∧ 1 < 329 - k.factorial := by
  intro k hk1 hk5
  interval_cases k <;>
    refine ⟨by norm_num [Nat.factorial], by norm_num [Nat.factorial]⟩

/-- **The auxiliary conditions for `L = 5`, `n = 329`.** -/
theorem example_L5_n329 :
    Nat.factorial 5 < 329 ∧ 329 ≤ Nat.factorial 6 ∧ IsRough 5 329 ∧
      ∀ k, 1 ≤ k → k ≤ 5 → ¬ (329 - k.factorial).Prime ∧ 1 < 329 - k.factorial :=
  ⟨by decide, by decide, isRough_five_329, factorial_differences_329⟩

/-- `329` belongs to the finite set counted by the quantitative theorem for `L = 5`. -/
theorem mem_goodSet_329 : 329 ∈ goodSet 5 := by
  rw [mem_goodSet]
  refine ⟨⟨by decide, by decide⟩, isRough_five_329, factorial_differences_329⟩

/-- In particular the set counted by the quantitative theorem is nonempty for `L = 5`. -/
theorem goodSet_five_nonempty : (goodSet 5).Nonempty := ⟨329, mem_goodSet_329⟩

end FactorialHypergraph
