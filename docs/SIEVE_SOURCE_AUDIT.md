STATUS: SOURCE MATCH VERIFIED — THEOREM 18.11(a)

# External-source audit of the Lean interface `UpperBoundSieveDimOne`

This report supersedes the earlier internal-only version of this audit (whose status line was
`AUDIT PASS — INTERNAL LEAN CHECK ONLY; SOURCE MATCH UNVERIFIED`).  The cited source has now
been read directly and the source match has been carried out.  The earlier internal audit of
the *application* of the interface is retained unchanged in Appendices A and B.

Scope: the single remaining external hypothesis of the formalisation of the **auxiliary**
problem suggested by Erdős (Theorems 1.1, 1.2 and the auxiliary existence statement of the
manuscript `Aug25.tex`).  This is **not** Erdős Problem 1059: no primality of the constructed
`n` is asserted anywhere, and none is proved.

The fundamental lemma of sieve theory is **not** formalized in Lean here, and this report does
not claim that it is.

Environment: Lean `4.28.0`; mathlib revision `8f9d9cff6bd728b17a24e163c9402775d9e6a365`
(`lean-toolchain`, `lake-manifest.json`).

---

## 0. Source identification

* **Bibliographic identification.** Dimitris Koukoulopoulos, *The Distribution of Prime
  Numbers*, Graduate Studies in Mathematics **203**, American Mathematical Society.
* **Version used.** The author-hosted **preliminary version**, made available with the
  permission of the AMS.  Its title page carries the notice that it is a preliminary version
  of the book published by the AMS, made available with the permission of the AMS.
* **Exact URL.** `https://dms.umontreal.ca/~koukoulo/documents/publications/primes.pdf`
* **How it was read.** The PDF itself was downloaded and its text extracted, not search
  snippets and not the manuscript's paraphrase.  The file has 367 PDF pages; printed page `n`
  is PDF page `n + 10`.  Locations used:

  | Item | Printed page | PDF page |
  | --- | --- | --- |
  | Chapter 18, *The axioms of sieve theory*: definition of `S(A, P)` and of the weighted set-up | 182 | 192 |
  | `A_d` and Möbius inversion (18.1)–(18.2) | 184 | 194 |
  | **Axiom 1**, `r_d := A_d − X ν(d)/d`, density `δ(d) = ν(d)/d ∈ [0,1]` (18.5) | 185 | 195 |
  | bound `ν(p) ≤ k` (18.9) | 186 | 196 |
  | **Axiom 2** (the Iwaniec condition) | 187 | 197 |
  | **Axiom 2′**, and **Axiom 3** | 188 | 198 |
  | **Theorem 18.11**, the Fundamental Lemma of Sieve Theory | 190 | 200 |
  | **Theorem 19.1** (fundamental lemma, II) | 195 | 205 |
  | Proof of Theorem 18.11 assuming Theorem 19.1 | 196 | 206 |

Only the precise hypotheses and conclusions needed for source matching are recorded below; no
long passage of the book is reproduced.

---

## 1. Verbatim Lean side

### 1.1 The declaration, verbatim

From `FactorialHypergraph/A3Sieve.lean` (auxiliary definition first, then the interface; copied
character for character from the source file):

```lean
/-- The set of squarefree numbers that are products of primes of `P`, i.e. the divisors of
`∏_{ℓ ∈ P} ℓ`. -/
def sieveDivisors (P : Finset ℕ) : Finset ℕ := P.powerset.image (fun t => ∏ ℓ ∈ t, ℓ)

open scoped Classical in
def UpperBoundSieveDimOne : Prop :=
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
        (∀ w : ℝ, 2 ≤ w →
          ∑ ℓ ∈ P with (((ℓ : ℕ) : ℝ) ≤ w), rho ℓ * Real.log ℓ / (ℓ : ℝ) ≤ Real.log w + C₁) →
        (∀ w₁ w₂ : ℝ, 2 ≤ w₁ → w₁ ≤ w₂ →
          ∑ ℓ ∈ P with (w₁ < ((ℓ : ℕ) : ℝ) ∧ ((ℓ : ℕ) : ℝ) ≤ w₂),
              rho ℓ * Real.log ℓ / (ℓ : ℝ)
            ≤ Real.log (w₂ / w₁) + C₁) →
        z ^ (10 : ℕ) ≤ D →
        ∑ n ∈ A with (∀ ℓ ∈ P, ¬ (ℓ ∣ n)), a n
          ≤ C * (X * ∏ ℓ ∈ P, (1 - rho ℓ / (ℓ : ℝ))
              + ∑ d ∈ sieveDivisors P with (((d : ℕ) : ℝ) ≤ D),
                  |(∑ n ∈ A with (d ∣ n), a n) - X * rho d / (d : ℝ)|)
```

### 1.2 Literal mathematical translation

For all real constants `C₁ ≥ 0`, `k ≥ 1`, `0 < ε < 1` there exists `C = C(C₁, k, ε) > 0` such
that the following holds, in this quantifier order (`C` is chosen **before** all data).

Let `A ⊆ ℕ` be a finite set of **positive** integers, let `(a_n)_{n ∈ ℕ}` be real weights with
`a_n ≥ 0` for all `n` and `a_n = 0` for `n ∉ A`, and put `X = ∑_{n ∈ A} a_n`.  Let `P` be a
finite set of primes with `ℓ ≤ z` for all `ℓ ∈ P`, where `z ≥ 2`.  Let `ρ : ℕ → ℝ` satisfy,
for every `ℓ ∈ P`,

  `0 ≤ ρ(ℓ) ≤ k`,   `ρ(ℓ)/ℓ ≤ 1 − ε`,

and `ρ(∏_{ℓ ∈ t} ℓ) = ∏_{ℓ ∈ t} ρ(ℓ)` for every `t ⊆ P` (in particular `ρ(1) = 1`).  Write
`g(ℓ) = ρ(ℓ)/ℓ`.  Assume

  (D-anchored) `∑_{ℓ ∈ P, ℓ ≤ w} g(ℓ) log ℓ ≤ log w + C₁`             for all `w ≥ 2`,
  (D-interval) `∑_{ℓ ∈ P, w₁ < ℓ ≤ w₂} g(ℓ) log ℓ ≤ log(w₂/w₁) + C₁`  for all `2 ≤ w₁ ≤ w₂`,

and let `D ≥ z¹⁰`.  Then, with

  `S = ∑_{n ∈ A, no ℓ ∈ P divides n} a_n`,
  `V = ∏_{ℓ ∈ P} (1 − g(ℓ))`,
  `A_d = ∑_{n ∈ A, d | n} a_n`,  `r_d = A_d − X ρ(d)/d`,

one has

  `S ≤ C · ( X · V + ∑_{d | ∏_{ℓ ∈ P} ℓ, d ≤ D} |r_d| )`.

### 1.3 The theorem that applies the interface

The **only** place where `UpperBoundSieveDimOne` is consumed as a sieve estimate is

```lean
theorem sieve_bound_single (hs : UpperBoundSieveDimOne) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L m a : ℕ) (z D : ℝ), 0 < m → a < m → m ∣ fq a →
      2 ≤ z → z ≤ (L : ℝ) → z ^ (10 : ℕ) ≤ D →
      (((Tset L m a).filter (fun t => Nat.Prime (Gpoly m a t) ∧ L < Gpoly m a t)).card : ℝ)
        ≤ C * (((Tset L m a).card : ℝ) * sieveProduct m z
            + ∑ d ∈ sieveDivisors (sievePrimes m z) with (((d : ℕ) : ℝ) ≤ D),
                (rootCount d : ℝ))
```

in `FactorialHypergraph/A3Apply.lean`.  It is invoked with `C₁ = max C₁a C₁b` (the two dimension
constants), `k = 2`, `ε = 1/2`.  Downstream chain (all in Lean):

`sieve_bound_single` → `card_prime_values_le` (`z = H^{1/20}`, `D = H^{1/2}`) →
`card_smallCofactorSet_le_sum` → `smallCofactorSieve_of_inputs` = **(A3)** →
`AnalyticInputs.of_sieve_theorem` → `cover_cost_of_sieve_theorem`,
`main_quantitative_of_sieve_theorem`, `auxiliary_erdos_problem_of_sieve_theorem`.

Every one of these theorems carries `hs : UpperBoundSieveDimOne` as an explicit hypothesis;
none of them is an axiom, and none of them assumes (A3) or any consequence of it (verified in
Appendix A, §3.15).

---

## 2. Verbatim source side

All items below were read in the PDF at the pages listed in §0 and are reproduced only in the
compressed form needed for matching.

**Set-up (printed p. 182).**  `A = (a_n)_{n=1}^∞ ⊂ ℝ_{≥0}` with `∑_n a_n < ∞`; `P` a *finite*
set of primes; `S(A, P) = ∑_{(n,P)=1} a_n`.  The special case of a finite set of integers is
the case `a_n = 1_A(n)`; the book explicitly switches between the two.

**`A_d` (printed p. 184, (18.2)).**  `A_d := ∑_{n ≡ 0 (mod d)} a_n`, and `d | P` means
`d | ∏_{p ∈ P} p`, i.e. `d` is squarefree with all prime factors in `P`.

**Axiom 1 (printed p. 185).**  *There is a multiplicative function `ν`, a parameter `X` and a
sequence of remainders `(r_d)_{d|P}` such that*

  `A_d = (ν(d)/d)·X + r_d`  for all `d | P`,  and  `ν(p) < p`  for all `p ∈ P`.

The remainder is *defined* on the same page by `r_d := A_d − X·ν(d)/d`.

*Transcription correction to the statement supplied in the audit request.*  The request writes
Axiom 1 with "`ν` multiplicative and `0 ≤ ν(p) < p`".  The printed Axiom 1 requires only
`ν(p) < p`; nonnegativity appears on the same page as (18.5), `δ(d) := ν(d)/d ∈ [0,1]` for
`d | P`, and it is an explicit hypothesis of Theorem 19.1(c) (`0 ≤ ν(p) < p`), which is the
technical form from which Theorem 18.11 is deduced.  So `0 ≤ ν(p) < p` is the effective
hypothesis; the Lean interface supplies both halves.  Everything else in the request's
transcription of Axiom 1 is correct.

**Bound (18.9) (printed p. 186).**  A parameter `k > 0` with `ν(p) ≤ k` for all `p ∈ P`.

**Axiom 2 (printed p. 187).**  *There are constants `κ ⩾ 0` and `C > 0` such that*

  `∏_{p ∈ P ∩ (y₁,y₂]} (1 − ν(p)/p)^{−1} ⩽ (1 + C/log y₁)·(log y₂ / log y₁)^κ`

*uniformly for `3/2 ⩽ y₁ ⩽ y₂ ⩽ max P`.*  The book calls this the Iwaniec condition and notes
in a footnote that the name is often used for the weaker version in which `1 + C/log y₁` is
replaced by an absolute constant `C′`.  It also notes that (18.9) together with
`ν(p)/p ⩽ 1 − ε` implies Axiom 2 with `κ = k` and `C = C(k, ε)`.

*Transcription correction.*  The request lists the constants of Axiom 2 as `κ, k ⩾ 0, C`; the
printed Axiom 2 has only `κ ⩾ 0` and `C > 0` (the constant `k` belongs to (18.9) and to
Axiom 2′).  The displayed inequality and the range `3/2 ⩽ y₁ ⩽ y₂ ⩽ max P` in the request are
exactly right.

**Axiom 2′ (printed p. 188).**  *There are constants `κ, k ⩾ 0` and `ε ∈ (0,1]` such that*

  `∑_{p ∈ P ∩ [1,w]} ν(p) log p / p = κ log w + O(1)`  for all `w ⩽ max P`,
  `ν(p) ⩽ min{(1−ε)p, k}`  for all `p ∈ P`.

*It is easy to show that Axiom 2′ implies Axiom 2 for some `C = C(ε, k, κ)`.*

**Axiom 3 (printed p. 188).**  Constants `A > 0`, `m ∈ ℕ` and `D ⩾ 1` with
`∑_{d ⩽ D, d|P} τ_m(d)|r_d| ⩽ X/(log X)^A`.

**Theorem 18.11 (printed p. 190).**  *Consider `A` and `P` satisfying Axioms 1 and 2 for some
`κ, C > 0`.  Set `y = max P` and `u_κ = 1 + 2/(e^{0.53/κ} − 1)`, and note that
`1 < u_κ < 1 + 3.8κ`.*

*(a) Uniformly for `u ⩾ 1`,*

  `S(A, P) = (1 + O_{κ,C}(u^{−u/2}))·X·∏_{p ∈ P}(1 − ν(p)/p) + O( ∑_{d ⩽ y^u, d|P} |r_d| )`.

*(b) Assume Axiom 3 with `m = 1`, `A = κ+1` and `D ⩾ y^{u_κ}`.  If `log X ≫ log y` and `D, X`
are large enough in terms of `κ` and `C`, then `X/100·∏(1−ν(p)/p) ⩽ S(A,P) ⩽ 5X·∏(1−ν(p)/p)`.*

The request's transcription of part (a) is **exactly correct**.  Two points are worth
recording:

* **Part (a) does not use Axiom 3.**  Axiom 3 is invoked only in part (b) — the hypothesis
  "Assume Axiom 3 with `m = 1`, `A = κ+1` and `D ⩾ y^{u_κ}`" appears in the statement of (b)
  alone, and the proof (printed p. 196) uses it only for (b).  Part (a) needs Axioms 1 and 2
  only.  Note also that Theorem 18.11 requires `κ > 0` (Axiom 2 alone permits `κ ⩾ 0`); we use
  `κ = 1`.
* **The implied constant of the remainder is absolute, and equals 1.**  In the proof of
  Theorem 18.11 (printed p. 196) the upper bound reads `S(A,P) ⩽ X ∑_d λ⁺(d)ν(d)/d + R⁺` with
  `R⁺ = ∑_d λ⁺(d) r_d`, and, since `|λ±| ⩽ 1` and `supp(λ±) ⊂ {d|P, d ⩽ D}` with `D = y^u`,
  `|R±| ⩽ ∑_{d|P, d ⩽ D} |r_d|`.  We nevertheless only use the printed form
  `O(∑_{d ⩽ y^u, d|P} |r_d|)`, i.e. some absolute constant `c₂ ≥ 0`.

---

## 3. Line-by-line match

Notation: Lean objects on the left, source objects on the right.  Direction of strength is
recorded in the last column: *"=" means literal match; "Lean ⇒ source" means the Lean
hypothesis is a (clearly identified) specialisation/strengthening, which is the admissible
direction, since it makes the source theorem applicable.*

| # | Lean hypothesis / object | Source counterpart | Verdict |
| --- | --- | --- | --- |
| 1 | `A : Finset ℕ`, `a : ℕ → ℝ`, `∀ n, 0 ≤ a n`, `∀ n ∉ A, a n = 0` | `A = (a_n)_{n≥1} ⊂ ℝ_{≥0}` with `∑ a_n < ∞` (p. 182) | Lean ⇒ source: finitely supported nonnegative weights are a summable nonnegative sequence |
| 2 | `∀ n ∈ A, 0 < n` | the book's sequence is indexed by `n ≥ 1` | Lean ⇒ source (and it is needed: `d ∣ 0` for every `d`) |
| 3 | weights are arbitrary nonnegative reals, so `a_n = #{t : G(t) = n}` is allowed | "sequence of weights", multiplicities carried by `a_n` (p. 182) | = : multiplicities are permitted |
| 4 | `∑ n ∈ A with (d ∣ n), a n` | `A_d = ∑_{n ≡ 0 (mod d)} a_n` (18.2) | = (the weights vanish off `A`) |
| 5 | index set `sieveDivisors P` of the remainder sum | `{d : d | P}` = squarefree `d` with all prime factors in `P` | = ; **machine-checked**: `mem_sieveDivisors_iff` in `FactorialHypergraph/A3SieveAudit.lean` proves `d ∈ sieveDivisors P ↔ d ∣ ∏_{ℓ ∈ P} ℓ` for `P` a finite set of primes |
| 6 | `rho : ℕ → ℝ`, used only through `rho ℓ` (`ℓ ∈ P`) and `rho d` (`d ∣ ∏P`); density `rho d / d` | `ν` with density `δ(d) = ν(d)/d` (18.5) | = , with **no normalisation reversal**: `X·rho d/(d:ℝ)` in Lean is `X·ν(d)/d` in the book |
| 7 | `∀ t ⊆ P, rho (∏_{ℓ ∈ t} ℓ) = ∏_{ℓ ∈ t} rho ℓ` | `ν` multiplicative | exactly the required strength: define `ν(p^a) := rho(p)^a` for `p ∈ P` and `ν(p^a) := 1` otherwise; this `ν` is multiplicative on `ℕ` and agrees with `rho` on every `d | P`, which is all that Axiom 1, Axiom 2, `r_d` and the conclusion involve.  Conversely a multiplicative `ν` satisfies the Lean hypothesis on subsets of `P`. |
| 8 | `∀ ℓ ∈ P, 0 ≤ rho ℓ` and `rho ℓ / ℓ ≤ 1 − ε` with `0 < ε < 1` | `0 ≤ ν(p) < p` (Axiom 1 with (18.5) / Theorem 19.1(c)) | Lean ⇒ source: `ρ(ℓ) ≤ (1−ε)ℓ < ℓ` since `ℓ ≥ 2 > 0`; the strict inequality is uniform, as in Axiom 2′ |
| 9 | `∀ ℓ ∈ P, rho ℓ ≤ k`, `1 ≤ k` | (18.9) `ν(p) ⩽ k` | = |
| 10 | `P : Finset ℕ`, `∀ ℓ ∈ P, Nat.Prime ℓ`, `∀ ℓ ∈ P, (ℓ:ℝ) ≤ z`, `2 ≤ z` | `P` a finite set of primes; `y = max P ⩽ z` | = ; the empty case is treated in §3.2 below |
| 11 | (D-interval) `∑_{ℓ ∈ P, w₁ < ℓ ≤ w₂} (ρ(ℓ)/ℓ) log ℓ ≤ log(w₂/w₁) + C₁`, `2 ≤ w₁ ≤ w₂` | Axiom 2 (p. 187), via the standard partial-summation implication — see §3.1 | Lean ⇒ source: (D-interval) implies Axiom 2 with `κ = 1` and `C = C(C₁,k,ε)`; and (D-interval) is itself implied by Axiom 2′ with `κ = 1` (take the difference of the two anchored estimates), so it sits *between* Axiom 2′ and Axiom 2 |
| 12 | range `2 ≤ w₁ ≤ w₂` (unbounded above) vs the source range `3/2 ⩽ y₁ ⩽ y₂ ⩽ max P` | Axiom 2 range | reconciled in both directions: upwards, `w₂ > max P` adds nothing (**machine-checked**: `interval_condition_of_bounded_range`); downwards, `y₁ ∈ [3/2, 2)` is covered by the local bound at the single prime `2` — see §3.1(iv) |
| 13 | (D-anchored) `∑_{ℓ ∈ P, ℓ ≤ w} (ρ(ℓ)/ℓ) log ℓ ≤ log w + C₁`, `w ≥ 2` | — (no counterpart needed) | **redundant, machine-checked**: `dim_anchored_of_interval` derives it from (D-interval) and `ρ(ℓ)/ℓ ≤ 1` with the *same* `C₁`; consequently `upperBoundSieveDimOne_iff_interval` proves that the interface is *equivalent* to the interface without it.  It is therefore neither an extra assumption nor a weakening — see §6.1 |
| 14 | `X = ∑_{n ∈ A} a_n` | `X` an arbitrary parameter in Axiom 1 | Lean ⇒ source: a particular admissible choice of `X` (`X = A_1`, whence `r_1 = 0`) |
| 15 | `r_d` appears in the conclusion as `(∑_{n ∈ A, d∣n} a n) − X·rho d/d` | `r_d := A_d − X ν(d)/d` (p. 185) | = : Axiom 1 holds by definition, with no smallness assumed |
| 16 | sifted sum `∑ n ∈ A with (∀ ℓ ∈ P, ¬ ℓ ∣ n), a n` | `S(A,P) = ∑_{(n,P)=1} a_n` | = ; **machine-checked**: `sifted_sum_eq_coprime_sum` proves the two filters agree (`(n, ∏P) = 1 ↔ no ℓ ∈ P divides n`) |
| 17 | `V = ∏_{ℓ ∈ P} (1 − rho ℓ / ℓ)` | `∏_{p ∈ P}(1 − ν(p)/p)` | = |
| 18 | remainder sum `∑_{d ∈ sieveDivisors P, d ≤ D} |r_d|` | `∑_{d ⩽ y^u, d|P} |r_d|` | correct support (item 5), absolute values present, and `y^{10} ≤ z^{10} ≤ D` (§4), so the source sum is `≤` the Lean sum |
| 19 | conclusion `S ≤ C(X·V + ∑|r_d|)`, `C = C(C₁,k,ε) > 0` chosen before the data | Theorem 18.11(a) with `κ = 1`, `u = 10`: constants `O_{κ,C}` and the absolute `O` | Lean ⇐ source, after the conversion of §4; all constants depend only on `κ = 1` and on `C = C(C₁,k,ε)`, i.e. only on `(C₁,k,ε)`, which is exactly the dependence the Lean binder order allows |
| 20 | no Lean hypothesis mentions a sifted-set estimate, a level-of-distribution bound on `∑ τ_m(d)|r_d|`, or (A3) | Axiom 3 is **not** a hypothesis of Theorem 18.11(a) | = : the interface uses only Axioms 1 and 2 |

### 3.1 The one paper-level step: (D-interval) `⇒` Axiom 2 with `κ = 1`

This is the only step of the match that is a mathematical argument rather than a Lean check;
it is elementary (partial summation plus `−log(1−x) ≤ x + x²/(2(1−x))`) and is recorded here
in full so that the claim boundary is explicit.  It is the same implication the book records
after Axiom 2′ ("It is easy to show that Axiom 2′ implies Axiom 2 for some `C = C(ε,k,κ)`"),
carried out with the one-sided interval hypothesis, which is all an upper bound needs.

*Claim.*  Let `P` be a finite set of primes, `δ(p) = ν(p)/p` with `0 ≤ ν(p) ≤ k` and
`δ(p) ≤ 1 − ε` for `p ∈ P`, and assume (D-interval) with constant `C₁ ≥ 0`.  Then Axiom 2
holds with `κ = 1` and some `C = C(C₁, k, ε)`.

*Proof.*  (i) Fix `2 ≤ y₁ ≤ y₂` and set `T(t) = ∑_{p ∈ P, y₁ < p ≤ t} δ(p) log p`, so `T(y₁)=0`
and `T(t) ≤ log(t/y₁) + C₁` by (D-interval).  Partial summation gives

  `∑_{y₁ < p ≤ y₂} δ(p) = T(y₂)/log y₂ + ∫_{y₁}^{y₂} T(t) dt/(t log²t)
     ≤ log(log y₂ / log y₁) + C₁/log y₁`,

the two `1/log y₂`-terms cancelling exactly.  (ii) For `0 ≤ x ≤ 1 − ε`,
`−log(1−x) ≤ x + x²/(2ε)`, and `∑_{p > y₁} δ(p)² ≤ k² ∑_{n > y₁} n^{−2} ≤ k²/(y₁−1) ≤
k² log 2 / log y₁` for `y₁ ≥ 2`.  Hence

  `log ∏_{p ∈ P ∩ (y₁,y₂]} (1 − δ(p))^{−1} ≤ log(log y₂/log y₁) + A/log y₁`,
  `A = C₁ + k² log 2/(2ε)`.

(iii) Exponentiating and using `e^x ≤ 1 + x e^{x₀}` for `0 ≤ x ≤ x₀ = A/log 2`,

  `∏_{p ∈ P ∩ (y₁,y₂]} (1 − δ(p))^{−1} ≤ (log y₂/log y₁)·(1 + C/log y₁)`,
  `C = A e^{A/log 2}`,

which is Axiom 2 with `κ = 1`.  (iv) Range `3/2 ≤ y₁ < 2`.  If `y₂ < 2` the product is empty
and the bound is trivial (its right-hand side is `≥ 1`).  Otherwise only the prime `2` can lie
in `(y₁, 2]`, and `(1 − δ(2))^{−1} ≤ 1/ε`; applying (iii) on `(2, y₂]` and using
`log y₁ ≤ log 2` gives the bound with `C` replaced by `log 2·ε^{−1}(1 + C/log 2)`.  ∎

Only the *upper* half of Axiom 2′ is used; no lower bound on the prime sums is required, which
matters because the one-sided anchored condition would **not** suffice (§5.2).

### 3.2 The empty sieving-prime set

The source writes `y = max P`, which presupposes `P ≠ ∅`.  The Lean interface does **not**
assume `P` nonempty, so this case must be discharged separately — and it can be, with no
external input: for `P = ∅` the sifted sum is `∑_{n ∈ A} a_n = X`, `V` is the empty product
`1`, and the remainder sum is `≥ 0`, so the conclusion holds for every `C ≥ 1`.  This is
**machine-checked**: `sieve_conclusion_of_empty` in `FactorialHypergraph/A3SieveAudit.lean`.
Since the constant `C` produced from the source theorem may always be increased, taking
`max(C, 1)` covers both cases.  (In the application `P = sievePrimes m z` is in fact nonempty
for `z ≥ 16`, but the interface is stated for arbitrary `P` and the empty case is genuinely
proved, not assumed away.)

---

## 4. The numerical specialisation `κ = 1`, `u = 10`

Parameters: `κ = 1`, `u = 10`, `y = max P ≤ z`, and in the application `z = H^{1/20}`,
`D = H^{1/2} = z^{10}`.

* **No size restriction is needed on `y` or `D`.**  Theorem 18.11(a) as printed is uniform
  for `u ⩾ 1` with constants depending only on `κ` and `C`, and imposes no lower bound on
  `y = max P`, on `X`, or on `D` (unlike part (b), which requires `D, X` large in terms of
  `κ, C`).  This is consistent: in the regime where `y` is bounded in terms of `κ, C`, Axiom 2
  applied with `y₁ = 3/2`, `y₂ = y` bounds `V = ∏_{p ∈ P}(1 − ν(p)/p)` from below by a
  positive constant `c(κ,C)`, so `S(A,P) ≤ X ≤ c(κ,C)^{−1}·X·V` and the statement holds with a
  large enough implied constant.  We use the printed statement as it stands.
* **`u = 10` is admissible.**  Theorem 18.11(a) holds uniformly for `u ⩾ 1`; `10 ⩾ 1`.  (For
  `κ = 1`, `u_κ = 1 + 2/(e^{0.53} − 1) = 3.83…`, so `u = 10 > u_κ` even lies in the range where
  the deduction from Theorem 19.1 is direct, but part (a) does not require this.)
* **`y^{10} ≤ z^{10} ≤ D`.**  Machine-checked: `level_max_pow_le` in
  `FactorialHypergraph/A3SieveAudit.lean` proves `(max P)^{10} ≤ z^{10}` and `(max P)^{10} ≤ D`
  from `∀ ℓ ∈ P, (ℓ:ℝ) ≤ z` and `z^{10} ≤ D`.  In the application `z^{10} = D` holds with
  equality (`level_eq_of_application`: `(H^{1/20})^{10} = H^{1/2}` for `H > 0`).
* **The source remainder is dominated by the Lean remainder.**  Both sums run over `d | P`;
  the source truncates at `y^{10}`, Lean at `D ≥ y^{10}`, and all terms `|r_d|` are `≥ 0`.
  Machine-checked: `remainder_sum_mono`.
* **Error factor.**  `u^{−u/2} = 10^{−5} = 1/100000` (machine-checked: `u_ten_error`).  Thus
  Theorem 18.11(a) with `u = 10` reads

    `S = (1 + θ)·X·V + ϑ·R`,  `|θ| ≤ c₁(κ,C)·10^{−5}`,  `|ϑ| ≤ c₂`,
    `R = ∑_{d ⩽ y^{10}, d|P}|r_d|`,

  with `c₁` depending only on `κ = 1` and `C = C(C₁,k,ε)`, and `c₂` absolute.
* **Conversion to a one-sided bound, with an explicit constant.**  From the displayed equality,
  `S ≤ (1 + |θ|)·X·V + c₂·R` **provided `X·V ≥ 0` and `R ≥ 0`**, which is where nonnegativity
  is needed.  Both are machine-checked: `total_mass_nonneg` (`X ≥ 0`, from `a ≥ 0`),
  `sieve_product_nonneg` (`V ≥ 0`; indeed every factor is `≥ ε > 0`), `remainder_sum_nonneg`
  (`R ≥ 0`, a sum of absolute values).  Then `one_sided_of_asymptotic` gives

    `S ≤ max(1 + |θ|, c₂)·(X·V + R)`,

  and since `R ≤ ∑_{d|P, d ≤ D}|r_d|` (previous item) we obtain exactly the Lean conclusion
  with `C_sieve = max(1 + c₁·10^{−5}, c₂, 1)`, a constant depending only on `(C₁, k, ε)`.  The
  final `max(·, 1)` also covers the empty-`P` case of §3.2.  No asymptotic equality was
  silently replaced by an inequality: the constant is extracted explicitly from the two
  implied constants of Theorem 18.11(a).

---

## 5. Application uniformity

### 5.1 Independence of the source constant from `m, a, L, α`

* Theorem 18.11(a)'s constants depend only on `κ` and `C` (§2).  In the Lean interface this is
  reflected in the binder order: `C` is produced from `(C₁, k, ε)` *before* `A, a, P, rho,
  X, z, D` are quantified.  Nothing in `(C₁, k, ε)` depends on `m, a, L, α`: the application
  passes `k = 2` (the degree bound for `f(t) = t² + 3t + 1`), `ε = 1/2`, and
  `C₁ = max C₁a C₁b`, where `C₁a`, `C₁b` come from `dimension_condition` and
  `dimension_condition_interval`, whose statements begin `∃ C₁, 0 ≤ C₁ ∧ ∀ P : Finset ℕ, …` —
  a single constant valid for **all** finite prime sets.
* Accordingly `sieve_bound_single` has the shape `∃ C, 0 < C ∧ ∀ L m a z D, …`, and
  `card_prime_values_le` the shape `∃ C, 0 < C ∧ ∃ L₀, ∀ L ≥ L₀, ∀ m, ∀ a, …`; the constant
  and the threshold are fixed before `L, m, a`, and (see Appendix A, §3.13) before `α`.

### 5.2 Axiom 2 after truncation and deletion of the primes dividing `10m`

The application sieves with `P = sievePrimes m z = {ℓ ≤ ⌊z⌋₊ : ℓ prime, ℓ ∤ 10m}`, i.e. the
base prime system truncated at `z` with the primes dividing `10m` (in particular `2` and `5`)
deleted.  Because `dimension_condition_interval` is proved **for an arbitrary finite set of
primes** — with one constant, uniformly — truncation and deletion require no separate
argument: both operations only remove nonnegative terms from the sums.

**Precision about "arbitrary finite prime sets".**  The quantifier `∀ P : Finset ℕ,
(∀ ℓ ∈ P, Nat.Prime ℓ) → …` in `dimension_condition_interval` ranges over arbitrary finite
sets of primes, but the local density there is the *fixed* function `rootCount`, the number of
roots of `f(t) = t² + 3t + 1` modulo `ℓ`.  It is therefore **not** a statement about arbitrary
densities supported on arbitrary primes; it is a statement about arbitrary finite subsets of
the factorial-polynomial prime system.  That is exactly what the application needs, and the
interface `UpperBoundSieveDimOne` — which does quantify over arbitrary densities — receives it
as one particular instance.

### 5.3 Recheck of the counterexample to the anchored-only condition

The earlier audit rejected the *anchored-only* dimension hypothesis on the strength of a
counterexample.  Rechecked against Axiom 2 as printed:

Let `z` be large, `P = {p prime : √z < p ≤ z}` and `ν(p) = 2` on `P`.  By Mertens,
`∑_{p ≤ w} (ν(p)/p) log p = 2(log w − log √z) + O(1) ≤ log w + O(1)` for `√z < w ≤ z`, and it
equals `log z + O(1) ≤ log w + O(1)` for `w > z`; so the anchored bound holds with `κ = 1` and
an absolute `C₁`.  But at `y₁ = √z`, `y₂ = z`,

  `∏_{p ∈ P ∩ (√z, z]} (1 − 2/p)^{−1} = 4 + o(1)`,  while  `(1 + C/log√z)(log z/log√z)^1 = 2 + o(1)`,

so **Axiom 2 with `κ = 1` fails** for every fixed `C` once `z` is large.  The counterexample is
valid, in the precise sense that matters here: an anchored-only interface would *not* be an
instance of Theorem 18.11(a) with `κ = 1` and a constant depending only on `(C₁, k, ε)`.  (The
example does not by itself show that such an interface would be a false statement — a
dimension-`2` sieve with `u = 10 > u_2 = 7.59…` might still deliver a comparable bound with a
different constant; what fails is the *source justification*, which is what an external
interface must have.)

The repaired hypothesis eliminates the defect: (D-interval) applied with `y₁ = √z`, `y₂ = z`
gives `log z + O(1) ≤ ½ log z + C₁`, which is false for large `z`, so the example is excluded;
and §3.1 shows that (D-interval) always yields Axiom 2 with `κ = 1`.

---

## 6. Outcome and repairs

**Outcome: source match verified.**  Theorem 18.11(a) of the source, specialised to `κ = 1`
and the fixed value `u = 10`, together with the elementary implication of §3.1 and the
nonnegativity/monotonicity facts of §4 (all machine-checked), rigorously yields the conclusion
of `UpperBoundSieveDimOne` for every admissible instance of its data, including the empty
prime set (§3.2).  The interface is therefore a *fixed-`u` corollary of the source theorem
under hypotheses that are at least as strong as the source's*.

The Lean interface imposes the following hypotheses beyond Axioms 1–2 of the source; each is
listed with its justification.

| Extra Lean hypothesis | Status |
| --- | --- |
| `X = ∑_{n ∈ A} a_n` | admissible specialisation of the free parameter `X` of Axiom 1; proved in the application (`X = H = #T_{a,m}`) |
| `0 ≤ ρ(ℓ)`, `ρ(ℓ) ≤ k`, `ρ(ℓ)/ℓ ≤ 1 − ε` | (18.5), (18.9) and the uniform version of `ν(p) < p` used in Axiom 2′; proved in the application with `k = 2`, `ε = 1/2` |
| `2 ≤ z`, `∀ ℓ ∈ P, ℓ ≤ z`, `z^{10} ≤ D` | the parameters `y = max P ≤ z` and `u = 10` of the source; proved in the application, with `z^{10} = D` |
| `∀ n ∈ A, 0 < n` | the source's index range `n ≥ 1`; proved in the application (`G_{a,m}(t) > 0`) |
| (D-anchored) | **redundant** — `dim_anchored_of_interval` derives it from (D-interval); `upperBoundSieveDimOne_iff_interval` shows the interface is equivalent to the one without it |

None of these hypotheses contains Axiom 3, the level-of-distribution estimate, (A3), or any
consequence of (A3); the only inequality about the quantity being estimated is the conclusion.

**Repairs made in this run.**  None were required to the interface or to its application: the
mismatch found in the previous run (the anchored-only dimension hypothesis) had already been
repaired there, and the present source reading confirms that the repaired hypothesis is the
right one.  What was added is machine-checked evidence for the items above, in the new file
`FactorialHypergraph/A3SieveAudit.lean`:

| Lean declaration | Audit item |
| --- | --- |
| `squarefree_prod_primes`, `mem_sieveDivisors_iff` | the remainder index set is exactly `{d : d | P}` |
| `dim_anchored_of_interval` | (D-anchored) is redundant |
| `upperBoundSieveDimOneInterval`, `upperBoundSieveDimOne_iff_interval` | the interface is *equivalent* to its interval-only form |
| `interval_condition_of_bounded_range` | the source's range `y₂ ≤ max P` loses nothing |
| `sifted_sum_eq_coprime_sum` | the Lean sifted sum is `S(A,P)` |
| `sieve_conclusion_of_empty` | the empty prime set, proved outright |
| `level_max_pow_le`, `remainder_sum_mono`, `level_eq_of_application`, `u_ten_error` | the `u = 10` specialisation `y^{10} ≤ z^{10} = D`, and `10^{−5}` |
| `total_mass_nonneg`, `sieve_product_nonneg`, `remainder_sum_nonneg`, `one_sided_of_asymptotic` | the nonnegativity needed to convert the asymptotic equality into a one-sided bound with an explicit constant |

No `sorry`, `admit`, `unsafe`, global `axiom`, opaque placeholder, or problem-specific
restatement of (A3) was introduced.  The manuscript `Aug25.tex` and `ARISTOTLE_SUMMARY.md`
were not modified, and the fundamental lemma of sieve theory was not formalized.

### 6.1 On keeping the redundant anchored hypothesis in the interface

`upperBoundSieveDimOne_iff_interval` proves that the interface and its interval-only form are
the *same* `Prop` up to logical equivalence, so keeping (D-anchored) neither strengthens nor
weakens the external assumption.  It is retained only because downstream files supply it and
because it records, in the statement itself, the anchored form that the manuscript quotes.
The interval-only form is available in the project as `UpperBoundSieveDimOneInterval` for
anyone who prefers the minimal statement.

---

## 7. Final verification

### 7.1 Build

```
$ lake build
Build completed successfully (8056 jobs).
```

Zero errors; warnings only (unused variables and `simp` lints in unrelated files).  A search
for forbidden constructs finds only prose occurrences inside comments:

```
$ rg -n "sorry|admit\b|unsafe|^axiom " FactorialHypergraph/*.lean
FactorialHypergraph/PrimeCountingUpper.lean:30:no `sorry`, `admit`, opaque placeholder or user-defined axiom is introduced.
FactorialHypergraph/Main.lean:251:for each of them: **no `sorryAx` and no user-defined axiom occurs anywhere in this
```

### 7.2 `#print axioms` for the sieve-to-main-theorem dependency chain

All results are exactly `[propext, Classical.choice, Quot.sound]`; in particular **no
`sorryAx` and no user-defined axiom** occurs anywhere in the chain.

| Theorem | Axioms |
| --- | --- |
| `dimension_condition` | `[propext, Classical.choice, Quot.sound]` |
| `dimension_condition_interval` | `[propext, Classical.choice, Quot.sound]` |
| `mertensRoots_lower`, `mertensRoots_upper_div_p` | `[propext, Classical.choice, Quot.sound]` |
| `sieveProduct_le`, `sum_gMaj_div_le`, `sum_rootCount_div_sqrt_le` | `[propext, Classical.choice, Quot.sound]` |
| `abs_card_dvd_Gpoly_sub_le` | `[propext, Classical.choice, Quot.sound]` |
| `sieve_bound_single` | `[propext, Classical.choice, Quot.sound]` |
| `sum_rootCount_sieveDivisors_le` | `[propext, Classical.choice, Quot.sound]` |
| `card_prime_values_le` | `[propext, Classical.choice, Quot.sound]` |
| `card_smallCofactorSet_le_sum` | `[propext, Classical.choice, Quot.sound]` |
| `smallCofactorSieve_of_inputs` | `[propext, Classical.choice, Quot.sound]` |
| `smallCofactorSieve_conditional` | `[propext, Classical.choice, Quot.sound]` |
| `largePrimeFactor_fortieth`, `primeCountingUpper_two` | `[propext, Classical.choice, Quot.sound]` |
| `AnalyticInputs.of_smallCofactorSieve` | `[propext, Classical.choice, Quot.sound]` |
| `AnalyticInputs.of_sieve_theorem` | `[propext, Classical.choice, Quot.sound]` |
| `cover_cost_of_sieve_theorem` | `[propext, Classical.choice, Quot.sound]` |
| `main_quantitative_of_sieve_theorem` | `[propext, Classical.choice, Quot.sound]` |
| `auxiliary_erdos_problem_of_sieve_theorem` | `[propext, Classical.choice, Quot.sound]` |

and, for the new audit file `FactorialHypergraph/A3SieveAudit.lean`, all of
`squarefree_prod_primes`, `mem_sieveDivisors_iff`, `dim_anchored_of_interval`,
`upperBoundSieveDimOne_iff_interval`, `interval_condition_of_bounded_range`,
`total_mass_nonneg`, `sieve_product_nonneg`, `remainder_sum_nonneg`,
`sieve_conclusion_of_empty`, `sifted_sum_eq_coprime_sum`, `level_max_pow_le`,
`remainder_sum_mono`, `u_ten_error`, `one_sided_of_asymptotic`, `level_eq_of_application`:
`[propext, Classical.choice, Quot.sound]`.

The corresponding `#print axioms` commands are compiled as part of the project
(`FactorialHypergraph/A3SieveAudit.lean`, `FactorialHypergraph/Assembly.lean`,
`FactorialHypergraph/A2Assembly.lean`, `FactorialHypergraph/PrimeCountingUpper.lean`,
`FactorialHypergraph/Main.lean`).

### 7.3 The explicit hypothesis, which does not appear in the axiom output

`#print axioms` does not display `Prop`-valued hypotheses.  Listed separately, therefore:

> The theorems `smallCofactorSieve_conditional`, `AnalyticInputs.of_sieve_theorem`,
> `cover_cost_of_sieve_theorem`, `main_quantitative_of_sieve_theorem` and
> `auxiliary_erdos_problem_of_sieve_theorem` each take **exactly one** external hypothesis,
> `hs : UpperBoundSieveDimOne` (§1.1), and nothing else.

(A1) (prime supply) and (A2) (large prime factors) are proved in Lean unconditionally and
contribute no hypothesis.  `WienerIkeharaTheorem` survives only as a hypothesis of the
optional statements that reproduce the manuscript's sharper constant `1/8`
(`largePrimeFactor_eighth` and companions); no final theorem uses them.

### 7.4 The exact final claim boundary

What is machine-checked in Lean: everything from `UpperBoundSieveDimOne` down to the
manuscript's Theorem 1.1, Theorem 1.2 and the auxiliary Erdős statement, with no `sorry` and
no user-defined axiom.

What is **not** formalized, and is invoked as an external hypothesis: the fundamental lemma of
sieve theory.  Its source justification consists of Theorem 18.11(a) of the source (§2)
together with the elementary partial-summation implication of §3.1 and the arithmetic of §4;
of these, §4 is machine-checked and §3.1 is a paper-level argument recorded in full above.

> **The auxiliary Erdős theorem is formally verified in Lean modulo Koukoulopoulos's
> established Fundamental Lemma of Sieve Theory, Theorem 18.11(a), which is invoked through
> the explicit interface `UpperBoundSieveDimOne` but is not itself formalized in Lean.**

The Lean development is therefore **not** completely unconditional, and nothing here claims a
solution of the original prime version of Erdős Problem 1059.

---

## Appendix A. A3 application audit (from the earlier internal audit; unchanged)

*Subsection numbers below are those of the earlier audit.*

Deduction chain, with the file of each step.  Every statement below is proved in Lean with
no `sorry` and with only the three standard axioms (§7).

```
MertensAux, MertensCharacter, MertensSecond, MertensRoots, MertensLower   (Mertens, χ₅)
        │
        ├─► A3Mertens :  sum_inv_primes_chi5                     (unconditional)
        ├─► A3Roots   :  rootCount classification & multiplicativity, hFactor, gMaj
        ├─► A3Euler   :  sum_gMaj_div_le, sum_rootCount_div_sqrt_le
        ├─► A3Product :  dimension_condition, dimension_condition_interval,
        │                sievePrimes, sieveProduct, sieveProduct_le
        └─► A3Local   :  Tset, Gpoly, discriminant, primitivity, card_Tset_le,
                         le_card_Tset, card_roots_Gpoly, abs_card_dvd_Gpoly_sub_le
                                  │
A3Sieve : UpperBoundSieveDimOne ──┴─► A3Apply : sieve_bound_single,
                                                sum_rootCount_sieveDivisors_le,
                                                card_prime_values_le
                                            └─► A3Main : card_smallCofactorSet_le_sum,
                                                         smallCofactorSieve_of_inputs
                                                     └─► Assembly : smallCofactorSieve_conditional
                                                                    AnalyticInputs.of_sieve_theorem
                                                                    cover_cost_of_sieve_theorem
                                                                    main_quantitative_of_sieve_theorem
                                                                    auxiliary_erdos_problem_of_sieve_theorem
```

### 3.1 Classification and multiplicativity of `R(m)` (`rootCount`)

`rootCount p = #{a < p : p | f(a)}` (`FactorialHypergraph/LargePrimeFactors.lean`).  Proved in
`A3Roots.lean`:

* `rootCount_one`, `rootCount_zero` (`decide`);
* `rootCount_mul_of_coprime`, `rootCount_mul` — multiplicativity on coprime arguments (CRT);
* `rootCount_eq_factorization_prod` — the multiplicative expansion.

### 3.2 The exceptional primes 2 and 5

`rootCount_two_pow : rootCount (2^e) = 0` for `e ≥ 1`; `rootCount_five : rootCount 5 = 1`;
`rootCount_five_pow : rootCount (5^e) = 0` for `e ≥ 2`; and for `p ≠ 2, 5`,
`rootCount_prime_eq_two` (`χ₅(p) = 1`) resp. `rootCount_prime_pow_eq_zero` (`χ₅(p) ≠ 1`).
This is exactly the manuscript's display for `R(2^e), R(5), R(5^e), R(p^e)`.
Both exceptional primes are then *excluded from the sieve* by
`sievePrimes m z = {ℓ ≤ ⌊z⌋₊ : ℓ prime, ℓ ∤ 10m}` and
`ne_two_five_of_mem_sievePrimes : ℓ ∈ sievePrimes m z → ℓ ≠ 2 ∧ ℓ ≠ 5`.

### 3.3 Integrality and primitivity of `G_{a,m}`, discriminant 5

`Gpoly m a t = fq (a + m*t) / m` (natural-number division) with
`Gpoly_spec : m ∣ fq a → m * Gpoly m a t = fq (a + m*t)` — this is *integrality*: the
division is exact, proved from `dvd_fq_add_mul`.  `Gpoly_pos` gives `G > 0`.

`Gpoly_discriminant : 4 * m * Gpoly m a t + 5 = (2*(a + m*t) + 3)^2` — the discriminant 5
identity, in the exact integral form used later.

`Gpoly_primitive : p prime → p ∣ m → p ∣ 2a+3 → ¬ p ∣ fq a / m`, proved exactly as in the
manuscript: `p²` would divide `(2a+3)² − 4 f(a) = 5`.

### 3.4 The interval length `H = L/m + O(1)`

`Tset_eq_Ico` (the set of `t` is a genuine interval), `card_Tset_le : H ≤ L/m + 1`, and
`le_card_Tset : L/m − 1 ≤ H` (for `a < m`).  In `card_prime_values_le` these give
`H ≥ √L − 1 ≥ 2^80` and `H ≤ 2L/m`.  All are real-number statements; the truncated
natural subtraction is avoided by casting first (`nat_div_bounds`).

### 3.5 The local remainder bound `|r_d| ≤ ρ(d)`

`abs_card_dvd_Gpoly_sub_le` (`A3Local.lean`):

```lean
theorem abs_card_dvd_Gpoly_sub_le {L m a d : ℕ} (hm : 0 < m) (hdvd : m ∣ fq a) (hd : 0 < d)
    (hcop : Nat.Coprime d m) :
    |(((Tset L m a).filter (fun t => d ∣ Gpoly m a t)).card : ℝ)
        - ((Tset L m a).card : ℝ) * (rootCount d : ℝ) / (d : ℝ)| ≤ (rootCount d : ℝ)
```

i.e. `#{t ∈ T : d | G(t)} = H ρ(d)/d + r_d` with `|r_d| ≤ ρ(d)`, which is the manuscript's
`\eqref{eq:localcount}`.  It rests on `card_roots_Gpoly` (`#{r < d : d | G(r)} = ρ(d)` for
`d` coprime to `m`, via the bijection `t ↦ a + mt` mod `d`) and on the elementary
`abs_card_Ico_mod_sub_le` (counting one residue class in an interval).

Note: the interface does **not** assume this bound; it is used in `sieve_bound_single` to
bound the remainder sum *after* the interface is applied.

### 3.6 Squarefree support and exclusion of primes dividing `10m`

`sieveDivisors P = P.powerset.image (∏)` consists exactly of the squarefree products of
primes of `P`.  With `P = sievePrimes m z` (primes `≤ z` not dividing `10m`),
`coprime_of_mem_sieveDivisors` proves `Nat.Coprime d m ∧ 0 < d` for every
`d ∈ sieveDivisors (sievePrimes m z)`, which is exactly the hypothesis needed by
`abs_card_dvd_Gpoly_sub_le`.  Primes dividing `10m` (in particular 2 and 5) never enter.

### 3.7 Why a prime value `G_{a,m}(t) > L` survives sieving

In `sieve_bound_single`, the sifted sum dominates the count (`hsift`): if `G(t)` is prime and
`G(t) > L`, and `ℓ ∈ P` divided `G(t)`, then `ℓ = G(t)` (two primes dividing each other),
whence `L < G(t) = ℓ ≤ z ≤ L` — a contradiction.  The hypothesis `z ≤ L` is an explicit
binder of `sieve_bound_single` and is discharged in `card_prime_values_le` by
`hzL : z = H^{1/20} ≤ L` (from `H ≤ 2L ≤ L^20` for `L ≥ 2^170`).  This is the manuscript's
"for sufficiently large `L` we have `z < L`", made explicit.

### 3.8 The remainder sum `∑_{d ≤ H^{1/2}} ρ(d) ≪ H^{1/2} log H`

`sum_rootCount_sieveDivisors_le : ∑_{d | ∏P, d ≤ D} ρ(d) ≤ D (1 + log D)`, proved from
`ρ(d) ≤ τ(d)` (`rootCount_le_card_divisors`) and `∑_{d ≤ M} τ(d) ≤ M(1 + log M)`
(`sum_card_divisors_le`).  With `D = H^{1/2}` this is the manuscript's `≪ H^{1/2} log H`; in
`card_prime_values_le` it is converted to `≤ 4 √(L/m) log L`.

### 3.9 `V_m(z) ≪ h(m)/log z`

`sieveProduct m z = ∏_{ℓ ∈ sievePrimes m z} (1 − ρ(ℓ)/ℓ)`;
`sieveProduct_eq_chi` reduces it to the primes with `χ₅ = 1`;
`sieveProduct_le_mul_hFactor : V_m(z) ≤ V_1(z) · h(m)`;
`sieveProduct_one_le : V_1(z) ≤ C/log z` for `z ≥ 16`;
`sieveProduct_le : ∃ C > 0, ∀ m ≥ 1, ∀ z ≥ 16, V_m(z) ≤ C h(m)/log z`.
`hFactor m = ∏_{p | m} (1 − 2/p)^{-1}`-type factor (`A3Roots.lean`), with `1 ≤ h(m)` and
`ρ(m) h(m) ≤ gMaj m`.

### 3.10 Mertens / `χ₅` inputs used in that product estimate

* `mertensRoots_unconditional` (root-weighted Mertens first theorem, upper form) —
  `FactorialHypergraph/MertensRoots.lean`;
* `mertensRoots_upper_div_p`, `mertensRoots_lower` (both directions, in the `1/p` form) —
  `FactorialHypergraph/MertensLower.lean` (**new in this run**, elementary and unconditional);
* `sum_inv_primes_chi5` — `A3Mertens.lean`, which is *definitionally*
  `sum_inv_primes_chi5_unconditional` of `FactorialHypergraph/MertensSecond.lean`.  The
  hypothesis `MertensProgressions` is retained in `A3Mertens.lean` only as documentation of
  what the manuscript appeals to; **it is used by no theorem** in the chain.

Every one of these is unconditional; none of them is a hypothesis of any theorem in the
chain.

### 3.11 Euler-product sums over complementary factors

* `sum_gMaj_div_le : ∃ C₃ > 0, ∀ N ≥ 1, ∑_{m ≤ N} gMaj(m)/m ≤ C₃ (1 + log N)`
  (`A3Euler.lean`), which majorises `∑_{m ≤ Y} R(m) h(m)/m` via
  `rootCount_mul_hFactor_le : R(m) h(m) ≤ gMaj m`;
* `sum_rootCount_div_sqrt_le : ∀ N, ∑_{m ≤ N} R(m)/√m ≤ 2 √N (1 + log N)`
  (`A3Euler.lean`, unconditional, by `R ≤ 1 * 1` Dirichlet-convolution majorisation).

Both are proved for **all** `N ≥ 1`, with constants independent of `N`.

### 3.12 The union bound over complementary factors and floors/casts with `Y = L^α`

`card_smallCofactorSet_le_sum` embeds `E_α(L)` into
`⋃_{m ≤ Y} ⋃_{a < m, m | f(a)} { a + m t : t ∈ T_{a,m}, G_{a,m}(t) prime > L }` and applies
`Finset.card_biUnion_le` twice and `Finset.card_image_le`.  Its hypothesis is
`∀ m ≥ 1, (m : ℝ) ≤ L^α → m ≤ Y`, instantiated with the natural-number floor
`Y = ⌊L^α⌋₊` via `Nat.le_floor`.  The two floor facts used afterwards are
`(Y : ℝ) ≤ L^α` (`Nat.floor_le`) and `1 ≤ Y` (from `L^α ≥ 1`), and then
`log Y ≤ α log L` and `√Y ≤ L^{α/2}`, `√L √Y ≤ L^{(1+α)/2}`.  Also
`(Y : ℝ) ≤ √L` for `α ≤ 1/2`, which is what allows `card_prime_values_le` (valid for
`m ≤ √L`) to be applied to every `m ≤ Y`.  All casts are performed on the real side; there
is no truncated subtraction anywhere in this argument.

### 3.13 Uniformity for every `0 < α ≤ 1/2`, including `α → 0`

In `smallCofactorSieve_of_inputs`:

```lean
  obtain ⟨C, hC, Lc, hcard⟩ := card_prime_values_le hs
  obtain ⟨C₃, hC₃, hsum1⟩ := sum_gMaj_div_le
  refine ⟨max 1 (C * C₃ + 3 * C), le_max_left _ _, max Lc 8, ?_⟩
  intro α hα hα2 L hL
```

`C₀ = max 1 (C·C₃ + 3C)` and `L₀ = max Lc 8` are produced **before** `α` and `L` are
introduced, so a single absolute `C₀ ≥ 1` and a single `α`-independent threshold `L₀` serve
all `0 < α ≤ 1/2`.  Inside, `C` comes from `card_prime_values_le` (whose own threshold is the
absolute `L₀ = 2^170` and whose constant is `Cs·(160 C₂ + 4)` with `Cs` from the sieve
interface and `C₂` from `sieveProduct_le`), and `C₃` from `sum_gMaj_div_le`; none of them
depends on `α, L, m, a`.

The limit `α → 0` is harmless: the only place `α` enters is through `log Y ≤ α log L` with
`Y = ⌊L^α⌋₊ ≥ 1`, giving the term `C₃(1 + α log L)·(L/log L) = C₃(α L + L/log L)`, and
through `√Y ≤ L^{α/2}`.  Both remain valid at every `α ∈ (0, 1/2]`, and the bound degrades
continuously to `C₀(L/log L + √L (log L)²)` as `α → 0`.  No step divides by `α` and no step
requires `α` bounded away from 0.

### 3.14 Endpoint / numerical checks in `card_prime_values_le`

| Requirement | Value used | Discharged by |
| --- | --- | --- |
| `H ≥ 2^80` | from `L ≥ 2^170`, `m ≤ √L`, `H ≥ √L − 1 ≥ 2^85 − 1` | `hHR80` |
| `z ≥ 16` (needed by `sieveProduct_le`) | `z = H^{1/20} ≥ (2^80)^{1/20} = 16` | `hz16` |
| `z ≥ 2` (needed by the interface) | from `z ≥ 16` | `hz2` |
| `z ≤ L` (needed for "primes `> L` survive") | `H ≤ 2L ≤ L^20` | `hzL` |
| `z^{10} ≤ D` (the `u = 10` relation) | `z^{10} = D` **exactly**, with `D = H^{1/2}` | `hzD` |
| `D ≥ 1` (needed by the divisor-sum bound) | `D = √H ≥ 1` | `hD1` |
| `log L ≥ 100` | from `L ≥ 2^170` | `hlogL100` |
| `log H ≥ (log L)/4` | from `H ≥ √L / 2` | `hlogHRlow` |

### 3.15 No circularity

Mechanical check: no file in the chain (`MertensLower`, `MertensRoots`, `MertensSecond`,
`MertensAux`, `MertensCharacter`, `A3Sieve`, `A3Mertens`, `A3Roots`, `A3Local`, `A3Product`,
`A3Euler`, `A3Apply`) contains any occurrence of `AnalyticInputs`, `smallCofactorSieve`,
`goodSet` or `kappa`:

```
$ rg -n "AnalyticInputs|smallCofactorSieve|goodSet|kappa " FactorialHypergraph/A3Sieve.lean \
    FactorialHypergraph/A3Roots.lean FactorialHypergraph/A3Local.lean FactorialHypergraph/A3Product.lean \
    FactorialHypergraph/A3Euler.lean FactorialHypergraph/A3Apply.lean FactorialHypergraph/A3Mertens.lean \
    FactorialHypergraph/MertensLower.lean FactorialHypergraph/MertensRoots.lean FactorialHypergraph/MertensSecond.lean
(no matches)
```

In `A3Main.lean` the only occurrence of `AnalyticInputs` is in a docstring stating that
`smallCofactorSieve_of_inputs` restates the field verbatim.  `A3Sieve.lean` imports only
`Mathlib`.  Therefore no theorem in the chain assumes A3, `AnalyticInputs`, or the final
result.

---

## Appendix B. Large-prime-factor deviation: `1/8` versus `1/40` (from the earlier internal audit; unchanged)

### 4.1 The two statements, kept strictly apart

`FactorialHypergraph/A2Assembly.lean` now carries both, under unambiguous names:

```lean
/-- **UNCONDITIONAL.** … The numerical check is `2κ/c = 2·2/40 = 0.1 ≤ 0.27`. -/
theorem largePrimeFactor_fortieth :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → (N : ℝ) / 5 ≤ ((largePrimeFactorSet N).card : ℝ) := by
  have h := largePrimeFactor_of_estimates (c := 40) (kap := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    mertensRoots_unconditional primeCountingUpper_two
  simpa [largePrimeFactorSet] using h

/-- **CONDITIONAL on `LargePrimeInputs`** (i.e. on `π(y) ≤ 1.02 y/log y`).  Lemma 3.2 with
the manuscript's own threshold constant `8`. … -/
theorem largePrimeFactor_eighth (h : LargePrimeInputs) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → (N : ℝ) / 5 ≤ ((largePrimeFactorSetC 8 N).card : ℝ) :=
  largePrimeFactor_of_inputs_eight h
```

Here `largePrimeFactorSetC c N = {1 ≤ i ≤ N : ∃ q prime, q | f(i), q > i log i / c}` and
`largePrimeFactorSet N = largePrimeFactorSetC 40 N`.  The name
`largePrimeFactor_unconditional` is retained as an explicit alias of
`largePrimeFactor_fortieth`, with a docstring saying that the threshold constant is 40.
**The exact manuscript statement (constant 8) is nowhere labelled unconditional.**

### 4.2 The Chebyshev instantiation, checked

`largePrimeFactor_of_estimates` (`FactorialHypergraph/LargePrimeFactors.lean`) has the explicit
numerical side conditions

```lean
{c kap : ℝ} (hc : 8 ≤ c) (hc' : c ≤ 1000) (hkap1 : 1 ≤ kap) (hkap2 : kap ≤ 2)
    (hnum : 2 * kap / c ≤ 0.27)
```

and takes the prime-counting input in the form `π(y) ≤ kap · y / log y` for large `y`.  With
`c = 40`, `kap = 2` these are `8 ≤ 40`, `40 ≤ 1000`, `1 ≤ 2`, `2 ≤ 2`, and

    2κ/c = 2·2/40 = 0.1 ≤ 0.27  ✓

all discharged by `norm_num` (i.e. kernel-checked).

The prime-counting input is `primeCountingUpper_two`
(`FactorialHypergraph/PrimeCountingUpper.lean`):

```lean
theorem primeCountingUpper_two :
    ∃ y₀ : ℕ, ∀ y : ℕ, y₀ ≤ y → ((primesLE y).card : ℝ) ≤ 2 * (y : ℝ) / Real.log y
```

derived from mathlib's `Chebyshev.theta_le_log4_mul_x` (`θ(x) ≤ (log 4) x`) through
`primeCountingUpper_const_of_theta_le`.  **No exact coefficient `log 4` is claimed for `π`.**
The passage from `θ` to `π` in `primeCountingUpper_const_of_theta_le` costs an arbitrarily
small positive amount, so what is available for `π` is `log 4 + ε` for every `ε > 0`; the
value `κ = 2` is instantiated precisely to keep a wide, safe margin.  The docstrings of
`primeCountingUpper_log4` (which uses the strictly larger constant `1.3863 > log 4`) and of
`largePrimeFactorSet` were corrected in this run to state this explicitly.

With the manuscript's `c = 8` the side condition `2κ/8 ≤ 0.27` forces `κ ≤ 1.08`, which is
below `log 4 = 1.38629…`; hence `largePrimeFactor_eighth` genuinely stays conditional on
`LargePrimeInputs` (which is in turn reducible to Wiener–Ikehara, see
`REPORT_PrimeCountingUpper.md`).

### 4.3 Nothing downstream changes

The only property of the threshold constant `c` used downstream (Proposition 5.1,
`FactorialHypergraph/Estimates.lean` / `MainConditional.lean`) is that `i log i / c > L` when
`L/10 ≤ i ≤ L` and `L` is large — true for every fixed `c`.  Consequently replacing `1/8` by
`1/40` changes only the "sufficiently large `L`" threshold.  The statements of

* Theorem 1.1 — `cover_cost` / `cover_cost_of_sieve_theorem`,
* Theorem 1.2 — `main_quantitative` / `main_quantitative_of_sieve_theorem`,
* the auxiliary Erdős result — `auxiliary_erdos_problem` /
  `auxiliary_erdos_problem_of_sieve_theorem`,

are **literally unchanged**: each is quantified as "there exist `δ`/`η`/`L₀` such that for all
`L ≥ L₀` …", and only the witness `L₀` moves.  (This is verifiable by reading the four
statements in `FactorialHypergraph/MainConditional.lean` and `FactorialHypergraph/Assembly.lean`; they
contain no occurrence of the constant 8, 40, or of `largePrimeFactorSetC`.)

---


---

## Appendix C. Provenance of the earlier repairs (retained)

The repairs listed here were made in the previous run and are unchanged; §5.3 above rechecks
the counterexample that motivated the first of them.

* **Dimension hypothesis (repaired then, confirmed now).**  `UpperBoundSieveDimOne`
  originally assumed only the anchored dimension condition; the interval condition
  `∑_{ℓ ∈ P, w₁ < ℓ ≤ w₂} g(ℓ) log ℓ ≤ log(w₂/w₁) + C₁` was added, and proved
  unconditionally for arbitrary finite prime sets in `dimension_condition_interval`
  (`FactorialHypergraph/A3Product.lean`), which rests on the elementary unconditional
  `FactorialHypergraph/MertensLower.lean`.  `FactorialHypergraph/A3Apply.lean` applies the sieve with
  `C₁ = max C₁a C₁b`.
* **`1/8` versus `1/40`.**  `largePrimeFactor_fortieth` (unconditional, used downstream) and
  `largePrimeFactor_eighth` (conditional, the manuscript's constant); see Appendix B.
* **Docstring accuracy fixes** to `sieveProduct_one_le`, `sieveProduct_le`, `sum_gMaj_div_le`,
  `primeCountingUpper_log4`, `largePrimeFactorSet`.
