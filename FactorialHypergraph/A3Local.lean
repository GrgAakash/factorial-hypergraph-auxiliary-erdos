/-
# The polynomial reduction and the local counting formula

Layer 1 (second half) of the sieve estimate (A3).  Fix `L`, a modulus `m ≥ 1` and a root
`a mod m` of `f`, represented by `0 ≤ a < m`.  Writing `i = a + m t`, we introduce

* `Tset L m a = {t : 1 ≤ a + m t ≤ L}`, an interval of integers, of cardinality
  `H = L/m + O(1)`;
* `Gpoly m a t = f(a + m t)/m`, which is an integer because `m ∣ f(a)`, and which as a
  polynomial in `t` equals `m t² + (2a+3) t + f(a)/m`, of discriminant `5` and primitive.

The main result is the **local counting formula**

  `#{t ∈ T : d ∣ G(t)} = H ρ(d)/d + r_d`,  `|r_d| ≤ ρ(d)`,

for every `d ≥ 1` coprime to `m`, where `ρ = rootCount` is the *base* root-count function.
(The sieve is then applied with the local density obtained by restricting `ρ` to the primes
that do not divide `10 m`; the two functions are deliberately kept distinct.)
-/
import FactorialHypergraph.A3Roots

namespace FactorialHypergraph

open Finset

/-! ## The interval of `t` and the polynomial `G` -/

/-- `T_{a,m} = {t : 1 ≤ a + m t ≤ L}`. -/
def Tset (L m a : ℕ) : Finset ℕ :=
  (Finset.range (L + 1)).filter (fun t => 1 ≤ a + m * t ∧ a + m * t ≤ L)

/-- `G_{a,m}(t) = f(a + m t)/m`. -/
def Gpoly (m a t : ℕ) : ℕ := fq (a + m * t) / m

theorem mem_Tset {L m a t : ℕ} (hm : 0 < m) :
    t ∈ Tset L m a ↔ (1 ≤ a + m * t ∧ a + m * t ≤ L) := by
  constructor
  · intro ht; exact (Finset.mem_filter.mp ht).2
  · intro ht
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ht⟩
    have : t ≤ m * t := Nat.le_mul_of_pos_left t hm
    omega

/-- `m` divides `f(a + m t)` whenever it divides `f(a)`. -/
theorem dvd_fq_add_mul {m a : ℕ} (hdvd : m ∣ fq a) (t : ℕ) : m ∣ fq (a + m * t) := by
  have h : a + m * t ≡ a [MOD m] := by
    simp [Nat.ModEq, Nat.add_mul_mod_self_left]
  exact Nat.modEq_zero_iff_dvd.mp ((fq_modEq h).trans (Nat.modEq_zero_iff_dvd.mpr hdvd))

/-- `m · G(t) = f(a + m t)`. -/
theorem Gpoly_spec {m a : ℕ} (hdvd : m ∣ fq a) (t : ℕ) :
    m * Gpoly m a t = fq (a + m * t) :=
  Nat.mul_div_cancel' (dvd_fq_add_mul hdvd t)

/-- The manuscript's explicit form `G(t) = m t² + (2a+3) t + f(a)/m`. -/
theorem Gpoly_eq {m a : ℕ} (hm : 0 < m) (_hdvd : m ∣ fq a) (t : ℕ) :
    Gpoly m a t = m * t ^ 2 + (2 * a + 3) * t + fq a / m := by
  have h : fq (a + m * t) = m * (m * t ^ 2 + (2 * a + 3) * t) + fq a := by
    unfold fq; ring
  unfold Gpoly
  rw [h, Nat.mul_add_div hm]

/-- Positivity of `G`. -/
theorem Gpoly_pos {m a : ℕ} (_hm : 0 < m) (hdvd : m ∣ fq a) (t : ℕ) : 0 < Gpoly m a t := by
  by_contra hcon
  push_neg at hcon
  have h0 : Gpoly m a t = 0 := by omega
  have := Gpoly_spec hdvd t
  rw [h0, Nat.mul_zero] at this
  exact (fq_pos (a + m * t)).ne this

/-- **Discriminant 5.**  `4 m G(t) + 5 = (2(a + m t) + 3)²`. -/
theorem Gpoly_discriminant {m a : ℕ} (hdvd : m ∣ fq a) (t : ℕ) :
    4 * m * Gpoly m a t + 5 = (2 * (a + m * t) + 3) ^ 2 := by
  calc 4 * m * Gpoly m a t + 5 = 4 * (m * Gpoly m a t) + 5 := by ring
    _ = 4 * fq (a + m * t) + 5 := by rw [Gpoly_spec hdvd t]
    _ = (2 * (a + m * t) + 3) ^ 2 := four_mul_fq_add_five _

/-- **Primitivity of `G`.**  No prime divides all three coefficients of `G`; indeed the
square of such a prime would divide `(2a+3)² - 4 f(a) = 5`. -/
theorem Gpoly_primitive {m a : ℕ} (_hm : 0 < m) (hdvd : m ∣ fq a) {p : ℕ} (hp : p.Prime)
    (h1 : p ∣ m) (h2 : p ∣ 2 * a + 3) : ¬ (p ∣ fq a / m) := by
  intro h3
  obtain ⟨u, hu⟩ := h1
  obtain ⟨v, hv⟩ := h3
  have hfa : fq a = m * (fq a / m) := (Nat.mul_div_cancel' hdvd).symm
  have hsq : p * p ∣ fq a := ⟨u * v, by rw [hfa, hv, hu]; ring⟩
  have hsq2 : p * p ∣ (2 * a + 3) ^ 2 := by
    obtain ⟨w, hw⟩ := h2
    exact ⟨w * w, by rw [hw]; ring⟩
  have hkey : p * p ∣ 5 := by
    have h5 : (2 * a + 3) ^ 2 = 4 * fq a + 5 := (four_mul_fq_add_five a).symm
    have hd4 : p * p ∣ 4 * fq a := Dvd.dvd.mul_left hsq 4
    have hsub : p * p ∣ (4 * fq a + 5) - 4 * fq a := Nat.dvd_sub (h5 ▸ hsq2) hd4
    simpa using hsub
  have hple : p * p ≤ 5 := Nat.le_of_dvd (by norm_num) hkey
  have hp2 : 2 ≤ p := hp.two_le
  have hp5 : p ≤ 5 := by nlinarith
  interval_cases p <;> omega

/-! ## The interval structure and the length `H` -/

/-- `T_{a,m}` is an interval of integers. -/
theorem Tset_eq_Ico (L m a : ℕ) (hm : 0 < m) :
    Tset L m a =
      Finset.Ico (if a = 0 then 1 else 0) (if a ≤ L then (L - a) / m + 1 else 0) := by
  ext t
  rw [mem_Tset hm, Finset.mem_Ico]
  have hdiv : ∀ x : ℕ, m * t ≤ x ↔ t < x / m + 1 := by
    intro x
    rw [Nat.lt_succ_iff, Nat.le_div_iff_mul_le hm, Nat.mul_comm]
  by_cases ha : a ≤ L
  · rw [if_pos ha]
    have key : (a + m * t ≤ L) ↔ (t < (L - a) / m + 1) := by
      rw [← hdiv (L - a)]; omega
    by_cases h0 : a = 0
    · subst h0
      rw [if_pos rfl]
      have hone : (1 ≤ 0 + m * t) ↔ 1 ≤ t := by
        constructor
        · intro h
          rcases Nat.eq_zero_or_pos t with rfl | ht
          · simp at h
          · exact ht
        · intro h
          have : m * 1 ≤ m * t := Nat.mul_le_mul_left m h
          omega
      rw [hone, key]
    · rw [if_neg h0]
      rw [key]
      constructor
      · rintro ⟨-, h2⟩; exact ⟨Nat.zero_le _, h2⟩
      · rintro ⟨-, h2⟩; exact ⟨by omega, h2⟩
  · rw [if_neg ha]
    constructor
    · rintro ⟨-, h2⟩; omega
    · rintro ⟨-, h2⟩; omega

/-- `T_{a,m}` is an interval of integers (existential form). -/
theorem Tset_exists_Ico (L m a : ℕ) (hm : 0 < m) :
    ∃ t₀ t₁ : ℕ, Tset L m a = Finset.Ico t₀ t₁ :=
  ⟨_, _, Tset_eq_Ico L m a hm⟩

/-- Elementary bounds for the natural-number quotient. -/
theorem nat_div_bounds (x m : ℕ) (hm : 0 < m) :
    ((x / m : ℕ) : ℝ) ≤ (x : ℝ) / (m : ℝ) ∧ (x : ℝ) / (m : ℝ) < ((x / m : ℕ) : ℝ) + 1 := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  refine ⟨Nat.cast_div_le, ?_⟩
  have h1 : m * (x / m) + x % m = x := Nat.div_add_mod x m
  have h2 : x % m < m := Nat.mod_lt _ hm
  have h1R : (m : ℝ) * ((x / m : ℕ) : ℝ) + ((x % m : ℕ) : ℝ) = (x : ℝ) := by exact_mod_cast h1
  have h2R : ((x % m : ℕ) : ℝ) < (m : ℝ) := by exact_mod_cast h2
  rw [div_lt_iff₀ hmR]
  nlinarith

/-- `H ≤ L/m + 1`. -/
theorem card_Tset_le (L m a : ℕ) (hm : 0 < m) :
    ((Tset L m a).card : ℝ) ≤ (L : ℝ) / (m : ℝ) + 1 := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  rw [Tset_eq_Ico L m a hm, Nat.card_Ico]
  by_cases ha : a ≤ L
  · rw [if_pos ha]
    have hle : ((L - a) / m + 1 - (if a = 0 then 1 else 0) : ℕ) ≤ (L - a) / m + 1 :=
      Nat.sub_le _ _
    have hleR : (((L - a) / m + 1 - (if a = 0 then 1 else 0) : ℕ) : ℝ)
        ≤ (((L - a) / m : ℕ) : ℝ) + 1 := by
      have : (((L - a) / m + 1 - (if a = 0 then 1 else 0) : ℕ) : ℝ)
          ≤ (((L - a) / m + 1 : ℕ) : ℝ) := by exact_mod_cast hle
      push_cast at this
      linarith
    have hd := (nat_div_bounds (L - a) m hm).1
    have hsub : ((L - a : ℕ) : ℝ) ≤ (L : ℝ) := by
      have : (L - a : ℕ) ≤ L := Nat.sub_le _ _
      exact_mod_cast this
    have hmono : ((L - a : ℕ) : ℝ) / (m : ℝ) ≤ (L : ℝ) / (m : ℝ) := by gcongr
    linarith
  · rw [if_neg ha]
    have h0 : ((0 - (if a = 0 then 1 else 0) : ℕ) : ℝ) = 0 := by
      split_ifs <;> simp
    rw [h0]
    positivity

/-- `H ≥ L/m - 1`. -/
theorem le_card_Tset (L m a : ℕ) (hm : 0 < m) (ham : a < m) :
    (L : ℝ) / (m : ℝ) - 1 ≤ ((Tset L m a).card : ℝ) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  rw [Tset_eq_Ico L m a hm, Nat.card_Ico]
  by_cases ha : a ≤ L
  · rw [if_pos ha]
    by_cases h0 : a = 0
    · subst h0
      rw [if_pos rfl]
      have hsimp : (L - 0) / m + 1 - 1 = L / m := by simp
      rw [hsimp]
      have hd := (nat_div_bounds L m hm).2
      linarith
    · rw [if_neg h0]
      rw [Nat.sub_zero]
      have hd := (nat_div_bounds (L - a) m hm).2
      have hcast : ((L - a : ℕ) : ℝ) = (L : ℝ) - (a : ℝ) := by
        push_cast [Nat.cast_sub ha]; ring
      have haR : (a : ℝ) ≤ (m : ℝ) := by exact_mod_cast le_of_lt ham
      have hstep : (L : ℝ) / (m : ℝ) - 1 ≤ ((L - a : ℕ) : ℝ) / (m : ℝ) := by
        rw [hcast, le_div_iff₀ hmR, sub_mul, div_mul_cancel₀ _ (ne_of_gt hmR)]
        linarith
      push_cast
      linarith
  · rw [if_neg ha]
    have hmL : L < m := by omega
    have hLm : (L : ℝ) / (m : ℝ) ≤ 1 := by
      rw [div_le_one hmR]
      exact_mod_cast le_of_lt hmL
    have h0 : (0 : ℝ) ≤ ((0 - (if a = 0 then 1 else 0) : ℕ) : ℝ) := by positivity
    linarith

/-! ## Counting an interval in a residue class -/

/-- Exactly one element of a window of `d` consecutive integers lies in a given class. -/
theorem card_window (u d r : ℕ) (hd : 0 < d) (hr : r < d) :
    ((Finset.Ico u (u + d)).filter (fun t => t % d = r)).card = 1 := by
  classical
  have hinj : Set.InjOn (fun t => t % d) (Finset.Ico u (u + d)) := by
    intro x hx y hy hxy
    simp only [Finset.coe_Ico, Set.mem_Ico] at hx hy
    have hmod : x % d = y % d := hxy
    have hdvd : (d : ℤ) ∣ (y : ℤ) - x := (Nat.modEq_iff_dvd (n := d) (a := x) (b := y)).mp hmod
    have := Int.eq_zero_of_abs_lt_dvd hdvd (by rw [abs_lt]; omega)
    omega
  have himg : (Finset.Ico u (u + d)).image (fun t => t % d) = Finset.range d := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_image] at hx
      obtain ⟨t, _, rfl⟩ := hx
      exact Finset.mem_range.mpr (Nat.mod_lt _ hd)
    · rw [Finset.card_image_of_injOn hinj]
      simp
  have hex : ∃ t ∈ Finset.Ico u (u + d), t % d = r := by
    have : r ∈ (Finset.Ico u (u + d)).image (fun t => t % d) := by
      rw [himg]; exact Finset.mem_range.mpr hr
    simpa using this
  obtain ⟨t, ht, htr⟩ := hex
  refine Finset.card_eq_one.mpr ⟨t, ?_⟩
  apply Finset.eq_singleton_iff_unique_mem.mpr
  refine ⟨Finset.mem_filter.mpr ⟨ht, htr⟩, ?_⟩
  intro y hy
  simp only [Finset.mem_filter] at hy
  exact hinj hy.1 ht (by show y % d = t % d; rw [hy.2, htr])

/-- At most one element of a window of length `≤ d` lies in a given class. -/
theorem card_window_le (u s d r : ℕ) (hs : s ≤ d) :
    ((Finset.Ico u (u + s)).filter (fun t => t % d = r)).card ≤ 1 := by
  classical
  refine Finset.card_le_one.mpr ?_
  intro x hx y hy
  simp only [Finset.mem_filter, Finset.mem_Ico] at hx hy
  have hmod : x % d = y % d := by rw [hx.2, hy.2]
  have hdvd : (d : ℤ) ∣ (y : ℤ) - x := (Nat.modEq_iff_dvd (n := d) (a := x) (b := y)).mp hmod
  have := Int.eq_zero_of_abs_lt_dvd hdvd (by rw [abs_lt]; omega)
  omega

/-- Splitting an interval into `q` full periods and a remainder. -/
theorem card_block (d r : ℕ) (hd : 0 < d) (hr : r < d) (q : ℕ) : ∀ u s : ℕ,
    ((Finset.Ico u (u + (d * q + s))).filter (fun t => t % d = r)).card
      = q + ((Finset.Ico (u + d * q) (u + d * q + s)).filter (fun t => t % d = r)).card := by
  induction q with
  | zero => intro u s; simp
  | succ n ih =>
    intro u s
    have hsplit : Finset.Ico u (u + (d * (n + 1) + s))
        = Finset.Ico u (u + d) ∪ Finset.Ico (u + d) (u + (d * (n + 1) + s)) := by
      rw [Finset.Ico_union_Ico_eq_Ico (by omega) (by nlinarith)]
    have hdisj : Disjoint (Finset.Ico u (u + d)) (Finset.Ico (u + d) (u + (d * (n + 1) + s))) :=
      Finset.Ico_disjoint_Ico_consecutive _ _ _
    classical
    rw [hsplit, Finset.filter_union,
      Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hdisj),
      card_window u d r hd hr]
    have harg : u + (d * (n + 1) + s) = (u + d) + (d * n + s) := by ring
    rw [harg, ih (u + d) s]
    have hrw : u + d + d * n = u + d * (n + 1) := by ring
    rw [hrw]
    omega

/-- Counting the elements of an interval in a fixed residue class: the count differs from
`(length)/d` by at most `1`. -/
theorem abs_card_Ico_mod_sub_le (t₀ t₁ d r : ℕ) (hd : 0 < d) (hr : r < d) :
    |((((Finset.Ico t₀ t₁).filter (fun t => t % d = r)).card : ℝ)) -
      ((Finset.Ico t₀ t₁).card : ℝ) / (d : ℝ)| ≤ 1 := by
  classical
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  rcases Nat.lt_or_ge t₁ t₀ with hlt | hge
  · rw [Finset.Ico_eq_empty (by omega)]
    simp
  · set H := t₁ - t₀ with hH
    have hIco : Finset.Ico t₀ t₁ = Finset.Ico t₀ (t₀ + (d * (H / d) + H % d)) := by
      have hdm : d * (H / d) + H % d = H := Nat.div_add_mod H d
      rw [hdm]
      congr 1
      omega
    rw [hIco, card_block d r hd hr (H / d) t₀ (H % d)]
    have hcard : (Finset.Ico t₀ (t₀ + (d * (H / d) + H % d))).card = H := by
      rw [Nat.card_Ico]
      have hdm : d * (H / d) + H % d = H := Nat.div_add_mod H d
      omega
    rw [hcard]
    set N₀ := ((Finset.Ico (t₀ + d * (H / d)) (t₀ + d * (H / d) + H % d)).filter
      (fun t => t % d = r)).card with hN₀
    have hN₀le : N₀ ≤ 1 := card_window_le _ _ _ _ (le_of_lt (Nat.mod_lt _ hd))
    have hHd : (H : ℝ) = (d : ℝ) * ((H / d : ℕ) : ℝ) + ((H % d : ℕ) : ℝ) := by
      have hdm : d * (H / d) + H % d = H := Nat.div_add_mod H d
      exact_mod_cast hdm.symm
    have hmod : ((H % d : ℕ) : ℝ) < (d : ℝ) := by exact_mod_cast Nat.mod_lt _ hd
    have hmod0 : (0 : ℝ) ≤ ((H % d : ℕ) : ℝ) := by positivity
    have hN₀R : (N₀ : ℝ) ≤ 1 := by exact_mod_cast hN₀le
    have hN₀0 : (0 : ℝ) ≤ (N₀ : ℝ) := by positivity
    have hHdiv : (H : ℝ) / (d : ℝ) = ((H / d : ℕ) : ℝ) + ((H % d : ℕ) : ℝ) / (d : ℝ) := by
      rw [hHd]; field_simp
    have hfrac0 : (0 : ℝ) ≤ ((H % d : ℕ) : ℝ) / (d : ℝ) := by positivity
    have hfrac1 : ((H % d : ℕ) : ℝ) / (d : ℝ) ≤ 1 := by
      rw [div_le_one hdR]; linarith
    rw [abs_le]
    push_cast
    rw [hHdiv]
    constructor <;> linarith

/-! ## The local counting formula -/

/-- The number of residues `r mod d` with `d ∣ G(r)` equals `ρ(d) = rootCount d`, for `d`
coprime to `m`: the affine substitution `t ↦ a + m t` is a bijection modulo `d`. -/
theorem card_roots_Gpoly {m a d : ℕ} (_hm : 0 < m) (hdvd : m ∣ fq a) (hd : 0 < d)
    (hcop : Nat.Coprime d m) :
    ((Finset.range d).filter (fun r => d ∣ Gpoly m a r)).card = rootCount d := by
  classical
  -- `d ∣ G(t) ↔ d ∣ f(a + m t)`
  have hiff : ∀ t : ℕ, d ∣ Gpoly m a t ↔ d ∣ fq (a + m * t) := by
    intro t
    constructor
    · intro h
      rw [← Gpoly_spec hdvd t]
      exact Dvd.dvd.mul_left h m
    · intro h
      rw [← Gpoly_spec hdvd t] at h
      exact (Nat.Coprime.dvd_of_dvd_mul_left hcop h)
  -- the affine map is injective modulo `d`
  have hinj : ∀ x ∈ Finset.range d, ∀ y ∈ Finset.range d,
      (a + m * x) % d = (a + m * y) % d → x = y := by
    intro x hx y hy hxy
    simp only [Finset.mem_range] at hx hy
    have h1 : a + m * x ≡ a + m * y [MOD d] := hxy
    have h2 : m * x ≡ m * y [MOD d] := (Nat.ModEq.add_left_cancel' a h1)
    have h3 : x ≡ y [MOD d] := (Nat.ModEq.cancel_left_of_coprime (by simpa [Nat.Coprime, Nat.gcd_comm] using hcop) h2)
    exact Nat.ModEq.eq_of_lt_of_lt h3 hx hy
  refine Finset.card_bij (fun r _ => (a + m * r) % d) ?_ ?_ ?_
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_range] at hr ⊢
    refine ⟨Nat.mod_lt _ hd, ?_⟩
    exact (dvd_fq_congr (Nat.mod_modEq (a + m * r) d)).mpr ((hiff r).mp hr.2)
  · intro x hx y hy hxy
    exact hinj x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 hxy
  · intro s hs
    simp only [Finset.mem_filter, Finset.mem_range] at hs
    -- surjectivity: the affine map permutes `range d`
    have himg : (Finset.range d).image (fun r => (a + m * r) % d) = Finset.range d := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        simp only [Finset.mem_image] at hx
        obtain ⟨r, _, rfl⟩ := hx
        exact Finset.mem_range.mpr (Nat.mod_lt _ hd)
      · rw [Finset.card_image_of_injOn (fun x hx y hy h => hinj x hx y hy h)]
    have : s ∈ (Finset.range d).image (fun r => (a + m * r) % d) := by
      rw [himg]; exact Finset.mem_range.mpr hs.1
    simp only [Finset.mem_image, Finset.mem_range] at this
    obtain ⟨r, hr, hrs⟩ := this
    refine ⟨r, ?_, hrs⟩
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨hr, (hiff r).mpr ?_⟩
    have hcong : (a + m * r) ≡ s [MOD d] := by
      unfold Nat.ModEq
      rw [hrs, Nat.mod_eq_of_lt hs.1]
    exact (dvd_fq_congr hcong).mpr hs.2

/-- **The local counting formula** `#{t ∈ T : d ∣ G(t)} = H ρ(d)/d + r_d` with
`|r_d| ≤ ρ(d)`, for every `d ≥ 1` coprime to `m`. -/
theorem abs_card_dvd_Gpoly_sub_le {L m a d : ℕ} (hm : 0 < m) (hdvd : m ∣ fq a) (hd : 0 < d)
    (hcop : Nat.Coprime d m) :
    |(((Tset L m a).filter (fun t => d ∣ Gpoly m a t)).card : ℝ)
        - ((Tset L m a).card : ℝ) * (rootCount d : ℝ) / (d : ℝ)| ≤ (rootCount d : ℝ) := by
  classical
  obtain ⟨t₀, t₁, hT⟩ := Tset_exists_Ico L m a hm
  set K := (Finset.range d).filter (fun r => d ∣ Gpoly m a r) with hK
  have hKcard : K.card = rootCount d := card_roots_Gpoly hm hdvd hd hcop
  -- divisibility of `G(t)` depends only on `t mod d`
  have hdep : ∀ t : ℕ, (d ∣ Gpoly m a t) ↔ t % d ∈ K := by
    intro t
    have hcong : (a + m * (t % d)) ≡ (a + m * t) [MOD d] :=
      Nat.ModEq.add_left a (Nat.ModEq.mul_left m (Nat.mod_modEq t d))
    have h1 : d ∣ Gpoly m a t ↔ d ∣ fq (a + m * t) := by
      constructor
      · intro h; rw [← Gpoly_spec hdvd t]; exact Dvd.dvd.mul_left h m
      · intro h; rw [← Gpoly_spec hdvd t] at h; exact Nat.Coprime.dvd_of_dvd_mul_left hcop h
    have h2 : d ∣ Gpoly m a (t % d) ↔ d ∣ fq (a + m * (t % d)) := by
      constructor
      · intro h; rw [← Gpoly_spec hdvd (t % d)]; exact Dvd.dvd.mul_left h m
      · intro h; rw [← Gpoly_spec hdvd (t % d)] at h
        exact Nat.Coprime.dvd_of_dvd_mul_left hcop h
    rw [hK]
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · intro h
      exact ⟨Nat.mod_lt _ hd, h2.mpr ((dvd_fq_congr hcong).mpr (h1.mp h))⟩
    · rintro ⟨-, h⟩
      exact h1.mpr ((dvd_fq_congr hcong).mp (h2.mp h))
  -- split the count according to the residue class
  have hsplit : ((Tset L m a).filter (fun t => d ∣ Gpoly m a t)).card
      = ∑ r ∈ K, ((Tset L m a).filter (fun t => t % d = r)).card := by
    have hmem : Set.MapsTo (fun x => x % d)
        ↑((Tset L m a).filter (fun t => d ∣ Gpoly m a t)) (↑K : Set ℕ) := by
      intro x hx
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe] at hx ⊢
      exact (hdep x).mp hx.2
    rw [Finset.card_eq_sum_card_fiberwise hmem]
    refine Finset.sum_congr rfl (fun r hr => ?_)
    congr 1
    ext t
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨ht, -⟩, hmod⟩; exact ⟨ht, hmod⟩
    · rintro ⟨ht, hmod⟩
      exact ⟨⟨ht, (hdep t).mpr (hmod ▸ hr)⟩, hmod⟩
  rw [hsplit, hT]
  push_cast
  have hrw : (∑ r ∈ K, (((Finset.Ico t₀ t₁).filter (fun t => t % d = r)).card : ℝ))
      - ((Finset.Ico t₀ t₁).card : ℝ) * (rootCount d : ℝ) / (d : ℝ)
      = ∑ r ∈ K, ((((Finset.Ico t₀ t₁).filter (fun t => t % d = r)).card : ℝ)
          - ((Finset.Ico t₀ t₁).card : ℝ) / (d : ℝ)) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hKcard]
    ring
  rw [hrw]
  have hbound : ∀ r ∈ K, |(((Finset.Ico t₀ t₁).filter (fun t => t % d = r)).card : ℝ)
      - ((Finset.Ico t₀ t₁).card : ℝ) / (d : ℝ)| ≤ 1 := by
    intro r hr
    have : r < d := Finset.mem_range.mp (Finset.mem_filter.mp (hK ▸ hr)).1
    exact abs_card_Ico_mod_sub_le t₀ t₁ d r hd this
  calc |∑ r ∈ K, ((((Finset.Ico t₀ t₁).filter (fun t => t % d = r)).card : ℝ)
          - ((Finset.Ico t₀ t₁).card : ℝ) / (d : ℝ))|
      ≤ ∑ r ∈ K, |(((Finset.Ico t₀ t₁).filter (fun t => t % d = r)).card : ℝ)
          - ((Finset.Ico t₀ t₁).card : ℝ) / (d : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r ∈ K, (1 : ℝ) := Finset.sum_le_sum hbound
    _ = (rootCount d : ℝ) := by rw [Finset.sum_const, hKcard]; simp

end FactorialHypergraph
