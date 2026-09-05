/-
# Continuants

Heilbronn's bijection (Heilbronn 1969, p. 93), which underlies equation
(eq. heilbron) of Blomer--Bux, sends a continued-fraction expansion
`n = K(c₀,…,c_l)` together with a split point `j` to the quadruple

  `x = K(c₀,…,c_j)`,   `x' = K(c_{j+1},…,c_l)`,
  `y = K(c₀,…,c_{j-1})`, `y' = K(c_{j+2},…,c_l)`,

and the relation `n = x·x' + y·y'` that makes the quadruple a solution is
exactly **Euler's continuant identity**.  This file defines the continuant of a
list and proves that identity.

The continuant is `K[] = 1`, `K[c] = c`, `K(c₀ :: c₁ :: cs) = c₀·K(c₁ :: cs) + K cs`;
`K` of the expansion of a rational is the numerator of its continued fraction.
-/

import BlockCycleRotation.DivisorBound
import BlockCycleRotation.Euclid

namespace BlockCycleRotation

/-- The continuant of a list, `K(c₀,…,c_l)`. -/
def K : List ℕ → ℕ
  | [] => 1
  | [c] => c
  | c₀ :: c₁ :: cs => c₀ * K (c₁ :: cs) + K cs

@[simp] theorem K_nil : K [] = 1 := rfl

@[simp] theorem K_singleton (c : ℕ) : K [c] = c := rfl

theorem K_cons_cons (c₀ c₁ : ℕ) (cs : List ℕ) :
    K (c₀ :: c₁ :: cs) = c₀ * K (c₁ :: cs) + K cs := rfl

/-- **Euler's continuant identity.**  Splitting a list at any interior point,

  `K (l₁ ++ l₂) = K l₁ · K l₂ + K (l₁.dropLast) · K (l₂.tail)`.

This is the identity that turns a split continued-fraction expansion into a
solution of `n = x·x' + y·y'`. -/
theorem K_append : ∀ (l₁ l₂ : List ℕ), l₁ ≠ [] → l₂ ≠ [] →
    K (l₁ ++ l₂) = K l₁ * K l₂ + K l₁.dropLast * K l₂.tail := by
  intro l₁
  induction l₁ using K.induct with
  | case1 => intro _ h; exact absurd rfl h
  | case2 c =>
    intro l₂ _ h₂
    match l₂, h₂ with
    | d :: ds, _ =>
      simp [K_cons_cons]
  | case3 c₀ c₁ cs ih1 ih2 =>
    intro l₂ _ h₂
    rcases cs with _ | ⟨c₂, cs'⟩
    · -- `l₁ = [c₀, c₁]`
      match l₂, h₂ with
      | d :: ds, _ =>
        simp [K_cons_cons]
        ring
    · -- `cs` is nonempty, so both inductive hypotheses apply
      have hcs : (c₂ :: cs') ≠ [] := by simp
      have h1 := ih1 l₂ (by simp) h₂
      have h2 := ih2 l₂ hcs h₂
      simp only [List.cons_append, K_cons_cons, List.dropLast_cons_cons] at *
      rw [h1, h2]
      ring

/-- The mirrored recursion: appending an entry at the end. -/
theorem K_concat (l : List ℕ) (h : l ≠ []) (c : ℕ) :
    K (l ++ [c]) = c * K l + K l.dropLast := by
  rw [K_append l [c] h (by simp)]
  simp [Nat.mul_comm]

/-- **Continuants are palindromic**: `K` is invariant under reversing the list.

This is what lets Heilbronn's bijection read the second half of the expansion
backwards. -/
theorem K_reverse : ∀ l : List ℕ, K l.reverse = K l := by
  intro l
  induction l using K.induct with
  | case1 => simp
  | case2 c => simp
  | case3 c₀ c₁ cs ih1 ih2 =>
    have hne : ((c₁ :: cs).reverse) ≠ [] := by simp
    have hdrop : ((c₁ :: cs).reverse).dropLast = cs.reverse := by
      rw [List.reverse_cons]
      simp
    rw [List.reverse_cons, K_concat _ hne c₀, ih1, hdrop, ih2, K_cons_cons]

/-- **Consecutive continuants are coprime**: `gcd (K l) (K l.dropLast) = 1`.

This supplies the condition `gcd(x, y) = 1` in Heilbronn's correspondence. -/
theorem K_coprime : ∀ l : List ℕ, Nat.gcd (K l) (K l.dropLast) = 1 := by
  intro l
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton m c ih =>
    by_cases hm : m = []
    · subst hm; simp
    · have hdl : (m ++ [c]).dropLast = m := by simp
      rw [K_concat m hm c, hdl, Nat.add_comm, Nat.mul_comm c (K m),
        Nat.gcd_add_mul_left_left, Nat.gcd_comm]
      exact ih

/-! ## Size conditions

Heilbronn's quadruples satisfy `x > y ≥ 1` and `x' > y' ≥ 1`, where `y` is the
continuant of the truncated prefix and `y'` that of the truncated suffix.  These
follow from positivity together with the two truncation inequalities below. -/

/-- Continuants of lists of positive entries are positive. -/
theorem K_pos : ∀ l : List ℕ, (∀ c ∈ l, 1 ≤ c) → 1 ≤ K l := by
  intro l
  induction l using K.induct with
  | case1 => intro _; simp
  | case2 c => intro h; exact h c (by simp)
  | case3 c₀ c₁ cs ih1 ih2 =>
    intro h
    have h1 := ih1 (fun x hx => h x (List.mem_cons_of_mem c₀ hx))
    have h2 := ih2 (fun x hx => h x (List.mem_cons_of_mem c₀ (List.mem_cons_of_mem c₁ hx)))
    have hc0 : 1 ≤ c₀ := h c₀ (by simp)
    rw [K_cons_cons]
    nlinarith

/-- Dropping the last entry strictly decreases the continuant, provided at least
two entries remain in play. -/
theorem K_dropLast_lt : ∀ l : List ℕ, 2 ≤ l.length → (∀ c ∈ l, 1 ≤ c) →
    K l.dropLast < K l := by
  intro l
  induction l using List.reverseRecOn with
  | nil => intro h _; simp at h
  | append_singleton m c _ =>
    intro hlen hpos
    have hm : m ≠ [] := by
      rintro rfl
      simp at hlen
    have hdl : (m ++ [c]).dropLast = m := by simp
    have hsub : ∀ x ∈ m, x ∈ m ++ [c] := fun x hx => List.mem_append.2 (Or.inl hx)
    have hc1 : 1 ≤ c := hpos c (by simp)
    have hmp : 1 ≤ K m := K_pos m (fun x hx => hpos x (hsub x hx))
    have hmd : 1 ≤ K m.dropLast :=
      K_pos _ (fun x hx => hpos x (hsub x (List.dropLast_subset m hx)))
    rw [K_concat m hm c, hdl]
    nlinarith

/-- Dropping the first entry strictly decreases the continuant.  This is the
mirror image of `K_dropLast_lt`, via `K_reverse`. -/
theorem K_tail_lt (l : List ℕ) (hlen : 2 ≤ l.length) (hpos : ∀ c ∈ l, 1 ≤ c) :
    K l.tail < K l := by
  have hrev : (l.reverse).dropLast = (l.tail).reverse := by
    rcases l with _ | ⟨a, t⟩
    · simp
    · simp
  have hlen' : 2 ≤ l.reverse.length := by simpa using hlen
  have hpos' : ∀ c ∈ l.reverse, 1 ≤ c := by
    intro c hc
    exact hpos c (List.mem_reverse.1 hc)
  have h := K_dropLast_lt l.reverse hlen' hpos'
  rwa [hrev, K_reverse, K_reverse] at h

/-- The prefix continuants are coprime, mirrored to suffixes. -/
theorem K_coprime_tail (l : List ℕ) : Nat.gcd (K l) (K l.tail) = 1 := by
  have hrev : (l.reverse).dropLast = (l.tail).reverse := by
    rcases l with _ | ⟨a, t⟩ <;> simp
  have h := K_coprime l.reverse
  rwa [hrev, K_reverse, K_reverse] at h

/-- `K l.dropLast < K l`, allowing a one-element list provided its entry is at
least `2` — which is Heilbronn's condition `2 ≤ c₀`. -/
theorem K_dropLast_lt' {l : List ℕ} (hne : l ≠ []) (hpos : ∀ c ∈ l, 1 ≤ c)
    (hsingle : l.length = 1 → 2 ≤ K l) : K l.dropLast < K l := by
  rcases Nat.lt_or_ge l.length 2 with hlen | hlen
  · have h1 : l.length = 1 := by
      have hne' : l.length ≠ 0 := by simpa using hne
      omega
    obtain ⟨c, hc⟩ := List.length_eq_one_iff.1 h1
    subst hc
    have h2 := hsingle h1
    simp at h2 ⊢
    omega
  · exact K_dropLast_lt l hlen hpos

/-- `K l.tail < K l`, allowing a one-element list provided its entry is at least
`2` — Heilbronn's condition `2 ≤ c_l`. -/
theorem K_tail_lt' {l : List ℕ} (hne : l ≠ []) (hpos : ∀ c ∈ l, 1 ≤ c)
    (hsingle : l.length = 1 → 2 ≤ K l) : K l.tail < K l := by
  rcases Nat.lt_or_ge l.length 2 with hlen | hlen
  · have h1 : l.length = 1 := by
      have hne' : l.length ≠ 0 := by simpa using hne
      omega
    obtain ⟨c, hc⟩ := List.length_eq_one_iff.1 h1
    subst hc
    have h2 := hsingle h1
    simp at h2 ⊢
    omega
  · exact K_tail_lt l hlen hpos

/-! ## Heilbronn's correspondence, forward direction

Splitting an expansion `n = K (l₁ ++ l₂)` at an interior point produces the
quadruple

  `x = K l₁`,  `x' = K l₂`,  `y = K l₁.dropLast`,  `y' = K l₂.tail`,

and the theorem below is that this quadruple satisfies every condition defining
the target set of Heilbronn's bijection. -/

/-- **Heilbronn's correspondence, forward direction.**  The quadruple obtained by
splitting an expansion satisfies `n = x·x' + y·y'`, the size conditions
`x > y ≥ 1` and `x' > y' ≥ 1`, and the coprimality conditions. -/
theorem heilbronn_forward {l₁ l₂ : List ℕ} (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ [])
    (hpos₁ : ∀ c ∈ l₁, 1 ≤ c) (hpos₂ : ∀ c ∈ l₂, 1 ≤ c)
    (hfirst : l₁.length = 1 → 2 ≤ K l₁) (hlast : l₂.length = 1 → 2 ≤ K l₂) :
    K (l₁ ++ l₂) = K l₁ * K l₂ + K l₁.dropLast * K l₂.tail ∧
      K l₁.dropLast < K l₁ ∧ 1 ≤ K l₁.dropLast ∧
      K l₂.tail < K l₂ ∧ 1 ≤ K l₂.tail ∧
      Nat.gcd (K l₁) (K l₁.dropLast) = 1 ∧
      Nat.gcd (K l₂) (K l₂.tail) = 1 := by
  refine ⟨K_append l₁ l₂ h₁ h₂, K_dropLast_lt' h₁ hpos₁ hfirst, ?_,
    K_tail_lt' h₂ hpos₂ hlast, ?_, K_coprime l₁, K_coprime_tail l₂⟩
  · exact K_pos _ (fun x hx => hpos₁ x (List.dropLast_subset l₁ hx))
  · exact K_pos _ (fun x hx => hpos₂ x (List.tail_subset l₂ hx))

/-! ## The inverse map

Recovering the expansion from the pair `(x, y)` is exactly the Euclidean
algorithm: `K_concat` says `x = c·y + K m.dropLast` with `c = x / y` and
`K m.dropLast = x mod y`, so peeling entries off the end of the list is the
same as running Euclid on `(x, y)`.  This is the point of contact between
Heilbronn's bijection and the remainder sums of `Euclid.lean`. -/

/-- The continued-fraction expansion of `x / y`, read off by the Euclidean
algorithm.  The quotients are collected from the end of the list backwards. -/
def cf (x y : ℕ) : List ℕ :=
  if h : y = 0 then [] else cf y (x % y) ++ [x / y]
termination_by y
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero h)

@[simp] theorem cf_zero (a : ℕ) : cf a 0 = [] := by rw [cf]; simp

theorem cf_of_pos {x y : ℕ} (h : y ≠ 0) :
    cf x y = cf y (x % y) ++ [x / y] := by rw [cf]; simp [h]

/-- **Heilbronn's correspondence, inverse direction.**  Every coprime pair
`x > y ≥ 1` is `(K l, K l.dropLast)` for the expansion `l = cf x y`. -/
theorem K_cf : ∀ y x : ℕ, 1 ≤ y → y < x → Nat.gcd x y = 1 →
    K (cf x y) = x ∧ K (cf x y).dropLast = y := by
  intro y
  induction y using Nat.strong_induction_on with
  | _ y ih =>
    intro x hy1 hlt hgcd
    rcases Nat.lt_or_ge y 2 with h2 | h2
    · -- `y = 1`: the expansion is the single entry `x`
      have hyeq : y = 1 := by omega
      subst hyeq
      have h1 : cf x 1 = [x] := by
        rw [cf_of_pos (by norm_num), Nat.mod_one, cf_zero, Nat.div_one]
        simp
      rw [h1]
      simp
    · -- `y ≥ 2`: peel off the quotient and recurse
      have hyne : y ≠ 0 := by omega
      have hrlt : x % y < y := Nat.mod_lt _ (by omega)
      have hr1 : 1 ≤ x % y := by
        rcases Nat.eq_zero_or_pos (x % y) with h0 | h0
        · exfalso
          have hdvd : y ∣ x := Nat.dvd_of_mod_eq_zero h0
          have hg : Nat.gcd x y = y := Nat.gcd_eq_right hdvd
          omega
        · exact h0
      have hgcd' : Nat.gcd y (x % y) = 1 := by
        rw [← hgcd, Nat.gcd_comm x y, Nat.gcd_rec y x]
        exact Nat.gcd_comm _ _
      obtain ⟨hK, hKd⟩ := ih (x % y) hrlt y hr1 hrlt hgcd'
      have hne : cf y (x % y) ≠ [] := by
        intro hc
        rw [hc] at hK
        simp at hK
        omega
      have hcf : cf x y = cf y (x % y) ++ [x / y] := cf_of_pos hyne
      constructor
      · rw [hcf, K_concat _ hne (x / y), hK, hKd]
        have hdm := Nat.div_add_mod x y
        have hcomm : x / y * y = y * (x / y) := Nat.mul_comm _ _
        omega
      · rw [hcf]
        simpa using hK

/-- **Heilbronn's correspondence, injectivity.**  A normalised expansion is
recovered from its pair of continuants.

Normalisation is `2 ≤ c₀`: without it `[1, c]` and `[c+1]` have the same pair,
which is the familiar ambiguity of continued fractions. -/
theorem cf_K : ∀ l : List ℕ, l ≠ [] → (∀ c ∈ l, 1 ≤ c) → (∀ x ∈ l.head?, 2 ≤ x) →
    cf (K l) (K l.dropLast) = l := by
  intro l
  induction l using List.reverseRecOn with
  | nil => intro h; exact absurd rfl h
  | append_singleton m c ih =>
    intro _ hpos hhead
    rcases m with _ | ⟨d, ds⟩
    · -- `l = [c]`, normalised means `2 ≤ c`
      have hc2 : 2 ≤ c := hhead c (by simp)
      simp only [List.nil_append]
      rw [K_singleton, show ([c] : List ℕ).dropLast = [] from by simp, K_nil,
        cf_of_pos (by norm_num), Nat.mod_one, cf_zero, Nat.div_one]
      simp
    · set m := d :: ds with hm
      have hmne : m ≠ [] := by simp [hm]
      have hmpos : ∀ x ∈ m, 1 ≤ x := fun x hx => hpos x (List.mem_append.2 (Or.inl hx))
      have hhead_d : 2 ≤ d := by
        apply hhead d
        rw [hm]
        simp
      have hmhead : ∀ x ∈ m.head?, 2 ≤ x := by
        intro x hx
        rw [hm] at hx
        simp at hx
        omega
      have hsingle : m.length = 1 → 2 ≤ K m := by
        intro h1
        obtain ⟨e, he⟩ := List.length_eq_one_iff.1 h1
        rw [he, K_singleton]
        exact hmhead e (by rw [he]; simp)
      have hlt : K m.dropLast < K m := K_dropLast_lt' hmne hmpos hsingle
      have hKmpos : K m ≠ 0 := by
        have := K_pos m hmpos
        omega
      have hdl : (m ++ [c]).dropLast = m := by simp
      rw [K_concat m hmne c, hdl,
        show c * K m + K m.dropLast = K m.dropLast + K m * c from by ring,
        cf_of_pos hKmpos, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt,
        Nat.add_mul_div_left _ _ (by omega : 0 < K m), Nat.div_eq_of_lt hlt,
        Nat.zero_add, ih hmne hmpos hmhead]

/-- The expansion produced by `cf` is normalised: nonempty, with positive
entries and first entry at least `2`. -/
theorem cf_spec : ∀ y x : ℕ, 1 ≤ y → y < x → Nat.gcd x y = 1 →
    cf x y ≠ [] ∧ (∀ c ∈ cf x y, 1 ≤ c) ∧ (∀ c ∈ (cf x y).head?, 2 ≤ c) := by
  intro y
  induction y using Nat.strong_induction_on with
  | _ y ih =>
    intro x hy1 hlt hgcd
    rcases Nat.lt_or_ge y 2 with h2 | h2
    · have hyeq : y = 1 := by omega
      subst hyeq
      have h1 : cf x 1 = [x] := by
        rw [cf_of_pos (by norm_num), Nat.mod_one, cf_zero, Nat.div_one]
        simp
      rw [h1]
      refine ⟨by simp, ?_, ?_⟩ <;> intro c hx <;> simp at hx <;> omega
    · have hyne : y ≠ 0 := by omega
      have hrlt : x % y < y := Nat.mod_lt _ (by omega)
      have hr1 : 1 ≤ x % y := by
        rcases Nat.eq_zero_or_pos (x % y) with h0 | h0
        · exfalso
          have hg : Nat.gcd x y = y := Nat.gcd_eq_right (Nat.dvd_of_mod_eq_zero h0)
          omega
        · exact h0
      have hgcd' : Nat.gcd y (x % y) = 1 := by
        rw [← hgcd, Nat.gcd_comm x y, Nat.gcd_rec y x]
        exact Nat.gcd_comm _ _
      obtain ⟨hne, hpos, hhd⟩ := ih (x % y) hrlt y hr1 hrlt hgcd'
      have hq1 : 1 ≤ x / y := (Nat.one_le_div_iff (by omega)).2 (by omega)
      rw [cf_of_pos hyne]
      refine ⟨by simp, ?_, ?_⟩
      · intro c hx
        rcases List.mem_append.1 hx with h | h
        · exact hpos c h
        · simp at h; omega
      · intro c hx
        rcases hcf : cf y (x % y) with _ | ⟨c₀, cs⟩
        · exact absurd hcf hne
        · rw [hcf] at hx hhd
          simp at hx ⊢
          exact hhd c (by simp [hx])

/-- **Heilbronn's bijection.**

The map `l ↦ (K l, K l.dropLast)` is a bijection from normalised expansions
(nonempty, positive entries, first entry at least `2`) onto the coprime pairs
`x > y ≥ 1`.  The first component is injectivity, the second surjectivity
together with the fact that the inverse lands among normalised expansions.

Combined with `heilbronn_forward`, this is the correspondence underlying
equation (eq. heilbron) of Blomer--Bux. -/
theorem heilbronn_bijection :
    (∀ l : List ℕ, l ≠ [] → (∀ c ∈ l, 1 ≤ c) → (∀ hd ∈ l.head?, 2 ≤ hd) →
        cf (K l) (K l.dropLast) = l)
      ∧ (∀ x y : ℕ, 1 ≤ y → y < x → Nat.gcd x y = 1 →
        (cf x y ≠ [] ∧ (∀ c ∈ cf x y, 1 ≤ c) ∧ (∀ hd ∈ (cf x y).head?, 2 ≤ hd))
          ∧ K (cf x y) = x ∧ K (cf x y).dropLast = y) :=
  ⟨cf_K, fun x y h1 h2 h3 => ⟨cf_spec y x h1 h2 h3, K_cf y x h1 h2 h3⟩⟩

/-- Dropping the last entry of a reversed list drops the first entry. -/
theorem reverse_dropLast_eq (l : List ℕ) : (l.reverse).dropLast = (l.tail).reverse := by
  rcases l with _ | ⟨a, t⟩ <;> simp

/-- Mirror of the earlier reversal identity. -/
theorem reverse_tail_eq (l : List ℕ) : (l.reverse).tail = (l.dropLast).reverse := by
  have h : ((l.reverse).reverse).dropLast = ((l.reverse).tail).reverse := by
    rcases hl : l.reverse with _ | ⟨a, t⟩ <;> simp
  rw [List.reverse_reverse] at h
  rw [h, List.reverse_reverse]

/-- **Heilbronn's correspondence, surjectivity at the level of quadruples.**

Every quadruple `(x, x', y, y')` with `x > y ≥ 1`, `x' > y' ≥ 1` and both
coprimality conditions arises from a split expansion, and its continuant
identity `n = x·x' + y·y'` holds.  The suffix is obtained by reversing, which is
legitimate by `K_reverse`. -/
theorem heilbronn_surjective {x x' y y' : ℕ}
    (hx : 1 ≤ y) (hab : y < x) (hga : Nat.gcd x y = 1)
    (hx' : 1 ≤ y') (hbb : y' < x') (hgb : Nat.gcd x' y' = 1) :
    ∃ l₁ l₂ : List ℕ, l₁ ≠ [] ∧ l₂ ≠ [] ∧
      K l₁ = x ∧ K l₁.dropLast = y ∧ K l₂ = x' ∧ K l₂.tail = y' ∧
      K (l₁ ++ l₂) = x * x' + y * y' := by
  obtain ⟨hK₁, hKd₁⟩ := K_cf y x hx hab hga
  obtain ⟨hne₁, -, -⟩ := cf_spec y x hx hab hga
  obtain ⟨hK₂, hKd₂⟩ := K_cf y' x' hx' hbb hgb
  obtain ⟨hne₂, -, -⟩ := cf_spec y' x' hx' hbb hgb
  have hne₂' : (cf x' y').reverse ≠ [] := by simpa using hne₂
  have hx'₂ : K (cf x' y').reverse = x' := by rw [K_reverse]; exact hK₂
  have hx'₂' : K ((cf x' y').reverse).tail = y' := by
    rw [reverse_tail_eq, K_reverse]; exact hKd₂
  refine ⟨cf x y, (cf x' y').reverse, hne₁, hne₂', hK₁, hKd₁, hx'₂, hx'₂', ?_⟩
  rw [K_append _ _ hne₁ hne₂', hK₁, hKd₁, hx'₂, hx'₂']

/-! ## The bridge to remainder sums

Equation (eq. RemainderSum) of the paper: for coprime `n > k`, the remainders
`r₁, r₂, …` of the Euclidean algorithm are exactly the continuants of the
prefixes of the expansion `cf n k`, so the remainder sum of `Euclid.lean` is a
sum of continuants.  This is the point where Tier 1 meets Heilbronn. -/

/-- **Equation (eq. RemainderSum).**  For coprime `n > k ≥ 1`,

  `remSum n k = ∑_{j < |cf n k|} K ((cf n k).take j)`.

The remainders in the Euclidean algorithm are the continuants of the prefixes
of the expansion. -/
theorem remSum_eq_sum_K : ∀ k n : ℕ, 1 ≤ k → k < n → Nat.gcd n k = 1 →
    remSum n k = ∑ j ∈ Finset.range (cf n k).length, K ((cf n k).take j) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro n hk1 hkn hgcd
    rcases Nat.lt_or_ge k 2 with h2 | h2
    · have hk : k = 1 := by omega
      subst hk
      have hcf : cf n 1 = [n] := by
        rw [cf_of_pos (by norm_num), Nat.mod_one, cf_zero, Nat.div_one]
        simp
      rw [hcf, remSum_of_pos n (by norm_num)]
      simp [Nat.mod_one]
    · have hkne : k ≠ 0 := by omega
      have hrlt : n % k < k := Nat.mod_lt _ (by omega)
      have hr1 : 1 ≤ n % k := by
        rcases Nat.eq_zero_or_pos (n % k) with h0 | h0
        · exfalso
          have hg : Nat.gcd n k = k := Nat.gcd_eq_right (Nat.dvd_of_mod_eq_zero h0)
          omega
        · exact h0
      have hgcd' : Nat.gcd k (n % k) = 1 := by
        rw [← hgcd, Nat.gcd_comm n k, Nat.gcd_rec k n]
        exact Nat.gcd_comm _ _
      have hM : K (cf k (n % k)) = k := (K_cf (n % k) k hr1 hrlt hgcd').1
      have hIH := ih (n % k) hrlt k hr1 hrlt hgcd'
      rw [remSum_of_pos n hkne, hIH, cf_of_pos hkne, List.length_append,
        List.length_singleton, Finset.sum_range_succ]
      have h1 : ∀ j ∈ Finset.range (cf k (n % k)).length,
          K ((cf k (n % k) ++ [n / k]).take j) = K ((cf k (n % k)).take j) := by
        intro j hj
        rw [List.take_append_of_le_length (Nat.le_of_lt (Finset.mem_range.1 hj))]
      rw [Finset.sum_congr rfl h1, List.take_left, hM]
      ring

/-! ## The constraint `k ≤ n/2`

Heilbronn's correspondence also asks `2 ≤ c_l`.  The last entry of `cf n k` is
the first Euclidean quotient `n / k`, so that condition says exactly `2k ≤ n` —
which is the range of shifts the block cycle algorithm recurses on.  The two
lemmas below are the two directions of that equivalence. -/

/-- The last entry of `cf n k` is the first Euclidean quotient. -/
theorem cf_getLast {n k : ℕ} (hk : k ≠ 0) : (cf n k).getLast? = some (n / k) := by
  rw [cf_of_pos hk]
  simp

/-- If `2k ≤ n` the expansion's last entry is at least `2`. -/
theorem two_le_cf_getLast {n k : ℕ} (hk : k ≠ 0) (h : 2 * k ≤ n) :
    ∀ x ∈ (cf n k).getLast?, 2 ≤ x := by
  intro x hx
  rw [cf_getLast hk] at hx
  simp at hx
  subst hx
  exact (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hk)).2 (by omega)

/-- Conversely, an expansion whose last entry is at least `2` has
`2 · K L.dropLast ≤ K L`. -/
theorem two_mul_K_dropLast_le : ∀ L : List ℕ, L ≠ [] → (∀ c ∈ L, 1 ≤ c) →
    (∀ x ∈ L.getLast?, 2 ≤ x) → 2 * K L.dropLast ≤ K L := by
  intro L
  induction L using List.reverseRecOn with
  | nil => intro h; exact absurd rfl h
  | append_singleton m c _ =>
    intro _ hpos hlast
    have hc2 : 2 ≤ c := by
      apply hlast c
      simp
    have hdl : (m ++ [c]).dropLast = m := by simp
    rw [hdl]
    by_cases hm : m = []
    · subst hm
      simp
      omega
    · have hmp : 1 ≤ K m := K_pos m (fun x hx => hpos x (List.mem_append.2 (Or.inl hx)))
      rw [K_concat m hm c]
      nlinarith [Nat.zero_le (K m.dropLast)]

/-- **The shift–expansion bijection.**

For each `n`, the map `k ↦ cf n k` sends the shifts `1 ≤ k` with `2k ≤ n` and
`gcd(n,k) = 1` — exactly the range the block cycle algorithm recurses on — to
the normalised expansions of `n` whose last entry is at least `2`, i.e. exactly
Heilbronn's index set.  The inverse is `L ↦ K L.dropLast`.

The first component says the forward map lands correctly and is inverted by
`L ↦ K L.dropLast`; the second says the backward map lands correctly and is
inverted by `k ↦ cf n k`. -/
theorem shift_expansion_bijection (n : ℕ) :
    (∀ k : ℕ, 1 ≤ k → 2 * k ≤ n → Nat.gcd n k = 1 →
        K (cf n k) = n ∧ K (cf n k).dropLast = k ∧ cf n k ≠ []
          ∧ (∀ c ∈ cf n k, 1 ≤ c) ∧ (∀ x ∈ (cf n k).head?, 2 ≤ x)
          ∧ (∀ x ∈ (cf n k).getLast?, 2 ≤ x))
      ∧ (∀ L : List ℕ, L ≠ [] → (∀ c ∈ L, 1 ≤ c) → (∀ x ∈ L.head?, 2 ≤ x) →
        (∀ x ∈ L.getLast?, 2 ≤ x) →
          cf (K L) (K L.dropLast) = L ∧ 1 ≤ K L.dropLast
            ∧ 2 * K L.dropLast ≤ K L ∧ Nat.gcd (K L) (K L.dropLast) = 1) := by
  constructor
  · intro k hk1 hk2 hgcd
    have hkn : k < n := by omega
    have hkne : k ≠ 0 := by omega
    obtain ⟨hK, hKd⟩ := K_cf k n hk1 hkn hgcd
    obtain ⟨hne, hpos, hhead⟩ := cf_spec k n hk1 hkn hgcd
    exact ⟨hK, hKd, hne, hpos, hhead, two_le_cf_getLast hkne hk2⟩
  · intro L hne hpos hhead hlast
    refine ⟨cf_K L hne hpos hhead, ?_, two_mul_K_dropLast_le L hne hpos hlast,
      K_coprime L⟩
    exact K_pos _ (fun x hx => hpos x (List.dropLast_subset L hx))

/-! ## Towards equation (eq. heilbron)

The left-hand side of (eq. heilbron) sums `remSum` over the shifts the
algorithm recurses on.  Expanding each term by `remSum_eq_sum_K` and splitting
off the `j = 0` contribution `K [] = 1` gives the shape of the identity: a count
of shifts, plus a double sum over splits of expansions.  The `j = 0` terms are
what the paper records as `∑ gcd(n,k)`, here all equal to `1` by coprimality. -/

/-- The shifts the block cycle algorithm recurses on that are coprime to `n`. -/
def shifts (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter (fun k => 1 ≤ k ∧ 2 * k ≤ n ∧ Nat.gcd n k = 1)

theorem mem_shifts {n k : ℕ} :
    k ∈ shifts n ↔ k ≤ n ∧ 1 ≤ k ∧ 2 * k ≤ n ∧ Nat.gcd n k = 1 := by
  simp [shifts]

/-- **The left-hand side of (eq. heilbron).**  Summing `remSum` over the shifts
splits into a count of shifts plus a double sum of continuants over splits. -/
theorem sum_remSum_eq (n : ℕ) :
    ∑ k ∈ shifts n, remSum n k
      = (shifts n).card
        + ∑ k ∈ shifts n, ∑ j ∈ Finset.Ico 1 (cf n k).length, K ((cf n k).take j) := by
  rw [Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  obtain ⟨-, hk1, hk2, hgcd⟩ := mem_shifts.1 hk
  have hkn : k < n := by omega
  have hne : cf n k ≠ [] := (cf_spec k n hk1 hkn hgcd).1
  have hlen : 0 < (cf n k).length := List.length_pos_iff.2 hne
  rw [remSum_eq_sum_K k n hk1 hkn hgcd, Finset.range_eq_Ico,
    Finset.sum_eq_sum_Ico_succ_bot hlen]
  simp

/-- A one-element list has `K` equal to its entry, so a head condition gives a
lower bound on `K`. -/
theorem two_le_K_of_length_one {l : List ℕ} (h : l.length = 1)
    (hhead : ∀ x ∈ l.head?, 2 ≤ x) : 2 ≤ K l := by
  obtain ⟨c, hc⟩ := List.length_eq_one_iff.1 h
  subst hc
  simpa using hhead c (by simp)

/-- The same from a last-entry condition. -/
theorem two_le_K_of_length_one' {l : List ℕ} (h : l.length = 1)
    (hlast : ∀ x ∈ l.getLast?, 2 ≤ x) : 2 ≤ K l := by
  obtain ⟨c, hc⟩ := List.length_eq_one_iff.1 h
  subst hc
  simpa using hlast c (by simp)

/-- A prefix inherits the head condition. -/
theorem head?_take_of_head? {L : List ℕ} {j : ℕ} (hj : 1 ≤ j)
    (hhead : ∀ x ∈ L.head?, 2 ≤ x) : ∀ x ∈ (L.take j).head?, 2 ≤ x := by
  intro x hx
  apply hhead
  rcases L with _ | ⟨a, t⟩
  · simp at hx
  · rcases j with _ | j'
    · omega
    · simp at hx ⊢
      omega

/-- A suffix inherits the last-entry condition. -/
theorem getLast?_drop_of_getLast? {L : List ℕ} {j : ℕ} (hj : j < L.length)
    (hlast : ∀ x ∈ L.getLast?, 2 ≤ x) : ∀ x ∈ (L.drop j).getLast?, 2 ≤ x := by
  have hdropne : L.drop j ≠ [] := by
    intro hc
    have hl : (L.drop j).length = 0 := by rw [hc]; simp
    rw [List.length_drop] at hl
    omega
  have hgl : L.getLast? = (L.drop j).getLast? := by
    conv_lhs => rw [← List.take_append_drop j L]
    exact List.getLast?_append_of_ne_nil _ hdropne
  intro x hx
  exact hlast x (hgl ▸ hx)

/-- **The quadruple produced by a split.**  For a shift `k` the algorithm
recurses on and an interior split point `j`, the four continuants satisfy every
condition defining Heilbronn's target set. -/
theorem split_quadruple {n k j : ℕ} (hk : k ∈ shifts n) (hj1 : 1 ≤ j)
    (hj2 : j < (cf n k).length) :
    n = K ((cf n k).take j) * K ((cf n k).drop j)
        + K ((cf n k).take j).dropLast * K ((cf n k).drop j).tail
      ∧ 1 ≤ K ((cf n k).take j).dropLast
      ∧ K ((cf n k).take j).dropLast < K ((cf n k).take j)
      ∧ 1 ≤ K ((cf n k).drop j).tail
      ∧ K ((cf n k).drop j).tail < K ((cf n k).drop j)
      ∧ Nat.gcd (K ((cf n k).take j)) (K ((cf n k).take j).dropLast) = 1
      ∧ Nat.gcd (K ((cf n k).drop j)) (K ((cf n k).drop j).tail) = 1 := by
  obtain ⟨-, hk1, hk2, hgcd⟩ := mem_shifts.1 hk
  have hkn : k < n := by omega
  have hkne : k ≠ 0 := by omega
  obtain ⟨hne, hpos, hhead⟩ := cf_spec k n hk1 hkn hgcd
  have hlast := two_le_cf_getLast hkne hk2
  have hKn : K (cf n k) = n := (K_cf k n hk1 hkn hgcd).1
  -- the two halves
  have hne₁ : (cf n k).take j ≠ [] := by
    intro hc
    have hl : ((cf n k).take j).length = 0 := by rw [hc]; simp
    rw [List.length_take] at hl
    omega
  have hne₂ : (cf n k).drop j ≠ [] := by
    intro hc
    have hl : ((cf n k).drop j).length = 0 := by rw [hc]; simp
    rw [List.length_drop] at hl
    omega
  have hpos₁ : ∀ c ∈ (cf n k).take j, 1 ≤ c := fun c hc => hpos c (List.take_subset j _ hc)
  have hpos₂ : ∀ c ∈ (cf n k).drop j, 1 ≤ c := fun c hc => hpos c (List.drop_subset j _ hc)
  have hfirst : ((cf n k).take j).length = 1 → 2 ≤ K ((cf n k).take j) := fun h =>
    two_le_K_of_length_one h (head?_take_of_head? hj1 hhead)
  have hlast' : ((cf n k).drop j).length = 1 → 2 ≤ K ((cf n k).drop j) := fun h =>
    two_le_K_of_length_one' h (getLast?_drop_of_getLast? hj2 hlast)
  obtain ⟨hsum, h₁, h₂, h₃, h₄, h₅, h₆⟩ :=
    heilbronn_forward hne₁ hne₂ hpos₁ hpos₂ hfirst hlast'
  refine ⟨?_, h₂, h₁, h₄, h₃, h₅, h₆⟩
  rw [List.take_append_drop, hKn] at hsum
  exact hsum

/-- **The round trip on a split.**  For a normalised expansion `L` and an
interior split point, both halves are recovered from their continuants — the
prefix directly, the suffix after reversing.  This is what makes the passage
from splits to quadruples injective. -/
theorem heilbronn_split_roundtrip {L : List ℕ} (hpos : ∀ c ∈ L, 1 ≤ c)
    (hhead : ∀ x ∈ L.head?, 2 ≤ x) (hlast : ∀ x ∈ L.getLast?, 2 ≤ x)
    {j : ℕ} (hj1 : 1 ≤ j) (hj2 : j < L.length) :
    cf (K (L.take j)) (K (L.take j).dropLast) = L.take j
      ∧ cf (K (L.drop j)) (K (L.drop j).tail) = (L.drop j).reverse := by
  have hL : L ≠ [] := by
    intro hc
    rw [hc] at hj2
    simp at hj2
  -- the prefix inherits the head condition
  have hne₁ : L.take j ≠ [] := by
    intro hc
    have : (L.take j).length = 0 := by rw [hc]; simp
    rw [List.length_take] at this
    omega
  have hpos₁ : ∀ c ∈ L.take j, 1 ≤ c := fun c hc => hpos c (List.take_subset j L hc)
  have hhead₁ : ∀ x ∈ (L.take j).head?, 2 ≤ x := head?_take_of_head? hj1 hhead
  -- the reversed suffix inherits the last-entry condition as a head condition
  have hne₂ : (L.drop j).reverse ≠ [] := by
    intro hc
    have : (L.drop j).length = 0 := by
      have := congrArg List.length hc
      simpa using this
    rw [List.length_drop] at this
    omega
  have hpos₂ : ∀ c ∈ (L.drop j).reverse, 1 ≤ c := by
    intro c hc
    exact hpos c (List.drop_subset j L (List.mem_reverse.1 hc))
  have hdropne : L.drop j ≠ [] := by
    intro hc
    have hl : (L.drop j).length = 0 := by rw [hc]; simp
    rw [List.length_drop] at hl
    omega
  have hgl : L.getLast? = (L.drop j).getLast? := by
    conv_lhs => rw [← List.take_append_drop j L]
    exact List.getLast?_append_of_ne_nil _ hdropne
  have hhead₂ : ∀ x ∈ ((L.drop j).reverse).head?, 2 ≤ x := by
    intro x hx
    rw [List.head?_reverse, ← hgl] at hx
    exact hlast x hx
  refine ⟨cf_K _ hne₁ hpos₁ hhead₁, ?_⟩
  have h := cf_K _ hne₂ hpos₂ hhead₂
  rwa [K_reverse, reverse_dropLast_eq, K_reverse] at h

/-! ## The quadruple index set

The right-hand side of (eq. heilbron) sums over quadruples `(x, x', y, y')`
with `x > y ≥ 1`, `x' > y' ≥ 1`, both coprimality conditions, and
`n = x·x' + y·y'`.  Every component is bounded by `n`, so this is a `Finset`. -/

/-- The quadruples appearing on the right of (eq. heilbron). -/
def quadruples (n : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  ((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1)) ×ˢ (Finset.range (n + 1))
      ×ˢ (Finset.range (n + 1))).filter
    (fun q => 1 ≤ q.2.2.1 ∧ q.2.2.1 < q.1 ∧ 1 ≤ q.2.2.2 ∧ q.2.2.2 < q.2.1
      ∧ Nat.gcd q.1 q.2.2.1 = 1 ∧ Nat.gcd q.2.1 q.2.2.2 = 1
      ∧ n = q.1 * q.2.1 + q.2.2.1 * q.2.2.2)

theorem mem_quadruples {n x x' y y' : ℕ} :
    (x, x', y, y') ∈ quadruples n ↔
      (x ≤ n ∧ x' ≤ n ∧ y ≤ n ∧ y' ≤ n) ∧ 1 ≤ y ∧ y < x ∧ 1 ≤ y' ∧ y' < x'
        ∧ Nat.gcd x y = 1 ∧ Nat.gcd x' y' = 1 ∧ n = x * x' + y * y' := by
  simp [quadruples, Finset.mem_filter, Finset.mem_product, and_assoc]

/-- The components of a quadruple are bounded by `n`. -/
theorem quadruple_le {n x x' y y' : ℕ} (h1 : 1 ≤ y) (h2 : y < x) (h3 : 1 ≤ y')
    (h4 : y' < x') (hsum : n = x * x' + y * y') :
    x ≤ n ∧ x' ≤ n ∧ y ≤ n ∧ y' ≤ n := by
  have hx : 1 ≤ x := by omega
  have hx' : 1 ≤ x' := by omega
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

/-- **Splits land in the quadruple set.** -/
theorem split_mem_quadruples {n k j : ℕ} (hk : k ∈ shifts n) (hj1 : 1 ≤ j)
    (hj2 : j < (cf n k).length) :
    (K ((cf n k).take j), K ((cf n k).drop j),
      K ((cf n k).take j).dropLast, K ((cf n k).drop j).tail) ∈ quadruples n := by
  obtain ⟨hsum, h1, h2, h3, h4, h5, h6⟩ := split_quadruple hk hj1 hj2
  rw [mem_quadruples]
  exact ⟨quadruple_le h1 h2 h3 h4 hsum, h1, h2, h3, h4, h5, h6, hsum⟩

/-! ## The expansion attached to a quadruple

The inverse of the passage from splits to quadruples: given `(x, x', y, y')`,
reassemble the expansion as `cf x y` followed by the reverse of `cf x' y'`.
Reversing is what `K_reverse` licenses. -/

theorem head?_append_of_ne_nil {l₁ l₂ : List ℕ} (h : l₁ ≠ []) :
    (l₁ ++ l₂).head? = l₁.head? := by
  rcases l₁ with _ | ⟨x, xs⟩
  · exact absurd rfl h
  · simp

/-- The expansion attached to a quadruple. -/
def quadExpansion (x x' y y' : ℕ) : List ℕ := cf x y ++ (cf x' y').reverse

/-- **The expansion attached to a quadruple is the split it came from.**  It is
a normalised expansion of `n`, and splitting it at `|cf x y|` returns the two
halves. -/
theorem quadExpansion_spec {n x x' y y' : ℕ} (hq : (x, x', y, y') ∈ quadruples n) :
    K (quadExpansion x x' y y') = n ∧ quadExpansion x x' y y' ≠ []
      ∧ (∀ c ∈ quadExpansion x x' y y', 1 ≤ c)
      ∧ (∀ hd ∈ (quadExpansion x x' y y').head?, 2 ≤ hd)
      ∧ (∀ hd ∈ (quadExpansion x x' y y').getLast?, 2 ≤ hd)
      ∧ (quadExpansion x x' y y').take (cf x y).length = cf x y
      ∧ (quadExpansion x x' y y').drop (cf x y).length = (cf x' y').reverse
      ∧ 1 ≤ (cf x y).length
      ∧ (cf x y).length < (quadExpansion x x' y y').length := by
  obtain ⟨-, hx1, hx2, hx'1, hx'2, hga, hgb, hsum⟩ := mem_quadruples.1 hq
  obtain ⟨hKa, hKy⟩ := K_cf y x hx1 hx2 hga
  obtain ⟨hnea, hposa, hheada⟩ := cf_spec y x hx1 hx2 hga
  obtain ⟨hKb, hKy'⟩ := K_cf y' x' hx'1 hx'2 hgb
  obtain ⟨hneb, hposb, hheadb⟩ := cf_spec y' x' hx'1 hx'2 hgb
  have hnebr : (cf x' y').reverse ≠ [] := by simpa using hneb
  have hKbr : K (cf x' y').reverse = x' := by rw [K_reverse]; exact hKb
  have hKbr' : K ((cf x' y').reverse).tail = y' := by
    rw [reverse_tail_eq, K_reverse]; exact hKy'
  have hlen : 1 ≤ (cf x y).length := List.length_pos_iff.2 hnea
  refine ⟨?_, ?_, ?_, ?_, ?_, List.take_left, List.drop_left, hlen, ?_⟩
  · rw [quadExpansion, K_append _ _ hnea hnebr, hKa, hKy, hKbr, hKbr', hsum]
  · simp [quadExpansion, hnea]
  · intro c hc
    rcases List.mem_append.1 hc with h | h
    · exact hposa c h
    · exact hposb c (List.mem_reverse.1 h)
  · intro hd hhd
    rw [quadExpansion, head?_append_of_ne_nil hnea] at hhd
    exact hheada hd hhd
  · intro hd hhd
    rw [quadExpansion, List.getLast?_append_of_ne_nil _ hnebr,
      List.getLast?_reverse] at hhd
    exact hheadb hd hhd
  · rw [quadExpansion, List.length_append]
    have hbl : 0 < (cf x' y').reverse.length := List.length_pos_iff.2 hnebr
    omega

/-- The shift attached to a quadruple lies in `shifts n`, and its expansion is
the reassembled one. -/
theorem quadExpansion_shift {n x x' y y' : ℕ} (hq : (x, x', y, y') ∈ quadruples n) :
    K (quadExpansion x x' y y').dropLast ∈ shifts n
      ∧ cf n (K (quadExpansion x x' y y').dropLast) = quadExpansion x x' y y' := by
  obtain ⟨hKL, hne, hpos, hhead, hlast, -, -, -, -⟩ := quadExpansion_spec hq
  set L := quadExpansion x x' y y' with hL
  have hk1 : 1 ≤ K L.dropLast :=
    K_pos _ (fun c hc => hpos c (List.dropLast_subset L hc))
  have hk2 : 2 * K L.dropLast ≤ n := by
    have := two_mul_K_dropLast_le L hne hpos hlast
    omega
  have hgcd : Nat.gcd n (K L.dropLast) = 1 := by
    rw [← hKL]
    exact K_coprime L
  refine ⟨mem_shifts.2 ⟨by omega, hk1, hk2, hgcd⟩, ?_⟩
  have := cf_K L hne hpos hhead
  rwa [hKL] at this

/-! ## Equation (eq. heilbron)

The reindexing: the double sum of continuants over interior splits equals the
sum of `a` over Heilbronn's quadruples. -/

/-- **The reindexing of (eq. heilbron).** -/
theorem sum_split_eq_sum_quadruples (n : ℕ) :
    ∑ k ∈ shifts n, ∑ j ∈ Finset.Ico 1 (cf n k).length, K ((cf n k).take j)
      = ∑ q ∈ quadruples n, q.1 := by
  rw [Finset.sum_sigma']
  refine Finset.sum_bij'
    (i := fun p _ => (K ((cf n p.1).take p.2), K ((cf n p.1).drop p.2),
      K ((cf n p.1).take p.2).dropLast, K ((cf n p.1).drop p.2).tail))
    (j := fun q _ => (⟨K (quadExpansion q.1 q.2.1 q.2.2.1 q.2.2.2).dropLast,
      (cf q.1 q.2.2.1).length⟩ : (_ : ℕ) × ℕ))
    ?_ ?_ ?_ ?_ ?_
  · -- the forward map lands in `quadruples n`
    rintro ⟨k, j⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_Ico] at hp
    exact split_mem_quadruples hp.1 hp.2.1 hp.2.2
  · -- the inverse map lands in the sigma set
    rintro ⟨x, x', y, y'⟩ hq
    obtain ⟨hs, hcf⟩ := quadExpansion_shift hq
    obtain ⟨-, -, -, -, -, -, -, hlen1, hlen2⟩ := quadExpansion_spec hq
    rw [Finset.mem_sigma, Finset.mem_Ico]
    refine ⟨hs, hlen1, ?_⟩
    rw [hcf]
    exact hlen2
  · -- left inverse
    rintro ⟨k, j⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_Ico] at hp
    obtain ⟨hk, hj1, hj2⟩ := hp
    obtain ⟨-, hk1, hk2, hgcd⟩ := mem_shifts.1 hk
    have hkn : k < n := by omega
    obtain ⟨hne, hpos, hhead⟩ := cf_spec k n hk1 hkn hgcd
    have hlast := two_le_cf_getLast (by omega : k ≠ 0) hk2
    obtain ⟨h₁, h₂⟩ := heilbronn_split_roundtrip hpos hhead hlast hj1 hj2
    have hLeq : quadExpansion (K ((cf n k).take j)) (K ((cf n k).drop j))
        (K ((cf n k).take j).dropLast) (K ((cf n k).drop j).tail) = cf n k := by
      rw [quadExpansion, h₁, h₂, List.reverse_reverse, List.take_append_drop]
    simp only [hLeq, h₁]
    have hKd : K (cf n k).dropLast = k := (K_cf k n hk1 hkn hgcd).2
    have hjlen : ((cf n k).take j).length = j := by
      rw [List.length_take]
      omega
    rw [hKd, hjlen]
  · -- right inverse
    rintro ⟨x, x', y, y'⟩ hq
    obtain ⟨-, hcf⟩ := quadExpansion_shift hq
    obtain ⟨-, -, -, -, -, htake, hdrop, -, -⟩ := quadExpansion_spec hq
    obtain ⟨-, hx1, hx2, hx'1, hx'2, hga, hgb, -⟩ := mem_quadruples.1 hq
    obtain ⟨hKa, hKy⟩ := K_cf y x hx1 hx2 hga
    obtain ⟨hKb, hKy'⟩ := K_cf y' x' hx'1 hx'2 hgb
    simp only [hcf, htake, hdrop]
    have e2 : K (cf x' y').reverse = x' := by rw [K_reverse]; exact hKb
    have e4 : K ((cf x' y').reverse).tail = y' := by
      rw [reverse_tail_eq, K_reverse]; exact hKy'
    rw [hKa, e2, hKy, e4]
  · rintro ⟨k, j⟩ _
    rfl

/-- The quadruple set is symmetric under swapping the two halves. -/
theorem mem_quadruples_swap {n x x' y y' : ℕ} (h : (x, x', y, y') ∈ quadruples n) :
    (x', x, y', y) ∈ quadruples n := by
  rw [mem_quadruples] at h ⊢
  obtain ⟨⟨h1, h2, h3, h4⟩, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨⟨h2, h1, h4, h3⟩, h7, h8, h5, h6, h10, h9, by rw [h11]; ring⟩

/-- **Summing `a` over the quadruples is the same as summing `b`.**

The paper uses this to symmetrise; it is the involution swapping the two
halves of the quadruple. -/
theorem sum_fst_eq_sum_snd (n : ℕ) :
    ∑ q ∈ quadruples n, q.1 = ∑ q ∈ quadruples n, q.2.1 := by
  refine Finset.sum_bij'
    (i := fun q _ => (q.2.1, q.1, q.2.2.2, q.2.2.1))
    (j := fun q _ => (q.2.1, q.1, q.2.2.2, q.2.2.1)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨x, x', y, y'⟩ hq
    exact mem_quadruples_swap hq
  · rintro ⟨x, x', y, y'⟩ hq
    exact mem_quadruples_swap hq
  · rintro ⟨x, x', y, y'⟩ _
    rfl
  · rintro ⟨x, x', y, y'⟩ _
    rfl
  · rintro ⟨x, x', y, y'⟩ _
    rfl

/-- **The coprime form of the Heilbronn identity.**

Summing the Euclidean remainder sums over the shifts the block cycle algorithm
recurses on *that are coprime to `n`* equals the number of those shifts plus a
sum over Heilbronn's quadruples.  The first term is the paper's `∑ gcd(n,k)`,
which is a count here because the shifts are coprime to `n`.

This is the unlabelled display preceding equation (eq. heilbron) in the paper.
Equation (eq. heilbron) itself drops both coprimality restrictions, and follows
from this by summing over `d = gcd(n,k)`; see `remSum_mul` for the scaling that
aggregation relies on. -/
theorem heilbron_coprime (n : ℕ) :
    ∑ k ∈ shifts n, remSum n k = (shifts n).card + ∑ q ∈ quadruples n, q.1 := by
  rw [sum_remSum_eq, sum_split_eq_sum_quadruples]

/-! ## Aggregating over the gcd

Equation (eq. heilbron) drops both coprimality restrictions.  Recovering it from
the coprime form means classifying each shift `k` by `g = gcd(n,k)`, writing
`k = g·k'` with `k'` coprime to `n/g`.  The following reindexing does that once
and for all, for an arbitrary summand. -/

/-- All shifts the algorithm recurses on, coprime or not. -/
def allShifts (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter (fun k => 1 ≤ k ∧ 2 * k ≤ n)

theorem mem_allShifts {n k : ℕ} : k ∈ allShifts n ↔ k ≤ n ∧ 1 ≤ k ∧ 2 * k ≤ n := by
  simp [allShifts]

/-- **Classifying shifts by their gcd with `n`.**  Every shift is `g·k'` for a
unique divisor `g` of `n` and a shift `k'` of `n/g` coprime to it. -/
theorem sum_allShifts_eq {n : ℕ} (hn : 0 < n) (F : ℕ → ℕ → ℕ) :
    ∑ k ∈ allShifts n, F (Nat.gcd n k) (k / Nat.gcd n k)
      = ∑ g ∈ n.divisors, ∑ k' ∈ shifts (n / g), F g k' := by
  rw [Finset.sum_sigma']
  refine Finset.sum_bij'
    (i := fun k _ => (⟨Nat.gcd n k, k / Nat.gcd n k⟩ : (_ : ℕ) × ℕ))
    (j := fun p _ => p.1 * p.2) ?_ ?_ ?_ ?_ ?_
  · -- forward map lands correctly
    intro k hk
    obtain ⟨hkn, hk1, hk2⟩ := mem_allShifts.1 hk
    have hg : 0 < Nat.gcd n k := Nat.gcd_pos_of_pos_left _ hn
    have hgn : Nat.gcd n k ∣ n := Nat.gcd_dvd_left _ _
    have hgk : Nat.gcd n k ∣ k := Nat.gcd_dvd_right _ _
    simp only [Finset.mem_sigma, Nat.mem_divisors]
    refine ⟨⟨hgn, hn.ne'⟩, mem_shifts.2 ⟨?_, ?_, ?_, ?_⟩⟩
    · exact Nat.div_le_div_right hkn
    · exact Nat.one_le_div_iff hg |>.2 (Nat.le_of_dvd (by omega) hgk)
    · calc 2 * (k / Nat.gcd n k) = 2 * k / Nat.gcd n k := (Nat.mul_div_assoc 2 hgk).symm
        _ ≤ n / Nat.gcd n k := Nat.div_le_div_right hk2
    · exact Nat.coprime_div_gcd_div_gcd hg
  · -- inverse map lands correctly
    rintro ⟨g, k'⟩ hp
    simp only [Finset.mem_sigma, Nat.mem_divisors] at hp
    obtain ⟨⟨hgn, -⟩, hk'⟩ := hp
    obtain ⟨-, hk'1, hk'2, -⟩ := mem_shifts.1 hk'
    have hg : 0 < g := Nat.pos_of_dvd_of_pos hgn hn
    have hmul : g * (n / g) = n := Nat.mul_div_cancel' hgn
    rw [mem_allShifts]
    refine ⟨?_, ?_, ?_⟩
    · nlinarith [hmul, hk'2]
    · exact Nat.mul_pos hg hk'1
    · nlinarith [hmul, hk'2]
  · -- left inverse
    intro k hk
    obtain ⟨-, hk1, -⟩ := mem_allShifts.1 hk
    exact Nat.mul_div_cancel' (Nat.gcd_dvd_right n k)
  · -- right inverse
    rintro ⟨g, k'⟩ hp
    simp only [Finset.mem_sigma, Nat.mem_divisors] at hp
    obtain ⟨⟨hgn, -⟩, hk'⟩ := hp
    obtain ⟨-, -, -, hcop⟩ := mem_shifts.1 hk'
    have hg : 0 < g := Nat.pos_of_dvd_of_pos hgn hn
    have hmul : g * (n / g) = n := Nat.mul_div_cancel' hgn
    have hgcd : Nat.gcd n (g * k') = g := by
      conv_lhs => rw [← hmul]
      rw [Nat.gcd_mul_left, hcop, mul_one]
    simp only [hgcd]
    congr 1
    rw [Nat.mul_div_cancel_left _ hg]
  · intro k _
    rfl

/-- The remainder sums, aggregated over the gcd. -/
theorem sum_remSum_allShifts {n : ℕ} (hn : 0 < n) :
    ∑ k ∈ allShifts n, remSum n k
      = ∑ g ∈ n.divisors, g * ∑ k' ∈ shifts (n / g), remSum (n / g) k' := by
  rw [show (∑ g ∈ n.divisors, g * ∑ k' ∈ shifts (n / g), remSum (n / g) k')
      = ∑ g ∈ n.divisors, ∑ k' ∈ shifts (n / g), g * remSum (n / g) k' from
    Finset.sum_congr rfl fun g _ => Finset.mul_sum _ _ _]
  rw [← sum_allShifts_eq hn (fun g k' => g * remSum (n / g) k')]
  refine Finset.sum_congr rfl fun k hk => ?_
  have h1 : Nat.gcd n k * (n / Nat.gcd n k) = n := Nat.mul_div_cancel' (Nat.gcd_dvd_left n k)
  have h2 : Nat.gcd n k * (k / Nat.gcd n k) = k := Nat.mul_div_cancel' (Nat.gcd_dvd_right n k)
  have hm := remSum_mul (k / Nat.gcd n k) (n / Nat.gcd n k) (Nat.gcd n k)
  rw [h1, h2] at hm
  exact hm

/-- The gcds, aggregated over the gcd. -/
theorem sum_gcd_allShifts {n : ℕ} (hn : 0 < n) :
    ∑ k ∈ allShifts n, Nat.gcd n k = ∑ g ∈ n.divisors, g * (shifts (n / g)).card := by
  rw [sum_allShifts_eq hn (fun g _ => g)]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- **Equation (eq. heilbron), aggregated form.**

Summing the Euclidean remainder sums over *all* shifts the algorithm recurses
on — not only those coprime to `n` — equals the sum of `gcd(n,k)` over the same
range plus a divisor-weighted sum over Heilbronn's quadruples.

This is the coprime form summed over `g = gcd(n,k)`.  The paper writes the
second term as a single sum over quadruples constrained only by
`gcd(x,y) = 1`; that regrouping is `sum_quadruplesAll` below. -/
theorem heilbron_aggregated {n : ℕ} (hn : 0 < n) :
    ∑ k ∈ allShifts n, remSum n k
      = (∑ k ∈ allShifts n, Nat.gcd n k)
        + ∑ g ∈ n.divisors, g * ∑ q ∈ quadruples (n / g), q.1 := by
  rw [sum_remSum_allShifts hn, sum_gcd_allShifts hn, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [heilbron_coprime (n / g), Nat.mul_add]

/-! ## The quadruples of (eq. heilbron)

The paper's right-hand side sums `x'` over quadruples constrained only by
`gcd(x,y) = 1`.  Classifying those by `e = gcd(x',y')` regroups them into the
divisor-weighted sum over fully coprime quadruples. -/

/-- The quadruples of (eq. heilbron): only `gcd(x,y) = 1` is imposed. -/
def quadruplesAll (n : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  ((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1)) ×ˢ (Finset.range (n + 1))
      ×ˢ (Finset.range (n + 1))).filter
    (fun q => 1 ≤ q.2.2.1 ∧ q.2.2.1 < q.1 ∧ 1 ≤ q.2.2.2 ∧ q.2.2.2 < q.2.1
      ∧ Nat.gcd q.1 q.2.2.1 = 1 ∧ n = q.1 * q.2.1 + q.2.2.1 * q.2.2.2)

theorem mem_quadruplesAll {n x x' y y' : ℕ} :
    (x, x', y, y') ∈ quadruplesAll n ↔
      (x ≤ n ∧ x' ≤ n ∧ y ≤ n ∧ y' ≤ n) ∧ 1 ≤ y ∧ y < x ∧ 1 ≤ y' ∧ y' < x'
        ∧ Nat.gcd x y = 1 ∧ n = x * x' + y * y' := by
  simp [quadruplesAll, Finset.mem_filter, Finset.mem_product, and_assoc]

/-- **Classifying the quadruples by `gcd(x',y')`.** -/
theorem sum_snd_quadruplesAll {n : ℕ} (hn : 0 < n) :
    ∑ q ∈ quadruplesAll n, q.2.1
      = ∑ e ∈ n.divisors, e * ∑ p ∈ quadruples (n / e), p.2.1 := by
  rw [show (∑ e ∈ n.divisors, e * ∑ p ∈ quadruples (n / e), p.2.1)
      = ∑ e ∈ n.divisors, ∑ p ∈ quadruples (n / e), e * p.2.1 from
    Finset.sum_congr rfl fun e _ => Finset.mul_sum _ _ _, Finset.sum_sigma']
  refine Finset.sum_bij'
    (i := fun q _ => (⟨Nat.gcd q.2.1 q.2.2.2,
        (q.1, q.2.1 / Nat.gcd q.2.1 q.2.2.2, q.2.2.1,
          q.2.2.2 / Nat.gcd q.2.1 q.2.2.2)⟩ : (_ : ℕ) × (ℕ × ℕ × ℕ × ℕ)))
    (j := fun p _ => (p.2.1, p.1 * p.2.2.1, p.2.2.2.1, p.1 * p.2.2.2.2))
    ?_ ?_ ?_ ?_ ?_
  · -- forward
    rintro ⟨x, x', y, y'⟩ hq
    obtain ⟨⟨-, -, -, -⟩, hx1, hx2, hx'1, hx'2, hga, hsum⟩ := mem_quadruplesAll.1 hq
    have he : 0 < Nat.gcd x' y' := Nat.gcd_pos_of_pos_left _ (by omega)
    have heb : Nat.gcd x' y' ∣ x' := Nat.gcd_dvd_left _ _
    have hey' : Nat.gcd x' y' ∣ y' := Nat.gcd_dvd_right _ _
    have hen : Nat.gcd x' y' ∣ n := by
      rw [hsum]
      exact Dvd.dvd.add (Dvd.dvd.mul_left heb x) (Dvd.dvd.mul_left hey' y)
    have hne : n / Nat.gcd x' y' = x * (x' / Nat.gcd x' y') + y * (y' / Nat.gcd x' y') := by
      rw [Nat.div_eq_iff_eq_mul_left he hen, hsum, Nat.add_mul, Nat.mul_assoc,
        Nat.mul_assoc, Nat.div_mul_cancel heb, Nat.div_mul_cancel hey']
    simp only [Finset.mem_sigma, Nat.mem_divisors]
    refine ⟨⟨hen, hn.ne'⟩, mem_quadruples.2 ⟨?_, hx1, hx2, ?_, ?_, hga, ?_, hne⟩⟩
    · refine quadruple_le hx1 hx2 ?_ ?_ hne
      · exact (Nat.one_le_div_iff he).2 (Nat.le_of_dvd (by omega) hey')
      · exact Nat.div_lt_div_of_lt_of_dvd heb hx'2
    · exact (Nat.one_le_div_iff he).2 (Nat.le_of_dvd (by omega) hey')
    · exact Nat.div_lt_div_of_lt_of_dvd heb hx'2
    · exact Nat.coprime_div_gcd_div_gcd he
  · -- backward
    rintro ⟨e, x, x'1, y, y'1⟩ hp
    simp only [Finset.mem_sigma, Nat.mem_divisors] at hp
    obtain ⟨⟨hen, -⟩, hq⟩ := hp
    obtain ⟨-, hx1, hx2, hx'1, hx'2, hga, -, hsum⟩ := mem_quadruples.1 hq
    have he : 0 < e := Nat.pos_of_dvd_of_pos hen hn
    have hmul : e * (n / e) = n := Nat.mul_div_cancel' hen
    have hsum' : n = x * (e * x'1) + y * (e * y'1) := by
      rw [← hmul, hsum]; ring
    rw [mem_quadruplesAll]
    have hp1 : 1 ≤ e * y'1 := Nat.mul_pos he hx'1
    have hp2 : e * y'1 < e * x'1 := by nlinarith
    exact ⟨quadruple_le hx1 hx2 hp1 hp2 hsum', hx1, hx2, hp1, hp2, hga, hsum'⟩
  · -- left inverse
    rintro ⟨x, x', y, y'⟩ hq
    obtain ⟨-, -, -, hx'1, hx'2, -, -⟩ := mem_quadruplesAll.1 hq
    have he : 0 < Nat.gcd x' y' := Nat.gcd_pos_of_pos_left _ (by omega)
    have e1 : Nat.gcd x' y' * (x' / Nat.gcd x' y') = x' :=
      Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
    have e2 : Nat.gcd x' y' * (y' / Nat.gcd x' y') = y' :=
      Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
    rw [e1, e2]
  · -- right inverse
    rintro ⟨e, x, x'1, y, y'1⟩ hp
    simp only [Finset.mem_sigma, Nat.mem_divisors] at hp
    obtain ⟨⟨hen, -⟩, hq⟩ := hp
    obtain ⟨-, -, -, hx'1, hx'2, -, hcop, -⟩ := mem_quadruples.1 hq
    have he : 0 < e := Nat.pos_of_dvd_of_pos hen hn
    have hgcd : Nat.gcd (e * x'1) (e * y'1) = e := by
      rw [Nat.gcd_mul_left, hcop, mul_one]
    simp only [hgcd, Nat.mul_div_cancel_left _ he]
  · rintro ⟨x, x', y, y'⟩ hq
    obtain ⟨-, -, -, hx'1, hx'2, -, -⟩ := mem_quadruplesAll.1 hq
    have he : 0 < Nat.gcd x' y' := Nat.gcd_pos_of_pos_left _ (by omega)
    exact (Nat.mul_div_cancel' (Nat.gcd_dvd_left x' y')).symm

/-- **Equation (eq. heilbron).**

Summing the Euclidean remainder sums over all shifts the block cycle algorithm
recurses on equals the sum of `gcd(n,k)` over the same range, plus the sum of
`x'` over the quadruples constrained only by `gcd(x,y) = 1`.

This is the paper's labelled identity, the passage from move counts to lattice
point counts. -/
theorem heilbron {n : ℕ} (hn : 0 < n) :
    ∑ k ∈ allShifts n, remSum n k
      = (∑ k ∈ allShifts n, Nat.gcd n k) + ∑ q ∈ quadruplesAll n, q.2.1 := by
  rw [heilbron_aggregated hn, sum_snd_quadruplesAll hn]
  congr 1
  exact Finset.sum_congr rfl fun e _ => by rw [sum_fst_eq_sum_snd]

/-! ## Removing the gcd condition

The paper writes `R(n)` for the sum of `x'` over quadruples with `gcd(x,y) = 1`
— the right-hand side of (eq. heilbron) — and `Q(n)` for the same sum with no
gcd condition at all.  Classifying by `d = gcd(x,y)` gives `Q(n) = ∑_{d ∣ n} R(d)`,
which is what Möbius inversion is then applied to.

Note the summand `x'` is untouched by this classification, so unlike the
aggregation of (eq. heilbron) there is no divisor weight. -/

/-- The quadruples with no gcd condition. -/
def quadruplesQ (n : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  ((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1)) ×ˢ (Finset.range (n + 1))
      ×ˢ (Finset.range (n + 1))).filter
    (fun q => 1 ≤ q.2.2.1 ∧ q.2.2.1 < q.1 ∧ 1 ≤ q.2.2.2 ∧ q.2.2.2 < q.2.1
      ∧ n = q.1 * q.2.1 + q.2.2.1 * q.2.2.2)

theorem mem_quadruplesQ {n x x' y y' : ℕ} :
    (x, x', y, y') ∈ quadruplesQ n ↔
      (x ≤ n ∧ x' ≤ n ∧ y ≤ n ∧ y' ≤ n) ∧ 1 ≤ y ∧ y < x ∧ 1 ≤ y' ∧ y' < x'
        ∧ n = x * x' + y * y' := by
  simp [quadruplesQ, Finset.mem_filter, Finset.mem_product, and_assoc]

/-- **`Q(n) = ∑_{d ∣ n} R(n/d)`.**  Classifying quadruples by `d = gcd(x,y)`. -/
theorem sum_snd_quadruplesQ {n : ℕ} (hn : 0 < n) :
    ∑ q ∈ quadruplesQ n, q.2.1
      = ∑ d ∈ n.divisors, ∑ p ∈ quadruplesAll (n / d), p.2.1 := by
  rw [Finset.sum_sigma']
  refine Finset.sum_bij'
    (i := fun q _ => (⟨Nat.gcd q.1 q.2.2.1,
        (q.1 / Nat.gcd q.1 q.2.2.1, q.2.1, q.2.2.1 / Nat.gcd q.1 q.2.2.1,
          q.2.2.2)⟩ : (_ : ℕ) × (ℕ × ℕ × ℕ × ℕ)))
    (j := fun p _ => (p.1 * p.2.1, p.2.2.1, p.1 * p.2.2.2.1, p.2.2.2.2))
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨x, x', y, y'⟩ hq
    obtain ⟨-, hx1, hx2, hx'1, hx'2, hsum⟩ := mem_quadruplesQ.1 hq
    have hd : 0 < Nat.gcd x y := Nat.gcd_pos_of_pos_left _ (by omega)
    have hda : Nat.gcd x y ∣ x := Nat.gcd_dvd_left _ _
    have hdy : Nat.gcd x y ∣ y := Nat.gcd_dvd_right _ _
    have hdn : Nat.gcd x y ∣ n := by
      rw [hsum]
      exact Dvd.dvd.add (Dvd.dvd.mul_right hda x') (Dvd.dvd.mul_right hdy y')
    have hnd : n / Nat.gcd x y
        = x / Nat.gcd x y * x' + y / Nat.gcd x y * y' := by
      rw [Nat.div_eq_iff_eq_mul_left hd hdn, hsum, Nat.add_mul, Nat.mul_right_comm,
        Nat.mul_right_comm (y / Nat.gcd x y), Nat.div_mul_cancel hda,
        Nat.div_mul_cancel hdy]
    have hq1 : 1 ≤ y / Nat.gcd x y :=
      (Nat.one_le_div_iff hd).2 (Nat.le_of_dvd (by omega) hdy)
    have hq2 : y / Nat.gcd x y < x / Nat.gcd x y :=
      Nat.div_lt_div_of_lt_of_dvd hda hx2
    simp only [Finset.mem_sigma, Nat.mem_divisors]
    exact ⟨⟨hdn, hn.ne'⟩, mem_quadruplesAll.2
      ⟨quadruple_le hq1 hq2 hx'1 hx'2 hnd, hq1, hq2, hx'1, hx'2,
        Nat.coprime_div_gcd_div_gcd hd, hnd⟩⟩
  · rintro ⟨d, a1, x', a1', y'⟩ hp
    simp only [Finset.mem_sigma, Nat.mem_divisors] at hp
    obtain ⟨⟨hdn, -⟩, hq⟩ := hp
    obtain ⟨-, hx1, hx2, hx'1, hx'2, -, hsum⟩ := mem_quadruplesAll.1 hq
    have hd : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
    have hmul : d * (n / d) = n := Nat.mul_div_cancel' hdn
    have hsum' : n = d * a1 * x' + d * a1' * y' := by
      rw [← hmul, hsum]; ring
    have hp1 : 1 ≤ d * a1' := Nat.mul_pos hd hx1
    have hp2 : d * a1' < d * a1 := by nlinarith
    rw [mem_quadruplesQ]
    exact ⟨quadruple_le hp1 hp2 hx'1 hx'2 hsum', hp1, hp2, hx'1, hx'2, hsum'⟩
  · rintro ⟨x, x', y, y'⟩ hq
    obtain ⟨-, hx1, hx2, -, -, -⟩ := mem_quadruplesQ.1 hq
    have hd : 0 < Nat.gcd x y := Nat.gcd_pos_of_pos_left _ (by omega)
    have e1 : Nat.gcd x y * (x / Nat.gcd x y) = x :=
      Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
    have e2 : Nat.gcd x y * (y / Nat.gcd x y) = y :=
      Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
    rw [e1, e2]
  · rintro ⟨d, a1, x', a1', y'⟩ hp
    simp only [Finset.mem_sigma, Nat.mem_divisors] at hp
    obtain ⟨⟨hdn, -⟩, hq⟩ := hp
    obtain ⟨-, -, -, -, -, hcop, -⟩ := mem_quadruplesAll.1 hq
    have hd : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
    have hgcd : Nat.gcd (d * a1) (d * a1') = d := by
      rw [Nat.gcd_mul_left, hcop, mul_one]
    simp only [hgcd, Nat.mul_div_cancel_left _ hd]
  · rintro ⟨x, x', y, y'⟩ _
    rfl

/-! ## Möbius inversion

With `Q(n) = ∑_{d ∣ n} R(d)` in hand, Möbius inversion gives `R` back from `Q`.
This is equation (mobius) of the paper.  Both are recast over `ℤ` so that
Mathlib's inversion applies. -/

/-- `R(n)`: the sum of `x'` over quadruples with `gcd(x,y) = 1`. -/
def Rquad (n : ℕ) : ℤ := ∑ q ∈ quadruplesAll n, (q.2.1 : ℤ)

/-- `Q(n)`: the same sum with no gcd condition. -/
def Qquad (n : ℕ) : ℤ := ∑ q ∈ quadruplesQ n, (q.2.1 : ℤ)

theorem Qquad_eq {n : ℕ} (hn : 0 < n) : Qquad n = ∑ d ∈ n.divisors, Rquad (n / d) := by
  unfold Qquad Rquad
  exact_mod_cast sum_snd_quadruplesQ hn

/-- `Q(n) = ∑_{d ∣ n} R(d)`. -/
theorem sum_Rquad {n : ℕ} (hn : 0 < n) : ∑ d ∈ n.divisors, Rquad d = Qquad n := by
  rw [Qquad_eq hn, Nat.sum_div_divisors]

/-- **Equation (mobius).**  `R(n) = ∑_{d ∣ n} μ(d) · Q(n/d)`. -/
theorem moebius_Rquad {n : ℕ} (hn : 0 < n) :
    ∑ x ∈ n.divisorsAntidiagonal, ArithmeticFunction.moebius x.1 • Qquad x.2 = Rquad n :=
  ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq.1 (fun _ hm => sum_Rquad hm) n hn

/-! ## Sanity checks

`K(c₀,…,c_l)` is the numerator of the continued fraction `[c₀; c₁,…,c_l]`.
For instance `[2;3,4] = 2 + 1/(3 + 1/4) = 30/13`, so `K[2,3,4] = 30`. -/

#guard K [2, 3, 4] = 30
#guard K [3, 7] = 22
#guard K [1, 1, 1, 1, 1] = 8
#guard (K ([2, 3] ++ [4, 5]) = K [2, 3] * K [4, 5] + K [2] * K [5])
#guard K [2, 3, 4].reverse = K [2, 3, 4]
#guard Nat.gcd (K [2, 3, 4]) (K [2, 3, 4].dropLast) = 1
#guard K [2, 3, 4].dropLast < K [2, 3, 4]
#guard K [2, 3, 4].tail < K [2, 3, 4]
-- `K [2,3,4] = 30` and `K [2,3] = 7`, so the pair `(30, 7)` recovers `[2,3,4]`.
#guard cf 30 7 = [2, 3, 4]
#guard K (cf 30 7) = 30
#guard K (cf 30 7).dropLast = 7
-- `(30, 13)` is the reversed expansion, since `K [4,3] = 13`.
#guard cf 30 13 = [4, 3, 2]
#guard cf (K [2, 3, 4]) (K [2, 3, 4].dropLast) = [2, 3, 4]
#guard cf (K [5, 1, 7, 2]) (K [5, 1, 7, 2].dropLast) = [5, 1, 7, 2]
-- Euclid on (30,13) gives remainders 13, 4, 1, summing to 18; the prefixes of
-- `cf 30 13 = [4,3,2]` have continuants `K [] = 1`, `K [4] = 4`, `K [4,3] = 13`.
#guard remSum 30 13 = 18
#guard (List.range (cf 30 13).length).map (fun j => K ((cf 30 13).take j)) = [1, 4, 13]
-- `k = 13 > 30/2`, so the last entry of `cf 30 13` is `30/13 = 2`; for `k = 7`
-- we get `30/7 = 4`.
#guard (cf 30 13).getLast? = some 2
#guard (cf 30 7).getLast? = some 4
-- Splitting `cf 30 7 = [2,3,4]` at `j = 1` gives `x = K [2] = 2`,
-- `x' = K [3,4] = 13`, `y = K [] = 1`, `y' = K [4] = 4`, and indeed
-- `2 * 13 + 1 * 4 = 30`.
#guard K ((cf 30 7).take 1) * K ((cf 30 7).drop 1)
        + K ((cf 30 7).take 1).dropLast * K ((cf 30 7).drop 1).tail = 30
#guard K ((cf 30 7).take 2) * K ((cf 30 7).drop 2)
        + K ((cf 30 7).take 2).dropLast * K ((cf 30 7).drop 2).tail = 30
#guard ((2, 13, 1, 4) : ℕ × ℕ × ℕ × ℕ) ∈ quadruples 30
#guard ((7, 4, 2, 1) : ℕ × ℕ × ℕ × ℕ) ∈ quadruples 30
-- Equation (eq. heilbron), checked numerically for several `n`.
#guard (List.range 40).all (fun n =>
  (∑ k ∈ shifts n, remSum n k) = (shifts n).card + ∑ q ∈ quadruples n, q.1)
-- The remainder sum scales: Euclid on `(dn, dk)` is `d` times Euclid on `(n,k)`.
#guard remSum 42 18 = 3 * remSum 14 6
-- Q(n) = sum over divisors of R, checked numerically.
#guard (List.range 20).all (fun m => let n := m + 1
  (∑ q ∈ quadruplesQ n, q.2.1)
    = ∑ d ∈ n.divisors, ∑ p ∈ quadruplesAll (n / d), p.2.1)
-- Equation (eq. heilbron) itself, checked numerically.
#guard (List.range 22).all (fun m => let n := m + 1
  (∑ k ∈ allShifts n, remSum n k)
    = (∑ k ∈ allShifts n, Nat.gcd n k) + ∑ q ∈ quadruplesAll n, q.2.1)
-- The aggregated Heilbronn identity, checked numerically.
#guard (List.range 25).all (fun m => let n := m + 1
  (∑ k ∈ allShifts n, remSum n k)
    = (∑ k ∈ allShifts n, Nat.gcd n k)
      + ∑ g ∈ n.divisors, g * ∑ q ∈ quadruples (n / g), q.1)
#guard (List.range 12).all (fun n => (List.range 12).all (fun k =>
  (List.range 5).all (fun d => remSum (d * n) (d * k) = d * remSum n k)))

end BlockCycleRotation
