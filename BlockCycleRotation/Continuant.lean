/-
# Continuants

Heilbronn's bijection (Heilbronn 1969, p. 93), which underlies equation
(eq. heilbron) of Blomer--Bux, sends a continued-fraction expansion
`n = K(c₀,…,c_l)` together with a split point `j` to the quadruple

  `a = K(c₀,…,c_j)`,   `b = K(c_{j+1},…,c_l)`,
  `a' = K(c₀,…,c_{j-1})`, `b' = K(c_{j+2},…,c_l)`,

and the relation `n = a·b + a'·b'` that makes the quadruple a solution is
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
solution of `n = a·b + a'·b'`. -/
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

This supplies the condition `gcd(a, a') = 1` in Heilbronn's correspondence. -/
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

Heilbronn's quadruples satisfy `a > a' ≥ 1` and `b > b' ≥ 1`, where `a'` is the
continuant of the truncated prefix and `b'` that of the truncated suffix.  These
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

  `a = K l₁`,  `b = K l₂`,  `a' = K l₁.dropLast`,  `b' = K l₂.tail`,

and the theorem below is that this quadruple satisfies every condition defining
the target set of Heilbronn's bijection. -/

/-- **Heilbronn's correspondence, forward direction.**  The quadruple obtained by
splitting an expansion satisfies `n = a·b + a'·b'`, the size conditions
`a > a' ≥ 1` and `b > b' ≥ 1`, and the coprimality conditions. -/
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

Recovering the expansion from the pair `(a, a')` is exactly the Euclidean
algorithm: `K_concat` says `a = c·a' + K m.dropLast` with `c = a / a'` and
`K m.dropLast = a mod a'`, so peeling entries off the end of the list is the
same as running Euclid on `(a, a')`.  This is the point of contact between
Heilbronn's bijection and the remainder sums of `Euclid.lean`. -/

/-- The continued-fraction expansion of `a / a'`, read off by the Euclidean
algorithm.  The quotients are collected from the end of the list backwards. -/
def cf (a a' : ℕ) : List ℕ :=
  if h : a' = 0 then [] else cf a' (a % a') ++ [a / a']
termination_by a'
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero h)

@[simp] theorem cf_zero (a : ℕ) : cf a 0 = [] := by rw [cf]; simp

theorem cf_of_pos {a a' : ℕ} (h : a' ≠ 0) :
    cf a a' = cf a' (a % a') ++ [a / a'] := by rw [cf]; simp [h]

/-- **Heilbronn's correspondence, inverse direction.**  Every coprime pair
`a > a' ≥ 1` is `(K l, K l.dropLast)` for the expansion `l = cf a a'`. -/
theorem K_cf : ∀ a' a : ℕ, 1 ≤ a' → a' < a → Nat.gcd a a' = 1 →
    K (cf a a') = a ∧ K (cf a a').dropLast = a' := by
  intro a'
  induction a' using Nat.strong_induction_on with
  | _ a' ih =>
    intro a ha'1 hlt hgcd
    rcases Nat.lt_or_ge a' 2 with h2 | h2
    · -- `a' = 1`: the expansion is the single entry `a`
      have ha'eq : a' = 1 := by omega
      subst ha'eq
      have h1 : cf a 1 = [a] := by
        rw [cf_of_pos (by norm_num), Nat.mod_one, cf_zero, Nat.div_one]
        simp
      rw [h1]
      simp
    · -- `a' ≥ 2`: peel off the quotient and recurse
      have ha'ne : a' ≠ 0 := by omega
      have hrlt : a % a' < a' := Nat.mod_lt _ (by omega)
      have hr1 : 1 ≤ a % a' := by
        rcases Nat.eq_zero_or_pos (a % a') with h0 | h0
        · exfalso
          have hdvd : a' ∣ a := Nat.dvd_of_mod_eq_zero h0
          have hg : Nat.gcd a a' = a' := Nat.gcd_eq_right hdvd
          omega
        · exact h0
      have hgcd' : Nat.gcd a' (a % a') = 1 := by
        rw [← hgcd, Nat.gcd_comm a a', Nat.gcd_rec a' a]
        exact Nat.gcd_comm _ _
      obtain ⟨hK, hKd⟩ := ih (a % a') hrlt a' hr1 hrlt hgcd'
      have hne : cf a' (a % a') ≠ [] := by
        intro hc
        rw [hc] at hK
        simp at hK
        omega
      have hcf : cf a a' = cf a' (a % a') ++ [a / a'] := cf_of_pos ha'ne
      constructor
      · rw [hcf, K_concat _ hne (a / a'), hK, hKd]
        have hdm := Nat.div_add_mod a a'
        have hcomm : a / a' * a' = a' * (a / a') := Nat.mul_comm _ _
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
theorem cf_spec : ∀ a' a : ℕ, 1 ≤ a' → a' < a → Nat.gcd a a' = 1 →
    cf a a' ≠ [] ∧ (∀ x ∈ cf a a', 1 ≤ x) ∧ (∀ x ∈ (cf a a').head?, 2 ≤ x) := by
  intro a'
  induction a' using Nat.strong_induction_on with
  | _ a' ih =>
    intro a ha'1 hlt hgcd
    rcases Nat.lt_or_ge a' 2 with h2 | h2
    · have ha'eq : a' = 1 := by omega
      subst ha'eq
      have h1 : cf a 1 = [a] := by
        rw [cf_of_pos (by norm_num), Nat.mod_one, cf_zero, Nat.div_one]
        simp
      rw [h1]
      refine ⟨by simp, ?_, ?_⟩ <;> intro x hx <;> simp at hx <;> omega
    · have ha'ne : a' ≠ 0 := by omega
      have hrlt : a % a' < a' := Nat.mod_lt _ (by omega)
      have hr1 : 1 ≤ a % a' := by
        rcases Nat.eq_zero_or_pos (a % a') with h0 | h0
        · exfalso
          have hg : Nat.gcd a a' = a' := Nat.gcd_eq_right (Nat.dvd_of_mod_eq_zero h0)
          omega
        · exact h0
      have hgcd' : Nat.gcd a' (a % a') = 1 := by
        rw [← hgcd, Nat.gcd_comm a a', Nat.gcd_rec a' a]
        exact Nat.gcd_comm _ _
      obtain ⟨hne, hpos, hhd⟩ := ih (a % a') hrlt a' hr1 hrlt hgcd'
      have hq1 : 1 ≤ a / a' := (Nat.one_le_div_iff (by omega)).2 (by omega)
      rw [cf_of_pos ha'ne]
      refine ⟨by simp, ?_, ?_⟩
      · intro x hx
        rcases List.mem_append.1 hx with h | h
        · exact hpos x h
        · simp at h; omega
      · intro x hx
        rcases hcf : cf a' (a % a') with _ | ⟨y, ys⟩
        · exact absurd hcf hne
        · rw [hcf] at hx hhd
          simp at hx ⊢
          exact hhd x (by simp [hx])

/-- **Heilbronn's bijection.**

The map `l ↦ (K l, K l.dropLast)` is a bijection from normalised expansions
(nonempty, positive entries, first entry at least `2`) onto the coprime pairs
`a > a' ≥ 1`.  The first component is injectivity, the second surjectivity
together with the fact that the inverse lands among normalised expansions.

Combined with `heilbronn_forward`, this is the correspondence underlying
equation (eq. heilbron) of Blomer--Bux. -/
theorem heilbronn_bijection :
    (∀ l : List ℕ, l ≠ [] → (∀ c ∈ l, 1 ≤ c) → (∀ x ∈ l.head?, 2 ≤ x) →
        cf (K l) (K l.dropLast) = l)
      ∧ (∀ a a' : ℕ, 1 ≤ a' → a' < a → Nat.gcd a a' = 1 →
        (cf a a' ≠ [] ∧ (∀ c ∈ cf a a', 1 ≤ c) ∧ (∀ x ∈ (cf a a').head?, 2 ≤ x))
          ∧ K (cf a a') = a ∧ K (cf a a').dropLast = a') :=
  ⟨cf_K, fun a a' h1 h2 h3 => ⟨cf_spec a' a h1 h2 h3, K_cf a' a h1 h2 h3⟩⟩

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

Every quadruple `(a, b, a', b')` with `a > a' ≥ 1`, `b > b' ≥ 1` and both
coprimality conditions arises from a split expansion, and its continuant
identity `n = a·b + a'·b'` holds.  The suffix is obtained by reversing, which is
legitimate by `K_reverse`. -/
theorem heilbronn_surjective {a b a' b' : ℕ}
    (ha : 1 ≤ a') (hab : a' < a) (hga : Nat.gcd a a' = 1)
    (hb : 1 ≤ b') (hbb : b' < b) (hgb : Nat.gcd b b' = 1) :
    ∃ l₁ l₂ : List ℕ, l₁ ≠ [] ∧ l₂ ≠ [] ∧
      K l₁ = a ∧ K l₁.dropLast = a' ∧ K l₂ = b ∧ K l₂.tail = b' ∧
      K (l₁ ++ l₂) = a * b + a' * b' := by
  obtain ⟨hK₁, hKd₁⟩ := K_cf a' a ha hab hga
  obtain ⟨hne₁, -, -⟩ := cf_spec a' a ha hab hga
  obtain ⟨hK₂, hKd₂⟩ := K_cf b' b hb hbb hgb
  obtain ⟨hne₂, -, -⟩ := cf_spec b' b hb hbb hgb
  have hne₂' : (cf b b').reverse ≠ [] := by simpa using hne₂
  have hb₂ : K (cf b b').reverse = b := by rw [K_reverse]; exact hK₂
  have hb₂' : K ((cf b b').reverse).tail = b' := by
    rw [reverse_tail_eq, K_reverse]; exact hKd₂
  refine ⟨cf a a', (cf b b').reverse, hne₁, hne₂', hK₁, hKd₁, hb₂, hb₂', ?_⟩
  rw [K_append _ _ hne₁ hne₂', hK₁, hKd₁, hb₂, hb₂']

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
-- Splitting `cf 30 7 = [2,3,4]` at `j = 1` gives `a = K [2] = 2`,
-- `b = K [3,4] = 13`, `a' = K [] = 1`, `b' = K [4] = 4`, and indeed
-- `2 * 13 + 1 * 4 = 30`.
#guard K ((cf 30 7).take 1) * K ((cf 30 7).drop 1)
        + K ((cf 30 7).take 1).dropLast * K ((cf 30 7).drop 1).tail = 30
#guard K ((cf 30 7).take 2) * K ((cf 30 7).drop 2)
        + K ((cf 30 7).take 2).dropLast * K ((cf 30 7).drop 2).tail = 30

end BlockCycleRotation
