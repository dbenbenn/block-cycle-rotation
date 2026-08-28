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

end BlockCycleRotation
