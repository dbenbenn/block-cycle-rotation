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

/-! ## Sanity checks

`K(c₀,…,c_l)` is the numerator of the continued fraction `[c₀; c₁,…,c_l]`.
For instance `[2;3,4] = 2 + 1/(3 + 1/4) = 30/13`, so `K[2,3,4] = 30`. -/

#guard K [2, 3, 4] = 30
#guard K [3, 7] = 22
#guard K [1, 1, 1, 1, 1] = 8
#guard (K ([2, 3] ++ [4, 5]) = K [2, 3] * K [4, 5] + K [2] * K [5])
#guard K [2, 3, 4].reverse = K [2, 3, 4]
#guard Nat.gcd (K [2, 3, 4]) (K [2, 3, 4].dropLast) = 1

end BlockCycleRotation
