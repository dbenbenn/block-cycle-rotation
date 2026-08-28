/-
# Correctness of the block cycle step

The block cycle algorithm rotates a list `l` of length `n` left by `k`.  Writing
`b = ⌊n / k⌋`, one step cyclically permutes the first `b` blocks of length `k`,
moving block 1 to the end of that group.  This file proves that step correct:
the first `(b - 1) * k` entries land in their final position, and what remains is
a rotation of the last `k + (n % k)` entries.

Reference: Blomer--Bux, section 2 and Figure 1.
-/

import BlockCycleRotation.Algorithm

namespace BlockCycleRotation

variable {α : Type*}

/-- **The block cycle step.**

With `m = ⌊n / k⌋ * k` the length of the part covered by whole blocks, splitting
`l = P ++ Q` with `P = l.take m` and `Q = l.drop m`:

* `P.drop k` (the first `(b-1) * k` entries) is already in final position, and
* the remaining suffix is `(P.take k ++ Q).rotate k`, a rotation of a list of
  length `k + n % k` — the subproblem the algorithm recurses on. -/
theorem rotate_block_step (l : List α) {k : ℕ} (hk : 0 < k) (hkn : k ≤ l.length) :
    l.rotate k =
      (l.take (l.length / k * k)).drop k ++
        ((l.take (l.length / k * k)).take k ++ l.drop (l.length / k * k)).rotate k := by
  set n := l.length with hn
  set m := n / k * k with hm
  have hmn : m ≤ n := Nat.div_mul_le_self n k
  have hb : 1 ≤ n / k := (Nat.one_le_div_iff hk).2 hkn
  have hkm : k ≤ m := by
    calc k = 1 * k := (one_mul k).symm
      _ ≤ n / k * k := Nat.mul_le_mul_right k hb
  have hPlen : (l.take m).length = m := by
    rw [List.length_take]
    omega
  -- the first `k` entries of `l` are the first `k` entries of `P`
  have htakek : l.take k = (l.take m).take k := by
    rw [List.take_take]
    congr 1
    omega
  -- dropping `k` from `l` splits as dropping `k` from `P`, then all of `Q`
  have hdropk : l.drop k = (l.take m).drop k ++ l.drop m := by
    conv_lhs => rw [← List.take_append_drop m l]
    rw [List.drop_append_of_le_length (by omega)]
  -- the inner rotation just swaps the two pieces
  have hinner : ((l.take m).take k ++ l.drop m).rotate k
      = l.drop m ++ (l.take m).take k := by
    have hlen : ((l.take m).take k).length = k := by
      rw [List.length_take, hPlen]
      omega
    have hle : k ≤ ((l.take m).take k ++ l.drop m).length := by
      rw [List.length_append, hlen]
      omega
    rw [List.rotate_eq_drop_append_take hle, List.drop_left' hlen, List.take_left' hlen]
  rw [List.rotate_eq_drop_append_take hkn, hdropk, htakek, hinner, List.append_assoc]

/-! ## The algorithm

The step above is degenerate when `⌊n / k⌋ = 1`, i.e. when `k > n / 2`: it moves
nothing and recurses on the whole list.  This is exactly the case the paper
handles "using symmetry", by swapping the roles of the two segments and moving
blocks the other way.  We implement that mirrored step by reversal, which turns
a left rotation by `k` into a left rotation by `n - k` (`List.reverse_rotate`).

Termination is lexicographic in `(k, l.length)`: the left step keeps `k` and
shortens the list, the mirrored step strictly decreases `k`. -/

/-- The block cycle rotation algorithm on lists. -/
def bcRotate (l : List α) (k : ℕ) : List α :=
  if k = 0 then l
  else if l.length ≤ k then l
  else if 2 * k ≤ l.length then
    (l.take (l.length / k * k)).drop k ++
      bcRotate ((l.take (l.length / k * k)).take k ++ l.drop (l.length / k * k)) k
  else
    (bcRotate l.reverse (l.length - k)).reverse
termination_by (k, l.length)
decreasing_by
  · -- left step: `k` unchanged, the list gets strictly shorter
    refine Prod.Lex.right _ ?_
    have hk : 0 < k := Nat.pos_of_ne_zero ‹k ≠ 0›
    have hb : 2 ≤ l.length / k := (Nat.le_div_iff_mul_le hk).2 (by omega)
    have hmn : l.length / k * k ≤ l.length := Nat.div_mul_le_self _ _
    have hkm : 2 * k ≤ l.length / k * k := by
      calc 2 * k = 2 * k := rfl
        _ ≤ l.length / k * k := Nat.mul_le_mul_right k hb
    simp only [List.length_append, List.length_take, List.length_drop]
    omega
  · -- mirrored step: `k` strictly decreases
    exact Prod.Lex.left _ _ (by omega)

/-- **Correctness of the block cycle algorithm.**  For `k ≤ l.length`,
`bcRotate l k` is the rotation of `l` by `k`. -/
theorem bcRotate_eq_rotate : ∀ (l : List α) (k : ℕ), k ≤ l.length →
    bcRotate l k = l.rotate k := by
  intro l k
  induction l, k using bcRotate.induct with
  | case1 l =>
    intro _
    rw [bcRotate]
    simp
  | case2 l k h0 h1 =>
    intro hk
    have hkl : k = l.length := le_antisymm hk h1
    rw [bcRotate, if_neg h0, if_pos h1, hkl, List.rotate_length]
  | case3 l k h0 h1 h2 ih =>
    intro hk
    rw [bcRotate, if_neg h0, if_neg h1, if_pos h2]
    have hkpos : 0 < k := Nat.pos_of_ne_zero h0
    have hmn : l.length / k * k ≤ l.length := Nat.div_mul_le_self _ _
    have hb : 1 ≤ l.length / k := (Nat.one_le_div_iff hkpos).2 hk
    have hkm : k ≤ l.length / k * k := by
      calc k = 1 * k := (one_mul k).symm
        _ ≤ l.length / k * k := Nat.mul_le_mul_right k hb
    have hsub : k ≤ (List.take k (List.take (l.length / k * k) l) ++
        List.drop (l.length / k * k) l).length := by
      simp only [List.length_append, List.length_take, List.length_drop]
      omega
    rw [ih hsub]
    exact (rotate_block_step l hkpos hk).symm
  | case4 l k h0 h1 h2 ih =>
    intro hk
    rw [bcRotate, if_neg h0, if_neg h1, if_neg h2]
    simp only [List.unattach_reverse, List.unattach_attach] at ih
    have hkn : k < l.length := by omega
    have hrev : l.length - k ≤ l.reverse.length := by simp
    rw [ih hrev]
    have hrr := List.reverse_rotate l k
    rw [Nat.mod_eq_of_lt hkn] at hrr
    rw [← hrr, List.reverse_reverse]

/-! ## Sanity checks -/

example : ([0, 1, 2, 3, 4] : List ℕ).rotate 2 = [2, 3, 4, 0, 1] := by decide

#guard bcRotate [0, 1, 2, 3, 4] 2 = [2, 3, 4, 0, 1]
#guard bcRotate [0, 1, 2, 3, 4] 3 = [3, 4, 0, 1, 2]
#guard (List.range 30).all (fun n => (List.range 30).all (fun k =>
  k > n || bcRotate (List.range n) k = (List.range n).rotate k))

end BlockCycleRotation
