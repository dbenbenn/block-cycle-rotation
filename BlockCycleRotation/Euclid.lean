/-
# Remainder sums in the Euclidean algorithm

This file formalises the arithmetic core of

  Valentin Blomer and Kai-Uwe Bux,
  *The cost of cyclic permutations and remainder sums in the Euclidean algorithm*,
  AofA 2026, LIPIcs vol. 381, 14:1--14:17.  arXiv:2601.00979.

The block cycle rotation algorithm rotates an array of length `n` by `k` places.
By Lemma 12 of the paper, the sequence of segment lengths arising in its
recursion is exactly the sequence of remainders produced by the Euclidean
algorithm on `(n, k)`, and the total number of moves is

  `moveCount n k = n - gcd n k + 2 * remSum n k`.

Here we define `remSum`, the sum of those remainders, and prove the worst-case
bound underlying Theorem A: the algorithm uses at most `3 * (n - gcd n k)` moves.
-/

import Mathlib

namespace BlockCycleRotation

/-! ## The remainder sum -/

/-- `remSum n k` is the sum of the nonzero remainders produced by the Euclidean
algorithm started on the pair `(n, k)`.

Concretely, with `r₁ = k`, `p₁ = n` and `rᵢ₊₁ = pᵢ % rᵢ`, `pᵢ₊₁ = rᵢ`, this is
`r₁ + r₂ + ⋯`, the sum stopping at the last nonzero remainder.  This is the
quantity denoted `𝔯₁ + 𝔯₂ + ⋯` in Lemma 12 of the paper. -/
def remSum (n k : ℕ) : ℕ :=
  if h : k = 0 then 0 else k + remSum k (n % k)
termination_by k
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero h)

@[simp]
theorem remSum_zero (n : ℕ) : remSum n 0 = 0 := by
  rw [remSum]; simp

/-- The defining recursion, in the form we actually use. -/
theorem remSum_of_pos {k : ℕ} (n : ℕ) (hk : k ≠ 0) :
    remSum n k = k + remSum k (n % k) := by
  rw [remSum]; simp [hk]

/-! ## The master inequality

The bound we ultimately want, `remSum n k + gcd n k ≤ n` for `2 * k ≤ n`, is not
directly amenable to induction: the hypothesis `2 * k ≤ n` is *not* inherited by
the recursive call.  (For `n = 21`, `k = 8` the algorithm steps to `(8, 5)`, and
`2 * 5 > 8`.)  The following inequality holds for *every* pair and does
propagate, and it specialises to the bound we want. -/

/-- **Master inequality.**  For all `n` and `k`,
`remSum n k + gcd n k ≤ 2 * k + n % k`.

This is the inductive engine behind the worst-case analysis.  Note it holds
unconditionally, including for `k = 0` (where both sides equal `n`). -/
theorem remSum_add_gcd_le : ∀ k n : ℕ, remSum n k + Nat.gcd n k ≤ 2 * k + n % k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro n
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; simp
    have hk0 : k ≠ 0 := hk.ne'
    have hrk : n % k < k := Nat.mod_lt _ hk
    -- `gcd n k = gcd k (n % k)`, matching one step of the Euclidean algorithm.
    have hgcd : Nat.gcd n k = Nat.gcd k (n % k) := by
      rw [Nat.gcd_comm n k, Nat.gcd_rec k n]
      exact Nat.gcd_comm _ _
    rw [remSum_of_pos n hk0, hgcd]
    rcases Nat.eq_zero_or_pos (n % k) with hr0 | hr0
    · -- `k` divides `n`: the algorithm stops here, and both sides equal `2 * k`.
      rw [hr0]
      simp only [remSum_zero, Nat.gcd_zero_right, add_zero]
      omega
    · -- The inductive step, applying the master inequality to `(k, n % k)`.
      have IH := ih (n % k) hrk k
      -- `n % k + k % (n % k) ≤ k`, because `k % (n % k) ≤ k - n % k`.
      have key : n % k + k % (n % k) ≤ k := by
        have h1 : k % (n % k) ≤ k - n % k := by
          rw [Nat.mod_eq_sub_mod hrk.le]
          exact Nat.mod_le _ _
        omega
      omega

/-! ## The worst-case bound (Theorem A, worst case) -/

/-- For `2 * k ≤ n`, the remainder sum is at most `n - gcd n k`.

Stated additively to avoid truncated subtraction. -/
theorem remSum_add_gcd_le_self {n k : ℕ} (h : 2 * k ≤ n) :
    remSum n k + Nat.gcd n k ≤ n := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; simp
  -- Since `2 * k ≤ n`, the first quotient is at least `2`, so `2 * k + n % k ≤ n`.
  have hq : 2 ≤ n / k := (Nat.le_div_iff_mul_le hk).2 (by linarith)
  have : 2 * k + n % k ≤ n := by nlinarith [Nat.div_add_mod n k]
  exact le_trans (remSum_add_gcd_le k n) this

/-! ## Move count -/

/-- The number of moves the block cycle algorithm performs when rotating an
array of length `n` by `k ≤ n / 2` places (equation (12) of the paper):
`n - gcd n k` moves of type B, and `2 * remSum n k` moves of type A. -/
def moveCount (n k : ℕ) : ℕ := n - Nat.gcd n k + 2 * remSum n k

/-- **Worst case, Theorem A.**  The block cycle algorithm uses at most
`3 * (n - gcd n k)` moves; in particular at most `3 * n`. -/
theorem moveCount_add_gcd_le {n k : ℕ} (h : 2 * k ≤ n) :
    moveCount n k + 3 * Nat.gcd n k ≤ 3 * n := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · have hk : k = 0 := by omega
    subst hn; subst hk; simp [moveCount]
  · have hg : Nat.gcd n k ≤ n := Nat.le_of_dvd hn (Nat.gcd_dvd_left n k)
    have := remSum_add_gcd_le_self h
    simp only [moveCount]
    omega

/-- The block cycle algorithm never uses more than `3 * n` moves. -/
theorem moveCount_le_three_mul {n k : ℕ} (h : 2 * k ≤ n) : moveCount n k ≤ 3 * n := by
  have := moveCount_add_gcd_le h
  omega

/-! ## Sanity checks against the paper

Observation 6 of the paper works out the example of a left segment of length `8`
and a right segment of length `13`, i.e. `n = 21`, `k = 8`, and reports a cost of
`58` moves, via the remainder sequence `8, 5, 3, 2, 1`. -/

-- `remSum` is defined by well-founded recursion, so `decide` cannot reduce it;
-- `#guard` evaluates via the interpreter and fails at elaboration time if false.
#guard remSum 21 8 = 19
#guard moveCount 21 8 = 58
#guard remSum 13 5 = 11

end BlockCycleRotation
