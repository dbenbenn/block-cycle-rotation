/-
# The average cost

Theorem 14 of Blomer--Bux states that the average number of moves, over shifts
`0 ≤ k < n`, is `D * n + O(n^(1/2+ε))` with `D ≈ 1.85`.  This file sets up the
average and proves the unconditional upper bound `avgCost n ≤ 3 * n`, which is
what the worst-case analysis gives.  The content of Theorem 14 is the sharp
constant and the error term; see `ExpSum.lean` for its analytic core.

The algorithm always recurses on the shorter of the two segments, using the
symmetry `M(n,k) = M(n, n-k)`; `algCost` records that.
-/

import BlockCycleRotation.Algorithm

namespace BlockCycleRotation

open Finset

/-- The number of moves used to rotate `n` items by `k` places.  The algorithm
exploits the symmetry `M(n,k) = M(n, n-k)` and recurses on the shorter segment. -/
def algCost (n k : ℕ) : ℕ := cost n (min k (n - k))

/-- Whatever the shift, the shorter segment is at most half the array. -/
theorem two_mul_min_le {n k : ℕ} (h : k ≤ n) : 2 * min k (n - k) ≤ n := by omega

/-- **Worst case.**  For any shift, the algorithm uses at most `3 * n` moves. -/
theorem algCost_le_three_mul {n k : ℕ} (h : k ≤ n) : algCost n k ≤ 3 * n :=
  cost_le_three_mul (two_mul_min_le h)

/-- `gcd` does not see the reflection the algorithm applies to the shift. -/
theorem gcd_min_eq {n k : ℕ} (h : k ≤ n) : Nat.gcd n (min k (n - k)) = Nat.gcd n k := by
  rcases le_total k (n - k) with hk | hk
  · rw [min_eq_left hk]
  · rw [min_eq_right hk, Nat.gcd_comm n (n - k), Nat.gcd_comm n k]
    exact Nat.gcd_self_sub_left h

/-- **Observation 2.**  The block cycle algorithm uses at most `3 * (n - gcd n k)`
moves, for *any* shift `k ≤ n` — the paper states it without restricting to
`2 * k ≤ n`.  Stated additively so that it holds with no truncated subtraction. -/
theorem algCost_add_gcd_le {n k : ℕ} (h : k ≤ n) :
    algCost n k + 3 * Nat.gcd n k ≤ 3 * n := by
  rw [algCost, ← gcd_min_eq h]
  exact cost_add_gcd_le (two_mul_min_le h)

/-- The average number of moves, over all shifts `0 ≤ k < n`. -/
noncomputable def avgCost (n : ℕ) : ℝ := (∑ k ∈ range n, (algCost n k : ℝ)) / n

/-- **The average cost is at most `3 * n`.**

Theorem 14 refines this to `D * n + O(n^(1/2+ε))` with `D ≈ 1.85`; see
`theorem13` in `Theorem13.lean`. -/
theorem avgCost_le_three_mul {n : ℕ} (hn : 0 < n) : avgCost n ≤ 3 * n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [avgCost, div_le_iff₀ hn']
  calc ∑ k ∈ range n, (algCost n k : ℝ)
      ≤ ∑ _k ∈ range n, (3 * n : ℝ) := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hkn : k ≤ n := le_of_lt (mem_range.1 hk)
        exact_mod_cast algCost_le_three_mul hkn
    _ = n * (3 * n) := by rw [sum_const, card_range, nsmul_eq_mul]
    _ = 3 * n * n := by ring

/-! ## Sanity check

For `n = 21`, `k = 8` the shorter segment is `8`, so this is Observation 3. -/

#guard algCost 21 8 = 58
#guard algCost 21 13 = 58

end BlockCycleRotation
