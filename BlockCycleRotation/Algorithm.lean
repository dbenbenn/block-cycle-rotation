/-
# The block cycle recursion and its move count

This file formalises the cost accounting of section 2 and Lemma 11 of

  Valentin Blomer and Kai-Uwe Bux,
  *The cost of cyclic permutations and remainder sums in the Euclidean algorithm*,
  AofA 2026, LIPIcs vol. 381, 14:1--14:17.  arXiv:2601.00979.

The block cycle algorithm, rotating an array of length `n` by `k` places,
recurses on the pair `(n, k)`.  Writing `b = ⌊n / k⌋` for the number of blocks,
one step performs a cyclic permutation of `b` blocks of length `k`, costing
`(b + 1) * k` moves, and leaves the subproblem of rotating the last
`k + (n % k)` entries by `n % k`.  So the algorithm's recursion is

  `(n, k) ↦ (k + n % k, n % k)`.

Note this is *not* the Euclidean step `(n, k) ↦ (k, n % k)`: the first components
differ.  They agree modulo the second component, which is the congruence
`pᵢ ≡ nᵢ mod 𝔯ᵢ` appearing in the paper's proof of Lemma 11, and it is why the
segment lengths are nevertheless the Euclidean remainders.

The main result is `cost_add_gcd`, an unconditional form of the paper's
Lemma 11(2) together with equation (7), labelled (relation):

  `cost n k + gcd n k = n + 2 * remSum n k`,

which identifies the algorithm's true move count with the quantity `moveCount`
studied in `Euclid.lean`.  Combined with the worst-case bound proved there, this
upgrades that bound from a statement about a recurrence to a statement about the
number of moves the algorithm actually performs.
-/

import BlockCycleRotation.Euclid

namespace BlockCycleRotation

/-! ## The algorithm's recursion -/

/-- `cost n k` is the total number of moves the block cycle algorithm performs
when rotating an array of length `n` by `k` places.

One step permutes `⌊n / k⌋` blocks of length `k` cyclically, at a cost of
`(⌊n / k⌋ + 1) * k` moves, and recurses on `(k + n % k, n % k)`. -/
def cost (n k : ℕ) : ℕ :=
  if h : k = 0 then 0 else (n / k + 1) * k + cost (k + n % k) (n % k)
termination_by k
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero h)

@[simp]
theorem cost_zero (n : ℕ) : cost n 0 = 0 := by
  rw [cost]; simp

theorem cost_of_pos {k : ℕ} (n : ℕ) (hk : k ≠ 0) :
    cost n k = (n / k + 1) * k + cost (k + n % k) (n % k) := by
  rw [cost]; simp [hk]

/-- `finalSeg n k` is the segment length the recursion terminates on. -/
def finalSeg (n k : ℕ) : ℕ :=
  if h : k = 0 then n else finalSeg (k + n % k) (n % k)
termination_by k
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero h)

@[simp]
theorem finalSeg_zero (n : ℕ) : finalSeg n 0 = n := by
  rw [finalSeg]; simp

theorem finalSeg_of_pos {k : ℕ} (n : ℕ) (hk : k ≠ 0) :
    finalSeg n k = finalSeg (k + n % k) (n % k) := by
  rw [finalSeg]; simp [hk]

/-! ## Arithmetic of one step -/

/-- One Euclidean step, in the orientation we use throughout. -/
theorem gcd_step (n k : ℕ) : Nat.gcd n k = Nat.gcd k (n % k) := by
  rw [Nat.gcd_comm n k, Nat.gcd_rec k n]
  exact Nat.gcd_comm _ _

/-- Shifting the first argument by the second does not change the gcd. -/
theorem gcd_add_left (k r : ℕ) : Nat.gcd (k + r) r = Nat.gcd k r := by
  rw [Nat.gcd_comm (k + r) r, Nat.gcd_comm k r]
  exact Nat.gcd_add_self_right r k

/-- **`remSum` only sees the first argument modulo the second.**

This is the content of the induction in the paper's proof of Lemma 11: the
algorithm's recursion and the Euclidean algorithm keep different first
components, but congruent ones, and so produce the same remainders. -/
theorem remSum_congr_mod {n m k : ℕ} (h : n % k = m % k) : remSum n k = remSum m k := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    simp only [Nat.mod_zero] at h
    subst h
    rfl
  · rw [remSum_of_pos n hk.ne', remSum_of_pos m hk.ne', h]

/-- The step of the algorithm's recursion agrees with the Euclidean step. -/
theorem remSum_step {k r : ℕ} : remSum (k + r) r = remSum k r :=
  remSum_congr_mod (by simp [Nat.add_mod_right])

/-! ## Lemma 11(1): where the recursion stops -/

/-- **Lemma 11(1).**  The block cycle algorithm terminates on a subproblem with
parameters `(gcd n k, 0)`. -/
theorem finalSeg_eq_gcd : ∀ k n : ℕ, finalSeg n k = Nat.gcd n k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro n
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; simp
    · rw [finalSeg_of_pos n hk.ne', ih (n % k) (Nat.mod_lt _ hk), gcd_add_left,
        ← gcd_step]

/-! ## The move count: Lemma 11(2) with equation (7) -/

/-- **Lemma 11(2), with equation (7).**  The number of moves performed by the block cycle
algorithm is `n - gcd n k` moves of type B plus `2 * remSum n k` moves of type A.

Stated additively, so that it holds unconditionally (with no truncated
subtraction and no hypothesis relating `n` and `k`). -/
theorem cost_add_gcd : ∀ k n : ℕ, cost n k + Nat.gcd n k = n + 2 * remSum n k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro n
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; simp
    have hk0 : k ≠ 0 := hk.ne'
    have hrk : n % k < k := Nat.mod_lt _ hk
    -- the recursive call, rewritten so both gcd and remSum refer to `(n, k)`
    have IH := ih (n % k) hrk (k + n % k)
    rw [gcd_add_left, ← gcd_step, remSum_step] at IH
    -- unfold one step of the algorithm and of `remSum`
    rw [cost_of_pos n hk0, remSum_of_pos n hk0]
    have hq : k * (n / k) + n % k = n := Nat.div_add_mod n k
    have hmul : (n / k + 1) * k = k * (n / k) + k := by ring
    rw [hmul]
    omega

/-- The algorithm's move count is the `moveCount` of `Euclid.lean`. -/
theorem cost_eq_moveCount {n k : ℕ} (hn : 0 < n) : cost n k = moveCount n k := by
  have hg : Nat.gcd n k ≤ n := Nat.le_of_dvd hn (Nat.gcd_dvd_left n k)
  have := cost_add_gcd k n
  simp only [moveCount]
  omega

/-- **Worst case, for the algorithm itself.**  For `2 * k ≤ n` the block cycle
algorithm performs at most `3 * (n - gcd n k)` moves. -/
theorem cost_add_gcd_le {n k : ℕ} (h : 2 * k ≤ n) :
    cost n k + 3 * Nat.gcd n k ≤ 3 * n := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · have hk : k = 0 := by omega
    subst hn; subst hk; simp
  · rw [cost_eq_moveCount hn]
    exact moveCount_add_gcd_le h

/-- The block cycle algorithm never performs more than `3 * n` moves. -/
theorem cost_le_three_mul {n k : ℕ} (h : 2 * k ≤ n) : cost n k ≤ 3 * n := by
  have := cost_add_gcd_le h
  omega

/-! ## Sanity checks

Observation 3: `n = 21`, `k = 8` costs 58 moves.  The recursion visits
`(21,8), (13,5), (8,3), (5,2), (3,1)` at costs `24, 15, 9, 6, 4`. -/

#guard cost 21 8 = 58
#guard cost 21 8 = moveCount 21 8
#guard finalSeg 21 8 = 1
#guard (List.range 40).all (fun n => (List.range 40).all
  (fun k => cost n k + Nat.gcd n k = n + 2 * remSum n k))

/-! ## The Fibonacci worst case

Observation 3 says the worst case is approached along `k = F_m`, `n = F_{m+2}`,
where the algorithm takes `3∑_{j≤m} F_j - 2 = 3n - 3gcd(n,k) - 2` moves.  Since
`∑_{j≤m} F_j = F_{m+2} - 1` and `gcd(F_{m+2}, F_m) = 1`, that is `3n - 5`. -/

theorem fib_two_le {j : ℕ} : 2 ≤ Nat.fib (j + 3) := by
  have h : Nat.fib 3 ≤ Nat.fib (j + 3) := Nat.fib_mono (by omega)
  have h3 : Nat.fib 3 = 2 := by decide
  omega

/-- One Euclidean step on consecutive Fibonacci numbers.  (Stated from index `2`
upwards: at the very bottom `F₁ = F₂ = 1` and the pattern breaks.) -/
theorem fib_mod_fib (j : ℕ) : Nat.fib (j + 4) % Nat.fib (j + 3) = Nat.fib (j + 2) := by
  have hsplit : Nat.fib (j + 4) = Nat.fib (j + 2) + Nat.fib (j + 3) := Nat.fib_add_two
  have hlt : Nat.fib (j + 2) < Nat.fib (j + 3) := Nat.fib_lt_fib_succ (n := j + 2) (by omega)
  rw [hsplit, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt hlt

/-- Consecutive Fibonacci numbers: `remSum F_{m+1} F_m = F_{m+2} - 2` for `m ≥ 2`. -/
theorem remSum_fib_consec : ∀ j : ℕ, remSum (Nat.fib (j + 3)) (Nat.fib (j + 2)) =
    Nat.fib (j + 4) - 2 := by
  intro j
  induction j with
  | zero =>
    have h2 : Nat.fib 2 = 1 := by decide
    have h3 : Nat.fib 3 = 2 := by decide
    have h4 : Nat.fib 4 = 3 := by decide
    norm_num [h2, h3, h4, remSum_of_pos (k := 1) 2 (by norm_num)]
  | succ J ih =>
    have hfib0 : Nat.fib (J + 3) ≠ 0 := (Nat.fib_pos.2 (by omega)).ne'
    have e1 : J + 1 + 2 = J + 3 := by omega
    have e2 : J + 1 + 3 = J + 4 := by omega
    have e3 : J + 1 + 4 = J + 5 := by omega
    rw [e1, e2, e3]
    rw [remSum_of_pos _ hfib0, fib_mod_fib J, ih]
    have hadd : Nat.fib (J + 5) = Nat.fib (J + 3) + Nat.fib (J + 4) := by
      have h : Nat.fib (J + 3 + 2) = Nat.fib (J + 3) + Nat.fib (J + 3 + 1) := Nat.fib_add_two
      have e4 : J + 3 + 2 = J + 5 := by omega
      have e5 : J + 3 + 1 = J + 4 := by omega
      rw [e4, e5] at h
      exact h
    have hpos : 2 ≤ Nat.fib (J + 4) := by
      have h : Nat.fib 3 ≤ Nat.fib (J + 4) := Nat.fib_mono (by omega)
      have h3 : Nat.fib 3 = 2 := by decide
      omega
    omega

/-- The paper's `n = F_{m+2}`, `k = F_m` case: `remSum = F_{m+2} - 2`. -/
theorem remSum_fib (j : ℕ) :
    remSum (Nat.fib (j + 4)) (Nat.fib (j + 2)) = Nat.fib (j + 4) - 2 := by
  have hfib0 : Nat.fib (j + 2) ≠ 0 := (Nat.fib_pos.2 (by omega)).ne'
  rcases Nat.eq_zero_or_pos j with hj | hj
  · -- `j = 0`: here `F₂ = 1` divides `F₄ = 3` and the recursion stops at once.
    subst hj
    have h2 : Nat.fib 2 = 1 := by decide
    have h4 : Nat.fib 4 = 3 := by decide
    norm_num [h2, h4, remSum_of_pos (k := 1) 3 (by norm_num)]
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have e2 : i + 1 + 2 = i + 3 := by omega
    have e4 : i + 1 + 4 = i + 5 := by omega
    rw [e2, e4]
    have hfib0' : Nat.fib (i + 3) ≠ 0 := (Nat.fib_pos.2 (by omega)).ne'
    have hsplit : Nat.fib (i + 5) = Nat.fib (i + 2) + 2 * Nat.fib (i + 3) := by
      have h1 : Nat.fib (i + 3 + 2) = Nat.fib (i + 3) + Nat.fib (i + 3 + 1) := Nat.fib_add_two
      have h2 : Nat.fib (i + 2 + 2) = Nat.fib (i + 2) + Nat.fib (i + 2 + 1) := Nat.fib_add_two
      have a1 : i + 3 + 2 = i + 5 := by omega
      have a2 : i + 3 + 1 = i + 4 := by omega
      have a3 : i + 2 + 2 = i + 4 := by omega
      have a4 : i + 2 + 1 = i + 3 := by omega
      rw [a1, a2] at h1
      rw [a3, a4] at h2
      omega
    have hlt : Nat.fib (i + 2) < Nat.fib (i + 3) := Nat.fib_lt_fib_succ (n := i + 2) (by omega)
    have hmod : Nat.fib (i + 5) % Nat.fib (i + 3) = Nat.fib (i + 2) := by
      rw [hsplit, Nat.mul_comm 2 (Nat.fib (i + 3)), Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt hlt
    have hprev : remSum (Nat.fib (i + 3)) (Nat.fib (i + 2)) = Nat.fib (i + 4) - 2 :=
      remSum_fib_consec i
    have hpos : 2 ≤ Nat.fib (i + 4) := by
      have h : Nat.fib 3 ≤ Nat.fib (i + 4) := Nat.fib_mono (by omega)
      have h3 : Nat.fib 3 = 2 := by decide
      omega
    have hadd : Nat.fib (i + 5) = Nat.fib (i + 3) + Nat.fib (i + 4) := by
      have h : Nat.fib (i + 3 + 2) = Nat.fib (i + 3) + Nat.fib (i + 3 + 1) := Nat.fib_add_two
      have a1 : i + 3 + 2 = i + 5 := by omega
      have a2 : i + 3 + 1 = i + 4 := by omega
      rw [a1, a2] at h
      exact h
    rw [remSum_of_pos _ hfib0', hmod, hprev]
    omega

theorem gcd_fib_add_two (m : ℕ) : Nat.gcd (Nat.fib (m + 2)) (Nat.fib m) = 1 := by
  have hsplit : Nat.fib (m + 2) = Nat.fib (m + 1) + Nat.fib m := by
    rw [Nat.fib_add_two]; ring
  rw [hsplit, gcd_add_left]
  exact (Nat.fib_coprime_fib_succ m).symm

/-- **Observation 3, the Fibonacci family.**  At `n = F_{m+2}`, `k = F_m` (`m ≥ 2`)
the algorithm uses `3n - 5 = 3n - 3gcd(n,k) - 2` moves, two short of the
worst-case bound `3n - 3gcd(n,k)` of Theorem A. -/
theorem moveCount_fib (j : ℕ) :
    moveCount (Nat.fib (j + 4)) (Nat.fib (j + 2)) = 3 * Nat.fib (j + 4) - 5 := by
  have hg : Nat.gcd (Nat.fib (j + 4)) (Nat.fib (j + 2)) = 1 := by
    have h := gcd_fib_add_two (m := j + 2)
    have e : j + 2 + 2 = j + 4 := by omega
    rwa [e] at h
  have hr : remSum (Nat.fib (j + 4)) (Nat.fib (j + 2)) = Nat.fib (j + 4) - 2 := remSum_fib j
  have hpos : 3 ≤ Nat.fib (j + 4) := by
    have h : Nat.fib 4 ≤ Nat.fib (j + 4) := Nat.fib_mono (by omega)
    have h4 : Nat.fib 4 = 3 := by decide
    omega
  unfold moveCount
  rw [hg, hr]
  omega

end BlockCycleRotation
