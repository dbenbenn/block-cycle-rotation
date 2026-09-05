/-
# `D < 2`

Remark 15 says the expected number of moves per element is
less than `2`, so that on average the block cycle scheme beats trinity
rotation, which "uses essentially `2n` moves".  That is `D = 1 + 4C < 2`,
i.e. `C < 1/4`, and it needs a certified numerical bound on `C`.

The termwise bound of `Constant.lean` is `cTerm ≤ 3/(2x³)`; the sharper
`cTerm ≤ 1/x³` holds as well, because `x(2x+y) ≤ 2(x+y)²`.  Summing the
`x-1` admissible `y` gives `1/x²` per row and a tail `≤ 1/N`, so truncating
at `N = 20` leaves `C ≤ partial(20) + 1/20`, and `partial(20) < 1/5`.
-/

import BlockCycleRotation.Constant

namespace BlockCycleRotation

/-- **Sharper termwise bound.**  `cTerm ≤ 1/x³`. -/
theorem cTerm_le_cube (p : ℕ × ℕ) : cTerm p ≤ 1 / (p.1 : ℝ) ^ 3 := by
  unfold cTerm
  split
  · rename_i h
    obtain ⟨h1, h2, -⟩ := h
    have hp1 : (0 : ℝ) < (p.1 : ℝ) := by
      have : 0 < p.1 := by omega
      exact_mod_cast this
    have hp2 : (0 : ℝ) ≤ (p.2 : ℝ) := by positivity
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pow_pos hp1 2, mul_nonneg hp1.le hp2, mul_nonneg hp2 hp2,
      mul_nonneg (mul_nonneg hp1.le hp1.le) hp2]
  · positivity

/-- Each row is at most `1/x²`. -/
theorem cTerm_row_le_sq (x : ℕ) :
    ∑ y ∈ Finset.range x, cTerm (x, y) ≤ 1 / (x : ℝ) ^ 2 := by
  rcases Nat.eq_zero_or_pos x with h0 | h0
  · subst h0
    simp
  · have hx : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast h0
    calc ∑ y ∈ Finset.range x, cTerm (x, y)
        ≤ ∑ _y ∈ Finset.range x, 1 / (x : ℝ) ^ 3 :=
          Finset.sum_le_sum fun y _ => cTerm_le_cube (x, y)
      _ = (x : ℝ) * (1 / (x : ℝ) ^ 3) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = 1 / (x : ℝ) ^ 2 := by
          field_simp

/-- **The sharper tail bound.**  Truncating at `x ≤ N` loses at most `1/N`. -/
theorem cConst_le_partial_add_sharp {N : ℕ} (hN : 0 < N) :
    cConst ≤ (∑ x ∈ Finset.range (N + 1), ∑ y ∈ Finset.range x, cTerm (x, y))
      + 1 / (N : ℝ) := by
  rw [cConst_eq_tsum_finRows]
  refine Real.tsum_le_of_sum_le
    (fun x => Finset.sum_nonneg fun y _ => cTerm_nonneg _) fun s => ?_
  classical
  have hsplit : ∑ x ∈ s, (∑ y ∈ Finset.range x, cTerm (x, y))
      = (∑ x ∈ s.filter (fun x => x ≤ N), ∑ y ∈ Finset.range x, cTerm (x, y))
        + ∑ x ∈ s.filter (fun x => ¬ x ≤ N), ∑ y ∈ Finset.range x, cTerm (x, y) :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hlow : (∑ x ∈ s.filter (fun x => x ≤ N), ∑ y ∈ Finset.range x, cTerm (x, y))
      ≤ ∑ x ∈ Finset.range (N + 1), ∑ y ∈ Finset.range x, cTerm (x, y) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_
      (fun x _ _ => Finset.sum_nonneg fun y _ => cTerm_nonneg _)
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
    omega
  have hhigh : (∑ x ∈ s.filter (fun x => ¬ x ≤ N), ∑ y ∈ Finset.range x, cTerm (x, y))
      ≤ 1 / (N : ℝ) := by
    refine le_trans (Finset.sum_le_sum fun x _ => cTerm_row_le_sq x) ?_
    refine sum_inv_sq_tail_le hN _ fun x hx => ?_
    simp only [Finset.mem_filter] at hx
    omega
  rw [hsplit]
  linarith

/-! ## The numerical bound

Truncating at `N = 20` leaves `127` nonzero terms; their exact rational sum is
`0.193736…`, comfortably below `39/200`. -/

set_option maxHeartbeats 4000000 in
-- 127 nonzero rational terms with a 32-digit common denominator.
/-- The truncated series for `C` at `x ≤ 20`. -/
theorem cConst_partial_le :
    (∑ x ∈ Finset.range 21, ∑ y ∈ Finset.range x, cTerm (x, y)) ≤ 39 / 200 := by
  norm_num [cTerm, Finset.sum_range_succ]

/-- **`C < 1/4`.** -/
theorem cConst_lt_quarter : cConst < 1 / 4 := by
  have h := cConst_le_partial_add_sharp (N := 20) (by norm_num)
  have h2 := cConst_partial_le
  norm_num at h
  linarith

/-- **`D < 2`**: on average the block cycle scheme uses fewer than two moves per
element, hence fewer than trinity rotation, which uses essentially `2n`. -/
theorem dConst_lt_two : dConst < 2 := by
  rw [dConst]
  linarith [cConst_lt_quarter]

/-- `D > 1`, so the constant is not degenerate. -/
theorem one_lt_dConst : 1 < dConst := by
  rw [dConst]
  have h : 0 < cConst := by
    have h1 : cTerm (2, 1) ≤ ∑ y ∈ Finset.range 2, cTerm (2, y) := by
      refine Finset.single_le_sum (fun i _ => cTerm_nonneg _) ?_
      simp
    have h2 : (0 : ℝ) < cTerm (2, 1) := by
      unfold cTerm
      rw [if_pos (by norm_num)]
      norm_num
    have h3 : ∑ y ∈ Finset.range 2, cTerm (2, y) ≤ cConst := by
      rw [cConst_eq_tsum_finRows]
      exact (cRow_summable).le_tsum 2 (fun x' _ => Finset.sum_nonneg fun y _ => cTerm_nonneg _)
    linarith
  linarith

end BlockCycleRotation
