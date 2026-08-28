/-
# `D ≤ 1.85`

The paper records `D ≈ 1.85`.  Proving `D ≤ 1.85` means `C ≤ 17/80 = 0.2125`,
and `C = 0.211378…`, so the margin is about half a percent.  The series for `C`
converges harmonically, so a certified bound needs care.

Two obstacles, and how they are handled.

* The rows of `C` are thinned by the coprimality condition: `∑_{a'<a} cTerm`
  averages `0.5966/(ζ(2)a²) ≈ 0.363/a²`, but any *pointwise* row bound must
  cover the primes, where it is `0.5966/a²`.  A row-by-row tail estimate is
  therefore 70% lossy.  Remark 21 avoids this: `ζ(3)·C` is the same sum
  *without* the coprimality condition, whose rows really do behave like
  `0.5966/a²`.

* For that all-pairs sum, `gTerm(a,a') = 1/(2a(a+a')²) + 1/(2a²(a+a'))`, and
  the two pieces are bounded by `1/(4a²)` and `3/(8a²)`: the first telescopes,
  and the second is the reflection `j ↦ a-j`, under which
  `1/(a+j) + 1/(2a-j) ≤ 3a/((a+1)(2a-1))`.  That gives `5/(8a²)` per row,
  within 5% of the truth.

Truncating at `a ≤ 60` (1770 terms) and `ζ(3) ≥ ∑_{d≤50} 1/d³` then closes it.
-/

import BlockCycleRotation.Remark21

namespace BlockCycleRotation

/-! ## The two row sums -/

theorem sum_inv_sq_shift_le {a : ℕ} (ha : 0 < a) :
    ∑ a' ∈ Finset.Ico 1 a, 1 / ((a : ℝ) + (a' : ℝ)) ^ 2 ≤ 1 / (2 * (a : ℝ)) := by
  have haR : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hre : ∑ a' ∈ Finset.Ico 1 a, 1 / ((a : ℝ) + (a' : ℝ)) ^ 2
      = ∑ m ∈ Finset.Ioc a (2 * a - 1), 1 / ((m : ℝ)) ^ 2 := by
    refine Finset.sum_bij' (i := fun a' _ => a + a') (j := fun m _ => m - a) ?_ ?_ ?_ ?_ ?_
    · intro a' h
      rw [Finset.mem_Ico] at h
      rw [Finset.mem_Ioc]
      omega
    · intro m h
      rw [Finset.mem_Ioc] at h
      rw [Finset.mem_Ico]
      omega
    · intro a' h
      rw [Finset.mem_Ico] at h
      omega
    · intro m h
      rw [Finset.mem_Ioc] at h
      omega
    · intro a' h
      rw [Finset.mem_Ico] at h
      push_cast
      ring_nf
  rw [hre]
  have hle : a ≤ 2 * a - 1 := by omega
  have h := sum_inv_sq_Ioc_le ha (2 * a - 1) hle
  have hcast : ((2 * a - 1 : ℕ) : ℝ) = 2 * (a : ℝ) - 1 := by
    have : (1 : ℕ) ≤ 2 * a := by omega
    push_cast [Nat.cast_sub this]
    ring
  rw [hcast] at h
  have hpos : (0 : ℝ) < 2 * (a : ℝ) - 1 := by linarith
  have hstep : 1 / (a : ℝ) - 1 / (2 * (a : ℝ) - 1) ≤ 1 / (2 * (a : ℝ)) := by
    rw [div_sub_div _ _ (by linarith) (by linarith), div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  linarith

/-- **The reflection bound.**  `∑_{j=1}^{a-1} 1/(a+j) ≤ 3/4`, from
`1/(a+j) + 1/(2a-j) ≤ 3a/((a+1)(2a-1))`. -/
theorem sum_inv_shift_le (a : ℕ) :
    ∑ a' ∈ Finset.Ico 1 a, 1 / ((a : ℝ) + (a' : ℝ)) ≤ 3 / 4 := by
  rcases Nat.lt_or_ge a 2 with ha | ha
  · interval_cases a <;> norm_num
  · have haR : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
    -- the reflected sum
    have hre : ∑ a' ∈ Finset.Ico 1 a, 1 / ((a : ℝ) + (a' : ℝ))
        = ∑ a' ∈ Finset.Ico 1 a, 1 / (2 * (a : ℝ) - (a' : ℝ)) := by
      refine Finset.sum_bij' (i := fun j _ => a - j) (j := fun j _ => a - j) ?_ ?_ ?_ ?_ ?_
      · intro j h
        rw [Finset.mem_Ico] at h ⊢
        omega
      · intro j h
        rw [Finset.mem_Ico] at h ⊢
        omega
      · intro j h
        rw [Finset.mem_Ico] at h
        omega
      · intro j h
        rw [Finset.mem_Ico] at h
        omega
      · intro j h
        rw [Finset.mem_Ico] at h
        have hcast : ((a - j : ℕ) : ℝ) = (a : ℝ) - (j : ℝ) := by
          push_cast [Nat.cast_sub (by omega : j ≤ a)]
          ring
        rw [hcast]
        ring_nf
    have hpair : ∀ j ∈ Finset.Ico 1 a,
        1 / ((a : ℝ) + (j : ℝ)) + 1 / (2 * (a : ℝ) - (j : ℝ))
          ≤ 3 * (a : ℝ) / (((a : ℝ) + 1) * (2 * (a : ℝ) - 1)) := by
      intro j h
      rw [Finset.mem_Ico] at h
      have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast h.1
      have hja : (j : ℝ) ≤ (a : ℝ) - 1 := by
        have : (j : ℝ) < (a : ℝ) := by exact_mod_cast h.2
        have hji : j + 1 ≤ a := by omega
        have : ((j + 1 : ℕ) : ℝ) ≤ (a : ℝ) := by exact_mod_cast hji
        push_cast at this
        linarith
      have hd1 : (0 : ℝ) < (a : ℝ) + (j : ℝ) := by linarith
      have hd2 : (0 : ℝ) < 2 * (a : ℝ) - (j : ℝ) := by linarith
      have hd3 : (0 : ℝ) < ((a : ℝ) + 1) * (2 * (a : ℝ) - 1) := by nlinarith
      have hprod : ((a : ℝ) + 1) * (2 * (a : ℝ) - 1)
          ≤ ((a : ℝ) + (j : ℝ)) * (2 * (a : ℝ) - (j : ℝ)) := by
        nlinarith [mul_nonneg (sub_nonneg.2 hj1) (sub_nonneg.2 hja)]
      rw [div_add_div _ _ (ne_of_gt hd1) (ne_of_gt hd2), div_le_div_iff₀ (by positivity) hd3]
      nlinarith
    have hsum : (∑ a' ∈ Finset.Ico 1 a, 1 / ((a : ℝ) + (a' : ℝ)))
        + ∑ a' ∈ Finset.Ico 1 a, 1 / (2 * (a : ℝ) - (a' : ℝ))
        ≤ ((a : ℕ) - 1 : ℕ) * (3 * (a : ℝ) / (((a : ℝ) + 1) * (2 * (a : ℝ) - 1))) := by
      rw [← Finset.sum_add_distrib]
      calc ∑ a' ∈ Finset.Ico 1 a, (1 / ((a : ℝ) + (a' : ℝ)) + 1 / (2 * (a : ℝ) - (a' : ℝ)))
          ≤ ∑ _a' ∈ Finset.Ico 1 a, 3 * (a : ℝ) / (((a : ℝ) + 1) * (2 * (a : ℝ) - 1)) :=
            Finset.sum_le_sum hpair
        _ = ((a - 1 : ℕ) : ℝ) * (3 * (a : ℝ) / (((a : ℝ) + 1) * (2 * (a : ℝ) - 1))) := by
            rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    have hcard : ((a - 1 : ℕ) : ℝ) = (a : ℝ) - 1 := by
      push_cast [Nat.cast_sub (by omega : 1 ≤ a)]
      ring
    rw [hcard] at hsum
    have hfin : ((a : ℝ) - 1) * (3 * (a : ℝ) / (((a : ℝ) + 1) * (2 * (a : ℝ) - 1))) ≤ 3 / 2 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by nlinarith) (by norm_num)]
      nlinarith
    rw [← hre] at hsum
    linarith

/-! ## The row bound for the all-pairs sum -/

/-- **`∑_{a'<a} gTerm ≤ 5/(8a²)`.** -/
theorem gTerm_row_le (a : ℕ) :
    ∑ a' ∈ Finset.range a, gTerm (a, a') ≤ 5 / (8 * (a : ℝ) ^ 2) := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp [gTerm]
  · have haR : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
    have ha0 : (0 : ℝ) < (a : ℝ) := by linarith
    have hrange : Finset.range a = insert 0 (Finset.Ico 1 a) := by
      ext k
      rw [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
      omega
    have h0 : gTerm (a, 0) = 0 := by simp [gTerm]
    rw [hrange, Finset.sum_insert (by simp), h0, zero_add]
    have hsplit : ∀ a' ∈ Finset.Ico 1 a, gTerm (a, a')
        = 1 / (2 * (a : ℝ)) * (1 / ((a : ℝ) + (a' : ℝ)) ^ 2)
          + 1 / (2 * (a : ℝ) ^ 2) * (1 / ((a : ℝ) + (a' : ℝ))) := by
      intro a' h
      rw [Finset.mem_Ico] at h
      unfold gTerm
      rw [if_pos ⟨h.1, h.2⟩]
      have haa : (0 : ℝ) < (a : ℝ) + (a' : ℝ) := by positivity
      field_simp
      ring
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have hb1 : 1 / (2 * (a : ℝ)) * (∑ a' ∈ Finset.Ico 1 a, 1 / ((a : ℝ) + (a' : ℝ)) ^ 2)
        ≤ 1 / (2 * (a : ℝ)) * (1 / (2 * (a : ℝ))) :=
      mul_le_mul_of_nonneg_left (sum_inv_sq_shift_le ha) (by positivity)
    have hb2 : 1 / (2 * (a : ℝ) ^ 2) * (∑ a' ∈ Finset.Ico 1 a, 1 / ((a : ℝ) + (a' : ℝ)))
        ≤ 1 / (2 * (a : ℝ) ^ 2) * (3 / 4) :=
      mul_le_mul_of_nonneg_left (sum_inv_shift_le a) (by positivity)
    have harith : 1 / (2 * (a : ℝ)) * (1 / (2 * (a : ℝ))) + 1 / (2 * (a : ℝ) ^ 2) * (3 / 4)
        = 5 / (8 * (a : ℝ) ^ 2) := by
      field_simp
      ring
    linarith

/-! ## The tail -/

theorem gTerm_row_support (a a' : ℕ) (h : a' ∉ Finset.range a) : gTerm (a, a') = 0 := by
  simp only [Finset.mem_range, not_lt] at h
  unfold gTerm
  rw [if_neg]
  rintro ⟨-, h2⟩
  omega

theorem gTerm_row_summable (a : ℕ) : Summable (fun a' => gTerm (a, a')) :=
  summable_of_ne_finset_zero (s := Finset.range a) (gTerm_row_support a)

theorem gTerm_eq_tsum_finRows :
    ∑' p, gTerm p = ∑' a : ℕ, ∑ a' ∈ Finset.range a, gTerm (a, a') := by
  rw [gTerm_summable.tsum_prod]
  exact tsum_congr fun a => tsum_eq_sum (gTerm_row_support a)

/-- **Truncating the all-pairs sum at `a ≤ N` loses at most `5/(8N)`.** -/
theorem tsum_gTerm_le_partial {N : ℕ} (hN : 0 < N) :
    ∑' p, gTerm p
      ≤ (∑ a ∈ Finset.range (N + 1), ∑ a' ∈ Finset.range a, gTerm (a, a'))
        + 5 / (8 * (N : ℝ)) := by
  rw [gTerm_eq_tsum_finRows]
  refine Real.tsum_le_of_sum_le
    (fun a => Finset.sum_nonneg fun a' _ => gTerm_nonneg _) fun s => ?_
  classical
  have hsplit : ∑ a ∈ s, (∑ a' ∈ Finset.range a, gTerm (a, a'))
      = (∑ a ∈ s.filter (fun a => a ≤ N), ∑ a' ∈ Finset.range a, gTerm (a, a'))
        + ∑ a ∈ s.filter (fun a => ¬ a ≤ N), ∑ a' ∈ Finset.range a, gTerm (a, a') :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hlow : (∑ a ∈ s.filter (fun a => a ≤ N), ∑ a' ∈ Finset.range a, gTerm (a, a'))
      ≤ ∑ a ∈ Finset.range (N + 1), ∑ a' ∈ Finset.range a, gTerm (a, a') := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_
      (fun a _ _ => Finset.sum_nonneg fun a' _ => gTerm_nonneg _)
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_range] at ha ⊢
    omega
  have hhigh : (∑ a ∈ s.filter (fun a => ¬ a ≤ N), ∑ a' ∈ Finset.range a, gTerm (a, a'))
      ≤ 5 / (8 * (N : ℝ)) := by
    have h1 : (∑ a ∈ s.filter (fun a => ¬ a ≤ N), ∑ a' ∈ Finset.range a, gTerm (a, a'))
        ≤ ∑ a ∈ s.filter (fun a => ¬ a ≤ N), 5 / (8 * (a : ℝ) ^ 2) :=
      Finset.sum_le_sum fun a _ => gTerm_row_le a
    have h2 : (∑ a ∈ s.filter (fun a => ¬ a ≤ N), 5 / (8 * (a : ℝ) ^ 2))
        = (5 / 8) * ∑ a ∈ s.filter (fun a => ¬ a ≤ N), 1 / ((a : ℝ) ^ 2) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [div_mul_eq_mul_div, mul_one_div]
      ring_nf
    have h3 : (∑ a ∈ s.filter (fun a => ¬ a ≤ N), 1 / ((a : ℝ) ^ 2)) ≤ 1 / (N : ℝ) := by
      refine sum_inv_sq_tail_le hN _ fun a ha => ?_
      simp only [Finset.mem_filter] at ha
      omega
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    rw [h2] at h1
    have heq : (5 / 8 : ℝ) * (1 / (N : ℝ)) = 5 / (8 * (N : ℝ)) := by field_simp
    nlinarith [h1, h3]
  rw [hsplit]
  linarith

/-! ## The numerical bounds -/

set_option maxHeartbeats 10000000 in
-- 1770 rational terms; about 40 seconds.
/-- The all-pairs sum truncated at `a ≤ 60`. -/
theorem gTerm_partial_le :
    (∑ a ∈ Finset.range 61, ∑ a' ∈ Finset.range a, gTerm (a, a')) ≤ 2447 / 10000 := by
  norm_num [gTerm, Finset.sum_range_succ]

set_option maxHeartbeats 1000000 in
/-- `ζ(3) ≥ ∑_{d ≤ 50} 1/d³ ≥ 1.2018`. -/
theorem zeta3_ge : (6009 : ℝ) / 5000 ≤ zeta3 := by
  have h : ∑ d ∈ Finset.range 50, uTerm d ≤ zeta3 := by
    rw [← tsum_uTerm]
    exact uTerm_summable.sum_le_tsum _ (fun d _ => (uTerm_pos d).le)
  refine le_trans ?_ h
  norm_num [uTerm, Finset.sum_range_succ]

/-- **`C ≤ 17/80 = 0.2125`.** -/
theorem cConst_le_seventeen_eightieths : cConst ≤ 17 / 80 := by
  have hG : zeta3 * cConst = ∑' p, gTerm p := by
    rw [zeta3_mul_cConst, tsum_gTerm]
  have htail := tsum_gTerm_le_partial (N := 60) (by norm_num)
  have hB : zeta3 * cConst ≤ 2447 / 10000 + 5 / (8 * (60 : ℝ)) := by
    rw [hG]
    linarith [gTerm_partial_le]
  have hlow : (6009 / 5000 : ℝ) * cConst ≤ zeta3 * cConst :=
    mul_le_mul_of_nonneg_right zeta3_ge cConst_nonneg
  have hkey : (6009 / 5000 : ℝ) * cConst ≤ (6009 / 5000 : ℝ) * (17 / 80) := by
    refine le_trans hlow (le_trans hB ?_)
    norm_num
  exact le_of_mul_le_mul_left hkey (by norm_num)

/-- **`D ≤ 1.85`**, the value quoted in the paper. -/
theorem dConst_le_185 : dConst ≤ 1.85 := by
  rw [dConst]
  have h := cConst_le_seventeen_eightieths
  norm_num
  linarith

/-! ## Lower bounds for the row sums

The same reflection `j ↦ a-j`, now bounding the products from *above*:
`(a+j)(2a-j) ≤ (9/4)a²`, because the difference is `(j - a/2)²`.  That gives
`1/(a+j) + 1/(2a-j) ≥ 4/(3a)` and, with `1/x² + 1/y² ≥ 2/(xy)`,
`1/(a+j)² + 1/(2a-j)² ≥ 8/(9a²)`. -/

theorem sum_shift_reflect (a : ℕ) (f : ℝ → ℝ) :
    ∑ j ∈ Finset.Ico 1 a, f ((a : ℝ) + (j : ℝ))
      = ∑ j ∈ Finset.Ico 1 a, f (2 * (a : ℝ) - (j : ℝ)) := by
  refine Finset.sum_bij' (i := fun j _ => a - j) (j := fun j _ => a - j) ?_ ?_ ?_ ?_ ?_
  · intro j h; rw [Finset.mem_Ico] at h ⊢; omega
  · intro j h; rw [Finset.mem_Ico] at h ⊢; omega
  · intro j h; rw [Finset.mem_Ico] at h; omega
  · intro j h; rw [Finset.mem_Ico] at h; omega
  · intro j h
    rw [Finset.mem_Ico] at h
    have hcast : ((a - j : ℕ) : ℝ) = (a : ℝ) - (j : ℝ) := by
      push_cast [Nat.cast_sub (by omega : j ≤ a)]
      ring
    rw [hcast]
    congr 1
    ring

theorem prod_shift_le {a : ℕ} {j : ℕ} :
    ((a : ℝ) + (j : ℝ)) * (2 * (a : ℝ) - (j : ℝ)) ≤ 9 / 4 * (a : ℝ) ^ 2 := by
  nlinarith [sq_nonneg ((j : ℝ) - (a : ℝ) / 2)]

theorem sum_inv_shift_ge {a : ℕ} (ha : 1 ≤ a) :
    2 * ((a : ℝ) - 1) / (3 * (a : ℝ)) ≤ ∑ j ∈ Finset.Ico 1 a, 1 / ((a : ℝ) + (j : ℝ)) := by
  have haR : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hpair : ∀ j ∈ Finset.Ico 1 a,
      4 / (3 * (a : ℝ)) ≤ 1 / ((a : ℝ) + (j : ℝ)) + 1 / (2 * (a : ℝ) - (j : ℝ)) := by
    intro j h
    rw [Finset.mem_Ico] at h
    have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast h.1
    have hja : (j : ℝ) < (a : ℝ) := by exact_mod_cast h.2
    have hd1 : (0 : ℝ) < (a : ℝ) + (j : ℝ) := by linarith
    have hd2 : (0 : ℝ) < 2 * (a : ℝ) - (j : ℝ) := by linarith
    rw [div_add_div _ _ (ne_of_gt hd1) (ne_of_gt hd2), div_le_div_iff₀ (by positivity)
      (by positivity)]
    nlinarith [prod_shift_le (a := a) (j := j), hd1, hd2]
  have hdouble : (∑ j ∈ Finset.Ico 1 a, 1 / ((a : ℝ) + (j : ℝ)))
      + ∑ j ∈ Finset.Ico 1 a, 1 / (2 * (a : ℝ) - (j : ℝ))
      ≥ ((a : ℝ) - 1) * (4 / (3 * (a : ℝ))) := by
    rw [← Finset.sum_add_distrib]
    have hcard : ((a - 1 : ℕ) : ℝ) = (a : ℝ) - 1 := by
      push_cast [Nat.cast_sub ha]
      ring
    calc ((a : ℝ) - 1) * (4 / (3 * (a : ℝ)))
        = ∑ _j ∈ Finset.Ico 1 a, 4 / (3 * (a : ℝ)) := by
          rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, hcard]
      _ ≤ ∑ j ∈ Finset.Ico 1 a, (1 / ((a : ℝ) + (j : ℝ)) + 1 / (2 * (a : ℝ) - (j : ℝ))) :=
          Finset.sum_le_sum hpair
  rw [← sum_shift_reflect a (fun x => 1 / x)] at hdouble
  have ha0 : (0 : ℝ) < (a : ℝ) := by linarith
  have hrw : ((a : ℝ) - 1) * (4 / (3 * (a : ℝ))) = 2 * (2 * ((a : ℝ) - 1) / (3 * (a : ℝ))) := by
    field_simp
    ring
  rw [hrw] at hdouble
  linarith

theorem sum_inv_sq_shift_ge {a : ℕ} (ha : 1 ≤ a) :
    4 * ((a : ℝ) - 1) / (9 * (a : ℝ) ^ 2)
      ≤ ∑ j ∈ Finset.Ico 1 a, 1 / ((a : ℝ) + (j : ℝ)) ^ 2 := by
  have haR : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hpair : ∀ j ∈ Finset.Ico 1 a,
      8 / (9 * (a : ℝ) ^ 2)
        ≤ 1 / ((a : ℝ) + (j : ℝ)) ^ 2 + 1 / (2 * (a : ℝ) - (j : ℝ)) ^ 2 := by
    intro j h
    rw [Finset.mem_Ico] at h
    have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast h.1
    have hja : (j : ℝ) < (a : ℝ) := by exact_mod_cast h.2
    have hd1 : (0 : ℝ) < (a : ℝ) + (j : ℝ) := by linarith
    have hd2 : (0 : ℝ) < 2 * (a : ℝ) - (j : ℝ) := by linarith
    have hprod := prod_shift_le (a := a) (j := j)
    have hamgm : 2 / (((a : ℝ) + (j : ℝ)) * (2 * (a : ℝ) - (j : ℝ)))
        ≤ 1 / ((a : ℝ) + (j : ℝ)) ^ 2 + 1 / (2 * (a : ℝ) - (j : ℝ)) ^ 2 := by
      rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
        (by positivity)]
      nlinarith [mul_nonneg (mul_pos hd1 hd2).le
        (sq_nonneg (((a : ℝ) + (j : ℝ)) - (2 * (a : ℝ) - (j : ℝ))))]
    have hstep : 8 / (9 * (a : ℝ) ^ 2)
        ≤ 2 / (((a : ℝ) + (j : ℝ)) * (2 * (a : ℝ) - (j : ℝ))) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hprod]
    linarith
  have hdouble : (∑ j ∈ Finset.Ico 1 a, 1 / ((a : ℝ) + (j : ℝ)) ^ 2)
      + ∑ j ∈ Finset.Ico 1 a, 1 / (2 * (a : ℝ) - (j : ℝ)) ^ 2
      ≥ ((a : ℝ) - 1) * (8 / (9 * (a : ℝ) ^ 2)) := by
    rw [← Finset.sum_add_distrib]
    have hcard : ((a - 1 : ℕ) : ℝ) = (a : ℝ) - 1 := by
      push_cast [Nat.cast_sub ha]
      ring
    calc ((a : ℝ) - 1) * (8 / (9 * (a : ℝ) ^ 2))
        = ∑ _j ∈ Finset.Ico 1 a, 8 / (9 * (a : ℝ) ^ 2) := by
          rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, hcard]
      _ ≤ ∑ j ∈ Finset.Ico 1 a,
            (1 / ((a : ℝ) + (j : ℝ)) ^ 2 + 1 / (2 * (a : ℝ) - (j : ℝ)) ^ 2) :=
          Finset.sum_le_sum hpair
  rw [← sum_shift_reflect a (fun x => 1 / x ^ 2)] at hdouble
  have ha0 : (0 : ℝ) < (a : ℝ) := by linarith
  have hrw : ((a : ℝ) - 1) * (8 / (9 * (a : ℝ) ^ 2))
      = 2 * (4 * ((a : ℝ) - 1) / (9 * (a : ℝ) ^ 2)) := by
    field_simp
    ring
  rw [hrw] at hdouble
  linarith

/-! ## A matching lower bound

`ζ(3) ≤ ∑_{d≤50} 1/d³ + 1/2550`, using `1/m³ ≤ (1/51)·1/m²` past `m = 50` and
the tail bound for `∑ 1/m²`.  With the same truncation of the all-pairs sum
from below this gives `1.81 ≤ D`. -/

set_option maxHeartbeats 10000000 in
-- 1770 rational terms again.
theorem gTerm_partial_ge :
    (2443 : ℝ) / 10000 ≤ ∑ a ∈ Finset.range 61, ∑ a' ∈ Finset.range a, gTerm (a, a') := by
  norm_num [gTerm, Finset.sum_range_succ]

theorem uTerm_tail_le : ∑' j : ℕ, uTerm (j + 50) ≤ 1 / 2550 := by
  have hsum : Summable (fun j : ℕ => uTerm (j + 50)) := (summable_nat_add_iff 50).2 uTerm_summable
  have hg : Summable (fun j : ℕ => (1 / 51 : ℝ) * (1 / ((50 : ℝ) + (j : ℝ) + 1) ^ 2)) := by
    have h : Summable (fun j : ℕ => 1 / ((50 : ℝ) + (j : ℝ) + 1) ^ 2) := by
      have h0 : Summable (fun m : ℕ => 1 / (m : ℝ) ^ 2) := by
        rw [Real.summable_one_div_nat_pow]; norm_num
      refine ((summable_nat_add_iff 51).2 h0).congr fun j => ?_
      push_cast
      ring_nf
    exact h.mul_left _
  have hle : ∀ j : ℕ, uTerm (j + 50) ≤ (1 / 51 : ℝ) * (1 / ((50 : ℝ) + (j : ℝ) + 1) ^ 2) := by
    intro j
    unfold uTerm
    have hj : (0 : ℝ) ≤ (j : ℝ) := by positivity
    push_cast
    have hrw : (1 / 51 : ℝ) * (1 / ((50 : ℝ) + (j : ℝ) + 1) ^ 2)
        = 1 / (51 * ((50 : ℝ) + (j : ℝ) + 1) ^ 2) := by field_simp
    rw [hrw, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hj, sq_nonneg ((j : ℝ) + 51), mul_nonneg hj (sq_nonneg ((j : ℝ) + 51))]
  calc ∑' j : ℕ, uTerm (j + 50)
      ≤ ∑' j : ℕ, (1 / 51 : ℝ) * (1 / ((50 : ℝ) + (j : ℝ) + 1) ^ 2) :=
        hsum.tsum_le_tsum hle hg
    _ = (1 / 51 : ℝ) * ∑' j : ℕ, 1 / ((50 : ℝ) + (j : ℝ) + 1) ^ 2 := tsum_mul_left
    _ ≤ (1 / 51 : ℝ) * (1 / (50 : ℝ)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        have h := tsum_tail_inv_sq (n := 50) (by norm_num)
        push_cast at h ⊢
        exact h
    _ = 1 / 2550 := by norm_num

set_option maxHeartbeats 1000000 in
-- 50 rational terms of the series for `ζ(3)`.
/-- `ζ(3) ≤ 1.2023`. -/
theorem zeta3_le : zeta3 ≤ 12023 / 10000 := by
  have hsplit : (∑ d ∈ Finset.range 50, uTerm d) + ∑' j : ℕ, uTerm (j + 50) = zeta3 := by
    rw [← tsum_uTerm]
    exact uTerm_summable.sum_add_tsum_nat_add 50
  have h1 : ∑ d ∈ Finset.range 50, uTerm d ≤ 12019 / 10000 := by
    norm_num [uTerm, Finset.sum_range_succ]
  linarith [uTerm_tail_le]

/-- **`C ≥ 0.2025`.** -/
theorem cConst_ge : (2025 : ℝ) / 10000 ≤ cConst := by
  have hnn : (0 : ℕ × ℕ → ℝ) ≤ gTerm := fun p => gTerm_nonneg p
  have hrows := (summable_prod_of_nonneg hnn).1 gTerm_summable
  have hrowsum : Summable (fun a : ℕ => ∑ a' ∈ Finset.range a, gTerm (a, a')) := by
    refine hrows.2.congr fun a => ?_
    exact tsum_eq_sum (gTerm_row_support a)
  have hpartial : (∑ a ∈ Finset.range 61, ∑ a' ∈ Finset.range a, gTerm (a, a'))
      ≤ ∑' p, gTerm p := by
    rw [gTerm_eq_tsum_finRows]
    exact hrowsum.sum_le_tsum _ (fun a _ => Finset.sum_nonneg fun a' _ => gTerm_nonneg _)
  have hG : zeta3 * cConst = ∑' p, gTerm p := by
    rw [zeta3_mul_cConst, tsum_gTerm]
  have hlow : (2443 : ℝ) / 10000 ≤ zeta3 * cConst := by
    rw [hG]
    linarith [gTerm_partial_ge]
  have hup : zeta3 * cConst ≤ (12023 / 10000 : ℝ) * cConst :=
    mul_le_mul_of_nonneg_right zeta3_le cConst_nonneg
  nlinarith [hlow, hup]

/-! ## Sharpening the lower bound to `1.84`

Dropping the tail entirely costs `0.5966/N`; recovering most of it needs a row
bound from below.  The reflection gives `∑_{a'<a} gTerm ≥ 5(a-1)/(9a³)`, which
for `a ≥ 61` is at least `0.54/a²`, and `∑_{a>60} 1/a² ≥ 1/61` telescopes. -/

theorem gTerm_row_ge {a : ℕ} (ha : 61 ≤ a) :
    (54 / 100 : ℝ) / (a : ℝ) ^ 2 ≤ ∑ a' ∈ Finset.range a, gTerm (a, a') := by
  have ha1 : 1 ≤ a := by omega
  have haR : (61 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have ha0 : (0 : ℝ) < (a : ℝ) := by linarith
  have hrange : Finset.range a = insert 0 (Finset.Ico 1 a) := by
    ext k
    rw [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
    omega
  have h0 : gTerm (a, 0) = 0 := by simp [gTerm]
  rw [hrange, Finset.sum_insert (by simp), h0, zero_add]
  have hsplit : ∀ a' ∈ Finset.Ico 1 a, gTerm (a, a')
      = 1 / (2 * (a : ℝ)) * (1 / ((a : ℝ) + (a' : ℝ)) ^ 2)
        + 1 / (2 * (a : ℝ) ^ 2) * (1 / ((a : ℝ) + (a' : ℝ))) := by
    intro a' h
    rw [Finset.mem_Ico] at h
    unfold gTerm
    rw [if_pos ⟨h.1, h.2⟩]
    have haa : (0 : ℝ) < (a : ℝ) + (a' : ℝ) := by positivity
    field_simp
    ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hb1 : 1 / (2 * (a : ℝ)) * (4 * ((a : ℝ) - 1) / (9 * (a : ℝ) ^ 2))
      ≤ 1 / (2 * (a : ℝ)) * (∑ a' ∈ Finset.Ico 1 a, 1 / ((a : ℝ) + (a' : ℝ)) ^ 2) :=
    mul_le_mul_of_nonneg_left (sum_inv_sq_shift_ge ha1) (by positivity)
  have hb2 : 1 / (2 * (a : ℝ) ^ 2) * (2 * ((a : ℝ) - 1) / (3 * (a : ℝ)))
      ≤ 1 / (2 * (a : ℝ) ^ 2) * (∑ a' ∈ Finset.Ico 1 a, 1 / ((a : ℝ) + (a' : ℝ))) :=
    mul_le_mul_of_nonneg_left (sum_inv_shift_ge ha1) (by positivity)
  have harith : (54 / 100 : ℝ) / (a : ℝ) ^ 2
      ≤ 1 / (2 * (a : ℝ)) * (4 * ((a : ℝ) - 1) / (9 * (a : ℝ) ^ 2))
        + 1 / (2 * (a : ℝ) ^ 2) * (2 * ((a : ℝ) - 1) / (3 * (a : ℝ))) := by
    rw [div_le_iff₀ (by positivity)]
    have hexp : (1 / (2 * (a : ℝ)) * (4 * ((a : ℝ) - 1) / (9 * (a : ℝ) ^ 2))
        + 1 / (2 * (a : ℝ) ^ 2) * (2 * ((a : ℝ) - 1) / (3 * (a : ℝ)))) * (a : ℝ) ^ 2
        = 5 * ((a : ℝ) - 1) / (9 * (a : ℝ)) := by
      field_simp
      ring
    rw [hexp, le_div_iff₀ (by positivity)]
    linarith
  linarith

/-! ### The telescoping tail of `∑ 1/a²` -/

theorem tsum_telescope_inv {K : ℕ} (hK : 0 < K) :
    ∑' j : ℕ, (1 / ((j : ℝ) + (K : ℝ)) - 1 / ((j : ℝ) + (K : ℝ) + 1)) = 1 / (K : ℝ) := by
  have hKR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hnn : ∀ j : ℕ, 0 ≤ 1 / ((j : ℝ) + (K : ℝ)) - 1 / ((j : ℝ) + (K : ℝ) + 1) := by
    intro j
    have h1 : (0 : ℝ) < (j : ℝ) + (K : ℝ) := by positivity
    have := one_div_le_one_div_of_le h1 (by linarith : (j : ℝ) + (K : ℝ) ≤ (j : ℝ) + (K : ℝ) + 1)
    linarith
  have hle : ∀ j : ℕ, 1 / ((j : ℝ) + (K : ℝ)) - 1 / ((j : ℝ) + (K : ℝ) + 1)
      ≤ 1 / ((j : ℝ) + (K : ℝ)) ^ 2 := by
    intro j
    have h1 : (0 : ℝ) < (j : ℝ) + (K : ℝ) := by positivity
    have hrw : 1 / ((j : ℝ) + (K : ℝ)) - 1 / ((j : ℝ) + (K : ℝ) + 1)
        = 1 / (((j : ℝ) + (K : ℝ)) * ((j : ℝ) + (K : ℝ) + 1)) := by
      field_simp
      ring
    rw [hrw]
    refine one_div_le_one_div_of_le (by positivity) ?_
    nlinarith
  have hgs : Summable (fun j : ℕ => 1 / ((j : ℝ) + (K : ℝ)) ^ 2) := by
    have h0 : Summable (fun m : ℕ => 1 / (m : ℝ) ^ 2) := by
      rw [Real.summable_one_div_nat_pow]; norm_num
    refine ((summable_nat_add_iff K).2 h0).congr fun j => ?_
    push_cast
    ring_nf
  have hs : Summable (fun j : ℕ => 1 / ((j : ℝ) + (K : ℝ)) - 1 / ((j : ℝ) + (K : ℝ) + 1)) :=
    Summable.of_nonneg_of_le hnn hle hgs
  refine (hs.hasSum_iff_tendsto_nat.2 ?_).tsum_eq
  have hpart : ∀ N : ℕ, ∑ j ∈ Finset.range N,
      (1 / ((j : ℝ) + (K : ℝ)) - 1 / ((j : ℝ) + (K : ℝ) + 1))
      = 1 / (K : ℝ) - 1 / ((N : ℝ) + (K : ℝ)) := by
    intro N
    induction N with
    | zero => simp
    | succ M ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring
  have hzero : Filter.Tendsto (fun N : ℕ => 1 / ((N : ℝ) + (K : ℝ))) Filter.atTop (nhds 0) := by
    have hK1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
    refine squeeze_zero (fun N => by positivity) (fun N => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hlim : Filter.Tendsto (fun N : ℕ => 1 / (K : ℝ) - 1 / ((N : ℝ) + (K : ℝ)))
      Filter.atTop (nhds (1 / (K : ℝ))) := by
    have h := Filter.Tendsto.sub (tendsto_const_nhds (x := 1 / (K : ℝ))) hzero
    rw [sub_zero] at h
    exact h
  exact hlim.congr (fun N => (hpart N).symm)

theorem tsum_inv_sq_ge {K : ℕ} (hK : 0 < K) :
    (1 : ℝ) / (K : ℝ) ≤ ∑' j : ℕ, 1 / ((j : ℝ) + (K : ℝ)) ^ 2 := by
  have hgs : Summable (fun j : ℕ => 1 / ((j : ℝ) + (K : ℝ)) ^ 2) := by
    have h0 : Summable (fun m : ℕ => 1 / (m : ℝ) ^ 2) := by
      rw [Real.summable_one_div_nat_pow]; norm_num
    refine ((summable_nat_add_iff K).2 h0).congr fun j => ?_
    push_cast
    ring_nf
  have hnn : ∀ j : ℕ, 0 ≤ 1 / ((j : ℝ) + (K : ℝ)) - 1 / ((j : ℝ) + (K : ℝ) + 1) := by
    intro j
    have h1 : (0 : ℝ) < (j : ℝ) + (K : ℝ) := by
      have : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
      positivity
    have := one_div_le_one_div_of_le h1 (by linarith : (j : ℝ) + (K : ℝ) ≤ (j : ℝ) + (K : ℝ) + 1)
    linarith
  have hle : ∀ j : ℕ, 1 / ((j : ℝ) + (K : ℝ)) - 1 / ((j : ℝ) + (K : ℝ) + 1)
      ≤ 1 / ((j : ℝ) + (K : ℝ)) ^ 2 := by
    intro j
    have h1 : (0 : ℝ) < (j : ℝ) + (K : ℝ) := by
      have : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
      positivity
    have hrw : 1 / ((j : ℝ) + (K : ℝ)) - 1 / ((j : ℝ) + (K : ℝ) + 1)
        = 1 / (((j : ℝ) + (K : ℝ)) * ((j : ℝ) + (K : ℝ) + 1)) := by
      field_simp
      ring
    rw [hrw]
    refine one_div_le_one_div_of_le (by positivity) ?_
    nlinarith
  have hs : Summable (fun j : ℕ => 1 / ((j : ℝ) + (K : ℝ)) - 1 / ((j : ℝ) + (K : ℝ) + 1)) :=
    Summable.of_nonneg_of_le hnn hle hgs
  calc (1 : ℝ) / (K : ℝ)
      = ∑' j : ℕ, (1 / ((j : ℝ) + (K : ℝ)) - 1 / ((j : ℝ) + (K : ℝ) + 1)) :=
        (tsum_telescope_inv hK).symm
    _ ≤ ∑' j : ℕ, 1 / ((j : ℝ) + (K : ℝ)) ^ 2 := hs.tsum_le_tsum hle hgs

/-! ### The tail from below, and `D ≥ 1.84` -/

set_option maxHeartbeats 800000 in
-- Several tsum manipulations chained.
theorem tsum_gTerm_ge :
    (∑ a ∈ Finset.range 61, ∑ a' ∈ Finset.range a, gTerm (a, a')) + (54 / 100) * (1 / 61)
      ≤ ∑' p, gTerm p := by
  have hnn : (0 : ℕ × ℕ → ℝ) ≤ gTerm := fun p => gTerm_nonneg p
  have hrows := (summable_prod_of_nonneg hnn).1 gTerm_summable
  have hrowsum : Summable (fun a : ℕ => ∑ a' ∈ Finset.range a, gTerm (a, a')) := by
    refine hrows.2.congr fun a => ?_
    exact tsum_eq_sum (gTerm_row_support a)
  have hshift : Summable (fun j : ℕ => ∑ a' ∈ Finset.range (j + 61), gTerm (j + 61, a')) :=
    (summable_nat_add_iff (f := fun a : ℕ => ∑ a' ∈ Finset.range a, gTerm (a, a')) 61).2 hrowsum
  have hgs : Summable (fun j : ℕ => (54 / 100 : ℝ) * (1 / ((j : ℝ) + 61) ^ 2)) := by
    have h0 : Summable (fun m : ℕ => 1 / (m : ℝ) ^ 2) := by
      rw [Real.summable_one_div_nat_pow]; norm_num
    have h1 : Summable (fun j : ℕ => 1 / ((j : ℝ) + 61) ^ 2) := by
      refine ((summable_nat_add_iff 61).2 h0).congr fun j => ?_
      push_cast
      ring_nf
    exact h1.mul_left _
  have hsplit : (∑ a ∈ Finset.range 61, ∑ a' ∈ Finset.range a, gTerm (a, a'))
      + ∑' j : ℕ, (∑ a' ∈ Finset.range (j + 61), gTerm (j + 61, a'))
      = ∑' p, gTerm p := by
    rw [gTerm_eq_tsum_finRows]
    exact hrowsum.sum_add_tsum_nat_add 61
  have htail : (54 / 100 : ℝ) * (1 / 61)
      ≤ ∑' j : ℕ, (∑ a' ∈ Finset.range (j + 61), gTerm (j + 61, a')) := by
    have hterm : ∀ j : ℕ, (54 / 100 : ℝ) * (1 / ((j : ℝ) + 61) ^ 2)
        ≤ ∑ a' ∈ Finset.range (j + 61), gTerm (j + 61, a') := by
      intro j
      have h := gTerm_row_ge (a := j + 61) (by omega)
      have hcast : ((j + 61 : ℕ) : ℝ) = (j : ℝ) + 61 := by push_cast; ring
      rw [hcast] at h
      calc (54 / 100 : ℝ) * (1 / ((j : ℝ) + 61) ^ 2)
          = (54 / 100 : ℝ) / ((j : ℝ) + 61) ^ 2 := by ring
        _ ≤ _ := h
    have hK := tsum_inv_sq_ge (K := 61) (by norm_num)
    have hcast61 : ((61 : ℕ) : ℝ) = 61 := by norm_num
    rw [hcast61] at hK
    have h1 : (54 / 100 : ℝ) * (1 / 61) ≤ (54 / 100 : ℝ) * ∑' j : ℕ, 1 / ((j : ℝ) + 61) ^ 2 :=
      mul_le_mul_of_nonneg_left hK (by norm_num)
    have h2 : (54 / 100 : ℝ) * ∑' j : ℕ, 1 / ((j : ℝ) + 61) ^ 2
        = ∑' j : ℕ, (54 / 100 : ℝ) * (1 / ((j : ℝ) + 61) ^ 2) := tsum_mul_left.symm
    rw [h2] at h1
    exact le_trans h1 (hgs.tsum_le_tsum hterm hshift)
  rw [← hsplit]
  exact add_le_add_right htail _

/-- **`C ≥ 0.21`.** -/
theorem cConst_ge_21_100 : (21 : ℝ) / 100 ≤ cConst := by
  have hG : zeta3 * cConst = ∑' p, gTerm p := by
    rw [zeta3_mul_cConst, tsum_gTerm]
  have hlow : (2443 : ℝ) / 10000 + (54 / 100) * (1 / 61) ≤ zeta3 * cConst := by
    rw [hG]
    linarith [gTerm_partial_ge, tsum_gTerm_ge]
  have hup : zeta3 * cConst ≤ (12023 / 10000 : ℝ) * cConst :=
    mul_le_mul_of_nonneg_right zeta3_le cConst_nonneg
  nlinarith [hlow, hup]

/-- **`1.84 ≤ D`.** -/
theorem dConst_ge_184 : (1.84 : ℝ) ≤ dConst := by
  rw [dConst]
  have h := cConst_ge_21_100
  norm_num
  linarith

/-- **The paper's `D ≈ 1.85`, certified:** `1.84 ≤ D ≤ 1.85`. -/
theorem dConst_enclosure : (1.84 : ℝ) ≤ dConst ∧ dConst ≤ 1.85 :=
  ⟨dConst_ge_184, dConst_le_185⟩

end BlockCycleRotation
