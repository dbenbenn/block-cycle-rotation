/-
# Exponential sums at roots of unity

Section 4 of Blomer--Bux removes a congruence condition `b ≡ c mod a` by
expanding it in additive characters `b ↦ e(mb/a)`, and then bounds each
resulting sum for `m ≢ 0`.  This file supplies the quantitative input for that
step: at a nontrivial `a`-th root of unity the chord length is bounded below by

  `‖e(2πm/a) - 1‖ ≥ 4 · min(m, a-m) / a`,

so the geometric sums of `ExpSum.lean` obey

  `‖∑_{B ≤ j < T} e(2πmj/a)‖ ≤ a / (2 · min(m, a-m))`.

Summing `1 / min(m, a-m)` over `0 < m < a` is what produces the `log a` in the
paper's Lemma 18.
-/

import BlockCycleRotation.ExpSum

namespace BlockCycleRotation

open Real Finset

/-- **Jordan's inequality at a root of unity.**  For `0 < m < a`,
`2 · min(m, a-m) / a ≤ sin (π m / a)`.

The two cases are `m ≤ a/2`, where Jordan applies directly, and `m > a/2`, where
it applies after reflecting via `sin (π - x) = sin x`. -/
theorem two_mul_min_div_le_sin {a m : ℕ} (h0 : 0 < m) (hma : m < a) :
    2 * ((min m (a - m) : ℕ) : ℝ) / (a : ℝ) ≤ Real.sin (π * m / a) := by
  have hapos : 0 < a := lt_trans h0 hma
  have ha : (0 : ℝ) < a := by exact_mod_cast hapos
  have hpi := Real.pi_pos
  have hmle : (m : ℝ) ≤ (a : ℝ) := by exact_mod_cast hma.le
  rcases le_or_gt (2 * m) a with hcase | hcase
  · -- `min = m`, and `π m / a ≤ π / 2`
    have hmin : min m (a - m) = m := by omega
    rw [hmin]
    have hx0 : 0 ≤ π * m / a := by positivity
    have hx1 : π * (m : ℝ) / a ≤ π / 2 := by
      rw [div_le_div_iff₀ ha (by norm_num)]
      have h2m : (2 : ℝ) * m ≤ a := by exact_mod_cast hcase
      nlinarith
    have hj := Real.mul_le_sin hx0 hx1
    have hrw : 2 / π * (π * (m : ℝ) / a) = 2 * (m : ℝ) / a := by field_simp
    rw [hrw] at hj
    exact hj
  · -- `min = a - m`, and reflect
    have hmin : min m (a - m) = a - m := by omega
    have hsub : ((a - m : ℕ) : ℝ) = (a : ℝ) - m := by rw [Nat.cast_sub hma.le]
    have hd : (0 : ℝ) ≤ (a : ℝ) - m := by linarith
    rw [hmin, hsub]
    have hkey : π * (m : ℝ) / a = π - π * ((a : ℝ) - m) / a := by
      field_simp
      ring
    rw [hkey, Real.sin_pi_sub]
    have hx0 : 0 ≤ π * ((a : ℝ) - m) / a := div_nonneg (mul_nonneg hpi.le hd) ha.le
    have hx1 : π * ((a : ℝ) - m) / a ≤ π / 2 := by
      rw [div_le_div_iff₀ ha (by norm_num)]
      have h2m : (a : ℝ) < 2 * m := by exact_mod_cast hcase
      nlinarith
    have hj := Real.mul_le_sin hx0 hx1
    have hrw : 2 / π * (π * ((a : ℝ) - m) / a) = 2 * ((a : ℝ) - m) / a := by field_simp
    rw [hrw] at hj
    exact hj

/-- The chord length at a nontrivial `a`-th root of unity. -/
theorem four_mul_min_div_le_norm {a m : ℕ} (h0 : 0 < m) (hma : m < a) :
    4 * ((min m (a - m) : ℕ) : ℝ) / (a : ℝ) ≤ ‖e (2 * π * m / a) - 1‖ := by
  have hapos : 0 < a := lt_trans h0 hma
  have ha : (0 : ℝ) < a := by exact_mod_cast hapos
  have hhalf : 2 * π * (m : ℝ) / a / 2 = π * (m : ℝ) / a := by ring
  rw [norm_e_sub_one_eq, hhalf]
  have hs := two_mul_min_div_le_sin h0 hma
  have hnn : (0 : ℝ) ≤ 2 * ((min m (a - m) : ℕ) : ℝ) / a := by positivity
  rw [abs_of_nonneg (le_trans hnn hs)]
  calc 4 * ((min m (a - m) : ℕ) : ℝ) / (a : ℝ)
      = 2 * (2 * ((min m (a - m) : ℕ) : ℝ) / (a : ℝ)) := by ring
    _ ≤ 2 * Real.sin (π * (m : ℝ) / a) := by linarith

/-- **The bound §4 uses.**  For `0 < m < a`,
`‖∑_{B ≤ j < T} e(2πmj/a)‖ ≤ a / (2 · min(m, a-m))`. -/
theorem norm_geom_sum_root_le {a m : ℕ} (h0 : 0 < m) (hma : m < a) (B T : ℕ) :
    ‖∑ j ∈ Finset.Ico B T, e (2 * π * m / a) ^ j‖
      ≤ (a : ℝ) / (2 * ((min m (a - m) : ℕ) : ℝ)) := by
  have hapos : 0 < a := lt_trans h0 hma
  have ha : (0 : ℝ) < a := by exact_mod_cast hapos
  have hminpos : 0 < min m (a - m) := by omega
  have hmr : (0 : ℝ) < ((min m (a - m) : ℕ) : ℝ) := by exact_mod_cast hminpos
  have hlow := four_mul_min_div_le_norm h0 hma
  have hden : 0 < ‖e (2 * π * (m : ℝ) / a) - 1‖ := by
    have hp : (0 : ℝ) < 4 * ((min m (a - m) : ℕ) : ℝ) / a := by positivity
    linarith
  have hne : e (2 * π * (m : ℝ) / a) ≠ 1 := by
    intro hc
    rw [hc, sub_self, norm_zero] at hden
    exact lt_irrefl 0 hden
  refine (norm_geom_sum_le' hne B T).trans ?_
  rw [div_le_div_iff₀ hden (by positivity)]
  have hmul : 4 * ((min m (a - m) : ℕ) : ℝ) ≤ (a : ℝ) * ‖e (2 * π * (m : ℝ) / a) - 1‖ := by
    have hstep := mul_le_mul_of_nonneg_left hlow ha.le
    calc (4 : ℝ) * ((min m (a - m) : ℕ) : ℝ)
        = (a : ℝ) * (4 * ((min m (a - m) : ℕ) : ℝ) / a) := by field_simp
      _ ≤ (a : ℝ) * ‖e (2 * π * (m : ℝ) / a) - 1‖ := hstep
  linarith

/-! ## Summing the bounds over `m`

The paper's Lemma 18 sums `norm_geom_sum_root_le` over `0 < m < a`, producing a
factor `∑_{0<m<a} 1/min(m, a-m)`.  Splitting `1/min` as `1/m + 1/(a-m)` and
reflecting `m ↦ a - m` bounds this by twice a harmonic sum, i.e. by `O(log a)`. -/

/-- `1/min(m, a-m) ≤ 1/m + 1/(a-m)`. -/
theorem one_div_min_le {a m : ℕ} (h0 : 0 < m) (hma : m < a) :
    (1 : ℝ) / ((min m (a - m) : ℕ) : ℝ) ≤ 1 / (m : ℝ) + 1 / ((a - m : ℕ) : ℝ) := by
  have h1 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast h0
  have h2 : (0 : ℝ) < ((a - m : ℕ) : ℝ) := by
    have hpos : 0 < a - m := by omega
    exact_mod_cast hpos
  rcases le_total m (a - m) with h | h
  · rw [min_eq_left h]
    have : (0 : ℝ) < 1 / ((a - m : ℕ) : ℝ) := by positivity
    linarith
  · rw [min_eq_right h]
    have : (0 : ℝ) < 1 / (m : ℝ) := by positivity
    linarith

/-- **The `log a` factor.**  `∑_{0<m<a} 1/min(m, a-m) ≤ 2 ∑_{0<m<a} 1/m`. -/
theorem sum_inv_min_le (a : ℕ) :
    ∑ m ∈ Finset.Ico 1 a, (1 : ℝ) / ((min m (a - m) : ℕ) : ℝ)
      ≤ 2 * ∑ m ∈ Finset.Ico 1 a, (1 : ℝ) / (m : ℝ) := by
  have hrefl : ∑ m ∈ Finset.Ico 1 a, (1 : ℝ) / ((a - m : ℕ) : ℝ)
      = ∑ m ∈ Finset.Ico 1 a, (1 : ℝ) / (m : ℝ) := by
    have h := Finset.sum_Ico_reflect (fun j => (1 : ℝ) / (j : ℝ)) 1 (n := a) (Nat.le_succ a)
    simpa using h
  calc ∑ m ∈ Finset.Ico 1 a, (1 : ℝ) / ((min m (a - m) : ℕ) : ℝ)
      ≤ ∑ m ∈ Finset.Ico 1 a, ((1 : ℝ) / (m : ℝ) + 1 / ((a - m : ℕ) : ℝ)) := by
        refine Finset.sum_le_sum fun m hm => ?_
        have hm' := Finset.mem_Ico.1 hm
        exact one_div_min_le hm'.1 hm'.2
    _ = (∑ m ∈ Finset.Ico 1 a, (1 : ℝ) / (m : ℝ))
          + ∑ m ∈ Finset.Ico 1 a, (1 : ℝ) / ((a - m : ℕ) : ℝ) := Finset.sum_add_distrib
    _ = 2 * ∑ m ∈ Finset.Ico 1 a, (1 : ℝ) / (m : ℝ) := by rw [hrefl]; ring

end BlockCycleRotation
