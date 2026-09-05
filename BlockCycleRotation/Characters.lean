/-
# Exponential sums at roots of unity

Section 4 of Blomer--Bux removes a congruence condition `y' ≡ a mod x` by
expanding it in additive characters `y' ↦ e(mb/x)`, and then bounds each
resulting sum for `b ≢ 0`.  This file supplies the quantitative input for that
step: at a nontrivial `x`-th root of unity the chord length is bounded below by

  `‖e(2πb/x) - 1‖ ≥ 4 · min(b, x-b) / x`,

so the geometric sums of `ExpSum.lean` obey

  `‖∑_{B ≤ j < Y} e(2πmj/x)‖ ≤ x / (2 · min(b, x-b))`.

Summing `1 / min(b, x-b)` over `0 < b < x` is what produces the `log x` in the
paper's Lemma 16.
-/

import BlockCycleRotation.ExpSum

namespace BlockCycleRotation

open Real Finset

/-- **Jordan's inequality at a root of unity.**  For `0 < b < x`,
`2 · min(b, x-b) / x ≤ sin (π b / x)`.

The two cases are `b ≤ x/2`, where Jordan applies directly, and `b > x/2`, where
it applies after reflecting via `sin (π - x) = sin x`. -/
theorem two_mul_min_div_le_sin {x b : ℕ} (h0 : 0 < b) (hma : b < x) :
    2 * ((min b (x - b) : ℕ) : ℝ) / (x : ℝ) ≤ Real.sin (π * b / x) := by
  have hapos : 0 < x := lt_trans h0 hma
  have hx : (0 : ℝ) < x := by exact_mod_cast hapos
  have hpi := Real.pi_pos
  have hmle : (b : ℝ) ≤ (x : ℝ) := by exact_mod_cast hma.le
  rcases le_or_gt (2 * b) x with hcase | hcase
  · -- `min = b`, and `π b / x ≤ π / 2`
    have hmin : min b (x - b) = b := by omega
    rw [hmin]
    have hx0 : 0 ≤ π * b / x := by positivity
    have hx1 : π * (b : ℝ) / x ≤ π / 2 := by
      rw [div_le_div_iff₀ hx (by norm_num)]
      have h2b : (2 : ℝ) * b ≤ x := by exact_mod_cast hcase
      nlinarith
    have hj := Real.mul_le_sin hx0 hx1
    have hrw : 2 / π * (π * (b : ℝ) / x) = 2 * (b : ℝ) / x := by field_simp
    rw [hrw] at hj
    exact hj
  · -- `min = x - b`, and reflect
    have hmin : min b (x - b) = x - b := by omega
    have hsub : ((x - b : ℕ) : ℝ) = (x : ℝ) - b := by rw [Nat.cast_sub hma.le]
    have hd : (0 : ℝ) ≤ (x : ℝ) - b := by linarith
    rw [hmin, hsub]
    have hkey : π * (b : ℝ) / x = π - π * ((x : ℝ) - b) / x := by
      field_simp
      ring
    rw [hkey, Real.sin_pi_sub]
    have hx0 : 0 ≤ π * ((x : ℝ) - b) / x := div_nonneg (mul_nonneg hpi.le hd) hx.le
    have hx1 : π * ((x : ℝ) - b) / x ≤ π / 2 := by
      rw [div_le_div_iff₀ hx (by norm_num)]
      have h2b : (x : ℝ) < 2 * b := by exact_mod_cast hcase
      nlinarith
    have hj := Real.mul_le_sin hx0 hx1
    have hrw : 2 / π * (π * ((x : ℝ) - b) / x) = 2 * ((x : ℝ) - b) / x := by field_simp
    rw [hrw] at hj
    exact hj

/-- The chord length at a nontrivial `x`-th root of unity. -/
theorem four_mul_min_div_le_norm {x b : ℕ} (h0 : 0 < b) (hma : b < x) :
    4 * ((min b (x - b) : ℕ) : ℝ) / (x : ℝ) ≤ ‖e (2 * π * b / x) - 1‖ := by
  have hapos : 0 < x := lt_trans h0 hma
  have hx : (0 : ℝ) < x := by exact_mod_cast hapos
  have hhalf : 2 * π * (b : ℝ) / x / 2 = π * (b : ℝ) / x := by ring
  rw [norm_e_sub_one_eq, hhalf]
  have hs := two_mul_min_div_le_sin h0 hma
  have hnn : (0 : ℝ) ≤ 2 * ((min b (x - b) : ℕ) : ℝ) / x := by positivity
  rw [abs_of_nonneg (le_trans hnn hs)]
  calc 4 * ((min b (x - b) : ℕ) : ℝ) / (x : ℝ)
      = 2 * (2 * ((min b (x - b) : ℕ) : ℝ) / (x : ℝ)) := by ring
    _ ≤ 2 * Real.sin (π * (b : ℝ) / x) := by linarith

/-- A nontrivial `x`-th root of unity is not `1`. -/
theorem e_root_ne_one {x b : ℕ} (h0 : 0 < b) (hma : b < x) :
    e (2 * π * (b : ℝ) / x) ≠ 1 := by
  have hapos : 0 < x := lt_trans h0 hma
  have hx : (0 : ℝ) < x := by exact_mod_cast hapos
  have hminpos : 0 < min b (x - b) := by omega
  have hmr : (0 : ℝ) < ((min b (x - b) : ℕ) : ℝ) := by exact_mod_cast hminpos
  have hlow := four_mul_min_div_le_norm h0 hma
  have hden : 0 < ‖e (2 * π * (b : ℝ) / x) - 1‖ := by
    have hp : (0 : ℝ) < 4 * ((min b (x - b) : ℕ) : ℝ) / x := by positivity
    linarith
  intro ha
  rw [ha, sub_self, norm_zero] at hden
  exact lt_irrefl 0 hden

/-- The chord bound in the form the sum estimates use. -/
theorem two_div_norm_le {x b : ℕ} (h0 : 0 < b) (hma : b < x) :
    2 / ‖e (2 * π * (b : ℝ) / x) - 1‖ ≤ (x : ℝ) / (2 * ((min b (x - b) : ℕ) : ℝ)) := by
  have hapos : 0 < x := lt_trans h0 hma
  have hx : (0 : ℝ) < x := by exact_mod_cast hapos
  have hminpos : 0 < min b (x - b) := by omega
  have hmr : (0 : ℝ) < ((min b (x - b) : ℕ) : ℝ) := by exact_mod_cast hminpos
  have hlow := four_mul_min_div_le_norm h0 hma
  have hden : 0 < ‖e (2 * π * (b : ℝ) / x) - 1‖ := by
    have hp : (0 : ℝ) < 4 * ((min b (x - b) : ℕ) : ℝ) / x := by positivity
    linarith
  rw [div_le_div_iff₀ hden (by positivity)]
  have hmul : 4 * ((min b (x - b) : ℕ) : ℝ) ≤ (x : ℝ) * ‖e (2 * π * (b : ℝ) / x) - 1‖ := by
    have hstep := mul_le_mul_of_nonneg_left hlow hx.le
    calc (4 : ℝ) * ((min b (x - b) : ℕ) : ℝ)
        = (x : ℝ) * (4 * ((min b (x - b) : ℕ) : ℝ) / x) := by field_simp
      _ ≤ (x : ℝ) * ‖e (2 * π * (b : ℝ) / x) - 1‖ := hstep
  linarith

/-- **The bound §4 uses.**  For `0 < b < x`,
`‖∑_{B ≤ j < Y} e(2πmj/x)‖ ≤ x / (2 · min(b, x-b))`. -/
theorem norm_geom_sum_root_le {x b : ℕ} (h0 : 0 < b) (hma : b < x) (B Y : ℕ) :
    ‖∑ j ∈ Finset.Ico B Y, e (2 * π * b / x) ^ j‖
      ≤ (x : ℝ) / (2 * ((min b (x - b) : ℕ) : ℝ)) :=
  (norm_geom_sum_le' (e_root_ne_one h0 hma) B Y).trans (two_div_norm_le h0 hma)

/-! ## Summing the bounds over `b`

The paper's Lemma 16 sums `norm_geom_sum_root_le` over `0 < b < x`, producing a
factor `∑_{0<b<x} 1/min(b, x-b)`.  Splitting `1/min` as `1/b + 1/(x-b)` and
reflecting `b ↦ x - b` bounds this by twice a harmonic sum, i.e. by `O(log x)`. -/

/-- `1/min(b, x-b) ≤ 1/b + 1/(x-b)`. -/
theorem one_div_min_le {x b : ℕ} (h0 : 0 < b) (hma : b < x) :
    (1 : ℝ) / ((min b (x - b) : ℕ) : ℝ) ≤ 1 / (b : ℝ) + 1 / ((x - b : ℕ) : ℝ) := by
  have h1 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast h0
  have h2 : (0 : ℝ) < ((x - b : ℕ) : ℝ) := by
    have hpos : 0 < x - b := by omega
    exact_mod_cast hpos
  rcases le_total b (x - b) with h | h
  · rw [min_eq_left h]
    have : (0 : ℝ) < 1 / ((x - b : ℕ) : ℝ) := by positivity
    linarith
  · rw [min_eq_right h]
    have : (0 : ℝ) < 1 / (b : ℝ) := by positivity
    linarith

/-- **The `log x` factor.**  `∑_{0<b<x} 1/min(b, x-b) ≤ 2 ∑_{0<b<x} 1/b`. -/
theorem sum_inv_min_le (x : ℕ) :
    ∑ b ∈ Finset.Ico 1 x, (1 : ℝ) / ((min b (x - b) : ℕ) : ℝ)
      ≤ 2 * ∑ b ∈ Finset.Ico 1 x, (1 : ℝ) / (b : ℝ) := by
  have hrefl : ∑ b ∈ Finset.Ico 1 x, (1 : ℝ) / ((x - b : ℕ) : ℝ)
      = ∑ b ∈ Finset.Ico 1 x, (1 : ℝ) / (b : ℝ) := by
    have h := Finset.sum_Ico_reflect (fun j => (1 : ℝ) / (j : ℝ)) 1 (n := x) (Nat.le_succ x)
    simpa using h
  calc ∑ b ∈ Finset.Ico 1 x, (1 : ℝ) / ((min b (x - b) : ℕ) : ℝ)
      ≤ ∑ b ∈ Finset.Ico 1 x, ((1 : ℝ) / (b : ℝ) + 1 / ((x - b : ℕ) : ℝ)) := by
        refine Finset.sum_le_sum fun b hb => ?_
        have hm' := Finset.mem_Ico.1 hb
        exact one_div_min_le hm'.1 hm'.2
    _ = (∑ b ∈ Finset.Ico 1 x, (1 : ℝ) / (b : ℝ))
          + ∑ b ∈ Finset.Ico 1 x, (1 : ℝ) / ((x - b : ℕ) : ℝ) := Finset.sum_add_distrib
    _ = 2 * ∑ b ∈ Finset.Ico 1 x, (1 : ℝ) / (b : ℝ) := by rw [hrefl]; ring

end BlockCycleRotation
