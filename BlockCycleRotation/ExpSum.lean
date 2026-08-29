/-
# Elementary bounds on exponential sums

This file formalises Observation 15 of

  Valentin Blomer and Kai-Uwe Bux,
  *The cost of cyclic permutations and remainder sums in the Euclidean algorithm*,
  AofA 2026.  arXiv:2601.00979.

Observation 15 is the *only* analytic input to the error term in Theorem 13.
Notably it needs no Kloosterman or Weil bounds: everything follows from Jordan's
inequality (`Real.mul_abs_le_abs_sin` in Mathlib) together with the closed form
of a geometric series, i.e. the trivial bound on an exponential sum, with no
square-root cancellation anywhere.

The two estimates proved here are, for `0 < |θ| ≤ π`:

* `‖∑ j ∈ Ico B T, e(jθ)‖ ≤ π / |θ|`, and
* `‖∑ j ∈ Ico 1 T, j * e(jθ)‖ ≤ (T - 1) * (π / |θ|)`,

the second by writing `j` as a count and swapping the order of summation, which
is the double-counting argument in the paper.
-/

import Mathlib

open Real Finset

namespace BlockCycleRotation

/-- `e θ` is the point `exp (θ i)` on the unit circle. -/
noncomputable def e (θ : ℝ) : ℂ := Complex.exp ((θ : ℂ) * Complex.I)

@[simp]
theorem norm_e (θ : ℝ) : ‖e θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

@[simp]
theorem norm_e_pow (θ : ℝ) (n : ℕ) : ‖e θ ^ n‖ = 1 := by
  rw [norm_pow, norm_e, one_pow]

/-- `‖e θ - 1‖² = 2 - 2 cos θ`. -/
theorem norm_e_sub_one_sq (θ : ℝ) : ‖e θ - 1‖ ^ 2 = 2 - 2 * Real.cos θ := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [e, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, sub_zero]
  nlinarith [Real.sin_sq_add_cos_sq θ]

/-- The half-angle identity `2 - 2 cos θ = 4 sin²(θ/2)`. -/
theorem two_sub_two_cos (θ : ℝ) : 2 - 2 * Real.cos θ = 4 * Real.sin (θ / 2) ^ 2 := by
  have h := Real.cos_two_mul (θ / 2)
  rw [show 2 * (θ / 2) = θ by ring] at h
  nlinarith [Real.sin_sq_add_cos_sq (θ / 2)]

/-- `‖e θ - 1‖ = 2 |sin (θ/2)|`, the exact form of the chord length. -/
theorem norm_e_sub_one_eq (θ : ℝ) : ‖e θ - 1‖ = 2 * |Real.sin (θ / 2)| := by
  have hsq : ‖e θ - 1‖ ^ 2 = (2 * |Real.sin (θ / 2)|) ^ 2 := by
    rw [norm_e_sub_one_sq, two_sub_two_cos, mul_pow, sq_abs]
    ring
  have h := congrArg Real.sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (by positivity)] at h

/-- The easy half of Observation 15: `‖e θ - 1‖ ≤ |θ|`. -/
theorem norm_e_sub_one_le (θ : ℝ) : ‖e θ - 1‖ ≤ |θ| := by
  have habs : |θ / 2| = |θ| / 2 := by rw [abs_div, abs_two]
  have hs : |Real.sin (θ / 2)| ≤ |θ| / 2 := by
    have h := Real.abs_sin_le_abs (x := θ / 2)
    rwa [habs] at h
  have hsq : ‖e θ - 1‖ ^ 2 ≤ |θ| ^ 2 := by
    rw [norm_e_sub_one_sq, two_sub_two_cos, ← sq_abs (Real.sin (θ / 2))]
    nlinarith [abs_nonneg (Real.sin (θ / 2)), abs_nonneg θ, hs]
  have h1 := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (abs_nonneg θ)] at h1

/-- **Jordan's inequality for the circle.**  The hard half of Observation 15:
for `|θ| ≤ π` we have `(2/π)|θ| ≤ ‖e θ - 1‖`.

This is the bi-Lipschitz comparison between the arc-length and Euclidean metrics
on the unit circle. -/
theorem mul_abs_le_norm_e_sub_one {θ : ℝ} (h : |θ| ≤ π) : 2 / π * |θ| ≤ ‖e θ - 1‖ := by
  have hpi := Real.pi_pos
  have habs : |θ / 2| = |θ| / 2 := by rw [abs_div, abs_two]
  have hhalf : |θ / 2| ≤ π / 2 := by rw [habs]; linarith
  have hj : 2 / π * |θ / 2| ≤ |Real.sin (θ / 2)| := Real.mul_abs_le_abs_sin hhalf
  rw [habs] at hj
  -- `|θ| / π ≤ |sin (θ/2)|`
  have h2 : 2 / π * (|θ| / 2) = |θ| / π := by ring
  have hj' : |θ| / π ≤ |Real.sin (θ / 2)| := by rwa [h2] at hj
  have hsq : (2 / π * |θ|) ^ 2 ≤ ‖e θ - 1‖ ^ 2 := by
    rw [norm_e_sub_one_sq, two_sub_two_cos, ← sq_abs (Real.sin (θ / 2))]
    have hnn : 0 ≤ |θ| / π := by positivity
    have h3 : (2 / π * |θ|) ^ 2 = 4 * (|θ| / π) ^ 2 := by ring
    rw [h3]
    nlinarith [mul_self_le_mul_self hnn hj', hnn, abs_nonneg (Real.sin (θ / 2))]
  have h1 := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (by positivity), Real.sqrt_sq (norm_nonneg _)] at h1

theorem e_ne_one {θ : ℝ} (h0 : θ ≠ 0) (h : |θ| ≤ π) : e θ ≠ 1 := by
  intro hc
  have hpos : 0 < 2 / π * |θ| := by
    have : 0 < |θ| := abs_pos.2 h0
    have := Real.pi_pos
    positivity
  have hle := mul_abs_le_norm_e_sub_one h
  rw [hc, sub_self, norm_zero] at hle
  linarith

/-! ## The exponential sum bounds -/

/-- **Observation 15, geometric sum.**  For `0 < |θ| ≤ π`,
`‖∑_{B ≤ j < T} e(jθ)‖ ≤ π / |θ|`.

This is the trivial bound: the sum telescopes to a quotient whose numerator has
norm at most `2`, and the denominator is bounded below by Jordan's inequality. -/
theorem norm_geom_sum_le' {θ : ℝ} (hne : e θ ≠ 1) (B T : ℕ) :
    ‖∑ j ∈ Finset.Ico B T, e θ ^ j‖ ≤ 2 / ‖e θ - 1‖ := by
  have hpos : 0 < ‖e θ - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  rcases le_or_gt B T with hBT | hBT
  · rw [geom_sum_Ico hne hBT, norm_div]
    have hnum : ‖e θ ^ T - e θ ^ B‖ ≤ 2 := by
      calc ‖e θ ^ T - e θ ^ B‖ ≤ ‖e θ ^ T‖ + ‖e θ ^ B‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_e_pow, norm_e_pow]; norm_num
    gcongr
  · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty, norm_zero]
    positivity

/-- **Observation 15, geometric sum.**  For `0 < |θ| ≤ π`,
`‖∑_{B ≤ j < T} e(jθ)‖ ≤ π / |θ|`.

This is the trivial bound: the sum telescopes to a quotient whose numerator has
norm at most `2`, and the denominator is bounded below by Jordan's inequality. -/
theorem norm_geom_sum_le {θ : ℝ} (h0 : θ ≠ 0) (h : |θ| ≤ π) (B T : ℕ) :
    ‖∑ j ∈ Finset.Ico B T, e θ ^ j‖ ≤ π / |θ| := by
  have hpi := Real.pi_pos
  have hθpos : 0 < |θ| := abs_pos.2 h0
  have hden : 2 / π * |θ| ≤ ‖e θ - 1‖ := mul_abs_le_norm_e_sub_one h
  have hdenpos : 0 < ‖e θ - 1‖ := by
    have : 0 < 2 / π * |θ| := by positivity
    linarith
  refine (norm_geom_sum_le' (e_ne_one h0 h) B T).trans ?_
  rw [div_le_div_iff₀ hdenpos hθpos]
  have hstep : 2 * |θ| ≤ π * ‖e θ - 1‖ := by
    have hmul := mul_le_mul_of_nonneg_left hden hpi.le
    calc 2 * |θ| = π * (2 / π * |θ|) := by field_simp
      _ ≤ π * ‖e θ - 1‖ := hmul
  linarith

/-- The weighted sum bound in terms of the chord length, with no restriction on
`θ`.  Proved by the paper's double-counting argument: write `j` as the number of
`B` with `1 ≤ B ≤ j`, swap the order of summation, and apply the geometric
bound to each inner sum. -/
theorem norm_weighted_geom_sum_le' {θ : ℝ} (hne : e θ ≠ 1) (T : ℕ) :
    ‖∑ j ∈ Finset.Ico 1 T, (j : ℂ) * e θ ^ j‖ ≤ (T - 1 : ℕ) * (2 / ‖e θ - 1‖) := by
  have key : ∑ j ∈ Finset.Ico 1 T, (j : ℂ) * e θ ^ j
      = ∑ i ∈ Finset.Ico 1 T, ∑ j ∈ Finset.Ico i T, e θ ^ j := by
    rw [Finset.sum_Ico_Ico_comm 1 T (fun _ j => e θ ^ j)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    simp
  rw [key]
  calc ‖∑ i ∈ Finset.Ico 1 T, ∑ j ∈ Finset.Ico i T, e θ ^ j‖
      ≤ ∑ i ∈ Finset.Ico 1 T, ‖∑ j ∈ Finset.Ico i T, e θ ^ j‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ Finset.Ico 1 T, (2 / ‖e θ - 1‖) :=
        Finset.sum_le_sum fun i _ => norm_geom_sum_le' hne i T
    _ = (T - 1 : ℕ) * (2 / ‖e θ - 1‖) := by
        rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]

/-- **Observation 15, weighted sum.**  For `0 < |θ| ≤ π`,
`‖∑_{1 ≤ j < T} j · e(jθ)‖ ≤ (T - 1) · π / |θ|`.

Proved by the paper's double-counting argument: write `j` as the number of `B`
with `1 ≤ B ≤ j`, swap the order of summation, and apply the geometric bound to
each inner sum. -/
theorem norm_weighted_geom_sum_le {θ : ℝ} (h0 : θ ≠ 0) (h : |θ| ≤ π) (T : ℕ) :
    ‖∑ j ∈ Finset.Ico 1 T, (j : ℂ) * e θ ^ j‖ ≤ (T - 1 : ℕ) * (π / |θ|) := by
  have key : ∑ j ∈ Finset.Ico 1 T, (j : ℂ) * e θ ^ j
      = ∑ i ∈ Finset.Ico 1 T, ∑ j ∈ Finset.Ico i T, e θ ^ j := by
    rw [Finset.sum_Ico_Ico_comm 1 T (fun _ j => e θ ^ j)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    simp
  rw [key]
  calc ‖∑ i ∈ Finset.Ico 1 T, ∑ j ∈ Finset.Ico i T, e θ ^ j‖
      ≤ ∑ i ∈ Finset.Ico 1 T, ‖∑ j ∈ Finset.Ico i T, e θ ^ j‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ Finset.Ico 1 T, (π / |θ|) :=
        Finset.sum_le_sum fun i _ => norm_geom_sum_le h0 h i T
    _ = (T - 1 : ℕ) * (π / |θ|) := by
        rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]

/-! ### The sharp form of Observation 15

The paper does not stop at the triangle inequality: after the double-counting
step it evaluates the inner geometric sums in closed form,

  `∑_{1≤j<T} j x^j = ((T-1) x^T - (x^T - x)/(x-1)) / (x-1)`,

and reads off `π²/(2θ²) + (T-1)π/(2|θ|)`.  That is the bound stated in the
paper, and it is what we prove here. -/

theorem weighted_geom_sum_closed {θ : ℝ} (hne : e θ ≠ 1) (T : ℕ) (hT : 1 ≤ T) :
    ∑ j ∈ Finset.Ico 1 T, (j : ℂ) * e θ ^ j
      = ((T - 1 : ℕ) * e θ ^ T - (e θ ^ T - e θ) / (e θ - 1)) / (e θ - 1) := by
  have key : ∑ j ∈ Finset.Ico 1 T, (j : ℂ) * e θ ^ j
      = ∑ i ∈ Finset.Ico 1 T, ∑ j ∈ Finset.Ico i T, e θ ^ j := by
    rw [Finset.sum_Ico_Ico_comm 1 T (fun _ j => e θ ^ j)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    simp
  have hx1 : e θ - 1 ≠ 0 := sub_ne_zero.2 hne
  have hinner : ∀ i ∈ Finset.Ico 1 T,
      ∑ j ∈ Finset.Ico i T, e θ ^ j = (e θ ^ T - e θ ^ i) / (e θ - 1) := by
    intro i hi
    exact geom_sum_Ico hne (Finset.mem_Ico.1 hi).2.le
  rw [key, Finset.sum_congr rfl hinner]
  have hsplit : ∑ i ∈ Finset.Ico 1 T, (e θ ^ T - e θ ^ i) / (e θ - 1)
      = ((∑ _i ∈ Finset.Ico 1 T, e θ ^ T) - ∑ i ∈ Finset.Ico 1 T, e θ ^ i) / (e θ - 1) := by
    rw [← Finset.sum_sub_distrib, Finset.sum_div]
  rw [hsplit, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, geom_sum_Ico hne hT]
  norm_num

/-- **Observation 15, weighted sum, in the paper's sharp form.**
For `0 < |θ| ≤ π`,
`‖∑_{1 ≤ j < T} j · e(jθ)‖ ≤ π²/(2θ²) + (T-1)·π/(2|θ|)`. -/
theorem norm_weighted_geom_sum_le_sharp {θ : ℝ} (h0 : θ ≠ 0) (h : |θ| ≤ π) (T : ℕ) :
    ‖∑ j ∈ Finset.Ico 1 T, (j : ℂ) * e θ ^ j‖
      ≤ π ^ 2 / (2 * θ ^ 2) + (T - 1 : ℕ) * π / (2 * |θ|) := by
  have hpi := Real.pi_pos
  have hθpos : 0 < |θ| := abs_pos.2 h0
  have hθsq : 0 < θ ^ 2 := by positivity
  have hne : e θ ≠ 1 := e_ne_one h0 h
  have hx1 : e θ - 1 ≠ 0 := sub_ne_zero.2 hne
  have hu : 0 < ‖e θ - 1‖ := norm_pos_iff.2 hx1
  -- the chord bound `2|θ|/π ≤ ‖e θ - 1‖`, in the two forms we need
  have hchord : 2 / π * |θ| ≤ ‖e θ - 1‖ := mul_abs_le_norm_e_sub_one h
  have hinv : 1 / ‖e θ - 1‖ ≤ π / (2 * |θ|) := by
    rw [div_le_div_iff₀ hu (by positivity)]
    have : 2 / π * |θ| * π = 2 * |θ| := by field_simp
    nlinarith [mul_le_mul_of_nonneg_right hchord hpi.le]
  have hinvsq : 1 / ‖e θ - 1‖ ^ 2 ≤ π ^ 2 / (4 * θ ^ 2) := by
    have h1 : (1 / ‖e θ - 1‖) ^ 2 ≤ (π / (2 * |θ|)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hinv 2
    have hsq : (2 * |θ|) ^ 2 = 4 * θ ^ 2 := by
      rw [mul_pow, sq_abs]; norm_num
    have h2 : (π / (2 * |θ|)) ^ 2 = π ^ 2 / (4 * θ ^ 2) := by
      rw [div_pow, hsq]
    rw [div_pow, h2] at h1
    simpa using h1
  rcases Nat.eq_zero_or_pos T with hT | hT
  · subst hT
    rw [show Finset.Ico 1 0 = (∅ : Finset ℕ) from Finset.Ico_eq_empty (by omega),
      Finset.sum_empty, norm_zero]
    have h2 : ((0 - 1 : ℕ) : ℝ) = 0 := by norm_num
    rw [h2, zero_mul, zero_div, add_zero]
    exact le_of_lt (div_pos (by positivity) (by linarith))
  rw [weighted_geom_sum_closed hne T hT]
  have hnum : ‖((T - 1 : ℕ) : ℂ) * e θ ^ T - (e θ ^ T - e θ) / (e θ - 1)‖
      ≤ (T - 1 : ℕ) + 2 / ‖e θ - 1‖ := by
    refine (norm_sub_le _ _).trans ?_
    have h1 : ‖((T - 1 : ℕ) : ℂ) * e θ ^ T‖ = (T - 1 : ℕ) := by
      rw [norm_mul, norm_e_pow, mul_one, Complex.norm_natCast]
    have h2 : ‖(e θ ^ T - e θ) / (e θ - 1)‖ ≤ 2 / ‖e θ - 1‖ := by
      rw [norm_div]
      gcongr
      calc ‖e θ ^ T - e θ‖ ≤ ‖e θ ^ T‖ + ‖e θ‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_e_pow, norm_e]; norm_num
    linarith
  rw [norm_div]
  have hstep : ‖((T - 1 : ℕ) : ℂ) * e θ ^ T - (e θ ^ T - e θ) / (e θ - 1)‖ / ‖e θ - 1‖
      ≤ ((T - 1 : ℕ) + 2 / ‖e θ - 1‖) / ‖e θ - 1‖ := by
    gcongr
  refine hstep.trans ?_
  have hexp : ((T - 1 : ℕ) + 2 / ‖e θ - 1‖) / ‖e θ - 1‖
      = (T - 1 : ℕ) * (1 / ‖e θ - 1‖) + 2 * (1 / ‖e θ - 1‖ ^ 2) := by
    field_simp
  rw [hexp]
  have hA : ((T - 1 : ℕ) : ℝ) * (1 / ‖e θ - 1‖) ≤ ((T - 1 : ℕ) : ℝ) * (π / (2 * |θ|)) :=
    mul_le_mul_of_nonneg_left hinv (by positivity)
  have hB : 2 * (1 / ‖e θ - 1‖ ^ 2) ≤ 2 * (π ^ 2 / (4 * θ ^ 2)) :=
    mul_le_mul_of_nonneg_left hinvsq (by norm_num)
  have hBB : 2 * (π ^ 2 / (4 * θ ^ 2)) = π ^ 2 / (2 * θ ^ 2) := by
    rw [eq_div_iff (by positivity : (2 : ℝ) * θ ^ 2 ≠ 0)]
    field_simp
    ring
  have hAA : ((T - 1 : ℕ) : ℝ) * (π / (2 * |θ|)) = ((T - 1 : ℕ) : ℝ) * π / (2 * |θ|) := by
    ring
  linarith [hA, hB]

end BlockCycleRotation
