/-
# Linear functions twisted by characters

The sums §4 has to estimate are of the shape

  `∑_{1 ≤ y' < Y, y' ≡ a mod x} (A + B·y')`.

Expanding the congruence in additive characters (`Orthogonality.lean`) turns the
error into a weighted sum, over the nontrivial characters `b`, of

  `∑_{1 ≤ y' < Y} (A + B·y') · e(2πmb/x)`,

each weighted by a phase `e(-2πmc/x)` of modulus one.  This file bounds that
inner sum (`norm_linear_geom_sum_root_le`) and then the whole weighted sum
(`norm_sum_twisted_le`), the weights being any family of modulus at most one.

The resulting bound

  `‖∑_b w_m ∑_y' (A + B·y') e(2πmb/x)‖ ≤ (‖A‖ + ‖B‖(Y-1)) · x · ∑_{0<b<x} 1/b`

carries the `log x` of Lemma 16 in its harmonic sum.
-/

import BlockCycleRotation.Orthogonality

namespace BlockCycleRotation

open Real Finset

/-- `e` turns addition into multiplication. -/
theorem e_add (x y : ℝ) : e (x + y) = e x * e y := by
  rw [e, e, e, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **The inner sum.**  A linear function twisted by a character, bounded by the
chord length. -/
theorem norm_linear_geom_sum_le {θ : ℝ} (hne : e θ ≠ 1) (A B : ℂ) (Y : ℕ) :
    ‖∑ y' ∈ Finset.Ico 1 Y, (A + B * y') * e θ ^ y'‖
      ≤ (‖A‖ + ‖B‖ * (Y - 1 : ℕ)) * (2 / ‖e θ - 1‖) := by
  have hsplit : ∑ y' ∈ Finset.Ico 1 Y, (A + B * y') * e θ ^ y'
      = A * (∑ y' ∈ Finset.Ico 1 Y, e θ ^ y')
        + B * (∑ y' ∈ Finset.Ico 1 Y, (y' : ℂ) * e θ ^ y') := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun y' _ => by ring
  rw [hsplit]
  have h1 := norm_geom_sum_le' hne 1 Y
  have h2 := norm_weighted_geom_sum_le' hne Y
  calc ‖A * (∑ y' ∈ Finset.Ico 1 Y, e θ ^ y')
        + B * (∑ y' ∈ Finset.Ico 1 Y, (y' : ℂ) * e θ ^ y')‖
      ≤ ‖A * (∑ y' ∈ Finset.Ico 1 Y, e θ ^ y')‖
        + ‖B * (∑ y' ∈ Finset.Ico 1 Y, (y' : ℂ) * e θ ^ y')‖ := norm_add_le _ _
    _ = ‖A‖ * ‖∑ y' ∈ Finset.Ico 1 Y, e θ ^ y'‖
        + ‖B‖ * ‖∑ y' ∈ Finset.Ico 1 Y, (y' : ℂ) * e θ ^ y'‖ := by rw [norm_mul, norm_mul]
    _ ≤ ‖A‖ * (2 / ‖e θ - 1‖) + ‖B‖ * ((Y - 1 : ℕ) * (2 / ‖e θ - 1‖)) := by gcongr
    _ = (‖A‖ + ‖B‖ * (Y - 1 : ℕ)) * (2 / ‖e θ - 1‖) := by ring

/-- The inner sum at a nontrivial `x`-th root of unity. -/
theorem norm_linear_geom_sum_root_le {x b : ℕ} (h0 : 0 < b) (hma : b < x) (A B : ℂ) (Y : ℕ) :
    ‖∑ y' ∈ Finset.Ico 1 Y, (A + B * y') * e (2 * π * (b : ℝ) / x) ^ y'‖
      ≤ (‖A‖ + ‖B‖ * (Y - 1 : ℕ)) * ((x : ℝ) / (2 * ((min b (x - b) : ℕ) : ℝ))) := by
  refine (norm_linear_geom_sum_le (e_root_ne_one h0 hma) A B Y).trans ?_
  have hK : (0 : ℝ) ≤ ‖A‖ + ‖B‖ * (Y - 1 : ℕ) := by positivity
  exact mul_le_mul_of_nonneg_left (two_div_norm_le h0 hma) hK

/-- **The error term of §4.**  Summing the inner sums over the nontrivial
characters, against arbitrary weights of modulus at most one, costs a harmonic
sum — this is where the `log x` of Lemma 16 comes from. -/
theorem norm_sum_twisted_le {x : ℕ} (A B : ℂ) (Y : ℕ) (w : ℕ → ℂ) (hw : ∀ b, ‖w b‖ ≤ 1) :
    ‖∑ b ∈ Finset.Ico 1 x, w b * ∑ y' ∈ Finset.Ico 1 Y,
        (A + B * y') * e (2 * π * (b : ℝ) / x) ^ y'‖
      ≤ (‖A‖ + ‖B‖ * (Y - 1 : ℕ)) * (x : ℝ) * ∑ b ∈ Finset.Ico 1 x, (1 : ℝ) / (b : ℝ) := by
  have hK : (0 : ℝ) ≤ ‖A‖ + ‖B‖ * (Y - 1 : ℕ) := by positivity
  -- bound each term
  have hterm : ∀ b ∈ Finset.Ico 1 x,
      ‖w b * ∑ y' ∈ Finset.Ico 1 Y, (A + B * y') * e (2 * π * (b : ℝ) / x) ^ y'‖
        ≤ (‖A‖ + ‖B‖ * (Y - 1 : ℕ)) * ((x : ℝ) / (2 * ((min b (x - b) : ℕ) : ℝ))) := by
    intro b hb
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hb
    rw [norm_mul]
    calc ‖w b‖ * ‖∑ y' ∈ Finset.Ico 1 Y, (A + B * y') * e (2 * π * (b : ℝ) / x) ^ y'‖
        ≤ 1 * ‖∑ y' ∈ Finset.Ico 1 Y, (A + B * y') * e (2 * π * (b : ℝ) / x) ^ y'‖ := by
          gcongr
          exact hw b
      _ = ‖∑ y' ∈ Finset.Ico 1 Y, (A + B * y') * e (2 * π * (b : ℝ) / x) ^ y'‖ := one_mul _
      _ ≤ _ := norm_linear_geom_sum_root_le h1 h2 A B Y
  -- pull the constants out of the sum
  have hpull : ∑ b ∈ Finset.Ico 1 x,
        (‖A‖ + ‖B‖ * (Y - 1 : ℕ)) * ((x : ℝ) / (2 * ((min b (x - b) : ℕ) : ℝ)))
      = (‖A‖ + ‖B‖ * (Y - 1 : ℕ)) * (x : ℝ)
          * ∑ b ∈ Finset.Ico 1 x, (1 : ℝ) / (2 * ((min b (x - b) : ℕ) : ℝ)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  -- the harmonic bound
  have hhalf : ∑ b ∈ Finset.Ico 1 x, (1 : ℝ) / (2 * ((min b (x - b) : ℕ) : ℝ))
      ≤ ∑ b ∈ Finset.Ico 1 x, (1 : ℝ) / (b : ℝ) := by
    have h1 : ∑ b ∈ Finset.Ico 1 x, (1 : ℝ) / (2 * ((min b (x - b) : ℕ) : ℝ))
        = (1 / 2) * ∑ b ∈ Finset.Ico 1 x, (1 : ℝ) / ((min b (x - b) : ℕ) : ℝ) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun b _ => by ring
    have h2 := sum_inv_min_le x
    rw [h1]
    linarith
  calc ‖∑ b ∈ Finset.Ico 1 x, w b * ∑ y' ∈ Finset.Ico 1 Y,
          (A + B * y') * e (2 * π * (b : ℝ) / x) ^ y'‖
      ≤ ∑ b ∈ Finset.Ico 1 x,
          ‖w b * ∑ y' ∈ Finset.Ico 1 Y, (A + B * y') * e (2 * π * (b : ℝ) / x) ^ y'‖ :=
        norm_sum_le _ _
    _ ≤ ∑ b ∈ Finset.Ico 1 x,
          (‖A‖ + ‖B‖ * (Y - 1 : ℕ)) * ((x : ℝ) / (2 * ((min b (x - b) : ℕ) : ℝ))) :=
        Finset.sum_le_sum hterm
    _ = (‖A‖ + ‖B‖ * (Y - 1 : ℕ)) * (x : ℝ)
          * ∑ b ∈ Finset.Ico 1 x, (1 : ℝ) / (2 * ((min b (x - b) : ℕ) : ℝ)) := hpull
    _ ≤ (‖A‖ + ‖B‖ * (Y - 1 : ℕ)) * (x : ℝ) * ∑ b ∈ Finset.Ico 1 x, (1 : ℝ) / (b : ℝ) := by
        have hpos : (0 : ℝ) ≤ (‖A‖ + ‖B‖ * (Y - 1 : ℕ)) * (x : ℝ) := by positivity
        exact mul_le_mul_of_nonneg_left hhalf hpos

end BlockCycleRotation
