/-
# Linear functions twisted by characters

The sums §4 has to estimate are of the shape

  `∑_{1 ≤ b < T, b ≡ c mod a} (A + B·b)`.

Expanding the congruence in additive characters (`Orthogonality.lean`) turns the
error into a weighted sum, over the nontrivial characters `m`, of

  `∑_{1 ≤ b < T} (A + B·b) · e(2πmb/a)`,

each weighted by a phase `e(-2πmc/a)` of modulus one.  This file bounds that
inner sum (`norm_linear_geom_sum_root_le`) and then the whole weighted sum
(`norm_sum_twisted_le`), the weights being any family of modulus at most one.

The resulting bound

  `‖∑_m w_m ∑_b (A + B·b) e(2πmb/a)‖ ≤ (‖A‖ + ‖B‖(T-1)) · a · ∑_{0<m<a} 1/m`

carries the `log a` of Lemma 18 in its harmonic sum.
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
theorem norm_linear_geom_sum_le {θ : ℝ} (hne : e θ ≠ 1) (A B : ℂ) (T : ℕ) :
    ‖∑ b ∈ Finset.Ico 1 T, (A + B * b) * e θ ^ b‖
      ≤ (‖A‖ + ‖B‖ * (T - 1 : ℕ)) * (2 / ‖e θ - 1‖) := by
  have hsplit : ∑ b ∈ Finset.Ico 1 T, (A + B * b) * e θ ^ b
      = A * (∑ b ∈ Finset.Ico 1 T, e θ ^ b)
        + B * (∑ b ∈ Finset.Ico 1 T, (b : ℂ) * e θ ^ b) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [hsplit]
  have h1 := norm_geom_sum_le' hne 1 T
  have h2 := norm_weighted_geom_sum_le' hne T
  calc ‖A * (∑ b ∈ Finset.Ico 1 T, e θ ^ b)
        + B * (∑ b ∈ Finset.Ico 1 T, (b : ℂ) * e θ ^ b)‖
      ≤ ‖A * (∑ b ∈ Finset.Ico 1 T, e θ ^ b)‖
        + ‖B * (∑ b ∈ Finset.Ico 1 T, (b : ℂ) * e θ ^ b)‖ := norm_add_le _ _
    _ = ‖A‖ * ‖∑ b ∈ Finset.Ico 1 T, e θ ^ b‖
        + ‖B‖ * ‖∑ b ∈ Finset.Ico 1 T, (b : ℂ) * e θ ^ b‖ := by rw [norm_mul, norm_mul]
    _ ≤ ‖A‖ * (2 / ‖e θ - 1‖) + ‖B‖ * ((T - 1 : ℕ) * (2 / ‖e θ - 1‖)) := by gcongr
    _ = (‖A‖ + ‖B‖ * (T - 1 : ℕ)) * (2 / ‖e θ - 1‖) := by ring

/-- The inner sum at a nontrivial `a`-th root of unity. -/
theorem norm_linear_geom_sum_root_le {a m : ℕ} (h0 : 0 < m) (hma : m < a) (A B : ℂ) (T : ℕ) :
    ‖∑ b ∈ Finset.Ico 1 T, (A + B * b) * e (2 * π * (m : ℝ) / a) ^ b‖
      ≤ (‖A‖ + ‖B‖ * (T - 1 : ℕ)) * ((a : ℝ) / (2 * ((min m (a - m) : ℕ) : ℝ))) := by
  refine (norm_linear_geom_sum_le (e_root_ne_one h0 hma) A B T).trans ?_
  have hK : (0 : ℝ) ≤ ‖A‖ + ‖B‖ * (T - 1 : ℕ) := by positivity
  exact mul_le_mul_of_nonneg_left (two_div_norm_le h0 hma) hK

/-- **The error term of §4.**  Summing the inner sums over the nontrivial
characters, against arbitrary weights of modulus at most one, costs a harmonic
sum — this is where the `log a` of Lemma 18 comes from. -/
theorem norm_sum_twisted_le {a : ℕ} (A B : ℂ) (T : ℕ) (w : ℕ → ℂ) (hw : ∀ m, ‖w m‖ ≤ 1) :
    ‖∑ m ∈ Finset.Ico 1 a, w m * ∑ b ∈ Finset.Ico 1 T,
        (A + B * b) * e (2 * π * (m : ℝ) / a) ^ b‖
      ≤ (‖A‖ + ‖B‖ * (T - 1 : ℕ)) * (a : ℝ) * ∑ m ∈ Finset.Ico 1 a, (1 : ℝ) / (m : ℝ) := by
  have hK : (0 : ℝ) ≤ ‖A‖ + ‖B‖ * (T - 1 : ℕ) := by positivity
  -- bound each term
  have hterm : ∀ m ∈ Finset.Ico 1 a,
      ‖w m * ∑ b ∈ Finset.Ico 1 T, (A + B * b) * e (2 * π * (m : ℝ) / a) ^ b‖
        ≤ (‖A‖ + ‖B‖ * (T - 1 : ℕ)) * ((a : ℝ) / (2 * ((min m (a - m) : ℕ) : ℝ))) := by
    intro m hm
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hm
    rw [norm_mul]
    calc ‖w m‖ * ‖∑ b ∈ Finset.Ico 1 T, (A + B * b) * e (2 * π * (m : ℝ) / a) ^ b‖
        ≤ 1 * ‖∑ b ∈ Finset.Ico 1 T, (A + B * b) * e (2 * π * (m : ℝ) / a) ^ b‖ := by
          gcongr
          exact hw m
      _ = ‖∑ b ∈ Finset.Ico 1 T, (A + B * b) * e (2 * π * (m : ℝ) / a) ^ b‖ := one_mul _
      _ ≤ _ := norm_linear_geom_sum_root_le h1 h2 A B T
  -- pull the constants out of the sum
  have hpull : ∑ m ∈ Finset.Ico 1 a,
        (‖A‖ + ‖B‖ * (T - 1 : ℕ)) * ((a : ℝ) / (2 * ((min m (a - m) : ℕ) : ℝ)))
      = (‖A‖ + ‖B‖ * (T - 1 : ℕ)) * (a : ℝ)
          * ∑ m ∈ Finset.Ico 1 a, (1 : ℝ) / (2 * ((min m (a - m) : ℕ) : ℝ)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by ring
  -- the harmonic bound
  have hhalf : ∑ m ∈ Finset.Ico 1 a, (1 : ℝ) / (2 * ((min m (a - m) : ℕ) : ℝ))
      ≤ ∑ m ∈ Finset.Ico 1 a, (1 : ℝ) / (m : ℝ) := by
    have h1 : ∑ m ∈ Finset.Ico 1 a, (1 : ℝ) / (2 * ((min m (a - m) : ℕ) : ℝ))
        = (1 / 2) * ∑ m ∈ Finset.Ico 1 a, (1 : ℝ) / ((min m (a - m) : ℕ) : ℝ) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun m _ => by ring
    have h2 := sum_inv_min_le a
    rw [h1]
    linarith
  calc ‖∑ m ∈ Finset.Ico 1 a, w m * ∑ b ∈ Finset.Ico 1 T,
          (A + B * b) * e (2 * π * (m : ℝ) / a) ^ b‖
      ≤ ∑ m ∈ Finset.Ico 1 a,
          ‖w m * ∑ b ∈ Finset.Ico 1 T, (A + B * b) * e (2 * π * (m : ℝ) / a) ^ b‖ :=
        norm_sum_le _ _
    _ ≤ ∑ m ∈ Finset.Ico 1 a,
          (‖A‖ + ‖B‖ * (T - 1 : ℕ)) * ((a : ℝ) / (2 * ((min m (a - m) : ℕ) : ℝ))) :=
        Finset.sum_le_sum hterm
    _ = (‖A‖ + ‖B‖ * (T - 1 : ℕ)) * (a : ℝ)
          * ∑ m ∈ Finset.Ico 1 a, (1 : ℝ) / (2 * ((min m (a - m) : ℕ) : ℝ)) := hpull
    _ ≤ (‖A‖ + ‖B‖ * (T - 1 : ℕ)) * (a : ℝ) * ∑ m ∈ Finset.Ico 1 a, (1 : ℝ) / (m : ℝ) := by
        have hpos : (0 : ℝ) ≤ (‖A‖ + ‖B‖ * (T - 1 : ℕ)) * (a : ℝ) := by positivity
        exact mul_le_mul_of_nonneg_left hhalf hpos

end BlockCycleRotation
