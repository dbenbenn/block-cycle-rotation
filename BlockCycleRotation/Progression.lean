/-
# Sums over an arithmetic progression

This closes the loop on §4's key manoeuvre.  `Orthogonality.lean` supplies the
character expansion of the congruence `y' ≡ a mod x`, and `LinearSums.lean`
bounds the resulting twisted sums.  Here the two are combined: the phases
`e(-2πmc/x)`, previously abstracted as arbitrary weights of modulus one, are
instantiated, giving

  `‖∑_{1≤y'<Y, y'≡a mod x} (A + B·y')  −  (1/x)·∑_{1≤y'<Y} (A + B·y')‖`
      `≤ (‖A‖ + ‖B‖(Y-1)) · ∑_{0<b<x} 1/b`.

That is: replacing a sum over an arithmetic progression by its expected value
costs a harmonic sum, which is `O(log x)`.
-/

import BlockCycleRotation.LinearSums

namespace BlockCycleRotation

open Real Finset

/-- The character expansion of the indicator of `y' ≡ a mod x`. -/
theorem indicator_eq {x : ℕ} (hx : 0 < x) (a : ℤ) (y' : ℕ) :
    (if (x : ℤ) ∣ ((y' : ℤ) - a) then (1 : ℂ) else 0)
      = (1 / (x : ℂ)) * ∑ b ∈ Finset.range x,
          e (2 * π * (b : ℝ) / x) ^ y' * e (-(2 * π * (b : ℝ) * (a : ℝ) / x)) := by
  have hane : (x : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hx.ne'
  have hkey := sum_e_root hx ((y' : ℤ) - a)
  have hterm : ∀ b ∈ Finset.range x,
      (e (2 * π * (((y' : ℤ) - a : ℤ) : ℝ) / x)) ^ b
        = e (2 * π * (b : ℝ) / x) ^ y' * e (-(2 * π * (b : ℝ) * (a : ℝ) / x)) := by
    intro b _
    rw [e_pow, e_pow, ← e_add]
    congr 1
    push_cast
    ring
  rw [Finset.sum_congr rfl hterm] at hkey
  rw [hkey]
  by_cases hd : (x : ℤ) ∣ ((y' : ℤ) - a)
  · rw [if_pos hd, if_pos hd]
    field_simp
  · rw [if_neg hd, if_neg hd]
    simp

/-- **The character expansion of a sum over an arithmetic progression.**
The `b = 0` term is the main term; the rest is the error. -/
theorem sum_ap_eq {x : ℕ} (hx : 0 < x) (a : ℤ) (A B : ℂ) (Y : ℕ) :
    (∑ y' ∈ Finset.Ico 1 Y, if (x : ℤ) ∣ ((y' : ℤ) - a) then (A + B * y') else 0)
      = (1 / (x : ℂ)) * ((∑ y' ∈ Finset.Ico 1 Y, (A + B * y'))
          + ∑ b ∈ Finset.Ico 1 x, e (-(2 * π * (b : ℝ) * (a : ℝ) / x))
              * ∑ y' ∈ Finset.Ico 1 Y, (A + B * y') * e (2 * π * (b : ℝ) / x) ^ y') := by
  have pointwise : ∀ y' ∈ Finset.Ico 1 Y,
      (if (x : ℤ) ∣ ((y' : ℤ) - a) then (A + B * y') else 0)
        = ∑ b ∈ Finset.range x, (1 / (x : ℂ)) * ((A + B * y')
            * (e (2 * π * (b : ℝ) / x) ^ y' * e (-(2 * π * (b : ℝ) * (a : ℝ) / x)))) := by
    intro y' _
    have hite : (if (x : ℤ) ∣ ((y' : ℤ) - a) then (A + B * y') else 0)
        = (A + B * y') * (if (x : ℤ) ∣ ((y' : ℤ) - a) then (1 : ℂ) else 0) := by
      by_cases hd : (x : ℤ) ∣ ((y' : ℤ) - a) <;> simp [hd]
    rw [hite, indicator_eq hx a y', Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [Finset.sum_congr rfl pointwise, Finset.sum_comm]
  have inner : ∀ b : ℕ,
      (∑ y' ∈ Finset.Ico 1 Y, (1 / (x : ℂ)) * ((A + B * y')
          * (e (2 * π * (b : ℝ) / x) ^ y' * e (-(2 * π * (b : ℝ) * (a : ℝ) / x)))))
        = (1 / (x : ℂ)) * (e (-(2 * π * (b : ℝ) * (a : ℝ) / x))
            * ∑ y' ∈ Finset.Ico 1 Y, (A + B * y') * e (2 * π * (b : ℝ) / x) ^ y') := by
    intro b
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun y' _ => by ring
  rw [Finset.sum_congr rfl (fun b _ => inner b), ← Finset.mul_sum,
    Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hx]
  congr 2
  · simp [e_zero]

/-- **Sums over an arithmetic progression.**  Replacing the sum by its expected
value costs a harmonic sum, i.e. `O(log x)`. -/
theorem sum_ap_sub_main_le {x : ℕ} (hx : 0 < x) (a : ℤ) (A B : ℂ) (Y : ℕ) :
    ‖(∑ y' ∈ Finset.Ico 1 Y, if (x : ℤ) ∣ ((y' : ℤ) - a) then (A + B * y') else 0)
        - (1 / (x : ℂ)) * ∑ y' ∈ Finset.Ico 1 Y, (A + B * y')‖
      ≤ (‖A‖ + ‖B‖ * (Y - 1 : ℕ)) * ∑ b ∈ Finset.Ico 1 x, (1 : ℝ) / (b : ℝ) := by
  have hapos : (0 : ℝ) < x := by exact_mod_cast hx
  have hane : (x : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hx.ne'
  rw [sum_ap_eq hx a A B Y]
  have hsub : (1 / (x : ℂ)) * ((∑ y' ∈ Finset.Ico 1 Y, (A + B * y'))
        + ∑ b ∈ Finset.Ico 1 x, e (-(2 * π * (b : ℝ) * (a : ℝ) / x))
            * ∑ y' ∈ Finset.Ico 1 Y, (A + B * y') * e (2 * π * (b : ℝ) / x) ^ y')
      - (1 / (x : ℂ)) * ∑ y' ∈ Finset.Ico 1 Y, (A + B * y')
      = (1 / (x : ℂ)) * ∑ b ∈ Finset.Ico 1 x, e (-(2 * π * (b : ℝ) * (a : ℝ) / x))
            * ∑ y' ∈ Finset.Ico 1 Y, (A + B * y') * e (2 * π * (b : ℝ) / x) ^ y' := by
    ring
  rw [hsub, norm_mul, norm_div, norm_one, Complex.norm_natCast]
  have hbound := norm_sum_twisted_le (x := x) A B Y
    (fun b => e (-(2 * π * (b : ℝ) * (a : ℝ) / x))) (fun b => le_of_eq (norm_e _))
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hapos]
  calc ‖∑ b ∈ Finset.Ico 1 x, e (-(2 * π * (b : ℝ) * (a : ℝ) / x))
          * ∑ y' ∈ Finset.Ico 1 Y, (A + B * y') * e (2 * π * (b : ℝ) / x) ^ y'‖
      ≤ (‖A‖ + ‖B‖ * (Y - 1 : ℕ)) * (x : ℝ)
          * ∑ b ∈ Finset.Ico 1 x, (1 : ℝ) / (b : ℝ) := hbound
    _ = (‖A‖ + ‖B‖ * (Y - 1 : ℕ)) * (∑ b ∈ Finset.Ico 1 x, (1 : ℝ) / (b : ℝ)) * (x : ℝ) := by
        ring

/-! ## Making the `log x` explicit

The estimate above carries a raw harmonic sum.  Mathlib's
`harmonic_le_one_add_log` turns it into an explicit logarithm, which is the
shape §4 uses. -/

/-- `∑_{0<b<x} 1/b ≤ 1 + log x`. -/
theorem sum_inv_le_one_add_log (x : ℕ) :
    ∑ b ∈ Finset.Ico 1 x, (1 : ℝ) / (b : ℝ) ≤ 1 + Real.log x := by
  have hsub : Finset.Ico 1 x ⊆ Finset.Icc 1 x := by
    intro u hu
    rw [Finset.mem_Ico] at hu
    rw [Finset.mem_Icc]
    omega
  have h1 : ∑ b ∈ Finset.Ico 1 x, (1 : ℝ) / (b : ℝ)
      ≤ ∑ b ∈ Finset.Icc 1 x, (1 : ℝ) / (b : ℝ) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
    intro i _ _
    positivity
  have h2 : ((harmonic x : ℚ) : ℝ) = ∑ b ∈ Finset.Icc 1 x, (1 : ℝ) / (b : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    exact Finset.sum_congr rfl fun i _ => by simp [one_div]
  calc ∑ b ∈ Finset.Ico 1 x, (1 : ℝ) / (b : ℝ)
      ≤ ∑ b ∈ Finset.Icc 1 x, (1 : ℝ) / (b : ℝ) := h1
    _ = ((harmonic x : ℚ) : ℝ) := h2.symm
    _ ≤ 1 + Real.log x := harmonic_le_one_add_log x

/-- **Sums over an arithmetic progression, with an explicit logarithm.**

Replacing the sum by its expected value costs `O(log x)`. -/
theorem sum_ap_sub_main_le_log {x : ℕ} (hx : 0 < x) (a : ℤ) (A B : ℂ) (Y : ℕ) :
    ‖(∑ y' ∈ Finset.Ico 1 Y, if (x : ℤ) ∣ ((y' : ℤ) - a) then (A + B * y') else 0)
        - (1 / (x : ℂ)) * ∑ y' ∈ Finset.Ico 1 Y, (A + B * y')‖
      ≤ (‖A‖ + ‖B‖ * (Y - 1 : ℕ)) * (1 + Real.log x) := by
  refine (sum_ap_sub_main_le hx a A B Y).trans ?_
  have hK : (0 : ℝ) ≤ ‖A‖ + ‖B‖ * (Y - 1 : ℕ) := by positivity
  exact mul_le_mul_of_nonneg_left (sum_inv_le_one_add_log x) hK

end BlockCycleRotation
