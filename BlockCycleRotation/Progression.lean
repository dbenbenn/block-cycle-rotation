/-
# Sums over an arithmetic progression

This closes the loop on §4's key manoeuvre.  `Orthogonality.lean` supplies the
character expansion of the congruence `b ≡ c mod a`, and `LinearSums.lean`
bounds the resulting twisted sums.  Here the two are combined: the phases
`e(-2πmc/a)`, previously abstracted as arbitrary weights of modulus one, are
instantiated, giving

  `‖∑_{1≤b<T, b≡c mod a} (A + B·b)  −  (1/a)·∑_{1≤b<T} (A + B·b)‖`
      `≤ (‖A‖ + ‖B‖(T-1)) · ∑_{0<m<a} 1/m`.

That is: replacing a sum over an arithmetic progression by its expected value
costs a harmonic sum, which is `O(log a)`.
-/

import BlockCycleRotation.LinearSums

namespace BlockCycleRotation

open Real Finset

/-- The character expansion of the indicator of `b ≡ c mod a`. -/
theorem indicator_eq {a : ℕ} (ha : 0 < a) (c : ℤ) (b : ℕ) :
    (if (a : ℤ) ∣ ((b : ℤ) - c) then (1 : ℂ) else 0)
      = (1 / (a : ℂ)) * ∑ m ∈ Finset.range a,
          e (2 * π * (m : ℝ) / a) ^ b * e (-(2 * π * (m : ℝ) * (c : ℝ) / a)) := by
  have hane : (a : ℂ) ≠ 0 := Nat.cast_ne_zero.2 ha.ne'
  have hkey := sum_e_root ha ((b : ℤ) - c)
  have hterm : ∀ m ∈ Finset.range a,
      (e (2 * π * (((b : ℤ) - c : ℤ) : ℝ) / a)) ^ m
        = e (2 * π * (m : ℝ) / a) ^ b * e (-(2 * π * (m : ℝ) * (c : ℝ) / a)) := by
    intro m _
    rw [e_pow, e_pow, ← e_add]
    congr 1
    push_cast
    ring
  rw [Finset.sum_congr rfl hterm] at hkey
  rw [hkey]
  by_cases hd : (a : ℤ) ∣ ((b : ℤ) - c)
  · rw [if_pos hd, if_pos hd]
    field_simp
  · rw [if_neg hd, if_neg hd]
    simp

/-- **The character expansion of a sum over an arithmetic progression.**
The `m = 0` term is the main term; the rest is the error. -/
theorem sum_ap_eq {a : ℕ} (ha : 0 < a) (c : ℤ) (A B : ℂ) (T : ℕ) :
    (∑ b ∈ Finset.Ico 1 T, if (a : ℤ) ∣ ((b : ℤ) - c) then (A + B * b) else 0)
      = (1 / (a : ℂ)) * ((∑ b ∈ Finset.Ico 1 T, (A + B * b))
          + ∑ m ∈ Finset.Ico 1 a, e (-(2 * π * (m : ℝ) * (c : ℝ) / a))
              * ∑ b ∈ Finset.Ico 1 T, (A + B * b) * e (2 * π * (m : ℝ) / a) ^ b) := by
  have pointwise : ∀ b ∈ Finset.Ico 1 T,
      (if (a : ℤ) ∣ ((b : ℤ) - c) then (A + B * b) else 0)
        = ∑ m ∈ Finset.range a, (1 / (a : ℂ)) * ((A + B * b)
            * (e (2 * π * (m : ℝ) / a) ^ b * e (-(2 * π * (m : ℝ) * (c : ℝ) / a)))) := by
    intro b _
    have hite : (if (a : ℤ) ∣ ((b : ℤ) - c) then (A + B * b) else 0)
        = (A + B * b) * (if (a : ℤ) ∣ ((b : ℤ) - c) then (1 : ℂ) else 0) := by
      by_cases hd : (a : ℤ) ∣ ((b : ℤ) - c) <;> simp [hd]
    rw [hite, indicator_eq ha c b, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [Finset.sum_congr rfl pointwise, Finset.sum_comm]
  have inner : ∀ m : ℕ,
      (∑ b ∈ Finset.Ico 1 T, (1 / (a : ℂ)) * ((A + B * b)
          * (e (2 * π * (m : ℝ) / a) ^ b * e (-(2 * π * (m : ℝ) * (c : ℝ) / a)))))
        = (1 / (a : ℂ)) * (e (-(2 * π * (m : ℝ) * (c : ℝ) / a))
            * ∑ b ∈ Finset.Ico 1 T, (A + B * b) * e (2 * π * (m : ℝ) / a) ^ b) := by
    intro m
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [Finset.sum_congr rfl (fun m _ => inner m), ← Finset.mul_sum,
    Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot ha]
  congr 2
  · simp [e_zero]

/-- **Sums over an arithmetic progression.**  Replacing the sum by its expected
value costs a harmonic sum, i.e. `O(log a)`. -/
theorem sum_ap_sub_main_le {a : ℕ} (ha : 0 < a) (c : ℤ) (A B : ℂ) (T : ℕ) :
    ‖(∑ b ∈ Finset.Ico 1 T, if (a : ℤ) ∣ ((b : ℤ) - c) then (A + B * b) else 0)
        - (1 / (a : ℂ)) * ∑ b ∈ Finset.Ico 1 T, (A + B * b)‖
      ≤ (‖A‖ + ‖B‖ * (T - 1 : ℕ)) * ∑ m ∈ Finset.Ico 1 a, (1 : ℝ) / (m : ℝ) := by
  have hapos : (0 : ℝ) < a := by exact_mod_cast ha
  have hane : (a : ℂ) ≠ 0 := Nat.cast_ne_zero.2 ha.ne'
  rw [sum_ap_eq ha c A B T]
  have hsub : (1 / (a : ℂ)) * ((∑ b ∈ Finset.Ico 1 T, (A + B * b))
        + ∑ m ∈ Finset.Ico 1 a, e (-(2 * π * (m : ℝ) * (c : ℝ) / a))
            * ∑ b ∈ Finset.Ico 1 T, (A + B * b) * e (2 * π * (m : ℝ) / a) ^ b)
      - (1 / (a : ℂ)) * ∑ b ∈ Finset.Ico 1 T, (A + B * b)
      = (1 / (a : ℂ)) * ∑ m ∈ Finset.Ico 1 a, e (-(2 * π * (m : ℝ) * (c : ℝ) / a))
            * ∑ b ∈ Finset.Ico 1 T, (A + B * b) * e (2 * π * (m : ℝ) / a) ^ b := by
    ring
  rw [hsub, norm_mul, norm_div, norm_one, Complex.norm_natCast]
  have hbound := norm_sum_twisted_le (a := a) A B T
    (fun m => e (-(2 * π * (m : ℝ) * (c : ℝ) / a))) (fun m => le_of_eq (norm_e _))
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hapos]
  calc ‖∑ m ∈ Finset.Ico 1 a, e (-(2 * π * (m : ℝ) * (c : ℝ) / a))
          * ∑ b ∈ Finset.Ico 1 T, (A + B * b) * e (2 * π * (m : ℝ) / a) ^ b‖
      ≤ (‖A‖ + ‖B‖ * (T - 1 : ℕ)) * (a : ℝ)
          * ∑ m ∈ Finset.Ico 1 a, (1 : ℝ) / (m : ℝ) := hbound
    _ = (‖A‖ + ‖B‖ * (T - 1 : ℕ)) * (∑ m ∈ Finset.Ico 1 a, (1 : ℝ) / (m : ℝ)) * (a : ℝ) := by
        ring

end BlockCycleRotation
