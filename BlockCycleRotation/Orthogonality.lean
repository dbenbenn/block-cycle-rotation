/-
# Additive character orthogonality

Section 4 detects the congruence `b ≡ c mod a` by averaging the additive
characters `b ↦ e(2πmb/a)` over `m`.  The identity that makes this work is

  `∑_{m < a} e(2πmr/a) = a` if `a ∣ r`, and `0` otherwise,

which is just the geometric series again: the ratio is an `a`-th root of unity,
equal to `1` exactly when `a ∣ r`, and otherwise the sum telescopes to zero.
-/

import BlockCycleRotation.Characters

namespace BlockCycleRotation

open Real Finset

@[simp]
theorem e_zero : e 0 = 1 := by simp [e]

/-- `e` turns multiplication by a natural number into a power. -/
theorem e_pow (θ : ℝ) (n : ℕ) : e θ ^ n = e (n * θ) := by
  rw [e, e, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- `e θ = 1` exactly on the integer multiples of `2π`. -/
theorem e_eq_one_iff (θ : ℝ) : e θ = 1 ↔ ∃ n : ℤ, θ = 2 * π * n := by
  rw [e, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hn' : ((θ : ℝ) : ℂ) * Complex.I = ((2 * π * (n : ℝ) : ℝ) : ℂ) * Complex.I := by
      rw [hn]; push_cast; ring
    have h2 := mul_right_cancel₀ Complex.I_ne_zero hn'
    exact_mod_cast h2
  · rintro ⟨n, hn⟩
    exact ⟨n, by rw [hn]; push_cast; ring⟩

/-- **Orthogonality.**  `∑_{m < a} e(2πmr/a)` is `a` when `a ∣ r` and `0` otherwise. -/
theorem sum_e_root {a : ℕ} (ha : 0 < a) (r : ℤ) :
    ∑ _m ∈ Finset.range a, (e (2 * π * r / a)) ^ _m
      = if (a : ℤ) ∣ r then (a : ℂ) else 0 := by
  have hane : ((a : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 ha.ne'
  have hpi : (2 : ℝ) * π ≠ 0 := by have := Real.pi_pos; positivity
  by_cases hd : (a : ℤ) ∣ r
  · rw [if_pos hd]
    obtain ⟨t, ht⟩ := hd
    have hx : e (2 * π * (r : ℝ) / a) = 1 := by
      rw [e_eq_one_iff]
      refine ⟨t, ?_⟩
      have hr : (r : ℝ) = (a : ℝ) * (t : ℝ) := by
        exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) ht
      rw [hr]
      field_simp
    rw [hx]
    simp
  · rw [if_neg hd]
    have hx1 : e (2 * π * (r : ℝ) / a) ≠ 1 := by
      intro hcon
      rw [e_eq_one_iff] at hcon
      obtain ⟨n, hn⟩ := hcon
      refine hd ⟨n, ?_⟩
      rw [div_eq_iff hane] at hn
      have hcancel : (2 * π) * (r : ℝ) = (2 * π) * ((a : ℝ) * (n : ℝ)) := by
        calc (2 * π) * (r : ℝ) = 2 * π * (r : ℝ) := by ring
          _ = 2 * π * (n : ℝ) * a := hn
          _ = (2 * π) * ((a : ℝ) * (n : ℝ)) := by ring
      have h2 : (r : ℝ) = (a : ℝ) * (n : ℝ) := mul_left_cancel₀ hpi hcancel
      exact_mod_cast h2
    have hxa : e (2 * π * (r : ℝ) / a) ^ a = 1 := by
      rw [e_pow]
      have hcalc : (a : ℝ) * (2 * π * (r : ℝ) / a) = 2 * π * (r : ℝ) := by
        field_simp
      rw [hcalc, e_eq_one_iff]
      exact ⟨r, rfl⟩
    rw [geom_sum_eq hx1, hxa]
    simp

end BlockCycleRotation
