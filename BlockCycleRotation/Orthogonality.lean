/-
# Additive character orthogonality

Section 4 detects the congruence `y' ≡ a mod x` by averaging the additive
characters `y' ↦ e(2πmb/x)` over `b`.  The identity that makes this work is

  `∑_{b < x} e(2πmr/x) = x` if `x ∣ r`, and `0` otherwise,

which is just the geometric series again: the ratio is an `x`-th root of unity,
equal to `1` exactly when `x ∣ r`, and otherwise the sum telescopes to zero.
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

/-- **Orthogonality.**  `∑_{b < x} e(2πmr/x)` is `x` when `x ∣ r` and `0` otherwise. -/
theorem sum_e_root {x : ℕ} (hx : 0 < x) (r : ℤ) :
    ∑ _b ∈ Finset.range x, (e (2 * π * r / x)) ^ _b
      = if (x : ℤ) ∣ r then (x : ℂ) else 0 := by
  have hane : ((x : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hx.ne'
  have hpi : (2 : ℝ) * π ≠ 0 := by have := Real.pi_pos; positivity
  by_cases hd : (x : ℤ) ∣ r
  · rw [if_pos hd]
    obtain ⟨t, ht⟩ := hd
    have he : e (2 * π * (r : ℝ) / x) = 1 := by
      rw [e_eq_one_iff]
      refine ⟨t, ?_⟩
      have hr : (r : ℝ) = (x : ℝ) * (t : ℝ) := by
        exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) ht
      rw [hr]
      field_simp
    rw [he]
    simp
  · rw [if_neg hd]
    have he1 : e (2 * π * (r : ℝ) / x) ≠ 1 := by
      intro hcon
      rw [e_eq_one_iff] at hcon
      obtain ⟨n, hn⟩ := hcon
      refine hd ⟨n, ?_⟩
      rw [div_eq_iff hane] at hn
      have hcancel : (2 * π) * (r : ℝ) = (2 * π) * ((x : ℝ) * (n : ℝ)) := by
        calc (2 * π) * (r : ℝ) = 2 * π * (r : ℝ) := by ring
          _ = 2 * π * (n : ℝ) * x := hn
          _ = (2 * π) * ((x : ℝ) * (n : ℝ)) := by ring
      have h2 : (r : ℝ) = (x : ℝ) * (n : ℝ) := mul_left_cancel₀ hpi hcancel
      exact_mod_cast h2
    have hxa : e (2 * π * (r : ℝ) / x) ^ x = 1 := by
      rw [e_pow]
      have hcalc : (x : ℝ) * (2 * π * (r : ℝ) / x) = 2 * π * (r : ℝ) := by
        field_simp
      rw [hcalc, e_eq_one_iff]
      exact ⟨r, rfl⟩
    rw [geom_sum_eq he1, hxa]
    simp

end BlockCycleRotation
