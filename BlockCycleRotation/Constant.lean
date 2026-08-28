/-
# The constant `C`

Equation (const-c) of Blomer--Bux defines

```
C = ∑_{a > a' ≥ 1, gcd(a,a') = 1}  (2a + a') / (2 a² (a+a')²),
```

an explicit double series over coprime pairs.  Its value is `≈ 0.2125`, and
`D = 1 + 4C ≈ 1.85`.

Note this is a plain convergent series: no integral is involved.  (Theorem 10 of
the paper separately identifies the limit as `∫₀¹ ρ`, but that representation
plays no part in computing `C`.)  Remark 21 rewrites `C` using Euler's
`ζ(2,1) = ζ(3)`; that rewriting is optional.

Convergence is by comparison: for `a' < a` the term is at most `3/(2a³)`, and
summing over the fewer than `a` admissible `a'` leaves `3/(2a²)`.
-/

import BlockCycleRotation.TripleSum

namespace BlockCycleRotation

/-- The summand of equation (const-c), extended by zero. -/
noncomputable def cTerm (p : ℕ × ℕ) : ℝ :=
  if 1 ≤ p.2 ∧ p.2 < p.1 ∧ Nat.gcd p.1 p.2 = 1 then
    (2 * (p.1 : ℝ) + (p.2 : ℝ)) / (2 * (p.1 : ℝ) ^ 2 * ((p.1 : ℝ) + (p.2 : ℝ)) ^ 2)
  else 0

theorem cTerm_nonneg (p : ℕ × ℕ) : 0 ≤ cTerm p := by
  unfold cTerm
  split
  · positivity
  · exact le_refl 0

/-- **Termwise bound.**  Each term is at most `3 / (2a³)`. -/
theorem cTerm_le (p : ℕ × ℕ) : cTerm p ≤ 3 / (2 * (p.1 : ℝ) ^ 3) := by
  unfold cTerm
  split
  · rename_i h
    obtain ⟨h1, h2, -⟩ := h
    have hp1 : (0 : ℝ) < (p.1 : ℝ) := by
      have : 0 < p.1 := by omega
      exact_mod_cast this
    have hp2 : (0 : ℝ) ≤ (p.2 : ℝ) := by positivity
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pow_pos hp1 4, mul_nonneg (pow_nonneg hp1.le 3) hp2,
      mul_nonneg (pow_nonneg hp1.le 2) (mul_nonneg hp2 hp2)]
  · positivity

/-- The number of admissible `a'` for a given `a` is less than `a`, so the
row sums are at most `3 / (2a²)`. -/
theorem cTerm_row_le (a : ℕ) :
    ∑ a' ∈ Finset.range a, cTerm (a, a') ≤ 3 / (2 * (a : ℝ) ^ 2) := by
  rcases Nat.eq_zero_or_pos a with h0 | h0
  · subst h0
    simp
  · have ha : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast h0
    calc ∑ a' ∈ Finset.range a, cTerm (a, a')
        ≤ ∑ _a' ∈ Finset.range a, 3 / (2 * (a : ℝ) ^ 3) :=
          Finset.sum_le_sum fun a' _ => cTerm_le (a, a')
      _ = (a : ℝ) * (3 / (2 * (a : ℝ) ^ 3)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = 3 / (2 * (a : ℝ) ^ 2) := by
          field_simp

/-! ## Convergence -/

/-- Each row is supported on `a' < a`. -/
theorem cTerm_row_support (a a' : ℕ) (h : a' ∉ Finset.range a) : cTerm (a, a') = 0 := by
  simp only [Finset.mem_range, not_lt] at h
  unfold cTerm
  rw [if_neg]
  rintro ⟨-, h2, -⟩
  exact absurd h2 (by omega)

theorem cTerm_row_summable (a : ℕ) : Summable (fun a' => cTerm (a, a')) :=
  summable_of_ne_finset_zero (s := Finset.range a) (cTerm_row_support a)

theorem cTerm_row_tsum_le (a : ℕ) : ∑' a', cTerm (a, a') ≤ 3 / (2 * (a : ℝ) ^ 2) := by
  rw [tsum_eq_sum (s := Finset.range a) (cTerm_row_support a)]
  exact cTerm_row_le a

/-- **The series for `C` converges.** -/
theorem cTerm_summable : Summable cTerm := by
  rw [summable_prod_of_nonneg (fun p => cTerm_nonneg p)]
  refine ⟨cTerm_row_summable, ?_⟩
  have hg : Summable (fun a : ℕ => 3 / (2 * (a : ℝ) ^ 2)) := by
    have h : Summable (fun a : ℕ => 1 / (a : ℝ) ^ 2) := by
      rw [Real.summable_one_div_nat_pow]
      norm_num
    refine (h.mul_left (3 / 2)).congr fun a => ?_
    rw [div_mul_eq_mul_div, mul_one_div]
    ring_nf
  refine Summable.of_nonneg_of_le (fun a => ?_) cTerm_row_tsum_le hg
  exact tsum_nonneg fun a' => cTerm_nonneg _

/-- **The constant `C`** of equation (const-c). -/
noncomputable def cConst : ℝ := ∑' p : ℕ × ℕ, cTerm p

theorem cConst_nonneg : 0 ≤ cConst :=
  tsum_nonneg fun p => cTerm_nonneg p

/-- **The constant `D = 1 + 4C`** of Theorem A and Theorem 13.

Numerically, truncating the series for `C` at `a ≤ 20000` gives
`C ≈ 0.21138` and `D ≈ 1.8455`, consistent with the paper's `D ≈ 1.85`.
(The tail is `O(1/N)`, so the truncation converges slowly.) -/
noncomputable def dConst : ℝ := 1 + 4 * cConst

/-! ## The summand of Lemma 17

The bulk part of `G₁` in the paper's proof of Lemma 17 has summand

```
n²/(d²a²(a+a'))  -  n²a'/(2a²d²(a+a')²)  =  (n²/d²) · (2a + a')/(2a²(a+a')²),
```

so the coefficient is exactly `cTerm`.  This is the algebraic identity that
makes `C` appear. -/

/-- **The summand identity.**  `1/(a²(a+a')) - a'/(2a²(a+a')²) = (2a+a')/(2a²(a+a')²)`. -/
theorem cTerm_summand_eq {a a' : ℝ} (ha : a ≠ 0) (haa : a + a' ≠ 0) :
    1 / (a ^ 2 * (a + a')) - a' / (2 * a ^ 2 * (a + a') ^ 2)
      = (2 * a + a') / (2 * a ^ 2 * (a + a') ^ 2) := by
  field_simp
  ring

/-- The value of `cTerm` on an admissible pair, in the paper's split form. -/
theorem cTerm_eq_of_mem {a a' : ℕ} (h1 : 1 ≤ a') (h2 : a' < a) (h3 : Nat.gcd a a' = 1) :
    cTerm (a, a')
      = 1 / ((a : ℝ) ^ 2 * ((a : ℝ) + a')) - (a' : ℝ) / (2 * (a : ℝ) ^ 2 * ((a : ℝ) + a') ^ 2) := by
  have ha : (a : ℝ) ≠ 0 := by
    have : 0 < a := by omega
    positivity
  have haa : (a : ℝ) + (a' : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (a : ℝ) := by
      have : 0 < a := by omega
      exact_mod_cast this
    have : (0 : ℝ) ≤ (a' : ℝ) := by positivity
    positivity
  rw [cTerm_summand_eq ha haa]
  unfold cTerm
  rw [if_pos ⟨h1, h2, h3⟩]

/-- `C` as an iterated sum: first over `a'`, then over `a`. -/
theorem cConst_eq_tsum_rows : cConst = ∑' a : ℕ, ∑' a' : ℕ, cTerm (a, a') :=
  cTerm_summable.tsum_prod

/-- `C` as a sum of finite rows. -/
theorem cConst_eq_tsum_finRows : cConst = ∑' a : ℕ, ∑ a' ∈ Finset.range a, cTerm (a, a') := by
  rw [cConst_eq_tsum_rows]
  refine tsum_congr fun a => ?_
  exact tsum_eq_sum (s := Finset.range a) (cTerm_row_support a)

end BlockCycleRotation
