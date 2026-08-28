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

/-! ## The tail bound

`∑_{a > N} 1/a² ≤ 1/N`, by telescoping against `1/(a-1) - 1/a`.  Mathlib has the
summability of the `p`-series but no tail estimate, so this is proved here. -/

/-- Telescoping: `∑_{N < a ≤ M} 1/a² ≤ 1/N - 1/M`. -/
theorem sum_inv_sq_Ioc_le {N : ℕ} (hN : 0 < N) :
    ∀ M, N ≤ M → ∑ a ∈ Finset.Ioc N M, 1 / ((a : ℝ) ^ 2) ≤ 1 / (N : ℝ) - 1 / (M : ℝ) := by
  intro M hNM
  induction M, hNM using Nat.le_induction with
  | base => simp
  | succ M hNM ih =>
    rw [Finset.sum_Ioc_succ_top hNM]
    have hM : (1 : ℝ) ≤ (M : ℝ) := by
      have h : 1 ≤ M := by omega
      exact_mod_cast h
    have hstep : 1 / (((M + 1 : ℕ) : ℝ)) ^ 2 ≤ 1 / (M : ℝ) - 1 / (((M + 1 : ℕ) : ℝ)) := by
      push_cast
      have h1 : 1 / (M : ℝ) - 1 / ((M : ℝ) + 1) = 1 / ((M : ℝ) * ((M : ℝ) + 1)) := by
        field_simp
        ring
      rw [h1, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith

/-- For any finite set of integers beyond `N`, the sum of `1/a²` is at most `1/N`. -/
theorem sum_inv_sq_tail_le {N : ℕ} (hN : 0 < N) (s : Finset ℕ) (hs : ∀ a ∈ s, N < a) :
    ∑ a ∈ s, 1 / ((a : ℝ) ^ 2) ≤ 1 / (N : ℝ) := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp
  · have hM : N ≤ s.max' hne := le_of_lt (hs _ (s.max'_mem hne))
    have hsub : s ⊆ Finset.Ioc N (s.max' hne) := by
      intro a ha
      simp only [Finset.mem_Ioc]
      exact ⟨hs a ha, Finset.le_max' s a ha⟩
    calc ∑ a ∈ s, 1 / ((a : ℝ) ^ 2)
        ≤ ∑ a ∈ Finset.Ioc N (s.max' hne), 1 / ((a : ℝ) ^ 2) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ ≤ 1 / (N : ℝ) - 1 / ((s.max' hne : ℕ) : ℝ) := sum_inv_sq_Ioc_le hN _ hM
      _ ≤ 1 / (N : ℝ) := by
          have : (0 : ℝ) ≤ 1 / ((s.max' hne : ℕ) : ℝ) := by positivity
          linarith

/-- The row sums are summable. -/
theorem cRow_summable : Summable (fun a : ℕ => ∑ a' ∈ Finset.range a, cTerm (a, a')) := by
  have hg : Summable (fun a : ℕ => 3 / (2 * (a : ℝ) ^ 2)) := by
    have h : Summable (fun a : ℕ => 1 / (a : ℝ) ^ 2) := by
      rw [Real.summable_one_div_nat_pow]
      norm_num
    refine (h.mul_left (3 / 2)).congr fun a => ?_
    rw [div_mul_eq_mul_div, mul_one_div]
    ring_nf
  refine Summable.of_nonneg_of_le (fun a => ?_) cTerm_row_le hg
  exact Finset.sum_nonneg fun a' _ => cTerm_nonneg _

/-- **The tail bound for `C`.**  Truncating the series at `a ≤ N` loses at most
`3/(2N)`. -/
theorem cConst_le_partial_add {N : ℕ} (hN : 0 < N) :
    cConst ≤ (∑ a ∈ Finset.range (N + 1), ∑ a' ∈ Finset.range a, cTerm (a, a'))
      + 3 / (2 * (N : ℝ)) := by
  rw [cConst_eq_tsum_finRows]
  refine Real.tsum_le_of_sum_le
    (fun a => Finset.sum_nonneg fun a' _ => cTerm_nonneg _) fun s => ?_
  classical
  have hsplit : ∑ a ∈ s, (∑ a' ∈ Finset.range a, cTerm (a, a'))
      = (∑ a ∈ s.filter (fun a => a ≤ N), ∑ a' ∈ Finset.range a, cTerm (a, a'))
        + ∑ a ∈ s.filter (fun a => ¬ a ≤ N), ∑ a' ∈ Finset.range a, cTerm (a, a') :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hlow : (∑ a ∈ s.filter (fun a => a ≤ N), ∑ a' ∈ Finset.range a, cTerm (a, a'))
      ≤ ∑ a ∈ Finset.range (N + 1), ∑ a' ∈ Finset.range a, cTerm (a, a') := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_
      (fun a _ _ => Finset.sum_nonneg fun a' _ => cTerm_nonneg _)
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_range] at ha ⊢
    omega
  have hhigh : (∑ a ∈ s.filter (fun a => ¬ a ≤ N), ∑ a' ∈ Finset.range a, cTerm (a, a'))
      ≤ 3 / (2 * (N : ℝ)) := by
    have h1 : (∑ a ∈ s.filter (fun a => ¬ a ≤ N), ∑ a' ∈ Finset.range a, cTerm (a, a'))
        ≤ ∑ a ∈ s.filter (fun a => ¬ a ≤ N), 3 / (2 * (a : ℝ) ^ 2) :=
      Finset.sum_le_sum fun a _ => cTerm_row_le a
    have h2 : (∑ a ∈ s.filter (fun a => ¬ a ≤ N), 3 / (2 * (a : ℝ) ^ 2))
        = (3 / 2) * ∑ a ∈ s.filter (fun a => ¬ a ≤ N), 1 / ((a : ℝ) ^ 2) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [div_mul_eq_mul_div, mul_one_div]
      ring_nf
    have h3 : (∑ a ∈ s.filter (fun a => ¬ a ≤ N), 1 / ((a : ℝ) ^ 2)) ≤ 1 / (N : ℝ) := by
      refine sum_inv_sq_tail_le hN _ fun a ha => ?_
      simp only [Finset.mem_filter] at ha
      omega
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    rw [h2] at h1
    have : (3 / 2 : ℝ) * (1 / (N : ℝ)) = 3 / (2 * (N : ℝ)) := by field_simp
    nlinarith [h1, h3]
  rw [hsplit]
  linarith

/-- **The truncation bound.**  Restricting the series for `C` to the bulk pairs
loses at most `3/(2N)`, provided every pair with `a ≤ N` lies in the bulk. -/
theorem cConst_le_bulk_add {m d N : ℕ} (hN : 0 < N)
    (hbulk : ∀ a a', a ≤ N → 1 ≤ a' → a' < a → d * a * (a + a') ≤ m) :
    cConst ≤ (∑ a ∈ Finset.range (N + 1), ∑ a' ∈ Finset.range a,
        if d * a * (a + a') ≤ m then cTerm (a, a') else 0) + 3 / (2 * (N : ℝ)) := by
  refine le_trans (cConst_le_partial_add hN) ?_
  have heq : ∀ a ∈ Finset.range (N + 1), ∑ a' ∈ Finset.range a, cTerm (a, a')
      = ∑ a' ∈ Finset.range a, if d * a * (a + a') ≤ m then cTerm (a, a') else 0 := by
    intro a ha
    simp only [Finset.mem_range, Nat.lt_succ_iff] at ha
    refine Finset.sum_congr rfl fun a' ha' => ?_
    simp only [Finset.mem_range] at ha'
    rcases Nat.eq_zero_or_pos a' with h0 | h0
    · subst h0
      have hz : cTerm (a, 0) = 0 := by
        unfold cTerm
        rw [if_neg]
        rintro ⟨h1, -, -⟩
        omega
      simp [hz]
    · rw [if_pos (hbulk a a' ha h0 ha')]
  rw [Finset.sum_congr rfl heq]


/-! ## The substitution of Lemma 17

Substituting the paper's coefficients `A = d·a + m/a`, `B = -a'/a` and the real
bound `V = m/(a+a')` into the main term `(1/a)(A·V + B·V²/2)` gives

```
d·m/(a+a')  +  m² · cTerm(a, a').
```

The first term is lower order; the second is what sums to `m²·C`.  This is the
step where the constant appears. -/

/-- **The substitution.**  The main term at a coprime pair is
`d·m/(a+a') + m²·cTerm(a,a')`. -/
theorem main_term_substitute {m d a a' : ℕ} (h1 : 1 ≤ a') (h2 : a' < a)
    (h3 : Nat.gcd a a' = 1) :
    (1 / (a : ℝ)) * ((((d * a : ℕ) : ℝ) + (m : ℝ) / (a : ℝ)) * ((m : ℝ) / ((a : ℝ) + (a' : ℝ)))
        + (-(a' : ℝ) / (a : ℝ)) * ((m : ℝ) / ((a : ℝ) + (a' : ℝ))) ^ 2 / 2)
      = (d : ℝ) * (m : ℝ) / ((a : ℝ) + (a' : ℝ)) + (m : ℝ) ^ 2 * cTerm (a, a') := by
  have ha : (0 : ℝ) < (a : ℝ) := by
    have : 0 < a := by omega
    exact_mod_cast this
  have ha'0 : (0 : ℝ) ≤ (a' : ℝ) := by positivity
  have haa : (0 : ℝ) < (a : ℝ) + (a' : ℝ) := by linarith
  unfold cTerm
  rw [if_pos ⟨h1, h2, h3⟩]
  push_cast
  field_simp
  ring

/-! ## Assembling the main term

After substitution the main term splits into a lower-order part
`d·m·∑ 1/(a+a')` and `m²` times a partial sum of the series for `C`.  The latter
is squeezed between `C - 3/(2N)` and `C`. -/

/-- **The main term splits.** -/
theorem G1_split (m d : ℕ) (s : Finset (ℕ × ℕ)) :
    ∑ p ∈ s, ((d : ℝ) * (m : ℝ) / ((p.1 : ℝ) + (p.2 : ℝ)) + (m : ℝ) ^ 2 * cTerm p)
      = (∑ p ∈ s, (d : ℝ) * (m : ℝ) / ((p.1 : ℝ) + (p.2 : ℝ)))
        + (m : ℝ) ^ 2 * ∑ p ∈ s, cTerm p := by
  rw [Finset.sum_add_distrib, Finset.mul_sum]

/-- **Any partial sum of the series is at most `C`.** -/
theorem sum_cTerm_le_cConst (s : Finset (ℕ × ℕ)) : ∑ p ∈ s, cTerm p ≤ cConst :=
  Summable.sum_le_tsum s (fun p _ => cTerm_nonneg p) cTerm_summable

/-- **The partial sum over the bulk is squeezed.**  Together with
`cConst_le_bulk_add`, the bulk partial sum of `cTerm` lies within `3/(2N)` of
`C`, so `m²` times it lies within `m²·3/(2N)` of `m²·C`.  With
`N = √(m/(2d))` that error is `O(m^{3/2}√d)`, matching the small part. -/
theorem bulk_sum_close {m d N : ℕ} (hN : 0 < N)
    (hbulk : ∀ a a', a ≤ N → 1 ≤ a' → a' < a → d * a * (a + a') ≤ m) :
    cConst - 3 / (2 * (N : ℝ))
      ≤ ∑ a ∈ Finset.range (N + 1), ∑ a' ∈ Finset.range a,
          (if d * a * (a + a') ≤ m then cTerm (a, a') else 0) := by
  have h := cConst_le_bulk_add hN hbulk
  linarith

end BlockCycleRotation
