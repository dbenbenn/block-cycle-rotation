/-
# The constant `C`

Equation (const-c) of Blomer--Bux defines

```
C = ∑_{x > y ≥ 1, gcd(x,y) = 1}  (2x + y) / (2 x² (x+y)²),
```

an explicit double series over coprime pairs.  Its value is `≈ 0.2125`, and
`D = 1 + 4C ≈ 1.85`.

Note this is a plain convergent series: no integral is involved.  (Theorem 9 of
the paper separately identifies the limit as `∫₀¹ ρ`, but that representation
plays no part in computing `C`.)  Remark 21 rewrites `C` using Euler's
`ζ(2,1) = ζ(3)`; that rewriting is optional.

Convergence is by comparison: for `y < x` the term is at most `3/(2x³)`, and
summing over the fewer than `x` admissible `y` leaves `3/(2x²)`.
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

/-- The number of admissible `y` for a given `x` is less than `x`, so the
row sums are at most `3 / (2x²)`. -/
theorem cTerm_row_le (x : ℕ) :
    ∑ y ∈ Finset.range x, cTerm (x, y) ≤ 3 / (2 * (x : ℝ) ^ 2) := by
  rcases Nat.eq_zero_or_pos x with h0 | h0
  · subst h0
    simp
  · have hx : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast h0
    calc ∑ y ∈ Finset.range x, cTerm (x, y)
        ≤ ∑ _y ∈ Finset.range x, 3 / (2 * (x : ℝ) ^ 3) :=
          Finset.sum_le_sum fun y _ => cTerm_le (x, y)
      _ = (x : ℝ) * (3 / (2 * (x : ℝ) ^ 3)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = 3 / (2 * (x : ℝ) ^ 2) := by
          field_simp

/-! ## Convergence -/

/-- Each row is supported on `y < x`. -/
theorem cTerm_row_support (x y : ℕ) (h : y ∉ Finset.range x) : cTerm (x, y) = 0 := by
  simp only [Finset.mem_range, not_lt] at h
  unfold cTerm
  rw [if_neg]
  rintro ⟨-, h2, -⟩
  exact absurd h2 (by omega)

theorem cTerm_row_summable (x : ℕ) : Summable (fun y => cTerm (x, y)) :=
  summable_of_ne_finset_zero (s := Finset.range x) (cTerm_row_support x)

theorem cTerm_row_tsum_le (x : ℕ) : ∑' y, cTerm (x, y) ≤ 3 / (2 * (x : ℝ) ^ 2) := by
  rw [tsum_eq_sum (s := Finset.range x) (cTerm_row_support x)]
  exact cTerm_row_le x

/-- **The series for `C` converges.** -/
theorem cTerm_summable : Summable cTerm := by
  rw [summable_prod_of_nonneg (fun p => cTerm_nonneg p)]
  refine ⟨cTerm_row_summable, ?_⟩
  have hg : Summable (fun x : ℕ => 3 / (2 * (x : ℝ) ^ 2)) := by
    have h : Summable (fun x : ℕ => 1 / (x : ℝ) ^ 2) := by
      rw [Real.summable_one_div_nat_pow]
      norm_num
    refine (h.mul_left (3 / 2)).congr fun x => ?_
    rw [div_mul_eq_mul_div, mul_one_div]
    ring_nf
  refine Summable.of_nonneg_of_le (fun x => ?_) cTerm_row_tsum_le hg
  exact tsum_nonneg fun y => cTerm_nonneg _

/-- **The constant `C`** of equation (const-c). -/
noncomputable def cConst : ℝ := ∑' p : ℕ × ℕ, cTerm p

theorem cConst_nonneg : 0 ≤ cConst :=
  tsum_nonneg fun p => cTerm_nonneg p

/-- **The constant `D = 1 + 4C`** of Theorem A and Theorem 14.

Numerically, truncating the series for `C` at `a ≤ 20000` gives
`C ≈ 0.21138` and `D ≈ 1.8455`, consistent with the paper's `D ≈ 1.85`.
(The tail is `O(1/N)`, so the truncation converges slowly.) -/
noncomputable def dConst : ℝ := 1 + 4 * cConst

/-! ## The summand of Lemma 19

The bulk part of `G₁` in the paper's proof of Lemma 19 has summand

```
n²/(d²x²(x+y))  -  n²y/(2x²d²(x+y)²)  =  (n²/d²) · (2x + y)/(2x²(x+y)²),
```

so the coefficient is exactly `cTerm`.  This is the algebraic identity that
makes `C` appear. -/

/-- **The summand identity.**  `1/(x²(x+y)) - y/(2x²(x+y)²) = (2x+y)/(2x²(x+y)²)`. -/
theorem cTerm_summand_eq {x y : ℝ} (hx : x ≠ 0) (haa : x + y ≠ 0) :
    1 / (x ^ 2 * (x + y)) - y / (2 * x ^ 2 * (x + y) ^ 2)
      = (2 * x + y) / (2 * x ^ 2 * (x + y) ^ 2) := by
  field_simp
  ring

/-- The value of `cTerm` on an admissible pair, in the paper's split form. -/
theorem cTerm_eq_of_mem {x y : ℕ} (h1 : 1 ≤ y) (h2 : y < x) (h3 : Nat.gcd x y = 1) :
    cTerm (x, y)
      = 1 / ((x : ℝ) ^ 2 * ((x : ℝ) + y)) - (y : ℝ) / (2 * (x : ℝ) ^ 2 * ((x : ℝ) + y) ^ 2) := by
  have hx : (x : ℝ) ≠ 0 := by
    have : 0 < x := by omega
    positivity
  have haa : (x : ℝ) + (y : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (x : ℝ) := by
      have : 0 < x := by omega
      exact_mod_cast this
    have : (0 : ℝ) ≤ (y : ℝ) := by positivity
    positivity
  rw [cTerm_summand_eq hx haa]
  unfold cTerm
  rw [if_pos ⟨h1, h2, h3⟩]

/-- `C` as an iterated sum: first over `y`, then over `x`. -/
theorem cConst_eq_tsum_rows : cConst = ∑' x : ℕ, ∑' y : ℕ, cTerm (x, y) :=
  cTerm_summable.tsum_prod

/-- `C` as a sum of finite rows. -/
theorem cConst_eq_tsum_finRows : cConst = ∑' x : ℕ, ∑ y ∈ Finset.range x, cTerm (x, y) := by
  rw [cConst_eq_tsum_rows]
  refine tsum_congr fun x => ?_
  exact tsum_eq_sum (s := Finset.range x) (cTerm_row_support x)

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
theorem cRow_summable : Summable (fun x : ℕ => ∑ y ∈ Finset.range x, cTerm (x, y)) := by
  have hg : Summable (fun x : ℕ => 3 / (2 * (x : ℝ) ^ 2)) := by
    have h : Summable (fun x : ℕ => 1 / (x : ℝ) ^ 2) := by
      rw [Real.summable_one_div_nat_pow]
      norm_num
    refine (h.mul_left (3 / 2)).congr fun x => ?_
    rw [div_mul_eq_mul_div, mul_one_div]
    ring_nf
  refine Summable.of_nonneg_of_le (fun x => ?_) cTerm_row_le hg
  exact Finset.sum_nonneg fun y _ => cTerm_nonneg _

/-- **The tail bound for `C`.**  Truncating the series at `a ≤ N` loses at most
`3/(2N)`. -/
theorem cConst_le_partial_add {N : ℕ} (hN : 0 < N) :
    cConst ≤ (∑ x ∈ Finset.range (N + 1), ∑ y ∈ Finset.range x, cTerm (x, y))
      + 3 / (2 * (N : ℝ)) := by
  rw [cConst_eq_tsum_finRows]
  refine Real.tsum_le_of_sum_le
    (fun x => Finset.sum_nonneg fun y _ => cTerm_nonneg _) fun s => ?_
  classical
  have hsplit : ∑ x ∈ s, (∑ y ∈ Finset.range x, cTerm (x, y))
      = (∑ x ∈ s.filter (fun x => x ≤ N), ∑ y ∈ Finset.range x, cTerm (x, y))
        + ∑ x ∈ s.filter (fun x => ¬ x ≤ N), ∑ y ∈ Finset.range x, cTerm (x, y) :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hlow : (∑ x ∈ s.filter (fun x => x ≤ N), ∑ y ∈ Finset.range x, cTerm (x, y))
      ≤ ∑ x ∈ Finset.range (N + 1), ∑ y ∈ Finset.range x, cTerm (x, y) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_
      (fun x _ _ => Finset.sum_nonneg fun y _ => cTerm_nonneg _)
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
    omega
  have hhigh : (∑ x ∈ s.filter (fun x => ¬ x ≤ N), ∑ y ∈ Finset.range x, cTerm (x, y))
      ≤ 3 / (2 * (N : ℝ)) := by
    have h1 : (∑ x ∈ s.filter (fun x => ¬ x ≤ N), ∑ y ∈ Finset.range x, cTerm (x, y))
        ≤ ∑ x ∈ s.filter (fun x => ¬ x ≤ N), 3 / (2 * (x : ℝ) ^ 2) :=
      Finset.sum_le_sum fun x _ => cTerm_row_le x
    have h2 : (∑ x ∈ s.filter (fun x => ¬ x ≤ N), 3 / (2 * (x : ℝ) ^ 2))
        = (3 / 2) * ∑ x ∈ s.filter (fun x => ¬ x ≤ N), 1 / ((x : ℝ) ^ 2) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [div_mul_eq_mul_div, mul_one_div]
      ring_nf
    have h3 : (∑ x ∈ s.filter (fun x => ¬ x ≤ N), 1 / ((x : ℝ) ^ 2)) ≤ 1 / (N : ℝ) := by
      refine sum_inv_sq_tail_le hN _ fun x hx => ?_
      simp only [Finset.mem_filter] at hx
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
    (hbulk : ∀ x y, x ≤ N → 1 ≤ y → y < x → d * x * (x + y) ≤ m) :
    cConst ≤ (∑ x ∈ Finset.range (N + 1), ∑ y ∈ Finset.range x,
        if d * x * (x + y) ≤ m then cTerm (x, y) else 0) + 3 / (2 * (N : ℝ)) := by
  refine le_trans (cConst_le_partial_add hN) ?_
  have heq : ∀ x ∈ Finset.range (N + 1), ∑ y ∈ Finset.range x, cTerm (x, y)
      = ∑ y ∈ Finset.range x, if d * x * (x + y) ≤ m then cTerm (x, y) else 0 := by
    intro x hx
    simp only [Finset.mem_range, Nat.lt_succ_iff] at hx
    refine Finset.sum_congr rfl fun y hy => ?_
    simp only [Finset.mem_range] at hy
    rcases Nat.eq_zero_or_pos y with h0 | h0
    · subst h0
      have hz : cTerm (x, 0) = 0 := by
        unfold cTerm
        rw [if_neg]
        rintro ⟨h1, -, -⟩
        omega
      simp [hz]
    · rw [if_pos (hbulk x y hx h0 hy)]
  rw [Finset.sum_congr rfl heq]


/-! ## The substitution of Lemma 19

Substituting the paper's coefficients `A = d·x + m/x`, `B = -y/x` and the real
bound `V = m/(x+y)` into the main term `(1/x)(A·V + B·V²/2)` gives

```
d·m/(x+y)  +  m² · cTerm(x, y).
```

The first term is lower order; the second is what sums to `m²·C`.  This is the
step where the constant appears. -/

/-- **The substitution.**  The main term at a coprime pair is
`d·m/(x+y) + m²·cTerm(x,y)`. -/
theorem main_term_substitute {m d x y : ℕ} (h1 : 1 ≤ y) (h2 : y < x)
    (h3 : Nat.gcd x y = 1) :
    (1 / (x : ℝ)) * ((((d * x : ℕ) : ℝ) + (m : ℝ) / (x : ℝ)) * ((m : ℝ) / ((x : ℝ) + (y : ℝ)))
        + (-(y : ℝ) / (x : ℝ)) * ((m : ℝ) / ((x : ℝ) + (y : ℝ))) ^ 2 / 2)
      = (d : ℝ) * (m : ℝ) / ((x : ℝ) + (y : ℝ)) + (m : ℝ) ^ 2 * cTerm (x, y) := by
  have hx : (0 : ℝ) < (x : ℝ) := by
    have : 0 < x := by omega
    exact_mod_cast this
  have hy0 : (0 : ℝ) ≤ (y : ℝ) := by positivity
  have haa : (0 : ℝ) < (x : ℝ) + (y : ℝ) := by linarith
  unfold cTerm
  rw [if_pos ⟨h1, h2, h3⟩]
  push_cast
  field_simp
  ring

/-! ## Assembling the main term

After substitution the main term splits into a lower-order part
`d·m·∑ 1/(x+y)` and `m²` times a partial sum of the series for `C`.  The latter
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
    (hbulk : ∀ x y, x ≤ N → 1 ≤ y → y < x → d * x * (x + y) ≤ m) :
    cConst - 3 / (2 * (N : ℝ))
      ≤ ∑ x ∈ Finset.range (N + 1), ∑ y ∈ Finset.range x,
          (if d * x * (x + y) ≤ m then cTerm (x, y) else 0) := by
  have h := cConst_le_bulk_add hN hbulk
  linarith

/-! ## Reconciling the index shapes

`bulk_sum_close` is stated over the double sum `∑_{x ≤ N} ∑_{y < x}`, while
`G1_split` produces a sum over a `Finset (ℕ × ℕ)` of bulk pairs.  The first is a
sum over `{(x,y) : x ≤ N, y < x}`, whose nonzero terms all lie in the second. -/

/-- The double sum as a sum over pairs. -/
theorem double_sum_eq_pairs {N : ℕ} (f : ℕ → ℕ → ℝ) :
    ∑ x ∈ Finset.range (N + 1), ∑ y ∈ Finset.range x, f x y
      = ∑ p ∈ ((Finset.range (N + 1)) ×ˢ (Finset.range (N + 1))).filter (fun p => p.2 < p.1),
          f p.1 p.2 := by
  rw [Finset.sum_sigma']
  refine Finset.sum_bij' (i := fun q _ => (q.1, q.2))
    (j := fun p _ => (⟨p.1, p.2⟩ : (_ : ℕ) × ℕ)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨x, y⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    exact ⟨⟨hx.1, by omega⟩, hx.2⟩
  · rintro ⟨x, y⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
    simp only [Finset.mem_sigma, Finset.mem_range]
    exact ⟨hp.1.1, hp.2⟩
  · rintro ⟨x, y⟩ _; rfl
  · rintro ⟨x, y⟩ _; rfl
  · rintro ⟨x, y⟩ _; rfl

/-- **The reconciliation.**  The double sum over `a ≤ N` is at most the sum over
the bulk pairs. -/
theorem bulk_double_le_pairs {m d N : ℕ} (hd : 0 < d) :
    ∑ x ∈ Finset.range (N + 1), ∑ y ∈ Finset.range x,
        (if d * x * (x + y) ≤ m then cTerm (x, y) else 0)
      ≤ ∑ p ∈ (coprimePairs m).filter (fun p => d * p.1 * (p.1 + p.2) ≤ m), cTerm p := by
  classical
  rw [double_sum_eq_pairs (fun x y => if d * x * (x + y) ≤ m then cTerm (x, y) else 0)]
  set P := ((Finset.range (N + 1)) ×ˢ (Finset.range (N + 1))).filter (fun p => p.2 < p.1) with hP
  set B := (coprimePairs m).filter (fun p => d * p.1 * (p.1 + p.2) ≤ m) with hB
  -- every nonzero term of the left sum sits at a bulk pair
  have hzero : ∀ p ∈ P, p ∉ B →
      (if d * p.1 * (p.1 + p.2) ≤ m then cTerm (p.1, p.2) else 0) = 0 := by
    rintro ⟨x, y⟩ hp hnb
    by_cases hbulk : d * x * (x + y) ≤ m
    · simp only [hbulk, if_true]
      -- the pair must fail admissibility, else it would lie in `B`
      unfold cTerm
      rw [if_neg]
      rintro ⟨h1, h2, h3⟩
      have h1' : 1 ≤ y := h1
      have h2' : y < x := h2
      have h3' : Nat.gcd x y = 1 := h3
      have hd1 : 1 ≤ d := hd
      have ham : x ≤ m := by
        have hx1 : 1 ≤ x := by omega
        have haa : 1 ≤ x + y := by omega
        have hstep : x ≤ d * x * (x + y) := by
          calc x = 1 * x * 1 := by ring
            _ ≤ d * x * (x + y) := Nat.mul_le_mul (Nat.mul_le_mul hd1 (le_refl x)) haa
        omega
      have hym : y ≤ m := by omega
      refine hnb ?_
      rw [hB]
      simp only [Finset.mem_filter]
      exact ⟨mem_coprimePairs.2 ⟨⟨ham, hym⟩, h1', h2', h3'⟩, hbulk⟩
    · simp [hbulk]
  calc ∑ p ∈ P, (if d * p.1 * (p.1 + p.2) ≤ m then cTerm (p.1, p.2) else 0)
      = ∑ p ∈ P.filter (fun p => p ∈ B),
          (if d * p.1 * (p.1 + p.2) ≤ m then cTerm (p.1, p.2) else 0) := by
        refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
        intro q hx hnx
        simp only [Finset.mem_filter, not_and] at hnx
        exact hzero q hx (hnx hx)
    _ ≤ ∑ p ∈ P.filter (fun p => p ∈ B), cTerm p := by
        refine Finset.sum_le_sum fun p _ => ?_
        split
        · exact le_refl _
        · exact cTerm_nonneg p
    _ ≤ ∑ p ∈ B, cTerm p := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun p _ _ => cTerm_nonneg p)
        intro q hx
        simp only [Finset.mem_filter] at hx
        exact hx.2

/-- **The bulk pair sum is within `3/(2N)` of `C`.**

This is the reconciled form of `bulk_sum_close`: the partial sum of the series
for `C` over the bulk pairs — the shape the main term actually produces — is
squeezed between `C - 3/(2N)` and `C`. -/
theorem bulk_pairs_close {m d N : ℕ} (hN : 0 < N) (hd : 0 < d)
    (hbulk : ∀ x y, x ≤ N → 1 ≤ y → y < x → d * x * (x + y) ≤ m) :
    cConst - 3 / (2 * (N : ℝ))
        ≤ ∑ p ∈ (coprimePairs m).filter (fun p => d * p.1 * (p.1 + p.2) ≤ m), cTerm p
      ∧ ∑ p ∈ (coprimePairs m).filter (fun p => d * p.1 * (p.1 + p.2) ≤ m), cTerm p
        ≤ cConst :=
  ⟨le_trans (bulk_sum_close hN hbulk) (bulk_double_le_pairs hd),
    sum_cTerm_le_cConst _⟩

/-! ## The sum over divisors

For `d ∣ n` the natural-number quotient `n/d` is exact, so `m = n/d` gives
`m² = n²/d²` and the main terms sum to `C·n²·∑_{d∣n} 1/d²` — the shape of
Lemma 19.  The errors, of size `O((n/d)^{3/2}√d) = O(n^{3/2}/d)`, sum to
`O(n^{3/2}·d(n))`. -/

/-- **The main terms sum to `C·n²·∑_{d∣n} 1/d²`.** -/
theorem sum_div_sq_eq {n : ℕ} (hn : 0 < n) (K : ℝ) :
    ∑ d ∈ n.divisors, K * (((n / d : ℕ) : ℝ)) ^ 2
      = K * (n : ℝ) ^ 2 * ∑ d ∈ n.divisors, 1 / (d : ℝ) ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  obtain ⟨hdn, -⟩ := Nat.mem_divisors.1 hd
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
  have hcast : ((n / d : ℕ) : ℝ) = (n : ℝ) / (d : ℝ) :=
    Nat.cast_div hdn (by positivity)
  rw [hcast]
  field_simp

/-- **The errors sum to at most `d(n)` times their maximum.** -/
theorem sum_divisors_le {n : ℕ} (g : ℕ → ℝ) (K : ℝ)
    (hg : ∀ d ∈ n.divisors, g d ≤ K) :
    ∑ d ∈ n.divisors, g d ≤ (n.divisors.card : ℝ) * K := by
  calc ∑ d ∈ n.divisors, g d ≤ ∑ _d ∈ n.divisors, K := Finset.sum_le_sum hg
    _ = (n.divisors.card : ℝ) * K := by rw [Finset.sum_const, nsmul_eq_mul]

/-- The per-divisor error `(n/d)^{3/2}·√d` is `n^{3/2}/d`, hence at most
`n^{3/2}`. -/
theorem error_per_divisor_le {n d : ℕ} (hn : 0 < n) (hd : d ∈ n.divisors) :
    ((n / d : ℕ) : ℝ) ^ (3 / 2 : ℝ) * (d : ℝ) ^ ((1 : ℝ) / 2)
      ≤ (n : ℝ) ^ (3 / 2 : ℝ) := by
  obtain ⟨hdn, -⟩ := Nat.mem_divisors.1 hd
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd0
  have hnR : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hcast : ((n / d : ℕ) : ℝ) = (n : ℝ) / (d : ℝ) := Nat.cast_div hdn (by positivity)
  rw [hcast, Real.div_rpow hnR (by positivity), div_mul_eq_mul_div,
    div_le_iff₀ (by positivity)]
  have hexp : (d : ℝ) ^ ((1 : ℝ) / 2) ≤ (d : ℝ) ^ ((3 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le hdR (by norm_num)
  have hn32 : (0 : ℝ) ≤ (n : ℝ) ^ (3 / 2 : ℝ) := by positivity
  nlinarith [hexp, hn32]

/-! ## Lemma 19

At a single divisor, the main term is `m²·C` up to the lower-order part and the
truncation error.  Summing over `d ∣ n` then gives the statement of the paper's
Lemma 19. -/

/-- **Lemma 19, at a single divisor.**

The main term for the divisor `d`, with `m = n/d`, differs from `m²·C` by at
most the lower-order part plus the truncation error.  Taking
`N = √(m/(2d))` both are `O(m^{3/2}√d)`. -/
theorem lemma19_local {m d N : ℕ} (hm : 0 < m) (hd : 0 < d) (hN : 0 < N)
    (hbulk : ∀ x y, x ≤ N → 1 ≤ y → y < x → d * x * (x + y) ≤ m) :
    |(∑ p ∈ (coprimePairs m).filter (fun p => d * p.1 * (p.1 + p.2) ≤ m),
          ((d : ℝ) * (m : ℝ) / ((p.1 : ℝ) + (p.2 : ℝ)) + (m : ℝ) ^ 2 * cTerm p))
        - (m : ℝ) ^ 2 * cConst|
      ≤ ((Nat.sqrt ((m - 1) / d) : ℝ) + 1) * ((d : ℝ) * (m : ℝ))
        + (m : ℝ) ^ 2 * (3 / (2 * (N : ℝ))) := by
  rw [G1_split]
  obtain ⟨hlow, hhigh⟩ := bulk_pairs_close hN hd hbulk
  have hL := lower_order_le hm hd
  have hLnn : (0 : ℝ) ≤ ∑ p ∈ (coprimePairs m).filter (fun p => d * p.1 * (p.1 + p.2) ≤ m),
      (d : ℝ) * (m : ℝ) / ((p.1 : ℝ) + (p.2 : ℝ)) :=
    Finset.sum_nonneg fun p _ => by positivity
  have hm2 : (0 : ℝ) ≤ (m : ℝ) ^ 2 := by positivity
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have htrunc : (0 : ℝ) ≤ (m : ℝ) ^ 2 * (3 / (2 * (N : ℝ))) := by positivity
  rw [abs_le]
  constructor
  · nlinarith [hlow, hLnn, hm2]
  · nlinarith [hhigh, hL, hm2, htrunc]

/-- **`G₁`**, the main term of the triple sum, in its substituted form.

By `main_term_substitute` the summand here is the paper's
`(1/x)(A·V + B·V²/2)` at `A = d·x + m/x`, `B = -y/x`, `V = m/(x+y)`. -/
noncomputable def G1 (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors,
    ∑ p ∈ (coprimePairs (n / d)).filter (fun p => d * p.1 * (p.1 + p.2) ≤ n / d),
      ((d : ℝ) * ((n / d : ℕ) : ℝ) / ((p.1 : ℝ) + (p.2 : ℝ))
        + ((n / d : ℕ) : ℝ) ^ 2 * cTerm p)

/-- **Lemma 19.**

`G₁(n) = C·n²·∑_{d∣n} 1/d²` up to the sum of the per-divisor errors.  Each of
those is bounded by `lemma19_local`, and by `error_per_divisor_le` and
`sum_divisors_le` they total `O(n^{3/2+ε})`. -/
theorem lemma19 {n : ℕ} (hn : 0 < n) (E : ℕ → ℝ)
    (hE : ∀ d ∈ n.divisors,
      |(∑ p ∈ (coprimePairs (n / d)).filter (fun p => d * p.1 * (p.1 + p.2) ≤ n / d),
            ((d : ℝ) * ((n / d : ℕ) : ℝ) / ((p.1 : ℝ) + (p.2 : ℝ))
              + ((n / d : ℕ) : ℝ) ^ 2 * cTerm p))
          - ((n / d : ℕ) : ℝ) ^ 2 * cConst| ≤ E d) :
    |G1 n - cConst * (n : ℝ) ^ 2 * ∑ d ∈ n.divisors, 1 / (d : ℝ) ^ 2|
      ≤ ∑ d ∈ n.divisors, E d := by
  have hmain : cConst * (n : ℝ) ^ 2 * ∑ d ∈ n.divisors, 1 / (d : ℝ) ^ 2
      = ∑ d ∈ n.divisors, ((n / d : ℕ) : ℝ) ^ 2 * cConst := by
    rw [← sum_div_sq_eq hn cConst]
    exact Finset.sum_congr rfl fun d _ => mul_comm _ _
  rw [G1, hmain, ← Finset.sum_sub_distrib]
  calc |∑ d ∈ n.divisors,
        ((∑ p ∈ (coprimePairs (n / d)).filter (fun p => d * p.1 * (p.1 + p.2) ≤ n / d),
            ((d : ℝ) * ((n / d : ℕ) : ℝ) / ((p.1 : ℝ) + (p.2 : ℝ))
              + ((n / d : ℕ) : ℝ) ^ 2 * cTerm p))
          - ((n / d : ℕ) : ℝ) ^ 2 * cConst)|
      ≤ ∑ d ∈ n.divisors,
          |(∑ p ∈ (coprimePairs (n / d)).filter (fun p => d * p.1 * (p.1 + p.2) ≤ n / d),
              ((d : ℝ) * ((n / d : ℕ) : ℝ) / ((p.1 : ℝ) + (p.2 : ℝ))
                + ((n / d : ℕ) : ℝ) ^ 2 * cTerm p))
            - ((n / d : ℕ) : ℝ) ^ 2 * cConst| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ n.divisors, E d := Finset.sum_le_sum hE

/-! ## Instantiating the error

When `2d ≤ m` the cut-off `N = √(m/(2d))` is positive and `lemma19_local`
applies.  Otherwise `m < 2d ≤ 6d`, and the bulk set is empty — `x > y ≥ 1`
forces `x ≥ 2` and `x + y ≥ 3`, so `d·x·(x+y) ≥ 6d > m` — leaving the error
`m²·C`. -/

/-- **The bulk set is empty when `m` is small relative to `d`.** -/
theorem bulk_empty_of_small {m d : ℕ} (h : m < 6 * d) :
    (coprimePairs m).filter (fun p => d * p.1 * (p.1 + p.2) ≤ m) = ∅ := by
  rw [Finset.filter_eq_empty_iff]
  rintro ⟨x, y⟩ hp
  obtain ⟨-, hx1, hx2, -⟩ := mem_coprimePairs.1 hp
  have ha2' : 2 ≤ x := by omega
  have haa : 3 ≤ x + y := by omega
  intro hcon
  have hcon' : d * x * (x + y) ≤ m := hcon
  have hge : 6 * d ≤ d * x * (x + y) := by
    calc 6 * d = d * 2 * 3 := by ring
      _ ≤ d * x * (x + y) := Nat.mul_le_mul (Nat.mul_le_mul_left d ha2') haa
  omega

/-- **The per-divisor error of Lemma 19.** -/
noncomputable def Eterm (n d : ℕ) : ℝ :=
  if 2 * d ≤ n / d then
    ((Nat.sqrt ((n / d - 1) / d) : ℝ) + 1) * ((d : ℝ) * ((n / d : ℕ) : ℝ))
      + ((n / d : ℕ) : ℝ) ^ 2 * (3 / (2 * ((Nat.sqrt ((n / d) / (2 * d)) : ℕ) : ℝ)))
  else ((n / d : ℕ) : ℝ) ^ 2 * cConst

/-- **The per-divisor error bound holds.** -/
theorem lemma19_E {n : ℕ} (hn : 0 < n) (d : ℕ) (hd : d ∈ n.divisors) :
    |(∑ p ∈ (coprimePairs (n / d)).filter (fun p => d * p.1 * (p.1 + p.2) ≤ n / d),
          ((d : ℝ) * ((n / d : ℕ) : ℝ) / ((p.1 : ℝ) + (p.2 : ℝ))
            + ((n / d : ℕ) : ℝ) ^ 2 * cTerm p))
        - ((n / d : ℕ) : ℝ) ^ 2 * cConst| ≤ Eterm n d := by
  obtain ⟨hdn, -⟩ := Nat.mem_divisors.1 hd
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
  have hm : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hn hdn) hd0
  unfold Eterm
  by_cases hcase : 2 * d ≤ n / d
  · rw [if_pos hcase]
    have hN : 0 < Nat.sqrt ((n / d) / (2 * d)) := by
      refine Nat.sqrt_pos.2 ?_
      exact (Nat.one_le_div_iff (by omega)).2 hcase
    exact lemma19_local hm hd0 hN (fun x y hx h1 h2 => bulk_of_le_sqrt h1 h2 hx hd0)
  · rw [if_neg hcase, bulk_empty_of_small (by omega), Finset.sum_empty, zero_sub, abs_neg,
      abs_of_nonneg (mul_nonneg (by positivity) cConst_nonneg)]

/-- **Lemma 19, with the error instantiated.** -/
theorem lemma19_final {n : ℕ} (hn : 0 < n) :
    |G1 n - cConst * (n : ℝ) ^ 2 * ∑ d ∈ n.divisors, 1 / (d : ℝ) ^ 2|
      ≤ ∑ d ∈ n.divisors, Eterm n d :=
  lemma19 hn (Eterm n) (fun d hd => lemma19_E hn d hd)

/-! ## Bounding the total error

The truncation term is `m²·3/(2N)` with `N = √(m/(2d))`, so a lower bound on `N`
is needed.  The natural-number square root satisfies `q ≤ 4·(√q)²` for `q ≥ 1`,
and `m < 4dq`, giving `m ≤ 16·d·N²` — equivalently `√m ≤ 4√d·N`, which turns
`m²/N` into `4·m^{3/2}·√d`. -/

/-- `q ≤ 4·(√q)²`. -/
theorem le_four_mul_sqrt_sq {q : ℕ} (hq : 1 ≤ q) :
    q ≤ 4 * (Nat.sqrt q * Nat.sqrt q) := by
  have hs : 1 ≤ Nat.sqrt q := Nat.sqrt_pos.2 hq
  have h := Nat.lt_succ_sqrt' q
  nlinarith

/-- **The cut-off is large enough.**  `m ≤ 16·d·N²`. -/
theorem cutoff_lower {m d : ℕ} (hd : 0 < d) (h : 2 * d ≤ m) :
    m ≤ 16 * d * (Nat.sqrt (m / (2 * d)) * Nat.sqrt (m / (2 * d))) := by
  have hd2 : 0 < 2 * d := by omega
  have hq1 : 1 ≤ m / (2 * d) := (Nat.one_le_div_iff hd2).2 h
  have hlt : m < 2 * d * (m / (2 * d)) + 2 * d := by
    have hdm := Nat.div_add_mod m (2 * d)
    have hmod : m % (2 * d) < 2 * d := Nat.mod_lt m hd2
    omega
  have h4 : m / (2 * d) ≤ 4 * (Nat.sqrt (m / (2 * d)) * Nat.sqrt (m / (2 * d))) :=
    le_four_mul_sqrt_sq hq1
  nlinarith

/-- **`√m ≤ 4√d·N`**, the real form of `cutoff_lower`. -/
theorem sqrt_le_cutoff {m d : ℕ} (hd : 0 < d) (h : 2 * d ≤ m) :
    Real.sqrt (m : ℝ)
      ≤ 4 * Real.sqrt (d : ℝ) * ((Nat.sqrt (m / (2 * d)) : ℕ) : ℝ) := by
  have hN : (0 : ℝ) ≤ ((Nat.sqrt (m / (2 * d)) : ℕ) : ℝ) := by positivity
  have hdR : (0 : ℝ) ≤ (d : ℝ) := by positivity
  have hkey : (m : ℝ)
      ≤ (4 * Real.sqrt (d : ℝ) * ((Nat.sqrt (m / (2 * d)) : ℕ) : ℝ)) ^ 2 := by
    have h1 : (m : ℝ) ≤ 16 * (d : ℝ)
        * (((Nat.sqrt (m / (2 * d)) : ℕ) : ℝ) * ((Nat.sqrt (m / (2 * d)) : ℕ) : ℝ)) := by
      exact_mod_cast cutoff_lower hd h
    have hsq : Real.sqrt (d : ℝ) ^ 2 = (d : ℝ) := Real.sq_sqrt hdR
    nlinarith [hsq, h1]
  calc Real.sqrt (m : ℝ)
      ≤ Real.sqrt ((4 * Real.sqrt (d : ℝ) * ((Nat.sqrt (m / (2 * d)) : ℕ) : ℝ)) ^ 2) :=
        Real.sqrt_le_sqrt hkey
    _ = 4 * Real.sqrt (d : ℝ) * ((Nat.sqrt (m / (2 * d)) : ℕ) : ℝ) :=
        Real.sqrt_sq (by positivity)

/-- `x^{3/2} = x·√x`. -/
theorem rpow_three_halves {x : ℝ} (hx : 0 ≤ x) : x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
  rw [Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
    Real.rpow_add' hx (by norm_num), Real.rpow_one]

/-- **Every per-divisor error term is `O(n^{3/2})`.**

In the bulk case `2d ≤ m` the two pieces are `(√((m-1)/d)+1)·d·m ≤ 2·n^{3/2}`
(using `d·m = n`) and `m²·3/(2N) ≤ 6·n^{3/2}` (using `√m ≤ 4√d·N` and
`m·√m·√d = m·√n`).  In the degenerate case `m < 2d` one has `m² < 2n`. -/
theorem Eterm_le {n d : ℕ} (hn : 0 < n) (hd : d ∈ n.divisors) :
    Eterm n d ≤ (8 + 2 * cConst) * ((n : ℝ) * Real.sqrt n) := by
  obtain ⟨hdn, -⟩ := Nat.mem_divisors.1 hd
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
  have hCnn : (0 : ℝ) ≤ cConst := cConst_nonneg
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hsn : (1 : ℝ) ≤ Real.sqrt n := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hnR
  have hsqn : (0 : ℝ) ≤ Real.sqrt n := Real.sqrt_nonneg _
  unfold Eterm
  set m := n / d with hm
  have hdm : d * m = n := Nat.mul_div_cancel' hdn
  have hm0 : 0 < m := Nat.div_pos (Nat.le_of_dvd hn hdn) hd0
  have hmn' : m ≤ n := Nat.div_le_self n d
  have hmn : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn'
  have hmR : (0 : ℝ) ≤ (m : ℝ) := by positivity
  have hdmR : (d : ℝ) * (m : ℝ) = (n : ℝ) := by exact_mod_cast hdm
  split_ifs with hcase
  · -- bulk case `2d ≤ m`
    -- first piece: `√((m-1)/d) ≤ √n`
    have hs : ((Nat.sqrt ((m - 1) / d) : ℕ) : ℝ) ≤ Real.sqrt n := by
      have hnat : Nat.sqrt ((m - 1) / d) * Nat.sqrt ((m - 1) / d) ≤ n :=
        calc Nat.sqrt ((m - 1) / d) * Nat.sqrt ((m - 1) / d) ≤ (m - 1) / d := Nat.sqrt_le _
          _ ≤ m - 1 := Nat.div_le_self _ _
          _ ≤ m := Nat.sub_le _ _
          _ ≤ n := hmn'
      refine (Real.le_sqrt (by positivity) (by positivity)).2 ?_
      have hcast : ((Nat.sqrt ((m - 1) / d) : ℕ) : ℝ) * ((Nat.sqrt ((m - 1) / d) : ℕ) : ℝ)
          ≤ (n : ℝ) := by exact_mod_cast hnat
      nlinarith [hcast]
    have hA : (((Nat.sqrt ((m - 1) / d) : ℕ) : ℝ) + 1) * ((d : ℝ) * (m : ℝ))
        ≤ 2 * ((n : ℝ) * Real.sqrt n) := by
      rw [hdmR]
      nlinarith [hs, hsn, hnR]
    -- second piece: the cut-off is at least `√m/(4√d)`
    have hN1 : 1 ≤ Nat.sqrt (m / (2 * d)) :=
      Nat.sqrt_pos.2 ((Nat.one_le_div_iff (by omega)).2 hcase)
    have hNR : (1 : ℝ) ≤ ((Nat.sqrt (m / (2 * d)) : ℕ) : ℝ) := by exact_mod_cast hN1
    have hcut := sqrt_le_cutoff hd0 hcase
    have hsm : Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ) = (m : ℝ) := Real.mul_self_sqrt hmR
    have hsd : Real.sqrt (m : ℝ) * Real.sqrt (d : ℝ) = Real.sqrt n := by
      rw [← Real.sqrt_mul hmR]
      congr 1
      rw [← hdmR]; ring
    have hkey : (m : ℝ) * (m : ℝ)
        ≤ 4 * ((m : ℝ) * (Real.sqrt n * ((Nat.sqrt (m / (2 * d)) : ℕ) : ℝ))) := by
      have h1 : (m : ℝ) * Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ)
          ≤ (m : ℝ) * Real.sqrt (m : ℝ)
              * (4 * Real.sqrt (d : ℝ) * ((Nat.sqrt (m / (2 * d)) : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hcut (by positivity)
      have h2 : (m : ℝ) * Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ) = (m : ℝ) * (m : ℝ) := by
        rw [mul_assoc, hsm]
      have h3 : (m : ℝ) * Real.sqrt (m : ℝ)
            * (4 * Real.sqrt (d : ℝ) * ((Nat.sqrt (m / (2 * d)) : ℕ) : ℝ))
          = 4 * ((m : ℝ) * ((Real.sqrt (m : ℝ) * Real.sqrt (d : ℝ))
              * ((Nat.sqrt (m / (2 * d)) : ℕ) : ℝ))) := by ring
      rw [h2, h3, hsd] at h1
      exact h1
    have hB : (m : ℝ) ^ 2 * (3 / (2 * ((Nat.sqrt (m / (2 * d)) : ℕ) : ℝ)))
        ≤ 6 * ((n : ℝ) * Real.sqrt n) := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      have hslack : (0 : ℝ)
          ≤ ((n : ℝ) - (m : ℝ)) * (Real.sqrt n * ((Nat.sqrt (m / (2 * d)) : ℕ) : ℝ)) :=
        mul_nonneg (by linarith) (by positivity)
      nlinarith [hkey, hslack]
    nlinarith [hA, hB, mul_nonneg hCnn (mul_nonneg (by linarith : (0:ℝ) ≤ (n:ℝ)) hsqn)]
  · -- degenerate case `m < 2d`
    have hlt : m * m < 2 * n := by
      have hm2 : m < 2 * d := by omega
      calc m * m < 2 * d * m := (Nat.mul_lt_mul_right hm0).2 hm2
        _ = 2 * n := by rw [← hdm]; ring
    have hltR : (m : ℝ) ^ 2 < 2 * (n : ℝ) := by
      rw [pow_two]; exact_mod_cast hlt
    have h1 : (m : ℝ) ^ 2 * cConst ≤ (2 * (n : ℝ)) * cConst :=
      mul_le_mul_of_nonneg_right hltR.le hCnn
    have h2 : (0 : ℝ) ≤ cConst * ((n : ℝ) * (Real.sqrt n - 1)) :=
      mul_nonneg hCnn (mul_nonneg (by linarith) (by linarith))
    have h3 : (0 : ℝ) ≤ 8 * ((n : ℝ) * Real.sqrt n) :=
      by positivity
    nlinarith [h1, h2, h3]

/-- **Lemma 19 in the paper's form.**  The total error is `O(n^{3/2+ε})`. -/
theorem lemma19_isBigO {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 0 < n →
      |G1 n - cConst * (n : ℝ) ^ 2 * ∑ d ∈ n.divisors, 1 / (d : ℝ) ^ 2|
        ≤ K * (n : ℝ) ^ (3 / 2 + ε) := by
  obtain ⟨C0, hC0, hCd⟩ := exists_card_divisors_le hε
  refine ⟨(8 + 2 * cConst) * C0, mul_pos (by linarith [cConst_nonneg]) hC0, fun n hn => ?_⟩
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hCnn : (0 : ℝ) ≤ cConst := cConst_nonneg
  have h32 : (n : ℝ) * Real.sqrt n = (n : ℝ) ^ (3 / 2 : ℝ) :=
    (rpow_three_halves (by positivity)).symm
  refine (lemma19_final hn).trans ?_
  refine (sum_divisors_le _ _ (fun d hd => Eterm_le hn hd)).trans ?_
  have hd := hCd n hn.ne'
  have hstep : (n.divisors.card : ℝ) * ((8 + 2 * cConst) * ((n : ℝ) * Real.sqrt n))
      ≤ (C0 * (n : ℝ) ^ ε) * ((8 + 2 * cConst) * ((n : ℝ) * Real.sqrt n)) := by
    refine mul_le_mul_of_nonneg_right hd ?_
    have hs0 : (0 : ℝ) ≤ Real.sqrt n := Real.sqrt_nonneg _
    exact mul_nonneg (by linarith) (mul_nonneg (by linarith) hs0)
  refine hstep.trans ?_
  rw [h32, Real.rpow_add hnpos]
  exact le_of_eq (by ring)

end BlockCycleRotation
