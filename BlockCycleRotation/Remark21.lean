/-
# Remark 21

The paper rewrites the constant `C` of equation (const-c) as

```
C = 1/2 - S/(2·ζ(3)),     S = ∑_{a > a' ≥ 1} 1/(a'·(a+a')²),
```

equation (const-c-alternative).  The argument has three steps.

1. The summand `(2a+a')/(2a²(a+a')²)` equals `(1/(2a'))(1/a² - 1/(a+a')²)`.
2. Multiplying by `ζ(3) = ∑_d 1/d³` removes the coprimality condition, because
   the summand is homogeneous of degree `-3` and every pair `A > A' ≥ 1`
   factors uniquely as `A = d·a`, `A' = d·a'` with `d = gcd(A,A')`.
3. Euler's formula `ζ(2,1) = ζ(3)` for the resulting `∑_{a>a'≥1} 1/(a'a²)`.

The paper cites step 3; Mathlib has no multiple-zeta-value theory, so it is
proved here from scratch in `Euler.lean`.
-/

import BlockCycleRotation.Constant

namespace BlockCycleRotation

open Finset

/-! ## The three series over all pairs

Each is supported on `a > a' ≥ 1` and extended by zero, in the style of
`cTerm`. -/

/-- `cTerm` without the coprimality condition. -/
noncomputable def gTerm (p : ℕ × ℕ) : ℝ :=
  if 1 ≤ p.2 ∧ p.2 < p.1 then
    (2 * (p.1 : ℝ) + (p.2 : ℝ)) / (2 * (p.1 : ℝ) ^ 2 * ((p.1 : ℝ) + (p.2 : ℝ)) ^ 2)
  else 0

/-- The summand of `ζ(2,1) = ∑_{a > a' ≥ 1} 1/(a'·a²)`. -/
noncomputable def zTerm (p : ℕ × ℕ) : ℝ :=
  if 1 ≤ p.2 ∧ p.2 < p.1 then 1 / ((p.2 : ℝ) * (p.1 : ℝ) ^ 2) else 0

/-- The summand of `S = ∑_{a > a' ≥ 1} 1/(a'·(a+a')²)`. -/
noncomputable def eTerm (p : ℕ × ℕ) : ℝ :=
  if 1 ≤ p.2 ∧ p.2 < p.1 then 1 / ((p.2 : ℝ) * ((p.1 : ℝ) + (p.2 : ℝ)) ^ 2) else 0

theorem gTerm_nonneg (p : ℕ × ℕ) : 0 ≤ gTerm p := by
  unfold gTerm; split
  · positivity
  · exact le_refl 0

theorem zTerm_nonneg (p : ℕ × ℕ) : 0 ≤ zTerm p := by
  unfold zTerm; split
  · positivity
  · exact le_refl 0

theorem eTerm_nonneg (p : ℕ × ℕ) : 0 ≤ eTerm p := by
  unfold eTerm; split
  · positivity
  · exact le_refl 0

/-- **Step 1 of Remark 21.**  `(2a+a')/(2a²(a+a')²) = (1/(2a'))(1/a² - 1/(a+a')²)`. -/
theorem gTerm_eq (p : ℕ × ℕ) : gTerm p = (zTerm p - eTerm p) / 2 := by
  unfold gTerm zTerm eTerm
  split_ifs with h
  · obtain ⟨h1, h2⟩ := h
    have ha : (0 : ℝ) < (p.1 : ℝ) := by
      have : 0 < p.1 := by omega
      exact_mod_cast this
    have ha' : (0 : ℝ) < (p.2 : ℝ) := by
      have : 0 < p.2 := by omega
      exact_mod_cast this
    have haa : (0 : ℝ) < (p.1 : ℝ) + (p.2 : ℝ) := by linarith
    field_simp
    ring
  · norm_num

/-- `cTerm` is `gTerm` restricted to coprime pairs. -/
theorem cTerm_eq_gTerm (p : ℕ × ℕ) :
    cTerm p = if Nat.gcd p.1 p.2 = 1 then gTerm p else 0 := by
  unfold cTerm gTerm
  by_cases hc : Nat.gcd p.1 p.2 = 1
  · rw [if_pos hc]
    by_cases h : 1 ≤ p.2 ∧ p.2 < p.1
    · rw [if_pos ⟨h.1, h.2, hc⟩, if_pos h]
    · rw [if_neg (by tauto), if_neg h]
  · rw [if_neg hc, if_neg (by tauto)]

/-! ## Convergence

Bounding row by row in the *first* index needs a harmonic sum; bounding in the
second index does not, since `∑_{a > a'} 1/a² ≤ 1/a'` is the tail bound
`sum_inv_sq_tail_le`.  So the sums are taken columnwise. -/

theorem zTerm_col_sum_le (a' : ℕ) (s : Finset ℕ) :
    ∑ a ∈ s, zTerm (a, a') ≤ 1 / (a' : ℝ) ^ 2 := by
  rcases Nat.eq_zero_or_pos a' with rfl | ha'
  · simp [zTerm]
  · have ha'R : (0 : ℝ) < (a' : ℝ) := by exact_mod_cast ha'
    have h1 : ∑ a ∈ s, zTerm (a, a')
        = ∑ a ∈ s.filter (fun a => a' < a), (1 / (a' : ℝ)) * (1 / (a : ℝ) ^ 2) := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun a _ => ?_
      unfold zTerm
      by_cases h : a' < a
      · rw [if_pos ⟨ha', h⟩, if_pos h]
        field_simp
      · rw [if_neg (by tauto), if_neg h]
    rw [h1, ← Finset.mul_sum]
    have h3 := sum_inv_sq_tail_le ha' (s.filter (fun a => a' < a))
      (fun a ha => (Finset.mem_filter.1 ha).2)
    calc (1 / (a' : ℝ)) * ∑ a ∈ s.filter (fun a => a' < a), 1 / (a : ℝ) ^ 2
        ≤ (1 / (a' : ℝ)) * (1 / (a' : ℝ)) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = 1 / (a' : ℝ) ^ 2 := by ring

theorem zTerm_col_summable (a' : ℕ) : Summable (fun a => zTerm (a, a')) :=
  summable_of_sum_le (fun a => zTerm_nonneg (a, a')) (zTerm_col_sum_le a')

theorem zTerm_col_tsum_le (a' : ℕ) : ∑' a, zTerm (a, a') ≤ 1 / (a' : ℝ) ^ 2 :=
  Real.tsum_le_of_sum_le (fun a => zTerm_nonneg (a, a')) (zTerm_col_sum_le a')

theorem zTerm_summable : Summable zTerm := by
  refine (Equiv.prodComm ℕ ℕ).summable_iff.1 ?_
  change Summable (fun q : ℕ × ℕ => zTerm (q.2, q.1))
  have hnn : (0 : ℕ × ℕ → ℝ) ≤ fun q => zTerm (q.2, q.1) := fun q => zTerm_nonneg _
  rw [summable_prod_of_nonneg hnn]
  refine ⟨fun a' => zTerm_col_summable a', ?_⟩
  have hg : Summable (fun a' : ℕ => 1 / (a' : ℝ) ^ 2) := by
    rw [Real.summable_one_div_nat_pow]; norm_num
  refine Summable.of_nonneg_of_le (fun a' => ?_) (fun a' => zTerm_col_tsum_le a') hg
  exact tsum_nonneg fun a => zTerm_nonneg _

theorem eTerm_le_zTerm (p : ℕ × ℕ) : eTerm p ≤ zTerm p := by
  unfold eTerm zTerm
  split_ifs with h
  · obtain ⟨h1, h2⟩ := h
    have ha' : (0 : ℝ) < (p.2 : ℝ) := by
      have : 0 < p.2 := by omega
      exact_mod_cast this
    have ha : (0 : ℝ) < (p.1 : ℝ) := by
      have : 0 < p.1 := by omega
      exact_mod_cast this
    refine one_div_le_one_div_of_le (by positivity) ?_
    nlinarith [mul_nonneg ha'.le (mul_nonneg ha.le ha'.le),
      mul_nonneg ha'.le (mul_nonneg ha'.le ha'.le)]
  · exact le_refl 0

theorem eTerm_summable : Summable eTerm :=
  zTerm_summable.of_nonneg_of_le eTerm_nonneg eTerm_le_zTerm

theorem gTerm_summable : Summable gTerm := by
  have h : gTerm = fun p => (zTerm p - eTerm p) / 2 := funext gTerm_eq
  rw [h]
  exact (zTerm_summable.sub eTerm_summable).div_const 2

/-- `ζ(2,1) = ∑_{a > a' ≥ 1} 1/(a'·a²)`. -/
noncomputable def zeta21 : ℝ := ∑' p, zTerm p

/-- `S = ∑_{a > a' ≥ 1} 1/(a'·(a+a')²)`, the series of eq. (const-c-alternative). -/
noncomputable def sConst : ℝ := ∑' p, eTerm p

/-- `ζ(3) = ∑_{d ≥ 1} 1/d³`. -/
noncomputable def zeta3 : ℝ := ∑' d : ℕ, 1 / ((d : ℝ) + 1) ^ 3

/-- **The sum over all pairs.** -/
theorem tsum_gTerm : ∑' p, gTerm p = (zeta21 - sConst) / 2 := by
  rw [zeta21, sConst]
  calc ∑' p, gTerm p = ∑' p : ℕ × ℕ, (zTerm p - eTerm p) / 2 := tsum_congr gTerm_eq
    _ = (∑' p : ℕ × ℕ, (zTerm p - eTerm p)) / 2 := tsum_div_const
    _ = (∑' p : ℕ × ℕ, zTerm p - ∑' p : ℕ × ℕ, eTerm p) / 2 := by
        rw [Summable.tsum_sub zTerm_summable eTerm_summable]

/-! ## Step 2: removing the coprimality condition

`gTerm` is homogeneous of degree `-3`, and every pair `A > A' ≥ 1` is uniquely
`(d·a, d·a')` with `d = gcd(A,A')` and `gcd(a,a') = 1`.  So multiplying the
coprime sum by `ζ(3) = ∑_d 1/d³` gives the sum over all pairs. -/

/-- `1/(d+1)³`, the summand of `ζ(3)`. -/
noncomputable def uTerm (d : ℕ) : ℝ := 1 / ((d : ℝ) + 1) ^ 3

theorem uTerm_pos (d : ℕ) : 0 < uTerm d := by
  unfold uTerm; positivity

theorem uTerm_summable : Summable uTerm := by
  have h : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 3) := by
    rw [Real.summable_one_div_nat_pow]; norm_num
  refine ((summable_nat_add_iff 1).2 h).congr fun d => ?_
  unfold uTerm
  push_cast
  ring

theorem tsum_uTerm : ∑' d, uTerm d = zeta3 := rfl

/-- The support of `cTerm`. -/
theorem cTerm_ne_zero {p : ℕ × ℕ} (h : cTerm p ≠ 0) :
    1 ≤ p.2 ∧ p.2 < p.1 ∧ Nat.gcd p.1 p.2 = 1 := by
  unfold cTerm at h
  split_ifs at h with hc
  · exact hc
  · exact absurd rfl h

/-- The support of `gTerm`. -/
theorem gTerm_ne_zero {p : ℕ × ℕ} (h : gTerm p ≠ 0) : 1 ≤ p.2 ∧ p.2 < p.1 := by
  unfold gTerm at h
  split_ifs at h with hc
  · exact hc
  · exact absurd rfl h

theorem cTerm_pos {a a' : ℕ} (h1 : 1 ≤ a') (h2 : a' < a) (h3 : Nat.gcd a a' = 1) :
    0 < cTerm (a, a') := by
  unfold cTerm
  rw [if_pos ⟨h1, h2, h3⟩]
  have ha : (0 : ℝ) < (a : ℝ) := by
    have : 0 < a := by omega
    exact_mod_cast this
  have ha' : (0 : ℝ) < (a' : ℝ) := by
    have : 0 < a' := by omega
    exact_mod_cast this
  positivity

/-- **`gTerm` is homogeneous of degree `-3`.** -/
theorem gTerm_smul {k a a' : ℕ} (hk : 0 < k) (h1 : 1 ≤ a') (h2 : a' < a) :
    gTerm (k * a, k * a') = gTerm (a, a') / (k : ℝ) ^ 3 := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have ha : (0 : ℝ) < (a : ℝ) := by
    have : 0 < a := by omega
    exact_mod_cast this
  have ha' : (0 : ℝ) < (a' : ℝ) := by
    have : 0 < a' := by omega
    exact_mod_cast this
  have hk1 : 1 ≤ k * a' := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hk2 : k * a' < k * a := by
    rw [Nat.mul_comm k a', Nat.mul_comm k a]
    exact Nat.mul_lt_mul_of_lt_of_le h2 (le_refl k) hk
  unfold gTerm
  rw [if_pos ⟨hk1, hk2⟩, if_pos ⟨h1, h2⟩]
  push_cast
  field_simp

/-- **The `ζ(3)` unfolding.** -/
theorem tsum_gTerm_eq : ∑' p : ℕ × ℕ, gTerm p = ∑' q : ℕ × (ℕ × ℕ), uTerm q.1 * cTerm q.2 := by
  refine tsum_eq_tsum_of_ne_zero_bij
    (fun x => ((x.1.1 + 1) * x.1.2.1, (x.1.1 + 1) * x.1.2.2)) ?_ ?_ ?_
  · -- injective
    rintro ⟨⟨d, a, a'⟩, hx⟩ ⟨⟨e, b, b'⟩, hy⟩ heq
    simp only [Function.mem_support, ne_eq] at hx hy
    have hcx : cTerm (a, a') ≠ 0 := fun h => hx (by simp [h])
    have hcy : cTerm (b, b') ≠ 0 := fun h => hy (by simp [h])
    obtain ⟨hx1, hx2, hx3⟩ := cTerm_ne_zero hcx
    obtain ⟨hy1, hy2, hy3⟩ := cTerm_ne_zero hcy
    simp only [Prod.mk.injEq] at heq
    obtain ⟨he1, he2⟩ := heq
    have hg : Nat.gcd ((d + 1) * a) ((d + 1) * a') = d + 1 := by
      rw [Nat.gcd_mul_left, hx3, Nat.mul_one]
    have hg' : Nat.gcd ((e + 1) * b) ((e + 1) * b') = e + 1 := by
      rw [Nat.gcd_mul_left, hy3, Nat.mul_one]
    have hde : d + 1 = e + 1 := by rw [← hg, ← hg', he1, he2]
    have hd : d = e := by omega
    subst hd
    have hab : a = b := Nat.eq_of_mul_eq_mul_left (by omega) he1
    have hab' : a' = b' := Nat.eq_of_mul_eq_mul_left (by omega) he2
    subst hab; subst hab'
    rfl
  · -- surjective onto the support of `gTerm`
    rintro p hp
    simp only [Function.mem_support, ne_eq] at hp
    obtain ⟨h1, h2⟩ := gTerm_ne_zero hp
    set g0 := Nat.gcd p.1 p.2 with hg0
    have hg0pos : 0 < g0 := Nat.gcd_pos_of_pos_left _ (by omega)
    have hd1 : g0 ∣ p.1 := Nat.gcd_dvd_left _ _
    have hd2 : g0 ∣ p.2 := Nat.gcd_dvd_right _ _
    set a := p.1 / g0 with ha
    set a' := p.2 / g0 with ha'
    have he1 : g0 * a = p.1 := Nat.mul_div_cancel' hd1
    have he2 : g0 * a' = p.2 := Nat.mul_div_cancel' hd2
    have hco : Nat.gcd a a' = 1 := Nat.coprime_div_gcd_div_gcd hg0pos
    have hpos1 : 1 ≤ a' := by
      rcases Nat.eq_zero_or_pos a' with h | h
      · rw [h, Nat.mul_zero] at he2; omega
      · omega
    have hlt : a' < a := by
      by_contra hc
      have : g0 * a ≤ g0 * a' := Nat.mul_le_mul_left _ (by omega)
      omega
    refine ⟨⟨(g0 - 1, (a, a')), ?_⟩, ?_⟩
    · simp only [Function.mem_support, ne_eq]
      exact ne_of_gt (mul_pos (uTerm_pos _) (cTerm_pos hpos1 hlt hco))
    · simp only [Nat.sub_add_cancel hg0pos]
      rw [he1, he2]
  · -- the values match
    rintro ⟨⟨d, a, a'⟩, hx⟩
    simp only [Function.mem_support, ne_eq] at hx
    have hcx : cTerm (a, a') ≠ 0 := fun h => hx (by simp [h])
    obtain ⟨hx1, hx2, hx3⟩ := cTerm_ne_zero hcx
    have hg : gTerm ((d + 1) * a, (d + 1) * a') = gTerm (a, a') / ((d + 1 : ℕ) : ℝ) ^ 3 :=
      gTerm_smul (by omega) hx1 hx2
    have hcg : cTerm (a, a') = gTerm (a, a') := by
      rw [cTerm_eq_gTerm, if_pos hx3]
    change gTerm ((d + 1) * a, (d + 1) * a') = uTerm d * cTerm (a, a')
    rw [hg, hcg, uTerm]
    push_cast
    ring

/-- **Step 2, assembled.**  `ζ(3)·C = (ζ(2,1) - S)/2`. -/
theorem zeta3_mul_cConst : zeta3 * cConst = (zeta21 - sConst) / 2 := by
  have hprod : Summable (fun q : ℕ × (ℕ × ℕ) => uTerm q.1 * cTerm q.2) :=
    uTerm_summable.mul_of_nonneg cTerm_summable (fun d => (uTerm_pos d).le) cTerm_nonneg
  rw [← tsum_uTerm, cConst, Summable.tsum_mul_tsum uTerm_summable cTerm_summable hprod,
    ← tsum_gTerm_eq, tsum_gTerm]

end BlockCycleRotation
