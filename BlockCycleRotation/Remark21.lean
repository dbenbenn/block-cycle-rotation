/-
# Remark 21

The paper rewrites the constant `C` of equation (const-c) as

```
C = 1/2 - S/(2·ζ(3)),     S = ∑_{x > y ≥ 1} 1/(y·(x+y)²),
```

equation (const-c-alternative).  The argument has three steps.

1. The summand `(2x+y)/(2x²(x+y)²)` equals `(1/(2y))(1/x² - 1/(x+y)²)`.
2. Multiplying by `ζ(3) = ∑_d 1/d³` removes the coprimality condition, because
   the summand is homogeneous of degree `-3` and every pair `A > A' ≥ 1`
   factors uniquely as `A = d·x`, `A' = d·y` with `d = gcd(A,A')`.
3. Euler's formula `ζ(2,1) = ζ(3)` for the resulting `∑_{x>y≥1} 1/(y·x²)`.

The paper cites step 3; Mathlib has no multiple-zeta-value theory, so it is
proved here from scratch in `Euler.lean`.
-/

import BlockCycleRotation.Constant

namespace BlockCycleRotation

open Finset

/-! ## The three series over all pairs

Each is supported on `x > y ≥ 1` and extended by zero, in the style of
`cTerm`. -/

/-- `cTerm` without the coprimality condition. -/
noncomputable def gTerm (p : ℕ × ℕ) : ℝ :=
  if 1 ≤ p.2 ∧ p.2 < p.1 then
    (2 * (p.1 : ℝ) + (p.2 : ℝ)) / (2 * (p.1 : ℝ) ^ 2 * ((p.1 : ℝ) + (p.2 : ℝ)) ^ 2)
  else 0

/-- The summand of `ζ(2,1) = ∑_{x > y ≥ 1} 1/(y·x²)`. -/
noncomputable def zTerm (p : ℕ × ℕ) : ℝ :=
  if 1 ≤ p.2 ∧ p.2 < p.1 then 1 / ((p.2 : ℝ) * (p.1 : ℝ) ^ 2) else 0

/-- The summand of `S = ∑_{x > y ≥ 1} 1/(y·(x+y)²)`. -/
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

/-- **Step 1 of Remark 21.**  `(2x+y)/(2x²(x+y)²) = (1/(2y))(1/x² - 1/(x+y)²)`. -/
theorem gTerm_eq (p : ℕ × ℕ) : gTerm p = (zTerm p - eTerm p) / 2 := by
  unfold gTerm zTerm eTerm
  split_ifs with h
  · obtain ⟨h1, h2⟩ := h
    have ha : (0 : ℝ) < (p.1 : ℝ) := by
      have : 0 < p.1 := by omega
      exact_mod_cast this
    have hy : (0 : ℝ) < (p.2 : ℝ) := by
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
second index does not, since `∑_{x > y} 1/x² ≤ 1/y` is the tail bound
`sum_inv_sq_tail_le`.  So the sums are taken columnwise. -/

theorem zTerm_col_sum_le (y : ℕ) (s : Finset ℕ) :
    ∑ x ∈ s, zTerm (x, y) ≤ 1 / (y : ℝ) ^ 2 := by
  rcases Nat.eq_zero_or_pos y with rfl | hy
  · simp [zTerm]
  · have hyR : (0 : ℝ) < (y : ℝ) := by exact_mod_cast hy
    have h1 : ∑ x ∈ s, zTerm (x, y)
        = ∑ x ∈ s.filter (fun x => y < x), (1 / (y : ℝ)) * (1 / (x : ℝ) ^ 2) := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun x _ => ?_
      unfold zTerm
      by_cases h : y < x
      · rw [if_pos ⟨hy, h⟩, if_pos h]
        field_simp
      · rw [if_neg (by tauto), if_neg h]
    rw [h1, ← Finset.mul_sum]
    have h3 := sum_inv_sq_tail_le hy (s.filter (fun x => y < x))
      (fun x hx => (Finset.mem_filter.1 hx).2)
    calc (1 / (y : ℝ)) * ∑ x ∈ s.filter (fun x => y < x), 1 / (x : ℝ) ^ 2
        ≤ (1 / (y : ℝ)) * (1 / (y : ℝ)) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = 1 / (y : ℝ) ^ 2 := by ring

theorem zTerm_col_summable (y : ℕ) : Summable (fun x => zTerm (x, y)) :=
  summable_of_sum_le (fun x => zTerm_nonneg (x, y)) (zTerm_col_sum_le y)

theorem zTerm_col_tsum_le (y : ℕ) : ∑' x, zTerm (x, y) ≤ 1 / (y : ℝ) ^ 2 :=
  Real.tsum_le_of_sum_le (fun x => zTerm_nonneg (x, y)) (zTerm_col_sum_le y)

theorem zTerm_summable : Summable zTerm := by
  refine (Equiv.prodComm ℕ ℕ).summable_iff.1 ?_
  change Summable (fun q : ℕ × ℕ => zTerm (q.2, q.1))
  have hnn : (0 : ℕ × ℕ → ℝ) ≤ fun q => zTerm (q.2, q.1) := fun q => zTerm_nonneg _
  rw [summable_prod_of_nonneg hnn]
  refine ⟨fun y => zTerm_col_summable y, ?_⟩
  have hg : Summable (fun y : ℕ => 1 / (y : ℝ) ^ 2) := by
    rw [Real.summable_one_div_nat_pow]; norm_num
  refine Summable.of_nonneg_of_le (fun y => ?_) (fun y => zTerm_col_tsum_le y) hg
  exact tsum_nonneg fun x => zTerm_nonneg _

theorem eTerm_le_zTerm (p : ℕ × ℕ) : eTerm p ≤ zTerm p := by
  unfold eTerm zTerm
  split_ifs with h
  · obtain ⟨h1, h2⟩ := h
    have hy : (0 : ℝ) < (p.2 : ℝ) := by
      have : 0 < p.2 := by omega
      exact_mod_cast this
    have ha : (0 : ℝ) < (p.1 : ℝ) := by
      have : 0 < p.1 := by omega
      exact_mod_cast this
    refine one_div_le_one_div_of_le (by positivity) ?_
    nlinarith [mul_nonneg hy.le (mul_nonneg ha.le hy.le),
      mul_nonneg hy.le (mul_nonneg hy.le hy.le)]
  · exact le_refl 0

theorem eTerm_summable : Summable eTerm :=
  zTerm_summable.of_nonneg_of_le eTerm_nonneg eTerm_le_zTerm

theorem gTerm_summable : Summable gTerm := by
  have h : gTerm = fun p => (zTerm p - eTerm p) / 2 := funext gTerm_eq
  rw [h]
  exact (zTerm_summable.sub eTerm_summable).div_const 2

/-- `ζ(2,1) = ∑_{x > y ≥ 1} 1/(y·x²)`. -/
noncomputable def zeta21 : ℝ := ∑' p, zTerm p

/-- `S = ∑_{x > y ≥ 1} 1/(y·(x+y)²)`, the series of eq. (const-c-alternative). -/
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
`(d·x, d·y)` with `d = gcd(A,A')` and `gcd(x,y) = 1`.  So multiplying the
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

theorem cTerm_pos {x y : ℕ} (h1 : 1 ≤ y) (h2 : y < x) (h3 : Nat.gcd x y = 1) :
    0 < cTerm (x, y) := by
  unfold cTerm
  rw [if_pos ⟨h1, h2, h3⟩]
  have hx : (0 : ℝ) < (x : ℝ) := by
    have : 0 < x := by omega
    exact_mod_cast this
  have hy : (0 : ℝ) < (y : ℝ) := by
    have : 0 < y := by omega
    exact_mod_cast this
  positivity

/-- **`gTerm` is homogeneous of degree `-3`.** -/
theorem gTerm_smul {k x y : ℕ} (hk : 0 < k) (h1 : 1 ≤ y) (h2 : y < x) :
    gTerm (k * x, k * y) = gTerm (x, y) / (k : ℝ) ^ 3 := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hx : (0 : ℝ) < (x : ℝ) := by
    have : 0 < x := by omega
    exact_mod_cast this
  have hy : (0 : ℝ) < (y : ℝ) := by
    have : 0 < y := by omega
    exact_mod_cast this
  have hk1 : 1 ≤ k * y := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hk2 : k * y < k * x := by
    rw [Nat.mul_comm k y, Nat.mul_comm k x]
    exact Nat.mul_lt_mul_of_lt_of_le h2 (le_refl k) hk
  unfold gTerm
  rw [if_pos ⟨hk1, hk2⟩, if_pos ⟨h1, h2⟩]
  push_cast
  field_simp

/-- **The `ζ(3)` unfolding.** -/
theorem tsum_gTerm_eq : ∑' p : ℕ × ℕ, gTerm p = ∑' q : ℕ × (ℕ × ℕ), uTerm q.1 * cTerm q.2 := by
  refine tsum_eq_tsum_of_ne_zero_bij
    (fun w => ((w.1.1 + 1) * w.1.2.1, (w.1.1 + 1) * w.1.2.2)) ?_ ?_ ?_
  · -- injective
    rintro ⟨⟨d, x, y⟩, hx⟩ ⟨⟨e, x', y'⟩, hy⟩ heq
    simp only [Function.mem_support, ne_eq] at hx hy
    have hcx : cTerm (x, y) ≠ 0 := fun h => hx (by simp [h])
    have hcy : cTerm (x', y') ≠ 0 := fun h => hy (by simp [h])
    obtain ⟨hx1, hx2, hx3⟩ := cTerm_ne_zero hcx
    obtain ⟨hy1, hy2, hy3⟩ := cTerm_ne_zero hcy
    simp only [Prod.mk.injEq] at heq
    obtain ⟨he1, he2⟩ := heq
    have hg : Nat.gcd ((d + 1) * x) ((d + 1) * y) = d + 1 := by
      rw [Nat.gcd_mul_left, hx3, Nat.mul_one]
    have hg' : Nat.gcd ((e + 1) * x') ((e + 1) * y') = e + 1 := by
      rw [Nat.gcd_mul_left, hy3, Nat.mul_one]
    have hde : d + 1 = e + 1 := by rw [← hg, ← hg', he1, he2]
    have hd : d = e := by omega
    subst hd
    have hab : x = x' := Nat.eq_of_mul_eq_mul_left (by omega) he1
    have hxy' : y = y' := Nat.eq_of_mul_eq_mul_left (by omega) he2
    subst hab; subst hxy'
    rfl
  · -- surjective onto the support of `gTerm`
    rintro p hp
    simp only [Function.mem_support, ne_eq] at hp
    obtain ⟨h1, h2⟩ := gTerm_ne_zero hp
    set g0 := Nat.gcd p.1 p.2 with hg0
    have hg0pos : 0 < g0 := Nat.gcd_pos_of_pos_left _ (by omega)
    have hd1 : g0 ∣ p.1 := Nat.gcd_dvd_left _ _
    have hd2 : g0 ∣ p.2 := Nat.gcd_dvd_right _ _
    set x := p.1 / g0 with hx
    set y := p.2 / g0 with hy
    have he1 : g0 * x = p.1 := Nat.mul_div_cancel' hd1
    have he2 : g0 * y = p.2 := Nat.mul_div_cancel' hd2
    have hco : Nat.gcd x y = 1 := Nat.coprime_div_gcd_div_gcd hg0pos
    have hpos1 : 1 ≤ y := by
      rcases Nat.eq_zero_or_pos y with h | h
      · rw [h, Nat.mul_zero] at he2; omega
      · omega
    have hlt : y < x := by
      by_contra hc
      have : g0 * x ≤ g0 * y := Nat.mul_le_mul_left _ (by omega)
      omega
    refine ⟨⟨(g0 - 1, (x, y)), ?_⟩, ?_⟩
    · simp only [Function.mem_support, ne_eq]
      exact ne_of_gt (mul_pos (uTerm_pos _) (cTerm_pos hpos1 hlt hco))
    · simp only [Nat.sub_add_cancel hg0pos]
      rw [he1, he2]
  · -- the values match
    rintro ⟨⟨d, x, y⟩, hx⟩
    simp only [Function.mem_support, ne_eq] at hx
    have hcx : cTerm (x, y) ≠ 0 := fun h => hx (by simp [h])
    obtain ⟨hx1, hx2, hx3⟩ := cTerm_ne_zero hcx
    have hg : gTerm ((d + 1) * x, (d + 1) * y) = gTerm (x, y) / ((d + 1 : ℕ) : ℝ) ^ 3 :=
      gTerm_smul (by omega) hx1 hx2
    have hcg : cTerm (x, y) = gTerm (x, y) := by
      rw [cTerm_eq_gTerm, if_pos hx3]
    change gTerm ((d + 1) * x, (d + 1) * y) = uTerm d * cTerm (x, y)
    rw [hg, hcg, uTerm]
    push_cast
    ring

/-- **Step 2, assembled.**  `ζ(3)·C = (ζ(2,1) - S)/2`. -/
theorem zeta3_mul_cConst : zeta3 * cConst = (zeta21 - sConst) / 2 := by
  have hprod : Summable (fun q : ℕ × (ℕ × ℕ) => uTerm q.1 * cTerm q.2) :=
    uTerm_summable.mul_of_nonneg cTerm_summable (fun d => (uTerm_pos d).le) cTerm_nonneg
  rw [← tsum_uTerm, cConst, Summable.tsum_mul_tsum uTerm_summable cTerm_summable hprod,
    ← tsum_gTerm_eq, tsum_gTerm]

/-! ## Step 3: Euler's `ζ(2,1) = ζ(3)`

Mathlib has no multiple-zeta-value theory, so the formula the paper cites is
proved here.  Writing `n = y` and `k = x - y`, the point is the identity

```
1/(n(n+k)²) + 1/(k(n+k)²) = 1/(n·k·(n+k)),
```

whose left side is `ζ(2,1)`'s summand plus the same with `n` and `k` swapped.
So the right side sums to `2·ζ(2,1)`.  Summing it instead over `k` first uses
only the telescoping `∑_k 1/(k(n+k)) = H_n/n`, giving `∑_n H_n/n² = ζ(2,1) +
ζ(3)`.  Hence `2·ζ(2,1) = ζ(2,1) + ζ(3)`. -/

open Filter Topology

/-- `harm a = ∑_{i=1}^{a-1} 1/i`. -/
noncomputable def harm (a : ℕ) : ℝ := ∑ i ∈ Finset.Ico 1 a, (1 : ℝ) / (i : ℝ)

theorem harm_eq_range (n : ℕ) : harm (n + 1) = ∑ j ∈ Finset.range n, 1 / ((j : ℝ) + 1) := by
  unfold harm
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  refine Finset.sum_congr rfl fun j _ => ?_
  push_cast
  ring_nf

theorem harm_succ {a : ℕ} (ha : 1 ≤ a) : harm (a + 1) = harm a + 1 / (a : ℝ) := by
  unfold harm
  rw [Finset.sum_Ico_succ_top ha]

theorem harm_nonneg (a : ℕ) : 0 ≤ harm a :=
  Finset.sum_nonneg fun i _ => by positivity

/-- The partial sums of the telescoping series. -/
theorem telescope_partial (n N : ℕ) (h : n ≤ N) :
    ∑ j ∈ Finset.range N, (1 / ((j : ℝ) + 1) - 1 / ((j : ℝ) + (n : ℝ) + 1))
      = (∑ j ∈ Finset.range n, 1 / ((j : ℝ) + 1))
        - ∑ j ∈ Finset.Ico N (N + n), 1 / ((j : ℝ) + 1) := by
  have h1 : ∑ j ∈ Finset.range N, 1 / ((j : ℝ) + (n : ℝ) + 1)
      = ∑ j ∈ Finset.Ico n (N + n), 1 / ((j : ℝ) + 1) := by
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring_nf
  rw [Finset.sum_sub_distrib, h1, Finset.range_eq_Ico, Finset.range_eq_Ico]
  have s1 : (∑ j ∈ Finset.Ico 0 n, 1 / ((j : ℝ) + 1))
      + ∑ j ∈ Finset.Ico n N, 1 / ((j : ℝ) + 1)
      = ∑ j ∈ Finset.Ico 0 N, 1 / ((j : ℝ) + 1) :=
    Finset.sum_Ico_consecutive _ (Nat.zero_le n) h
  have s2 : (∑ j ∈ Finset.Ico n N, 1 / ((j : ℝ) + 1))
      + ∑ j ∈ Finset.Ico N (N + n), 1 / ((j : ℝ) + 1)
      = ∑ j ∈ Finset.Ico n (N + n), 1 / ((j : ℝ) + 1) :=
    Finset.sum_Ico_consecutive _ h (by omega)
  linarith

/-- The moving window of `n` terms tends to zero. -/
theorem tendsto_window (n : ℕ) :
    Tendsto (fun N : ℕ => ∑ j ∈ Finset.Ico N (N + n), 1 / ((j : ℝ) + 1)) atTop (𝓝 0) := by
  have hz : Tendsto (fun N : ℕ => (n : ℝ) * (1 / ((N : ℝ) + 1))) atTop (𝓝 0) := by
    have h : Tendsto (fun N : ℕ => 1 / ((N : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 := h.const_mul (n : ℝ)
    rw [mul_zero] at h2
    exact h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hz
    (fun N => Finset.sum_nonneg fun j _ => by positivity) (fun N => ?_)
  calc ∑ j ∈ Finset.Ico N (N + n), 1 / ((j : ℝ) + 1)
      ≤ ∑ _j ∈ Finset.Ico N (N + n), 1 / ((N : ℝ) + 1) := by
        refine Finset.sum_le_sum fun j hj => ?_
        rw [Finset.mem_Ico] at hj
        have : (N : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj.1
        exact one_div_le_one_div_of_le (by positivity) (by linarith)
    _ = (n : ℝ) * (1 / ((N : ℝ) + 1)) := by
        rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
        simp

/-- The telescoping series `∑_j [1/(j+1) - 1/(j+n+1)]` sums to `H_n`. -/
theorem tsum_telescope (n : ℕ) :
    ∑' j : ℕ, (1 / ((j : ℝ) + 1) - 1 / ((j : ℝ) + (n : ℝ) + 1))
      = ∑ j ∈ Finset.range n, 1 / ((j : ℝ) + 1) := by
  have hsum : Summable (fun j : ℕ => 1 / ((j : ℝ) + 1) - 1 / ((j : ℝ) + (n : ℝ) + 1)) := by
    have hg : Summable (fun j : ℕ => (n : ℝ) * (1 / ((j : ℝ) + 1) ^ 2)) := by
      have h : Summable (fun j : ℕ => 1 / ((j : ℝ) + 1) ^ 2) := by
        have h0 : Summable (fun m : ℕ => 1 / (m : ℝ) ^ 2) := by
          rw [Real.summable_one_div_nat_pow]; norm_num
        refine ((summable_nat_add_iff 1).2 h0).congr fun j => ?_
        push_cast; ring
      exact h.mul_left _
    refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) hg
    · have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
      have h1 : 1 / ((j : ℝ) + (n : ℝ) + 1) ≤ 1 / ((j : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      linarith
    · have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
      have hjn : (0 : ℝ) < (j : ℝ) + (n : ℝ) + 1 := by positivity
      have key : 1 / ((j : ℝ) + 1) - 1 / ((j : ℝ) + (n : ℝ) + 1)
          = (n : ℝ) / (((j : ℝ) + 1) * ((j : ℝ) + (n : ℝ) + 1)) := by
        field_simp
        ring
      have hr : (n : ℝ) * (1 / ((j : ℝ) + 1) ^ 2) = (n : ℝ) / ((j : ℝ) + 1) ^ 2 := by ring
      rw [key, hr]
      gcongr
      nlinarith
  refine (hsum.hasSum_iff_tendsto_nat.2 ?_).tsum_eq
  have heq : (fun N : ℕ => ∑ j ∈ Finset.range N,
        (1 / ((j : ℝ) + 1) - 1 / ((j : ℝ) + (n : ℝ) + 1)))
      =ᶠ[atTop] (fun N : ℕ => (∑ j ∈ Finset.range n, 1 / ((j : ℝ) + 1))
        - ∑ j ∈ Finset.Ico N (N + n), 1 / ((j : ℝ) + 1)) := by
    filter_upwards [eventually_ge_atTop n] with N hN
    exact telescope_partial n N hN
  refine Tendsto.congr' heq.symm ?_
  have hlim : Tendsto (fun N : ℕ => (∑ j ∈ Finset.range n, 1 / ((j : ℝ) + 1))
      - ∑ j ∈ Finset.Ico N (N + n), 1 / ((j : ℝ) + 1)) atTop
      (𝓝 ((∑ j ∈ Finset.range n, 1 / ((j : ℝ) + 1)) - 0)) :=
    tendsto_const_nhds.sub (tendsto_window n)
  rw [sub_zero] at hlim
  exact hlim

/-! ### The two symmetric series -/

/-- The tail of `∑ 1/m²` past `n`. -/
theorem tsum_tail_inv_sq {n : ℕ} (hn : 0 < n) :
    ∑' j : ℕ, 1 / ((n : ℝ) + (j : ℝ) + 1) ^ 2 ≤ 1 / (n : ℝ) := by
  refine Real.tsum_le_of_sum_le (fun j => by positivity) fun s => ?_
  have hcast : ∀ j : ℕ, 1 / ((n : ℝ) + (j : ℝ) + 1) ^ 2 = 1 / (((n + j + 1 : ℕ) : ℝ)) ^ 2 := by
    intro j; push_cast; ring
  simp only [hcast]
  have himg : ∑ x ∈ s.image (fun j => n + j + 1), 1 / ((x : ℝ)) ^ 2
      = ∑ x ∈ s, 1 / (((n + x + 1 : ℕ) : ℝ)) ^ 2 :=
    Finset.sum_image (by
      intro x _ y _ h
      have h' : n + x + 1 = n + y + 1 := h
      omega)
  rw [← himg]
  refine sum_inv_sq_tail_le hn _ ?_
  intro a ha
  simp only [Finset.mem_image] at ha
  obtain ⟨x, -, rfl⟩ := ha
  omega

/-- `1/(n(n+k)²)` at `n = i+1`, `k = j+1`. -/
noncomputable def pTerm (q : ℕ × ℕ) : ℝ :=
  1 / (((q.1 : ℝ) + 1) * (((q.1 : ℝ) + 1) + ((q.2 : ℝ) + 1)) ^ 2)

theorem pTerm_pos (q : ℕ × ℕ) : 0 < pTerm q := by
  unfold pTerm; positivity

theorem pTerm_row_summable (i : ℕ) : Summable (fun j => pTerm (i, j)) := by
  have hg : Summable (fun j : ℕ => 1 / (((i : ℝ) + 1) * ((j : ℝ) + 1) ^ 2)) := by
    have h : Summable (fun j : ℕ => 1 / ((j : ℝ) + 1) ^ 2) := by
      have h0 : Summable (fun m : ℕ => 1 / (m : ℝ) ^ 2) := by
        rw [Real.summable_one_div_nat_pow]; norm_num
      refine ((summable_nat_add_iff 1).2 h0).congr fun j => ?_
      push_cast; ring
    refine (h.mul_left (1 / ((i : ℝ) + 1))).congr fun j => ?_
    field_simp
  refine Summable.of_nonneg_of_le (fun j => (pTerm_pos _).le) (fun j => ?_) hg
  unfold pTerm
  refine one_div_le_one_div_of_le (by positivity) ?_
  have hi0 : (0 : ℝ) ≤ (i : ℝ) := by positivity
  have hj0 : (0 : ℝ) ≤ (j : ℝ) := by positivity
  have h1 : ((j : ℝ) + 1) ^ 2 ≤ (((i : ℝ) + 1) + ((j : ℝ) + 1)) ^ 2 := by nlinarith
  have h2 : (0 : ℝ) < (i : ℝ) + 1 := by positivity
  nlinarith

theorem pTerm_row_tsum_le (i : ℕ) : ∑' j, pTerm (i, j) ≤ 1 / ((i : ℝ) + 1) ^ 2 := by
  have hi : 0 < i + 1 := by omega
  have heq : ∀ j : ℕ, pTerm (i, j)
      = (1 / ((i : ℝ) + 1)) * (1 / (((i + 1 : ℕ) : ℝ) + (j : ℝ) + 1) ^ 2) := by
    intro j
    unfold pTerm
    push_cast
    field_simp
    ring
  rw [tsum_congr heq, tsum_mul_left]
  have ht := tsum_tail_inv_sq hi
  have hpos : (0 : ℝ) < ((i + 1 : ℕ) : ℝ) := by positivity
  calc (1 / ((i : ℝ) + 1)) * ∑' j : ℕ, 1 / (((i + 1 : ℕ) : ℝ) + (j : ℝ) + 1) ^ 2
      ≤ (1 / ((i : ℝ) + 1)) * (1 / ((i + 1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left ht (by positivity)
    _ = 1 / ((i : ℝ) + 1) ^ 2 := by
        have hc : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by push_cast; ring
        rw [hc]
        field_simp

theorem pTerm_summable : Summable pTerm := by
  have hnn : (0 : ℕ × ℕ → ℝ) ≤ pTerm := fun q => (pTerm_pos q).le
  rw [summable_prod_of_nonneg hnn]
  refine ⟨pTerm_row_summable, ?_⟩
  have hg : Summable (fun i : ℕ => 1 / ((i : ℝ) + 1) ^ 2) := by
    have h0 : Summable (fun m : ℕ => 1 / (m : ℝ) ^ 2) := by
      rw [Real.summable_one_div_nat_pow]; norm_num
    refine ((summable_nat_add_iff 1).2 h0).congr fun j => ?_
    push_cast; ring
  exact Summable.of_nonneg_of_le (fun i => tsum_nonneg fun j => (pTerm_pos _).le)
    pTerm_row_tsum_le hg

/-- **`∑ pTerm = ζ(2,1)`**: the reindexing `(i,j) ↦ (x,y) = (i+j+2, i+1)`. -/
theorem tsum_pTerm : ∑' p : ℕ × ℕ, zTerm p = ∑' q : ℕ × ℕ, pTerm q := by
  refine tsum_eq_tsum_of_ne_zero_bij (fun q => (q.1.1 + q.1.2 + 2, q.1.1 + 1)) ?_ ?_ ?_
  · intro x y heq
    obtain ⟨⟨i, j⟩, hx⟩ := x
    obtain ⟨⟨i', j'⟩, hy⟩ := y
    simp only [Prod.mk.injEq] at heq
    have hij : i = i' ∧ j = j' := by omega
    simp only [Subtype.mk.injEq, Prod.mk.injEq]
    exact ⟨hij.1, hij.2⟩
  · rintro ⟨p1, p2⟩ hp
    simp only [Function.mem_support, ne_eq] at hp
    have hz : 1 ≤ p2 ∧ p2 < p1 := by
      unfold zTerm at hp
      split_ifs at hp with hc
      · exact hc
      · exact absurd rfl hp
    refine ⟨⟨(p2 - 1, p1 - p2 - 1), ?_⟩, ?_⟩
    · simp only [Function.mem_support, ne_eq]
      exact ne_of_gt (pTerm_pos _)
    · simp only [Prod.mk.injEq]
      omega
  · rintro ⟨⟨i, j⟩, -⟩
    change zTerm (i + j + 2, i + 1) = pTerm (i, j)
    unfold zTerm pTerm
    rw [if_pos (by omega)]
    push_cast
    ring_nf

/-- `1/(n·k·(n+k))` at `n = i+1`, `k = j+1`. -/
noncomputable def qTerm (q : ℕ × ℕ) : ℝ :=
  1 / ((((q.2 : ℝ) + 1) * ((q.1 : ℝ) + 1)) * (((q.1 : ℝ) + 1) + ((q.2 : ℝ) + 1)))

/-- **The key identity.**  `1/(n(n+k)²) + 1/(k(n+k)²) = 1/(n·k·(n+k))`. -/
theorem pTerm_add_swap (q : ℕ × ℕ) : pTerm q + pTerm (q.2, q.1) = qTerm q := by
  have h1 : (0 : ℝ) < (q.1 : ℝ) + 1 := by positivity
  have h2 : (0 : ℝ) < (q.2 : ℝ) + 1 := by positivity
  unfold pTerm qTerm
  field_simp
  ring

theorem pTerm_swap_summable : Summable (fun q : ℕ × ℕ => pTerm (q.2, q.1)) :=
  (Equiv.prodComm ℕ ℕ).summable_iff.2 pTerm_summable

theorem tsum_pTerm_swap : ∑' q : ℕ × ℕ, pTerm (q.2, q.1) = ∑' q : ℕ × ℕ, pTerm q :=
  (Equiv.prodComm ℕ ℕ).tsum_eq pTerm

theorem qTerm_summable : Summable qTerm :=
  (pTerm_summable.add pTerm_swap_summable).congr fun q => pTerm_add_swap q

/-- **The swap symmetry gives `2·ζ(2,1)`.** -/
theorem tsum_qTerm_eq_two : ∑' q : ℕ × ℕ, qTerm q = 2 * zeta21 := by
  have h : ∑' q : ℕ × ℕ, qTerm q = (∑' q : ℕ × ℕ, pTerm q) + ∑' q : ℕ × ℕ, pTerm (q.2, q.1) := by
    rw [← Summable.tsum_add pTerm_summable pTerm_swap_summable]
    exact tsum_congr fun q => (pTerm_add_swap q).symm
  rw [h, tsum_pTerm_swap, zeta21, tsum_pTerm]
  ring

/-- **The row sums give `H_n/n²`.** -/
theorem qTerm_row (i : ℕ) : ∑' j : ℕ, qTerm (i, j) = harm (i + 2) / ((i : ℝ) + 1) ^ 2 := by
  have hn : (0 : ℝ) < (i : ℝ) + 1 := by positivity
  have hc : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by push_cast; ring
  have heq : ∀ j : ℕ, qTerm (i, j)
      = (1 / ((i : ℝ) + 1) ^ 2)
        * (1 / ((j : ℝ) + 1) - 1 / ((j : ℝ) + ((i + 1 : ℕ) : ℝ) + 1)) := by
    intro j
    have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have hjn : (0 : ℝ) < (j : ℝ) + ((i : ℝ) + 1) + 1 := by positivity
    rw [hc]
    unfold qTerm
    field_simp
    ring
  rw [tsum_congr heq, tsum_mul_left, tsum_telescope (i + 1), ← harm_eq_range]
  ring

theorem tsum_qTerm_rows :
    ∑' q : ℕ × ℕ, qTerm q = ∑' i : ℕ, harm (i + 2) / ((i : ℝ) + 1) ^ 2 := by
  rw [qTerm_summable.tsum_prod]
  exact tsum_congr qTerm_row

/-! ### The rows of `ζ(2,1)` -/

theorem zTerm_row (x : ℕ) : ∑' y : ℕ, zTerm (x, y) = harm x / (x : ℝ) ^ 2 := by
  have hsupp : ∀ y ∉ Finset.range x, zTerm (x, y) = 0 := by
    intro y hy
    simp only [Finset.mem_range, not_lt] at hy
    unfold zTerm
    rw [if_neg]
    rintro ⟨-, h2⟩
    omega
  rw [tsum_eq_sum hsupp]
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp [harm]
  · rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hx]
    have h0 : zTerm (x, 0) = 0 := by
      unfold zTerm; rw [if_neg]; rintro ⟨h1, -⟩; omega
    rw [h0, zero_add]
    unfold harm
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [Finset.mem_Ico] at hy
    have hy0 : (0 : ℝ) < (y : ℝ) := by
      have : 0 < y := by omega
      exact_mod_cast this
    have haR : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx
    unfold zTerm
    rw [if_pos ⟨by omega, by omega⟩]
    field_simp

theorem harmRow_summable : Summable (fun a : ℕ => harm a / (a : ℝ) ^ 2) := by
  have hnn : (0 : ℕ × ℕ → ℝ) ≤ zTerm := fun p => zTerm_nonneg p
  have h := (summable_prod_of_nonneg hnn).1 zTerm_summable
  exact h.2.congr fun a => zTerm_row a

theorem zeta21_eq : zeta21 = ∑' a : ℕ, harm a / (a : ℝ) ^ 2 := by
  rw [zeta21, zTerm_summable.tsum_prod]
  exact tsum_congr zTerm_row

theorem inv_cube_summable : Summable (fun a : ℕ => 1 / (a : ℝ) ^ 3) := by
  rw [Real.summable_one_div_nat_pow]; norm_num

theorem zeta3_eq : zeta3 = ∑' a : ℕ, 1 / (a : ℝ) ^ 3 := by
  have hshift : Summable (fun n : ℕ => 1 / (((n + 1 : ℕ)) : ℝ) ^ 3) :=
    (summable_nat_add_iff 1).2 inv_cube_summable
  have h1 : ∑' a : ℕ, 1 / (a : ℝ) ^ 3
      = 1 / (((0 : ℕ)) : ℝ) ^ 3 + ∑' n : ℕ, 1 / (((n + 1 : ℕ)) : ℝ) ^ 3 :=
    tsum_eq_zero_add' hshift
  have h2 : (1 : ℝ) / (((0 : ℕ)) : ℝ) ^ 3 = 0 := by norm_num
  have h3 : ∑' n : ℕ, 1 / (((n + 1 : ℕ)) : ℝ) ^ 3 = zeta3 := by
    rw [zeta3]
    exact tsum_congr fun n => by push_cast; ring
  rw [h1, h2, h3, zero_add]

/-! ### Euler's formula -/

/-- **Euler's `ζ(2,1) = ζ(3)`.** -/
theorem euler_zeta21 : zeta21 = zeta3 := by
  have hsum : Summable (fun a : ℕ => harm a / (a : ℝ) ^ 2 + 1 / (a : ℝ) ^ 3) :=
    harmRow_summable.add inv_cube_summable
  have hrow : ∑' q : ℕ × ℕ, qTerm q = zeta21 + zeta3 := by
    rw [tsum_qTerm_rows, zeta21_eq, zeta3_eq,
      ← Summable.tsum_add harmRow_summable inv_cube_summable,
      tsum_eq_zero_add' ((summable_nat_add_iff 1).2 hsum)]
    have hzero : harm 0 / ((0 : ℕ) : ℝ) ^ 2 + 1 / ((0 : ℕ) : ℝ) ^ 3 = 0 := by
      simp [harm]
    rw [hzero, zero_add]
    refine tsum_congr fun i => ?_
    have hi : (0 : ℝ) < (i : ℝ) + 1 := by positivity
    have hc : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by push_cast; ring
    rw [hc, harm_succ (by omega : 1 ≤ i + 1), hc]
    field_simp
  have h2 := tsum_qTerm_eq_two
  rw [hrow] at h2
  linarith

/-! ## Step 4: equation (const-c-alternative) -/

theorem zeta3_pos : (0 : ℝ) < zeta3 := by
  have h1 : uTerm 0 ≤ ∑' d, uTerm d :=
    uTerm_summable.le_tsum 0 (fun j _ => (uTerm_pos j).le)
  have h2 : (0 : ℝ) < uTerm 0 := uTerm_pos 0
  rw [← tsum_uTerm]
  linarith

/-- **Remark 21.**  `C = 1/2 - S/(2·ζ(3))`. -/
theorem cConst_eq_alternative : cConst = 1 / 2 - sConst / (2 * zeta3) := by
  have hz : (0 : ℝ) < zeta3 := zeta3_pos
  have h := zeta3_mul_cConst
  rw [euler_zeta21] at h
  field_simp at h ⊢
  linarith

/-- **Truncating `S` bounds `C` from above**, the closing observation of
Remark 21: the terms of `S` are nonnegative, so every partial sum is a lower
bound for `S` and hence gives an upper bound for `C`. -/
theorem cConst_le_truncation (s : Finset (ℕ × ℕ)) :
    cConst ≤ 1 / 2 - (∑ p ∈ s, eTerm p) / (2 * zeta3) := by
  have hz : (0 : ℝ) < zeta3 := zeta3_pos
  have hle : ∑ p ∈ s, eTerm p ≤ sConst :=
    eTerm_summable.sum_le_tsum s (fun p _ => eTerm_nonneg p)
  rw [cConst_eq_alternative]
  have hdiv : (∑ p ∈ s, eTerm p) / (2 * zeta3) ≤ sConst / (2 * zeta3) :=
    div_le_div_of_nonneg_right hle (by positivity)
  linarith

/-- The same, for `D = 1 + 4C`. -/
theorem dConst_le_truncation (s : Finset (ℕ × ℕ)) :
    dConst ≤ 3 - 2 * (∑ p ∈ s, eTerm p) / zeta3 := by
  have h := cConst_le_truncation s
  have hz : (0 : ℝ) < zeta3 := zeta3_pos
  rw [dConst]
  have hrw : 4 * (1 / 2 - (∑ p ∈ s, eTerm p) / (2 * zeta3))
      = 2 - 2 * (∑ p ∈ s, eTerm p) / zeta3 := by
    field_simp
    ring
  nlinarith [h, hrw]

end BlockCycleRotation
