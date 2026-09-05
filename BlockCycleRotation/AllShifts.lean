/-
# Averaging over all shifts

Remark 20.  A run of the Euclidean algorithm on `(n,k)` with
`k` in the upper half first produces the remainder `k` and then repeats the run
of `(n, n-k)`, so

```
remSum n k = k + remSum n (n - k).
```

Summing over `1 ≤ k ≤ n` therefore counts the lower-half remainder sums twice
and adds `∑_{k > n/2} k = 3n²/8 + O(n)`, giving the average

```
(1/n) ∑_{k=1}^{n} remSum n k = (3/8 + 2C)·n + O(n^{1/2+ε}).
```

**Departure from the paper.**  The paper states the reflection for
`n > k ≥ n/2`.  The hypothesis has to be strict: at `2k = n` it would read
`k = k + k`.  Indeed `remSum n (n/2) = n/2` while `k + remSum n (n-k) = n`
there.  The conclusion is unaffected — that single term contributes `O(n)` to a
sum of size `Θ(n²)` — and the proof below uses `n < 2k` throughout.
-/

import BlockCycleRotation.Theorem13

namespace BlockCycleRotation

open Filter Topology

/-! ## The reflection -/

/-- Shifts in the upper half: `2k > n`. -/
def bigShifts (n : ℕ) : Finset ℕ := (Finset.Icc 1 n).filter (fun k => ¬ (2 * k ≤ n))

/-- Shifts strictly below the midpoint, `0` included. -/
def smallShifts (n : ℕ) : Finset ℕ := (Finset.range n).filter (fun j => 2 * j < n)

theorem mem_bigShifts {n k : ℕ} : k ∈ bigShifts n ↔ (1 ≤ k ∧ k ≤ n) ∧ n < 2 * k := by
  rw [bigShifts, Finset.mem_filter, Finset.mem_Icc]
  omega

theorem mem_smallShifts {n j : ℕ} : j ∈ smallShifts n ↔ j < n ∧ 2 * j < n := by
  rw [smallShifts, Finset.mem_filter, Finset.mem_range]

/-- **The reflection.**  For `2k > n` the run on `(n,k)` yields `k` and then
repeats the run on `(n, n-k)`. -/
theorem remSum_reflect {n k : ℕ} (hk : k ≤ n) (h : n < 2 * k) :
    remSum n k = k + remSum n (n - k) := by
  have hk0 : k ≠ 0 := by omega
  have hmod : n % k = n - k := by
    rcases Nat.eq_or_lt_of_le hk with rfl | hlt
    · simp
    · rw [Nat.mod_eq_sub_mod hk, Nat.mod_eq_of_lt (by omega)]
  have hstep : remSum n (n - k) = remSum k (n - k) := by
    have h1 : k + (n - k) = n := by omega
    calc remSum n (n - k) = remSum (k + (n - k)) (n - k) := by rw [h1]
      _ = remSum k (n - k) := remSum_step
  rw [remSum_of_pos n hk0, hmod, hstep]

/-! ## The index sets -/

theorem allShifts_eq_filter' {n : ℕ} (hn : 0 < n) :
    allShifts n = (Finset.Icc 1 n).filter (fun k => 2 * k ≤ n) := by
  ext k
  rw [mem_allShifts, Finset.mem_filter, Finset.mem_Icc]
  omega

theorem sum_Icc_split {n : ℕ} (hn : 0 < n) (f : ℕ → ℕ) :
    ∑ k ∈ Finset.Icc 1 n, f k
      = (∑ k ∈ allShifts n, f k) + ∑ k ∈ bigShifts n, f k := by
  rw [allShifts_eq_filter' hn, bigShifts]
  exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm

/-- The reflection is a bijection between the upper-half shifts and the
strictly-lower-half ones. -/
theorem sum_reflect_bij {n : ℕ} :
    ∑ k ∈ bigShifts n, remSum n (n - k) = ∑ j ∈ smallShifts n, remSum n j := by
  refine Finset.sum_bij' (i := fun k _ => n - k) (j := fun j _ => n - j) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    rw [mem_bigShifts] at hk
    rw [mem_smallShifts]
    omega
  · intro j hj
    rw [mem_smallShifts] at hj
    rw [mem_bigShifts]
    omega
  · intro k hk
    rw [mem_bigShifts] at hk
    omega
  · intro j hj
    rw [mem_smallShifts] at hj
    omega
  · intro k _
    rfl

/-- The upper-half remainder sums, reflected. -/
theorem sum_bigShifts_remSum {n : ℕ} :
    ∑ k ∈ bigShifts n, remSum n k
      = (∑ k ∈ bigShifts n, k) + ∑ j ∈ smallShifts n, remSum n j := by
  rw [← sum_reflect_bij, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [mem_bigShifts] at hk
  exact remSum_reflect hk.1.2 hk.2

/-! ## Comparing the two lower-half sums

They differ only by the midpoint term `remSum n (n/2)`, present when `n` is
even, which is at most `n`. -/

theorem allShifts_eq_Icc (n : ℕ) : allShifts n = Finset.Icc 1 (n / 2) := by
  ext k
  rw [mem_allShifts, Finset.mem_Icc]
  omega

theorem remSum_le_self {n k : ℕ} (h : 2 * k ≤ n) : remSum n k ≤ n := by
  have := remSum_add_gcd_le_self h
  omega

theorem sum_smallShifts_le {n : ℕ} (hn : 0 < n) :
    ∑ j ∈ smallShifts n, remSum n j ≤ ∑ k ∈ allShifts n, remSum n k := by
  have h0 : (0 : ℕ) ∉ allShifts n := by
    rw [mem_allShifts]
    omega
  have hsub : smallShifts n ⊆ insert 0 (allShifts n) := by
    intro j hj
    rw [mem_smallShifts] at hj
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (mem_allShifts.2 ⟨by omega, hj0, by omega⟩)
  calc ∑ j ∈ smallShifts n, remSum n j
      ≤ ∑ j ∈ insert 0 (allShifts n), remSum n j :=
        Finset.sum_le_sum_of_subset hsub
    _ = ∑ k ∈ allShifts n, remSum n k := by
        rw [Finset.sum_insert h0, remSum_zero, zero_add]

theorem sum_allShifts_le_smallShifts {n : ℕ} (hn : 0 < n) :
    ∑ k ∈ allShifts n, remSum n k ≤ (∑ j ∈ smallShifts n, remSum n j) + n := by
  have hsub : allShifts n ⊆ insert (n / 2) (smallShifts n) := by
    intro k hk
    obtain ⟨hkn, hk1, hk2⟩ := mem_allShifts.1 hk
    rcases lt_or_eq_of_le hk2 with hlt | heq
    · exact Finset.mem_insert_of_mem (mem_smallShifts.2 ⟨by omega, by omega⟩)
    · have hk' : k = n / 2 := by omega
      rw [hk']
      exact Finset.mem_insert_self _ _
  have hmid : remSum n (n / 2) ≤ n := remSum_le_self (by omega)
  refine le_trans (Finset.sum_le_sum_of_subset hsub) ?_
  by_cases hm : n / 2 ∈ smallShifts n
  · rw [Finset.insert_eq_self.2 hm]
    omega
  · rw [Finset.sum_insert hm]
    omega

/-! ## The arithmetic sum `∑_{k > n/2} k` -/

theorem two_mul_sum_Icc (m : ℕ) : 2 * ∑ k ∈ Finset.Icc 1 m, k = m * (m + 1) := by
  have hIcc : Finset.Icc 1 m = Finset.Ico 1 (m + 1) := by
    ext k
    rw [Finset.mem_Icc, Finset.mem_Ico]
    omega
  have h : ∑ k ∈ Finset.Icc 1 m, k = ∑ i ∈ Finset.range (m + 1), i := by
    rw [hIcc, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < m + 1)]
    simp
  rw [h]
  have h2 := Finset.sum_range_id_mul_two (m + 1)
  rw [Nat.add_sub_cancel] at h2
  have hcomm : (m + 1) * m = m * (m + 1) := Nat.mul_comm _ _
  omega

theorem two_mul_sum_bigShifts {n : ℕ} (hn : 0 < n) :
    2 * (∑ k ∈ bigShifts n, k) + (n / 2) * (n / 2 + 1) = n * (n + 1) := by
  have hsplit := sum_Icc_split hn (fun k => k)
  rw [allShifts_eq_Icc] at hsplit
  have h1 := two_mul_sum_Icc n
  have h2 := two_mul_sum_Icc (n / 2)
  omega

/-- `∑_{k > n/2} k` is `3n²/8` up to `n`. -/
theorem sum_bigShifts_id_close {n : ℕ} (hn : 0 < n) :
    |((∑ k ∈ bigShifts n, k : ℕ) : ℝ) - 3 * (n : ℝ) ^ 2 / 8| ≤ (n : ℝ) := by
  have hkey := two_mul_sum_bigShifts hn
  have hm : 2 * (n / 2) + n % 2 = n := Nat.div_add_mod n 2 ▸ by omega
  have hr : n % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have hkeyR : 2 * ((∑ k ∈ bigShifts n, k : ℕ) : ℝ)
      + ((n / 2 : ℕ) : ℝ) * (((n / 2 : ℕ) : ℝ) + 1) = (n : ℝ) * ((n : ℝ) + 1) := by
    exact_mod_cast hkey
  have hmR : 2 * ((n / 2 : ℕ) : ℝ) + ((n % 2 : ℕ) : ℝ) = (n : ℝ) := by exact_mod_cast hm
  have hrR : ((n % 2 : ℕ) : ℝ) < 2 := by exact_mod_cast hr
  have hr0 : (0 : ℝ) ≤ ((n % 2 : ℕ) : ℝ) := by positivity
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [abs_le]
  constructor <;> nlinarith [hkeyR, hmR, hrR, hr0, hn1]

/-! ## Remark 20 -/

/-- Summing over all shifts counts the lower half twice, up to the midpoint
term and `∑_{k > n/2} k`. -/
theorem sum_Icc_bounds {n : ℕ} (hn : 0 < n) :
    2 * (∑ k ∈ allShifts n, remSum n k) + (∑ k ∈ bigShifts n, k)
        ≤ (∑ k ∈ Finset.Icc 1 n, remSum n k) + n
      ∧ (∑ k ∈ Finset.Icc 1 n, remSum n k)
        ≤ 2 * (∑ k ∈ allShifts n, remSum n k) + (∑ k ∈ bigShifts n, k) := by
  have hS := sum_Icc_split hn (fun k => remSum n k)
  have hbig := sum_bigShifts_remSum (n := n)
  have h1 := sum_smallShifts_le hn
  have h2 := sum_allShifts_le_smallShifts hn
  omega

/-- **Remark 20.**  The remainder sum averaged over `1 ≤ k ≤ n` is
`(3/8 + 2C)·n + O(n^{1/2+ε})`. -/
theorem remark_all_shifts {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 0 < n →
      |((∑ k ∈ Finset.Icc 1 n, remSum n k : ℕ) : ℝ) / (n : ℝ)
          - (3 / 8 + 2 * cConst) * (n : ℝ)|
        ≤ K * (n : ℝ) ^ (1 / 2 + ε) := by
  obtain ⟨K1, hK1, hA⟩ := sum_remSum_isBigO hε
  refine ⟨2 * K1 + 2, by positivity, fun n hn => ?_⟩
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hpow : (1 : ℝ) ≤ (n : ℝ) ^ (1 / 2 + ε : ℝ) := Real.one_le_rpow hnR (by linarith)
  set S : ℝ := ((∑ k ∈ Finset.Icc 1 n, remSum n k : ℕ) : ℝ) with hSdef
  set A : ℝ := ((∑ k ∈ allShifts n, remSum n k : ℕ) : ℝ) with hAdef
  set B : ℝ := ((∑ k ∈ bigShifts n, k : ℕ) : ℝ) with hBdef
  obtain ⟨hb1, hb2⟩ := sum_Icc_bounds hn
  have hb1R : 2 * A + B ≤ S + (n : ℝ) := by rw [hSdef, hAdef, hBdef]; exact_mod_cast hb1
  have hb2R : S ≤ 2 * A + B := by rw [hSdef, hAdef, hBdef]; exact_mod_cast hb2
  have hAb : |A - cConst * (n : ℝ) ^ 2| ≤ K1 * (n : ℝ) ^ (3 / 2 + ε : ℝ) := hA n hn
  have hBb : |B - 3 * (n : ℝ) ^ 2 / 8| ≤ (n : ℝ) := sum_bigShifts_id_close hn
  -- the numerator estimate
  have hnum : |S - (3 / 8 + 2 * cConst) * (n : ℝ) ^ 2|
      ≤ 2 * (K1 * (n : ℝ) ^ (3 / 2 + ε : ℝ)) + 2 * (n : ℝ) := by
    rw [abs_le] at hAb hBb ⊢
    constructor <;> linarith [hAb.1, hAb.2, hBb.1, hBb.2, hb1R, hb2R]
  -- divide by `n`
  have hdiv : S / (n : ℝ) - (3 / 8 + 2 * cConst) * (n : ℝ)
      = (S - (3 / 8 + 2 * cConst) * (n : ℝ) ^ 2) / (n : ℝ) := by
    field_simp
  rw [hdiv, abs_div, abs_of_pos hnpos, div_le_iff₀ hnpos]
  have hr : (n : ℝ) ^ (3 / 2 + ε : ℝ) = (n : ℝ) ^ (1 / 2 + ε : ℝ) * (n : ℝ) := by
    rw [show (3 / 2 + ε : ℝ) = (1 / 2 + ε) + 1 by ring, Real.rpow_add hnpos, Real.rpow_one]
  rw [hr] at hnum
  nlinarith [hnum, hpow, hnpos, hK1]

end BlockCycleRotation
