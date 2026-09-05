/-
# The buffered variant

The closing remark of §3 introduces `f_β(x) := μ(1,x,β)`, the number of moves
per element when the algorithm may use a buffer of size `β·n`.  Equation
(def-mu-nu) is the recursion

```
μ(N,ℓ,β) - N  =  ℓ                            if ℓ ≤ β,
                 2ℓ + μ(N',ℓ',β) - N'         otherwise,
```

so with `ψ_β(x) := μ(1,x,β) - 1` and the relative maps of `Theorem10.lean`,

```
ψ_β(x) = x                              if x ≤ β,
         2x + Out(x)·ψ_{β/Out(x)}(In(x)) otherwise,
```

the buffer being of fixed absolute size, hence of relative size `β/Out(x)` in
the subproblem.  Since `Out ≤ 2/3`, the relative buffer grows geometrically, so
for `β > 0` the recursion terminates: unlike `ψ`, `ψ_β` is a *finite* sum.

Writing `segᵢ(x)` for the relative size of the `i`-th segment — the `i`-th term
of the Euclidean remainder sequence, divided by `n` — the recursion unravels to

```
ψ_β(x) = 2·∑_{i < T} segᵢ(x) + seg_T(x),    T = least i with segᵢ(x) ≤ β,
```

which is how `psiBuf` is defined here.  For `β = 0` the same formula with
`T = ∞` is `ψ`, and indeed `ψ - ψ_β ≤ 6β`.
-/

import BlockCycleRotation.Theorem10
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace BlockCycleRotation

open Filter Topology

/-! ## Segments -/

/-- The relative size of the `i`-th segment.  At `x = k/n` this is `kᵢ/n`. -/
noncomputable def seg (x : ℝ) (i : ℕ) : ℝ :=
  (∏ m ∈ Finset.range i, Outt (Inn^[m] x)) * Inn^[i] x

theorem psiTerm_eq_two_mul_seg (x : ℝ) (i : ℕ) : psiTerm x i = 2 * seg x i := by
  unfold psiTerm seg
  ring

theorem seg_zero (x : ℝ) : seg x 0 = x := by
  unfold seg
  simp

theorem seg_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) (i : ℕ) : 0 ≤ seg x i := by
  unfold seg
  exact mul_nonneg (prod_Outt_le hx0 hx i).1 (iterate_Inn_mem hx0 hx i).1

theorem seg_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) (i : ℕ) :
    seg x i ≤ (2 / 3 : ℝ) ^ i * (1 / 2) := by
  unfold seg
  obtain ⟨hp0, hp⟩ := prod_Outt_le hx0 hx i
  obtain ⟨hi0, hi⟩ := iterate_Inn_mem hx0 hx i
  have hpow : (0 : ℝ) ≤ (2 / 3 : ℝ) ^ i := by positivity
  nlinarith

theorem exists_seg_le {β x : ℝ} (hβ : 0 < β) (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    ∃ i, seg x i ≤ β := by
  obtain ⟨i, hi⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 2 * β by linarith)
    (show (2 / 3 : ℝ) < 1 by norm_num)
  exact ⟨i, le_of_lt (lt_of_le_of_lt (seg_le hx0 hx i) (by linarith))⟩

/-! ## The buffered cost -/

/-- The index of the first segment that fits into the buffer. -/
noncomputable def bufDepth (β x : ℝ) : ℕ := sInf {i | seg x i ≤ β}

/-- **The buffered relative cost** `ψ_β`. -/
noncomputable def psiBuf (β x : ℝ) : ℝ :=
  2 * (∑ i ∈ Finset.range (bufDepth β x), seg x i) + seg x (bufDepth β x)

/-- **`f_β(x) = μ(1,x,β)`**, the number of moves per element with a buffer of
relative size `β`. -/
noncomputable def fCostBuf (β x : ℝ) : ℝ := 1 + psiBuf β x

theorem seg_bufDepth_le {β x : ℝ} (h : ∃ i, seg x i ≤ β) : seg x (bufDepth β x) ≤ β :=
  Nat.sInf_mem h

theorem lt_seg_of_lt_bufDepth {β x : ℝ} {i : ℕ} (hi : i < bufDepth β x) : β < seg x i := by
  by_contra hc
  push_neg at hc
  exact absurd hi (not_lt.2 (Nat.sInf_le hc))

theorem bufDepth_eq_zero {β x : ℝ} (h : x ≤ β) : bufDepth β x = 0 :=
  Nat.eq_zero_of_le_zero (Nat.sInf_le (by rw [Set.mem_setOf_eq, seg_zero]; exact h))

/-- **The terminating branch.** -/
theorem psiBuf_of_le {β x : ℝ} (h : x ≤ β) : psiBuf β x = x := by
  rw [psiBuf, bufDepth_eq_zero h, seg_zero]
  simp

theorem Outt_pos {x : ℝ} (hx : 0 < x) : 0 < Outt x := by
  unfold Outt
  rw [if_neg (ne_of_gt hx)]
  have : (0 : ℝ) ≤ Int.fract (1 / x) := Int.fract_nonneg _
  positivity

/-- The shift identity for segments. -/
theorem seg_succ (x : ℝ) (i : ℕ) : seg x (i + 1) = Outt x * seg (Inn x) i := by
  unfold seg
  rw [Finset.prod_range_succ']
  have hit : ∀ m : ℕ, Inn^[m] (Inn x) = Inn^[m + 1] x := by
    intro m
    rw [← Function.iterate_succ_apply]
  have hprod : ∏ m ∈ Finset.range i, Outt (Inn^[m] (Inn x))
      = ∏ m ∈ Finset.range i, Outt (Inn^[m + 1] x) :=
    Finset.prod_congr rfl fun m _ => by rw [hit]
  rw [hprod, hit i, Function.iterate_zero_apply]
  ring

/-- **The recursion, eq. (def-mu-nu).**  Off the terminating branch the buffer
is unchanged in absolute size, hence of relative size `β/Out(x)` in the
subproblem. -/
theorem psiBuf_rec {β x : ℝ} (hβ : 0 < β) (hx : β < x) (hx2 : x ≤ 1 / 2) :
    psiBuf β x = 2 * x + Outt x * psiBuf (β / Outt x) (Inn x) := by
  have hx0 : 0 < x := lt_trans hβ hx
  have hOut : 0 < Outt x := Outt_pos hx0
  have hβ' : 0 < β / Outt x := by positivity
  have hIn0 : 0 ≤ Inn x := Inn_nonneg x
  have hIn : Inn x ≤ 1 / 2 := le_of_lt (Inn_lt_half x)
  have hex : ∃ i, seg (Inn x) i ≤ β / Outt x := exists_seg_le hβ' hIn0 hIn
  set T' := bufDepth (β / Outt x) (Inn x) with hT'
  -- the depth increases by one
  have hmem : seg x (T' + 1) ≤ β := by
    rw [seg_succ]
    have h := seg_bufDepth_le hex
    rw [← hT'] at h
    calc Outt x * seg (Inn x) T' ≤ Outt x * (β / Outt x) :=
          mul_le_mul_of_nonneg_left h (le_of_lt hOut)
      _ = β := by field_simp
  have hall : ∀ i, i < T' + 1 → β < seg x i := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · rw [seg_zero]; exact hx
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hipos.ne'
      have hj : j < T' := by omega
      have hgt : β / Outt x < seg (Inn x) j := lt_seg_of_lt_bufDepth (by rw [← hT']; exact hj)
      rw [seg_succ]
      calc β = Outt x * (β / Outt x) := by field_simp
        _ < Outt x * seg (Inn x) j := by
            exact mul_lt_mul_of_pos_left hgt hOut
  have hdepth : bufDepth β x = T' + 1 := by
    refine le_antisymm (Nat.sInf_le hmem) ?_
    by_contra hlt
    push_neg at hlt
    have h2 : seg x (bufDepth β x) ≤ β := seg_bufDepth_le ⟨T' + 1, hmem⟩
    exact absurd h2 (not_le.2 (hall _ hlt))
  rw [psiBuf, hdepth, psiBuf, ← hT', Finset.sum_range_succ', seg_zero,
    Finset.sum_congr rfl (fun i (_ : i ∈ Finset.range T') => seg_succ x i), ← Finset.mul_sum,
    seg_succ]
  ring

/-! ## Comparison with the unbuffered cost -/

theorem psiPartial_eq_two_mul (x : ℝ) (N : ℕ) :
    psiPartial N x = 2 * ∑ i ∈ Finset.range N, seg x i := by
  rw [psiPartial, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => psiTerm_eq_two_mul_seg x i

theorem psiPartial_le_psi {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) (N : ℕ) :
    psiPartial N x ≤ psi x :=
  (psi_summable hx0 hx).sum_le_tsum (Finset.range N) (fun i _ => psiTerm_nonneg hx0 hx i)

theorem psiBuf_eq_partial_add {β x : ℝ} :
    psiBuf β x = psiPartial (bufDepth β x) x + seg x (bufDepth β x) := by
  rw [psiBuf, psiPartial_eq_two_mul]

/-- **The buffer never hurts.**  `ψ_β ≤ ψ`. -/
theorem psiBuf_le_psi {β x : ℝ} (hβ : 0 < β) (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    psiBuf β x ≤ psi x := by
  have hstep : psiBuf β x ≤ psiPartial (bufDepth β x + 1) x := by
    rw [psiBuf, psiPartial_eq_two_mul, Finset.sum_range_succ]
    have := seg_nonneg hx0 hx (bufDepth β x)
    linarith
  exact le_trans hstep (psiPartial_le_psi hx0 hx _)

/-- **The buffered cost is within `3·(2/3)^T` of the unbuffered one.** -/
theorem psi_sub_psiBuf_le {β x : ℝ} (hβ : 0 < β) (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    psi x - psiBuf β x ≤ 3 * (2 / 3 : ℝ) ^ (bufDepth β x) := by
  have h1 := psi_sub_partial_le hx0 hx (bufDepth β x)
  have h2 := seg_nonneg hx0 hx (bufDepth β x)
  rw [psiBuf_eq_partial_add]
  rw [abs_le] at h1
  linarith [h1.2]

/-- **Monotone in the buffer size** (the corollary's first item). -/
theorem psiBuf_antitone {β₁ β₂ x : ℝ} (h12 : β₁ ≤ β₂) (hβ : 0 < β₁) (hx0 : 0 ≤ x)
    (hx : x ≤ 1 / 2) : psiBuf β₂ x ≤ psiBuf β₁ x := by
  have hex1 : ∃ i, seg x i ≤ β₁ := exists_seg_le hβ hx0 hx
  have hT : bufDepth β₂ x ≤ bufDepth β₁ x :=
    Nat.sInf_le (le_trans (seg_bufDepth_le hex1) h12)
  rcases eq_or_lt_of_le hT with heq | hlt
  · rw [psiBuf, psiBuf, heq]
  · rw [psiBuf, psiBuf]
    have hsplit : ∑ i ∈ Finset.range (bufDepth β₁ x), seg x i
        = (∑ i ∈ Finset.range (bufDepth β₂ x), seg x i)
          + ∑ i ∈ Finset.Ico (bufDepth β₂ x) (bufDepth β₁ x), seg x i := by
      rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
        Finset.sum_Ico_consecutive _ (Nat.zero_le _) hT]
    have hmem : bufDepth β₂ x ∈ Finset.Ico (bufDepth β₂ x) (bufDepth β₁ x) :=
      Finset.mem_Ico.2 ⟨le_refl _, hlt⟩
    have hone : seg x (bufDepth β₂ x)
        ≤ ∑ i ∈ Finset.Ico (bufDepth β₂ x) (bufDepth β₁ x), seg x i :=
      Finset.single_le_sum (fun i _ => seg_nonneg hx0 hx i) hmem
    have h1 := seg_nonneg hx0 hx (bufDepth β₁ x)
    have h2 := seg_nonneg hx0 hx (bufDepth β₂ x)
    rw [hsplit]
    linarith

/-! ## The relative cost with a buffer -/

theorem fCost_eq_of_le_half {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) : fCost x = 1 + psi x := by
  rw [fCost, min_eq_left (by linarith)]

/-- **The buffer never hurts**, for `f`. -/
theorem fCostBuf_le_fCost {β x : ℝ} (hβ : 0 < β) (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    fCostBuf β x ≤ fCost x := by
  rw [fCostBuf, fCost_eq_of_le_half hx0 hx]
  linarith [psiBuf_le_psi hβ hx0 hx]

/-! ## Two-step decay

The *one*-step ratio of segments is exactly `{1/y}` at `y = Inⁱ(x)`:
`Out(y)·In(y) = y·{1/y}`, and `{1/y}` can be arbitrarily close to `1` (take `y`
just below `1/m`).  So segments need not shrink from one step to the next.

Over *two* steps they do.  Writing `g = {1/y}`, the next ratio is `{1/In(y)}`,
and `1/In(y) = 1/g + 1`, so it is `{1/g}`.  The two-step ratio is therefore
`g·{1/g} = 1 - g⌊1/g⌋`, and with `m = ⌊1/g⌋ ≥ 1` and `g > 1/(m+1)` one has
`g·m > m/(m+1) ≥ 1/2`.  Hence `seg_{i+2} ≤ seg_i/2` — the classical fact that
Euclidean remainders halve every two steps. -/

theorem Outt_mul_Inn (y : ℝ) : Outt y * Inn y = y * Int.fract (1 / y) := by
  unfold Outt Inn
  split_ifs with h
  · rw [h]; simp
  · have hg : (0 : ℝ) ≤ Int.fract (1 / y) := Int.fract_nonneg _
    have hden : (1 : ℝ) + Int.fract (1 / y) ≠ 0 := by positivity
    field_simp

/-- The one-step ratio of segments is `{1/Inⁱ(x)}`. -/
theorem seg_succ' (x : ℝ) (i : ℕ) :
    seg x (i + 1) = seg x i * Int.fract (1 / Inn^[i] x) := by
  unfold seg
  rw [Finset.prod_range_succ, Function.iterate_succ_apply']
  have h := Outt_mul_Inn (Inn^[i] x)
  calc (∏ m ∈ Finset.range i, Outt (Inn^[m] x)) * Outt (Inn^[i] x) * Inn (Inn^[i] x)
      = (∏ m ∈ Finset.range i, Outt (Inn^[m] x)) * (Outt (Inn^[i] x) * Inn (Inn^[i] x)) := by
        ring
    _ = (∏ m ∈ Finset.range i, Outt (Inn^[m] x)) * (Inn^[i] x * Int.fract (1 / Inn^[i] x)) := by
        rw [h]
    _ = (∏ m ∈ Finset.range i, Outt (Inn^[m] x)) * Inn^[i] x * Int.fract (1 / Inn^[i] x) := by
        ring

/-- `1/In(y) = 1/{1/y} + 1`, so the fractional parts agree. -/
theorem fract_inv_Inn (y : ℝ) :
    Int.fract (1 / Inn y) = Int.fract (1 / Int.fract (1 / y)) := by
  unfold Inn
  split_ifs with h
  · rw [h]; simp
  · rcases eq_or_lt_of_le (Int.fract_nonneg (1 / y)) with hg | hg
    · rw [← hg]; simp
    · have hden : (0 : ℝ) < 1 + Int.fract (1 / y) := by linarith
      have hrw : 1 / (Int.fract (1 / y) / (1 + Int.fract (1 / y)))
          = 1 / Int.fract (1 / y) + 1 := by field_simp
      rw [hrw, Int.fract_add_one]

/-- **`g·{1/g} ≤ 1/2`** for `0 ≤ g < 1`. -/
theorem fract_mul_le_half {g : ℝ} (hg0 : 0 ≤ g) (hg1 : g < 1) :
    g * Int.fract (1 / g) ≤ 1 / 2 := by
  rcases eq_or_lt_of_le hg0 with h | hg
  · rw [← h]; simp
  · have hm : (1 : ℝ) < 1 / g := by rw [lt_div_iff₀ hg]; linarith
    have hm1 : (1 : ℝ) ≤ ((⌊1 / g⌋ : ℤ) : ℝ) := by
      have : (1 : ℤ) ≤ ⌊1 / g⌋ := Int.le_floor.2 (by exact_mod_cast le_of_lt hm)
      exact_mod_cast this
    have hlt : 1 / g < ((⌊1 / g⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
    have hub : 1 < (((⌊1 / g⌋ : ℤ) : ℝ) + 1) * g := (div_lt_iff₀ hg).1 hlt
    rw [Int.fract]
    have heq : g * (1 / g - ((⌊1 / g⌋ : ℤ) : ℝ)) = 1 - g * ((⌊1 / g⌋ : ℤ) : ℝ) := by
      field_simp
    rw [heq]
    nlinarith [hub, hm1, hg,
      mul_lt_mul_of_pos_left hub (show (0 : ℝ) < ((⌊1 / g⌋ : ℤ) : ℝ) by linarith)]

/-- **Segments halve every two steps.** -/
theorem seg_add_two_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) (i : ℕ) :
    seg x (i + 2) ≤ 1 / 2 * seg x i := by
  have h1 : seg x (i + 1) = seg x i * Int.fract (1 / Inn^[i] x) := seg_succ' x i
  have h2 : seg x (i + 2) = seg x (i + 1) * Int.fract (1 / Inn^[i + 1] x) := seg_succ' x (i + 1)
  have h3 : Inn^[i + 1] x = Inn (Inn^[i] x) := Function.iterate_succ_apply' Inn i x
  have hg0 : (0 : ℝ) ≤ Int.fract (1 / Inn^[i] x) := Int.fract_nonneg _
  have hg1 : Int.fract (1 / Inn^[i] x) < 1 := Int.fract_lt_one _
  have hhalf := fract_mul_le_half hg0 hg1
  have hsi := seg_nonneg hx0 hx i
  rw [h2, h1, h3, fract_inv_Inn]
  nlinarith

/-- The one-step ratio is at most `1`, so segments are non-increasing. -/
theorem seg_succ_le_self {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) (i : ℕ) :
    seg x (i + 1) ≤ seg x i := by
  rw [seg_succ' x i]
  have hg0 : (0 : ℝ) ≤ Int.fract (1 / Inn^[i] x) := Int.fract_nonneg _
  have hg1 : Int.fract (1 / Inn^[i] x) < 1 := Int.fract_lt_one _
  nlinarith [seg_nonneg hx0 hx i]

/-! ## The buffered cost converges to the unbuffered one

Because segments halve every two steps, the tail past the cut-off is at most
`2(seg_T + seg_{T+1}) ≤ 4β`, so `ψ - ψ_β ≤ 8β`.  This is the paper's
`μ(N,ℓ) = lim_{β→0+} μ(N,ℓ,β)`. -/

theorem seg_summable {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) : Summable (seg x) := by
  have h := (psi_summable hx0 hx).div_const 2
  refine h.congr fun i => ?_
  rw [psiTerm_eq_two_mul_seg]
  ring

theorem tsum_seg_tail_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) (T : ℕ) :
    ∑' j, seg x (T + j) ≤ 2 * (seg x T + seg x (T + 1)) := by
  have hs : Summable (fun j => seg x (T + j)) := by
    have := (seg_summable hx0 hx).comp_injective (add_right_injective T)
    exact this
  have hs2 : Summable (fun j => seg x (T + (j + 2))) := by
    have := (summable_nat_add_iff 2).2 hs
    exact this
  have hsplit := hs.sum_add_tsum_nat_add 2
  have hbound : ∑' j, seg x (T + (j + 2)) ≤ ∑' j, seg x (T + j) / 2 := by
    refine hs2.tsum_le_tsum (fun j => ?_) (hs.div_const 2)
    have := seg_add_two_le hx0 hx (T + j)
    have heq : T + (j + 2) = T + j + 2 := by omega
    rw [heq]
    linarith
  rw [tsum_div_const] at hbound
  have hfin : ∑ j ∈ Finset.range 2, seg x (T + j) = seg x T + seg x (T + 1) := by
    rw [Finset.sum_range_succ, Finset.sum_range_one, Nat.add_zero]
  rw [hfin] at hsplit
  linarith

/-- **`ψ - ψ_β ≤ 8β`.** -/
theorem psi_sub_psiBuf_le_linear {β x : ℝ} (hβ : 0 < β) (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    psi x - psiBuf β x ≤ 8 * β := by
  have hex : ∃ i, seg x i ≤ β := exists_seg_le hβ hx0 hx
  set T := bufDepth β x with hT
  have hsT : seg x T ≤ β := seg_bufDepth_le hex
  have hsT1 : seg x (T + 1) ≤ β := le_trans (seg_succ_le_self hx0 hx T) hsT
  have htail := tsum_seg_tail_le hx0 hx T
  have hs : Summable (seg x) := seg_summable hx0 hx
  have hsplit := hs.sum_add_tsum_nat_add T
  have hpsi : psi x = 2 * ∑' i, seg x i := by
    rw [psi, ← tsum_mul_left]
    exact tsum_congr fun i => psiTerm_eq_two_mul_seg x i
  have hnn := seg_nonneg hx0 hx T
  have hcomm : ∑' i : ℕ, seg x (i + T) = ∑' j : ℕ, seg x (T + j) :=
    tsum_congr fun i => by rw [Nat.add_comm]
  rw [hcomm] at hsplit
  rw [hpsi, psiBuf]
  linarith

/-- **`ψ_β → ψ` as `β → 0⁺`.** -/
theorem tendsto_psiBuf {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    Filter.Tendsto (fun β => psiBuf β x) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (psi x)) := by
  have hlow : Filter.Tendsto (fun β : ℝ => psi x - 8 * β) (nhdsWithin 0 (Set.Ioi 0))
      (𝓝 (psi x)) := by
    have h : Filter.Tendsto (fun β : ℝ => psi x - 8 * β) (𝓝 0) (𝓝 (psi x - 8 * 0)) :=
      tendsto_const_nhds.sub (tendsto_const_nhds.mul Filter.tendsto_id)
    rw [mul_zero, sub_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with β hβ
    linarith [psi_sub_psiBuf_le_linear hβ hx0 hx]
  · filter_upwards [self_mem_nhdsWithin] with β hβ
    exact psiBuf_le_psi hβ hx0 hx

/-! ## The remark

"The algorithm takes advantage of the buffer even in cases where neither the
bottom nor the top segment fits into the buffer.  The algorithm makes use of
the buffer as soon as the recursion leads to a subproblem that benefits from
the use of the buffer."

At `x = 2/5` with `β = 1/4` neither segment fits — `β < 2/5` and `β < 3/5` —
but the *second* segment does: the segments are `2/5` and `1/5`, and
`1/5 ≤ 1/4`.  So the recursion stops one step early and `f_β(2/5) = 2` instead
of `f(2/5) = 11/5`. -/

theorem fract_five_halves : Int.fract ((5 : ℝ) / 2) = 1 / 2 := by
  have hfl : ⌊(5 : ℝ) / 2⌋ = 2 := by
    rw [Int.floor_eq_iff]
    norm_num
  rw [Int.fract, hfl]
  norm_num

theorem Outt_two_fifths : Outt (2 / 5 : ℝ) = 3 / 5 := by
  rw [Outt, if_neg (by norm_num)]
  rw [show (1 : ℝ) / (2 / 5) = 5 / 2 by norm_num, fract_five_halves]
  norm_num

theorem Inn_two_fifths : Inn (2 / 5 : ℝ) = 1 / 3 := by
  rw [Inn, if_neg (by norm_num)]
  rw [show (1 : ℝ) / (2 / 5) = 5 / 2 by norm_num, fract_five_halves]
  norm_num

theorem seg_two_fifths_one : seg (2 / 5 : ℝ) 1 = 1 / 5 := by
  rw [seg_succ, seg_zero, Outt_two_fifths, Inn_two_fifths]
  norm_num

theorem bufDepth_example : bufDepth (1 / 4 : ℝ) (2 / 5 : ℝ) = 1 := by
  have hmem : seg (2 / 5 : ℝ) 1 ≤ 1 / 4 := by rw [seg_two_fifths_one]; norm_num
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra hlt
  push_neg at hlt
  have h0 : bufDepth (1 / 4 : ℝ) (2 / 5 : ℝ) = 0 := by omega
  have h1 : seg (2 / 5 : ℝ) (bufDepth (1 / 4 : ℝ) (2 / 5 : ℝ)) ≤ 1 / 4 :=
    seg_bufDepth_le ⟨1, hmem⟩
  rw [h0, seg_zero] at h1
  norm_num at h1

theorem psi_two_fifths : psi (2 / 5 : ℝ) = 6 / 5 := by
  have h := psi_rat 2 5 (by norm_num) (by norm_num)
  have hrem : remSum 5 2 = 3 := by
    rw [remSum_of_pos 5 (by norm_num), show 5 % 2 = 1 from rfl,
      remSum_of_pos 2 (by norm_num), show 2 % 1 = 0 from rfl, remSum_zero]
  rw [hrem] at h
  norm_num at h
  linarith

/-- **The remark.**  With `β = 1/4` and a rotation by `x = 2/5`, neither segment
fits into the buffer, yet the buffered cost is strictly smaller. -/
theorem buffer_helps :
    (1 / 4 : ℝ) < 2 / 5 ∧ (1 / 4 : ℝ) < 1 - 2 / 5
      ∧ fCostBuf (1 / 4 : ℝ) (2 / 5 : ℝ) = 2 ∧ fCost (2 / 5 : ℝ) = 11 / 5 := by
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  · rw [fCostBuf, psiBuf, bufDepth_example]
    rw [Finset.sum_range_one, seg_zero, seg_two_fifths_one]
    norm_num
  · rw [fCost_eq_of_le_half (by norm_num) (by norm_num), psi_two_fifths]
    norm_num

/-! ## The paper's `μ(N,ℓ,β)`

The paper works with the three-variable cost `μ(N,ℓ,β)` and reduces to the
relative function by homogeneity.  Here the reduction is the definition, and
the paper's recursion (def-mu-nu), its homogeneity, the bound `μ ≤ 3N` and the
monotonicity in `β` are recovered from it. -/

/-- **`μ(N,ℓ,β)`**, the idealised move count for rotating `N` items by `ℓ`
with a buffer of size `β`. -/
noncomputable def muCost (N l b : ℝ) : ℝ := N * (1 + psiBuf (b / N) (l / N))

/-- **Corollary, item 2: homogeneity.**  `μ(λN, λℓ, λβ) = λ·μ(N,ℓ,β)`. -/
theorem muCost_homogeneous {lam N l b : ℝ} (hlam : 0 < lam) (hN : 0 < N) :
    muCost (lam * N) (lam * l) (lam * b) = lam * muCost N l b := by
  unfold muCost
  have h1 : lam * b / (lam * N) = b / N := by
    rw [mul_div_mul_left _ _ (ne_of_gt hlam)]
  have h2 : lam * l / (lam * N) = l / N := by
    rw [mul_div_mul_left _ _ (ne_of_gt hlam)]
  rw [h1, h2]
  ring

/-- **Equation (def-mu-nu).**  `μ(N,ℓ,β) - N = ℓ` when `ℓ ≤ β`, and otherwise
`2ℓ + μ(N',ℓ',β) - N'` for the subproblem `N' = N·Out(ℓ/N)`,
`ℓ' = N'·In(ℓ/N)`. -/
theorem muCost_rec_of_le {N l b : ℝ} (hN : 0 < N) (h : l ≤ b) :
    muCost N l b - N = l := by
  unfold muCost
  rw [psiBuf_of_le (by
    rw [div_le_div_iff_of_pos_right hN]
    exact h)]
  field_simp
  ring

theorem muCost_rec_of_gt {N l b : ℝ} (hN : 0 < N) (hb : 0 < b) (h : b < l)
    (hl : 2 * l ≤ N) :
    muCost N l b - N
      = 2 * l + (muCost (N * Outt (l / N)) (N * Outt (l / N) * Inn (l / N)) b
          - N * Outt (l / N)) := by
  have hx0 : 0 < l / N := by
    have : 0 < l := lt_trans hb h
    positivity
  have hx : l / N ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hN (by norm_num)]
    linarith
  have hbx : b / N < l / N := by gcongr
  have hbN : 0 < b / N := by positivity
  have hOut : 0 < Outt (l / N) := Outt_pos hx0
  have hN' : 0 < N * Outt (l / N) := by positivity
  unfold muCost
  rw [psiBuf_rec hbN hbx hx]
  have h1 : N * Outt (l / N) * Inn (l / N) / (N * Outt (l / N)) = Inn (l / N) := by
    field_simp
  have h2 : b / (N * Outt (l / N)) = b / N / Outt (l / N) := by
    field_simp
  rw [h1, h2]
  field_simp
  ring

/-- **The Observation `μ(N,ℓ,β) ≤ 3N`.** -/
theorem muCost_le_three_mul {N l b : ℝ} (hN : 0 < N) (hb : 0 < b) (hl0 : 0 ≤ l)
    (hl : 2 * l ≤ N) : muCost N l b ≤ 3 * N := by
  have hx0 : 0 ≤ l / N := by positivity
  have hx : l / N ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hN (by norm_num)]
    linarith
  have hbN : 0 < b / N := by positivity
  have h1 : psiBuf (b / N) (l / N) ≤ psi (l / N) := psiBuf_le_psi hbN hx0 hx
  have h2 : psi (l / N) ≤ 2 := psi_le_two hx0 hx
  unfold muCost
  nlinarith

/-- **Corollary, item 1: `μ` decreases in the buffer size.** -/
theorem muCost_antitone {N l b₁ b₂ : ℝ} (hN : 0 < N) (hb : 0 < b₁) (h12 : b₁ ≤ b₂)
    (hl0 : 0 ≤ l) (hl : 2 * l ≤ N) : muCost N l b₂ ≤ muCost N l b₁ := by
  have hx0 : 0 ≤ l / N := by positivity
  have hx : l / N ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hN (by norm_num)]
    linarith
  have hbN : 0 < b₁ / N := by positivity
  have h12' : b₁ / N ≤ b₂ / N := by gcongr
  unfold muCost
  have := psiBuf_antitone h12' hbN hx0 hx
  nlinarith

/-- **Corollary, item 3, unbuffered case.**  The actual move count is at most
`μ(N,ℓ,0⁺) = N·f(ℓ/N)`; this is equation (relation). -/
theorem cost_le_muCost {n k : ℕ} (hn : 0 < n) (hk : k ≤ n) :
    ((algCost n k : ℕ) : ℝ) ≤ (n : ℝ) * fCost ((k : ℝ) / (n : ℝ)) := by
  have h := relation hn hk
  have hg : (0 : ℝ) ≤ ((Nat.gcd n k : ℕ) : ℝ) := by positivity
  linarith

/-! ## The 50% buffer

The figure's caption records that at a buffer size of `50%` the expected cost
is exactly `1.25` moves per element: the shorter segment always fits, so the
recursion stops immediately and `f_{1/2}(x) = 1 + x`. -/

theorem psiBuf_half {x : ℝ} (hx : x ≤ 1 / 2) : psiBuf (1 / 2) x = x :=
  psiBuf_of_le hx

theorem fCostBuf_half {x : ℝ} (hx : x ≤ 1 / 2) : fCostBuf (1 / 2) x = 1 + x := by
  rw [fCostBuf, psiBuf_half hx]

/-- **The figure's `1.25`.**  With a buffer of half the array, the expected cost
is `5/4` moves per element. -/
theorem expected_cost_half_buffer :
    2 * ∫ x in (0 : ℝ)..(1 / 2), fCostBuf (1 / 2) x = 5 / 4 := by
  have hcongr : ∫ x in (0 : ℝ)..(1 / 2), fCostBuf (1 / 2) x
      = ∫ x in (0 : ℝ)..(1 / 2), (1 + x) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2), Set.mem_Icc] at hx
    exact fCostBuf_half hx.2
  rw [hcongr, intervalIntegral.integral_add intervalIntegrable_const
    intervalIntegral.intervalIntegrable_id, intervalIntegral.integral_const, integral_id]
  norm_num

/-! ## The buffered algorithm, equation (integral)

Equation (integral) of the paper defines `Cost(n, k, β)`, the number of moves
the block cycle method makes when rotating an array of `n` elements by `k`
places with an auxiliary buffer of `β` elements, by the recursion

  `Cost(n,k,β) = 0`                                     if `k = 0`,
  `Cost(n,k,β) = n + k`                                  if `k ≤ β`,
  `Cost(n,k,β) = (⌊n/k⌋+1)k + Cost(n', k', β)`           otherwise,

with `k' = n - ⌊n/k⌋k = n % k` and `n' = n - (⌊n/k⌋-1)k = k + n % k`.  This is
the same recursion as the continuous `μ` of equation (continuous), except that
the discrete algorithm also stops when the remainder vanishes; that extra base
case is exactly what makes item 3 of the Corollary an inequality. -/

/-- **Equation (integral).**  The number of moves with a buffer of `b`. -/
def costB (n k b : ℕ) : ℕ :=
  if h : k = 0 then 0
  else if k ≤ b then n + k
  else (n / k + 1) * k + costB (k + n % k) (n % k) b
termination_by k
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero h)

@[simp]
theorem costB_zero (n b : ℕ) : costB n 0 b = 0 := by rw [costB]; simp

theorem costB_of_le {n k b : ℕ} (hk : k ≠ 0) (h : k ≤ b) : costB n k b = n + k := by
  rw [costB]; simp [hk, h]

theorem costB_of_gt {n k b : ℕ} (hk : k ≠ 0) (h : b < k) :
    costB n k b = (n / k + 1) * k + costB (k + n % k) (n % k) b := by
  rw [costB]; simp [hk, Nat.not_le.2 h]

/-- `N·Out(k/N)` is the next array length `n' = k + n % k`. -/
theorem mul_Outt_natCast {n k : ℕ} (hn : 0 < n) (hk : 0 < k) :
    (n : ℝ) * Outt ((k : ℝ) / (n : ℝ)) = ((k + n % k : ℕ) : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hx : ((k : ℝ) / (n : ℝ)) ≠ 0 := by positivity
  have hinv : 1 / ((k : ℝ) / (n : ℝ)) = (n : ℝ) / (k : ℝ) := one_div_div _ _
  unfold Outt
  rw [if_neg hx, hinv, Int.fract_div_natCast_eq_div_natCast_mod]
  push_cast
  field_simp

/-- `n'·In(k/N)` is the next shift `k' = n % k`. -/
theorem mul_Inn_natCast {n k : ℕ} (hn : 0 < n) (hk : 0 < k) :
    ((k + n % k : ℕ) : ℝ) * Inn ((k : ℝ) / (n : ℝ)) = ((n % k : ℕ) : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hx : ((k : ℝ) / (n : ℝ)) ≠ 0 := by positivity
  have hinv : 1 / ((k : ℝ) / (n : ℝ)) = (n : ℝ) / (k : ℝ) := one_div_div _ _
  unfold Inn
  rw [if_neg hx, hinv, Int.fract_div_natCast_eq_div_natCast_mod]
  have hden : (1 : ℝ) + ((n % k : ℕ) : ℝ) / (k : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp

/-- **Corollary, item 3.**  The buffered algorithm never uses more moves than
the continuous upper bound `μ`.  The two recursions agree step for step; the
inequality comes from the algorithm's extra base case `k = 0`. -/
theorem costB_le_muCost : ∀ k n b : ℕ, 0 < n → 0 < b → 2 * k ≤ n →
    ((costB n k b : ℕ) : ℝ) ≤ muCost (n : ℝ) (k : ℝ) (b : ℝ) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro n b hn hb hkn
    have hN : (0 : ℝ) < n := by exact_mod_cast hn
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0
      have h := muCost_rec_of_le (N := (n : ℝ)) (l := 0) (b := (b : ℝ)) hN (by positivity)
      rw [costB_zero]
      push_cast
      linarith
    rcases le_or_gt k b with hkb | hkb
    · have h := muCost_rec_of_le (N := (n : ℝ)) (l := (k : ℝ)) (b := (b : ℝ)) hN
        (by exact_mod_cast hkb)
      rw [costB_of_le hk0.ne' hkb]
      push_cast
      linarith
    · have hbR : (0 : ℝ) < b := by exact_mod_cast hb
      have hbkR : (b : ℝ) < (k : ℝ) := by exact_mod_cast hkb
      have hlR : 2 * (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
      have hrec := muCost_rec_of_gt hN hbR hbkR hlR
      rw [mul_Outt_natCast hn hk0] at hrec
      rw [mul_Inn_natCast hn hk0] at hrec
      -- the recursive call, via the induction hypothesis
      have hmod : n % k < k := Nat.mod_lt _ hk0
      have hIH := ih (n % k) hmod (k + n % k) b (by omega) hb (by omega)
      -- the discrete step `(⌊n/k⌋+1)k = n - n % k + k`
      have hdm : n / k * k + n % k = n := Nat.div_add_mod' n k
      have hstep : (((n / k + 1) * k : ℕ) : ℝ) = (n : ℝ) - ((n % k : ℕ) : ℝ) + (k : ℝ) := by
        have h1 : ((n / k * k + n % k : ℕ) : ℝ) = (n : ℝ) := by exact_mod_cast hdm
        push_cast at h1 ⊢
        linarith
      rw [costB_of_gt hk0.ne' hkb]
      push_cast
      push_cast at hstep hIH hrec
      linarith

/-- **Consistency of the two cost models.**  With no buffer, equation (integral)
computes exactly the move count `n - gcd(n,k) + 2·remSum(n,k)` of Lemma 11. -/
theorem costB_eq_moveCount : ∀ k n : ℕ, 2 * k ≤ n → costB n k 0 = moveCount n k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro n hkn
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0
      rw [costB_zero]
      unfold moveCount
      simp
    · have hmod : n % k < k := Nat.mod_lt _ hk0
      have hIH := ih (n % k) hmod (k + n % k) (by omega)
      rw [costB_of_gt hk0.ne' hk0, hIH]
      -- the gcd is unchanged along the Euclidean step
      have hg1 : Nat.gcd n k = Nat.gcd k (n % k) := by
        rw [Nat.gcd_comm n k, Nat.gcd_rec k n]
        exact Nat.gcd_comm _ _
      have hg2 : Nat.gcd (k + n % k) (n % k) = Nat.gcd k (n % k) := gcd_add_left k (n % k)
      -- the remainder sums differ by the leading term `k`
      have hr : remSum (k + n % k) (n % k) = remSum k (n % k) := by
        rcases Nat.eq_zero_or_pos (n % k) with h0 | h0
        · rw [h0, remSum_zero, remSum_zero]
        · rw [remSum_of_pos _ h0.ne', remSum_of_pos _ h0.ne', Nat.add_mod_right]
      have hrs : remSum n k = k + remSum k (n % k) := remSum_of_pos n hk0.ne'
      -- the gcds are bounded by the array lengths
      have hgle : Nat.gcd n k ≤ n := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left n k)
      have hgle' : Nat.gcd (k + n % k) (n % k) ≤ k + n % k :=
        Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left _ _)
      have hdm : n / k * k + n % k = n := Nat.div_add_mod' n k
      have hmul : (n / k + 1) * k = n / k * k + k := by ring
      unfold moveCount
      rw [hmul, hg2, hr, hrs, hg1]
      omega

/-- **Remark (buffered relative cost).**  `f_β(ℓ) = μ(1, ℓ, β)`: the per-element
cost with a buffer of relative size `β` is the continuous cost of the unit
problem. -/
theorem muCost_one (l b : ℝ) : muCost 1 l b = fCostBuf b l := by
  unfold muCost fCostBuf
  norm_num

end BlockCycleRotation
