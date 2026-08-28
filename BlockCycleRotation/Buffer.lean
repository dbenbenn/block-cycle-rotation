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

end BlockCycleRotation
