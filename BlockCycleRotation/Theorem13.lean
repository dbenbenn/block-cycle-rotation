/-
# Theorem 13

The paper's main theorem: the average cost of the block cycle scheme is

```
avgCost n = D·n + O(n^{1/2+ε}),     D = 1 + 4C ≈ 1.85.
```

`Constant.lean` proves Lemma 17 — the `G₁` main term is `C·n²·∑_{d∣n} 1/d²` up
to `O(n^{3/2+ε})` — and `TripleSum.lean` proves the error layers bounding
`G₂ + G₃`.  What is still missing, and is supplied here, is the link between
the two: the estimate at a single coprime pair, which says that the actual inner
sum over `b'` differs from the `G₁` summand by at most the `G₂ + G₃` bound.
Everything after that is aggregation.
-/

import BlockCycleRotation.Constant

namespace BlockCycleRotation

open Finset

/-! ## The estimate at a single pair

Fix `d`, `m = n/d`, and a coprime pair `a > a' ≥ 1` in the bulk, meaning
`d·a·(a+a') ≤ m`.  By `gtBound_bulk_eq` the cut-off is then `K+1` with
`K = ⌊(m-1)/(a+a')⌋`, and `K ≤ V ≤ K+1` for the paper's real cut-off
`V = m/(a+a')`.  Three proved facts combine:

* `inner_gt_estimate` — removing the congruence condition costs
  `(|A| + |B|·K)(1 + log a)`;
* `main_term_vs_sum` — replacing the discrete sum by `A·V + B·V²/2` costs
  `|A| + |B|·V`;
* `main_term_substitute` — the result is `d·m/(a+a') + m²·cTerm(a,a')`, the
  summand of `G₁`.

Since `|A| = d·a + m/a` and `|B|·V ≤ m/a`, both costs are at most
`W = d·a + 2m/a`, and the total is at most `2·W·(1 + log m)`. -/

set_option maxHeartbeats 1000000 in
-- Three separate approximations are chained here, each with its own algebraic
-- normalisation; the default budget is not enough.
/-- **The estimate at a single bulk pair.** -/
theorem bulk_pair_estimate {m d a a' : ℕ} (hm : 0 < m) (hd : 0 < d)
    (ha' : 1 ≤ a') (haa : a' < a) (hgcd : Nat.gcd a a' = 1)
    (hbulk : d * a * (a + a') ≤ m) :
    |((∑ b' ∈ (Finset.Ico 1 (gtBound m d a a')).filter (fun b' => a ∣ (m - a' * b')),
          (d * a + (m - a' * b') / a) : ℕ) : ℝ)
        - ((d : ℝ) * (m : ℝ) / ((a : ℝ) + (a' : ℝ)) + (m : ℝ) ^ 2 * cTerm (a, a'))|
      ≤ 2 * (((d * a : ℕ) : ℝ) + 2 * (m : ℝ) / (a : ℝ)) * (1 + Real.log m) := by
  have ha : 0 < a := by omega
  have hs : 0 < a + a' := by omega
  have hda2 : d * a * a < m := by nlinarith
  have haleM : a ≤ m := by
    refine le_trans ?_ hbulk
    calc a = 1 * a * 1 := by ring
      _ ≤ d * a * (a + a') := Nat.mul_le_mul (Nat.mul_le_mul hd (le_refl a)) hs
  have hsm : a + a' ≤ m := by
    refine le_trans ?_ hbulk
    calc a + a' = 1 * 1 * (a + a') := by ring
      _ ≤ d * a * (a + a') := Nat.mul_le_mul (Nat.mul_le_mul hd ha) (le_refl _)
  have haR : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have ha'R : (1 : ℝ) ≤ (a' : ℝ) := by exact_mod_cast ha'
  have hsR : (0 : ℝ) < (a : ℝ) + (a' : ℝ) := by linarith
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  -- the cut-off
  have hUeq : gtBound m d a a' = (m - 1) / (a + a') + 1 := gtBound_bulk_eq hd ha' haa hbulk
  set K := (m - 1) / (a + a') with hKdef
  set U := gtBound m d a a' with hUdef
  have hU1 : 1 ≤ U := by rw [hUeq]; exact Nat.le_add_left 1 K
  have hrange : ∀ b' ∈ Finset.Ico 1 U, a' * b' ≤ m := by
    intro b' hb'
    have := (mem_gtRange hm hs ha' hda2).1 hb'
    omega
  -- the three approximations
  obtain ⟨c, hc⟩ := inner_gt_estimate (m := m) (d := d) (a := a) (a' := a') ha hgcd U hrange
  set A : ℝ := ((d * a : ℕ) : ℝ) + (m : ℝ) / (a : ℝ) with hA
  set B : ℝ := -(a' : ℝ) / (a : ℝ) with hB
  set V : ℝ := (m : ℝ) / ((a : ℝ) + (a' : ℝ)) with hV
  have hsum : ∑ b' ∈ Finset.Ico 1 U, (A + B * (b' : ℝ))
      = A * (K : ℝ) + B * ((K : ℝ) * ((K : ℝ) + 1)) / 2 := by
    rw [sum_linear_Ico A B U hU1, hUeq]
    push_cast
    ring
  have hKV : (K : ℝ) ≤ V := by
    rw [hV, le_div_iff₀ hsR]
    have h1 : K * (a + a') ≤ m := le_trans (Nat.div_mul_le_self _ _) (by omega)
    have h2 : ((K * (a + a') : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast h1
    push_cast at h2
    linarith
  have hVK : V ≤ (K : ℝ) + 1 := by
    rw [hV, div_le_iff₀ hsR]
    have h1 : m - 1 < (K + 1) * (a + a') := by
      have hdm := Nat.div_add_mod (m - 1) (a + a')
      have hlt : (m - 1) % (a + a') < a + a' := Nat.mod_lt _ hs
      nlinarith
    have h2 : m ≤ (K + 1) * (a + a') := by omega
    have h3 : (m : ℝ) ≤ (((K + 1) * (a + a') : ℕ) : ℝ) := by exact_mod_cast h2
    push_cast at h3
    linarith
  have hV1 : 1 ≤ V := by
    rw [hV, le_div_iff₀ hsR]
    have : ((a + a' : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hsm
    push_cast at this
    linarith
  have hmts := main_term_vs_sum A B V K hKV hVK hV1
  have hsubst := main_term_substitute (m := m) (d := d) ha' haa hgcd
  -- absolute values of the coefficients
  have hAnn : (0 : ℝ) ≤ A := by rw [hA]; positivity
  have hAabs : |A| = A := abs_of_nonneg hAnn
  have hBabs : |B| = (a' : ℝ) / (a : ℝ) := by
    rw [hB, abs_div, abs_neg, abs_of_nonneg (by positivity : (0:ℝ) ≤ (a' : ℝ)),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (a : ℝ))]
  have hBV : |B| * V ≤ (m : ℝ) / (a : ℝ) := by
    rw [hBabs, hV, div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ (m : ℝ))
      (by linarith : (0:ℝ) ≤ (a : ℝ))) (by linarith : (0:ℝ) ≤ (a : ℝ))]
  set W : ℝ := ((d * a : ℕ) : ℝ) + 2 * (m : ℝ) / (a : ℝ) with hW
  have hAW : |A| + |B| * V ≤ W := by
    rw [hAabs, hA, hW]
    have : (m : ℝ) / (a : ℝ) + (m : ℝ) / (a : ℝ) = 2 * (m : ℝ) / (a : ℝ) := by ring
    linarith [hBV]
  have hAWK : |A| + |B| * ((U - 1 : ℕ) : ℝ) ≤ W := by
    have hUK : ((U - 1 : ℕ) : ℝ) = (K : ℝ) := by
      have : U - 1 = K := by omega
      rw [this]
    rw [hUK]
    have hBK : |B| * (K : ℝ) ≤ |B| * V := by
      refine mul_le_mul_of_nonneg_left hKV (abs_nonneg B)
    linarith [hAW]
  -- assemble
  have hWnn : (0 : ℝ) ≤ W := by rw [hW]; positivity
  have hloga : Real.log a ≤ Real.log m := Real.log_le_log (by linarith) (by exact_mod_cast haleM)
  have hlogm : (0 : ℝ) ≤ Real.log m := Real.log_nonneg hmR
  have hlogann : (0 : ℝ) ≤ Real.log a := Real.log_nonneg haR
  have hstep1 : |((∑ b' ∈ (Finset.Ico 1 U).filter (fun b' => a ∣ (m - a' * b')),
        (d * a + (m - a' * b') / a) : ℕ) : ℝ)
      - (1 / (a : ℝ)) * (A * (K : ℝ) + B * ((K : ℝ) * ((K : ℝ) + 1)) / 2)|
      ≤ W * (1 + Real.log a) := by
    rw [← hsum]
    refine hc.trans ?_
    exact mul_le_mul_of_nonneg_right hAWK (by linarith)
  have hstep2 : |(1 / (a : ℝ)) * (A * (K : ℝ) + B * ((K : ℝ) * ((K : ℝ) + 1)) / 2)
      - ((d : ℝ) * (m : ℝ) / ((a : ℝ) + (a' : ℝ)) + (m : ℝ) ^ 2 * cTerm (a, a'))| ≤ W := by
    rw [← hsubst, ← mul_sub, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / (a : ℝ))]
    have hinner : |(A * (K : ℝ) + B * ((K : ℝ) * ((K : ℝ) + 1)) / 2) - (A * V + B * V ^ 2 / 2)|
        ≤ W := by
      rw [abs_sub_comm]
      exact hmts.trans hAW
    have hia : 1 / (a : ℝ) ≤ 1 := by
      rw [div_le_one (by linarith)]; linarith
    calc 1 / (a : ℝ) * |(A * (K : ℝ) + B * ((K : ℝ) * ((K : ℝ) + 1)) / 2) - (A * V + B * V ^ 2 / 2)|
        ≤ 1 * W := mul_le_mul hia hinner (abs_nonneg _) (by norm_num)
      _ = W := one_mul W
  calc |((∑ b' ∈ (Finset.Ico 1 U).filter (fun b' => a ∣ (m - a' * b')),
          (d * a + (m - a' * b') / a) : ℕ) : ℝ)
        - ((d : ℝ) * (m : ℝ) / ((a : ℝ) + (a' : ℝ)) + (m : ℝ) ^ 2 * cTerm (a, a'))|
      ≤ W * (1 + Real.log a) + W := by
        have := abs_add_le
          (((∑ b' ∈ (Finset.Ico 1 U).filter (fun b' => a ∣ (m - a' * b')),
              (d * a + (m - a' * b') / a) : ℕ) : ℝ)
            - (1 / (a : ℝ)) * (A * (K : ℝ) + B * ((K : ℝ) * ((K : ℝ) + 1)) / 2))
          ((1 / (a : ℝ)) * (A * (K : ℝ) + B * ((K : ℝ) * ((K : ℝ) + 1)) / 2)
            - ((d : ℝ) * (m : ℝ) / ((a : ℝ) + (a' : ℝ)) + (m : ℝ) ^ 2 * cTerm (a, a')))
        simp only [sub_add_sub_cancel] at this
        linarith [hstep1, hstep2]
    _ ≤ 2 * W * (1 + Real.log m) := by nlinarith

/-! ## Aggregating over the pairs

The bulk part of the triple sum decomposes by pairs, and `bulk_pair_estimate`
applies to each.  The complementary part is bounded by `small_part_le`. -/

/-- **The bulk part of the triple sum, decomposed by pairs.** -/
theorem gtTriples_bulk_decompose {m d : ℕ} (hm : 0 < m) (hd : 0 < d) :
    ∑ t ∈ (gtTriples m d).filter (fun t => d * t.1 * (t.1 + t.2.1) ≤ m),
        (d * t.1 + (m - t.2.1 * t.2.2) / t.1)
      = ∑ p ∈ (coprimePairs m).filter (fun p => d * p.1 * (p.1 + p.2) ≤ m),
          ∑ b' ∈ (Finset.Ico 1 (gtBound m d p.1 p.2)).filter (fun b' => p.1 ∣ (m - p.2 * b')),
            (d * p.1 + (m - p.2 * b') / p.1) := by
  classical
  have h := gtTriples_decompose (m := m) (d := d) hm
    (fun a a' b' => if d * a * (a + a') ≤ m then d * a + (m - a' * b') / a else 0)
  calc ∑ t ∈ (gtTriples m d).filter (fun t => d * t.1 * (t.1 + t.2.1) ≤ m),
          (d * t.1 + (m - t.2.1 * t.2.2) / t.1)
      = ∑ t ∈ gtTriples m d,
          (if d * t.1 * (t.1 + t.2.1) ≤ m then d * t.1 + (m - t.2.1 * t.2.2) / t.1 else 0) :=
        Finset.sum_filter _ _
    _ = ∑ p ∈ (coprimePairs m).filter (fun p => d * p.1 * p.1 < m),
          ∑ b' ∈ (Finset.Ico 1 (gtBound m d p.1 p.2)).filter (fun b' => p.1 ∣ (m - p.2 * b')),
            (if d * p.1 * (p.1 + p.2) ≤ m then d * p.1 + (m - p.2 * b') / p.1 else 0) := h
    _ = ∑ p ∈ (coprimePairs m).filter (fun p => d * p.1 * p.1 < m),
          (if d * p.1 * (p.1 + p.2) ≤ m then
            ∑ b' ∈ (Finset.Ico 1 (gtBound m d p.1 p.2)).filter (fun b' => p.1 ∣ (m - p.2 * b')),
              (d * p.1 + (m - p.2 * b') / p.1) else 0) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        split_ifs with hb
        · rfl
        · simp
    _ = ∑ p ∈ (coprimePairs m).filter (fun p => d * p.1 * (p.1 + p.2) ≤ m),
          ∑ b' ∈ (Finset.Ico 1 (gtBound m d p.1 p.2)).filter (fun b' => p.1 ∣ (m - p.2 * b')),
            (d * p.1 + (m - p.2 * b') / p.1) := by
        rw [← Finset.sum_filter, Finset.filter_filter]
        refine Finset.sum_congr (Finset.filter_congr fun p hp => ?_) (fun _ _ => rfl)
        obtain ⟨a, a'⟩ := p
        obtain ⟨-, ha1, haa, -⟩ := mem_coprimePairs.1 hp
        have ha : 0 < a := by omega
        constructor
        · rintro ⟨-, h2⟩; exact h2
        · intro h2
          refine ⟨?_, h2⟩
          have hpos : 0 < d * a * a' := Nat.mul_pos (Nat.mul_pos hd ha) (by omega)
          have hlt : d * a * a < d * a * (a + a') := by nlinarith
          exact lt_of_lt_of_le hlt h2

/-- **The estimate at a single divisor.**

The triple sum at `d` differs from the `G₁` summand at `d` by at most twice the
middle-layer bound plus the small part. -/
theorem divisor_estimate {m d : ℕ} (hm : 0 < m) (hd : 0 < d) :
    |((∑ t ∈ gtTriples m d, (d * t.1 + (m - t.2.1 * t.2.2) / t.1) : ℕ) : ℝ)
        - ∑ p ∈ (coprimePairs m).filter (fun p => d * p.1 * (p.1 + p.2) ≤ m),
            ((d : ℝ) * (m : ℝ) / ((p.1 : ℝ) + (p.2 : ℝ)) + (m : ℝ) ^ 2 * cTerm p)|
      ≤ 2 * (((Nat.sqrt ((m - 1) / d) : ℝ) + 1) * (3 * (m : ℝ) * (1 + Real.log m)))
        + (((Nat.sqrt ((m - 1) / d) + 1) * ((2 * d + 2) * (2 * m)) : ℕ) : ℝ) := by
  classical
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hlogm : (0 : ℝ) ≤ Real.log m := Real.log_nonneg hmR
  set Sb := (coprimePairs m).filter (fun p => d * p.1 * (p.1 + p.2) ≤ m) with hSb
  -- split the triple sum
  have hsplit : (∑ t ∈ gtTriples m d, (d * t.1 + (m - t.2.1 * t.2.2) / t.1))
      = (∑ t ∈ (gtTriples m d).filter (fun t => d * t.1 * (t.1 + t.2.1) ≤ m),
          (d * t.1 + (m - t.2.1 * t.2.2) / t.1))
        + ∑ t ∈ (gtTriples m d).filter (fun t => ¬ (d * t.1 * (t.1 + t.2.1) ≤ m)),
            (d * t.1 + (m - t.2.1 * t.2.2) / t.1) :=
    gtTriples_bulk_small m d (fun a a' b' => d * a + (m - a' * b') / a)
  have hbd := gtTriples_bulk_decompose hm hd
  -- the bulk part, pair by pair
  have hpair : ∀ p ∈ Sb,
      |((∑ b' ∈ (Finset.Ico 1 (gtBound m d p.1 p.2)).filter (fun b' => p.1 ∣ (m - p.2 * b')),
            (d * p.1 + (m - p.2 * b') / p.1) : ℕ) : ℝ)
          - ((d : ℝ) * (m : ℝ) / ((p.1 : ℝ) + (p.2 : ℝ)) + (m : ℝ) ^ 2 * cTerm p)|
        ≤ 2 * (((d * p.1 : ℕ) : ℝ) + 2 * (m : ℝ) / (p.1 : ℝ)) * (1 + Real.log m) := by
    intro p hp
    obtain ⟨a, a'⟩ := p
    rw [hSb, Finset.mem_filter] at hp
    obtain ⟨hpc, hpb⟩ := hp
    obtain ⟨-, ha1, haa, hgcd⟩ := mem_coprimePairs.1 hpc
    exact bulk_pair_estimate hm hd ha1 haa hgcd hpb
  have hbulkest :
      |(∑ p ∈ Sb, ((∑ b' ∈ (Finset.Ico 1 (gtBound m d p.1 p.2)).filter
              (fun b' => p.1 ∣ (m - p.2 * b')), (d * p.1 + (m - p.2 * b') / p.1) : ℕ) : ℝ))
          - ∑ p ∈ Sb, ((d : ℝ) * (m : ℝ) / ((p.1 : ℝ) + (p.2 : ℝ)) + (m : ℝ) ^ 2 * cTerm p)|
        ≤ ∑ p ∈ Sb, 2 * (((d * p.1 : ℕ) : ℝ) + 2 * (m : ℝ) / (p.1 : ℝ)) * (1 + Real.log m) := by
    rw [← Finset.sum_sub_distrib]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hpair)
  -- the pair-error sum is at most twice the middle layer
  have hmid : ∑ p ∈ Sb, 2 * (((d * p.1 : ℕ) : ℝ) + 2 * (m : ℝ) / (p.1 : ℝ)) * (1 + Real.log m)
      ≤ 2 * (((Nat.sqrt ((m - 1) / d) : ℝ) + 1) * (3 * (m : ℝ) * (1 + Real.log m))) := by
    have hsub : Sb ⊆ (coprimePairs m).filter (fun p => d * p.1 * p.1 < m) := by
      intro p hp
      rw [hSb, Finset.mem_filter] at hp
      obtain ⟨hpc, hpb⟩ := hp
      refine Finset.mem_filter.2 ⟨hpc, ?_⟩
      obtain ⟨a, a'⟩ := p
      obtain ⟨-, ha1, haa, -⟩ := mem_coprimePairs.1 hpc
      have ha : 0 < a := by omega
      have hpos : 0 < d * a * a' := Nat.mul_pos (Nat.mul_pos hd ha) (by omega)
      have hlt : d * a * a < d * a * (a + a') := by nlinarith
      exact lt_of_lt_of_le hlt hpb
    have hstep : ∑ p ∈ Sb, 2 * (((d * p.1 : ℕ) : ℝ) + 2 * (m : ℝ) / (p.1 : ℝ))
            * (1 + Real.log m)
        ≤ ∑ p ∈ (coprimePairs m).filter (fun p => d * p.1 * p.1 < m),
            2 * (((d * p.1 : ℕ) : ℝ) + 2 * (m : ℝ) / (p.1 : ℝ)) * (1 + Real.log m) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => by positivity
    refine hstep.trans ?_
    rw [show ∑ p ∈ (coprimePairs m).filter (fun p => d * p.1 * p.1 < m),
          2 * (((d * p.1 : ℕ) : ℝ) + 2 * (m : ℝ) / (p.1 : ℝ)) * (1 + Real.log m)
        = 2 * ∑ p ∈ (coprimePairs m).filter (fun p => d * p.1 * p.1 < m),
            ((((d * p.1 : ℕ) : ℝ) + 2 * (m : ℝ) / (p.1 : ℝ)) * (1 + Real.log m)) from by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun p _ => by ring]
    exact mul_le_mul_of_nonneg_left (middle_layer (m := m) (d := d) hm hd) (by norm_num)
  -- the small part
  have hsmall := small_part_le hm hd
  have hsmallR : ((∑ t ∈ (gtTriples m d).filter (fun t => ¬ (d * t.1 * (t.1 + t.2.1) ≤ m)),
        (d * t.1 + (m - t.2.1 * t.2.2) / t.1) : ℕ) : ℝ)
      ≤ (((Nat.sqrt ((m - 1) / d) + 1) * ((2 * d + 2) * (2 * m)) : ℕ) : ℝ) := by
    exact_mod_cast hsmall
  have hsmallnn : (0 : ℝ) ≤ ((∑ t ∈ (gtTriples m d).filter
      (fun t => ¬ (d * t.1 * (t.1 + t.2.1) ≤ m)), (d * t.1 + (m - t.2.1 * t.2.2) / t.1) : ℕ) : ℝ) :=
    by positivity
  -- assemble
  have key : ∀ X Y M b1 b2 : ℝ, |X - M| ≤ b1 → 0 ≤ Y → Y ≤ b2 → |X + Y - M| ≤ b1 + b2 := by
    intro X Y M b1 b2 h1 h2 h3
    have htri := abs_add_le (X - M) Y
    rw [abs_of_nonneg h2] at htri
    have heq : X + Y - M = (X - M) + Y := by ring
    rw [heq]
    linarith
  rw [hsplit, hbd, Nat.cast_add, Nat.cast_sum]
  exact key _ _ _ _ _ (hbulkest.trans hmid) hsmallnn hsmallR

/-! ## Summing over the divisors

Both per-divisor errors are dominated by the quantity `outer_layer` and
`error_isBigO` handle, namely `d(n)·(√n+1)·3n(1+log n)`: the middle layer
directly, and the small part because `(2d+2)(2m) = 4dm + 4m ≤ 8n`. -/

/-- The aggregate error bound of `outer_layer`. -/
noncomputable def Err (n : ℕ) : ℝ :=
  (n.divisors.card : ℝ) * (((Nat.sqrt n : ℝ) + 1) * (3 * (n : ℝ) * (1 + Real.log n)))

/-- **The restricted quadruple sum is `G₁` up to `O(n^{3/2+ε})`.** -/
theorem Qgt_sub_G1_le {n : ℕ} (hn : 0 < n) :
    |((∑ q ∈ (quadruplesQ n).filter (fun q => q.1 < q.2.1), (q.1 + q.2.1) : ℕ) : ℝ) - G1 n|
      ≤ 5 * Err n := by
  classical
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlogn : (0 : ℝ) ≤ Real.log n := Real.log_nonneg hnR
  set Big : ℝ := ((Nat.sqrt n : ℝ) + 1) * (3 * (n : ℝ) * (1 + Real.log n)) with hBig
  have hper : ∀ d ∈ n.divisors,
      |((∑ t ∈ gtTriples (n / d) d, (d * t.1 + (n / d - t.2.1 * t.2.2) / t.1) : ℕ) : ℝ)
        - ∑ p ∈ (coprimePairs (n / d)).filter (fun p => d * p.1 * (p.1 + p.2) ≤ n / d),
            ((d : ℝ) * ((n / d : ℕ) : ℝ) / ((p.1 : ℝ) + (p.2 : ℝ))
              + ((n / d : ℕ) : ℝ) ^ 2 * cTerm p)|
        ≤ 2 * (((Nat.sqrt ((n / d - 1) / d) : ℝ) + 1)
            * (3 * ((n / d : ℕ) : ℝ) * (1 + Real.log ((n / d : ℕ) : ℝ)))) + 3 * Big := by
    intro d hd
    obtain ⟨hdn, -⟩ := Nat.mem_divisors.1 hd
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
    have hm0 : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hn hdn) hd0
    refine (divisor_estimate hm0 hd0).trans ?_
    -- the small part is at most `3·Big`
    have hmn : n / d ≤ n := Nat.div_le_self _ _
    have hdm : d * (n / d) = n := Nat.mul_div_cancel' hdn
    have hsq : Nat.sqrt ((n / d - 1) / d) ≤ Nat.sqrt n := by
      refine Nat.sqrt_le_sqrt ?_
      calc (n / d - 1) / d ≤ n / d - 1 := Nat.div_le_self _ _
        _ ≤ n := by omega
    have hsqR : ((Nat.sqrt ((n / d - 1) / d) : ℕ) : ℝ) ≤ ((Nat.sqrt n : ℕ) : ℝ) := by
      exact_mod_cast hsq
    have hbnd : ((2 * d + 2) * (2 * (n / d)) : ℕ) ≤ 8 * n := by
      have h1 : d * (n / d) ≤ n := by omega
      nlinarith
    have hbndR : (((2 * d + 2) * (2 * (n / d)) : ℕ) : ℝ) ≤ 8 * (n : ℝ) := by
      exact_mod_cast hbnd
    have hs1 : (0 : ℝ) ≤ ((Nat.sqrt ((n / d - 1) / d) : ℕ) : ℝ) := by positivity
    have hsmallbnd : (((Nat.sqrt ((n / d - 1) / d) + 1) * ((2 * d + 2) * (2 * (n / d))) : ℕ) : ℝ)
        ≤ 3 * Big := by
      calc (((Nat.sqrt ((n / d - 1) / d) + 1) * ((2 * d + 2) * (2 * (n / d))) : ℕ) : ℝ)
        = (((Nat.sqrt ((n / d - 1) / d) : ℕ) : ℝ) + 1)
            * (((2 * d + 2) * (2 * (n / d)) : ℕ) : ℝ) := by push_cast; ring
        _ ≤ (((Nat.sqrt n : ℕ) : ℝ) + 1) * (8 * (n : ℝ)) := by
            refine mul_le_mul (by linarith) hbndR (by positivity) (by positivity)
        _ ≤ 3 * Big := by
            rw [hBig]
            have h9 : (8 : ℝ) * (n : ℝ) ≤ 3 * (3 * (n : ℝ) * (1 + Real.log n)) := by nlinarith
            have hnn : (0 : ℝ) ≤ ((Nat.sqrt n : ℕ) : ℝ) + 1 := by positivity
            nlinarith
    linarith
  rw [Q_gt_tripleSum hn, G1, Nat.cast_sum, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum hper).trans ?_
  rw [Finset.sum_add_distrib]
  have h1 : ∑ d ∈ n.divisors, 2 * (((Nat.sqrt ((n / d - 1) / d) : ℝ) + 1)
        * (3 * ((n / d : ℕ) : ℝ) * (1 + Real.log ((n / d : ℕ) : ℝ))))
      ≤ 2 * Err n := by
    rw [← Finset.mul_sum, Err]
    exact mul_le_mul_of_nonneg_left (outer_layer hn) (by norm_num)
  have h2 : ∑ _d ∈ n.divisors, 3 * Big = 3 * Err n := by
    rw [Finset.sum_const, nsmul_eq_mul, Err, hBig]
    ring
  rw [h2]
  linarith

/-! ## `Q(n)` in closed form

Adding the diagonal (bounded by `sum_diag_isBigO`) and Lemma 17. -/

/-- **`Q(n) = C·n²·∑_{d∣n} 1/d² + O(n^{3/2+ε})`.** -/
theorem Q_isBigO {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 0 < n →
      |((Qquad n : ℤ) : ℝ) - cConst * (n : ℝ) ^ 2 * ∑ d ∈ n.divisors, 1 / (d : ℝ) ^ 2|
        ≤ K * (n : ℝ) ^ (3 / 2 + ε) := by
  classical
  obtain ⟨C1, hC1, hErr⟩ := error_isBigO hε
  obtain ⟨C2, hC2, hDiag⟩ := sum_diag_isBigO hε
  obtain ⟨C3, hC3, hG1⟩ := lemma17_isBigO hε
  refine ⟨5 * C1 + C2 + C3, by positivity, fun n hn => ?_⟩
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hsym : ((Qquad n : ℤ) : ℝ)
      = ((∑ q ∈ (quadruplesQ n).filter (fun q => q.1 < q.2.1), (q.1 + q.2.1) : ℕ) : ℝ)
        + ((∑ q ∈ (quadruplesQ n).filter (fun q => q.1 = q.2.1), q.1 : ℕ) : ℝ) := by
    have h1 : (Qquad n : ℤ) = ((∑ q ∈ quadruplesQ n, q.2.1 : ℕ) : ℤ) := by
      unfold Qquad; push_cast; rfl
    rw [h1, Q_symmetrise n]
    push_cast
    ring
  have hdiagnn : (0 : ℝ)
      ≤ ((∑ q ∈ (quadruplesQ n).filter (fun q => q.1 = q.2.1), q.1 : ℕ) : ℝ) := by positivity
  have hexp : (n : ℝ) ^ (1 + ε) ≤ (n : ℝ) ^ (3 / 2 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hnR (by linarith)
  have h1 := Qgt_sub_G1_le hn
  have h2 := hErr n hn
  have h3 := hDiag n hn
  have h4 := hG1 n hn
  have hsplit : ((Qquad n : ℤ) : ℝ) - cConst * (n : ℝ) ^ 2 * ∑ d ∈ n.divisors, 1 / (d : ℝ) ^ 2
      = (((∑ q ∈ (quadruplesQ n).filter (fun q => q.1 < q.2.1), (q.1 + q.2.1) : ℕ) : ℝ) - G1 n)
        + ((∑ q ∈ (quadruplesQ n).filter (fun q => q.1 = q.2.1), q.1 : ℕ) : ℝ)
        + (G1 n - cConst * (n : ℝ) ^ 2 * ∑ d ∈ n.divisors, 1 / (d : ℝ) ^ 2) := by
    rw [hsym]; ring
  rw [hsplit]
  have hA := abs_add_le
    ((((∑ q ∈ (quadruplesQ n).filter (fun q => q.1 < q.2.1), (q.1 + q.2.1) : ℕ) : ℝ) - G1 n)
      + ((∑ q ∈ (quadruplesQ n).filter (fun q => q.1 = q.2.1), q.1 : ℕ) : ℝ))
    (G1 n - cConst * (n : ℝ) ^ 2 * ∑ d ∈ n.divisors, 1 / (d : ℝ) ^ 2)
  have hB := abs_add_le
    ((((∑ q ∈ (quadruplesQ n).filter (fun q => q.1 < q.2.1), (q.1 + q.2.1) : ℕ) : ℝ) - G1 n))
    (((∑ q ∈ (quadruplesQ n).filter (fun q => q.1 = q.2.1), q.1 : ℕ) : ℝ))
  rw [abs_of_nonneg hdiagnn] at hB
  have hErrle : 5 * Err n ≤ 5 * (C1 * (n : ℝ) ^ (3 / 2 + ε)) := by
    have : Err n ≤ C1 * (n : ℝ) ^ (3 / 2 + ε) := h2
    linarith
  nlinarith [hA, hB, h1, h3, h4, hErrle, hexp, hC2]

/-! ## Möbius inversion

`∑_{d ∣ n} d² = n²·∑_{e ∣ n} 1/e²`, so Möbius inversion turns the main term of
`Q` into `C·n²` when it is summed against `μ`. -/

/-- **The main term after Möbius inversion.** -/
theorem moebius_main {n : ℕ} (hn : 0 < n) :
    ∑ d ∈ n.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℝ)
        * (cConst * ((n / d : ℕ) : ℝ) ^ 2 * ∑ e ∈ (n / d).divisors, 1 / (e : ℝ) ^ 2)
      = cConst * (n : ℝ) ^ 2 := by
  have hbase : ∑ x ∈ n.divisorsAntidiagonal,
      (ArithmeticFunction.moebius x.1) • (∑ d ∈ (x.2).divisors, (d : ℝ) ^ 2) = (n : ℝ) ^ 2 :=
    ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq.1 (fun _ _ => rfl) n hn
  rw [Nat.sum_divisorsAntidiagonal
    (fun x y => (ArithmeticFunction.moebius x) • (∑ e ∈ (y : ℕ).divisors, (e : ℝ) ^ 2))] at hbase
  have hstep : ∀ d ∈ n.divisors,
      ((ArithmeticFunction.moebius d : ℤ) : ℝ)
          * (cConst * ((n / d : ℕ) : ℝ) ^ 2 * ∑ e ∈ (n / d).divisors, 1 / (e : ℝ) ^ 2)
        = cConst * ((ArithmeticFunction.moebius d) • (∑ e ∈ (n / d).divisors, (e : ℝ) ^ 2)) := by
    intro d hd
    obtain ⟨hdn, -⟩ := Nat.mem_divisors.1 hd
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
    have hk : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hn hdn) hd0
    have hg : ∑ e ∈ (n / d).divisors, (e : ℝ) ^ 2
        = ((n / d : ℕ) : ℝ) ^ 2 * ∑ e ∈ (n / d).divisors, 1 / (e : ℝ) ^ 2 := by
      have h := sum_div_sq_eq hk (1 : ℝ)
      simp only [one_mul] at h
      rw [← h]
      exact (Nat.sum_div_divisors (n / d) (fun y => (y : ℝ) ^ 2)).symm
    rw [hg, zsmul_eq_mul]
    ring
  rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum, hbase]

/-- **`R(n) = C·n² + O(n^{3/2+ε})`.** -/
theorem R_isBigO {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 0 < n →
      |((Rquad n : ℤ) : ℝ) - cConst * (n : ℝ) ^ 2| ≤ K * (n : ℝ) ^ (3 / 2 + ε) := by
  classical
  obtain ⟨K1, hK1, hQ⟩ := Q_isBigO (half_pos hε)
  obtain ⟨C0, hC0, hCd⟩ := exists_card_divisors_le (half_pos hε)
  refine ⟨K1 * C0, by positivity, fun n hn => ?_⟩
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hR : ((Rquad n : ℤ) : ℝ)
      = ∑ d ∈ n.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℝ)
          * ((Qquad (n / d) : ℤ) : ℝ) := by
    have h := moebius_Rquad hn
    rw [Nat.sum_divisorsAntidiagonal
      (fun x y => (ArithmeticFunction.moebius x) • Qquad y)] at h
    rw [← h]
    push_cast [zsmul_eq_mul]
    ring
  have hterm : ∀ d ∈ n.divisors,
      |((ArithmeticFunction.moebius d : ℤ) : ℝ) * ((Qquad (n / d) : ℤ) : ℝ)
        - ((ArithmeticFunction.moebius d : ℤ) : ℝ)
            * (cConst * ((n / d : ℕ) : ℝ) ^ 2 * ∑ e ∈ (n / d).divisors, 1 / (e : ℝ) ^ 2)|
      ≤ K1 * (n : ℝ) ^ (3 / 2 + ε / 2) := by
    intro d hd
    obtain ⟨hdn, -⟩ := Nat.mem_divisors.1 hd
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
    have hk : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hn hdn) hd0
    have hkn : ((n / d : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.div_le_self n d
    rw [← mul_sub, abs_mul]
    have hmu : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1 := by
      rw [← Int.cast_abs]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have hq := hQ (n / d) hk
    have hmono : ((n / d : ℕ) : ℝ) ^ (3 / 2 + ε / 2) ≤ (n : ℝ) ^ (3 / 2 + ε / 2) :=
      Real.rpow_le_rpow (by positivity) hkn (by linarith)
    have habs : (0 : ℝ) ≤ |((Qquad (n / d) : ℤ) : ℝ)
        - cConst * ((n / d : ℕ) : ℝ) ^ 2 * ∑ e ∈ (n / d).divisors, 1 / (e : ℝ) ^ 2| :=
      abs_nonneg _
    nlinarith [hmu, hq, hmono, habs, hK1, abs_nonneg ((ArithmeticFunction.moebius d : ℤ) : ℝ)]
  rw [hR, ← moebius_main hn, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (sum_divisors_le _ _ hterm).trans ?_
  have hd := hCd n hn.ne'
  have hstep : (n.divisors.card : ℝ) * (K1 * (n : ℝ) ^ (3 / 2 + ε / 2))
      ≤ (C0 * (n : ℝ) ^ (ε / 2)) * (K1 * (n : ℝ) ^ (3 / 2 + ε / 2)) := by
    refine mul_le_mul_of_nonneg_right hd ?_
    positivity
  refine hstep.trans (le_of_eq ?_)
  have hpow : (n : ℝ) ^ (ε / 2) * (n : ℝ) ^ (3 / 2 + ε / 2) = (n : ℝ) ^ (3 / 2 + ε) := by
    rw [← Real.rpow_add hnpos]
    congr 1
    ring
  calc (C0 * (n : ℝ) ^ (ε / 2)) * (K1 * (n : ℝ) ^ (3 / 2 + ε / 2))
      = K1 * C0 * ((n : ℝ) ^ (ε / 2) * (n : ℝ) ^ (3 / 2 + ε / 2)) := by ring
    _ = K1 * C0 * (n : ℝ) ^ (3 / 2 + ε) := by rw [hpow]

end BlockCycleRotation
