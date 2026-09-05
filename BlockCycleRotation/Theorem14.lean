/-
# Theorem 14

The paper's main theorem: the average cost of the block cycle scheme is

```
avgCost n = D·n + O(n^{1/2+ε}),     D = 1 + 4C ≈ 1.85.
```

`Constant.lean` proves Lemma 19 — the `G₁` main term is `C·n²·∑_{d∣n} 1/d²` up
to `O(n^{3/2+ε})` — and `TripleSum.lean` proves the error layers bounding
`G₂ + G₃`.  What is still missing, and is supplied here, is the link between
the two: the estimate at a single coprime pair, which says that the actual inner
sum over `y'` differs from the `G₁` summand by at most the `G₂ + G₃` bound.
Everything after that is aggregation.
-/

import BlockCycleRotation.Constant
import BlockCycleRotation.Average

namespace BlockCycleRotation

open Finset

/-! ## The estimate at a single pair

Fix `d`, `m = n/d`, and a coprime pair `x > y ≥ 1` in the bulk, meaning
`d·x·(x+y) ≤ m`.  By `yBound_bulk_eq` the cut-off is then `K+1` with
`K = ⌊(m-1)/(x+y)⌋`, and `K ≤ V ≤ K+1` for the paper's real cut-off
`V = m/(x+y)`.  Three proved facts combine:

* `inner_gt_estimate` — removing the congruence condition costs
  `(|A| + |B|·K)(1 + log x)`;
* `main_term_vs_sum` — replacing the discrete sum by `A·V + B·V²/2` costs
  `|A| + |B|·V`;
* `main_term_substitute` — the result is `d·m/(x+y) + m²·cTerm(x,y)`, the
  summand of `G₁`.

Since `|A| = d·x + m/x` and `|B|·V ≤ m/x`, both costs are at most
`W = d·x + 2m/x`, and the total is at most `2·W·(1 + log m)`. -/

set_option maxHeartbeats 1000000 in
-- Three separate approximations are chained here, each with its own algebraic
-- normalisation; the default budget is not enough.
/-- **The estimate at a single bulk pair.** -/
theorem bulk_pair_estimate {m d x y : ℕ} (hm : 0 < m) (hd : 0 < d)
    (hy : 1 ≤ y) (haa : y < x) (hgcd : Nat.gcd x y = 1)
    (hbulk : d * x * (x + y) ≤ m) :
    |((∑ y' ∈ (Finset.Ico 1 (yBound m d x y)).filter (fun y' => x ∣ (m - y * y')),
          (d * x + (m - y * y') / x) : ℕ) : ℝ)
        - ((d : ℝ) * (m : ℝ) / ((x : ℝ) + (y : ℝ)) + (m : ℝ) ^ 2 * cTerm (x, y))|
      ≤ 2 * (((d * x : ℕ) : ℝ) + 2 * (m : ℝ) / (x : ℝ)) * (1 + Real.log m) := by
  have hx : 0 < x := by omega
  have hs : 0 < x + y := by omega
  have hda2 : d * x * x < m := by nlinarith
  have haleM : x ≤ m := by
    refine le_trans ?_ hbulk
    calc x = 1 * x * 1 := by ring
      _ ≤ d * x * (x + y) := Nat.mul_le_mul (Nat.mul_le_mul hd (le_refl x)) hs
  have hsm : x + y ≤ m := by
    refine le_trans ?_ hbulk
    calc x + y = 1 * 1 * (x + y) := by ring
      _ ≤ d * x * (x + y) := Nat.mul_le_mul (Nat.mul_le_mul hd hx) (le_refl _)
  have haR : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hyR : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hsR : (0 : ℝ) < (x : ℝ) + (y : ℝ) := by linarith
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  -- the cut-off
  have hUeq : yBound m d x y = (m - 1) / (x + y) + 1 := yBound_bulk_eq hd hy haa hbulk
  set K := (m - 1) / (x + y) with hKdef
  set U := yBound m d x y with hUdef
  have hU1 : 1 ≤ U := by rw [hUeq]; exact Nat.le_add_left 1 K
  have hrange : ∀ y' ∈ Finset.Ico 1 U, y * y' ≤ m := by
    intro y' hy'
    have := (mem_gtRange hm hs hy hda2).1 hy'
    omega
  -- the three approximations
  obtain ⟨c, hc⟩ := inner_gt_estimate (m := m) (d := d) (x := x) (y := y) hx hgcd U hrange
  set A : ℝ := ((d * x : ℕ) : ℝ) + (m : ℝ) / (x : ℝ) with hA
  set B : ℝ := -(y : ℝ) / (x : ℝ) with hB
  set V : ℝ := (m : ℝ) / ((x : ℝ) + (y : ℝ)) with hV
  have hsum : ∑ y' ∈ Finset.Ico 1 U, (A + B * (y' : ℝ))
      = A * (K : ℝ) + B * ((K : ℝ) * ((K : ℝ) + 1)) / 2 := by
    rw [sum_linear_Ico A B U hU1, hUeq]
    push_cast
    ring
  have hKV : (K : ℝ) ≤ V := by
    rw [hV, le_div_iff₀ hsR]
    have h1 : K * (x + y) ≤ m := le_trans (Nat.div_mul_le_self _ _) (by omega)
    have h2 : ((K * (x + y) : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast h1
    push_cast at h2
    linarith
  have hVK : V ≤ (K : ℝ) + 1 := by
    rw [hV, div_le_iff₀ hsR]
    have h1 : m - 1 < (K + 1) * (x + y) := by
      have hdm := Nat.div_add_mod (m - 1) (x + y)
      have hlt : (m - 1) % (x + y) < x + y := Nat.mod_lt _ hs
      nlinarith
    have h2 : m ≤ (K + 1) * (x + y) := by omega
    have h3 : (m : ℝ) ≤ (((K + 1) * (x + y) : ℕ) : ℝ) := by exact_mod_cast h2
    push_cast at h3
    linarith
  have hV1 : 1 ≤ V := by
    rw [hV, le_div_iff₀ hsR]
    have : ((x + y : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hsm
    push_cast at this
    linarith
  have hmts := main_term_vs_sum A B V K hKV hVK hV1
  have hsubst := main_term_substitute (m := m) (d := d) hy haa hgcd
  -- absolute values of the coefficients
  have hAnn : (0 : ℝ) ≤ A := by rw [hA]; positivity
  have hAabs : |A| = A := abs_of_nonneg hAnn
  have hBabs : |B| = (y : ℝ) / (x : ℝ) := by
    rw [hB, abs_div, abs_neg, abs_of_nonneg (by positivity : (0:ℝ) ≤ (y : ℝ)),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (x : ℝ))]
  have hBV : |B| * V ≤ (m : ℝ) / (x : ℝ) := by
    rw [hBabs, hV, div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ (m : ℝ))
      (by linarith : (0:ℝ) ≤ (x : ℝ))) (by linarith : (0:ℝ) ≤ (x : ℝ))]
  set W : ℝ := ((d * x : ℕ) : ℝ) + 2 * (m : ℝ) / (x : ℝ) with hW
  have hAW : |A| + |B| * V ≤ W := by
    rw [hAabs, hA, hW]
    have : (m : ℝ) / (x : ℝ) + (m : ℝ) / (x : ℝ) = 2 * (m : ℝ) / (x : ℝ) := by ring
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
  have hloga : Real.log x ≤ Real.log m := Real.log_le_log (by linarith) (by exact_mod_cast haleM)
  have hlogm : (0 : ℝ) ≤ Real.log m := Real.log_nonneg hmR
  have hlogann : (0 : ℝ) ≤ Real.log x := Real.log_nonneg haR
  have hstep1 : |((∑ y' ∈ (Finset.Ico 1 U).filter (fun y' => x ∣ (m - y * y')),
        (d * x + (m - y * y') / x) : ℕ) : ℝ)
      - (1 / (x : ℝ)) * (A * (K : ℝ) + B * ((K : ℝ) * ((K : ℝ) + 1)) / 2)|
      ≤ W * (1 + Real.log x) := by
    rw [← hsum]
    refine hc.trans ?_
    exact mul_le_mul_of_nonneg_right hAWK (by linarith)
  have hstep2 : |(1 / (x : ℝ)) * (A * (K : ℝ) + B * ((K : ℝ) * ((K : ℝ) + 1)) / 2)
      - ((d : ℝ) * (m : ℝ) / ((x : ℝ) + (y : ℝ)) + (m : ℝ) ^ 2 * cTerm (x, y))| ≤ W := by
    rw [← hsubst, ← mul_sub, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / (x : ℝ))]
    have hinner : |(A * (K : ℝ) + B * ((K : ℝ) * ((K : ℝ) + 1)) / 2) - (A * V + B * V ^ 2 / 2)|
        ≤ W := by
      rw [abs_sub_comm]
      exact hmts.trans hAW
    have hia : 1 / (x : ℝ) ≤ 1 := by
      rw [div_le_one (by linarith)]; linarith
    calc 1 / (x : ℝ) * |(A * (K : ℝ) + B * ((K : ℝ) * ((K : ℝ) + 1)) / 2) - (A * V + B * V ^ 2 / 2)|
        ≤ 1 * W := mul_le_mul hia hinner (abs_nonneg _) (by norm_num)
      _ = W := one_mul W
  calc |((∑ y' ∈ (Finset.Ico 1 U).filter (fun y' => x ∣ (m - y * y')),
          (d * x + (m - y * y') / x) : ℕ) : ℝ)
        - ((d : ℝ) * (m : ℝ) / ((x : ℝ) + (y : ℝ)) + (m : ℝ) ^ 2 * cTerm (x, y))|
      ≤ W * (1 + Real.log x) + W := by
        have := abs_add_le
          (((∑ y' ∈ (Finset.Ico 1 U).filter (fun y' => x ∣ (m - y * y')),
              (d * x + (m - y * y') / x) : ℕ) : ℝ)
            - (1 / (x : ℝ)) * (A * (K : ℝ) + B * ((K : ℝ) * ((K : ℝ) + 1)) / 2))
          ((1 / (x : ℝ)) * (A * (K : ℝ) + B * ((K : ℝ) * ((K : ℝ) + 1)) / 2)
            - ((d : ℝ) * (m : ℝ) / ((x : ℝ) + (y : ℝ)) + (m : ℝ) ^ 2 * cTerm (x, y)))
        simp only [sub_add_sub_cancel] at this
        linarith [hstep1, hstep2]
    _ ≤ 2 * W * (1 + Real.log m) := by nlinarith

/-! ## The paper's `G₁ + G₂ + G₃`

The paper splits the inner sum at a coprime pair into three named pieces:
`G₁` is the closed form `(1/x)(A·Y + B·Y²/2)` at the *real* cut-off `Y`, `G₂`
is the rounding error against the discrete sum, and `G₃` is what the
non-trivial characters contribute.  `bulk_pair_estimate` bounds `G₂ + G₃`
together; the three are named here so that Lemmas 18 and 19 can be stated
individually. -/

/-- The paper's `A = d·x + m/x`. -/
noncomputable def aCoeff (m d x : ℕ) : ℝ := ((d * x : ℕ) : ℝ) + (m : ℝ) / (x : ℝ)

/-- The paper's `B = -y/x`. -/
noncomputable def bCoeff (x y : ℕ) : ℝ := -(y : ℝ) / (x : ℝ)

/-- The paper's cut-off `Y = m/(x+y)`, which on the bulk branch is the active
one of the two. -/
noncomputable def yCut (m x y : ℕ) : ℝ := (m : ℝ) / ((x : ℝ) + (y : ℝ))

/-- The discrete sum `∑_{1 ≤ y' < Y} (A + B·y')`. -/
noncomputable def innerLinear (m d x y : ℕ) : ℝ :=
  ∑ y' ∈ Finset.Ico 1 (yBound m d x y), (aCoeff m d x + bCoeff x y * (y' : ℝ))

/-- The actual inner sum over the arithmetic progression. -/
noncomputable def innerActual (m d x y : ℕ) : ℝ :=
  ((∑ y' ∈ (Finset.Ico 1 (yBound m d x y)).filter (fun y' => x ∣ (m - y * y')),
      (d * x + (m - y * y') / x) : ℕ) : ℝ)

/-- **`G₁`**, the main term at the real cut-off. -/
noncomputable def G1term (m d x y : ℕ) : ℝ :=
  (1 / (x : ℝ)) * (aCoeff m d x * yCut m x y + bCoeff x y * yCut m x y ^ 2 / 2)

/-- **`G₂`**, the rounding error. -/
noncomputable def G2term (m d x y : ℕ) : ℝ :=
  (1 / (x : ℝ)) * innerLinear m d x y - G1term m d x y

/-- **`G₃`**, the contribution of the non-trivial characters. -/
noncomputable def G3term (m d x y : ℕ) : ℝ :=
  innerActual m d x y - (1 / (x : ℝ)) * innerLinear m d x y

/-- **The paper's decomposition** `Q(n,d,x,y) = G₁ + G₂ + G₃`. -/
theorem innerActual_decompose (m d x y : ℕ) :
    innerActual m d x y = G1term m d x y + G2term m d x y + G3term m d x y := by
  unfold G2term G3term
  ring

/-- `G₁` is the summand of `G₁(n)`, by `main_term_substitute`. -/
theorem G1term_eq {m d x y : ℕ} (h1 : 1 ≤ y) (h2 : y < x) (h3 : Nat.gcd x y = 1) :
    G1term m d x y
      = (d : ℝ) * (m : ℝ) / ((x : ℝ) + (y : ℝ)) + (m : ℝ) ^ 2 * cTerm (x, y) := by
  unfold G1term aCoeff bCoeff yCut
  exact main_term_substitute h1 h2 h3

/-- **The bound of Lemma 16 at one pair:** `|G₂| ≤ |A| + |B·Y|`. -/
theorem abs_G2term_le {m d x y : ℕ} (hm : 0 < m) (hd : 0 < d)
    (hy : 1 ≤ y) (haa : y < x) (hbulk : d * x * (x + y) ≤ m) :
    |G2term m d x y| ≤ |aCoeff m d x| + |bCoeff x y| * yCut m x y := by
  have hx : 0 < x := by omega
  have haR : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hs : x + y ≤ m := by
    refine le_trans ?_ hbulk
    calc x + y = 1 * 1 * (x + y) := by ring
      _ ≤ d * x * (x + y) := Nat.mul_le_mul (Nat.mul_le_mul hd hx) (le_refl _)
  have hsR : (0 : ℝ) < (x : ℝ) + (y : ℝ) := by
    have : (0 : ℝ) < (x : ℝ) := by linarith
    have : (0 : ℝ) ≤ (y : ℝ) := by positivity
    linarith
  have hUeq : yBound m d x y = (m - 1) / (x + y) + 1 := yBound_bulk_eq hd hy haa hbulk
  set K := (m - 1) / (x + y) with hKdef
  have hU1 : 1 ≤ yBound m d x y := by rw [hUeq]; exact Nat.le_add_left 1 K
  have hsum : innerLinear m d x y
      = aCoeff m d x * (K : ℝ) + bCoeff x y * ((K : ℝ) * ((K : ℝ) + 1)) / 2 := by
    rw [innerLinear, sum_linear_Ico _ _ _ hU1, hUeq]
    push_cast
    ring
  have hKV : (K : ℝ) ≤ yCut m x y := by
    rw [yCut, le_div_iff₀ hsR]
    have h1 : K * (x + y) ≤ m := le_trans (Nat.div_mul_le_self _ _) (by omega)
    have h2 : ((K * (x + y) : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast h1
    push_cast at h2
    linarith
  have hVK : yCut m x y ≤ (K : ℝ) + 1 := by
    rw [yCut, div_le_iff₀ hsR]
    have h1 : m - 1 < (K + 1) * (x + y) := by
      have hdm := Nat.div_add_mod (m - 1) (x + y)
      have hlt : (m - 1) % (x + y) < x + y := Nat.mod_lt _ (by omega)
      nlinarith
    have h2 : m ≤ (K + 1) * (x + y) := by omega
    have h3 : (m : ℝ) ≤ (((K + 1) * (x + y) : ℕ) : ℝ) := by exact_mod_cast h2
    push_cast at h3
    linarith
  have hV1 : 1 ≤ yCut m x y := by
    rw [yCut, le_div_iff₀ hsR]
    have : ((x + y : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hs
    push_cast at this
    linarith
  have hmts := main_term_vs_sum (aCoeff m d x) (bCoeff x y) (yCut m x y) K hKV hVK hV1
  have hG2 : G2term m d x y
      = (1 / (x : ℝ)) * ((aCoeff m d x * (K : ℝ)
          + bCoeff x y * ((K : ℝ) * ((K : ℝ) + 1)) / 2)
        - (aCoeff m d x * yCut m x y + bCoeff x y * yCut m x y ^ 2 / 2)) := by
    unfold G2term G1term
    rw [hsum]
    ring
  rw [hG2, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (x : ℝ))]
  have hia : 1 / (x : ℝ) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  have habs : |(aCoeff m d x * (K : ℝ) + bCoeff x y * ((K : ℝ) * ((K : ℝ) + 1)) / 2)
      - (aCoeff m d x * yCut m x y + bCoeff x y * yCut m x y ^ 2 / 2)|
      ≤ |aCoeff m d x| + |bCoeff x y| * yCut m x y := by
    rw [abs_sub_comm]
    exact hmts
  have hYnn : (0 : ℝ) ≤ yCut m x y := by linarith
  calc 1 / (x : ℝ) * |(aCoeff m d x * (K : ℝ) + bCoeff x y * ((K : ℝ) * ((K : ℝ) + 1)) / 2)
          - (aCoeff m d x * yCut m x y + bCoeff x y * yCut m x y ^ 2 / 2)|
      ≤ 1 * (|aCoeff m d x| + |bCoeff x y| * yCut m x y) :=
        mul_le_mul hia habs (abs_nonneg _)
          (by positivity)
    _ = |aCoeff m d x| + |bCoeff x y| * yCut m x y := one_mul _

/-- **The bound of Lemma 18 at one pair:** `|G₃| ≤ (|A| + |B|(Y-1))(1 + log x)`,
from the character estimate. -/
theorem abs_G3term_le {m d x y : ℕ} (hm : 0 < m) (hd : 0 < d)
    (hy : 1 ≤ y) (haa : y < x) (hgcd : Nat.gcd x y = 1) (hbulk : d * x * (x + y) ≤ m) :
    |G3term m d x y|
      ≤ (|aCoeff m d x| + |bCoeff x y| * ((yBound m d x y - 1 : ℕ) : ℝ))
          * (1 + Real.log x) := by
  have hx : 0 < x := by omega
  have hs : 0 < x + y := by omega
  have hda2 : d * x * x < m := by nlinarith
  have hrange : ∀ y' ∈ Finset.Ico 1 (yBound m d x y), y * y' ≤ m := by
    intro y' hy'
    have := (mem_gtRange hm hs hy hda2).1 hy'
    omega
  obtain ⟨c, hc⟩ := inner_gt_estimate (m := m) (d := d) (x := x) (y := y) hx hgcd
    (yBound m d x y) hrange
  exact hc

/-! ## Aggregating over the pairs

The bulk part of the triple sum decomposes by pairs, and `bulk_pair_estimate`
applies to each.  The complementary part is bounded by `small_part_le`. -/

/-- **The bulk part of the triple sum, decomposed by pairs.** -/
theorem gtTriples_bulk_decompose {m d : ℕ} (hm : 0 < m) (hd : 0 < d) :
    ∑ t ∈ (gtTriples m d).filter (fun t => d * t.1 * (t.1 + t.2.1) ≤ m),
        (d * t.1 + (m - t.2.1 * t.2.2) / t.1)
      = ∑ p ∈ (coprimePairs m).filter (fun p => d * p.1 * (p.1 + p.2) ≤ m),
          ∑ y' ∈ (Finset.Ico 1 (yBound m d p.1 p.2)).filter (fun y' => p.1 ∣ (m - p.2 * y')),
            (d * p.1 + (m - p.2 * y') / p.1) := by
  classical
  have h := gtTriples_decompose (m := m) (d := d) hm
    (fun x y y' => if d * x * (x + y) ≤ m then d * x + (m - y * y') / x else 0)
  calc ∑ t ∈ (gtTriples m d).filter (fun t => d * t.1 * (t.1 + t.2.1) ≤ m),
          (d * t.1 + (m - t.2.1 * t.2.2) / t.1)
      = ∑ t ∈ gtTriples m d,
          (if d * t.1 * (t.1 + t.2.1) ≤ m then d * t.1 + (m - t.2.1 * t.2.2) / t.1 else 0) :=
        Finset.sum_filter _ _
    _ = ∑ p ∈ (coprimePairs m).filter (fun p => d * p.1 * p.1 < m),
          ∑ y' ∈ (Finset.Ico 1 (yBound m d p.1 p.2)).filter (fun y' => p.1 ∣ (m - p.2 * y')),
            (if d * p.1 * (p.1 + p.2) ≤ m then d * p.1 + (m - p.2 * y') / p.1 else 0) := h
    _ = ∑ p ∈ (coprimePairs m).filter (fun p => d * p.1 * p.1 < m),
          (if d * p.1 * (p.1 + p.2) ≤ m then
            ∑ y' ∈ (Finset.Ico 1 (yBound m d p.1 p.2)).filter (fun y' => p.1 ∣ (m - p.2 * y')),
              (d * p.1 + (m - p.2 * y') / p.1) else 0) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        split_ifs with hx'
        · rfl
        · simp
    _ = ∑ p ∈ (coprimePairs m).filter (fun p => d * p.1 * (p.1 + p.2) ≤ m),
          ∑ y' ∈ (Finset.Ico 1 (yBound m d p.1 p.2)).filter (fun y' => p.1 ∣ (m - p.2 * y')),
            (d * p.1 + (m - p.2 * y') / p.1) := by
        rw [← Finset.sum_filter, Finset.filter_filter]
        refine Finset.sum_congr (Finset.filter_congr fun p hp => ?_) (fun _ _ => rfl)
        obtain ⟨x, y⟩ := p
        obtain ⟨-, hx1, haa, -⟩ := mem_coprimePairs.1 hp
        have hx : 0 < x := by omega
        constructor
        · rintro ⟨-, h2⟩; exact h2
        · intro h2
          refine ⟨?_, h2⟩
          have hpos : 0 < d * x * y := Nat.mul_pos (Nat.mul_pos hd hx) (by omega)
          have hlt : d * x * x < d * x * (x + y) := by nlinarith
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
    gtTriples_bulk_small m d (fun x y y' => d * x + (m - y * y') / x)
  have hbd := gtTriples_bulk_decompose hm hd
  -- the bulk part, pair by pair
  have hpair : ∀ p ∈ Sb,
      |((∑ y' ∈ (Finset.Ico 1 (yBound m d p.1 p.2)).filter (fun y' => p.1 ∣ (m - p.2 * y')),
            (d * p.1 + (m - p.2 * y') / p.1) : ℕ) : ℝ)
          - ((d : ℝ) * (m : ℝ) / ((p.1 : ℝ) + (p.2 : ℝ)) + (m : ℝ) ^ 2 * cTerm p)|
        ≤ 2 * (((d * p.1 : ℕ) : ℝ) + 2 * (m : ℝ) / (p.1 : ℝ)) * (1 + Real.log m) := by
    intro p hp
    obtain ⟨x, y⟩ := p
    rw [hSb, Finset.mem_filter] at hp
    obtain ⟨hpc, hpb⟩ := hp
    obtain ⟨-, hx1, haa, hgcd⟩ := mem_coprimePairs.1 hpc
    exact bulk_pair_estimate hm hd hx1 haa hgcd hpb
  have hbulkest :
      |(∑ p ∈ Sb, ((∑ y' ∈ (Finset.Ico 1 (yBound m d p.1 p.2)).filter
              (fun y' => p.1 ∣ (m - p.2 * y')), (d * p.1 + (m - p.2 * y') / p.1) : ℕ) : ℝ))
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
      obtain ⟨x, y⟩ := p
      obtain ⟨-, hx1, haa, -⟩ := mem_coprimePairs.1 hpc
      have hx : 0 < x := by omega
      have hpos : 0 < d * x * y := Nat.mul_pos (Nat.mul_pos hd hx) (by omega)
      have hlt : d * x * x < d * x * (x + y) := by nlinarith
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
  have key : ∀ X Y M x'1 b2 : ℝ, |X - M| ≤ x'1 → 0 ≤ Y → Y ≤ b2 → |X + Y - M| ≤ x'1 + b2 := by
    intro X Y M x'1 b2 h1 h2 h3
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

/-- A per-pair bound of size `W·(1 + log m)` aggregates to `Err n`.  This is the
middle and outer layer, applied to whichever of `G₂`, `G₃` is at hand. -/
theorem aggregate_le {n : ℕ} (hn : 0 < n) (F : ℕ → ℕ → ℕ → ℕ → ℝ)
    (hF : ∀ d ∈ n.divisors, ∀ p ∈ (coprimePairs (n / d)).filter
        (fun p => d * p.1 * (p.1 + p.2) ≤ n / d),
      |F (n / d) d p.1 p.2|
        ≤ (((d * p.1 : ℕ) : ℝ) + 2 * ((n / d : ℕ) : ℝ) / (p.1 : ℝ))
            * (1 + Real.log ((n / d : ℕ) : ℝ))) :
    |∑ d ∈ n.divisors, ∑ p ∈ (coprimePairs (n / d)).filter
        (fun p => d * p.1 * (p.1 + p.2) ≤ n / d), F (n / d) d p.1 p.2| ≤ Err n := by
  classical
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hper : ∀ d ∈ n.divisors,
      |∑ p ∈ (coprimePairs (n / d)).filter (fun p => d * p.1 * (p.1 + p.2) ≤ n / d),
          F (n / d) d p.1 p.2|
        ≤ ((Nat.sqrt ((n / d - 1) / d) : ℝ) + 1)
            * (3 * ((n / d : ℕ) : ℝ) * (1 + Real.log ((n / d : ℕ) : ℝ))) := by
    intro d hd
    obtain ⟨hdn, -⟩ := Nat.mem_divisors.1 hd
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
    have hm0 : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hn hdn) hd0
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_sum (hF d hd)) ?_
    have hsub : (coprimePairs (n / d)).filter (fun p => d * p.1 * (p.1 + p.2) ≤ n / d)
        ⊆ (coprimePairs (n / d)).filter (fun p => d * p.1 * p.1 < n / d) := by
      intro p hp
      rw [Finset.mem_filter] at hp ⊢
      obtain ⟨hpc, hpb⟩ := hp
      refine ⟨hpc, ?_⟩
      obtain ⟨x, y⟩ := p
      obtain ⟨-, hx1, haa, -⟩ := mem_coprimePairs.1 hpc
      have hx : 0 < x := by omega
      have hpos : 0 < d * x * y := Nat.mul_pos (Nat.mul_pos hd0 hx) (by omega)
      have hlt : d * x * x < d * x * (x + y) := by nlinarith
      exact lt_of_lt_of_le hlt hpb
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => by positivity) ?_
    exact middle_layer hm0 hd0
  refine le_trans (Finset.sum_le_sum hper) ?_
  rw [Err]
  exact outer_layer hn

/-- **Lemma 16.**  `G₂(n) = O(n^{3/2+ε})`. -/
noncomputable def G2sum (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors, ∑ p ∈ (coprimePairs (n / d)).filter
    (fun p => d * p.1 * (p.1 + p.2) ≤ n / d), G2term (n / d) d p.1 p.2

/-- **Lemma 18.**  `G₃(n) = O(n^{3/2+ε})`. -/
noncomputable def G3sum (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors, ∑ p ∈ (coprimePairs (n / d)).filter
    (fun p => d * p.1 * (p.1 + p.2) ≤ n / d), G3term (n / d) d p.1 p.2

theorem abs_G2sum_le {n : ℕ} (hn : 0 < n) : |G2sum n| ≤ Err n := by
  refine aggregate_le hn (fun m d x y => G2term m d x y) fun d hd p hp => ?_
  obtain ⟨hdn, -⟩ := Nat.mem_divisors.1 hd
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
  have hm0 : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hn hdn) hd0
  obtain ⟨x, y⟩ := p
  rw [Finset.mem_filter] at hp
  obtain ⟨hpc, hpb⟩ := hp
  have hpy' : d * x * (x + y) ≤ n / d := hpb
  obtain ⟨-, hx1, haa, hgcd⟩ := mem_coprimePairs.1 hpc
  have hx : 0 < x := by omega
  have haR : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hmR : (1 : ℝ) ≤ ((n / d : ℕ) : ℝ) := by exact_mod_cast hm0
  have hlog : (0 : ℝ) ≤ Real.log ((n / d : ℕ) : ℝ) := Real.log_nonneg hmR
  have hx' := abs_G2term_le hm0 hd0 hx1 haa hpy'
  -- `|A| + |B|·Y ≤ d·x + 2m/x`
  have hAabs : |aCoeff (n / d) d x| = aCoeff (n / d) d x :=
    abs_of_nonneg (by unfold aCoeff; positivity)
  have hBabs : |bCoeff x y| = (y : ℝ) / (x : ℝ) := by
    unfold bCoeff
    rw [abs_div, abs_neg, abs_of_nonneg (by positivity : (0:ℝ) ≤ (y : ℝ)),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (x : ℝ))]
  have hsR : (0 : ℝ) < (x : ℝ) + (y : ℝ) := by
    have h1 : (0 : ℝ) ≤ (y : ℝ) := by positivity
    have h2 : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx
    linarith
  have hBY : |bCoeff x y| * yCut (n / d) x y ≤ ((n / d : ℕ) : ℝ) / (x : ℝ) := by
    rw [hBabs, yCut, div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
    have hma : (0 : ℝ) ≤ ((n / d : ℕ) : ℝ) * (x : ℝ) * (x : ℝ) := by positivity
    nlinarith [hma, Nat.cast_nonneg (α := ℝ) y]
  have hW : |aCoeff (n / d) d x| + |bCoeff x y| * yCut (n / d) x y
      ≤ ((d * x : ℕ) : ℝ) + 2 * ((n / d : ℕ) : ℝ) / (x : ℝ) := by
    rw [hAabs]
    unfold aCoeff
    have : ((n / d : ℕ) : ℝ) / (x : ℝ) + ((n / d : ℕ) : ℝ) / (x : ℝ)
        = 2 * ((n / d : ℕ) : ℝ) / (x : ℝ) := by ring
    linarith [hBY]
  have hWnn : (0 : ℝ) ≤ ((d * x : ℕ) : ℝ) + 2 * ((n / d : ℕ) : ℝ) / (x : ℝ) := by positivity
  nlinarith [hx', hW, hWnn, hlog]

theorem yBound_sub_one_le_yCut {m d x y : ℕ} (hd : 0 < d) (hy : 1 ≤ y) (haa : y < x)
    (hbulk : d * x * (x + y) ≤ m) :
    ((yBound m d x y - 1 : ℕ) : ℝ) ≤ yCut m x y := by
  have hx : 0 < x := by omega
  have hsR : (0 : ℝ) < (x : ℝ) + (y : ℝ) := by
    have h1 : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx
    have h2 : (0 : ℝ) ≤ (y : ℝ) := by positivity
    linarith
  have hUeq : yBound m d x y = (m - 1) / (x + y) + 1 := yBound_bulk_eq hd hy haa hbulk
  have hK : yBound m d x y - 1 = (m - 1) / (x + y) := by
    rw [hUeq, Nat.add_sub_cancel]
  rw [hK, yCut, le_div_iff₀ hsR]
  have h1 : (m - 1) / (x + y) * (x + y) ≤ m :=
    le_trans (Nat.div_mul_le_self _ _) (by omega)
  have h2 : (((m - 1) / (x + y) * (x + y) : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast h1
  push_cast at h2
  linarith

theorem abs_G3sum_le {n : ℕ} (hn : 0 < n) : |G3sum n| ≤ Err n := by
  refine aggregate_le hn (fun m d x y => G3term m d x y) fun d hd p hp => ?_
  obtain ⟨hdn, -⟩ := Nat.mem_divisors.1 hd
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
  have hm0 : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hn hdn) hd0
  obtain ⟨x, y⟩ := p
  rw [Finset.mem_filter] at hp
  obtain ⟨hpc, hpb⟩ := hp
  have hpy' : d * x * (x + y) ≤ n / d := hpb
  obtain ⟨-, hx1, haa, hgcd⟩ := mem_coprimePairs.1 hpc
  have hx : 0 < x := by omega
  have haR : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hmR : (1 : ℝ) ≤ ((n / d : ℕ) : ℝ) := by exact_mod_cast hm0
  have haleM : x ≤ n / d := by
    refine le_trans ?_ hpy'
    calc x = 1 * x * 1 := by ring
      _ ≤ d * x * (x + y) := Nat.mul_le_mul (Nat.mul_le_mul hd0 (le_refl x)) (by omega)
  have haleMR : (x : ℝ) ≤ ((n / d : ℕ) : ℝ) := by exact_mod_cast haleM
  have h := abs_G3term_le hm0 hd0 hx1 haa hgcd hpy'
  -- `|A| + |B|·(U-1) ≤ d·x + 2m/x`
  have hAabs : |aCoeff (n / d) d x| = aCoeff (n / d) d x :=
    abs_of_nonneg (by unfold aCoeff; positivity)
  have hBabs : |bCoeff x y| = (y : ℝ) / (x : ℝ) := by
    unfold bCoeff
    rw [abs_div, abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (y : ℝ)),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (x : ℝ))]
  have hsR : (0 : ℝ) < (x : ℝ) + (y : ℝ) := by
    have h1 : (0 : ℝ) ≤ (y : ℝ) := by positivity
    have h2 : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx
    linarith
  have hBY : |bCoeff x y| * yCut (n / d) x y ≤ ((n / d : ℕ) : ℝ) / (x : ℝ) := by
    rw [hBabs, yCut, div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
    have hma : (0 : ℝ) ≤ ((n / d : ℕ) : ℝ) * (x : ℝ) * (x : ℝ) := by positivity
    nlinarith [hma, Nat.cast_nonneg (α := ℝ) y]
  have hKY := yBound_sub_one_le_yCut hd0 hx1 haa hpy'
  have hBK : |bCoeff x y| * ((yBound (n / d) d x y - 1 : ℕ) : ℝ)
      ≤ |bCoeff x y| * yCut (n / d) x y :=
    mul_le_mul_of_nonneg_left hKY (abs_nonneg _)
  have hW : |aCoeff (n / d) d x| + |bCoeff x y| * ((yBound (n / d) d x y - 1 : ℕ) : ℝ)
      ≤ ((d * x : ℕ) : ℝ) + 2 * ((n / d : ℕ) : ℝ) / (x : ℝ) := by
    rw [hAabs]
    unfold aCoeff
    have hrw : ((n / d : ℕ) : ℝ) / (x : ℝ) + ((n / d : ℕ) : ℝ) / (x : ℝ)
        = 2 * ((n / d : ℕ) : ℝ) / (x : ℝ) := by ring
    linarith [hBK, hBY]
  have hlogle : Real.log (x : ℝ) ≤ Real.log ((n / d : ℕ) : ℝ) :=
    Real.log_le_log (by linarith) haleMR
  have hloga : (0 : ℝ) ≤ Real.log (x : ℝ) := Real.log_nonneg haR
  have hWnn : (0 : ℝ) ≤ ((d * x : ℕ) : ℝ) + 2 * ((n / d : ℕ) : ℝ) / (x : ℝ) := by positivity
  have hnn : (0 : ℝ) ≤ |aCoeff (n / d) d x|
      + |bCoeff x y| * ((yBound (n / d) d x y - 1 : ℕ) : ℝ) := by positivity
  nlinarith [h, hW, hWnn, hlogle, hloga, hnn]

/-- **Lemma 16.**  `G₂(n) = O(n^{3/2+ε})`. -/
theorem lemma_g_two {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n → |G2sum n| ≤ C * (n : ℝ) ^ (3 / 2 + ε) := by
  obtain ⟨C, hC, hErr⟩ := error_isBigO hε
  exact ⟨C, hC, fun n hn => le_trans (abs_G2sum_le hn) (hErr n hn)⟩

/-- **Lemma 18.**  `G₃(n) = O(n^{3/2+ε})`. -/
theorem lemma_g_three {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n → |G3sum n| ≤ C * (n : ℝ) ^ (3 / 2 + ε) := by
  obtain ⟨C, hC, hErr⟩ := error_isBigO hε
  exact ⟨C, hC, fun n hn => le_trans (abs_G3sum_le hn) (hErr n hn)⟩

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

Adding the diagonal (bounded by `sum_diag_isBigO`) and Lemma 19. -/

/-- **`Q(n) = C·n²·∑_{d∣n} 1/d² + O(n^{3/2+ε})`.** -/
theorem Q_isBigO {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 0 < n →
      |((Qquad n : ℤ) : ℝ) - cConst * (n : ℝ) ^ 2 * ∑ d ∈ n.divisors, 1 / (d : ℝ) ^ 2|
        ≤ K * (n : ℝ) ^ (3 / 2 + ε) := by
  classical
  obtain ⟨C1, hC1, hErr⟩ := error_isBigO hε
  obtain ⟨C2, hC2, hDiag⟩ := sum_diag_isBigO hε
  obtain ⟨C3, hC3, hG1⟩ := lemma19_isBigO hε
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

/-! ## The remainder sums

Equation (heilbron) turns `R(n)` into `∑_{k} remSum(n,k)` at the cost of
`∑_k gcd(n,k) ≤ n·d(n) = O(n^{1+ε})`. -/

/-- **`∑_{2k ≤ n} remSum(n,k) = C·n² + O(n^{3/2+ε})`.** -/
theorem sum_remSum_isBigO {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 0 < n →
      |((∑ k ∈ allShifts n, remSum n k : ℕ) : ℝ) - cConst * (n : ℝ) ^ 2|
        ≤ K * (n : ℝ) ^ (3 / 2 + ε) := by
  obtain ⟨K1, hK1, hR⟩ := R_isBigO hε
  obtain ⟨C0, hC0, hCd⟩ := exists_card_divisors_le hε
  refine ⟨K1 + C0, by positivity, fun n hn => ?_⟩
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hRcast : ((Rquad n : ℤ) : ℝ) = ((∑ q ∈ quadruplesAll n, q.2.1 : ℕ) : ℝ) := by
    unfold Rquad; push_cast; ring
  have heil : ((∑ k ∈ allShifts n, remSum n k : ℕ) : ℝ)
      = ((∑ k ∈ allShifts n, Nat.gcd n k : ℕ) : ℝ)
        + ((∑ q ∈ quadruplesAll n, q.2.1 : ℕ) : ℝ) := by
    exact_mod_cast heilbron hn
  have hgcd : ((∑ k ∈ allShifts n, Nat.gcd n k : ℕ) : ℝ) ≤ (n : ℝ) * (n.divisors.card : ℝ) := by
    exact_mod_cast sum_gcd_le hn
  have hgcdnn : (0 : ℝ) ≤ ((∑ k ∈ allShifts n, Nat.gcd n k : ℕ) : ℝ) := by positivity
  have hbound : (n : ℝ) * (n.divisors.card : ℝ) ≤ C0 * (n : ℝ) ^ (3 / 2 + ε) := by
    have h1 : (n : ℝ) * (n.divisors.card : ℝ) ≤ (n : ℝ) * (C0 * (n : ℝ) ^ ε) :=
      mul_le_mul_of_nonneg_left (hCd n hn.ne') (by linarith)
    have h2 : (n : ℝ) * (C0 * (n : ℝ) ^ ε) = C0 * (n : ℝ) ^ (1 + ε) := by
      rw [Real.rpow_add hnpos, Real.rpow_one]; ring
    have h3 : (n : ℝ) ^ (1 + ε) ≤ (n : ℝ) ^ (3 / 2 + ε) :=
      Real.rpow_le_rpow_of_exponent_le hnR (by linarith)
    nlinarith [hC0]
  have hRb := hR n hn
  rw [heil, ← hRcast]
  have htri := abs_add_le (((∑ k ∈ allShifts n, Nat.gcd n k : ℕ) : ℝ))
    (((Rquad n : ℤ) : ℝ) - cConst * (n : ℝ) ^ 2)
  rw [abs_of_nonneg hgcdnn] at htri
  have heq : ((∑ k ∈ allShifts n, Nat.gcd n k : ℕ) : ℝ) + ((Rquad n : ℤ) : ℝ)
        - cConst * (n : ℝ) ^ 2
      = ((∑ k ∈ allShifts n, Nat.gcd n k : ℕ) : ℝ)
        + (((Rquad n : ℤ) : ℝ) - cConst * (n : ℝ) ^ 2) := by ring
  rw [heq]
  linarith [htri, hRb, hgcd, hbound]

/-! ## The symmetry `M(n,k) = M(n,n-k)`

The algorithm's cost at shift `k` depends only on `min k (n-k)`, so summing
over all `0 ≤ k < n` double-counts every shift `1 ≤ j` with `2j ≤ n`, except
the midpoint `j = n/2` when `n` is even. -/

theorem allShifts_eq_filter {n : ℕ} (hn : 0 < n) :
    allShifts n = (Finset.Ico 1 n).filter (fun k => 2 * k ≤ n) := by
  ext k
  rw [mem_allShifts, Finset.mem_filter, Finset.mem_Ico]
  omega

theorem card_allShifts (n : ℕ) : (allShifts n).card = n / 2 := by
  have h : allShifts n = Finset.Icc 1 (n / 2) := by
    ext k
    rw [mem_allShifts, Finset.mem_Icc]
    omega
  rw [h, Nat.card_Icc]
  omega

/-- **The double count.** -/
theorem sum_min_eq {n : ℕ} (hn : 0 < n) (f : ℕ → ℕ) :
    (∑ k ∈ Finset.Ico 1 n, f (min k (n - k))) + (if 2 ∣ n then f (n / 2) else 0)
      = 2 * ∑ j ∈ allShifts n, f j := by
  classical
  rw [allShifts_eq_filter hn]
  have hsplit : ∑ k ∈ Finset.Ico 1 n, f (min k (n - k))
      = (∑ k ∈ (Finset.Ico 1 n).filter (fun k => 2 * k ≤ n), f (min k (n - k)))
        + ∑ k ∈ (Finset.Ico 1 n).filter (fun k => ¬ (2 * k ≤ n)), f (min k (n - k)) :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hAval : ∑ k ∈ (Finset.Ico 1 n).filter (fun k => 2 * k ≤ n), f (min k (n - k))
      = ∑ k ∈ (Finset.Ico 1 n).filter (fun k => 2 * k ≤ n), f k := by
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_filter, Finset.mem_Ico] at hk
    congr 1
    omega
  have hBval : ∑ k ∈ (Finset.Ico 1 n).filter (fun k => ¬ (2 * k ≤ n)), f (min k (n - k))
      = ∑ j ∈ (Finset.Ico 1 n).filter (fun k => 2 * k < n), f j := by
    refine Finset.sum_bij' (i := fun k _ => n - k) (j := fun k _ => n - k) ?_ ?_ ?_ ?_ ?_
    · intro k hk
      rw [Finset.mem_filter, Finset.mem_Ico] at hk ⊢
      omega
    · intro k hk
      rw [Finset.mem_filter, Finset.mem_Ico] at hk ⊢
      omega
    · intro k hk
      rw [Finset.mem_filter, Finset.mem_Ico] at hk
      omega
    · intro k hk
      rw [Finset.mem_filter, Finset.mem_Ico] at hk
      omega
    · intro k hk
      rw [Finset.mem_filter, Finset.mem_Ico] at hk
      congr 1
      omega
  have hAA' : ∑ k ∈ (Finset.Ico 1 n).filter (fun k => 2 * k ≤ n), f k
      = (∑ j ∈ (Finset.Ico 1 n).filter (fun k => 2 * k < n), f j)
        + (if 2 ∣ n then f (n / 2) else 0) := by
    have hs := (Finset.sum_filter_add_sum_filter_not
      ((Finset.Ico 1 n).filter (fun k => 2 * k ≤ n)) (fun k => 2 * k < n) f).symm
    rw [hs, Finset.filter_filter, Finset.filter_filter]
    congr 1
    · exact Finset.sum_congr (Finset.filter_congr fun k hk => by
        rw [Finset.mem_Ico] at hk; omega) (fun _ _ => rfl)
    · by_cases hev : 2 ∣ n
      · have he : (Finset.Ico 1 n).filter (fun k => 2 * k ≤ n ∧ ¬ (2 * k < n)) = {n / 2} := by
          ext k
          rw [Finset.mem_filter, Finset.mem_Ico, Finset.mem_singleton]
          omega
        rw [he, Finset.sum_singleton, if_pos hev]
      · have he : (Finset.Ico 1 n).filter (fun k => 2 * k ≤ n ∧ ¬ (2 * k < n)) = ∅ := by
          ext k
          rw [Finset.mem_filter, Finset.mem_Ico]
          simp only [Finset.notMem_empty, iff_false]
          omega
        rw [he, Finset.sum_empty, if_neg hev]
  rw [hsplit, hAval, hBval, hAA']
  ring

/-- **The total cost over all shifts.** -/
theorem sum_algCost_eq {n : ℕ} (hn : 0 < n) :
    (∑ k ∈ Finset.range n, algCost n k) + (if 2 ∣ n then cost n (n / 2) else 0)
      = 2 * ∑ j ∈ allShifts n, cost n j := by
  have h0 : algCost n 0 = 0 := by
    unfold algCost
    simp [cost_zero]
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hn, h0, zero_add]
  exact sum_min_eq hn (cost n)

/-- **The cost over the shifts, via `cost + gcd = n + 2·remSum`.** -/
theorem sum_cost_allShifts {n : ℕ} (hn : 0 < n) :
    (∑ j ∈ allShifts n, cost n j) + ∑ j ∈ allShifts n, Nat.gcd n j
      = (n / 2) * n + 2 * ∑ j ∈ allShifts n, remSum n j := by
  rw [← Finset.sum_add_distrib]
  have hc : ∀ j ∈ allShifts n, cost n j + Nat.gcd n j = n + 2 * remSum n j :=
    fun j _ => cost_add_gcd j n
  rw [Finset.sum_congr rfl hc, Finset.sum_add_distrib, Finset.sum_const, card_allShifts,
    smul_eq_mul, Finset.mul_sum]

/-! ## Theorem 14 -/

/-- **Theorem 14.**  `avgCost n = D·n + O(n^{1/2+ε})` with `D = 1 + 4C ≈ 1.85`. -/
theorem theorem14 {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 0 < n →
      |avgCost n - dConst * (n : ℝ)| ≤ K * (n : ℝ) ^ (1 / 2 + ε) := by
  obtain ⟨K1, hK1, hS⟩ := sum_remSum_isBigO hε
  obtain ⟨C0, hC0, hCd⟩ := exists_card_divisors_le hε
  refine ⟨4 * K1 + 2 * C0 + 4, by positivity, fun n hn => ?_⟩
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hpow : (1 : ℝ) ≤ (n : ℝ) ^ (1 / 2 + ε : ℝ) := Real.one_le_rpow hnR (by linarith)
  -- the three ingredients, in `ℝ`
  set corr : ℕ := if 2 ∣ n then cost n (n / 2) else 0 with hcorr
  have hcorrle : corr ≤ 3 * n := by
    rw [hcorr]
    split_ifs with h
    · exact cost_le_three_mul (by omega)
    · omega
  have hA : (∑ k ∈ Finset.range n, (algCost n k : ℝ)) + (corr : ℝ)
      = 2 * ∑ j ∈ allShifts n, (cost n j : ℝ) := by
    exact_mod_cast sum_algCost_eq hn
  have hB : (∑ j ∈ allShifts n, (cost n j : ℝ)) + ((∑ j ∈ allShifts n, Nat.gcd n j : ℕ) : ℝ)
      = ((n / 2 : ℕ) : ℝ) * (n : ℝ) + 2 * ((∑ j ∈ allShifts n, remSum n j : ℕ) : ℝ) := by
    exact_mod_cast sum_cost_allShifts hn
  set S : ℝ := ((∑ j ∈ allShifts n, remSum n j : ℕ) : ℝ) with hSdef
  set G : ℝ := ((∑ j ∈ allShifts n, Nat.gcd n j : ℕ) : ℝ) with hGdef
  have hGnn : (0 : ℝ) ≤ G := by rw [hGdef]; positivity
  have hcorrnn : (0 : ℝ) ≤ (corr : ℝ) := by positivity
  have hcorrR : (corr : ℝ) ≤ 3 * (n : ℝ) := by exact_mod_cast hcorrle
  have hGle : G ≤ (n : ℝ) * (C0 * (n : ℝ) ^ ε) := by
    have h1 : G ≤ (n : ℝ) * (n.divisors.card : ℝ) := by
      rw [hGdef]; exact_mod_cast sum_gcd_le hn
    have h2 : (n : ℝ) * (n.divisors.card : ℝ) ≤ (n : ℝ) * (C0 * (n : ℝ) ^ ε) :=
      mul_le_mul_of_nonneg_left (hCd n hn.ne') (by linarith)
    linarith
  -- the rounding of `n/2`
  have hhalf : |2 * ((n / 2 : ℕ) : ℝ) * (n : ℝ) - (n : ℝ) ^ 2| ≤ (n : ℝ) := by
    have h1 : 2 * (n / 2) ≤ n := by omega
    have h2 : n ≤ 2 * (n / 2) + 1 := by omega
    have h1R : 2 * ((n / 2 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
    have h2R : (n : ℝ) ≤ 2 * ((n / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast h2
    rw [abs_le]
    constructor <;> nlinarith
  -- assemble the numerator
  have hnum : (∑ k ∈ Finset.range n, (algCost n k : ℝ)) - dConst * (n : ℝ) ^ 2
      = (2 * ((n / 2 : ℕ) : ℝ) * (n : ℝ) - (n : ℝ) ^ 2)
        + 4 * (S - cConst * (n : ℝ) ^ 2) - 2 * G - (corr : ℝ) := by
    rw [dConst]
    nlinarith [hA, hB]
  have hSb := hS n hn
  have key : ∀ x y z w b1 b2 b3 b4 : ℝ,
      |x| ≤ b1 → |y| ≤ b2 → 0 ≤ z → z ≤ b3 → 0 ≤ w → w ≤ b4 →
      |x + y - z - w| ≤ b1 + b2 + b3 + b4 := by
    intro x y z w b1 b2 b3 b4 h1 h2 h3 h4 h5 h6
    have e : x + y - z - w = x + y + -z + -w := by ring
    rw [e]
    calc |x + y + -z + -w| ≤ |x + y + -z| + |(-w)| := abs_add_le _ _
      _ ≤ (|x + y| + |(-z)|) + |(-w)| := by linarith [abs_add_le (x + y) (-z)]
      _ ≤ ((|x| + |y|) + |(-z)|) + |(-w)| := by linarith [abs_add_le x y]
      _ = |x| + |y| + z + w := by
          rw [abs_neg, abs_neg, abs_of_nonneg h3, abs_of_nonneg h5]
      _ ≤ b1 + b2 + b3 + b4 := by linarith
  have hy : |4 * (S - cConst * (n : ℝ) ^ 2)| ≤ 4 * (K1 * (n : ℝ) ^ (3 / 2 + ε)) := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 4)]
    linarith [hSb]
  have hnumb : |(∑ k ∈ Finset.range n, (algCost n k : ℝ)) - dConst * (n : ℝ) ^ 2|
      ≤ (n : ℝ) + 4 * (K1 * (n : ℝ) ^ (3 / 2 + ε)) + 2 * ((n : ℝ) * (C0 * (n : ℝ) ^ ε))
        + 3 * (n : ℝ) := by
    rw [hnum]
    exact key _ _ _ _ _ _ _ _ hhalf hy (by linarith) (by linarith) hcorrnn hcorrR
  -- divide by `n`
  have havg : avgCost n - dConst * (n : ℝ)
      = ((∑ k ∈ Finset.range n, (algCost n k : ℝ)) - dConst * (n : ℝ) ^ 2) / (n : ℝ) := by
    rw [avgCost]
    field_simp
  rw [havg, abs_div, abs_of_nonneg (le_of_lt hnpos), div_le_iff₀ hnpos]
  refine hnumb.trans ?_
  have hr1 : (n : ℝ) ^ (3 / 2 + ε : ℝ) = (n : ℝ) ^ (1 / 2 + ε : ℝ) * (n : ℝ) := by
    rw [show (3 / 2 + ε : ℝ) = (1 / 2 + ε) + 1 by ring, Real.rpow_add hnpos, Real.rpow_one]
  have hr2 : (n : ℝ) ^ (ε : ℝ) ≤ (n : ℝ) ^ (1 / 2 + ε : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hnR (by linarith)
  rw [hr1]
  nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 hr2) hnpos.le) hC0.le,
    mul_nonneg (sub_nonneg.2 hpow) hnpos.le, hK1, hnpos, hpow]

end BlockCycleRotation
