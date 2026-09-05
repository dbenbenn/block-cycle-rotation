/-
# Theorem 9 and Theorem 7

Theorem 9 states that `avgCost n / n` converges, and identifies the limit as
`2∫₀^{1/2} f` where `f` is the *relative cost*: the number of moves per element
the algorithm uses to rotate by a fraction `x` of the array.

`f = 1 + ψ` on `[0,1/2]`, where `ψ` is defined by the recursion the block cycle
algorithm follows.  Writing `{t}` for the fractional part, the recursion is

```
ψ(x) = 2x + Out(x)·ψ(In(x)),   Out(x) = x(1+{1/x}),  In(x) = {1/x}/(1+{1/x}),
```

with `In 0 = Out 0 = 0`.  This is the paper's `(k,n) ↦ (n mod k, k + n mod k)`
recursion in relative coordinates: at `x = k/n` one has `Out(x) = n'/n` and
`In(x) = k'/n'`.

Unravelled, `ψ` is the series `2x + 2∑_{i≥1} Out(x)···Out(Inⁱ⁻¹(x))·Inⁱ(x)`,
which converges uniformly because `In` maps into `[0,1/2)` and `Out ≤ 2/3`
there.  That is Theorem 7's convergence; continuity at irrationals follows
since `In` and `Out` are continuous away from `1/x ∈ ℤ` and preserve
irrationality.
-/

import BlockCycleRotation.Theorem14
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.BoxIntegral.UnitPartition
import Mathlib.Analysis.BoxIntegral.Integrability

namespace BlockCycleRotation

open Filter Topology

/-! ## The two maps -/

/-- `In(x) = {1/x}/(1+{1/x})`, the relative shift of the next subproblem. -/
noncomputable def Inn (x : ℝ) : ℝ :=
  if x = 0 then 0 else Int.fract (1 / x) / (1 + Int.fract (1 / x))

/-- `Out(x) = x(1+{1/x})`, the relative size of the next subproblem. -/
noncomputable def Outt (x : ℝ) : ℝ :=
  if x = 0 then 0 else x * (1 + Int.fract (1 / x))

theorem Inn_zero : Inn 0 = 0 := by simp [Inn]

theorem Outt_zero : Outt 0 = 0 := by simp [Outt]

theorem Inn_nonneg (x : ℝ) : 0 ≤ Inn x := by
  unfold Inn
  split_ifs
  · exact le_refl 0
  · have h1 : (0 : ℝ) ≤ Int.fract (1 / x) := Int.fract_nonneg _
    positivity

/-- **`In` maps into `[0,1/2)`.**  Since `{1/x} < 1`, `{1/x}/(1+{1/x}) < 1/2`. -/
theorem Inn_lt_half (x : ℝ) : Inn x < 1 / 2 := by
  unfold Inn
  split_ifs
  · norm_num
  · have h1 : (0 : ℝ) ≤ Int.fract (1 / x) := Int.fract_nonneg _
    have h2 : Int.fract (1 / x) < 1 := Int.fract_lt_one _
    rw [div_lt_div_iff₀ (by linarith) (by norm_num)]
    linarith

theorem Outt_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Outt x := by
  unfold Outt
  split_ifs
  · exact le_refl 0
  · have h1 : (0 : ℝ) ≤ Int.fract (1 / x) := Int.fract_nonneg _
    positivity

/-- **`Out ≤ 2/3` on `[0,1/2]`.**  With `m = ⌊1/x⌋ ≥ 2` one has
`Out(x) = 1 - (m-1)x` and `x > 1/(m+1)`, so `Out(x) < 2/(m+1) ≤ 2/3`. -/
theorem Outt_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) : Outt x ≤ 2 / 3 := by
  unfold Outt
  split_ifs with h
  · norm_num
  · have hx0' : 0 < x := lt_of_le_of_ne hx0 (Ne.symm h)
    have h2 : (2 : ℝ) ≤ 1 / x := by
      rw [le_div_iff₀ hx0']
      linarith
    have hm2 : (2 : ℝ) ≤ ((⌊1 / x⌋ : ℤ) : ℝ) := by
      have : (2 : ℤ) ≤ ⌊1 / x⌋ := Int.le_floor.2 (by exact_mod_cast h2)
      exact_mod_cast this
    have hfl' : 1 / x < ((⌊1 / x⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
    have hub : 1 < (((⌊1 / x⌋ : ℤ) : ℝ) + 1) * x := (div_lt_iff₀ hx0').1 hfl'
    have heq : x * (1 + Int.fract (1 / x)) = 1 - (((⌊1 / x⌋ : ℤ) : ℝ) - 1) * x := by
      rw [Int.fract]
      field_simp
      ring
    rw [heq]
    nlinarith [hub, hm2, hx0']

/-! ## The series for `ψ`

`ψ(x) = 2x + 2∑_{i≥1} Out(x)···Out(Inⁱ⁻¹(x))·Inⁱ(x)`.  Every iterate after the
first lies in `[0,1/2)`, where `Out ≤ 2/3`, so the `i`-th term is at most
`(2/3)ⁱ` and the series converges uniformly. -/

/-- The `i`-th term of the series for `ψ`. -/
noncomputable def psiTerm (x : ℝ) (i : ℕ) : ℝ :=
  2 * (∏ m ∈ Finset.range i, Outt (Inn^[m] x)) * (Inn^[i] x)

theorem iterate_Inn_mem {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) (i : ℕ) :
    0 ≤ Inn^[i] x ∧ Inn^[i] x ≤ 1 / 2 := by
  cases i with
  | zero => exact ⟨hx0, hx⟩
  | succ j =>
    rw [Function.iterate_succ_apply']
    exact ⟨Inn_nonneg _, le_of_lt (Inn_lt_half _)⟩

theorem prod_Outt_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) (i : ℕ) :
    (0 ≤ ∏ m ∈ Finset.range i, Outt (Inn^[m] x))
      ∧ (∏ m ∈ Finset.range i, Outt (Inn^[m] x)) ≤ (2 / 3) ^ i := by
  constructor
  · refine Finset.prod_nonneg fun m _ => Outt_nonneg (iterate_Inn_mem hx0 hx m).1
  · calc (∏ m ∈ Finset.range i, Outt (Inn^[m] x))
        ≤ ∏ _m ∈ Finset.range i, (2 / 3 : ℝ) := by
          refine Finset.prod_le_prod (fun m _ => Outt_nonneg (iterate_Inn_mem hx0 hx m).1)
            (fun m _ => Outt_le (iterate_Inn_mem hx0 hx m).1 (iterate_Inn_mem hx0 hx m).2)
      _ = (2 / 3 : ℝ) ^ i := by rw [Finset.prod_const, Finset.card_range]

theorem psiTerm_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) (i : ℕ) : 0 ≤ psiTerm x i := by
  unfold psiTerm
  have h1 := (prod_Outt_le hx0 hx i).1
  have h2 := (iterate_Inn_mem hx0 hx i).1
  positivity

theorem psiTerm_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) (i : ℕ) :
    psiTerm x i ≤ (2 / 3 : ℝ) ^ i := by
  unfold psiTerm
  obtain ⟨hp0, hp⟩ := prod_Outt_le hx0 hx i
  obtain ⟨hi0, hi⟩ := iterate_Inn_mem hx0 hx i
  have hpow : (0 : ℝ) ≤ (2 / 3 : ℝ) ^ i := by positivity
  nlinarith

theorem psi_summable {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) : Summable (psiTerm x) := by
  refine Summable.of_nonneg_of_le (psiTerm_nonneg hx0 hx) (psiTerm_le hx0 hx) ?_
  exact summable_geometric_of_lt_one (by norm_num) (by norm_num)

/-- **The relative type-A cost.**  `ψ(x)` is the number of type-A moves per
element when rotating by a fraction `x ≤ 1/2` of the array. -/
noncomputable def psi (x : ℝ) : ℝ := ∑' i, psiTerm x i

theorem psi_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) : 0 ≤ psi x :=
  tsum_nonneg (psiTerm_nonneg hx0 hx)

theorem psi_le_three {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) : psi x ≤ 3 := by
  have hgeo : ∑' i : ℕ, (2 / 3 : ℝ) ^ i = 3 := by
    rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
  calc psi x ≤ ∑' i : ℕ, (2 / 3 : ℝ) ^ i :=
        (psi_summable hx0 hx).tsum_le_tsum (psiTerm_le hx0 hx)
          (summable_geometric_of_lt_one (by norm_num) (by norm_num))
    _ = 3 := hgeo

theorem psi_zero : psi 0 = 0 := by
  unfold psi
  have h : ∀ i, psiTerm 0 i = 0 := by
    intro i
    unfold psiTerm
    have : Inn^[i] (0 : ℝ) = 0 := by
      induction i with
      | zero => rfl
      | succ j ih => rw [Function.iterate_succ_apply', ih, Inn_zero]
    rw [this, mul_zero]
  simp [h]

/-- **The functional equation.**  `ψ(x) = 2x + Out(x)·ψ(In(x))`. -/
theorem psi_eq {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    psi x = 2 * x + Outt x * psi (Inn x) := by
  have hIn0 : 0 ≤ Inn x := Inn_nonneg x
  have hIn : Inn x ≤ 1 / 2 := le_of_lt (Inn_lt_half x)
  have hshift : ∀ i : ℕ, psiTerm x (i + 1) = Outt x * psiTerm (Inn x) i := by
    intro i
    unfold psiTerm
    rw [Finset.prod_range_succ']
    have hit : ∀ m : ℕ, Inn^[m] (Inn x) = Inn^[m + 1] x := by
      intro m
      rw [← Function.iterate_succ_apply]
    have hprod : ∏ m ∈ Finset.range i, Outt (Inn^[m] (Inn x))
        = ∏ m ∈ Finset.range i, Outt (Inn^[m + 1] x) :=
      Finset.prod_congr rfl fun m _ => by rw [hit]
    rw [hprod, hit i, Function.iterate_zero_apply]
    ring
  have hsum1 : Summable (fun i => psiTerm x (i + 1)) :=
    (summable_nat_add_iff 1).2 (psi_summable hx0 hx)
  rw [psi, tsum_eq_zero_add' hsum1]
  have h0 : psiTerm x 0 = 2 * x := by
    unfold psiTerm
    simp
  rw [h0]
  congr 1
  rw [tsum_congr hshift, tsum_mul_left, psi]

/-! ## The bridge to the Euclidean algorithm

At `x = k/n` the recursion for `ψ` is exactly the algorithm's
`(k, n) ↦ (n mod k, k + n mod k)`. -/

theorem floor_nat_div {n k : ℕ} (hk : 0 < k) : ⌊(n : ℝ) / (k : ℝ)⌋ = ((n / k : ℕ) : ℤ) := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have h1 : (((n / k : ℕ) : ℤ) : ℝ) ≤ (n : ℝ) / (k : ℝ) := by
    rw [le_div_iff₀ hkR, Int.cast_natCast]
    have h : k * (n / k) ≤ n := Nat.mul_div_le n k
    have hc : ((k * (n / k) : ℕ) : ℝ) ≤ ((n : ℕ) : ℝ) := by exact_mod_cast h
    rw [Nat.cast_mul] at hc
    linarith
  have h2 : (n : ℝ) / (k : ℝ) < (((n / k : ℕ) : ℤ) : ℝ) + 1 := by
    rw [div_lt_iff₀ hkR, Int.cast_natCast]
    have hd : k * (n / k) + n % k = n := Nat.div_add_mod n k
    have hm : n % k < k := Nat.mod_lt _ hk
    have h : n < k * (n / k + 1) := by
      have h3 : k * (n / k + 1) = k * (n / k) + k := by ring
      omega
    have hc : ((n : ℕ) : ℝ) < ((k * (n / k + 1) : ℕ) : ℝ) := by exact_mod_cast h
    rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at hc
    linarith
  exact Int.floor_eq_iff.2 ⟨h1, h2⟩

theorem fract_nat_div {n k : ℕ} (hk : 0 < k) :
    Int.fract ((n : ℝ) / (k : ℝ)) = ((n % k : ℕ) : ℝ) / (k : ℝ) := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  rw [Int.fract, floor_nat_div hk, Int.cast_natCast]
  have h : k * (n / k) + n % k = n := Nat.div_add_mod n k
  have hR : (k : ℝ) * ((n / k : ℕ) : ℝ) + ((n % k : ℕ) : ℝ) = (n : ℝ) := by exact_mod_cast h
  field_simp
  linarith

theorem one_div_nat_div {n k : ℕ} (hn : 0 < n) (hk : 0 < k) :
    1 / ((k : ℝ) / (n : ℝ)) = (n : ℝ) / (k : ℝ) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  field_simp

theorem Outt_rat {n k : ℕ} (hn : 0 < n) (hk : 0 < k) :
    Outt ((k : ℝ) / (n : ℝ)) = ((k + n % k : ℕ) : ℝ) / (n : ℝ) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hne : (k : ℝ) / (n : ℝ) ≠ 0 := by positivity
  unfold Outt
  rw [if_neg hne, one_div_nat_div hn hk, fract_nat_div hk]
  push_cast
  field_simp

theorem Inn_rat {n k : ℕ} (hn : 0 < n) (hk : 0 < k) :
    Inn ((k : ℝ) / (n : ℝ)) = ((n % k : ℕ) : ℝ) / ((k + n % k : ℕ) : ℝ) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hne : (k : ℝ) / (n : ℝ) ≠ 0 := by positivity
  unfold Inn
  rw [if_neg hne, one_div_nat_div hn hk, fract_nat_div hk]
  push_cast
  field_simp

/-- **The bridge.**  `n·ψ(k/n) = 2·remSum(n,k)` for `2k ≤ n`. -/
theorem psi_rat : ∀ k : ℕ, ∀ n : ℕ, 0 < n → 2 * k ≤ n →
    (n : ℝ) * psi ((k : ℝ) / (n : ℝ)) = 2 * (remSum n k : ℝ) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro n hn hkn
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [psi_zero]
    · have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
      have hx0 : (0 : ℝ) ≤ (k : ℝ) / (n : ℝ) := by positivity
      have hx : (k : ℝ) / (n : ℝ) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ hnR (by norm_num)]
        have : ((2 * k : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
        push_cast at this
        linarith
      set k' := n % k with hk'
      set n' := k + k' with hn'
      have hk'k : k' < k := Nat.mod_lt _ hk
      have hn'pos : 0 < n' := by omega
      have hn'R : (0 : ℝ) < (n' : ℝ) := by exact_mod_cast hn'pos
      have hIH : (n' : ℝ) * psi ((k' : ℝ) / (n' : ℝ)) = 2 * (remSum n' k' : ℝ) :=
        ih k' hk'k n' hn'pos (by omega)
      rw [psi_eq hx0 hx, Outt_rat hn hk, Inn_rat hn hk]
      have hcast : ((k + n % k : ℕ) : ℝ) = (n' : ℝ) := by rw [hn', hk']
      have hcast2 : ((n % k : ℕ) : ℝ) = (k' : ℝ) := by rw [hk']
      rw [hcast, hcast2]
      have hstep : remSum n' k' = remSum k k' := remSum_step
      have hrec : remSum n k = k + remSum k k' := by
        rw [remSum_of_pos n hk.ne', hk']
      rw [hrec]
      push_cast
      have hexp : (n : ℝ) * (2 * ((k : ℝ) / (n : ℝ))
          + (n' : ℝ) / (n : ℝ) * psi ((k' : ℝ) / (n' : ℝ)))
          = 2 * (k : ℝ) + (n' : ℝ) * psi ((k' : ℝ) / (n' : ℝ)) := by
        field_simp
      rw [hexp, hIH, hstep]
      ring

/-! ## The relative cost `f`

`f(x) = 1 + ψ(min x (1-x))` is the number of moves per element.  The `min`
records that the algorithm rotates by the shorter of the two segments. -/

/-- **The relative cost.** -/
noncomputable def fCost (x : ℝ) : ℝ := 1 + psi (min x (1 - x))

theorem min_self_sub {n k : ℕ} (hn : 0 < n) (hk : k ≤ n) :
    min ((k : ℝ) / (n : ℝ)) (1 - (k : ℝ) / (n : ℝ))
      = ((min k (n - k) : ℕ) : ℝ) / (n : ℝ) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hsub : 1 - (k : ℝ) / (n : ℝ) = ((n - k : ℕ) : ℝ) / (n : ℝ) := by
    have hc : ((n - k : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) := by
      have := Nat.cast_sub (R := ℝ) hk
      linarith [this]
    rw [hc]
    field_simp
  rw [hsub]
  rcases le_total k (n - k) with h | h
  · have hd : ((k : ℕ) : ℝ) / (n : ℝ) ≤ ((n - k : ℕ) : ℝ) / (n : ℝ) := by
      gcongr
    rw [min_eq_left hd, Nat.min_eq_left h]
  · have hd : ((n - k : ℕ) : ℝ) / (n : ℝ) ≤ ((k : ℕ) : ℝ) / (n : ℝ) := by
      gcongr
    rw [min_eq_right hd, Nat.min_eq_right h]

theorem gcd_min_self_sub {n k : ℕ} (hk : k ≤ n) :
    Nat.gcd n (min k (n - k)) = Nat.gcd n k := by
  rcases le_total k (n - k) with h | h
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right h]
    calc Nat.gcd n (n - k) = Nat.gcd (k + (n - k)) (n - k) := by congr 1; omega
      _ = Nat.gcd k (n - k) := gcd_add_left k (n - k)
      _ = Nat.gcd (n - k) k := Nat.gcd_comm _ _
      _ = Nat.gcd ((n - k) + k) k := (gcd_add_left (n - k) k).symm
      _ = Nat.gcd n k := by congr 1; omega

/-- **Equation (relation).**  `M(n,k) = n·f(k/n) - gcd(n,k)`. -/
theorem relation {n k : ℕ} (hn : 0 < n) (hk : k ≤ n) :
    ((algCost n k : ℕ) : ℝ) + ((Nat.gcd n k : ℕ) : ℝ)
      = (n : ℝ) * fCost ((k : ℝ) / (n : ℝ)) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  set j := min k (n - k) with hj
  have hj2 : 2 * j ≤ n := by omega
  have hcost : cost n j + Nat.gcd n j = n + 2 * remSum n j := cost_add_gcd j n
  have hcostR : ((cost n j : ℕ) : ℝ) + ((Nat.gcd n j : ℕ) : ℝ)
      = (n : ℝ) + 2 * ((remSum n j : ℕ) : ℝ) := by exact_mod_cast hcost
  have hpsi : (n : ℝ) * psi ((j : ℝ) / (n : ℝ)) = 2 * (remSum n j : ℝ) := psi_rat j n hn hj2
  rw [fCost, min_self_sub hn hk, ← hj]
  have halg : algCost n k = cost n j := rfl
  have hgcd : Nat.gcd n j = Nat.gcd n k := gcd_min_self_sub hk
  rw [halg, ← hgcd]
  rw [mul_add, mul_one, hpsi]
  linarith [hcostR]

/-! ## Theorem 7: continuity at the irrationals

`In` and `Out` are continuous wherever `1/x` is not an integer, and `In`
preserves irrationality.  So each partial sum of the series is continuous at an
irrational point, and the uniform convergence transfers continuity to `ψ`. -/

theorem irrational_ne_zero {x : ℝ} (h : Irrational x) : x ≠ 0 := by
  intro hx
  exact Irrational.ne_int h 0 (by simp [hx])

theorem irrational_one_div {x : ℝ} (h : Irrational x) : Irrational (1 / x) := by
  rw [one_div]
  exact Irrational.inv h

theorem irrational_fract {x : ℝ} (h : Irrational x) : Irrational (Int.fract x) := by
  rw [Int.fract]
  exact Irrational.sub_intCast h _

/-- **`In` preserves irrationality.** -/
theorem irrational_Inn {x : ℝ} (h : Irrational x) : Irrational (Inn x) := by
  have hx0 : x ≠ 0 := irrational_ne_zero h
  have hg : Irrational (Int.fract (1 / x)) := irrational_fract (irrational_one_div h)
  have hgnn : (0 : ℝ) ≤ Int.fract (1 / x) := Int.fract_nonneg _
  have hglt : Int.fract (1 / x) < 1 := Int.fract_lt_one _
  unfold Inn
  rw [if_neg hx0]
  rintro ⟨q, hq⟩
  -- `g/(1+g) = q` forces `g = q/(1-q)`, which is rational
  have hden : (0 : ℝ) < 1 + Int.fract (1 / x) := by linarith
  have hqlt : (q : ℝ) < 1 := by
    rw [hq, div_lt_one hden]
    linarith
  have hq1 : (1 : ℝ) - (q : ℝ) ≠ 0 := by linarith
  refine hg ⟨q / (1 - q), ?_⟩
  have hmul : (q : ℝ) * (1 + Int.fract (1 / x)) = Int.fract (1 / x) := by
    rw [hq]
    field_simp
  push_cast
  rw [div_eq_iff (by exact_mod_cast hq1)]
  linarith [hmul]

theorem iterate_Inn_irrational {x : ℝ} (h : Irrational x) (m : ℕ) :
    Irrational (Inn^[m] x) := by
  induction m with
  | zero => exact h
  | succ j ih => rw [Function.iterate_succ_apply']; exact irrational_Inn ih

theorem continuousAt_Inn {x : ℝ} (h : Irrational x) : ContinuousAt Inn x := by
  have hx0 : x ≠ 0 := irrational_ne_zero h
  have hne : 1 / x ≠ ((⌊1 / x⌋ : ℤ) : ℝ) := Irrational.ne_int (irrational_one_div h) _
  have hcinv : ContinuousAt (fun y : ℝ => 1 / y) x := continuousAt_const.div continuousAt_id hx0
  have hcomp : ContinuousAt (fun y : ℝ => Int.fract (1 / y)) x :=
    (continuousAt_fract hne).comp hcinv
  have hgnn : (0 : ℝ) ≤ Int.fract (1 / x) := Int.fract_nonneg _
  have hden : (1 : ℝ) + Int.fract (1 / x) ≠ 0 := by positivity
  have hform : ContinuousAt
      (fun y : ℝ => Int.fract (1 / y) / (1 + Int.fract (1 / y))) x :=
    hcomp.div (continuousAt_const.add hcomp) hden
  refine hform.congr ?_
  filter_upwards [isOpen_ne.mem_nhds hx0] with y hy
  unfold Inn
  rw [if_neg hy]

theorem continuousAt_Outt {x : ℝ} (h : Irrational x) : ContinuousAt Outt x := by
  have hx0 : x ≠ 0 := irrational_ne_zero h
  have hne : 1 / x ≠ ((⌊1 / x⌋ : ℤ) : ℝ) := Irrational.ne_int (irrational_one_div h) _
  have hcinv : ContinuousAt (fun y : ℝ => 1 / y) x := continuousAt_const.div continuousAt_id hx0
  have hcomp : ContinuousAt (fun y : ℝ => Int.fract (1 / y)) x :=
    (continuousAt_fract hne).comp hcinv
  have hform : ContinuousAt (fun y : ℝ => y * (1 + Int.fract (1 / y))) x :=
    continuousAt_id.mul (continuousAt_const.add hcomp)
  refine hform.congr ?_
  filter_upwards [isOpen_ne.mem_nhds hx0] with y hy
  unfold Outt
  rw [if_neg hy]

theorem continuousAt_iterate_Inn {x : ℝ} (h : Irrational x) (m : ℕ) :
    ContinuousAt (fun y => Inn^[m] y) x := by
  induction m with
  | zero => exact continuousAt_id
  | succ j ih =>
    have hj : ContinuousAt Inn (Inn^[j] x) := continuousAt_Inn (iterate_Inn_irrational h j)
    have heq : (fun y => Inn^[j + 1] y) = (fun y => Inn (Inn^[j] y)) := by
      funext y
      rw [Function.iterate_succ_apply']
    rw [heq]
    exact hj.comp ih

theorem continuousAt_prod_Outt {x : ℝ} (h : Irrational x) (i : ℕ) :
    ContinuousAt (fun y => ∏ m ∈ Finset.range i, Outt (Inn^[m] y)) x := by
  induction i with
  | zero => simpa using continuousAt_const
  | succ j ih =>
    have heq : (fun y => ∏ m ∈ Finset.range (j + 1), Outt (Inn^[m] y))
        = (fun y => (∏ m ∈ Finset.range j, Outt (Inn^[m] y)) * Outt (Inn^[j] y)) := by
      funext y
      rw [Finset.prod_range_succ]
    rw [heq]
    exact ih.mul ((continuousAt_Outt (iterate_Inn_irrational h j)).comp
      (continuousAt_iterate_Inn h j))

theorem continuousAt_psiTerm {x : ℝ} (h : Irrational x) (i : ℕ) :
    ContinuousAt (fun y => psiTerm y i) x := by
  unfold psiTerm
  exact (continuousAt_const.mul (continuousAt_prod_Outt h i)).mul (continuousAt_iterate_Inn h i)

/-- The partial sums of the series for `ψ`. -/
noncomputable def psiPartial (N : ℕ) (x : ℝ) : ℝ := ∑ i ∈ Finset.range N, psiTerm x i

/-! ### The sharp bound `ψ ≤ 2`

The paper's Observation `μ(N,ℓ,β) ≤ 3N` says the algorithm never uses more than
three moves per element, i.e. `ψ ≤ 2`.  The series bound `∑ (2/3)ⁱ = 3` only
gives `ψ ≤ 3`; the sharp value comes from the recursion, since
`x + Out(x) = 2x + 1 - x⌊1/x⌋ ≤ 1` exactly because `⌊1/x⌋ ≥ 2` on `[0,1/2]`. -/

theorem psiTerm_succ (x : ℝ) (i : ℕ) : psiTerm x (i + 1) = Outt x * psiTerm (Inn x) i := by
  unfold psiTerm
  rw [Finset.prod_range_succ']
  have hit : ∀ m : ℕ, Inn^[m] (Inn x) = Inn^[m + 1] x := by
    intro m
    rw [← Function.iterate_succ_apply]
  have hprod : ∏ m ∈ Finset.range i, Outt (Inn^[m] (Inn x))
      = ∏ m ∈ Finset.range i, Outt (Inn^[m + 1] x) :=
    Finset.prod_congr rfl fun m _ => by rw [hit]
  rw [hprod, hit i, Function.iterate_zero_apply]
  ring

/-- **`x + Out(x) ≤ 1` on `[0,1/2]`.** -/
theorem add_Outt_le_one {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) : x + Outt x ≤ 1 := by
  unfold Outt
  split_ifs with h
  · rw [h]; norm_num
  · have hx0' : 0 < x := lt_of_le_of_ne hx0 (Ne.symm h)
    have h2 : (2 : ℝ) ≤ 1 / x := by
      rw [le_div_iff₀ hx0']
      linarith
    have hm2 : (2 : ℝ) ≤ ((⌊1 / x⌋ : ℤ) : ℝ) := by
      have : (2 : ℤ) ≤ ⌊1 / x⌋ := Int.le_floor.2 (by exact_mod_cast h2)
      exact_mod_cast this
    have heq : x * (1 + Int.fract (1 / x)) = 1 + x - ((⌊1 / x⌋ : ℤ) : ℝ) * x := by
      rw [Int.fract]
      field_simp
      ring
    rw [heq]
    nlinarith

/-- **`ψ_N ≤ 2` for every partial sum**, by induction along the recursion. -/
theorem psiPartial_le_two : ∀ (N : ℕ) {x : ℝ}, 0 ≤ x → x ≤ 1 / 2 → psiPartial N x ≤ 2 := by
  intro N
  induction N with
  | zero =>
    intro x _ _
    simp [psiPartial]
  | succ M ih =>
    intro x hx0 hx
    have hIn0 : 0 ≤ Inn x := Inn_nonneg x
    have hIn : Inn x ≤ 1 / 2 := le_of_lt (Inn_lt_half x)
    have hrec : psiPartial (M + 1) x = 2 * x + Outt x * psiPartial M (Inn x) := by
      rw [psiPartial, psiPartial, Finset.sum_range_succ']
      have h0 : psiTerm x 0 = 2 * x := by
        unfold psiTerm
        simp
      rw [h0, Finset.sum_congr rfl (fun i (_ : i ∈ Finset.range M) => psiTerm_succ x i),
        ← Finset.mul_sum]
      ring
    have hIH := ih hIn0 hIn
    have hOut : 0 ≤ Outt x := Outt_nonneg hx0
    have hkey := add_Outt_le_one hx0 hx
    rw [hrec]
    nlinarith

/-- **`ψ ≤ 2`**, the paper's `μ(N,ℓ) ≤ 3N` in relative form. -/
theorem psi_le_two {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) : psi x ≤ 2 := by
  refine Real.tsum_le_of_sum_le (psiTerm_nonneg hx0 hx) fun s => ?_
  obtain ⟨N, hN⟩ : ∃ N, s ⊆ Finset.range N :=
    ⟨s.sup id + 1, fun i hi => Finset.mem_range.2 (by
      have := Finset.le_sup (f := id) hi
      simp only [id] at this
      omega)⟩
  calc ∑ i ∈ s, psiTerm x i ≤ ∑ i ∈ Finset.range N, psiTerm x i :=
        Finset.sum_le_sum_of_subset_of_nonneg hN (fun i _ _ => psiTerm_nonneg hx0 hx i)
    _ ≤ 2 := psiPartial_le_two N hx0 hx

/-- **`f ≤ 3`:** the algorithm uses at most three moves per element. -/
theorem fCost_le_three {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1) : fCost x ≤ 3 := by
  have hm0 : 0 ≤ min x (1 - x) := le_min hx0 (by linarith)
  have hm : min x (1 - x) ≤ 1 / 2 := by
    rcases le_total x (1 - x) with h | h
    · rw [min_eq_left h]; linarith
    · rw [min_eq_right h]; linarith
  unfold fCost
  linarith [psi_le_two hm0 hm]

theorem continuousAt_psiPartial {x : ℝ} (h : Irrational x) (N : ℕ) :
    ContinuousAt (psiPartial N) x := by
  induction N with
  | zero =>
    have h0 : psiPartial 0 = fun _ : ℝ => (0 : ℝ) := by
      funext y
      simp [psiPartial]
    rw [h0]
    exact continuousAt_const
  | succ j ih =>
    have heq : psiPartial (j + 1) = fun y => psiPartial j y + psiTerm y j := by
      funext y
      rw [psiPartial, psiPartial, Finset.sum_range_succ]
    rw [heq]
    exact ih.add (continuousAt_psiTerm h j)

/-- The tail bound: `|ψ - ψ_N| ≤ 3·(2/3)^N` uniformly on `[0,1/2]`. -/
theorem psi_sub_partial_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) (N : ℕ) :
    |psi x - psiPartial N x| ≤ 3 * (2 / 3 : ℝ) ^ N := by
  have hs := psi_summable hx0 hx
  have hsplit : psiPartial N x + ∑' i, psiTerm x (i + N) = psi x := by
    rw [psiPartial, psi]
    exact hs.sum_add_tsum_nat_add N
  have hshift : Summable (fun i => psiTerm x (i + N)) := (summable_nat_add_iff N).2 hs
  have hgeo : Summable (fun i : ℕ => (2 / 3 : ℝ) ^ (i + N)) := by
    exact (summable_nat_add_iff N).2 (summable_geometric_of_lt_one (by norm_num) (by norm_num))
  have hnn : 0 ≤ ∑' i, psiTerm x (i + N) :=
    tsum_nonneg fun i => psiTerm_nonneg hx0 hx _
  have hub : ∑' i, psiTerm x (i + N) ≤ ∑' i : ℕ, (2 / 3 : ℝ) ^ (i + N) :=
    hshift.tsum_le_tsum (fun i => psiTerm_le hx0 hx _) hgeo
  have hval : ∑' i : ℕ, (2 / 3 : ℝ) ^ (i + N) = 3 * (2 / 3 : ℝ) ^ N := by
    have : ∀ i : ℕ, (2 / 3 : ℝ) ^ (i + N) = (2 / 3 : ℝ) ^ N * (2 / 3 : ℝ) ^ i := by
      intro i; rw [pow_add]; ring
    rw [tsum_congr this, tsum_mul_left,
      tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
    ring
  rw [abs_le]
  constructor <;> linarith [hval ▸ hub, hnn, hsplit]

/-- **Theorem 7.**  `ψ` is continuous at every irrational point of `(0,1/2)`. -/
theorem continuousAt_psi {x : ℝ} (hirr : Irrational x) (hx0 : 0 < x) (hx : x < 1 / 2) :
    ContinuousAt psi x := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (by positivity : (0 : ℝ) < ε / 9)
    (by norm_num : (2 / 3 : ℝ) < 1)
  have hcont := continuousAt_psiPartial hirr N
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ := hcont (ε / 3) (by linarith)
  refine ⟨min δ₁ (min x (1 / 2 - x)), by positivity, fun y hy => ?_⟩
  have hy1 : dist y x < δ₁ := lt_of_lt_of_le hy (min_le_left _ _)
  have hy2 : dist y x < x := lt_of_lt_of_le hy (le_trans (min_le_right _ _) (min_le_left _ _))
  have hy3 : dist y x < 1 / 2 - x :=
    lt_of_lt_of_le hy (le_trans (min_le_right _ _) (min_le_right _ _))
  rw [Real.dist_eq, abs_lt] at hy2 hy3
  have hyy0 : (0 : ℝ) ≤ y := by linarith [hy2.1]
  have hyy : y ≤ 1 / 2 := by linarith [hy3.2]
  have hA := psi_sub_partial_le hyy0 hyy N
  have hB := psi_sub_partial_le (le_of_lt hx0) (le_of_lt hx) N
  have hC : dist (psiPartial N y) (psiPartial N x) < ε / 3 := hδ₁' hy1
  rw [Real.dist_eq] at hC ⊢
  have hsplit : psi y - psi x = (psi y - psiPartial N y)
      + (psiPartial N y - psiPartial N x) + (psiPartial N x - psi x) := by ring
  have habs : |psi y - psi x| ≤ |psi y - psiPartial N y| + |psiPartial N y - psiPartial N x|
      + |psiPartial N x - psi x| := by
    have t1 := abs_add_le (psi y - psiPartial N y) (psiPartial N y - psiPartial N x)
    have t2 := abs_add_le ((psi y - psiPartial N y) + (psiPartial N y - psiPartial N x))
      (psiPartial N x - psi x)
    rw [hsplit]
    linarith
  have hB' : |psiPartial N x - psi x| = |psi x - psiPartial N x| := abs_sub_comm _ _
  have hpow : (3 : ℝ) * (2 / 3 : ℝ) ^ N < ε / 3 := by linarith
  linarith [habs, hA, hB, hC, hB', hpow]

/-- **`f` is continuous at every irrational point of `(0,1)`.** -/
theorem continuousAt_fCost {x : ℝ} (hirr : Irrational x) (hx0 : 0 < x) (hx : x < 1) :
    ContinuousAt fCost x := by
  have hne : x ≠ 1 / 2 := by
    intro h
    exact Irrational.ne_rat hirr (1 / 2) (by rw [h]; norm_num)
  have hmin : min x (1 - x) < 1 / 2 := by
    rcases lt_or_gt_of_ne hne with h | h
    · rw [min_eq_left (by linarith)]; exact h
    · rw [min_eq_right (by linarith)]; linarith
  have hmin0 : 0 < min x (1 - x) := by
    rw [lt_min_iff]
    exact ⟨hx0, by linarith⟩
  have hmirr : Irrational (min x (1 - x)) := by
    rcases le_total x (1 - x) with h | h
    · rw [min_eq_left h]; exact hirr
    · rw [min_eq_right h]
      have h1 : Irrational (x - 1) := by
        have := Irrational.sub_intCast hirr 1
        simpa using this
      have h2 : (1 : ℝ) - x = -(x - 1) := by ring
      rw [h2]
      exact Irrational.neg h1
  have hc : ContinuousAt (fun y : ℝ => min y (1 - y)) x :=
    continuousAt_id.min (continuousAt_const.sub continuousAt_id)
  have hcomp : ContinuousAt (fun y : ℝ => psi (min y (1 - y))) x :=
    ContinuousAt.comp (g := psi) (continuousAt_psi hmirr hmin0 hmin) hc
  unfold fCost
  exact continuousAt_const.add hcomp

/-! ## Integrability

`f` is bounded and continuous off a countable set, so it is integrable. -/

open MeasureTheory
open scoped ENNReal

/-- `f` cut down to `[0,1]`, so that it is globally bounded. -/
noncomputable def fBar (x : ℝ) : ℝ := if 0 ≤ x ∧ x ≤ 1 then fCost x else 1

theorem fCost_bounds {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1) : 1 ≤ fCost x ∧ fCost x ≤ 4 := by
  have hm0 : 0 ≤ min x (1 - x) := le_min hx0 (by linarith)
  have hm : min x (1 - x) ≤ 1 / 2 := by
    rcases le_total x (1 - x) with h | h
    · rw [min_eq_left h]; linarith
    · rw [min_eq_right h]; linarith
  constructor
  · unfold fCost; linarith [psi_nonneg hm0 hm]
  · unfold fCost; linarith [psi_le_three hm0 hm]

theorem fBar_bounds (x : ℝ) : 1 ≤ fBar x ∧ fBar x ≤ 4 := by
  unfold fBar
  split_ifs with h
  · exact fCost_bounds h.1 h.2
  · constructor <;> norm_num

theorem abs_fBar_le (x : ℝ) : |fBar x| ≤ 4 := by
  obtain ⟨h1, h2⟩ := fBar_bounds x
  rw [abs_le]
  constructor <;> linarith

theorem fBar_eq_fCost {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1) : fBar x = fCost x := by
  unfold fBar; rw [if_pos ⟨hx0, hx⟩]

theorem continuousAt_fBar {x : ℝ} (hirr : Irrational x) : ContinuousAt fBar x := by
  have hconst : ContinuousAt (fun _ : ℝ => (1 : ℝ)) x := continuousAt_const
  rcases lt_trichotomy x 0 with h | h | h
  · refine hconst.congr ?_
    filter_upwards [Iio_mem_nhds h] with y hy
    unfold fBar
    rw [if_neg (by simp only [not_and, not_le]; intro hc; linarith [Set.mem_Iio.1 hy])]
  · exact absurd h (irrational_ne_zero hirr)
  · rcases lt_trichotomy x 1 with h1 | h1 | h1
    · refine ContinuousAt.congr (continuousAt_fCost hirr h h1) ?_
      filter_upwards [Ioo_mem_nhds h h1] with y hy
      rw [fBar_eq_fCost (le_of_lt (Set.mem_Ioo.1 hy).1) (le_of_lt (Set.mem_Ioo.1 hy).2)]
    · exfalso
      have hx1 : x ≠ ((1 : ℤ) : ℝ) := Irrational.ne_int hirr 1
      simp only [Int.cast_one] at hx1
      exact hx1 h1
    · refine hconst.congr ?_
      filter_upwards [Ioi_mem_nhds h1] with y hy
      unfold fBar
      rw [if_neg (by simp only [not_and, not_le]; intro _; linarith [Set.mem_Ioi.1 hy])]

theorem ae_irrational : ∀ᵐ x : ℝ, Irrational x := by
  have hc : (Set.range ((↑) : ℚ → ℝ)).Countable := Set.countable_range _
  have h0 : volume (Set.range ((↑) : ℚ → ℝ)) = 0 := hc.measure_zero _
  rw [Filter.eventually_iff, mem_ae_iff]
  refine measure_mono_null (fun x hx => ?_) h0
  by_contra hcon
  exact hx hcon

theorem ae_continuousAt_fBar : ∀ᵐ x : ℝ, ContinuousAt fBar x :=
  ae_irrational.mono fun x hx => continuousAt_fBar hx

theorem fBar_aestronglyMeasurable : AEStronglyMeasurable fBar volume := by
  have hset : MeasurableSet {x : ℝ | ContinuousAt fBar x} := measurableSet_of_continuousAt fBar
  have hcont : ContinuousOn fBar {x : ℝ | ContinuousAt fBar x} :=
    continuousOn_of_forall_continuousAt fun _ h => h
  have h1 : AEStronglyMeasurable fBar (volume.restrict {x : ℝ | ContinuousAt fBar x}) :=
    hcont.aestronglyMeasurable hset
  have h2 : volume.restrict {x : ℝ | ContinuousAt fBar x} = volume :=
    Measure.restrict_eq_self_of_ae_mem ae_continuousAt_fBar
  rwa [h2] at h1

/-! ## Theorem 7, second half: Riemann integrability

The paper's Theorem 7 concludes that `f` is *Riemann integrable*.  In Mathlib
that is `BoxIntegral.HasIntegral I IntegrationParams.Riemann`, i.e. convergence
of the tagged-partition sums over all subdivisions whose mesh is below a
constant threshold.  The Riemann–Lebesgue criterion
`BoxIntegral.AEContinuous.hasBoxIntegral` supplies it from boundedness and a.e.
continuity, and identifies the value with the Lebesgue integral. -/

open BoxIntegral

/-- The unit box `[0,1]`, as a box in `Fin 1 → ℝ`. -/
def unitBox : Box (Fin 1) := ⟨fun _ => 0, fun _ => 1, fun _ => by norm_num⟩

/-- `f` as a function of one coordinate. -/
noncomputable def FBar (v : Fin 1 → ℝ) : ℝ := fBar (v 0)

theorem coe_unitBox : (unitBox : Set (Fin 1 → ℝ)) = (fun v : Fin 1 → ℝ => v 0) ⁻¹' Set.Ioc 0 1 := by
  ext v
  rw [Box.mem_coe, Box.mem_def]
  constructor
  · intro h; exact h 0
  · intro h i
    have : i = 0 := Subsingleton.elim _ _
    rw [this]; exact h

theorem measurePreserving_eval :
    MeasureTheory.MeasurePreserving (fun v : Fin 1 → ℝ => v 0) volume volume := by
  have h := MeasureTheory.volume_preserving_funUnique (Fin 1) ℝ
  exact h

theorem ae_continuousAt_FBar :
    ∀ᵐ v : Fin 1 → ℝ, ContinuousAt FBar v := by
  have hmeas : MeasurableSet {x : ℝ | ¬ Irrational x} := by
    have : {x : ℝ | ¬ Irrational x} = Set.range ((↑) : ℚ → ℝ) := by
      ext x
      simp only [Set.mem_setOf_eq, Irrational, not_not]
    rw [this]
    exact (Set.countable_range _).measurableSet
  have hnull : volume {x : ℝ | ¬ Irrational x} = 0 := by
    have := ae_irrational
    rw [Filter.eventually_iff, mem_ae_iff] at this
    exact this
  have hpre : volume ((fun v : Fin 1 → ℝ => v 0) ⁻¹' {x : ℝ | ¬ Irrational x}) = 0 := by
    rw [measurePreserving_eval.measure_preimage hmeas.nullMeasurableSet]
    exact hnull
  rw [Filter.eventually_iff, mem_ae_iff]
  refine measure_mono_null (fun v hv => ?_) hpre
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hv ⊢
  intro hirr
  exact hv (ContinuousAt.comp (g := fBar) (f := fun w : Fin 1 → ℝ => w 0)
    (continuousAt_fBar hirr) (continuous_apply (0 : Fin 1)).continuousAt)

set_option maxHeartbeats 1000000 in
-- The Riemann-Lebesgue criterion carries a large elaboration burden.
/-- **Theorem 7, second half.**  `f` is Riemann integrable on `[0,1]`, with
Riemann integral equal to its Lebesgue integral. -/
theorem fBar_hasBoxIntegral :
    HasIntegral unitBox IntegrationParams.Riemann FBar
      (BoxAdditiveMap.toSMul (MeasureTheory.Measure.toBoxAdditive volume))
      (∫ v in (unitBox : Set (Fin 1 → ℝ)), FBar v) := by
  refine AEContinuous.hasBoxIntegral (volume : MeasureTheory.Measure (Fin 1 → ℝ))
    ⟨4, fun x _ => ?_⟩ ae_continuousAt_FBar IntegrationParams.Riemann
  rw [Real.norm_eq_abs]
  exact abs_fBar_le _

/-- The Riemann integral of `f` over the unit box is `∫₀¹ f`. -/
theorem integral_unitBox :
    ∫ v in (unitBox : Set (Fin 1 → ℝ)), FBar v = ∫ x in (0 : ℝ)..1, fBar x := by
  rw [coe_unitBox, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact measurePreserving_eval.setIntegral_preimage_emb
    (MeasurableEquiv.funUnique (Fin 1) ℝ).measurableEmbedding fBar _

/-! ### Instantiating Riemann integrability at the evenly spaced subdivision -/

/-- The boxes of the uniform subdivision of `[0,1]` are indexed by `0,…,n-1`. -/
theorem admissibleIndex_unitBox (n : ℕ) [NeZero n] :
    unitPartition.admissibleIndex n unitBox
      = (Finset.range n).image (fun j : ℕ => (fun _ : Fin 1 => (j : ℤ))) := by
  have hn : 0 < n := Nat.pos_of_neZero n
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  ext ν
  rw [unitPartition.mem_admissibleIndex_iff, Box.le_iff_bounds, Finset.mem_image]
  simp only [unitPartition.box_lower, unitPartition.box_upper, unitBox, Pi.le_def]
  constructor
  · rintro ⟨hl, hu⟩
    have h1 : (0 : ℝ) ≤ (ν 0 : ℝ) / (n : ℝ) := hl 0
    have h2 : ((ν 0 : ℝ) + 1) / (n : ℝ) ≤ 1 := hu 0
    rw [le_div_iff₀ hnR, zero_mul] at h1
    rw [div_le_one hnR] at h2
    have h1' : (0 : ℤ) ≤ ν 0 := by exact_mod_cast h1
    have h2' : ν 0 + 1 ≤ (n : ℤ) := by exact_mod_cast h2
    refine ⟨(ν 0).toNat, Finset.mem_range.2 (by omega), ?_⟩
    funext i
    have : i = 0 := Subsingleton.elim _ _
    rw [this]
    omega
  · rintro ⟨j, hj, rfl⟩
    rw [Finset.mem_range] at hj
    have hjR : (j : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hj
    constructor
    · intro i; positivity
    · intro i
      rw [div_le_one hnR]
      push_cast
      linarith

/-- The integral sum of the uniform subdivision is the evenly spaced Riemann sum. -/
theorem integralSum_prepartition (n : ℕ) [NeZero n] :
    integralSum FBar (BoxAdditiveMap.toSMul (MeasureTheory.Measure.toBoxAdditive volume))
        (unitPartition.prepartition n unitBox)
      = (∑ j ∈ Finset.range n, fBar (((j : ℝ) + 1) / (n : ℝ))) / (n : ℝ) := by
  classical
  have hn : 0 < n := Nat.pos_of_neZero n
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [integralSum]
  have hboxes : (unitPartition.prepartition n unitBox).boxes
      = Finset.image (fun ν => unitPartition.box n ν) (unitPartition.admissibleIndex n unitBox) :=
    rfl
  rw [hboxes, Finset.sum_image (fun x _ y _ h => unitPartition.box_injective n h),
    admissibleIndex_unitBox n,
    Finset.sum_image (fun x hx y hy h => by
      have := congrFun h (0 : Fin 1)
      simpa using this)]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hν : (fun _ : Fin 1 => (j : ℤ)) ∈ unitPartition.admissibleIndex n unitBox := by
    rw [admissibleIndex_unitBox n]
    exact Finset.mem_image.2 ⟨j, hj, rfl⟩
  rw [unitPartition.prepartition_tag n hν]
  have hvol : (MeasureTheory.Measure.toBoxAdditive volume)
      (unitPartition.box n (fun _ : Fin 1 => (j : ℤ))) = 1 / (n : ℝ) := by
    rw [MeasureTheory.Measure.toBoxAdditive_apply, MeasureTheory.measureReal_def,
      unitPartition.volume_box]
    simp
  rw [BoxAdditiveMap.toSMul_apply, hvol]
  have htag : FBar (unitPartition.tag n (fun _ : Fin 1 => (j : ℤ)))
      = fBar (((j : ℝ) + 1) / (n : ℝ)) := by
    rw [FBar, unitPartition.tag_apply]
    push_cast
    ring_nf
  rw [htag, smul_eq_mul]
  ring

theorem unitBox_hasIntegralVertices : hasIntegralVertices unitBox :=
  ⟨fun _ => 0, fun _ => 1, fun _ => by simp [unitBox], fun _ => by simp [unitBox]⟩

theorem fBar_zero : fBar 0 = 1 := by
  rw [fBar_eq_fCost (le_refl 0) (by norm_num), fCost]
  norm_num [psi_zero]

theorem fBar_one : fBar 1 = 1 := by
  rw [fBar_eq_fCost (by norm_num) (le_refl 1), fCost]
  norm_num [psi_zero]

theorem sum_shift_eq {n : ℕ} (hn : 0 < n) :
    ∑ j ∈ Finset.range n, fBar (((j : ℝ) + 1) / (n : ℝ))
      = ∑ k ∈ Finset.range n, fBar ((k : ℝ) / (n : ℝ)) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hcast : ∀ j : ℕ, (((j + 1 : ℕ) : ℝ)) / (n : ℝ) = ((j : ℝ) + 1) / (n : ℝ) := by
    intro j; push_cast; ring
  have h := Finset.sum_range_succ' (fun k : ℕ => fBar ((k : ℝ) / (n : ℝ))) n
  have h2 := Finset.sum_range_succ (fun k : ℕ => fBar ((k : ℝ) / (n : ℝ))) n
  have h0 : fBar (((0 : ℕ) : ℝ) / (n : ℝ)) = 1 := by norm_num [fBar_zero]
  have h1 : fBar (((n : ℕ) : ℝ) / (n : ℝ)) = 1 := by
    rw [div_self (ne_of_gt hnR)]; exact fBar_one
  rw [h0] at h
  rw [h1] at h2
  have hleft : ∑ j ∈ Finset.range n, fBar ((((j + 1 : ℕ)) : ℝ) / (n : ℝ))
      = ∑ j ∈ Finset.range n, fBar (((j : ℝ) + 1) / (n : ℝ)) :=
    Finset.sum_congr rfl fun j _ => by rw [hcast j]
  rw [← hleft]
  linarith [h, h2]

/-- **The evenly spaced Riemann sums converge**, by instantiating Riemann
integrability at the uniform subdivision. -/
theorem tendsto_riemann_fBar :
    Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n, fBar ((k : ℝ) / (n : ℝ))) / (n : ℝ))
      atTop (𝓝 (∫ x in (0 : ℝ)..1, fBar x)) := by
  rw [← integral_unitBox]
  refine Metric.tendsto_atTop.mpr fun ε hε => ?_
  obtain ⟨r, hr₁, hr₂⟩ := (hasIntegral_iff.mp fBar_hasBoxIntegral) (ε / 2) (half_pos hε)
  refine ⟨max 1 ⌈((r 0 0 : ℝ))⁻¹⌉₊, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_left _ _) hn
  have hn0 : 0 < n := hn1
  have : NeZero n := ⟨by omega⟩
  rw [← sum_shift_eq hn0, ← integralSum_prepartition n]
  refine lt_of_le_of_lt (hr₂ 0 _ ⟨?_, fun _ => ?_, fun h => ?_, fun h => ?_⟩
    (unitPartition.prepartition_isPartition _ unitBox_hasIntegralVertices))
    (half_lt_self_iff.mpr hε)
  · rw [show r 0 = fun _ => r 0 0 from funext_iff.mpr (hr₁ 0 rfl)]
    apply unitPartition.prepartition_isSubordinate n unitBox
    rw [one_div, inv_le_comm₀ (by exact_mod_cast hn0) (r 0 0).prop]
    exact le_trans (Nat.le_ceil _) (Nat.cast_le.mpr (le_trans (le_max_right _ _) hn))
  · exact unitPartition.prepartition_isHenstock n unitBox
  · simp only [IntegrationParams.Riemann, Bool.false_eq_true] at h
  · simp only [IntegrationParams.Riemann, Bool.false_eq_true] at h

/-! ## The `gcd` term is negligible -/

theorem sum_gcd_range_le {n : ℕ} (hn : 0 < n) :
    ∑ k ∈ Finset.range n, Nat.gcd n k ≤ n + 2 * (n * n.divisors.card) := by
  have hsplit : ∑ k ∈ Finset.range n, Nat.gcd n k
      = Nat.gcd n 0 + ∑ k ∈ Finset.Ico 1 n, Nat.gcd n k := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hn]
  have hmin : ∀ k ∈ Finset.Ico 1 n, Nat.gcd n k = Nat.gcd n (min k (n - k)) := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    exact (gcd_min_self_sub (le_of_lt hk.2)).symm
  have hdouble := sum_min_eq hn (fun j => Nat.gcd n j)
  have hle : ∑ k ∈ Finset.Ico 1 n, Nat.gcd n (min k (n - k))
      ≤ 2 * ∑ j ∈ allShifts n, Nat.gcd n j := by
    rw [← hdouble]
    exact Nat.le_add_right _ _
  have hall := sum_gcd_le hn
  rw [hsplit, Finset.sum_congr rfl hmin, Nat.gcd_zero_right]
  have : 2 * ∑ j ∈ allShifts n, Nat.gcd n j ≤ 2 * (n * n.divisors.card) :=
    Nat.mul_le_mul_left 2 hall
  omega

theorem tendsto_divisors_div : Tendsto (fun n : ℕ => (n.divisors.card : ℝ) / (n : ℝ))
    atTop (𝓝 0) := by
  obtain ⟨C, hC, hCd⟩ := exists_card_divisors_le (show (0 : ℝ) < 1 / 2 by norm_num)
  have hlim : Tendsto (fun n : ℕ => C / (n : ℝ) ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
    refine Filter.Tendsto.const_div_atTop ?_ C
    exact (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  refine squeeze_zero' (Filter.Eventually.of_forall fun n => by positivity) ?_ hlim
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h1 := hCd n hn.ne'
  have hpow : (n : ℝ) = (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add hnR]
    norm_num
  have hp : (0 : ℝ) < (n : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hnR _
  rw [div_le_div_iff₀ hnR hp]
  nlinarith [h1, hp, hpow]

/-! ## Theorem 9 -/

theorem avgCost_eq_riemann {n : ℕ} (hn : 0 < n) :
    avgCost n / (n : ℝ)
      = (∑ k ∈ Finset.range n, fBar ((k : ℝ) / (n : ℝ))) / (n : ℝ)
        - ((∑ k ∈ Finset.range n, Nat.gcd n k : ℕ) : ℝ) / (n : ℝ) ^ 2 := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hterm : ∀ k ∈ Finset.range n,
      ((algCost n k : ℕ) : ℝ)
        = (n : ℝ) * fBar ((k : ℝ) / (n : ℝ)) - ((Nat.gcd n k : ℕ) : ℝ) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hkn : k ≤ n := le_of_lt hk
    have hk0 : (0 : ℝ) ≤ (k : ℝ) / (n : ℝ) := by positivity
    have hk1 : (k : ℝ) / (n : ℝ) ≤ 1 := by
      rw [div_le_one hnR]
      exact_mod_cast hkn
    rw [fBar_eq_fCost hk0 hk1]
    linarith [relation hn hkn]
  rw [avgCost, Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Nat.cast_sum]
  field_simp

/-- **Theorem 9.**  `avgCost n / n → ∫₀¹ f`. -/
theorem theorem9_unit :
    Tendsto (fun n : ℕ => avgCost n / (n : ℝ)) atTop (𝓝 (∫ x in (0 : ℝ)..1, fBar x)) := by
  have hgcd : Tendsto
      (fun n : ℕ => ((∑ k ∈ Finset.range n, Nat.gcd n k : ℕ) : ℝ) / (n : ℝ) ^ 2)
      atTop (𝓝 0) := by
    have hlim : Tendsto (fun n : ℕ => 1 / (n : ℝ) + 2 * ((n.divisors.card : ℝ) / (n : ℝ)))
        atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) :=
        tendsto_one_div_atTop_nhds_zero_nat
      have h2 : Tendsto (fun n : ℕ => 2 * ((n.divisors.card : ℝ) / (n : ℝ))) atTop (𝓝 (2 * 0)) :=
        tendsto_divisors_div.const_mul 2
      rw [mul_zero] at h2
      have h3 := h1.add h2
      rw [add_zero] at h3
      exact h3
    refine squeeze_zero' (Filter.Eventually.of_forall fun n => by positivity) ?_ hlim
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hb : ((∑ k ∈ Finset.range n, Nat.gcd n k : ℕ) : ℝ)
        ≤ (n : ℝ) + 2 * ((n : ℝ) * (n.divisors.card : ℝ)) := by
      have := sum_gcd_range_le hn
      exact_mod_cast this
    rw [div_le_iff₀ (by positivity)]
    have hexp : (1 / (n : ℝ) + 2 * ((n.divisors.card : ℝ) / (n : ℝ))) * (n : ℝ) ^ 2
        = (n : ℝ) + 2 * ((n : ℝ) * (n.divisors.card : ℝ)) := by
      field_simp
    rw [hexp]
    exact hb
  have hcomb := tendsto_riemann_fBar.sub hgcd
  rw [sub_zero] at hcomb
  refine hcomb.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact (avgCost_eq_riemann hn).symm

/-! ## The paper's form: `2∫₀^{1/2} f` -/

theorem intervalIntegrable_fBar (a b : ℝ) : IntervalIntegrable fBar volume a b := by
  constructor <;>
    exact Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne
      fBar_aestronglyMeasurable (M := 4)
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact abs_fBar_le _)

theorem uIoc_subset_Icc {a b : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) :
    ∀ x ∈ Set.uIoc a b, 0 ≤ x ∧ x ≤ 1 := by
  intro x hx
  rw [Set.uIoc, Set.mem_Ioc] at hx
  constructor
  · exact le_of_lt (lt_of_le_of_lt (le_inf ha hb) hx.1)
  · exact le_trans hx.2 (sup_le ha1 hb1)

theorem intervalIntegrable_fCost {a b : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b)
    (hb1 : b ≤ 1) : IntervalIntegrable fCost volume a b := by
  refine (intervalIntegrable_fBar a b).congr ?_
  intro x hx
  obtain ⟨h0, h1⟩ := uIoc_subset_Icc ha ha1 hb hb1 x hx
  exact fBar_eq_fCost h0 h1

theorem integral_fBar_eq_fCost {a b : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) :
    ∫ x in a..b, fBar x = ∫ x in a..b, fCost x := by
  refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun x hx => ?_)
  obtain ⟨h0, h1⟩ := uIoc_subset_Icc ha ha1 hb hb1 x hx
  exact fBar_eq_fCost h0 h1

/-- **`f(1-x) = f(x)`.**  This is `M(n,k) = M(n,n-k)` in relative form. -/
theorem fCost_symm (x : ℝ) : fCost (1 - x) = fCost x := by
  unfold fCost
  congr 2
  rw [show (1 : ℝ) - (1 - x) = x by ring, min_comm]

/-- **`∫₀¹ f = 2∫₀^{1/2} f`.** -/
theorem integral_fCost_split :
    ∫ x in (0 : ℝ)..1, fCost x = 2 * ∫ x in (0 : ℝ)..(1 / 2), fCost x := by
  have hI1 : IntervalIntegrable fCost volume 0 (1 / 2) :=
    intervalIntegrable_fCost (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hI2 : IntervalIntegrable fCost volume (1 / 2) 1 :=
    intervalIntegrable_fCost (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hadd := intervalIntegral.integral_add_adjacent_intervals hI1 hI2
  have hrefl : ∫ x in (1 / 2 : ℝ)..1, fCost x = ∫ x in (0 : ℝ)..(1 / 2), fCost x := by
    have hsub := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := 1 / 2)
      (d := (1 : ℝ)) fCost
    have hsym : ∫ x in (0 : ℝ)..(1 / 2), fCost (1 - x) = ∫ x in (0 : ℝ)..(1 / 2), fCost x :=
      intervalIntegral.integral_congr (fun x _ => fCost_symm x)
    rw [hsym] at hsub
    norm_num at hsub
    exact hsub.symm
  rw [← hadd, hrefl]
  ring

/-- **Theorem 9.**  `avgCost n / n → 2∫₀^{1/2} f`. -/
theorem theorem9 :
    Tendsto (fun n : ℕ => avgCost n / (n : ℝ)) atTop
      (𝓝 (2 * ∫ x in (0 : ℝ)..(1 / 2), fCost x)) := by
  have h := theorem9_unit
  rw [integral_fBar_eq_fCost (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    integral_fCost_split] at h
  exact h

/-! ## Higher moments

The corollary after Theorem 7: if `X` is uniform on `[0,1/2]` then the `j`-th
moment of `f(X)` is `(∫₀^{1/2} f^j)/(1/2)`, and moments of all orders exist.

Existence is Theorem 7 again: `f^j` is bounded by `4^j` and continuous wherever
`f` is, so it is Riemann integrable by the same criterion.  The formula is the
normalisation of the uniform measure, which here is `2 • volume` restricted to
`(0,1/2]` — the measure with constant density `2` on `[0,1/2]`. -/

theorem abs_fBar_pow_le (j : ℕ) (x : ℝ) : |fBar x ^ j| ≤ 4 ^ j := by
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_fBar_le x) j

theorem ae_continuousAt_FBar_pow (j : ℕ) :
    ∀ᵐ v : Fin 1 → ℝ, ContinuousAt (fun w : Fin 1 → ℝ => FBar w ^ j) v :=
  ae_continuousAt_FBar.mono fun v hv => hv.pow j

set_option maxHeartbeats 1000000 in
-- The Riemann-Lebesgue criterion carries a large elaboration burden.
/-- **`f^j` is Riemann integrable**, so the `j`-th moment exists. -/
theorem fBar_pow_hasBoxIntegral (j : ℕ) :
    HasIntegral unitBox IntegrationParams.Riemann (fun v : Fin 1 → ℝ => FBar v ^ j)
      (BoxAdditiveMap.toSMul (MeasureTheory.Measure.toBoxAdditive volume))
      (∫ v in (unitBox : Set (Fin 1 → ℝ)), FBar v ^ j) := by
  refine AEContinuous.hasBoxIntegral (volume : MeasureTheory.Measure (Fin 1 → ℝ))
    ⟨4 ^ j, fun x _ => ?_⟩ (ae_continuousAt_FBar_pow j) IntegrationParams.Riemann
  rw [Real.norm_eq_abs, FBar]
  exact abs_fBar_pow_le j _

/-- **The uniform distribution on `[0,1/2]`**: density `2` there, zero elsewhere. -/
noncomputable def unifHalf : Measure ℝ := (2 : ℝ≥0∞) • volume.restrict (Set.Ioc 0 (1 / 2))

instance isProbabilityMeasure_unifHalf : IsProbabilityMeasure unifHalf := by
  constructor
  rw [unifHalf, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, Real.volume_Ioc, smul_eq_mul]
  rw [show (1 : ℝ) / 2 - 0 = 1 / 2 by ring]
  rw [show ENNReal.ofReal (1 / 2 : ℝ) = 1 / 2 by
    rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one, ENNReal.ofReal_ofNat]]
  rw [ENNReal.mul_div_cancel'] <;> norm_num

theorem ae_mem_unifHalf : ∀ᵐ x ∂unifHalf, x ∈ Set.Ioc (0 : ℝ) (1 / 2) := by
  rw [unifHalf]
  exact Measure.ae_smul_measure (MeasureTheory.ae_restrict_mem measurableSet_Ioc) 2

/-- Integration against the uniform measure is `2·∫₀^{1/2}`. -/
theorem integral_unifHalf (g : ℝ → ℝ) :
    ∫ x, g x ∂unifHalf = 2 * ∫ x in (0 : ℝ)..(1 / 2), g x := by
  rw [unifHalf, MeasureTheory.integral_smul_measure,
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  simp

theorem fCost_pow_ae_eq (j : ℕ) :
    (fun x => fCost x ^ j) =ᵐ[unifHalf] (fun x => fBar x ^ j) := by
  filter_upwards [ae_mem_unifHalf] with x hx
  rw [fBar_eq_fCost (le_of_lt hx.1) (by linarith [hx.2])]

/-- **Moments of all orders exist.** -/
theorem integrable_fCost_pow (j : ℕ) : Integrable (fun x => fCost x ^ j) unifHalf := by
  refine Integrable.congr ?_ (fCost_pow_ae_eq j).symm
  have hmble : AEStronglyMeasurable (fun x => fBar x ^ j) unifHalf := by
    rw [unifHalf]
    exact AEStronglyMeasurable.smul_measure
      (AEStronglyMeasurable.pow (AEStronglyMeasurable.restrict fBar_aestronglyMeasurable) j) 2
  rw [← MeasureTheory.integrableOn_univ]
  refine Measure.integrableOn_of_bounded ?_ hmble (M := 4 ^ j) ?_
  · exact measure_ne_top unifHalf Set.univ
  · exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact abs_fBar_pow_le j x

/-- **The corollary.**  For `X` uniform on `[0,1/2]`, the `j`-th moment of
`f(X)` is `(∫₀^{1/2} f^j)/(1/2)`. -/
theorem moment_fCost (j : ℕ) :
    ∫ x, fCost x ^ j ∂unifHalf = (∫ x in (0 : ℝ)..(1 / 2), fCost x ^ j) / (1 / 2) := by
  rw [integral_unifHalf]
  ring

/-- The first moment is the constant of Theorem 9. -/
theorem moment_one : ∫ x, fCost x ^ 1 ∂unifHalf = 2 * ∫ x in (0 : ℝ)..(1 / 2), fCost x := by
  rw [integral_unifHalf]
  simp

end BlockCycleRotation
