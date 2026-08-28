/-
# Theorem 10 and Theorem 8

Theorem 10 states that `avgCost n / n` converges, and identifies the limit as
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
there.  That is Theorem 8's convergence; continuity at irrationals follows
since `In` and `Out` are continuous away from `1/x ∈ ℤ` and preserve
irrationality.
-/

import BlockCycleRotation.Theorem13
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

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

/-! ## Theorem 8: continuity at the irrationals

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

/-- **Theorem 8.**  `ψ` is continuous at every irrational point of `(0,1/2)`. -/
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

/-! ## Riemann sums

Mathlib's `∫` is the Lebesgue integral, so "the Riemann sums converge to the
integral" needs an argument.  The step functions `x ↦ f(⌊nx⌋/n)` converge to `f`
at every point of continuity, hence a.e., and are bounded by `4`, so dominated
convergence applies. -/

/-- The step function is measurable: it factors through `⌊n·x⌋ : ℤ`. -/
theorem measurable_step (n : ℕ) :
    Measurable (fun x : ℝ => fBar (((⌊(n : ℝ) * x⌋ : ℤ) : ℝ) / (n : ℝ))) := by
  have h1 : Measurable (fun x : ℝ => ⌊(n : ℝ) * x⌋) :=
    Int.measurable_floor.comp (measurable_const_mul _)
  exact (measurable_of_countable (fun j : ℤ => fBar ((j : ℝ) / (n : ℝ)))).comp h1

/-- On `[k/n, (k+1)/n)` the step function is the constant `f(k/n)`. -/
theorem step_eq_const {n k : ℕ} (hn : 0 < n) {x : ℝ}
    (h1 : (k : ℝ) / (n : ℝ) ≤ x) (h2 : x < ((k : ℝ) + 1) / (n : ℝ)) :
    ((⌊(n : ℝ) * x⌋ : ℤ) : ℝ) / (n : ℝ) = (k : ℝ) / (n : ℝ) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [div_le_iff₀ hnR] at h1
  rw [lt_div_iff₀ hnR] at h2
  have hfl : ⌊(n : ℝ) * x⌋ = (k : ℤ) := by
    rw [Int.floor_eq_iff]
    constructor
    · push_cast; linarith
    · push_cast; linarith
  rw [hfl]
  push_cast
  ring

/-- The integral of the step function is the Riemann sum. -/
theorem integral_step_eq {n : ℕ} (hn : 0 < n) :
    ∫ x in (0 : ℝ)..1, fBar (((⌊(n : ℝ) * x⌋ : ℤ) : ℝ) / (n : ℝ))
      = (∑ k ∈ Finset.range n, fBar ((k : ℝ) / (n : ℝ))) / (n : ℝ) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hFmeas : Measurable (fun x : ℝ => fBar (((⌊(n : ℝ) * x⌋ : ℤ) : ℝ) / (n : ℝ))) :=
    measurable_step n
  have hcast : ∀ k : ℕ, ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by intro k; push_cast; ring
  have hlt : ∀ k : ℕ, (k : ℝ) / (n : ℝ) < ((k + 1 : ℕ) : ℝ) / (n : ℝ) := by
    intro k
    rw [div_lt_div_iff₀ hnR hnR, hcast]
    nlinarith
  have hae : ∀ k : ℕ, ∀ᵐ x, x ∈ Set.uIoc ((k : ℝ) / (n : ℝ)) (((k + 1 : ℕ) : ℝ) / (n : ℝ)) →
      fBar (((⌊(n : ℝ) * x⌋ : ℤ) : ℝ) / (n : ℝ)) = fBar ((k : ℝ) / (n : ℝ)) := by
    intro k
    filter_upwards [MeasureTheory.compl_mem_ae_iff.2
      (measure_singleton (((k + 1 : ℕ) : ℝ) / (n : ℝ)))] with x hx hmem
    rw [Set.uIoc_of_le (le_of_lt (hlt k)), Set.mem_Ioc] at hmem
    refine congrArg fBar (step_eq_const hn (le_of_lt hmem.1) ?_)
    have h2 : x < ((k + 1 : ℕ) : ℝ) / (n : ℝ) := lt_of_le_of_ne hmem.2 hx
    rwa [hcast k] at h2
  have hint : ∀ k : ℕ, IntervalIntegrable
      (fun x : ℝ => fBar (((⌊(n : ℝ) * x⌋ : ℤ) : ℝ) / (n : ℝ))) volume
      ((k : ℝ) / (n : ℝ)) (((k + 1 : ℕ) : ℝ) / (n : ℝ)) := by
    intro k
    constructor <;>
      exact Measure.integrableOn_of_bounded (measure_Ioc_lt_top).ne
        hFmeas.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact abs_fBar_le _)
  have hpiece : ∀ k : ℕ,
      (∫ x in ((k : ℝ) / (n : ℝ))..(((k + 1 : ℕ) : ℝ) / (n : ℝ)),
        fBar (((⌊(n : ℝ) * x⌋ : ℤ) : ℝ) / (n : ℝ)))
        = fBar ((k : ℝ) / (n : ℝ)) / (n : ℝ) := by
    intro k
    rw [intervalIntegral.integral_congr_ae (hae k), intervalIntegral.integral_const]
    have hdiff : ((k + 1 : ℕ) : ℝ) / (n : ℝ) - (k : ℝ) / (n : ℝ) = 1 / (n : ℝ) := by
      rw [hcast k]; field_simp; ring
    rw [hdiff]
    ring
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun k : ℕ => (k : ℝ) / (n : ℝ))
    (f := fun x : ℝ => fBar (((⌊(n : ℝ) * x⌋ : ℤ) : ℝ) / (n : ℝ))) (n := n) (fun k _ => hint k)
  have ha0 : ((0 : ℕ) : ℝ) / (n : ℝ) = 0 := by simp
  have han : ((n : ℕ) : ℝ) / (n : ℝ) = 1 := by field_simp
  rw [ha0, han] at hsum
  rw [← hsum, Finset.sum_congr rfl (fun k _ => hpiece k), ← Finset.sum_div]

theorem tendsto_floor_div (x : ℝ) :
    Tendsto (fun n : ℕ => ((⌊(n : ℝ) * x⌋ : ℤ) : ℝ) / (n : ℝ)) atTop (𝓝 x) := by
  have h1 : Tendsto (fun n : ℕ => x - 1 / (n : ℝ)) atTop (𝓝 x) := by
    have h : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
    have h2 : Tendsto (fun n : ℕ => x - 1 / (n : ℝ)) atTop (𝓝 (x - 0)) :=
      Filter.Tendsto.sub tendsto_const_nhds h
    rwa [sub_zero] at h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h1 tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    rw [le_div_iff₀ hnR]
    have h := Int.sub_one_lt_floor ((n : ℝ) * x)
    have hexp : (x - 1 / (n : ℝ)) * (n : ℝ) = x * (n : ℝ) - 1 := by field_simp
    rw [hexp]
    nlinarith [h]
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    rw [div_le_iff₀ hnR]
    have h := Int.floor_le ((n : ℝ) * x)
    linarith

theorem tendsto_integral_step :
    Tendsto (fun n : ℕ => ∫ x in (0 : ℝ)..1, fBar (((⌊(n : ℝ) * x⌋ : ℤ) : ℝ) / (n : ℝ)))
      atTop (𝓝 (∫ x in (0 : ℝ)..1, fBar x)) := by
  simp only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  refine MeasureTheory.tendsto_integral_of_dominated_convergence (fun _ => (4 : ℝ))
    (fun n => (measurable_step n).aestronglyMeasurable) ?_ ?_ ?_
  · exact MeasureTheory.integrableOn_const (hs := measure_Ioc_lt_top.ne)
  · intro n
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact abs_fBar_le _
  · filter_upwards [MeasureTheory.ae_restrict_of_ae ae_irrational] with x hx
    exact (continuousAt_fBar hx).tendsto.comp (tendsto_floor_div x)

/-- **The Riemann sums of `f` converge to its integral.** -/
theorem tendsto_riemann_fBar :
    Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n, fBar ((k : ℝ) / (n : ℝ))) / (n : ℝ))
      atTop (𝓝 (∫ x in (0 : ℝ)..1, fBar x)) := by
  refine tendsto_integral_step.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact integral_step_eq hn

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

/-! ## Theorem 10 -/

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

/-- **Theorem 10.**  `avgCost n / n → ∫₀¹ f`. -/
theorem theorem10_unit :
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

/-- **Theorem 10.**  `avgCost n / n → 2∫₀^{1/2} f`. -/
theorem theorem10 :
    Tendsto (fun n : ℕ => avgCost n / (n : ℝ)) atTop
      (𝓝 (2 * ∫ x in (0 : ℝ)..(1 / 2), fCost x)) := by
  have h := theorem10_unit
  rw [integral_fBar_eq_fCost (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    integral_fCost_split] at h
  exact h

end BlockCycleRotation
