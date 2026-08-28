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

end BlockCycleRotation
