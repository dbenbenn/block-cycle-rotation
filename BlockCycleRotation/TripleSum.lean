/-
# The triple sum of section 4

After (eq. heilbron), Blomer--Bux rewrite the lattice point count as a triple
sum.  Ordering the pairs `(x, y)` by `d = gcd(x, y)`, which necessarily
divides `n`, and eliminating `x'` via `x' = n/(d·x) - y·y'/x`, they obtain

```
Q(n) = ∑_{d ∣ n} ∑_{x > y ≥ 1, gcd(x,y) = 1} ∑_{y'} ( n/(d·x) − y·y'/x + d·x )
         + O(n^{1+ε})
```

where `y'` runs over `1 ≤ y' < U` subject to `n/d ≡ y·y' (mod x)`, with
`U = min( n/(d(x+y)), (n/d − d·x²)/y )`.

The innermost sum is a linear function summed over an arithmetic progression —
exactly the shape estimated in `Progression.lean`.  This file records that: the
general estimate applies to the paper's summand verbatim, with

  `A = n/(d·x) + d·x`  and  `B = −y/x`.

What remains for Theorem 14 is the two outer layers — the sum over `x > y ≥ 1`
coprime, and the Möbius-inverted sum over `d ∣ n` — together with collecting the
resulting pieces `G₁ + G₂ + G₃` into `O(n^{3/2+ε})`.  Every ingredient those need
is proved: this estimate, `exists_card_divisors_le`, and Mathlib's Möbius
inversion.
-/

import BlockCycleRotation.Continuant

namespace BlockCycleRotation

open Real

/-- **The inner sum of the triple sum.**

For fixed `d`, `x`, `y`, summing the paper's linear function over an
arithmetic progression modulo `x` differs from its expected value by
`O(log x)`.  This is `sum_ap_sub_main_le_log` at the paper's coefficients. -/
theorem inner_sum_sub_main_le (n d x y : ℕ) (hx : 0 < x) (c : ℤ) (U : ℕ) :
    ‖(∑ x' ∈ Finset.Ico 1 U, if (x : ℤ) ∣ ((x' : ℤ) - c) then
          (((n : ℂ) / (d * x) + d * x) + (-(y : ℂ) / x) * x') else 0)
        - (1 / (x : ℂ)) * ∑ x' ∈ Finset.Ico 1 U,
            (((n : ℂ) / (d * x) + d * x) + (-(y : ℂ) / x) * x')‖
      ≤ (‖((n : ℂ) / (d * x) + d * x)‖ + ‖(-(y : ℂ) / x)‖ * (U - 1 : ℕ))
          * (1 + Real.log x) :=
  sum_ap_sub_main_le_log hx c _ _ U

/-! ## Equation (invquant)

The paper discards the `∑ gcd(n,k)` term of (eq. heilbron) as `O(n^{1+ε})`.
That bound is `∑_{k} gcd(n,k) ≤ n · d(n)`, which the divisor bound turns into
`O(n^{1+ε})`. -/

/-- The shifts of `m` number at most `m`. -/
theorem card_shifts_le (m : ℕ) : (shifts m).card ≤ m := by
  have hsub : shifts m ⊆ Finset.Icc 1 m := by
    intro k hk
    obtain ⟨hkm, hk1, hk2, -⟩ := mem_shifts.1 hk
    exact Finset.mem_Icc.2 ⟨hk1, hkm⟩
  calc (shifts m).card ≤ (Finset.Icc 1 m).card := Finset.card_le_card hsub
    _ = m := by simp

/-- **`∑ gcd(n,k) ≤ n · d(n)`.** -/
theorem sum_gcd_le {n : ℕ} (hn : 0 < n) :
    ∑ k ∈ allShifts n, Nat.gcd n k ≤ n * n.divisors.card := by
  rw [sum_gcd_allShifts hn, Finset.card_eq_sum_ones, Finset.mul_sum]
  refine Finset.sum_le_sum fun g hg => ?_
  obtain ⟨hgn, -⟩ := Nat.mem_divisors.1 hg
  have hmul : g * (n / g) = n := Nat.mul_div_cancel' hgn
  calc g * (shifts (n / g)).card ≤ g * (n / g) := Nat.mul_le_mul_left _ (card_shifts_le _)
    _ = n := hmul
    _ = n * 1 := (Nat.mul_one n).symm

/-- **Equation (invquant).**  The `∑ gcd(n,k)` term of (eq. heilbron) is
`O(n^{1+ε})`, so `∑_{k} remSum n k` and `R(n)` differ by that much. -/
theorem invquant {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
      ((∑ k ∈ allShifts n, remSum n k : ℕ) : ℝ)
          - ((∑ q ∈ quadruplesAll n, q.2.1 : ℕ) : ℝ)
        ≤ C * (n : ℝ) ^ (1 + ε) := by
  obtain ⟨C, hC, hCd⟩ := exists_card_divisors_le hε
  refine ⟨C, hC, fun n hn => ?_⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hdiff := heilbron hn
  have h1 : ((∑ k ∈ allShifts n, Nat.gcd n k : ℕ) : ℝ) ≤ (n : ℝ) * (n.divisors.card : ℝ) := by
    exact_mod_cast sum_gcd_le hn
  have h2 : ((∑ k ∈ allShifts n, remSum n k : ℕ) : ℝ)
      = ((∑ k ∈ allShifts n, Nat.gcd n k : ℕ) : ℝ)
        + ((∑ q ∈ quadruplesAll n, q.2.1 : ℕ) : ℝ) := by exact_mod_cast hdiff
  have h3 : (n : ℝ) * (n.divisors.card : ℝ) ≤ (n : ℝ) * (C * (n : ℝ) ^ ε) :=
    mul_le_mul_of_nonneg_left (hCd n hn.ne') hn'.le
  have hrpow : (n : ℝ) ^ (1 + ε) = (n : ℝ) * (n : ℝ) ^ ε := by
    rw [Real.rpow_add hn', Real.rpow_one]
  rw [hrpow]
  linarith

/-! ## Eliminating `x'`

The paper solves `n = x·x' + y·y'` for `x'`, turning the quadruples into triples
`(x, y, y')`.  The condition `x' > y'` becomes `(x + y)·y' < n`, and `x'` being
an integer becomes `x ∣ n - y·y'` — the congruence `n ≡ y·y' (mod x)`. -/

/-- The triples `(x, y, y')` of the triple sum. -/
def triples (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1)) ×ˢ (Finset.range (n + 1))).filter
    (fun t => 1 ≤ t.2.1 ∧ t.2.1 < t.1 ∧ 1 ≤ t.2.2 ∧ (t.1 + t.2.1) * t.2.2 < n
      ∧ t.1 ∣ (n - t.2.1 * t.2.2))

theorem mem_triples {n x y y' : ℕ} :
    (x, y, y') ∈ triples n ↔
      (x ≤ n ∧ y ≤ n ∧ y' ≤ n) ∧ 1 ≤ y ∧ y < x ∧ 1 ≤ y'
        ∧ (x + y) * y' < n ∧ x ∣ (n - y * y') := by
  simp [triples, Finset.mem_filter, Finset.mem_product, and_assoc]

/-- **The `x'`-elimination.**  `Q(n)` as a sum over triples. -/
theorem sum_snd_quadruplesQ_eq_triples {n : ℕ} (hn : 0 < n) :
    ∑ q ∈ quadruplesQ n, q.2.1 = ∑ t ∈ triples n, (n - t.2.1 * t.2.2) / t.1 := by
  refine Finset.sum_bij'
    (i := fun q _ => (q.1, q.2.2.1, q.2.2.2))
    (j := fun t _ => (t.1, (n - t.2.1 * t.2.2) / t.1, t.2.1, t.2.2)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨x, x', y, y'⟩ hq
    obtain ⟨⟨hab, hbb, hyx', hy'x'⟩, hx1, hx2, hx'1, hx'2, hsum⟩ := mem_quadruplesQ.1 hq
    have hdvd : x ∣ (n - y * y') := ⟨x', by omega⟩
    have hlt : (x + y) * y' < n := by nlinarith
    show (x, y, y') ∈ triples n
    rw [mem_triples]
    exact ⟨⟨hab, hyx', hy'x'⟩, hx1, hx2, hx'1, hlt, hdvd⟩
  · rintro ⟨x, y, y'⟩ ht
    obtain ⟨⟨han, hyn, hy'n⟩, hx1, hx2, hx'1, hlt, hdvd⟩ := mem_triples.1 ht
    have hx : 0 < x := by omega
    have hab : x * ((n - y * y') / x) = n - y * y' := Nat.mul_div_cancel' hdvd
    have hle : y * y' ≤ n := by nlinarith
    have hsum : n = x * ((n - y * y') / x) + y * y' := by omega
    have hbb : y' < (n - y * y') / x := by
      have h1 : x * y' < x * ((n - y * y') / x) := by
        rw [hab]; nlinarith
      exact Nat.lt_of_mul_lt_mul_left h1
    show (x, (n - y * y') / x, y, y') ∈ quadruplesQ n
    rw [mem_quadruplesQ]
    exact ⟨quadruple_le hx1 hx2 hx'1 hbb hsum, hx1, hx2, hx'1, hbb, hsum⟩
  · rintro ⟨x, x', y, y'⟩ hq
    obtain ⟨-, hx1, hx2, hx'1, hx'2, hsum⟩ := mem_quadruplesQ.1 hq
    have hx : 0 < x := by omega
    have h : n - y * y' = x * x' := by omega
    show (x, (n - y * y') / x, y, y') = (x, x', y, y')
    rw [h, Nat.mul_div_cancel_left _ hx]
  · rintro ⟨x, y, y'⟩ _
    rfl
  · rintro ⟨x, x', y, y'⟩ hq
    obtain ⟨-, hx1, hx2, hx'1, hx'2, hsum⟩ := mem_quadruplesQ.1 hq
    have hx : 0 < x := by omega
    have h : n - y * y' = x * x' := by omega
    show x' = (n - y * y') / x
    rw [h, Nat.mul_div_cancel_left _ hx]

/-! ## The triple sum

Combining the divisor layer `Q(n) = ∑_{d ∣ n} R(n/d)` with the `x'`-elimination
applied to each `R(n/d)` gives the paper's triple sum: over divisors `d ∣ n`,
over coprime pairs `x > y ≥ 1`, and over `y'` in an arithmetic progression. -/

/-- The triples with `gcd(x,y) = 1`. -/
def coprimeTriples (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (triples n).filter (fun t => Nat.gcd t.1 t.2.1 = 1)

theorem mem_coprimeTriples {n x y y' : ℕ} :
    (x, y, y') ∈ coprimeTriples n ↔
      ((x ≤ n ∧ y ≤ n ∧ y' ≤ n) ∧ 1 ≤ y ∧ y < x ∧ 1 ≤ y'
        ∧ (x + y) * y' < n ∧ x ∣ (n - y * y')) ∧ Nat.gcd x y = 1 := by
  simp [coprimeTriples, Finset.mem_filter, mem_triples]

/-- The `x'`-elimination for the coprime quadruples. -/
theorem sum_snd_quadruplesAll_eq {n : ℕ} (hn : 0 < n) :
    ∑ q ∈ quadruplesAll n, q.2.1
      = ∑ t ∈ coprimeTriples n, (n - t.2.1 * t.2.2) / t.1 := by
  refine Finset.sum_bij'
    (i := fun q _ => (q.1, q.2.2.1, q.2.2.2))
    (j := fun t _ => (t.1, (n - t.2.1 * t.2.2) / t.1, t.2.1, t.2.2)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨x, x', y, y'⟩ hq
    obtain ⟨⟨hab, hbb, hyx', hy'x'⟩, hx1, hx2, hx'1, hx'2, hgcd, hsum⟩ := mem_quadruplesAll.1 hq
    have hdvd : x ∣ (n - y * y') := ⟨x', by omega⟩
    have hlt : (x + y) * y' < n := by nlinarith
    show (x, y, y') ∈ coprimeTriples n
    rw [mem_coprimeTriples]
    exact ⟨⟨⟨hab, hyx', hy'x'⟩, hx1, hx2, hx'1, hlt, hdvd⟩, hgcd⟩
  · rintro ⟨x, y, y'⟩ ht
    obtain ⟨⟨⟨han, hyn, hy'n⟩, hx1, hx2, hx'1, hlt, hdvd⟩, hgcd⟩ := mem_coprimeTriples.1 ht
    have hx : 0 < x := by omega
    have hab : x * ((n - y * y') / x) = n - y * y' := Nat.mul_div_cancel' hdvd
    have hle : y * y' ≤ n := by nlinarith
    have hsum : n = x * ((n - y * y') / x) + y * y' := by omega
    have hbb : y' < (n - y * y') / x := by
      have h1 : x * y' < x * ((n - y * y') / x) := by rw [hab]; nlinarith
      exact Nat.lt_of_mul_lt_mul_left h1
    show (x, (n - y * y') / x, y, y') ∈ quadruplesAll n
    rw [mem_quadruplesAll]
    exact ⟨quadruple_le hx1 hx2 hx'1 hbb hsum, hx1, hx2, hx'1, hbb, hgcd, hsum⟩
  · rintro ⟨x, x', y, y'⟩ hq
    obtain ⟨-, hx1, hx2, hx'1, hx'2, -, hsum⟩ := mem_quadruplesAll.1 hq
    have hx : 0 < x := by omega
    have h : n - y * y' = x * x' := by omega
    show (x, (n - y * y') / x, y, y') = (x, x', y, y')
    rw [h, Nat.mul_div_cancel_left _ hx]
  · rintro ⟨x, y, y'⟩ _
    rfl
  · rintro ⟨x, x', y, y'⟩ hq
    obtain ⟨-, hx1, hx2, hx'1, hx'2, -, hsum⟩ := mem_quadruplesAll.1 hq
    have hx : 0 < x := by omega
    have h : n - y * y' = x * x' := by omega
    show x' = (n - y * y') / x
    rw [h, Nat.mul_div_cancel_left _ hx]

/-- **The triple sum.**  `Q(n)` as a sum over divisors `d ∣ n`, coprime pairs
`x > y ≥ 1`, and `y'` subject to `(x+y)y' < n/d` and `n/d ≡ y·y' (mod x)`. -/
theorem Q_eq_tripleSum {n : ℕ} (hn : 0 < n) :
    ∑ q ∈ quadruplesQ n, q.2.1
      = ∑ d ∈ n.divisors, ∑ t ∈ coprimeTriples (n / d), (n / d - t.2.1 * t.2.2) / t.1 := by
  rw [sum_snd_quadruplesQ hn]
  refine Finset.sum_congr rfl fun d hd => ?_
  obtain ⟨hdn, -⟩ := Nat.mem_divisors.1 hd
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
  have : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hn hdn) hd0
  exact sum_snd_quadruplesAll_eq this

/-! ## The congruence is an arithmetic progression

The triple sum's divisibility condition `x ∣ m - y·y'` is, because
`gcd(x,y) = 1`, a condition on `y'` modulo `x` — the shape the estimate of
`Progression.lean` requires.  This produces the residue `c` explicitly from
Bézout. -/

/-- With `gcd(x,y) = 1`, the congruence `x ∣ m - y·y'` is `y' ≡ c (mod x)` for
a residue `c` depending only on `x`, `y` and `m`. -/
theorem exists_residue {x y m : ℕ} (hgcd : Nat.gcd x y = 1) :
    ∃ c : ℤ, ∀ x' : ℤ, ((x : ℤ) ∣ ((m : ℤ) - y * x')) ↔ ((x : ℤ) ∣ (x' - c)) := by
  have hco : IsCoprime (x : ℤ) (y : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa using hgcd
  obtain ⟨u, v, huv⟩ := id hco
  -- `u * x + v * y = 1`, so `v * m` inverts `y` against `m`
  refine ⟨v * m, fun x' => ?_⟩
  have hkey : (m : ℤ) - y * x' = ((m : ℤ) - y * (v * m)) - y * (x' - v * m) := by ring
  have hdvd1 : (x : ℤ) ∣ ((m : ℤ) - y * (v * m)) := by
    refine ⟨u * m, ?_⟩
    have : (y : ℤ) * (v * m) = (1 - u * x) * m := by
      rw [← huv]; ring
    rw [this]; ring
  constructor
  · intro h
    rw [hkey] at h
    have h2 : (x : ℤ) ∣ (y : ℤ) * (x' - v * m) := (dvd_sub_right hdvd1).1 h
    exact IsCoprime.dvd_of_dvd_mul_left hco h2
  · intro h
    rw [hkey]
    exact dvd_sub hdvd1 (Dvd.dvd.mul_left h _)

/-- **The inner sum of the triple sum, as an arithmetic-progression sum.**

The natural-number inner sum `∑ (m - y·y')/x`, taken over `y'` satisfying the
divisibility condition, is the real sum of the linear function
`m/x - (y/x)·y'` over an arithmetic progression modulo `x` — the exact shape
`sum_ap_sub_main_le_log` estimates. -/
theorem inner_sum_nat_eq {m x y : ℕ} (hx : 0 < x) (hgcd : Nat.gcd x y = 1) :
    ∃ c : ℤ, ∀ U : ℕ, (∀ y' ∈ Finset.Ico 1 U, y * y' ≤ m) →
      ((∑ y' ∈ (Finset.Ico 1 U).filter (fun y' => x ∣ (m - y * y')),
          (m - y * y') / x : ℕ) : ℝ)
        = ∑ y' ∈ Finset.Ico 1 U,
            (if (x : ℤ) ∣ ((y' : ℤ) - c) then ((m : ℝ) / x - (y : ℝ) / x * y') else 0) := by
  obtain ⟨c, hc⟩ := exists_residue (m := m) hgcd
  refine ⟨c, fun U hU => ?_⟩
  rw [Finset.sum_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun y' hy' => ?_
  have hle : y * y' ≤ m := hU y' hy'
  -- the two divisibility conditions agree
  have hiff : (x ∣ (m - y * y')) ↔ ((x : ℤ) ∣ ((y' : ℤ) - c)) := by
    rw [← hc (y' : ℤ)]
    constructor
    · intro h
      have : ((x : ℤ)) ∣ (((m - y * y' : ℕ)) : ℤ) := Int.natCast_dvd_natCast.2 h
      rwa [Nat.cast_sub hle, Nat.cast_mul] at this
    · intro h
      have h2 : ((x : ℤ)) ∣ (((m - y * y' : ℕ)) : ℤ) := by
        rwa [Nat.cast_sub hle, Nat.cast_mul]
      exact Int.natCast_dvd_natCast.1 h2
  by_cases hd : x ∣ (m - y * y')
  · rw [if_pos hd, if_pos (hiff.1 hd)]
    have hmul : x * ((m - y * y') / x) = m - y * y' := Nat.mul_div_cancel' hd
    have hreal : ((x : ℝ)) * (((m - y * y') / x : ℕ) : ℝ) = (m : ℝ) - (y : ℝ) * y' := by
      have := congrArg (Nat.cast : ℕ → ℝ) hmul
      push_cast [Nat.cast_sub hle] at this
      linarith
    have hane : ((x : ℝ)) ≠ 0 := by positivity
    field_simp at hreal ⊢
    linarith
  · rw [if_neg hd, if_neg (fun h => hd (hiff.2 h))]
    simp

/-! ## Decomposing the triple sum by pairs

The triples split as a pair `(x, y)` together with `y'` ranging over an initial
segment cut by `(x + y)·y' < m` and filtered by the divisibility condition.
After this the innermost sum is literally the arithmetic-progression sum of
`inner_sum_nat_eq`. -/

/-- The bound on `y'` for a given pair. -/
def bBound (m x y : ℕ) : ℕ := (m - 1) / (x + y) + 1

theorem mem_bRange {m x y y' : ℕ} (hm : 0 < m) (hx : 0 < x + y) :
    y' ∈ Finset.Ico 1 (bBound m x y) ↔ 1 ≤ y' ∧ (x + y) * y' < m := by
  rw [Finset.mem_Ico, bBound, Nat.lt_succ_iff, Nat.le_div_iff_mul_le hx,
    Nat.mul_comm y' (x + y)]
  omega

/-- The coprime pairs `x > y ≥ 1`. -/
def coprimePairs (m : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (m + 1)) ×ˢ (Finset.range (m + 1))).filter
    (fun p => 1 ≤ p.2 ∧ p.2 < p.1 ∧ Nat.gcd p.1 p.2 = 1)

theorem mem_coprimePairs {m x y : ℕ} :
    (x, y) ∈ coprimePairs m ↔ (x ≤ m ∧ y ≤ m) ∧ 1 ≤ y ∧ y < x ∧ Nat.gcd x y = 1 := by
  simp [coprimePairs, Finset.mem_filter, Finset.mem_product, and_assoc]

/-- **The triple sum, decomposed by pairs.** -/
theorem coprimeTriples_decompose {m : ℕ} (hm : 0 < m) (f : ℕ → ℕ → ℕ → ℕ) :
    ∑ t ∈ coprimeTriples m, f t.1 t.2.1 t.2.2
      = ∑ p ∈ coprimePairs m, ∑ y' ∈ (Finset.Ico 1 (bBound m p.1 p.2)).filter
          (fun y' => p.1 ∣ (m - p.2 * y')), f p.1 p.2 y' := by
  rw [Finset.sum_sigma']
  refine Finset.sum_bij'
    (i := fun t _ => (⟨(t.1, t.2.1), t.2.2⟩ : (_ : ℕ × ℕ) × ℕ))
    (j := fun p _ => (p.1.1, p.1.2, p.2)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨x, y, y'⟩ ht
    obtain ⟨⟨⟨han, hyn, hy'n⟩, hx1, hx2, hx'1, hlt, hdvd⟩, hgcd⟩ := mem_coprimeTriples.1 ht
    have hx : 0 < x + y := by omega
    simp only [Finset.mem_sigma, Finset.mem_filter]
    exact ⟨mem_coprimePairs.2 ⟨⟨han, hyn⟩, hx1, hx2, hgcd⟩,
      (mem_bRange hm hx).2 ⟨hx'1, hlt⟩, hdvd⟩
  · rintro ⟨⟨x, y⟩, y'⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_filter] at hp
    obtain ⟨hpair, hx', hdvd⟩ := hp
    obtain ⟨⟨han, hyn⟩, hx1, hx2, hgcd⟩ := mem_coprimePairs.1 hpair
    have hx : 0 < x + y := by omega
    obtain ⟨hx'1, hlt⟩ := (mem_bRange hm hx).1 hx'
    have hy'n : y' ≤ m := by nlinarith
    show (x, y, y') ∈ coprimeTriples m
    rw [mem_coprimeTriples]
    exact ⟨⟨⟨han, hyn, hy'n⟩, hx1, hx2, hx'1, hlt, hdvd⟩, hgcd⟩
  · rintro ⟨x, y, y'⟩ _
    rfl
  · rintro ⟨⟨x, y⟩, y'⟩ _
    rfl
  · rintro ⟨x, y, y'⟩ _
    rfl

/-- **The triple sum in estimable form.**

`Q(n)` as a sum over divisors `d ∣ n`, coprime pairs `(x, y)`, and `y'` in an
initial segment filtered by the divisibility condition.  By `inner_sum_nat_eq`
the innermost sum is an arithmetic-progression sum of a linear function, which
`inner_sum_sub_main_le` estimates. -/
theorem Q_eq_tripleSum_decomposed {n : ℕ} (hn : 0 < n) :
    ∑ q ∈ quadruplesQ n, q.2.1
      = ∑ d ∈ n.divisors, ∑ p ∈ coprimePairs (n / d),
          ∑ y' ∈ (Finset.Ico 1 (bBound (n / d) p.1 p.2)).filter
            (fun y' => p.1 ∣ (n / d - p.2 * y')), (n / d - p.2 * y') / p.1 := by
  rw [Q_eq_tripleSum hn]
  refine Finset.sum_congr rfl fun d hd => ?_
  obtain ⟨hdn, -⟩ := Nat.mem_divisors.1 hd
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
  have hm : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hn hdn) hd0
  exact coprimeTriples_decompose hm (fun x y y' => (n / d - y * y') / x)

/-! ## Symmetrisation

Following the paper: `Q(n) = ½ ∑ (x' + x)`, and the involution swapping the two
halves pairs the quadruples with `x' > x` against those with `x' < x`, leaving the
diagonal `x = x'`.  So

  `Q(n) = ∑_{x' > x} (x + x') + ∑_{x = x'} x`,

exactly (the diagonal term is what the paper discards as `O(n^{1+ε})`).  The
restriction `x' > x` is what will bound `x` by about `√n` in the estimates. -/

/-- `quadruplesQ` is symmetric under swapping the two halves. -/
theorem mem_quadruplesQ_swap {n x x' y y' : ℕ} (h : (x, x', y, y') ∈ quadruplesQ n) :
    (x', x, y', y) ∈ quadruplesQ n := by
  rw [mem_quadruplesQ] at h ⊢
  obtain ⟨⟨h1, h2, h3, h4⟩, h5, h6, h7, h8, h9⟩ := h
  exact ⟨⟨h2, h1, h4, h3⟩, h7, h8, h5, h6, by rw [h9]; ring⟩

/-- Summing `x` over `quadruplesQ` equals summing `x'`. -/
theorem sum_fst_eq_sum_snd_Q (n : ℕ) :
    ∑ q ∈ quadruplesQ n, q.1 = ∑ q ∈ quadruplesQ n, q.2.1 := by
  refine Finset.sum_bij'
    (i := fun q _ => (q.2.1, q.1, q.2.2.2, q.2.2.1))
    (j := fun q _ => (q.2.1, q.1, q.2.2.2, q.2.2.1)) ?_ ?_ ?_ ?_ ?_ <;>
    rintro ⟨x, x', y, y'⟩ hq
  · exact mem_quadruplesQ_swap hq
  · exact mem_quadruplesQ_swap hq
  · rfl
  · rfl
  · rfl

/-- The involution matches the quadruples with `x' < x` against those with `x' > x`. -/
theorem sum_gt_eq_sum_lt (n : ℕ) :
    ∑ q ∈ (quadruplesQ n).filter (fun q => q.2.1 < q.1), (q.1 + q.2.1)
      = ∑ q ∈ (quadruplesQ n).filter (fun q => q.1 < q.2.1), (q.1 + q.2.1) := by
  refine Finset.sum_bij'
    (i := fun q _ => (q.2.1, q.1, q.2.2.2, q.2.2.1))
    (j := fun q _ => (q.2.1, q.1, q.2.2.2, q.2.2.1)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨x, x', y, y'⟩ hq
    simp only [Finset.mem_filter] at hq ⊢
    exact ⟨mem_quadruplesQ_swap hq.1, hq.2⟩
  · rintro ⟨x, x', y, y'⟩ hq
    simp only [Finset.mem_filter] at hq ⊢
    exact ⟨mem_quadruplesQ_swap hq.1, hq.2⟩
  · rintro ⟨x, x', y, y'⟩ _
    rfl
  · rintro ⟨x, x', y, y'⟩ _
    rfl
  · rintro ⟨x, x', y, y'⟩ _
    exact Nat.add_comm _ _

/-- **The symmetrisation.**  `Q(n)` splits into the part with `x' > x` and the
diagonal. -/
theorem Q_symmetrise (n : ℕ) :
    ∑ q ∈ quadruplesQ n, q.2.1
      = (∑ q ∈ (quadruplesQ n).filter (fun q => q.1 < q.2.1), (q.1 + q.2.1))
        + ∑ q ∈ (quadruplesQ n).filter (fun q => q.1 = q.2.1), q.1 := by
  classical
  have e1 : ((quadruplesQ n).filter (fun q => ¬ q.1 < q.2.1)).filter (fun q => q.2.1 < q.1)
      = (quadruplesQ n).filter (fun q => q.2.1 < q.1) := by
    ext q
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hq, -⟩, h⟩
      exact ⟨hq, h⟩
    · rintro ⟨hq, h⟩
      exact ⟨⟨hq, by omega⟩, h⟩
  have e2 : ((quadruplesQ n).filter (fun q => ¬ q.1 < q.2.1)).filter (fun q => ¬ q.2.1 < q.1)
      = (quadruplesQ n).filter (fun q => q.1 = q.2.1) := by
    ext q
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hq, h1⟩, h2⟩
      exact ⟨hq, by omega⟩
    · rintro ⟨hq, h⟩
      exact ⟨⟨hq, by omega⟩, by omega⟩
  have hsplit : ∑ q ∈ quadruplesQ n, (q.1 + q.2.1)
      = (∑ q ∈ (quadruplesQ n).filter (fun q => q.1 < q.2.1), (q.1 + q.2.1))
        + ((∑ q ∈ (quadruplesQ n).filter (fun q => q.2.1 < q.1), (q.1 + q.2.1))
          + ∑ q ∈ (quadruplesQ n).filter (fun q => q.1 = q.2.1), (q.1 + q.2.1)) := by
    rw [← Finset.sum_filter_add_sum_filter_not (quadruplesQ n) (fun q => q.1 < q.2.1),
      ← Finset.sum_filter_add_sum_filter_not
        ((quadruplesQ n).filter (fun q => ¬ q.1 < q.2.1)) (fun q => q.2.1 < q.1),
      e1, e2]
  have hab : ∑ q ∈ quadruplesQ n, (q.1 + q.2.1) = 2 * ∑ q ∈ quadruplesQ n, q.2.1 := by
    rw [Finset.sum_add_distrib, sum_fst_eq_sum_snd_Q]
    ring
  have hdiag : ∑ q ∈ (quadruplesQ n).filter (fun q => q.1 = q.2.1), (q.1 + q.2.1)
      = 2 * ∑ q ∈ (quadruplesQ n).filter (fun q => q.1 = q.2.1), q.1 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q hq => ?_
    simp only [Finset.mem_filter] at hq
    omega
  rw [hab, hdiag, sum_gt_eq_sum_lt] at hsplit
  omega

/-! ## The diagonal is `O(n^{1+ε})`

On the diagonal `x = x'` we have `n = x² + y·y'`, so `x ≤ √n` and `y` divides
`n - x²`; the quadruple is determined by `(x, y)`.  Counting gives
`√n · ∑_{x ≤ √n} d(n - x²)`, which the divisor bound makes `O(n^{1+ε})`. -/

theorem diag_card_le {n : ℕ} (hn : 0 < n) :
    ((quadruplesQ n).filter (fun q => q.1 = q.2.1)).card
      ≤ ∑ x ∈ Finset.range (Nat.sqrt n + 1), (n - x * x).divisors.card := by
  rw [← Finset.card_sigma]
  refine Finset.card_le_card_of_injOn
    (fun q => (⟨q.1, q.2.2.1⟩ : (_ : ℕ) × ℕ)) ?_ ?_
  · rintro ⟨x, x', y, y'⟩ hq
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hq
    obtain ⟨hmem, hab⟩ := hq
    obtain ⟨-, hx1, hx2, hx'1, hx'2, hsum⟩ := mem_quadruplesQ.1 hmem
    have hba : x' = x := hab.symm
    subst hba
    have hbb : 1 ≤ y * y' := Nat.one_le_iff_ne_zero.2 (by positivity)
    have hlt : x' * x' < n := by omega
    have hsq : x' ≤ Nat.sqrt n := Nat.le_sqrt.2 (by omega)
    have hdvd : y ∣ n - x' * x' := ⟨y', by omega⟩
    have hne : n - x' * x' ≠ 0 := by omega
    simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_range, Nat.mem_divisors]
    exact ⟨Nat.lt_succ_of_le hsq, hdvd, hne⟩
  · rintro ⟨x, x', y, y'⟩ hq ⟨c, e, c', e'⟩ hr heq
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hq hr
    obtain ⟨hmem, hab⟩ := hq
    obtain ⟨hmem2, hce⟩ := hr
    obtain ⟨-, hx1, hx2, hx'1, hx'2, hsum⟩ := mem_quadruplesQ.1 hmem
    obtain ⟨-, hc1, hc2, he1, he2, hsum2⟩ := mem_quadruplesQ.1 hmem2
    simp only [Sigma.mk.injEq] at heq
    obtain ⟨h1, h2⟩ := heq
    subst h1
    have h2' : y = c' := eq_of_heq h2
    subst h2'
    have hx' : x' = x := hab.symm
    have he : e = x := hce.symm
    subst hx'
    subst he
    have : y * y' = y * e' := by omega
    have : y' = e' := Nat.eq_of_mul_eq_mul_left (by omega) this
    subst this
    rfl

theorem sum_diag_le {n : ℕ} (hn : 0 < n) :
    ∑ q ∈ (quadruplesQ n).filter (fun q => q.1 = q.2.1), q.1
      ≤ Nat.sqrt n * ∑ x ∈ Finset.range (Nat.sqrt n + 1), (n - x * x).divisors.card := by
  have hterm : ∀ q ∈ (quadruplesQ n).filter (fun q => q.1 = q.2.1), q.1 ≤ Nat.sqrt n := by
    rintro ⟨x, x', y, y'⟩ hq
    simp only [Finset.mem_filter] at hq
    obtain ⟨hmem, hab⟩ := hq
    obtain ⟨-, hx1, hx2, hx'1, hx'2, hsum⟩ := mem_quadruplesQ.1 hmem
    have hba : x' = x := hab.symm
    subst hba
    have hbb : 1 ≤ y * y' := Nat.one_le_iff_ne_zero.2 (by positivity)
    have hsq : x' ≤ Nat.sqrt n := Nat.le_sqrt.2 (by omega)
    exact hsq
  calc ∑ q ∈ (quadruplesQ n).filter (fun q => q.1 = q.2.1), q.1
      ≤ ∑ _q ∈ (quadruplesQ n).filter (fun q => q.1 = q.2.1), Nat.sqrt n :=
        Finset.sum_le_sum hterm
    _ = ((quadruplesQ n).filter (fun q => q.1 = q.2.1)).card * Nat.sqrt n := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ (∑ x ∈ Finset.range (Nat.sqrt n + 1), (n - x * x).divisors.card) * Nat.sqrt n :=
        Nat.mul_le_mul_right _ (diag_card_le hn)
    _ = Nat.sqrt n * _ := Nat.mul_comm _ _

/-- **The diagonal is `O(n^{1+ε})`.**  This is the term the paper discards
after symmetrising. -/
theorem sum_diag_isBigO {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
      ((∑ q ∈ (quadruplesQ n).filter (fun q => q.1 = q.2.1), q.1 : ℕ) : ℝ)
        ≤ C * (n : ℝ) ^ (1 + ε) := by
  obtain ⟨C0, hC0, hCd⟩ := exists_card_divisors_le hε
  refine ⟨2 * C0, by positivity, fun n hn => ?_⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hnε : (0 : ℝ) ≤ (n : ℝ) ^ ε := by positivity
  -- each divisor count is at most `C₀ n^ε`
  have hterm : ∀ x ∈ Finset.range (Nat.sqrt n + 1),
      (((n - x * x).divisors.card : ℕ) : ℝ) ≤ C0 * (n : ℝ) ^ ε := by
    intro x _
    rcases Nat.eq_zero_or_pos (n - x * x) with h0 | h0
    · rw [h0]
      simp
      positivity
    · refine (hCd _ h0.ne').trans ?_
      have hle : ((n - x * x : ℕ) : ℝ) ≤ (n : ℝ) := by
        have : (n - x * x : ℕ) ≤ n := Nat.sub_le _ _
        exact_mod_cast this
      have := Real.rpow_le_rpow (by positivity) hle hε.le
      nlinarith
  have hS : ((∑ x ∈ Finset.range (Nat.sqrt n + 1), (n - x * x).divisors.card : ℕ) : ℝ)
      ≤ ((Nat.sqrt n : ℝ) + 1) * (C0 * (n : ℝ) ^ ε) := by
    push_cast
    calc ∑ x ∈ Finset.range (Nat.sqrt n + 1), (((n - x * x).divisors.card : ℕ) : ℝ)
        ≤ ∑ _x ∈ Finset.range (Nat.sqrt n + 1), C0 * (n : ℝ) ^ ε :=
          Finset.sum_le_sum hterm
      _ = ((Nat.sqrt n : ℝ) + 1) * (C0 * (n : ℝ) ^ ε) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  -- the natural-number bound
  have hnat := sum_diag_le hn
  have hcast : ((∑ q ∈ (quadruplesQ n).filter (fun q => q.1 = q.2.1), q.1 : ℕ) : ℝ)
      ≤ (Nat.sqrt n : ℝ)
        * ((∑ x ∈ Finset.range (Nat.sqrt n + 1), (n - x * x).divisors.card : ℕ) : ℝ) := by
    exact_mod_cast hnat
  -- `√n · (√n + 1) ≤ 2n`
  have hsq1 : (Nat.sqrt n : ℝ) * (Nat.sqrt n : ℝ) ≤ (n : ℝ) := by
    have h : Nat.sqrt n * Nat.sqrt n ≤ n := by
      have h2 := Nat.sqrt_le' n
      rwa [pow_two] at h2
    exact_mod_cast h
  have hsq2 : (Nat.sqrt n : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast Nat.sqrt_le_self n
  have hsqnn : (0 : ℝ) ≤ (Nat.sqrt n : ℝ) := by positivity
  have hrpow : (n : ℝ) ^ (1 + ε) = (n : ℝ) * (n : ℝ) ^ ε := by
    rw [Real.rpow_add hn', Real.rpow_one]
  rw [hrpow]
  have hmid : (Nat.sqrt n : ℝ)
      * ((∑ x ∈ Finset.range (Nat.sqrt n + 1), (n - x * x).divisors.card : ℕ) : ℝ)
      ≤ (Nat.sqrt n : ℝ) * (((Nat.sqrt n : ℝ) + 1) * (C0 * (n : ℝ) ^ ε)) :=
    mul_le_mul_of_nonneg_left hS hsqnn
  nlinarith [hcast, hmid, hsq1, hsq2, hnε, hC0.le]

/-! ## Carrying `x' > x` through the classification

Classifying the symmetrised sum by `d = gcd(x,y)` turns the restriction
`x' > x` into the paper's `x' > d·x`, since `x = d·x₁`. -/

/-- The coprime quadruples of `m` with `x' > d·x`. -/
def quadGT (m d : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  (quadruplesAll m).filter (fun q => d * q.1 < q.2.1)

theorem mem_quadGT {m d x x' y y' : ℕ} :
    (x, x', y, y') ∈ quadGT m d ↔
      ((x ≤ m ∧ x' ≤ m ∧ y ≤ m ∧ y' ≤ m) ∧ 1 ≤ y ∧ y < x ∧ 1 ≤ y' ∧ y' < x'
        ∧ Nat.gcd x y = 1 ∧ m = x * x' + y * y') ∧ d * x < x' := by
  simp [quadGT, Finset.mem_filter, mem_quadruplesAll]

/-- **The symmetrised sum, classified by `gcd(x,y)`.** -/
theorem sum_QGT_classify {n : ℕ} (hn : 0 < n) :
    ∑ q ∈ (quadruplesQ n).filter (fun q => q.1 < q.2.1), (q.1 + q.2.1)
      = ∑ d ∈ n.divisors, ∑ q ∈ quadGT (n / d) d, (d * q.1 + q.2.1) := by
  rw [Finset.sum_sigma']
  refine Finset.sum_bij'
    (i := fun q _ => (⟨Nat.gcd q.1 q.2.2.1,
        (q.1 / Nat.gcd q.1 q.2.2.1, q.2.1, q.2.2.1 / Nat.gcd q.1 q.2.2.1,
          q.2.2.2)⟩ : (_ : ℕ) × (ℕ × ℕ × ℕ × ℕ)))
    (j := fun p _ => (p.1 * p.2.1, p.2.2.1, p.1 * p.2.2.2.1, p.2.2.2.2))
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨x, x', y, y'⟩ hq
    simp only [Finset.mem_filter] at hq
    obtain ⟨hmem, hab⟩ := hq
    obtain ⟨-, hx1, hx2, hx'1, hx'2, hsum⟩ := mem_quadruplesQ.1 hmem
    have hd : 0 < Nat.gcd x y := Nat.gcd_pos_of_pos_left _ (by omega)
    have hda : Nat.gcd x y ∣ x := Nat.gcd_dvd_left _ _
    have hdy : Nat.gcd x y ∣ y := Nat.gcd_dvd_right _ _
    have hdn : Nat.gcd x y ∣ n := by
      rw [hsum]
      exact Dvd.dvd.add (Dvd.dvd.mul_right hda x') (Dvd.dvd.mul_right hdy y')
    have hnd : n / Nat.gcd x y
        = x / Nat.gcd x y * x' + y / Nat.gcd x y * y' := by
      rw [Nat.div_eq_iff_eq_mul_left hd hdn, hsum, Nat.add_mul, Nat.mul_right_comm,
        Nat.mul_right_comm (y / Nat.gcd x y), Nat.div_mul_cancel hda,
        Nat.div_mul_cancel hdy]
    have hq1 : 1 ≤ y / Nat.gcd x y :=
      (Nat.one_le_div_iff hd).2 (Nat.le_of_dvd (by omega) hdy)
    have hq2 : y / Nat.gcd x y < x / Nat.gcd x y :=
      Nat.div_lt_div_of_lt_of_dvd hda hx2
    have hgt : Nat.gcd x y * (x / Nat.gcd x y) < x' := by
      rwa [Nat.mul_div_cancel' hda]
    simp only [Finset.mem_sigma, Nat.mem_divisors]
    exact ⟨⟨hdn, hn.ne'⟩, mem_quadGT.2
      ⟨⟨quadruple_le hq1 hq2 hx'1 hx'2 hnd, hq1, hq2, hx'1, hx'2,
        Nat.coprime_div_gcd_div_gcd hd, hnd⟩, hgt⟩⟩
  · rintro ⟨d, a1, x', a1', y'⟩ hp
    simp only [Finset.mem_sigma, Nat.mem_divisors] at hp
    obtain ⟨⟨hdn, -⟩, hq⟩ := hp
    obtain ⟨⟨-, hx1, hx2, hx'1, hx'2, -, hsum⟩, hgt⟩ := mem_quadGT.1 hq
    have hd : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
    have hmul : d * (n / d) = n := Nat.mul_div_cancel' hdn
    have hsum' : n = d * a1 * x' + d * a1' * y' := by
      rw [← hmul, hsum]; ring
    have hp1 : 1 ≤ d * a1' := Nat.mul_pos hd hx1
    have hp2 : d * a1' < d * a1 := by nlinarith
    simp only [Finset.mem_filter]
    exact ⟨mem_quadruplesQ.2 ⟨quadruple_le hp1 hp2 hx'1 hx'2 hsum', hp1, hp2, hx'1, hx'2, hsum'⟩,
      hgt⟩
  · rintro ⟨x, x', y, y'⟩ hq
    simp only [Finset.mem_filter] at hq
    obtain ⟨hmem, -⟩ := hq
    obtain ⟨-, hx1, hx2, -, -, -⟩ := mem_quadruplesQ.1 hmem
    have hd : 0 < Nat.gcd x y := Nat.gcd_pos_of_pos_left _ (by omega)
    have e1 : Nat.gcd x y * (x / Nat.gcd x y) = x :=
      Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
    have e2 : Nat.gcd x y * (y / Nat.gcd x y) = y :=
      Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
    rw [e1, e2]
  · rintro ⟨d, a1, x', a1', y'⟩ hp
    simp only [Finset.mem_sigma, Nat.mem_divisors] at hp
    obtain ⟨⟨hdn, -⟩, hq⟩ := hp
    obtain ⟨⟨-, -, -, -, -, hcop, -⟩, -⟩ := mem_quadGT.1 hq
    have hd : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
    have hgcd : Nat.gcd (d * a1) (d * a1') = d := by
      rw [Nat.gcd_mul_left, hcop, mul_one]
    simp only [hgcd, Nat.mul_div_cancel_left _ hd]
  · rintro ⟨x, x', y, y'⟩ hq
    simp only [Finset.mem_filter] at hq
    obtain ⟨hmem, -⟩ := hq
    obtain ⟨-, hx1, hx2, -, -, -⟩ := mem_quadruplesQ.1 hmem
    have e1 : Nat.gcd x y * (x / Nat.gcd x y) = x :=
      Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
    show x + x' = Nat.gcd x y * (x / Nat.gcd x y) + x'
    rw [e1]

/-- The triples with the paper's condition `m - y·y' > d·x²`, which is `x' > d·x`
after eliminating `x'`. -/
def gtTriples (m d : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (coprimeTriples m).filter (fun t => d * t.1 * t.1 < m - t.2.1 * t.2.2)

theorem mem_gtTriples {m d x y y' : ℕ} :
    (x, y, y') ∈ gtTriples m d ↔
      (((x ≤ m ∧ y ≤ m ∧ y' ≤ m) ∧ 1 ≤ y ∧ y < x ∧ 1 ≤ y'
        ∧ (x + y) * y' < m ∧ x ∣ (m - y * y')) ∧ Nat.gcd x y = 1)
        ∧ d * x * x < m - y * y' := by
  simp [gtTriples, Finset.mem_filter, mem_coprimeTriples]

/-- **The `x'`-elimination on the restricted set.** -/
theorem sum_quadGT_eq {m d : ℕ} (hm : 0 < m) :
    ∑ q ∈ quadGT m d, (d * q.1 + q.2.1)
      = ∑ t ∈ gtTriples m d, (d * t.1 + (m - t.2.1 * t.2.2) / t.1) := by
  refine Finset.sum_bij'
    (i := fun q _ => (q.1, q.2.2.1, q.2.2.2))
    (j := fun t _ => (t.1, (m - t.2.1 * t.2.2) / t.1, t.2.1, t.2.2)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨x, x', y, y'⟩ hq
    obtain ⟨⟨⟨hab, hbb, hyx', hy'x'⟩, hx1, hx2, hx'1, hx'2, hgcd, hsum⟩, hgt⟩ := mem_quadGT.1 hq
    have hx : 0 < x := by omega
    have hdvd : x ∣ (m - y * y') := ⟨x', by omega⟩
    have hlt : (x + y) * y' < m := by nlinarith
    have heq : m - y * y' = x * x' := by omega
    have hgt' : d * x * x < m - y * y' := by
      rw [heq]
      nlinarith
    show (x, y, y') ∈ gtTriples m d
    rw [mem_gtTriples]
    exact ⟨⟨⟨⟨hab, hyx', hy'x'⟩, hx1, hx2, hx'1, hlt, hdvd⟩, hgcd⟩, hgt'⟩
  · rintro ⟨x, y, y'⟩ ht
    obtain ⟨⟨⟨⟨han, hyn, hy'n⟩, hx1, hx2, hx'1, hlt, hdvd⟩, hgcd⟩, hgt⟩ := mem_gtTriples.1 ht
    have hx : 0 < x := by omega
    have hab : x * ((m - y * y') / x) = m - y * y' := Nat.mul_div_cancel' hdvd
    have hle : y * y' ≤ m := by nlinarith
    have hsum : m = x * ((m - y * y') / x) + y * y' := by omega
    have hbb : y' < (m - y * y') / x := by
      have h1 : x * y' < x * ((m - y * y') / x) := by rw [hab]; nlinarith
      exact Nat.lt_of_mul_lt_mul_left h1
    have hgt' : d * x < (m - y * y') / x := by
      have h1 : x * (d * x) < x * ((m - y * y') / x) := by rw [hab]; nlinarith
      exact Nat.lt_of_mul_lt_mul_left h1
    show (x, (m - y * y') / x, y, y') ∈ quadGT m d
    rw [mem_quadGT]
    exact ⟨⟨quadruple_le hx1 hx2 hx'1 hbb hsum, hx1, hx2, hx'1, hbb, hgcd, hsum⟩, hgt'⟩
  · rintro ⟨x, x', y, y'⟩ hq
    obtain ⟨⟨-, hx1, hx2, hx'1, hx'2, -, hsum⟩, -⟩ := mem_quadGT.1 hq
    have hx : 0 < x := by omega
    have h : m - y * y' = x * x' := by omega
    show (x, (m - y * y') / x, y, y') = (x, x', y, y')
    rw [h, Nat.mul_div_cancel_left _ hx]
  · rintro ⟨x, y, y'⟩ _
    rfl
  · rintro ⟨x, x', y, y'⟩ hq
    obtain ⟨⟨-, hx1, hx2, hx'1, hx'2, -, hsum⟩, -⟩ := mem_quadGT.1 hq
    have hx : 0 < x := by omega
    have h : m - y * y' = x * x' := by omega
    show d * x + x' = d * x + (m - y * y') / x
    rw [h, Nat.mul_div_cancel_left _ hx]

/-- **The restricted triple sum.**  This is the paper's triple sum: over
divisors `d ∣ n`, coprime pairs `x > y ≥ 1`, and `y'` subject to
`(x+y)y' < n/d`, `n/d ≡ y·y' (mod x)` and `n/d - y·y' > d·x²`. -/
theorem Q_gt_tripleSum {n : ℕ} (hn : 0 < n) :
    ∑ q ∈ (quadruplesQ n).filter (fun q => q.1 < q.2.1), (q.1 + q.2.1)
      = ∑ d ∈ n.divisors, ∑ t ∈ gtTriples (n / d) d,
          (d * t.1 + (n / d - t.2.1 * t.2.2) / t.1) := by
  rw [sum_QGT_classify hn]
  refine Finset.sum_congr rfl fun d hd => ?_
  obtain ⟨hdn, -⟩ := Nat.mem_divisors.1 hd
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
  exact sum_quadGT_eq (Nat.div_pos (Nat.le_of_dvd hn hdn) hd0)

/-- **The key restriction.**  On `gtTriples m d` we have `d·x² < m`, so
`x ≤ √(m/d)`.  This is what makes the error sum converge. -/
theorem gtTriples_sq_lt {m d x y y' : ℕ} (h : (x, y, y') ∈ gtTriples m d) :
    d * x * x < m := by
  obtain ⟨⟨⟨-, -, -, hx'1, hlt, -⟩, -⟩, hgt⟩ := mem_gtTriples.1 h
  omega

/-! ## The innermost range

For a fixed pair `(x, y)` the conditions `(x+y)y' < m` and `m - y·y' > d·x²`
are two upper bounds on `y'`, so the range is an initial segment cut at the
paper's `Y = min( m/(x+y), (m - d·x²)/y )` (§4; with `m = n/d` this is the
paper's `Y(n,d,x,y) = min( n/(d(x+y)), (n - d²x²)/(dy) )`).  `Y` there is real;
`yBound` below is the integer endpoint it induces, as `mem_gtRange` records. -/

/-- The integer cut-off induced by the paper's `Y`. -/
def yBound (m d x y : ℕ) : ℕ :=
  min ((m - 1) / (x + y) + 1) ((m - d * x * x - 1) / y + 1)

theorem mem_gtRange {m d x y y' : ℕ} (hm : 0 < m) (haa : 0 < x + y) (hy : 0 < y)
    (hda : d * x * x < m) :
    y' ∈ Finset.Ico 1 (yBound m d x y)
      ↔ (1 ≤ y' ∧ (x + y) * y' < m ∧ y * y' + d * x * x < m) := by
  rw [Finset.mem_Ico, yBound, lt_min_iff, Nat.lt_succ_iff, Nat.lt_succ_iff,
    Nat.le_div_iff_mul_le haa, Nat.le_div_iff_mul_le hy,
    Nat.mul_comm y' (x + y), Nat.mul_comm y' y]
  omega

/-- **For a bulk pair the first branch of the cut-off wins.**

`Y = min(m/(x+y), (m - d x²)/y)`, and the paper observes that the first term
is the smaller exactly when `d·x·(x+y) ≤ m`.  In the floored form used here
that reads `yBound m d x y = (m-1)/(x+y) + 1`. -/
theorem yBound_bulk_eq {m d x y : ℕ} (hd : 0 < d) (hy : 1 ≤ y) (haa : y < x)
    (hbulk : d * x * (x + y) ≤ m) :
    yBound m d x y = (m - 1) / (x + y) + 1 := by
  have hx : 0 < x := by omega
  have hs : 0 < x + y := by omega
  have hda : 1 ≤ d * x := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hm2 : d * x * x + 1 ≤ m := by nlinarith
  have hdm := Nat.div_add_mod (m - 1) (x + y)
  have hr : (m - 1) % (x + y) < x + y := Nat.mod_lt _ hs
  set q := (m - 1) / (x + y) with hq
  set r := (m - 1) % (x + y) with hrr
  have hmeq : m = (x + y) * q + r + 1 := by omega
  have hexp : (x + y) * q = x * q + y * q := by ring
  -- either `d·x ≤ q`, or `d·x = q+1` and the remainder is maximal
  have hcase : d * x * x ≤ x * q + r := by
    rcases Nat.lt_or_ge q (d * x) with h | h
    swap
    · have h1 : d * x * x ≤ q * x := Nat.mul_le_mul_right x h
      nlinarith
    · have h1 : d * x * (x + y) ≤ (x + y) * q + r + 1 := by omega
      have h2 : (x + y) * q + r + 1 ≤ (q + 1) * (x + y) := by nlinarith
      have h5 : d * x ≤ q + 1 := Nat.le_of_mul_le_mul_right (by nlinarith) hs
      have hdq : d * x = q + 1 := by omega
      have h6 : (q + 1) * (x + y) ≤ (x + y) * q + r + 1 := by
        rw [← hdq]; exact h1
      have hrs : x + y ≤ r + 1 := by nlinarith
      have : d * x * x = x * q + x := by rw [hdq]; ring
      omega
  rw [yBound, min_eq_left]
  refine Nat.succ_le_succ ?_
  rw [Nat.le_div_iff_mul_le (by omega), Nat.sub_sub, Nat.le_sub_iff_add_le hm2]
  nlinarith

/-- **The restricted triple sum, decomposed by pairs.** -/
theorem gtTriples_decompose {m d : ℕ} (hm : 0 < m) (f : ℕ → ℕ → ℕ → ℕ) :
    ∑ t ∈ gtTriples m d, f t.1 t.2.1 t.2.2
      = ∑ p ∈ (coprimePairs m).filter (fun p => d * p.1 * p.1 < m),
          ∑ y' ∈ (Finset.Ico 1 (yBound m d p.1 p.2)).filter
            (fun y' => p.1 ∣ (m - p.2 * y')), f p.1 p.2 y' := by
  rw [Finset.sum_sigma']
  refine Finset.sum_bij'
    (i := fun t _ => (⟨(t.1, t.2.1), t.2.2⟩ : (_ : ℕ × ℕ) × ℕ))
    (j := fun p _ => (p.1.1, p.1.2, p.2)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨x, y, y'⟩ ht
    obtain ⟨⟨⟨⟨han, hyn, hy'n⟩, hx1, hx2, hx'1, hlt, hdvd⟩, hgcd⟩, hgt⟩ := mem_gtTriples.1 ht
    have haa : 0 < x + y := by omega
    have hle : y * y' ≤ m := by nlinarith
    have hda : d * x * x < m := by omega
    simp only [Finset.mem_sigma, Finset.mem_filter]
    exact ⟨⟨mem_coprimePairs.2 ⟨⟨han, hyn⟩, hx1, hx2, hgcd⟩, hda⟩,
      (mem_gtRange hm haa (by omega) hda).2 ⟨hx'1, hlt, by omega⟩, hdvd⟩
  · rintro ⟨⟨x, y⟩, y'⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_filter] at hp
    obtain ⟨⟨hpair, hda⟩, hx', hdvd⟩ := hp
    obtain ⟨⟨han, hyn⟩, hx1, hx2, hgcd⟩ := mem_coprimePairs.1 hpair
    have haa : 0 < x + y := by omega
    obtain ⟨hx'1, hlt, hgt⟩ := (mem_gtRange hm haa (by omega) hda).1 hx'
    have hy'n : y' ≤ m := by nlinarith
    show (x, y, y') ∈ gtTriples m d
    rw [mem_gtTriples]
    have hle : y * y' ≤ m := by nlinarith
    exact ⟨⟨⟨⟨han, hyn, hy'n⟩, hx1, hx2, hx'1, hlt, hdvd⟩, hgcd⟩, by omega⟩
  · rintro ⟨x, y, y'⟩ _
    rfl
  · rintro ⟨⟨x, y⟩, y'⟩ _
    rfl
  · rintro ⟨x, y, y'⟩ _
    rfl

/-! ## The estimate, over the reals

`Progression.lean` states the progression estimate over `ℂ`.  The triple sum is
real, so we record the real form. -/

/-- The progression estimate, over `ℝ`. -/
theorem sum_ap_sub_main_le_log_real {x : ℕ} (hx : 0 < x) (c : ℤ) (A B : ℝ) (T : ℕ) :
    |(∑ x' ∈ Finset.Ico 1 T, if (x : ℤ) ∣ ((x' : ℤ) - c) then (A + B * x') else 0)
        - (1 / (x : ℝ)) * ∑ x' ∈ Finset.Ico 1 T, (A + B * x')|
      ≤ (|A| + |B| * (T - 1 : ℕ)) * (1 + Real.log x) := by
  have h := sum_ap_sub_main_le_log hx c (A : ℂ) (B : ℂ) T
  have key : ((((∑ x' ∈ Finset.Ico 1 T, if (x : ℤ) ∣ ((x' : ℤ) - c) then (A + B * x') else 0)
        - (1 / (x : ℝ)) * ∑ x' ∈ Finset.Ico 1 T, (A + B * x') : ℝ)) : ℂ)
      = (∑ x' ∈ Finset.Ico 1 T, if (x : ℤ) ∣ ((x' : ℤ) - c) then ((A : ℂ) + B * x') else 0)
        - (1 / (x : ℂ)) * ∑ x' ∈ Finset.Ico 1 T, ((A : ℂ) + B * x') := by
    push_cast
    congr 1
    refine Finset.sum_congr rfl fun x' _ => ?_
    split <;> push_cast <;> ring
  rw [← key, Complex.norm_real] at h
  simpa using h

/-- The inner sum of the restricted triple sum, as an arithmetic-progression sum
with the paper's coefficients `A = d·x + m/x` and `B = -y/x`. -/
theorem inner_gt_sum_eq {m d x y : ℕ} (hx : 0 < x) (hgcd : Nat.gcd x y = 1) :
    ∃ c : ℤ, ∀ U : ℕ, (∀ y' ∈ Finset.Ico 1 U, y * y' ≤ m) →
      ((∑ y' ∈ (Finset.Ico 1 U).filter (fun y' => x ∣ (m - y * y')),
          (d * x + (m - y * y') / x) : ℕ) : ℝ)
        = ∑ y' ∈ Finset.Ico 1 U,
            (if (x : ℤ) ∣ ((y' : ℤ) - c) then
              ((((d * x : ℕ) : ℝ) + (m : ℝ) / x) + (-(y : ℝ) / x) * y') else 0) := by
  obtain ⟨c, hc⟩ := exists_residue (m := m) hgcd
  refine ⟨c, fun U hU => ?_⟩
  rw [Finset.sum_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun y' hy' => ?_
  have hle : y * y' ≤ m := hU y' hy'
  have hiff : (x ∣ (m - y * y')) ↔ ((x : ℤ) ∣ ((y' : ℤ) - c)) := by
    rw [← hc (y' : ℤ)]
    constructor
    · intro h
      have h2 : ((x : ℤ)) ∣ (((m - y * y' : ℕ)) : ℤ) := Int.natCast_dvd_natCast.2 h
      rwa [Nat.cast_sub hle, Nat.cast_mul] at h2
    · intro h
      have h2 : ((x : ℤ)) ∣ (((m - y * y' : ℕ)) : ℤ) := by
        rwa [Nat.cast_sub hle, Nat.cast_mul]
      exact Int.natCast_dvd_natCast.1 h2
  by_cases hd : x ∣ (m - y * y')
  · rw [if_pos hd, if_pos (hiff.1 hd)]
    have hmul : x * ((m - y * y') / x) = m - y * y' := Nat.mul_div_cancel' hd
    have hreal : ((x : ℝ)) * (((m - y * y') / x : ℕ) : ℝ) = (m : ℝ) - (y : ℝ) * y' := by
      have h3 := congrArg (Nat.cast : ℕ → ℝ) hmul
      push_cast [Nat.cast_sub hle] at h3
      linarith
    have hane : ((x : ℝ)) ≠ 0 := by positivity
    push_cast
    field_simp at hreal ⊢
    linarith
  · rw [if_neg hd, if_neg (fun h => hd (hiff.2 h))]
    simp

/-- **The innermost estimation layer.**  For a fixed pair `(x, y)`, the inner
sum differs from its expected value by `O(log x)` times the size of the
coefficients — the paper's `G₂ + G₃` for that pair. -/
theorem inner_gt_estimate {m d x y : ℕ} (hx : 0 < x) (hgcd : Nat.gcd x y = 1) (U : ℕ)
    (hU : ∀ y' ∈ Finset.Ico 1 U, y * y' ≤ m) :
    ∃ c : ℤ,
      |((∑ y' ∈ (Finset.Ico 1 U).filter (fun y' => x ∣ (m - y * y')),
            (d * x + (m - y * y') / x) : ℕ) : ℝ)
          - (1 / (x : ℝ)) * ∑ y' ∈ Finset.Ico 1 U,
              ((((d * x : ℕ) : ℝ) + (m : ℝ) / x) + (-(y : ℝ) / x) * y')|
        ≤ (|((d * x : ℕ) : ℝ) + (m : ℝ) / x| + |(-(y : ℝ) / x)| * (U - 1 : ℕ))
            * (1 + Real.log x) := by
  obtain ⟨c, hc⟩ := inner_gt_sum_eq (m := m) (d := d) hx hgcd
  refine ⟨c, ?_⟩
  rw [hc U hU]
  exact sum_ap_sub_main_le_log_real hx c _ _ U

/-! ## The middle layer

Summing the per-pair error over `y < x` coprime and then over `x ≤ √(m/d)`.
The grouping matters: the `x` values of `y` cancel the `1/x` in the
coefficient `2m/x`, leaving `d·x² + 2m ≤ 3m` per value of `x`. -/

/-- The pairs, decomposed by their first component. -/
theorem sum_coprimePairs_filter {M : Type*} [AddCommMonoid M] {m d : ℕ} (g : ℕ → ℕ → M) :
    ∑ p ∈ (coprimePairs m).filter (fun p => d * p.1 * p.1 < m), g p.1 p.2
      = ∑ x ∈ (Finset.range (m + 1)).filter (fun x => d * x * x < m),
          ∑ y ∈ (Finset.Ico 1 x).filter (fun y => Nat.gcd x y = 1), g x y := by
  rw [Finset.sum_sigma']
  refine Finset.sum_bij' (i := fun p _ => (⟨p.1, p.2⟩ : (_ : ℕ) × ℕ))
    (j := fun q _ => (q.1, q.2)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨x, y⟩ hp
    simp only [Finset.mem_filter] at hp
    obtain ⟨hpair, hda⟩ := hp
    obtain ⟨⟨han, hyn⟩, hx1, hx2, hgcd⟩ := mem_coprimePairs.1 hpair
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    exact ⟨⟨by omega, hda⟩, ⟨hx1, hx2⟩, hgcd⟩
  · rintro ⟨x, y⟩ hq
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at hq
    obtain ⟨⟨ham, hda⟩, ⟨hx1, hx2⟩, hgcd⟩ := hq
    simp only [Finset.mem_filter]
    exact ⟨mem_coprimePairs.2 ⟨⟨by omega, by omega⟩, hx1, hx2, hgcd⟩, hda⟩
  · rintro ⟨x, y⟩ _
    rfl
  · rintro ⟨x, y⟩ _
    rfl
  · rintro ⟨x, y⟩ _
    rfl

/-- For each `x`, the number of admissible `y` is less than `x`. -/
theorem card_coprimeSecond_lt {x : ℕ} (hx : 0 < x) :
    (((Finset.Ico 1 x).filter (fun y => Nat.gcd x y = 1)).card : ℝ) ≤ (x : ℝ) := by
  have h : ((Finset.Ico 1 x).filter (fun y => Nat.gcd x y = 1)).card ≤ x := by
    calc ((Finset.Ico 1 x).filter (fun y => Nat.gcd x y = 1)).card
        ≤ (Finset.Ico 1 x).card := Finset.card_filter_le _ _
      _ = x - 1 := by simp
      _ ≤ x := Nat.sub_le _ _
  exact_mod_cast h

/-- The admissible `x` are at most `√((m-1)/d)`. -/
theorem card_a_le {m d : ℕ} (hd : 0 < d) :
    ((Finset.range (m + 1)).filter (fun x => d * x * x < m)).card
      ≤ Nat.sqrt ((m - 1) / d) + 1 := by
  have hsub : (Finset.range (m + 1)).filter (fun x => d * x * x < m)
      ⊆ Finset.range (Nat.sqrt ((m - 1) / d) + 1) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
    obtain ⟨-, hda⟩ := hx
    have h1 : x * x * d ≤ m - 1 := by
      have heq : d * x * x = x * x * d := by ring
      omega
    exact Nat.lt_succ_of_le (Nat.le_sqrt.2 ((Nat.le_div_iff_mul_le hd).2 h1))
  calc ((Finset.range (m + 1)).filter (fun x => d * x * x < m)).card
      ≤ (Finset.range (Nat.sqrt ((m - 1) / d) + 1)).card := Finset.card_le_card hsub
    _ = Nat.sqrt ((m - 1) / d) + 1 := Finset.card_range _

/-- **The middle layer.**  Summing the per-pair error bound over the coprime
pairs gives `3m(1 + log m)` for each admissible `x`. -/
theorem middle_layer_bound {m d : ℕ} (hm : 0 < m) :
    ∑ p ∈ (coprimePairs m).filter (fun p => d * p.1 * p.1 < m),
        (((d * p.1 : ℕ) : ℝ) + 2 * (m : ℝ) / p.1) * (1 + Real.log m)
      ≤ (((Finset.range (m + 1)).filter (fun x => d * x * x < m)).card : ℝ)
          * (3 * (m : ℝ) * (1 + Real.log m)) := by
  have hm' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hlog : (0 : ℝ) ≤ 1 + Real.log m := by
    have := Real.log_nonneg hm'
    linarith
  rw [sum_coprimePairs_filter (m := m) (d := d)
    (g := fun x _ => (((d * x : ℕ) : ℝ) + 2 * (m : ℝ) / x) * (1 + Real.log m))]
  calc ∑ x ∈ (Finset.range (m + 1)).filter (fun x => d * x * x < m),
        ∑ _y ∈ (Finset.Ico 1 x).filter (fun y => Nat.gcd x y = 1),
          (((d * x : ℕ) : ℝ) + 2 * (m : ℝ) / x) * (1 + Real.log m)
      ≤ ∑ _x ∈ (Finset.range (m + 1)).filter (fun x => d * x * x < m),
          3 * (m : ℝ) * (1 + Real.log m) := by
        refine Finset.sum_le_sum fun x hx => ?_
        simp only [Finset.mem_filter, Finset.mem_range] at hx
        obtain ⟨ham, hda⟩ := hx
        rcases Nat.eq_zero_or_pos x with h0 | h0
        · subst h0
          simp
          positivity
        · have hcard := card_coprimeSecond_lt h0
          have hx1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast h0
          have hane : (x : ℝ) ≠ 0 := by linarith
          have hdle : (d : ℝ) * x * x ≤ (m : ℝ) := by
            have h2 : d * x * x ≤ m := hda.le
            exact_mod_cast h2
          calc ∑ _y ∈ (Finset.Ico 1 x).filter (fun y => Nat.gcd x y = 1),
                (((d * x : ℕ) : ℝ) + 2 * (m : ℝ) / x) * (1 + Real.log m)
              = ((((Finset.Ico 1 x).filter (fun y => Nat.gcd x y = 1)).card : ℝ))
                  * ((((d * x : ℕ) : ℝ) + 2 * (m : ℝ) / x) * (1 + Real.log m)) := by
                rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ (x : ℝ) * ((((d * x : ℕ) : ℝ) + 2 * (m : ℝ) / x) * (1 + Real.log m)) := by
                refine mul_le_mul_of_nonneg_right hcard ?_
                have hnn : (0 : ℝ) ≤ ((d * x : ℕ) : ℝ) + 2 * (m : ℝ) / x := by positivity
                exact mul_nonneg hnn hlog
            _ = ((d : ℝ) * x * x + 2 * (m : ℝ)) * (1 + Real.log m) := by
                push_cast
                field_simp
            _ ≤ 3 * (m : ℝ) * (1 + Real.log m) := by nlinarith
    _ = (((Finset.range (m + 1)).filter (fun x => d * x * x < m)).card : ℝ)
          * (3 * (m : ℝ) * (1 + Real.log m)) := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- **The middle layer, combined.**  The per-pair error bounds sum to
`O(√(m/d) · m · log m)` — which is `m^{3/2}/√d` up to the logarithm. -/
theorem middle_layer {m d : ℕ} (hm : 0 < m) (hd : 0 < d) :
    ∑ p ∈ (coprimePairs m).filter (fun p => d * p.1 * p.1 < m),
        (((d * p.1 : ℕ) : ℝ) + 2 * (m : ℝ) / p.1) * (1 + Real.log m)
      ≤ ((Nat.sqrt ((m - 1) / d) : ℝ) + 1) * (3 * (m : ℝ) * (1 + Real.log m)) := by
  have hm' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hlog : (0 : ℝ) ≤ 1 + Real.log m := by
    have := Real.log_nonneg hm'
    linarith
  refine (middle_layer_bound hm).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  have h := card_a_le (m := m) hd
  have : (((Finset.range (m + 1)).filter (fun x => d * x * x < m)).card : ℝ)
      ≤ ((Nat.sqrt ((m - 1) / d) + 1 : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at this
  linarith

/-! ## The outer layer

Summing the middle-layer bound over the divisors `d ∣ n`, with `m = n/d`.
Bounding each factor by its value at `d = 1` costs only a factor `d(n)`, which
the divisor bound absorbs. -/

/-- **The outer layer.** -/
theorem outer_layer {n : ℕ} (hn : 0 < n) :
    ∑ d ∈ n.divisors,
        ((Nat.sqrt ((n / d - 1) / d) : ℝ) + 1)
          * (3 * ((n / d : ℕ) : ℝ) * (1 + Real.log ((n / d : ℕ) : ℝ)))
      ≤ (n.divisors.card : ℝ)
          * (((Nat.sqrt n : ℝ) + 1) * (3 * (n : ℝ) * (1 + Real.log n))) := by
  calc ∑ d ∈ n.divisors,
        ((Nat.sqrt ((n / d - 1) / d) : ℝ) + 1)
          * (3 * ((n / d : ℕ) : ℝ) * (1 + Real.log ((n / d : ℕ) : ℝ)))
      ≤ ∑ _d ∈ n.divisors,
          (((Nat.sqrt n : ℝ) + 1) * (3 * (n : ℝ) * (1 + Real.log n))) := by
        refine Finset.sum_le_sum fun d hd => ?_
        obtain ⟨hdn, -⟩ := Nat.mem_divisors.1 hd
        have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
        have hm : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hn hdn) hd0
        have hmn : n / d ≤ n := Nat.div_le_self _ _
        have hm' : (1 : ℝ) ≤ ((n / d : ℕ) : ℝ) := by exact_mod_cast hm
        have hmn' : ((n / d : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
        have hlognn : (0 : ℝ) ≤ Real.log ((n / d : ℕ) : ℝ) := Real.log_nonneg hm'
        have hlog : Real.log ((n / d : ℕ) : ℝ) ≤ Real.log (n : ℝ) :=
          Real.log_le_log (by linarith) hmn'
        have hs : Nat.sqrt ((n / d - 1) / d) ≤ Nat.sqrt n := by
          refine Nat.sqrt_le_sqrt ?_
          calc (n / d - 1) / d ≤ n / d - 1 := Nat.div_le_self _ _
            _ ≤ n := by omega
        have h1 : ((Nat.sqrt ((n / d - 1) / d) : ℝ) + 1) ≤ ((Nat.sqrt n : ℝ) + 1) := by
          have hc : (Nat.sqrt ((n / d - 1) / d) : ℝ) ≤ (Nat.sqrt n : ℝ) := by
            exact_mod_cast hs
          linarith
        have h2 : (3 * ((n / d : ℕ) : ℝ) * (1 + Real.log ((n / d : ℕ) : ℝ)))
            ≤ (3 * (n : ℝ) * (1 + Real.log n)) := by nlinarith
        have hnn2 : (0 : ℝ) ≤ (3 * ((n / d : ℕ) : ℝ) * (1 + Real.log ((n / d : ℕ) : ℝ))) := by
          nlinarith
        exact mul_le_mul h1 h2 hnn2 (by positivity)
    _ = (n.divisors.card : ℝ)
          * (((Nat.sqrt n : ℝ) + 1) * (3 * (n : ℝ) * (1 + Real.log n))) := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- **The three layers combined: `O(n^{3/2+ε})`.**

The aggregate of the per-pair error bounds, summed over pairs and divisors, is
`O(n^{3/2+ε})` — the bound Lemmas 18 and 19 of the paper establish for
`G₂ + G₃`. -/
theorem error_isBigO {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
      (n.divisors.card : ℝ) * (((Nat.sqrt n : ℝ) + 1) * (3 * (n : ℝ) * (1 + Real.log n)))
        ≤ C * (n : ℝ) ^ (3 / 2 + ε) := by
  obtain ⟨C0, hC0, hCd⟩ := exists_card_divisors_le (half_pos hε)
  refine ⟨12 * C0 * (1 + 2 / ε), by positivity, fun n hn => ?_⟩
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hhalf : (0 : ℝ) < ε / 2 := half_pos hε
  -- `√n ≤ n^{1/2}`
  have hsqrt : ((Nat.sqrt n : ℝ) + 1) ≤ 2 * (n : ℝ) ^ ((1 : ℝ) / 2) := by
    have h1 : (Nat.sqrt n : ℝ) ≤ Real.sqrt (n : ℝ) := by
      refine (Real.le_sqrt (by positivity) (by positivity)).2 ?_
      have hsq : Nat.sqrt n * Nat.sqrt n ≤ n := by
        have h2 := Nat.sqrt_le' n
        rwa [pow_two] at h2
      have hcast : ((Nat.sqrt n : ℕ) : ℝ) * ((Nat.sqrt n : ℕ) : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast hsq
      nlinarith [hcast]
    have h2 : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt hn'
    rw [Real.sqrt_eq_rpow] at h1 h2
    linarith
  -- `1 + log n ≤ (1 + 2/ε)·n^{ε/2}`
  have hlogb : 1 + Real.log n ≤ (1 + 2 / ε) * (n : ℝ) ^ (ε / 2) := by
    have h := Real.log_le_rpow_div hnpos.le hhalf
    have hge : (1 : ℝ) ≤ (n : ℝ) ^ (ε / 2) := Real.one_le_rpow hn' hhalf.le
    have hdiv : (n : ℝ) ^ (ε / 2) / (ε / 2) = (2 / ε) * (n : ℝ) ^ (ε / 2) := by
      field_simp
    rw [hdiv] at h
    nlinarith
  have hd := hCd n hn.ne'
  have hdnn : (0 : ℝ) ≤ (n.divisors.card : ℝ) := by positivity
  have hrpow : (n : ℝ) ^ (3 / 2 + ε)
      = (n : ℝ) ^ (ε / 2) * ((n : ℝ) ^ ((1 : ℝ) / 2) * ((n : ℝ) * (n : ℝ) ^ (ε / 2))) := by
    rw [show ((n : ℝ) * (n : ℝ) ^ (ε / 2)) = (n : ℝ) ^ ((1 : ℝ) + ε / 2) from by
      rw [Real.rpow_add hnpos, Real.rpow_one]]
    rw [← Real.rpow_add hnpos, ← Real.rpow_add hnpos]
    congr 1
    ring
  rw [hrpow]
  have hlognn : (0 : ℝ) ≤ Real.log n := Real.log_nonneg hn'
  have hC : (3 * (n : ℝ) * (1 + Real.log n))
      ≤ 3 * (n : ℝ) * ((1 + 2 / ε) * (n : ℝ) ^ (ε / 2)) :=
    mul_le_mul_of_nonneg_left hlogb (by positivity)
  have hBC : ((Nat.sqrt n : ℝ) + 1) * (3 * (n : ℝ) * (1 + Real.log n))
      ≤ (2 * (n : ℝ) ^ ((1 : ℝ) / 2))
          * (3 * (n : ℝ) * ((1 + 2 / ε) * (n : ℝ) ^ (ε / 2))) :=
    mul_le_mul hsqrt hC (by positivity) (by positivity)
  refine (mul_le_mul hd hBC (by positivity) (by positivity)).trans ?_
  have heq : (C0 * (n : ℝ) ^ (ε / 2))
        * ((2 * (n : ℝ) ^ ((1 : ℝ) / 2))
          * (3 * (n : ℝ) * ((1 + 2 / ε) * (n : ℝ) ^ (ε / 2))))
      = 6 * C0 * (1 + 2 / ε)
          * ((n : ℝ) ^ (ε / 2) * ((n : ℝ) ^ ((1 : ℝ) / 2) * ((n : ℝ) * (n : ℝ) ^ (ε / 2)))) := by
    ring
  rw [heq]
  have hpos : (0 : ℝ)
      ≤ (n : ℝ) ^ (ε / 2) * ((n : ℝ) ^ ((1 : ℝ) / 2) * ((n : ℝ) * (n : ℝ) ^ (ε / 2))) := by
    positivity
  have hfac : (0 : ℝ) ≤ C0 * (1 + 2 / ε) := by positivity
  nlinarith [mul_nonneg hfac hpos]

/-! ## The bulk / small split

Lemma 19 splits `G₁` according to which of the two bounds defining `U` is
active.  Comparing `m/(x+y)` with `(m - d·x²)/y`, the first is the smaller
exactly when `d·x·(x+y) ≤ m`.  On that branch — the *bulk* — the constraint
`(x+y)·y' < m` implies the other one, so the range of `y'` is a single initial
segment.  The complementary branch is the *small* part. -/

/-- **On the bulk branch, the first constraint implies the second.** -/
theorem bulk_second_of_first {m d x y y' : ℕ} (hx : 0 < x) (hy : 0 < y)
    (hbulk : d * x * (x + y) ≤ m) (h2 : (x + y) * y' < m) :
    y * y' + d * x * x < m := by
  have haa : 0 < x + y := by omega
  have key : (x + y) * (y * y' + d * x * x) < (x + y) * m := by
    have e1 : (x + y) * (y * y' + d * x * x)
        = y * ((x + y) * y') + x * (d * x * (x + y)) := by ring
    have h3 : y * ((x + y) * y') < y * m := by nlinarith
    have h4 : x * (d * x * (x + y)) ≤ x * m := Nat.mul_le_mul_left x hbulk
    have e2 : (x + y) * m = y * m + x * m := by ring
    omega
  exact Nat.lt_of_mul_lt_mul_left key

/-- On the bulk branch the range of `y'` is cut by `(x+y)·y' < m` alone. -/
theorem yBound_bulk {m d x y : ℕ} (hm : 0 < m) (hx : 0 < x) (hy : 0 < y)
    (hda : d * x * x < m) (hbulk : d * x * (x + y) ≤ m) :
    Finset.Ico 1 (yBound m d x y) = Finset.Ico 1 ((m - 1) / (x + y) + 1) := by
  ext y'
  rw [mem_gtRange hm (by omega) hy hda, Finset.mem_Ico, Nat.lt_succ_iff,
    Nat.le_div_iff_mul_le (by omega : 0 < x + y), Nat.mul_comm y' (x + y)]
  constructor
  · rintro ⟨h1, h2, -⟩
    exact ⟨h1, by omega⟩
  · rintro ⟨h1, h2⟩
    have h2' : (x + y) * y' < m := by omega
    exact ⟨h1, h2', bulk_second_of_first hx hy hbulk h2'⟩

/-- **The bulk / small split of the triple sum.** -/
theorem gtTriples_bulk_small (m d : ℕ) (f : ℕ → ℕ → ℕ → ℕ) :
    ∑ t ∈ gtTriples m d, f t.1 t.2.1 t.2.2
      = (∑ t ∈ (gtTriples m d).filter (fun t => d * t.1 * (t.1 + t.2.1) ≤ m),
          f t.1 t.2.1 t.2.2)
        + ∑ t ∈ (gtTriples m d).filter (fun t => ¬ (d * t.1 * (t.1 + t.2.1) ≤ m)),
            f t.1 t.2.1 t.2.2 :=
  (Finset.sum_filter_add_sum_filter_not _ _ _).symm

/-- **On the small branch, `2·d·x² > m`.**  This is the paper's observation that
`2x²` is bounded below by `m/d`, which is what makes the small part small. -/
theorem small_two_mul_gt {m d x y y' : ℕ} (h : (x, y, y') ∈ gtTriples m d)
    (hsmall : m < d * x * (x + y)) : m < 2 * (d * x * x) := by
  obtain ⟨⟨⟨-, -, hx2, -, -, -⟩, -⟩, -⟩ := mem_gtTriples.1 h
  nlinarith

/-! ## Counting an arithmetic progression

The divisibility condition `x ∣ m - y·y'` puts `y'` in a single residue class
modulo `x`, so within an interval of length `U` there are at most `U/x + 1` of
them.  This factor of `1/x` is what makes the small part `O(m^{3/2})`: without
it a crude count would be too large by exactly that factor. -/

/-- **Counting a residue class in an interval.** -/
theorem card_mod_filter_le {x U c : ℕ} (hx : 0 < x) :
    (((Finset.Ico 1 U).filter (fun x' => x' % x = c)).card) ≤ U / x + 1 := by
  classical
  have hmap : ∀ x' ∈ (Finset.Ico 1 U).filter (fun x' => x' % x = c),
      x' / x ∈ Finset.range (U / x + 1) := by
    intro x' hx'
    simp only [Finset.mem_filter, Finset.mem_Ico] at hx'
    simp only [Finset.mem_range, Nat.lt_succ_iff]
    exact Nat.div_le_div_right (by omega)
  have hinj : ∀ x'₁ ∈ (Finset.Ico 1 U).filter (fun x' => x' % x = c),
      ∀ x'₂ ∈ (Finset.Ico 1 U).filter (fun x' => x' % x = c), x'₁ / x = x'₂ / x → x'₁ = x'₂ := by
    intro x'₁ h₁ x'₂ h₂ heq
    simp only [Finset.mem_filter] at h₁ h₂
    have e₁ := Nat.div_add_mod x'₁ x
    have e₂ := Nat.div_add_mod x'₂ x
    rw [h₁.2] at e₁
    rw [h₂.2] at e₂
    rw [heq] at e₁
    omega
  calc (((Finset.Ico 1 U).filter (fun x' => x' % x = c)).card)
      ≤ (Finset.range (U / x + 1)).card := Finset.card_le_card_of_injOn _ hmap hinj
    _ = U / x + 1 := Finset.card_range _

/-- **The divisibility condition confines `y'` to one residue class.** -/
theorem card_dvd_filter_le {m x y U : ℕ} (hx : 0 < x) (hgcd : Nat.gcd x y = 1)
    (hU : ∀ x' ∈ Finset.Ico 1 U, y * x' ≤ m) :
    (((Finset.Ico 1 U).filter (fun x' => x ∣ (m - y * x'))).card) ≤ U / x + 1 := by
  classical
  rcases Finset.eq_empty_or_nonempty
      ((Finset.Ico 1 U).filter (fun x' => x ∣ (m - y * x'))) with he | ⟨x'₀, hx'₀⟩
  · rw [he]
    simp
  · refine le_trans (Finset.card_le_card ?_) (card_mod_filter_le (c := x'₀ % x) hx)
    intro x' hx'
    simp only [Finset.mem_filter] at hx' hx'₀ ⊢
    refine ⟨hx'.1, ?_⟩
    -- `x ∣ y * (x'₀ - x')` over `ℤ`, and `gcd x y = 1`, so `x' ≡ x'₀ mod x`
    have hle : y * x' ≤ m := hU x' hx'.1
    have hle₀ : y * x'₀ ≤ m := hU x'₀ hx'₀.1
    have hz : ((x : ℤ)) ∣ ((y : ℤ) * ((x'₀ : ℤ) - (x' : ℤ))) := by
      have h1 : ((x : ℤ)) ∣ ((m : ℤ) - (y : ℤ) * (x' : ℤ)) := by
        have := Int.natCast_dvd_natCast.2 hx'.2
        rwa [Nat.cast_sub hle, Nat.cast_mul] at this
      have h2 : ((x : ℤ)) ∣ ((m : ℤ) - (y : ℤ) * (x'₀ : ℤ)) := by
        have := Int.natCast_dvd_natCast.2 hx'₀.2
        rwa [Nat.cast_sub hle₀, Nat.cast_mul] at this
      have := dvd_sub h1 h2
      have heq : ((m : ℤ) - (y : ℤ) * (x' : ℤ)) - ((m : ℤ) - (y : ℤ) * (x'₀ : ℤ))
          = (y : ℤ) * ((x'₀ : ℤ) - (x' : ℤ)) := by ring
      rwa [heq] at this
    have hco : IsCoprime (x : ℤ) (y : ℤ) := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      simpa using hgcd
    have hdvd : ((x : ℤ)) ∣ ((x'₀ : ℤ) - (x' : ℤ)) := IsCoprime.dvd_of_dvd_mul_left hco hz
    have : x' ≡ x'₀ [MOD x] := (Nat.modEq_iff_dvd).2 hdvd
    exact this

/-! ## The small-part bound

On the small branch `d·x² > m/2`, so `m/x² < 2d` and the residue class meets the
range in at most `2d+2` points; each summand is at most `2·(m/x)`.  Summing over
`y < x` the factor `x` cancels the `1/x`, leaving `O(d·m)` per value of `x`, and
`x` ranges over at most `√(m/d)+1` values. -/

/-- **The per-pair bound on the small branch.** -/
theorem small_pair_le {m d x y : ℕ} (hx : 0 < x) (hy : 0 < y) (hgcd : Nat.gcd x y = 1)
    (hda : d * x * x < m) (haa : y < x) (hsmall : ¬ (d * x * (x + y) ≤ m)) :
    ∑ y' ∈ (Finset.Ico 1 (yBound m d x y)).filter (fun y' => x ∣ (m - y * y')),
        (d * x + (m - y * y') / x)
      ≤ (2 * d + 2) * (2 * (m / x)) := by
  have hm : 0 < m := by omega
  have haa0 : 0 < x + y := by omega
  -- every `y'` in range has `y * y' ≤ m`
  have hU : ∀ x' ∈ Finset.Ico 1 (yBound m d x y), y * x' ≤ m := by
    intro x' hx'
    obtain ⟨-, -, h3⟩ := (mem_gtRange hm haa0 hy hda).1 hx'
    omega
  -- the count is at most `2d + 2`
  have hsq : m < 2 * (d * x * x) := by nlinarith
  have hcard : (((Finset.Ico 1 (yBound m d x y)).filter
      (fun y' => x ∣ (m - y * y'))).card) ≤ 2 * d + 2 := by
    refine le_trans (card_dvd_filter_le hx hgcd hU) ?_
    have hx'1 : yBound m d x y ≤ (m - 1) / (x + y) + 1 := min_le_left _ _
    have hx'2 : yBound m d x y ≤ (m - 1) / x + 1 :=
      le_trans hx'1 (by
        have : (m - 1) / (x + y) ≤ (m - 1) / x := Nat.div_le_div_left (by omega) hx
        omega)
    have hx'3 : yBound m d x y / x ≤ ((m - 1) / x + 1) / x := Nat.div_le_div_right hx'2
    have hx'4 : ((m - 1) / x + 1) / x ≤ (m - 1) / (x * x) + 1 := by
      rw [← Nat.div_div_eq_div_mul]
      have h2 : ((m - 1) / x + 1) / x ≤ ((m - 1) / x + x) / x :=
        Nat.div_le_div_right (by omega)
      have h3 : ((m - 1) / x + x) / x = (m - 1) / x / x + 1 := Nat.add_div_right _ hx
      omega
    have hx'5 : (m - 1) / (x * x) ≤ 2 * d := by
      have heq : 2 * (d * x * x) = 2 * d * (x * x) := by ring
      have h1 : m - 1 ≤ 2 * d * (x * x) := by omega
      calc (m - 1) / (x * x) ≤ (2 * d * (x * x)) / (x * x) := Nat.div_le_div_right h1
        _ = 2 * d := Nat.mul_div_cancel _ (by positivity)
    omega
  -- every summand is at most `2 * (m / x)`
  have hterm : ∀ y' ∈ (Finset.Ico 1 (yBound m d x y)).filter (fun y' => x ∣ (m - y * y')),
      d * x + (m - y * y') / x ≤ 2 * (m / x) := by
    intro y' _
    have h1 : d * x ≤ m / x := by
      refine (Nat.le_div_iff_mul_le hx).2 ?_
      nlinarith
    have h2 : (m - y * y') / x ≤ m / x := Nat.div_le_div_right (by omega)
    omega
  calc ∑ y' ∈ (Finset.Ico 1 (yBound m d x y)).filter (fun y' => x ∣ (m - y * y')),
        (d * x + (m - y * y') / x)
      ≤ ∑ _y' ∈ (Finset.Ico 1 (yBound m d x y)).filter (fun y' => x ∣ (m - y * y')),
          2 * (m / x) := Finset.sum_le_sum hterm
    _ = (((Finset.Ico 1 (yBound m d x y)).filter
          (fun y' => x ∣ (m - y * y'))).card) * (2 * (m / x)) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ (2 * d + 2) * (2 * (m / x)) := Nat.mul_le_mul_right _ hcard

/-- **The small part is `O(m^{3/2}·√d)`.** -/
theorem small_part_le {m d : ℕ} (hm : 0 < m) (hd : 0 < d) :
    ∑ t ∈ (gtTriples m d).filter (fun t => ¬ (d * t.1 * (t.1 + t.2.1) ≤ m)),
        (d * t.1 + (m - t.2.1 * t.2.2) / t.1)
      ≤ (Nat.sqrt ((m - 1) / d) + 1) * ((2 * d + 2) * (2 * m)) := by
  classical
  rw [Finset.sum_filter,
    gtTriples_decompose hm (fun x y y' =>
      if ¬ (d * x * (x + y) ≤ m) then d * x + (m - y * y') / x else 0)]
  -- each pair contributes at most `(2d+2) · 2·(m/x)`
  have hpair : ∀ p ∈ (coprimePairs m).filter (fun p => d * p.1 * p.1 < m),
      (∑ y' ∈ (Finset.Ico 1 (yBound m d p.1 p.2)).filter (fun y' => p.1 ∣ (m - p.2 * y')),
          if ¬ (d * p.1 * (p.1 + p.2) ≤ m) then d * p.1 + (m - p.2 * y') / p.1 else 0)
        ≤ (2 * d + 2) * (2 * (m / p.1)) := by
    rintro ⟨x, y⟩ hp
    simp only [Finset.mem_filter] at hp
    obtain ⟨hpair', hda⟩ := hp
    obtain ⟨-, hx1, hx2, hgcd⟩ := mem_coprimePairs.1 hpair'
    by_cases hsmall : ¬ (d * x * (x + y) ≤ m)
    · simp only [hsmall, if_true]
      exact small_pair_le (by omega) hx1 hgcd hda hx2 hsmall
    · simp only [hsmall, if_false]
      simp
  refine le_trans (Finset.sum_le_sum hpair) ?_
  -- decompose the pairs by their first component
  rw [sum_coprimePairs_filter (m := m) (d := d)
    (g := fun x _ => (2 * d + 2) * (2 * (m / x)))]
  calc ∑ x ∈ (Finset.range (m + 1)).filter (fun x => d * x * x < m),
        ∑ _y ∈ (Finset.Ico 1 x).filter (fun y => Nat.gcd x y = 1),
          (2 * d + 2) * (2 * (m / x))
      ≤ ∑ _x ∈ (Finset.range (m + 1)).filter (fun x => d * x * x < m),
          (2 * d + 2) * (2 * m) := by
        refine Finset.sum_le_sum fun x hx => ?_
        rw [Finset.sum_const, smul_eq_mul]
        have hc : ((Finset.Ico 1 x).filter (fun y => Nat.gcd x y = 1)).card ≤ x := by
          calc ((Finset.Ico 1 x).filter (fun y => Nat.gcd x y = 1)).card
              ≤ (Finset.Ico 1 x).card := Finset.card_filter_le _ _
            _ = x - 1 := by simp
            _ ≤ x := Nat.sub_le _ _
        have hma : x * (m / x) ≤ m := Nat.mul_div_le m x
        calc ((Finset.Ico 1 x).filter (fun y => Nat.gcd x y = 1)).card
              * ((2 * d + 2) * (2 * (m / x)))
            ≤ x * ((2 * d + 2) * (2 * (m / x))) := Nat.mul_le_mul_right _ hc
          _ = (2 * d + 2) * (2 * (x * (m / x))) := by ring
          _ ≤ (2 * d + 2) * (2 * m) := by
              exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hma)
    _ = (((Finset.range (m + 1)).filter (fun x => d * x * x < m)).card)
          * ((2 * d + 2) * (2 * m)) := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ (Nat.sqrt ((m - 1) / d) + 1) * ((2 * d + 2) * (2 * m)) :=
        Nat.mul_le_mul_right _ (card_a_le hd)

/-! ## Towards the main term

The main term per pair is `(1/x)·∑_{1 ≤ y' < U} (A + B·y')` with the paper's
coefficients.  Evaluating that sum in closed form and substituting
`U = m/(x+y)`, `A = d·x + m/x`, `B = -y/x` gives

```
d·m/(x+y)  +  m²·[ 1/(x²(x+y)) - y/(2x²(x+y)²) ]  =  d·m/(x+y)  +  m²·cTerm(x,y),
```

by `cTerm_summand_eq`.  Summing over all coprime pairs gives `m²·C`, and over
`d ∣ n` with `m = n/d` gives `C·n²·∑_{d∣n} 1/d²` — Lemma 19. -/

/-- **The closed form of the main term.**  `∑_{1 ≤ x' < U} (A + B·x')`. -/
theorem sum_linear_Ico (A B : ℝ) : ∀ U : ℕ, 1 ≤ U →
    ∑ x' ∈ Finset.Ico 1 U, (A + B * (x' : ℝ))
      = A * ((U : ℝ) - 1) + B * (((U : ℝ) - 1) * (U : ℝ) / 2) := by
  intro U hU
  induction U, hU using Nat.le_induction with
  | base => simp
  | succ U hU ih =>
    rw [Finset.sum_Ico_succ_top hU, ih]
    push_cast
    ring

/-- **Pairs outside the bulk have large `x`.**  If `d·x·(x+y) > m` then
`2d·x² > m`, so `x > √(m/(2d))`.  This is what makes the truncation of the
series for `C` cost only `O(√(d/m))`. -/
theorem excluded_pair_large {m d x y : ℕ} (hy : 1 ≤ y) (haa : y < x)
    (h : m < d * x * (x + y)) : m < 2 * d * (x * x) := by
  nlinarith

/-- **Pairs with small `x` lie in the bulk.**  The contrapositive of
`excluded_pair_large`. -/
theorem bulk_of_small_a {m d x y : ℕ} (hy : 1 ≤ y) (haa : y < x)
    (h : 2 * d * (x * x) ≤ m) : d * x * (x + y) ≤ m := by
  nlinarith

/-- The cut-off `N = √(m/(2d))` puts every pair with `x ≤ N` in the bulk. -/
theorem bulk_of_le_sqrt {m d x y : ℕ} (hy : 1 ≤ y) (haa : y < x)
    (hx : x ≤ Nat.sqrt (m / (2 * d))) (hd : 0 < d) : d * x * (x + y) ≤ m := by
  refine bulk_of_small_a hy haa ?_
  have h1 : x * x ≤ m / (2 * d) := by
    have := Nat.sqrt_le' (m / (2 * d))
    calc x * x ≤ Nat.sqrt (m / (2 * d)) * Nat.sqrt (m / (2 * d)) :=
          Nat.mul_le_mul hx hx
      _ ≤ m / (2 * d) := by rw [← pow_two]; exact Nat.sqrt_le' _
  calc 2 * d * (x * x) ≤ 2 * d * (m / (2 * d)) := Nat.mul_le_mul_left _ h1
    _ ≤ m := Nat.mul_div_le m (2 * d)

/-! ## The floor analysis

The main term is evaluated at the natural-number bound `U`, but the paper's
computation substitutes the real value `V = m/(x+y)`.  The two differ, and the
discrepancy must be bounded.  It has an exact algebraic form: for the quadratic
`f(x) = A(x-1) + B(x-1)x/2`,

```
f(U) - f(V) = (U - V) · (A + (B/2)(U + V - 1)),
```

so with `|U - V| ≤ 1` — which is exactly the floor property — the discrepancy is
controlled by the coefficients. -/

/-- **The exact discrepancy of the quadratic main term.** -/
theorem quadratic_diff (A B U V : ℝ) :
    (A * (U - 1) + B * ((U - 1) * U / 2)) - (A * (V - 1) + B * ((V - 1) * V / 2))
      = (U - V) * (A + (B / 2) * (U + V - 1)) := by ring

/-- The floor is within `1` from below. -/
theorem lt_natCast_div_add_one {x y : ℕ} (hy : 0 < y) :
    (x : ℝ) / (y : ℝ) < ((x / y : ℕ) : ℝ) + 1 := by
  have hy' : (0 : ℝ) < (y : ℝ) := by exact_mod_cast hy
  rw [div_lt_iff₀ hy']
  have h1 : x < y * (x / y + 1) := by
    have h2 := Nat.div_add_mod x y
    have h3 := Nat.mod_lt x hy
    nlinarith
  have h4 : (x : ℝ) < ((y * (x / y + 1) : ℕ) : ℝ) := by exact_mod_cast h1
  push_cast at h4
  linarith

/-- **The floor is within `1` of the real quotient.** -/
theorem abs_natCast_div_sub_le_one {x y : ℕ} (hy : 0 < y) :
    |((x / y : ℕ) : ℝ) - (x : ℝ) / (y : ℝ)| ≤ 1 := by
  have h1 : ((x / y : ℕ) : ℝ) ≤ (x : ℝ) / (y : ℝ) := Nat.cast_div_le
  have h2 : (x : ℝ) / (y : ℝ) < ((x / y : ℕ) : ℝ) + 1 := lt_natCast_div_add_one hy
  rw [abs_le]
  constructor <;> linarith

/-- **The rounding term, in the paper's form.**

The paper compares the closed form at the *real* bound `V` — namely
`A·V + B·V²/2` — with the actual sum `∑_{1 ≤ y' < V} (A + B·y')`, and bounds the
difference by `|A| + |B·V|`.  Writing `K` for the largest admissible `y'`, so
that `K ≤ V < K+1` and the sum is `A·K + B·K(K+1)/2`, that is what is proved
here. -/
theorem main_term_vs_sum (A B V : ℝ) (K : ℕ) (hK : (K : ℝ) ≤ V) (hK1 : V ≤ (K : ℝ) + 1)
    (hV : 1 ≤ V) :
    |(A * V + B * V ^ 2 / 2) - (A * (K : ℝ) + B * ((K : ℝ) * ((K : ℝ) + 1)) / 2)|
      ≤ |A| + |B| * V := by
  have hKnn : (0 : ℝ) ≤ (K : ℝ) := by positivity
  have hdiff : (A * V + B * V ^ 2 / 2) - (A * (K : ℝ) + B * ((K : ℝ) * ((K : ℝ) + 1)) / 2)
      = A * (V - (K : ℝ)) + B / 2 * (V ^ 2 - (K : ℝ) ^ 2 - (K : ℝ)) := by ring
  rw [hdiff]
  have h1 : |V - (K : ℝ)| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have h2 : |V ^ 2 - (K : ℝ) ^ 2 - (K : ℝ)| ≤ 2 * V := by
    rw [abs_le]
    constructor <;> nlinarith
  calc |A * (V - (K : ℝ)) + B / 2 * (V ^ 2 - (K : ℝ) ^ 2 - (K : ℝ))|
      ≤ |A * (V - (K : ℝ))| + |B / 2 * (V ^ 2 - (K : ℝ) ^ 2 - (K : ℝ))| := abs_add_le _ _
    _ = |A| * |V - (K : ℝ)| + |B| / 2 * |V ^ 2 - (K : ℝ) ^ 2 - (K : ℝ)| := by
        rw [abs_mul, abs_mul, abs_div, abs_two]
    _ ≤ |A| * 1 + |B| / 2 * (2 * V) := by
        have hx := abs_nonneg A
        have hx' : (0 : ℝ) ≤ |B| / 2 := by positivity
        nlinarith
    _ = |A| + |B| * V := by ring

/-! ## The lower-order part

After substitution the main term carries a term `d·m/(x+y)`.  Summing it over
`y < x` gives at most `d·m` per value of `x` — the `x` choices of `y` cancel
the `1/x` again — and `x` ranges over at most `√((m-1)/d)+1` values, so the
whole thing is `O(m^{3/2}√d)`, the same order as the other errors. -/

/-- **The lower-order part of the main term.** -/
theorem lower_order_le {m d : ℕ} (hm : 0 < m) (hd : 0 < d) :
    ∑ p ∈ (coprimePairs m).filter (fun p => d * p.1 * (p.1 + p.2) ≤ m),
        (d : ℝ) * (m : ℝ) / ((p.1 : ℝ) + (p.2 : ℝ))
      ≤ ((Nat.sqrt ((m - 1) / d) : ℝ) + 1) * ((d : ℝ) * (m : ℝ)) := by
  have hsub : (coprimePairs m).filter (fun p => d * p.1 * (p.1 + p.2) ≤ m)
      ⊆ (coprimePairs m).filter (fun p => d * p.1 * p.1 < m) := by
    rintro ⟨x, y⟩ hp
    simp only [Finset.mem_filter] at hp ⊢
    obtain ⟨hmem, hbulk⟩ := hp
    obtain ⟨-, hx1, hx2, -⟩ := mem_coprimePairs.1 hmem
    exact ⟨hmem, by nlinarith⟩
  calc ∑ p ∈ (coprimePairs m).filter (fun p => d * p.1 * (p.1 + p.2) ≤ m),
        (d : ℝ) * (m : ℝ) / ((p.1 : ℝ) + (p.2 : ℝ))
      ≤ ∑ p ∈ (coprimePairs m).filter (fun p => d * p.1 * p.1 < m),
          (d : ℝ) * (m : ℝ) / ((p.1 : ℝ) + (p.2 : ℝ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)
    _ = ∑ x ∈ (Finset.range (m + 1)).filter (fun x => d * x * x < m),
          ∑ y ∈ (Finset.Ico 1 x).filter (fun y => Nat.gcd x y = 1),
            (d : ℝ) * (m : ℝ) / ((x : ℝ) + (y : ℝ)) :=
        sum_coprimePairs_filter (m := m) (d := d)
          (g := fun x y => (d : ℝ) * (m : ℝ) / ((x : ℝ) + (y : ℝ)))
    _ ≤ ∑ _x ∈ (Finset.range (m + 1)).filter (fun x => d * x * x < m), (d : ℝ) * (m : ℝ) := by
        refine Finset.sum_le_sum fun x hx => ?_
        rcases Nat.eq_zero_or_pos x with h0 | h0
        · subst h0
          simp
          positivity
        · have hx1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast h0
          have hcard := card_coprimeSecond_lt h0
          calc ∑ y ∈ (Finset.Ico 1 x).filter (fun y => Nat.gcd x y = 1),
                (d : ℝ) * (m : ℝ) / ((x : ℝ) + (y : ℝ))
              ≤ ∑ _y ∈ (Finset.Ico 1 x).filter (fun y => Nat.gcd x y = 1),
                  (d : ℝ) * (m : ℝ) / (x : ℝ) := by
                refine Finset.sum_le_sum fun y _ => ?_
                have hy0 : (0 : ℝ) ≤ (y : ℝ) := by positivity
                apply div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
            _ = (((Finset.Ico 1 x).filter (fun y => Nat.gcd x y = 1)).card : ℝ)
                  * ((d : ℝ) * (m : ℝ) / (x : ℝ)) := by
                rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ (x : ℝ) * ((d : ℝ) * (m : ℝ) / (x : ℝ)) := by
                refine mul_le_mul_of_nonneg_right hcard (by positivity)
            _ = (d : ℝ) * (m : ℝ) := by field_simp
    _ = ((((Finset.range (m + 1)).filter (fun x => d * x * x < m)).card : ℝ))
          * ((d : ℝ) * (m : ℝ)) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((Nat.sqrt ((m - 1) / d) : ℝ) + 1) * ((d : ℝ) * (m : ℝ)) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        have h := card_a_le (m := m) hd
        have hc : ((((Finset.range (m + 1)).filter (fun x => d * x * x < m)).card : ℝ))
            ≤ ((Nat.sqrt ((m - 1) / d) + 1 : ℕ) : ℝ) := by exact_mod_cast h
        push_cast at hc
        linarith

/-! ## Sanity checks -/

-- The `x'`-elimination, checked numerically.
#guard (List.range 22).all (fun m => let n := m + 1
  (∑ q ∈ quadruplesQ n, q.2.1) = ∑ t ∈ triples n, (n - t.2.1 * t.2.2) / t.1)
-- The triple sum, checked numerically.
#guard (List.range 18).all (fun m => let n := m + 1
  (∑ q ∈ quadruplesQ n, q.2.1)
    = ∑ d ∈ n.divisors, ∑ t ∈ coprimeTriples (n / d), (n / d - t.2.1 * t.2.2) / t.1)
-- The fully decomposed triple sum, checked numerically.
#guard (List.range 15).all (fun mm => let n := mm + 1
  (∑ q ∈ quadruplesQ n, q.2.1)
    = ∑ d ∈ n.divisors, ∑ p ∈ coprimePairs (n / d),
        ∑ y' ∈ (Finset.Ico 1 (bBound (n / d) p.1 p.2)).filter
          (fun y' => p.1 ∣ (n / d - p.2 * y')), (n / d - p.2 * y') / p.1)
-- The symmetrisation, checked numerically.
#guard (List.range 18).all (fun mm => let n := mm + 1
  (∑ q ∈ quadruplesQ n, q.2.1)
    = (∑ q ∈ (quadruplesQ n).filter (fun q => q.1 < q.2.1), (q.1 + q.2.1))
      + ∑ q ∈ (quadruplesQ n).filter (fun q => q.1 = q.2.1), q.1)
-- The small-part bound, checked numerically.
#guard (List.range 12).all (fun mm => let m := mm + 1
  (List.range 3).all (fun dd => let d := dd + 1
    (∑ t ∈ (gtTriples m d).filter (fun t => ¬ (d * t.1 * (t.1 + t.2.1) ≤ m)),
        (d * t.1 + (m - t.2.1 * t.2.2) / t.1))
      ≤ (Nat.sqrt ((m - 1) / d) + 1) * ((2 * d + 2) * (2 * m))))
-- The restricted triple sum, checked numerically.
#guard (List.range 14).all (fun mm => let n := mm + 1
  (∑ q ∈ (quadruplesQ n).filter (fun q => q.1 < q.2.1), (q.1 + q.2.1))
    = ∑ d ∈ n.divisors, ∑ t ∈ gtTriples (n / d) d,
        (d * t.1 + (n / d - t.2.1 * t.2.2) / t.1))
-- `∑ gcd(n,k) ≤ n · d(n)`.
#guard (List.range 30).all (fun m => let n := m + 1
  (∑ k ∈ allShifts n, Nat.gcd n k) ≤ n * n.divisors.card)

end BlockCycleRotation
