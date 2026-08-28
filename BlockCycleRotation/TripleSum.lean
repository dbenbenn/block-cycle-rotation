/-
# The triple sum of section 4

After (eq. heilbron), Blomer--Bux rewrite the lattice point count as a triple
sum.  Ordering the pairs `(a, a')` by `d = gcd(a, a')`, which necessarily
divides `n`, and eliminating `b` via `b = n/(d·a) - a'·b'/a`, they obtain

```
Q(n) = ∑_{d ∣ n} ∑_{a > a' ≥ 1, gcd(a,a') = 1} ∑_{b'} ( n/(d·a) − a'·b'/a + d·a )
         + O(n^{1+ε})
```

where `b'` runs over `1 ≤ b' < U` subject to `n/d ≡ a'·b' (mod a)`, with
`U = min( n/(d(a+a')), (n/d − d·a²)/a' )`.

The innermost sum is a linear function summed over an arithmetic progression —
exactly the shape estimated in `Progression.lean`.  This file records that: the
general estimate applies to the paper's summand verbatim, with

  `A = n/(d·a) + d·a`  and  `B = −a'/a`.

What remains for Theorem 13 is the two outer layers — the sum over `a > a' ≥ 1`
coprime, and the Möbius-inverted sum over `d ∣ n` — together with collecting the
resulting pieces `G₁ + G₂ + G₃` into `O(n^{3/2+ε})`.  Every ingredient those need
is proved: this estimate, `exists_card_divisors_le`, and Mathlib's Möbius
inversion.
-/

import BlockCycleRotation.Continuant

namespace BlockCycleRotation

open Real

/-- **The inner sum of the triple sum.**

For fixed `d`, `a`, `a'`, summing the paper's linear function over an
arithmetic progression modulo `a` differs from its expected value by
`O(log a)`.  This is `sum_ap_sub_main_le_log` at the paper's coefficients. -/
theorem inner_sum_sub_main_le (n d a a' : ℕ) (ha : 0 < a) (c : ℤ) (U : ℕ) :
    ‖(∑ b ∈ Finset.Ico 1 U, if (a : ℤ) ∣ ((b : ℤ) - c) then
          (((n : ℂ) / (d * a) + d * a) + (-(a' : ℂ) / a) * b) else 0)
        - (1 / (a : ℂ)) * ∑ b ∈ Finset.Ico 1 U,
            (((n : ℂ) / (d * a) + d * a) + (-(a' : ℂ) / a) * b)‖
      ≤ (‖((n : ℂ) / (d * a) + d * a)‖ + ‖(-(a' : ℂ) / a)‖ * (U - 1 : ℕ))
          * (1 + Real.log a) :=
  sum_ap_sub_main_le_log ha c _ _ U

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

/-! ## Eliminating `b`

The paper solves `n = a·b + a'·b'` for `b`, turning the quadruples into triples
`(a, a', b')`.  The condition `b > b'` becomes `(a + a')·b' < n`, and `b` being
an integer becomes `a ∣ n - a'·b'` — the congruence `n ≡ a'b' (mod a)`. -/

/-- The triples `(a, a', b')` of the triple sum. -/
def triples (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1)) ×ˢ (Finset.range (n + 1))).filter
    (fun t => 1 ≤ t.2.1 ∧ t.2.1 < t.1 ∧ 1 ≤ t.2.2 ∧ (t.1 + t.2.1) * t.2.2 < n
      ∧ t.1 ∣ (n - t.2.1 * t.2.2))

theorem mem_triples {n a a' b' : ℕ} :
    (a, a', b') ∈ triples n ↔
      (a ≤ n ∧ a' ≤ n ∧ b' ≤ n) ∧ 1 ≤ a' ∧ a' < a ∧ 1 ≤ b'
        ∧ (a + a') * b' < n ∧ a ∣ (n - a' * b') := by
  simp [triples, Finset.mem_filter, Finset.mem_product, and_assoc]

/-- **The `b`-elimination.**  `Q(n)` as a sum over triples. -/
theorem sum_snd_quadruplesQ_eq_triples {n : ℕ} (hn : 0 < n) :
    ∑ q ∈ quadruplesQ n, q.2.1 = ∑ t ∈ triples n, (n - t.2.1 * t.2.2) / t.1 := by
  refine Finset.sum_bij'
    (i := fun q _ => (q.1, q.2.2.1, q.2.2.2))
    (j := fun t _ => (t.1, (n - t.2.1 * t.2.2) / t.1, t.2.1, t.2.2)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨a, b, a', b'⟩ hq
    obtain ⟨⟨hab, hbb, ha'b, hb'b⟩, ha1, ha2, hb1, hb2, hsum⟩ := mem_quadruplesQ.1 hq
    have hdvd : a ∣ (n - a' * b') := ⟨b, by omega⟩
    have hlt : (a + a') * b' < n := by nlinarith
    show (a, a', b') ∈ triples n
    rw [mem_triples]
    exact ⟨⟨hab, ha'b, hb'b⟩, ha1, ha2, hb1, hlt, hdvd⟩
  · rintro ⟨a, a', b'⟩ ht
    obtain ⟨⟨han, ha'n, hb'n⟩, ha1, ha2, hb1, hlt, hdvd⟩ := mem_triples.1 ht
    have ha : 0 < a := by omega
    have hab : a * ((n - a' * b') / a) = n - a' * b' := Nat.mul_div_cancel' hdvd
    have hle : a' * b' ≤ n := by nlinarith
    have hsum : n = a * ((n - a' * b') / a) + a' * b' := by omega
    have hbb : b' < (n - a' * b') / a := by
      have h1 : a * b' < a * ((n - a' * b') / a) := by
        rw [hab]; nlinarith
      exact Nat.lt_of_mul_lt_mul_left h1
    show (a, (n - a' * b') / a, a', b') ∈ quadruplesQ n
    rw [mem_quadruplesQ]
    exact ⟨quadruple_le ha1 ha2 hb1 hbb hsum, ha1, ha2, hb1, hbb, hsum⟩
  · rintro ⟨a, b, a', b'⟩ hq
    obtain ⟨-, ha1, ha2, hb1, hb2, hsum⟩ := mem_quadruplesQ.1 hq
    have ha : 0 < a := by omega
    have h : n - a' * b' = a * b := by omega
    show (a, (n - a' * b') / a, a', b') = (a, b, a', b')
    rw [h, Nat.mul_div_cancel_left _ ha]
  · rintro ⟨a, a', b'⟩ _
    rfl
  · rintro ⟨a, b, a', b'⟩ hq
    obtain ⟨-, ha1, ha2, hb1, hb2, hsum⟩ := mem_quadruplesQ.1 hq
    have ha : 0 < a := by omega
    have h : n - a' * b' = a * b := by omega
    show b = (n - a' * b') / a
    rw [h, Nat.mul_div_cancel_left _ ha]

/-! ## The triple sum

Combining the divisor layer `Q(n) = ∑_{d ∣ n} R(n/d)` with the `b`-elimination
applied to each `R(n/d)` gives the paper's triple sum: over divisors `d ∣ n`,
over coprime pairs `a > a' ≥ 1`, and over `b'` in an arithmetic progression. -/

/-- The triples with `gcd(a,a') = 1`. -/
def coprimeTriples (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (triples n).filter (fun t => Nat.gcd t.1 t.2.1 = 1)

theorem mem_coprimeTriples {n a a' b' : ℕ} :
    (a, a', b') ∈ coprimeTriples n ↔
      ((a ≤ n ∧ a' ≤ n ∧ b' ≤ n) ∧ 1 ≤ a' ∧ a' < a ∧ 1 ≤ b'
        ∧ (a + a') * b' < n ∧ a ∣ (n - a' * b')) ∧ Nat.gcd a a' = 1 := by
  simp [coprimeTriples, Finset.mem_filter, mem_triples]

/-- The `b`-elimination for the coprime quadruples. -/
theorem sum_snd_quadruplesAll_eq {n : ℕ} (hn : 0 < n) :
    ∑ q ∈ quadruplesAll n, q.2.1
      = ∑ t ∈ coprimeTriples n, (n - t.2.1 * t.2.2) / t.1 := by
  refine Finset.sum_bij'
    (i := fun q _ => (q.1, q.2.2.1, q.2.2.2))
    (j := fun t _ => (t.1, (n - t.2.1 * t.2.2) / t.1, t.2.1, t.2.2)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨a, b, a', b'⟩ hq
    obtain ⟨⟨hab, hbb, ha'b, hb'b⟩, ha1, ha2, hb1, hb2, hgcd, hsum⟩ := mem_quadruplesAll.1 hq
    have hdvd : a ∣ (n - a' * b') := ⟨b, by omega⟩
    have hlt : (a + a') * b' < n := by nlinarith
    show (a, a', b') ∈ coprimeTriples n
    rw [mem_coprimeTriples]
    exact ⟨⟨⟨hab, ha'b, hb'b⟩, ha1, ha2, hb1, hlt, hdvd⟩, hgcd⟩
  · rintro ⟨a, a', b'⟩ ht
    obtain ⟨⟨⟨han, ha'n, hb'n⟩, ha1, ha2, hb1, hlt, hdvd⟩, hgcd⟩ := mem_coprimeTriples.1 ht
    have ha : 0 < a := by omega
    have hab : a * ((n - a' * b') / a) = n - a' * b' := Nat.mul_div_cancel' hdvd
    have hle : a' * b' ≤ n := by nlinarith
    have hsum : n = a * ((n - a' * b') / a) + a' * b' := by omega
    have hbb : b' < (n - a' * b') / a := by
      have h1 : a * b' < a * ((n - a' * b') / a) := by rw [hab]; nlinarith
      exact Nat.lt_of_mul_lt_mul_left h1
    show (a, (n - a' * b') / a, a', b') ∈ quadruplesAll n
    rw [mem_quadruplesAll]
    exact ⟨quadruple_le ha1 ha2 hb1 hbb hsum, ha1, ha2, hb1, hbb, hgcd, hsum⟩
  · rintro ⟨a, b, a', b'⟩ hq
    obtain ⟨-, ha1, ha2, hb1, hb2, -, hsum⟩ := mem_quadruplesAll.1 hq
    have ha : 0 < a := by omega
    have h : n - a' * b' = a * b := by omega
    show (a, (n - a' * b') / a, a', b') = (a, b, a', b')
    rw [h, Nat.mul_div_cancel_left _ ha]
  · rintro ⟨a, a', b'⟩ _
    rfl
  · rintro ⟨a, b, a', b'⟩ hq
    obtain ⟨-, ha1, ha2, hb1, hb2, -, hsum⟩ := mem_quadruplesAll.1 hq
    have ha : 0 < a := by omega
    have h : n - a' * b' = a * b := by omega
    show b = (n - a' * b') / a
    rw [h, Nat.mul_div_cancel_left _ ha]

/-- **The triple sum.**  `Q(n)` as a sum over divisors `d ∣ n`, coprime pairs
`a > a' ≥ 1`, and `b'` subject to `(a+a')b' < n/d` and `n/d ≡ a'b' (mod a)`. -/
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

The triple sum's divisibility condition `a ∣ m - a'·b'` is, because
`gcd(a,a') = 1`, a condition on `b'` modulo `a` — the shape the estimate of
`Progression.lean` requires.  This produces the residue `c` explicitly from
Bézout. -/

/-- With `gcd(a,a') = 1`, the congruence `a ∣ m - a'·b'` is `b' ≡ c (mod a)` for
a residue `c` depending only on `a`, `a'` and `m`. -/
theorem exists_residue {a a' m : ℕ} (hgcd : Nat.gcd a a' = 1) :
    ∃ c : ℤ, ∀ b : ℤ, ((a : ℤ) ∣ ((m : ℤ) - a' * b)) ↔ ((a : ℤ) ∣ (b - c)) := by
  have hco : IsCoprime (a : ℤ) (a' : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa using hgcd
  obtain ⟨u, v, huv⟩ := id hco
  -- `u * a + v * a' = 1`, so `v * m` inverts `a'` against `m`
  refine ⟨v * m, fun b => ?_⟩
  have hkey : (m : ℤ) - a' * b = ((m : ℤ) - a' * (v * m)) - a' * (b - v * m) := by ring
  have hdvd1 : (a : ℤ) ∣ ((m : ℤ) - a' * (v * m)) := by
    refine ⟨u * m, ?_⟩
    have : (a' : ℤ) * (v * m) = (1 - u * a) * m := by
      rw [← huv]; ring
    rw [this]; ring
  constructor
  · intro h
    rw [hkey] at h
    have h2 : (a : ℤ) ∣ (a' : ℤ) * (b - v * m) := (dvd_sub_right hdvd1).1 h
    exact IsCoprime.dvd_of_dvd_mul_left hco h2
  · intro h
    rw [hkey]
    exact dvd_sub hdvd1 (Dvd.dvd.mul_left h _)

/-- **The inner sum of the triple sum, as an arithmetic-progression sum.**

The natural-number inner sum `∑ (m - a'b')/a`, taken over `b'` satisfying the
divisibility condition, is the real sum of the linear function
`m/a - (a'/a)·b'` over an arithmetic progression modulo `a` — the exact shape
`sum_ap_sub_main_le_log` estimates. -/
theorem inner_sum_nat_eq {m a a' : ℕ} (ha : 0 < a) (hgcd : Nat.gcd a a' = 1) :
    ∃ c : ℤ, ∀ U : ℕ, (∀ b' ∈ Finset.Ico 1 U, a' * b' ≤ m) →
      ((∑ b' ∈ (Finset.Ico 1 U).filter (fun b' => a ∣ (m - a' * b')),
          (m - a' * b') / a : ℕ) : ℝ)
        = ∑ b' ∈ Finset.Ico 1 U,
            (if (a : ℤ) ∣ ((b' : ℤ) - c) then ((m : ℝ) / a - (a' : ℝ) / a * b') else 0) := by
  obtain ⟨c, hc⟩ := exists_residue (m := m) hgcd
  refine ⟨c, fun U hU => ?_⟩
  rw [Finset.sum_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun b' hb' => ?_
  have hle : a' * b' ≤ m := hU b' hb'
  -- the two divisibility conditions agree
  have hiff : (a ∣ (m - a' * b')) ↔ ((a : ℤ) ∣ ((b' : ℤ) - c)) := by
    rw [← hc (b' : ℤ)]
    constructor
    · intro h
      have : ((a : ℤ)) ∣ (((m - a' * b' : ℕ)) : ℤ) := Int.natCast_dvd_natCast.2 h
      rwa [Nat.cast_sub hle, Nat.cast_mul] at this
    · intro h
      have h2 : ((a : ℤ)) ∣ (((m - a' * b' : ℕ)) : ℤ) := by
        rwa [Nat.cast_sub hle, Nat.cast_mul]
      exact Int.natCast_dvd_natCast.1 h2
  by_cases hd : a ∣ (m - a' * b')
  · rw [if_pos hd, if_pos (hiff.1 hd)]
    have hmul : a * ((m - a' * b') / a) = m - a' * b' := Nat.mul_div_cancel' hd
    have hreal : ((a : ℝ)) * (((m - a' * b') / a : ℕ) : ℝ) = (m : ℝ) - (a' : ℝ) * b' := by
      have := congrArg (Nat.cast : ℕ → ℝ) hmul
      push_cast [Nat.cast_sub hle] at this
      linarith
    have hane : ((a : ℝ)) ≠ 0 := by positivity
    field_simp at hreal ⊢
    linarith
  · rw [if_neg hd, if_neg (fun h => hd (hiff.2 h))]
    simp

/-! ## Decomposing the triple sum by pairs

The triples split as a pair `(a, a')` together with `b'` ranging over an initial
segment cut by `(a + a')·b' < m` and filtered by the divisibility condition.
After this the innermost sum is literally the arithmetic-progression sum of
`inner_sum_nat_eq`. -/

/-- The bound on `b'` for a given pair. -/
def bBound (m a a' : ℕ) : ℕ := (m - 1) / (a + a') + 1

theorem mem_bRange {m a a' b' : ℕ} (hm : 0 < m) (ha : 0 < a + a') :
    b' ∈ Finset.Ico 1 (bBound m a a') ↔ 1 ≤ b' ∧ (a + a') * b' < m := by
  rw [Finset.mem_Ico, bBound, Nat.lt_succ_iff, Nat.le_div_iff_mul_le ha,
    Nat.mul_comm b' (a + a')]
  omega

/-- The coprime pairs `a > a' ≥ 1`. -/
def coprimePairs (m : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (m + 1)) ×ˢ (Finset.range (m + 1))).filter
    (fun p => 1 ≤ p.2 ∧ p.2 < p.1 ∧ Nat.gcd p.1 p.2 = 1)

theorem mem_coprimePairs {m a a' : ℕ} :
    (a, a') ∈ coprimePairs m ↔ (a ≤ m ∧ a' ≤ m) ∧ 1 ≤ a' ∧ a' < a ∧ Nat.gcd a a' = 1 := by
  simp [coprimePairs, Finset.mem_filter, Finset.mem_product, and_assoc]

/-- **The triple sum, decomposed by pairs.** -/
theorem coprimeTriples_decompose {m : ℕ} (hm : 0 < m) (f : ℕ → ℕ → ℕ → ℕ) :
    ∑ t ∈ coprimeTriples m, f t.1 t.2.1 t.2.2
      = ∑ p ∈ coprimePairs m, ∑ b' ∈ (Finset.Ico 1 (bBound m p.1 p.2)).filter
          (fun b' => p.1 ∣ (m - p.2 * b')), f p.1 p.2 b' := by
  rw [Finset.sum_sigma']
  refine Finset.sum_bij'
    (i := fun t _ => (⟨(t.1, t.2.1), t.2.2⟩ : (_ : ℕ × ℕ) × ℕ))
    (j := fun p _ => (p.1.1, p.1.2, p.2)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨a, a', b'⟩ ht
    obtain ⟨⟨⟨han, ha'n, hb'n⟩, ha1, ha2, hb1, hlt, hdvd⟩, hgcd⟩ := mem_coprimeTriples.1 ht
    have ha : 0 < a + a' := by omega
    simp only [Finset.mem_sigma, Finset.mem_filter]
    exact ⟨mem_coprimePairs.2 ⟨⟨han, ha'n⟩, ha1, ha2, hgcd⟩,
      (mem_bRange hm ha).2 ⟨hb1, hlt⟩, hdvd⟩
  · rintro ⟨⟨a, a'⟩, b'⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_filter] at hp
    obtain ⟨hpair, hb, hdvd⟩ := hp
    obtain ⟨⟨han, ha'n⟩, ha1, ha2, hgcd⟩ := mem_coprimePairs.1 hpair
    have ha : 0 < a + a' := by omega
    obtain ⟨hb1, hlt⟩ := (mem_bRange hm ha).1 hb
    have hb'n : b' ≤ m := by nlinarith
    show (a, a', b') ∈ coprimeTriples m
    rw [mem_coprimeTriples]
    exact ⟨⟨⟨han, ha'n, hb'n⟩, ha1, ha2, hb1, hlt, hdvd⟩, hgcd⟩
  · rintro ⟨a, a', b'⟩ _
    rfl
  · rintro ⟨⟨a, a'⟩, b'⟩ _
    rfl
  · rintro ⟨a, a', b'⟩ _
    rfl

/-- **The triple sum in estimable form.**

`Q(n)` as a sum over divisors `d ∣ n`, coprime pairs `(a, a')`, and `b'` in an
initial segment filtered by the divisibility condition.  By `inner_sum_nat_eq`
the innermost sum is an arithmetic-progression sum of a linear function, which
`inner_sum_sub_main_le` estimates. -/
theorem Q_eq_tripleSum_decomposed {n : ℕ} (hn : 0 < n) :
    ∑ q ∈ quadruplesQ n, q.2.1
      = ∑ d ∈ n.divisors, ∑ p ∈ coprimePairs (n / d),
          ∑ b' ∈ (Finset.Ico 1 (bBound (n / d) p.1 p.2)).filter
            (fun b' => p.1 ∣ (n / d - p.2 * b')), (n / d - p.2 * b') / p.1 := by
  rw [Q_eq_tripleSum hn]
  refine Finset.sum_congr rfl fun d hd => ?_
  obtain ⟨hdn, -⟩ := Nat.mem_divisors.1 hd
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
  have hm : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hn hdn) hd0
  exact coprimeTriples_decompose hm (fun a a' b' => (n / d - a' * b') / a)

/-! ## Symmetrisation

Following the paper: `Q(n) = ½ ∑ (b + a)`, and the involution swapping the two
halves pairs the quadruples with `b > a` against those with `b < a`, leaving the
diagonal `a = b`.  So

  `Q(n) = ∑_{b > a} (a + b) + ∑_{a = b} a`,

exactly (the diagonal term is what the paper discards as `O(n^{1+ε})`).  The
restriction `b > a` is what will bound `a` by about `√n` in the estimates. -/

/-- `quadruplesQ` is symmetric under swapping the two halves. -/
theorem mem_quadruplesQ_swap {n a b a' b' : ℕ} (h : (a, b, a', b') ∈ quadruplesQ n) :
    (b, a, b', a') ∈ quadruplesQ n := by
  rw [mem_quadruplesQ] at h ⊢
  obtain ⟨⟨h1, h2, h3, h4⟩, h5, h6, h7, h8, h9⟩ := h
  exact ⟨⟨h2, h1, h4, h3⟩, h7, h8, h5, h6, by rw [h9]; ring⟩

/-- Summing `a` over `quadruplesQ` equals summing `b`. -/
theorem sum_fst_eq_sum_snd_Q (n : ℕ) :
    ∑ q ∈ quadruplesQ n, q.1 = ∑ q ∈ quadruplesQ n, q.2.1 := by
  refine Finset.sum_bij'
    (i := fun q _ => (q.2.1, q.1, q.2.2.2, q.2.2.1))
    (j := fun q _ => (q.2.1, q.1, q.2.2.2, q.2.2.1)) ?_ ?_ ?_ ?_ ?_ <;>
    rintro ⟨a, b, a', b'⟩ hq
  · exact mem_quadruplesQ_swap hq
  · exact mem_quadruplesQ_swap hq
  · rfl
  · rfl
  · rfl

/-- The involution matches the quadruples with `b < a` against those with `b > a`. -/
theorem sum_gt_eq_sum_lt (n : ℕ) :
    ∑ q ∈ (quadruplesQ n).filter (fun q => q.2.1 < q.1), (q.1 + q.2.1)
      = ∑ q ∈ (quadruplesQ n).filter (fun q => q.1 < q.2.1), (q.1 + q.2.1) := by
  refine Finset.sum_bij'
    (i := fun q _ => (q.2.1, q.1, q.2.2.2, q.2.2.1))
    (j := fun q _ => (q.2.1, q.1, q.2.2.2, q.2.2.1)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨a, b, a', b'⟩ hq
    simp only [Finset.mem_filter] at hq ⊢
    exact ⟨mem_quadruplesQ_swap hq.1, hq.2⟩
  · rintro ⟨a, b, a', b'⟩ hq
    simp only [Finset.mem_filter] at hq ⊢
    exact ⟨mem_quadruplesQ_swap hq.1, hq.2⟩
  · rintro ⟨a, b, a', b'⟩ _
    rfl
  · rintro ⟨a, b, a', b'⟩ _
    rfl
  · rintro ⟨a, b, a', b'⟩ _
    exact Nat.add_comm _ _

/-- **The symmetrisation.**  `Q(n)` splits into the part with `b > a` and the
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

On the diagonal `a = b` we have `n = a² + a'b'`, so `a ≤ √n` and `a'` divides
`n - a²`; the quadruple is determined by `(a, a')`.  Counting gives
`√n · ∑_{a ≤ √n} d(n - a²)`, which the divisor bound makes `O(n^{1+ε})`. -/

theorem diag_card_le {n : ℕ} (hn : 0 < n) :
    ((quadruplesQ n).filter (fun q => q.1 = q.2.1)).card
      ≤ ∑ a ∈ Finset.range (Nat.sqrt n + 1), (n - a * a).divisors.card := by
  rw [← Finset.card_sigma]
  refine Finset.card_le_card_of_injOn
    (fun q => (⟨q.1, q.2.2.1⟩ : (_ : ℕ) × ℕ)) ?_ ?_
  · rintro ⟨a, b, a', b'⟩ hq
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hq
    obtain ⟨hmem, hab⟩ := hq
    obtain ⟨-, ha1, ha2, hb1, hb2, hsum⟩ := mem_quadruplesQ.1 hmem
    have hba : b = a := hab.symm
    subst hba
    have hbb : 1 ≤ a' * b' := Nat.one_le_iff_ne_zero.2 (by positivity)
    have hlt : b * b < n := by omega
    have hsq : b ≤ Nat.sqrt n := Nat.le_sqrt.2 (by omega)
    have hdvd : a' ∣ n - b * b := ⟨b', by omega⟩
    have hne : n - b * b ≠ 0 := by omega
    simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_range, Nat.mem_divisors]
    exact ⟨Nat.lt_succ_of_le hsq, hdvd, hne⟩
  · rintro ⟨a, b, a', b'⟩ hq ⟨c, e, c', e'⟩ hr heq
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hq hr
    obtain ⟨hmem, hab⟩ := hq
    obtain ⟨hmem2, hce⟩ := hr
    obtain ⟨-, ha1, ha2, hb1, hb2, hsum⟩ := mem_quadruplesQ.1 hmem
    obtain ⟨-, hc1, hc2, he1, he2, hsum2⟩ := mem_quadruplesQ.1 hmem2
    simp only [Sigma.mk.injEq] at heq
    obtain ⟨h1, h2⟩ := heq
    subst h1
    have h2' : a' = c' := eq_of_heq h2
    subst h2'
    have hb : b = a := hab.symm
    have he : e = a := hce.symm
    subst hb
    subst he
    have : a' * b' = a' * e' := by omega
    have : b' = e' := Nat.eq_of_mul_eq_mul_left (by omega) this
    subst this
    rfl

theorem sum_diag_le {n : ℕ} (hn : 0 < n) :
    ∑ q ∈ (quadruplesQ n).filter (fun q => q.1 = q.2.1), q.1
      ≤ Nat.sqrt n * ∑ a ∈ Finset.range (Nat.sqrt n + 1), (n - a * a).divisors.card := by
  have hterm : ∀ q ∈ (quadruplesQ n).filter (fun q => q.1 = q.2.1), q.1 ≤ Nat.sqrt n := by
    rintro ⟨a, b, a', b'⟩ hq
    simp only [Finset.mem_filter] at hq
    obtain ⟨hmem, hab⟩ := hq
    obtain ⟨-, ha1, ha2, hb1, hb2, hsum⟩ := mem_quadruplesQ.1 hmem
    have hba : b = a := hab.symm
    subst hba
    have hbb : 1 ≤ a' * b' := Nat.one_le_iff_ne_zero.2 (by positivity)
    have hsq : b ≤ Nat.sqrt n := Nat.le_sqrt.2 (by omega)
    exact hsq
  calc ∑ q ∈ (quadruplesQ n).filter (fun q => q.1 = q.2.1), q.1
      ≤ ∑ _q ∈ (quadruplesQ n).filter (fun q => q.1 = q.2.1), Nat.sqrt n :=
        Finset.sum_le_sum hterm
    _ = ((quadruplesQ n).filter (fun q => q.1 = q.2.1)).card * Nat.sqrt n := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ (∑ a ∈ Finset.range (Nat.sqrt n + 1), (n - a * a).divisors.card) * Nat.sqrt n :=
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
  have hterm : ∀ a ∈ Finset.range (Nat.sqrt n + 1),
      (((n - a * a).divisors.card : ℕ) : ℝ) ≤ C0 * (n : ℝ) ^ ε := by
    intro a _
    rcases Nat.eq_zero_or_pos (n - a * a) with h0 | h0
    · rw [h0]
      simp
      positivity
    · refine (hCd _ h0.ne').trans ?_
      have hle : ((n - a * a : ℕ) : ℝ) ≤ (n : ℝ) := by
        have : (n - a * a : ℕ) ≤ n := Nat.sub_le _ _
        exact_mod_cast this
      have := Real.rpow_le_rpow (by positivity) hle hε.le
      nlinarith
  have hS : ((∑ a ∈ Finset.range (Nat.sqrt n + 1), (n - a * a).divisors.card : ℕ) : ℝ)
      ≤ ((Nat.sqrt n : ℝ) + 1) * (C0 * (n : ℝ) ^ ε) := by
    push_cast
    calc ∑ a ∈ Finset.range (Nat.sqrt n + 1), (((n - a * a).divisors.card : ℕ) : ℝ)
        ≤ ∑ _a ∈ Finset.range (Nat.sqrt n + 1), C0 * (n : ℝ) ^ ε :=
          Finset.sum_le_sum hterm
      _ = ((Nat.sqrt n : ℝ) + 1) * (C0 * (n : ℝ) ^ ε) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  -- the natural-number bound
  have hnat := sum_diag_le hn
  have hcast : ((∑ q ∈ (quadruplesQ n).filter (fun q => q.1 = q.2.1), q.1 : ℕ) : ℝ)
      ≤ (Nat.sqrt n : ℝ)
        * ((∑ a ∈ Finset.range (Nat.sqrt n + 1), (n - a * a).divisors.card : ℕ) : ℝ) := by
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
      * ((∑ a ∈ Finset.range (Nat.sqrt n + 1), (n - a * a).divisors.card : ℕ) : ℝ)
      ≤ (Nat.sqrt n : ℝ) * (((Nat.sqrt n : ℝ) + 1) * (C0 * (n : ℝ) ^ ε)) :=
    mul_le_mul_of_nonneg_left hS hsqnn
  nlinarith [hcast, hmid, hsq1, hsq2, hnε, hC0.le]

/-! ## Carrying `b > a` through the classification

Classifying the symmetrised sum by `d = gcd(a,a')` turns the restriction
`b > a` into the paper's `b > d·a`, since `a = d·a₁`. -/

/-- The coprime quadruples of `m` with `b > d·a`. -/
def quadGT (m d : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  (quadruplesAll m).filter (fun q => d * q.1 < q.2.1)

theorem mem_quadGT {m d a b a' b' : ℕ} :
    (a, b, a', b') ∈ quadGT m d ↔
      ((a ≤ m ∧ b ≤ m ∧ a' ≤ m ∧ b' ≤ m) ∧ 1 ≤ a' ∧ a' < a ∧ 1 ≤ b' ∧ b' < b
        ∧ Nat.gcd a a' = 1 ∧ m = a * b + a' * b') ∧ d * a < b := by
  simp [quadGT, Finset.mem_filter, mem_quadruplesAll]

/-- **The symmetrised sum, classified by `gcd(a,a')`.** -/
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
  · rintro ⟨a, b, a', b'⟩ hq
    simp only [Finset.mem_filter] at hq
    obtain ⟨hmem, hab⟩ := hq
    obtain ⟨-, ha1, ha2, hb1, hb2, hsum⟩ := mem_quadruplesQ.1 hmem
    have hd : 0 < Nat.gcd a a' := Nat.gcd_pos_of_pos_left _ (by omega)
    have hda : Nat.gcd a a' ∣ a := Nat.gcd_dvd_left _ _
    have hda' : Nat.gcd a a' ∣ a' := Nat.gcd_dvd_right _ _
    have hdn : Nat.gcd a a' ∣ n := by
      rw [hsum]
      exact Dvd.dvd.add (Dvd.dvd.mul_right hda b) (Dvd.dvd.mul_right hda' b')
    have hnd : n / Nat.gcd a a'
        = a / Nat.gcd a a' * b + a' / Nat.gcd a a' * b' := by
      rw [Nat.div_eq_iff_eq_mul_left hd hdn, hsum, Nat.add_mul, Nat.mul_right_comm,
        Nat.mul_right_comm (a' / Nat.gcd a a'), Nat.div_mul_cancel hda,
        Nat.div_mul_cancel hda']
    have hq1 : 1 ≤ a' / Nat.gcd a a' :=
      (Nat.one_le_div_iff hd).2 (Nat.le_of_dvd (by omega) hda')
    have hq2 : a' / Nat.gcd a a' < a / Nat.gcd a a' :=
      Nat.div_lt_div_of_lt_of_dvd hda ha2
    have hgt : Nat.gcd a a' * (a / Nat.gcd a a') < b := by
      rwa [Nat.mul_div_cancel' hda]
    simp only [Finset.mem_sigma, Nat.mem_divisors]
    exact ⟨⟨hdn, hn.ne'⟩, mem_quadGT.2
      ⟨⟨quadruple_le hq1 hq2 hb1 hb2 hnd, hq1, hq2, hb1, hb2,
        Nat.coprime_div_gcd_div_gcd hd, hnd⟩, hgt⟩⟩
  · rintro ⟨d, a1, b, a1', b'⟩ hp
    simp only [Finset.mem_sigma, Nat.mem_divisors] at hp
    obtain ⟨⟨hdn, -⟩, hq⟩ := hp
    obtain ⟨⟨-, ha1, ha2, hb1, hb2, -, hsum⟩, hgt⟩ := mem_quadGT.1 hq
    have hd : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
    have hmul : d * (n / d) = n := Nat.mul_div_cancel' hdn
    have hsum' : n = d * a1 * b + d * a1' * b' := by
      rw [← hmul, hsum]; ring
    have hp1 : 1 ≤ d * a1' := Nat.mul_pos hd ha1
    have hp2 : d * a1' < d * a1 := by nlinarith
    simp only [Finset.mem_filter]
    exact ⟨mem_quadruplesQ.2 ⟨quadruple_le hp1 hp2 hb1 hb2 hsum', hp1, hp2, hb1, hb2, hsum'⟩,
      hgt⟩
  · rintro ⟨a, b, a', b'⟩ hq
    simp only [Finset.mem_filter] at hq
    obtain ⟨hmem, -⟩ := hq
    obtain ⟨-, ha1, ha2, -, -, -⟩ := mem_quadruplesQ.1 hmem
    have hd : 0 < Nat.gcd a a' := Nat.gcd_pos_of_pos_left _ (by omega)
    have e1 : Nat.gcd a a' * (a / Nat.gcd a a') = a :=
      Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
    have e2 : Nat.gcd a a' * (a' / Nat.gcd a a') = a' :=
      Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
    rw [e1, e2]
  · rintro ⟨d, a1, b, a1', b'⟩ hp
    simp only [Finset.mem_sigma, Nat.mem_divisors] at hp
    obtain ⟨⟨hdn, -⟩, hq⟩ := hp
    obtain ⟨⟨-, -, -, -, -, hcop, -⟩, -⟩ := mem_quadGT.1 hq
    have hd : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
    have hgcd : Nat.gcd (d * a1) (d * a1') = d := by
      rw [Nat.gcd_mul_left, hcop, mul_one]
    simp only [hgcd, Nat.mul_div_cancel_left _ hd]
  · rintro ⟨a, b, a', b'⟩ hq
    simp only [Finset.mem_filter] at hq
    obtain ⟨hmem, -⟩ := hq
    obtain ⟨-, ha1, ha2, -, -, -⟩ := mem_quadruplesQ.1 hmem
    have e1 : Nat.gcd a a' * (a / Nat.gcd a a') = a :=
      Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
    show a + b = Nat.gcd a a' * (a / Nat.gcd a a') + b
    rw [e1]

/-- The triples with the paper's condition `m - a'·b' > d·a²`, which is `b > d·a`
after eliminating `b`. -/
def gtTriples (m d : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (coprimeTriples m).filter (fun t => d * t.1 * t.1 < m - t.2.1 * t.2.2)

theorem mem_gtTriples {m d a a' b' : ℕ} :
    (a, a', b') ∈ gtTriples m d ↔
      (((a ≤ m ∧ a' ≤ m ∧ b' ≤ m) ∧ 1 ≤ a' ∧ a' < a ∧ 1 ≤ b'
        ∧ (a + a') * b' < m ∧ a ∣ (m - a' * b')) ∧ Nat.gcd a a' = 1)
        ∧ d * a * a < m - a' * b' := by
  simp [gtTriples, Finset.mem_filter, mem_coprimeTriples]

/-- **The `b`-elimination on the restricted set.** -/
theorem sum_quadGT_eq {m d : ℕ} (hm : 0 < m) :
    ∑ q ∈ quadGT m d, (d * q.1 + q.2.1)
      = ∑ t ∈ gtTriples m d, (d * t.1 + (m - t.2.1 * t.2.2) / t.1) := by
  refine Finset.sum_bij'
    (i := fun q _ => (q.1, q.2.2.1, q.2.2.2))
    (j := fun t _ => (t.1, (m - t.2.1 * t.2.2) / t.1, t.2.1, t.2.2)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨a, b, a', b'⟩ hq
    obtain ⟨⟨⟨hab, hbb, ha'b, hb'b⟩, ha1, ha2, hb1, hb2, hgcd, hsum⟩, hgt⟩ := mem_quadGT.1 hq
    have ha : 0 < a := by omega
    have hdvd : a ∣ (m - a' * b') := ⟨b, by omega⟩
    have hlt : (a + a') * b' < m := by nlinarith
    have heq : m - a' * b' = a * b := by omega
    have hgt' : d * a * a < m - a' * b' := by
      rw [heq]
      nlinarith
    show (a, a', b') ∈ gtTriples m d
    rw [mem_gtTriples]
    exact ⟨⟨⟨⟨hab, ha'b, hb'b⟩, ha1, ha2, hb1, hlt, hdvd⟩, hgcd⟩, hgt'⟩
  · rintro ⟨a, a', b'⟩ ht
    obtain ⟨⟨⟨⟨han, ha'n, hb'n⟩, ha1, ha2, hb1, hlt, hdvd⟩, hgcd⟩, hgt⟩ := mem_gtTriples.1 ht
    have ha : 0 < a := by omega
    have hab : a * ((m - a' * b') / a) = m - a' * b' := Nat.mul_div_cancel' hdvd
    have hle : a' * b' ≤ m := by nlinarith
    have hsum : m = a * ((m - a' * b') / a) + a' * b' := by omega
    have hbb : b' < (m - a' * b') / a := by
      have h1 : a * b' < a * ((m - a' * b') / a) := by rw [hab]; nlinarith
      exact Nat.lt_of_mul_lt_mul_left h1
    have hgt' : d * a < (m - a' * b') / a := by
      have h1 : a * (d * a) < a * ((m - a' * b') / a) := by rw [hab]; nlinarith
      exact Nat.lt_of_mul_lt_mul_left h1
    show (a, (m - a' * b') / a, a', b') ∈ quadGT m d
    rw [mem_quadGT]
    exact ⟨⟨quadruple_le ha1 ha2 hb1 hbb hsum, ha1, ha2, hb1, hbb, hgcd, hsum⟩, hgt'⟩
  · rintro ⟨a, b, a', b'⟩ hq
    obtain ⟨⟨-, ha1, ha2, hb1, hb2, -, hsum⟩, -⟩ := mem_quadGT.1 hq
    have ha : 0 < a := by omega
    have h : m - a' * b' = a * b := by omega
    show (a, (m - a' * b') / a, a', b') = (a, b, a', b')
    rw [h, Nat.mul_div_cancel_left _ ha]
  · rintro ⟨a, a', b'⟩ _
    rfl
  · rintro ⟨a, b, a', b'⟩ hq
    obtain ⟨⟨-, ha1, ha2, hb1, hb2, -, hsum⟩, -⟩ := mem_quadGT.1 hq
    have ha : 0 < a := by omega
    have h : m - a' * b' = a * b := by omega
    show d * a + b = d * a + (m - a' * b') / a
    rw [h, Nat.mul_div_cancel_left _ ha]

/-- **The restricted triple sum.**  This is the paper's triple sum: over
divisors `d ∣ n`, coprime pairs `a > a' ≥ 1`, and `b'` subject to
`(a+a')b' < n/d`, `n/d ≡ a'b' (mod a)` and `n/d - a'b' > d·a²`. -/
theorem Q_gt_tripleSum {n : ℕ} (hn : 0 < n) :
    ∑ q ∈ (quadruplesQ n).filter (fun q => q.1 < q.2.1), (q.1 + q.2.1)
      = ∑ d ∈ n.divisors, ∑ t ∈ gtTriples (n / d) d,
          (d * t.1 + (n / d - t.2.1 * t.2.2) / t.1) := by
  rw [sum_QGT_classify hn]
  refine Finset.sum_congr rfl fun d hd => ?_
  obtain ⟨hdn, -⟩ := Nat.mem_divisors.1 hd
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
  exact sum_quadGT_eq (Nat.div_pos (Nat.le_of_dvd hn hdn) hd0)

/-- **The key restriction.**  On `gtTriples m d` we have `d·a² < m`, so
`a ≤ √(m/d)`.  This is what makes the error sum converge. -/
theorem gtTriples_sq_lt {m d a a' b' : ℕ} (h : (a, a', b') ∈ gtTriples m d) :
    d * a * a < m := by
  obtain ⟨⟨⟨-, -, -, hb1, hlt, -⟩, -⟩, hgt⟩ := mem_gtTriples.1 h
  omega

/-! ## The innermost range

For a fixed pair `(a, a')` the conditions `(a+a')b' < m` and `m - a'b' > d·a²`
are two upper bounds on `b'`, so the range is an initial segment cut at the
paper's `U = min( m/(a+a'), (m - d·a²)/a' )`. -/

/-- The paper's `U`. -/
def gtBound (m d a a' : ℕ) : ℕ :=
  min ((m - 1) / (a + a') + 1) ((m - d * a * a - 1) / a' + 1)

theorem mem_gtRange {m d a a' b' : ℕ} (hm : 0 < m) (haa : 0 < a + a') (ha' : 0 < a')
    (hda : d * a * a < m) :
    b' ∈ Finset.Ico 1 (gtBound m d a a')
      ↔ (1 ≤ b' ∧ (a + a') * b' < m ∧ a' * b' + d * a * a < m) := by
  rw [Finset.mem_Ico, gtBound, lt_min_iff, Nat.lt_succ_iff, Nat.lt_succ_iff,
    Nat.le_div_iff_mul_le haa, Nat.le_div_iff_mul_le ha',
    Nat.mul_comm b' (a + a'), Nat.mul_comm b' a']
  omega

/-- **The restricted triple sum, decomposed by pairs.** -/
theorem gtTriples_decompose {m d : ℕ} (hm : 0 < m) (f : ℕ → ℕ → ℕ → ℕ) :
    ∑ t ∈ gtTriples m d, f t.1 t.2.1 t.2.2
      = ∑ p ∈ (coprimePairs m).filter (fun p => d * p.1 * p.1 < m),
          ∑ b' ∈ (Finset.Ico 1 (gtBound m d p.1 p.2)).filter
            (fun b' => p.1 ∣ (m - p.2 * b')), f p.1 p.2 b' := by
  rw [Finset.sum_sigma']
  refine Finset.sum_bij'
    (i := fun t _ => (⟨(t.1, t.2.1), t.2.2⟩ : (_ : ℕ × ℕ) × ℕ))
    (j := fun p _ => (p.1.1, p.1.2, p.2)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨a, a', b'⟩ ht
    obtain ⟨⟨⟨⟨han, ha'n, hb'n⟩, ha1, ha2, hb1, hlt, hdvd⟩, hgcd⟩, hgt⟩ := mem_gtTriples.1 ht
    have haa : 0 < a + a' := by omega
    have hle : a' * b' ≤ m := by nlinarith
    have hda : d * a * a < m := by omega
    simp only [Finset.mem_sigma, Finset.mem_filter]
    exact ⟨⟨mem_coprimePairs.2 ⟨⟨han, ha'n⟩, ha1, ha2, hgcd⟩, hda⟩,
      (mem_gtRange hm haa (by omega) hda).2 ⟨hb1, hlt, by omega⟩, hdvd⟩
  · rintro ⟨⟨a, a'⟩, b'⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_filter] at hp
    obtain ⟨⟨hpair, hda⟩, hb, hdvd⟩ := hp
    obtain ⟨⟨han, ha'n⟩, ha1, ha2, hgcd⟩ := mem_coprimePairs.1 hpair
    have haa : 0 < a + a' := by omega
    obtain ⟨hb1, hlt, hgt⟩ := (mem_gtRange hm haa (by omega) hda).1 hb
    have hb'n : b' ≤ m := by nlinarith
    show (a, a', b') ∈ gtTriples m d
    rw [mem_gtTriples]
    have hle : a' * b' ≤ m := by nlinarith
    exact ⟨⟨⟨⟨han, ha'n, hb'n⟩, ha1, ha2, hb1, hlt, hdvd⟩, hgcd⟩, by omega⟩
  · rintro ⟨a, a', b'⟩ _
    rfl
  · rintro ⟨⟨a, a'⟩, b'⟩ _
    rfl
  · rintro ⟨a, a', b'⟩ _
    rfl

/-! ## The estimate, over the reals

`Progression.lean` states the progression estimate over `ℂ`.  The triple sum is
real, so we record the real form. -/

/-- The progression estimate, over `ℝ`. -/
theorem sum_ap_sub_main_le_log_real {a : ℕ} (ha : 0 < a) (c : ℤ) (A B : ℝ) (T : ℕ) :
    |(∑ b ∈ Finset.Ico 1 T, if (a : ℤ) ∣ ((b : ℤ) - c) then (A + B * b) else 0)
        - (1 / (a : ℝ)) * ∑ b ∈ Finset.Ico 1 T, (A + B * b)|
      ≤ (|A| + |B| * (T - 1 : ℕ)) * (1 + Real.log a) := by
  have h := sum_ap_sub_main_le_log ha c (A : ℂ) (B : ℂ) T
  have key : ((((∑ b ∈ Finset.Ico 1 T, if (a : ℤ) ∣ ((b : ℤ) - c) then (A + B * b) else 0)
        - (1 / (a : ℝ)) * ∑ b ∈ Finset.Ico 1 T, (A + B * b) : ℝ)) : ℂ)
      = (∑ b ∈ Finset.Ico 1 T, if (a : ℤ) ∣ ((b : ℤ) - c) then ((A : ℂ) + B * b) else 0)
        - (1 / (a : ℂ)) * ∑ b ∈ Finset.Ico 1 T, ((A : ℂ) + B * b) := by
    push_cast
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    split <;> push_cast <;> ring
  rw [← key, Complex.norm_real] at h
  simpa using h

/-- The inner sum of the restricted triple sum, as an arithmetic-progression sum
with the paper's coefficients `A = d·a + m/a` and `B = -a'/a`. -/
theorem inner_gt_sum_eq {m d a a' : ℕ} (ha : 0 < a) (hgcd : Nat.gcd a a' = 1) :
    ∃ c : ℤ, ∀ U : ℕ, (∀ b' ∈ Finset.Ico 1 U, a' * b' ≤ m) →
      ((∑ b' ∈ (Finset.Ico 1 U).filter (fun b' => a ∣ (m - a' * b')),
          (d * a + (m - a' * b') / a) : ℕ) : ℝ)
        = ∑ b' ∈ Finset.Ico 1 U,
            (if (a : ℤ) ∣ ((b' : ℤ) - c) then
              ((((d * a : ℕ) : ℝ) + (m : ℝ) / a) + (-(a' : ℝ) / a) * b') else 0) := by
  obtain ⟨c, hc⟩ := exists_residue (m := m) hgcd
  refine ⟨c, fun U hU => ?_⟩
  rw [Finset.sum_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun b' hb' => ?_
  have hle : a' * b' ≤ m := hU b' hb'
  have hiff : (a ∣ (m - a' * b')) ↔ ((a : ℤ) ∣ ((b' : ℤ) - c)) := by
    rw [← hc (b' : ℤ)]
    constructor
    · intro h
      have h2 : ((a : ℤ)) ∣ (((m - a' * b' : ℕ)) : ℤ) := Int.natCast_dvd_natCast.2 h
      rwa [Nat.cast_sub hle, Nat.cast_mul] at h2
    · intro h
      have h2 : ((a : ℤ)) ∣ (((m - a' * b' : ℕ)) : ℤ) := by
        rwa [Nat.cast_sub hle, Nat.cast_mul]
      exact Int.natCast_dvd_natCast.1 h2
  by_cases hd : a ∣ (m - a' * b')
  · rw [if_pos hd, if_pos (hiff.1 hd)]
    have hmul : a * ((m - a' * b') / a) = m - a' * b' := Nat.mul_div_cancel' hd
    have hreal : ((a : ℝ)) * (((m - a' * b') / a : ℕ) : ℝ) = (m : ℝ) - (a' : ℝ) * b' := by
      have h3 := congrArg (Nat.cast : ℕ → ℝ) hmul
      push_cast [Nat.cast_sub hle] at h3
      linarith
    have hane : ((a : ℝ)) ≠ 0 := by positivity
    push_cast
    field_simp at hreal ⊢
    linarith
  · rw [if_neg hd, if_neg (fun h => hd (hiff.2 h))]
    simp

/-- **The innermost estimation layer.**  For a fixed pair `(a, a')`, the inner
sum differs from its expected value by `O(log a)` times the size of the
coefficients — the paper's `G₂ + G₃` for that pair. -/
theorem inner_gt_estimate {m d a a' : ℕ} (ha : 0 < a) (hgcd : Nat.gcd a a' = 1) (U : ℕ)
    (hU : ∀ b' ∈ Finset.Ico 1 U, a' * b' ≤ m) :
    ∃ c : ℤ,
      |((∑ b' ∈ (Finset.Ico 1 U).filter (fun b' => a ∣ (m - a' * b')),
            (d * a + (m - a' * b') / a) : ℕ) : ℝ)
          - (1 / (a : ℝ)) * ∑ b' ∈ Finset.Ico 1 U,
              ((((d * a : ℕ) : ℝ) + (m : ℝ) / a) + (-(a' : ℝ) / a) * b')|
        ≤ (|((d * a : ℕ) : ℝ) + (m : ℝ) / a| + |(-(a' : ℝ) / a)| * (U - 1 : ℕ))
            * (1 + Real.log a) := by
  obtain ⟨c, hc⟩ := inner_gt_sum_eq (m := m) (d := d) ha hgcd
  refine ⟨c, ?_⟩
  rw [hc U hU]
  exact sum_ap_sub_main_le_log_real ha c _ _ U

/-! ## The middle layer

Summing the per-pair error over `a' < a` coprime and then over `a ≤ √(m/d)`.
The grouping matters: the `a` values of `a'` cancel the `1/a` in the
coefficient `2m/a`, leaving `d·a² + 2m ≤ 3m` per value of `a`. -/

/-- The pairs, decomposed by their first component. -/
theorem sum_coprimePairs_filter {M : Type*} [AddCommMonoid M] {m d : ℕ} (g : ℕ → ℕ → M) :
    ∑ p ∈ (coprimePairs m).filter (fun p => d * p.1 * p.1 < m), g p.1 p.2
      = ∑ a ∈ (Finset.range (m + 1)).filter (fun a => d * a * a < m),
          ∑ a' ∈ (Finset.Ico 1 a).filter (fun x => Nat.gcd a x = 1), g a a' := by
  rw [Finset.sum_sigma']
  refine Finset.sum_bij' (i := fun p _ => (⟨p.1, p.2⟩ : (_ : ℕ) × ℕ))
    (j := fun q _ => (q.1, q.2)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨a, a'⟩ hp
    simp only [Finset.mem_filter] at hp
    obtain ⟨hpair, hda⟩ := hp
    obtain ⟨⟨han, ha'n⟩, ha1, ha2, hgcd⟩ := mem_coprimePairs.1 hpair
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    exact ⟨⟨by omega, hda⟩, ⟨ha1, ha2⟩, hgcd⟩
  · rintro ⟨a, a'⟩ hq
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at hq
    obtain ⟨⟨ham, hda⟩, ⟨ha1, ha2⟩, hgcd⟩ := hq
    simp only [Finset.mem_filter]
    exact ⟨mem_coprimePairs.2 ⟨⟨by omega, by omega⟩, ha1, ha2, hgcd⟩, hda⟩
  · rintro ⟨a, a'⟩ _
    rfl
  · rintro ⟨a, a'⟩ _
    rfl
  · rintro ⟨a, a'⟩ _
    rfl

/-- For each `a`, the number of admissible `a'` is less than `a`. -/
theorem card_coprimeSecond_lt {a : ℕ} (ha : 0 < a) :
    (((Finset.Ico 1 a).filter (fun x => Nat.gcd a x = 1)).card : ℝ) ≤ (a : ℝ) := by
  have h : ((Finset.Ico 1 a).filter (fun x => Nat.gcd a x = 1)).card ≤ a := by
    calc ((Finset.Ico 1 a).filter (fun x => Nat.gcd a x = 1)).card
        ≤ (Finset.Ico 1 a).card := Finset.card_filter_le _ _
      _ = a - 1 := by simp
      _ ≤ a := Nat.sub_le _ _
  exact_mod_cast h

/-- The admissible `a` are at most `√((m-1)/d)`. -/
theorem card_a_le {m d : ℕ} (hd : 0 < d) :
    ((Finset.range (m + 1)).filter (fun a => d * a * a < m)).card
      ≤ Nat.sqrt ((m - 1) / d) + 1 := by
  have hsub : (Finset.range (m + 1)).filter (fun a => d * a * a < m)
      ⊆ Finset.range (Nat.sqrt ((m - 1) / d) + 1) := by
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_range] at ha ⊢
    obtain ⟨-, hda⟩ := ha
    have h1 : a * a * d ≤ m - 1 := by
      have heq : d * a * a = a * a * d := by ring
      omega
    exact Nat.lt_succ_of_le (Nat.le_sqrt.2 ((Nat.le_div_iff_mul_le hd).2 h1))
  calc ((Finset.range (m + 1)).filter (fun a => d * a * a < m)).card
      ≤ (Finset.range (Nat.sqrt ((m - 1) / d) + 1)).card := Finset.card_le_card hsub
    _ = Nat.sqrt ((m - 1) / d) + 1 := Finset.card_range _

/-- **The middle layer.**  Summing the per-pair error bound over the coprime
pairs gives `3m(1 + log m)` for each admissible `a`. -/
theorem middle_layer_bound {m d : ℕ} (hm : 0 < m) :
    ∑ p ∈ (coprimePairs m).filter (fun p => d * p.1 * p.1 < m),
        (((d * p.1 : ℕ) : ℝ) + 2 * (m : ℝ) / p.1) * (1 + Real.log m)
      ≤ (((Finset.range (m + 1)).filter (fun a => d * a * a < m)).card : ℝ)
          * (3 * (m : ℝ) * (1 + Real.log m)) := by
  have hm' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hlog : (0 : ℝ) ≤ 1 + Real.log m := by
    have := Real.log_nonneg hm'
    linarith
  rw [sum_coprimePairs_filter (m := m) (d := d)
    (g := fun a _ => (((d * a : ℕ) : ℝ) + 2 * (m : ℝ) / a) * (1 + Real.log m))]
  calc ∑ a ∈ (Finset.range (m + 1)).filter (fun a => d * a * a < m),
        ∑ _a' ∈ (Finset.Ico 1 a).filter (fun x => Nat.gcd a x = 1),
          (((d * a : ℕ) : ℝ) + 2 * (m : ℝ) / a) * (1 + Real.log m)
      ≤ ∑ _a ∈ (Finset.range (m + 1)).filter (fun a => d * a * a < m),
          3 * (m : ℝ) * (1 + Real.log m) := by
        refine Finset.sum_le_sum fun a ha => ?_
        simp only [Finset.mem_filter, Finset.mem_range] at ha
        obtain ⟨ham, hda⟩ := ha
        rcases Nat.eq_zero_or_pos a with h0 | h0
        · subst h0
          simp
          positivity
        · have hcard := card_coprimeSecond_lt h0
          have ha1 : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast h0
          have hane : (a : ℝ) ≠ 0 := by linarith
          have hdle : (d : ℝ) * a * a ≤ (m : ℝ) := by
            have h2 : d * a * a ≤ m := hda.le
            exact_mod_cast h2
          calc ∑ _a' ∈ (Finset.Ico 1 a).filter (fun x => Nat.gcd a x = 1),
                (((d * a : ℕ) : ℝ) + 2 * (m : ℝ) / a) * (1 + Real.log m)
              = ((((Finset.Ico 1 a).filter (fun x => Nat.gcd a x = 1)).card : ℝ))
                  * ((((d * a : ℕ) : ℝ) + 2 * (m : ℝ) / a) * (1 + Real.log m)) := by
                rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ (a : ℝ) * ((((d * a : ℕ) : ℝ) + 2 * (m : ℝ) / a) * (1 + Real.log m)) := by
                refine mul_le_mul_of_nonneg_right hcard ?_
                have hnn : (0 : ℝ) ≤ ((d * a : ℕ) : ℝ) + 2 * (m : ℝ) / a := by positivity
                exact mul_nonneg hnn hlog
            _ = ((d : ℝ) * a * a + 2 * (m : ℝ)) * (1 + Real.log m) := by
                push_cast
                field_simp
            _ ≤ 3 * (m : ℝ) * (1 + Real.log m) := by nlinarith
    _ = (((Finset.range (m + 1)).filter (fun a => d * a * a < m)).card : ℝ)
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
  have : (((Finset.range (m + 1)).filter (fun a => d * a * a < m)).card : ℝ)
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

Lemma 17 splits `G₁` according to which of the two bounds defining `U` is
active.  Comparing `m/(a+a')` with `(m - d·a²)/a'`, the first is the smaller
exactly when `d·a·(a+a') ≤ m`.  On that branch — the *bulk* — the constraint
`(a+a')·b' < m` implies the other one, so the range of `b'` is a single initial
segment.  The complementary branch is the *small* part. -/

/-- **On the bulk branch, the first constraint implies the second.** -/
theorem bulk_second_of_first {m d a a' b' : ℕ} (ha : 0 < a) (ha' : 0 < a')
    (hbulk : d * a * (a + a') ≤ m) (h2 : (a + a') * b' < m) :
    a' * b' + d * a * a < m := by
  have haa : 0 < a + a' := by omega
  have key : (a + a') * (a' * b' + d * a * a) < (a + a') * m := by
    have e1 : (a + a') * (a' * b' + d * a * a)
        = a' * ((a + a') * b') + a * (d * a * (a + a')) := by ring
    have h3 : a' * ((a + a') * b') < a' * m := by nlinarith
    have h4 : a * (d * a * (a + a')) ≤ a * m := Nat.mul_le_mul_left a hbulk
    have e2 : (a + a') * m = a' * m + a * m := by ring
    omega
  exact Nat.lt_of_mul_lt_mul_left key

/-- On the bulk branch the range of `b'` is cut by `(a+a')·b' < m` alone. -/
theorem gtBound_bulk {m d a a' : ℕ} (hm : 0 < m) (ha : 0 < a) (ha' : 0 < a')
    (hda : d * a * a < m) (hbulk : d * a * (a + a') ≤ m) :
    Finset.Ico 1 (gtBound m d a a') = Finset.Ico 1 ((m - 1) / (a + a') + 1) := by
  ext b'
  rw [mem_gtRange hm (by omega) ha' hda, Finset.mem_Ico, Nat.lt_succ_iff,
    Nat.le_div_iff_mul_le (by omega : 0 < a + a'), Nat.mul_comm b' (a + a')]
  constructor
  · rintro ⟨h1, h2, -⟩
    exact ⟨h1, by omega⟩
  · rintro ⟨h1, h2⟩
    have h2' : (a + a') * b' < m := by omega
    exact ⟨h1, h2', bulk_second_of_first ha ha' hbulk h2'⟩

/-- **The bulk / small split of the triple sum.** -/
theorem gtTriples_bulk_small (m d : ℕ) (f : ℕ → ℕ → ℕ → ℕ) :
    ∑ t ∈ gtTriples m d, f t.1 t.2.1 t.2.2
      = (∑ t ∈ (gtTriples m d).filter (fun t => d * t.1 * (t.1 + t.2.1) ≤ m),
          f t.1 t.2.1 t.2.2)
        + ∑ t ∈ (gtTriples m d).filter (fun t => ¬ (d * t.1 * (t.1 + t.2.1) ≤ m)),
            f t.1 t.2.1 t.2.2 :=
  (Finset.sum_filter_add_sum_filter_not _ _ _).symm

/-- **On the small branch, `2·d·a² > m`.**  This is the paper's observation that
`2a²` is bounded below by `m/d`, which is what makes the small part small. -/
theorem small_two_mul_gt {m d a a' b' : ℕ} (h : (a, a', b') ∈ gtTriples m d)
    (hsmall : m < d * a * (a + a')) : m < 2 * (d * a * a) := by
  obtain ⟨⟨⟨-, -, ha2, -, -, -⟩, -⟩, -⟩ := mem_gtTriples.1 h
  nlinarith

/-! ## Counting an arithmetic progression

The divisibility condition `a ∣ m - a'·b'` puts `b'` in a single residue class
modulo `a`, so within an interval of length `U` there are at most `U/a + 1` of
them.  This factor of `1/a` is what makes the small part `O(m^{3/2})`: without
it a crude count would be too large by exactly that factor. -/

/-- **Counting a residue class in an interval.** -/
theorem card_mod_filter_le {a U c : ℕ} (ha : 0 < a) :
    (((Finset.Ico 1 U).filter (fun b => b % a = c)).card) ≤ U / a + 1 := by
  classical
  have hmap : ∀ b ∈ (Finset.Ico 1 U).filter (fun b => b % a = c),
      b / a ∈ Finset.range (U / a + 1) := by
    intro b hb
    simp only [Finset.mem_filter, Finset.mem_Ico] at hb
    simp only [Finset.mem_range, Nat.lt_succ_iff]
    exact Nat.div_le_div_right (by omega)
  have hinj : ∀ b₁ ∈ (Finset.Ico 1 U).filter (fun b => b % a = c),
      ∀ b₂ ∈ (Finset.Ico 1 U).filter (fun b => b % a = c), b₁ / a = b₂ / a → b₁ = b₂ := by
    intro b₁ h₁ b₂ h₂ heq
    simp only [Finset.mem_filter] at h₁ h₂
    have e₁ := Nat.div_add_mod b₁ a
    have e₂ := Nat.div_add_mod b₂ a
    rw [h₁.2] at e₁
    rw [h₂.2] at e₂
    rw [heq] at e₁
    omega
  calc (((Finset.Ico 1 U).filter (fun b => b % a = c)).card)
      ≤ (Finset.range (U / a + 1)).card := Finset.card_le_card_of_injOn _ hmap hinj
    _ = U / a + 1 := Finset.card_range _

/-- **The divisibility condition confines `b'` to one residue class.** -/
theorem card_dvd_filter_le {m a a' U : ℕ} (ha : 0 < a) (hgcd : Nat.gcd a a' = 1)
    (hU : ∀ b ∈ Finset.Ico 1 U, a' * b ≤ m) :
    (((Finset.Ico 1 U).filter (fun b => a ∣ (m - a' * b))).card) ≤ U / a + 1 := by
  classical
  rcases Finset.eq_empty_or_nonempty
      ((Finset.Ico 1 U).filter (fun b => a ∣ (m - a' * b))) with he | ⟨b₀, hb₀⟩
  · rw [he]
    simp
  · refine le_trans (Finset.card_le_card ?_) (card_mod_filter_le (c := b₀ % a) ha)
    intro b hb
    simp only [Finset.mem_filter] at hb hb₀ ⊢
    refine ⟨hb.1, ?_⟩
    -- `a ∣ a' * (b₀ - b)` over `ℤ`, and `gcd a a' = 1`, so `b ≡ b₀ mod a`
    have hle : a' * b ≤ m := hU b hb.1
    have hle₀ : a' * b₀ ≤ m := hU b₀ hb₀.1
    have hz : ((a : ℤ)) ∣ ((a' : ℤ) * ((b₀ : ℤ) - (b : ℤ))) := by
      have h1 : ((a : ℤ)) ∣ ((m : ℤ) - (a' : ℤ) * (b : ℤ)) := by
        have := Int.natCast_dvd_natCast.2 hb.2
        rwa [Nat.cast_sub hle, Nat.cast_mul] at this
      have h2 : ((a : ℤ)) ∣ ((m : ℤ) - (a' : ℤ) * (b₀ : ℤ)) := by
        have := Int.natCast_dvd_natCast.2 hb₀.2
        rwa [Nat.cast_sub hle₀, Nat.cast_mul] at this
      have := dvd_sub h1 h2
      have heq : ((m : ℤ) - (a' : ℤ) * (b : ℤ)) - ((m : ℤ) - (a' : ℤ) * (b₀ : ℤ))
          = (a' : ℤ) * ((b₀ : ℤ) - (b : ℤ)) := by ring
      rwa [heq] at this
    have hco : IsCoprime (a : ℤ) (a' : ℤ) := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      simpa using hgcd
    have hdvd : ((a : ℤ)) ∣ ((b₀ : ℤ) - (b : ℤ)) := IsCoprime.dvd_of_dvd_mul_left hco hz
    have : b ≡ b₀ [MOD a] := (Nat.modEq_iff_dvd).2 hdvd
    exact this

/-! ## The small-part bound

On the small branch `d·a² > m/2`, so `m/a² < 2d` and the residue class meets the
range in at most `2d+2` points; each summand is at most `2·(m/a)`.  Summing over
`a' < a` the factor `a` cancels the `1/a`, leaving `O(d·m)` per value of `a`, and
`a` ranges over at most `√(m/d)+1` values. -/

/-- **The per-pair bound on the small branch.** -/
theorem small_pair_le {m d a a' : ℕ} (ha : 0 < a) (ha' : 0 < a') (hgcd : Nat.gcd a a' = 1)
    (hda : d * a * a < m) (haa : a' < a) (hsmall : ¬ (d * a * (a + a') ≤ m)) :
    ∑ b' ∈ (Finset.Ico 1 (gtBound m d a a')).filter (fun b' => a ∣ (m - a' * b')),
        (d * a + (m - a' * b') / a)
      ≤ (2 * d + 2) * (2 * (m / a)) := by
  have hm : 0 < m := by omega
  have haa0 : 0 < a + a' := by omega
  -- every `b'` in range has `a' * b' ≤ m`
  have hU : ∀ b ∈ Finset.Ico 1 (gtBound m d a a'), a' * b ≤ m := by
    intro b hb
    obtain ⟨-, -, h3⟩ := (mem_gtRange hm haa0 ha' hda).1 hb
    omega
  -- the count is at most `2d + 2`
  have hsq : m < 2 * (d * a * a) := by nlinarith
  have hcard : (((Finset.Ico 1 (gtBound m d a a')).filter
      (fun b' => a ∣ (m - a' * b'))).card) ≤ 2 * d + 2 := by
    refine le_trans (card_dvd_filter_le ha hgcd hU) ?_
    have hb1 : gtBound m d a a' ≤ (m - 1) / (a + a') + 1 := min_le_left _ _
    have hb2 : gtBound m d a a' ≤ (m - 1) / a + 1 :=
      le_trans hb1 (by
        have : (m - 1) / (a + a') ≤ (m - 1) / a := Nat.div_le_div_left (by omega) ha
        omega)
    have hb3 : gtBound m d a a' / a ≤ ((m - 1) / a + 1) / a := Nat.div_le_div_right hb2
    have hb4 : ((m - 1) / a + 1) / a ≤ (m - 1) / (a * a) + 1 := by
      rw [← Nat.div_div_eq_div_mul]
      have h2 : ((m - 1) / a + 1) / a ≤ ((m - 1) / a + a) / a :=
        Nat.div_le_div_right (by omega)
      have h3 : ((m - 1) / a + a) / a = (m - 1) / a / a + 1 := Nat.add_div_right _ ha
      omega
    have hb5 : (m - 1) / (a * a) ≤ 2 * d := by
      have heq : 2 * (d * a * a) = 2 * d * (a * a) := by ring
      have h1 : m - 1 ≤ 2 * d * (a * a) := by omega
      calc (m - 1) / (a * a) ≤ (2 * d * (a * a)) / (a * a) := Nat.div_le_div_right h1
        _ = 2 * d := Nat.mul_div_cancel _ (by positivity)
    omega
  -- every summand is at most `2 * (m / a)`
  have hterm : ∀ b' ∈ (Finset.Ico 1 (gtBound m d a a')).filter (fun b' => a ∣ (m - a' * b')),
      d * a + (m - a' * b') / a ≤ 2 * (m / a) := by
    intro b' _
    have h1 : d * a ≤ m / a := by
      refine (Nat.le_div_iff_mul_le ha).2 ?_
      nlinarith
    have h2 : (m - a' * b') / a ≤ m / a := Nat.div_le_div_right (by omega)
    omega
  calc ∑ b' ∈ (Finset.Ico 1 (gtBound m d a a')).filter (fun b' => a ∣ (m - a' * b')),
        (d * a + (m - a' * b') / a)
      ≤ ∑ _b' ∈ (Finset.Ico 1 (gtBound m d a a')).filter (fun b' => a ∣ (m - a' * b')),
          2 * (m / a) := Finset.sum_le_sum hterm
    _ = (((Finset.Ico 1 (gtBound m d a a')).filter
          (fun b' => a ∣ (m - a' * b'))).card) * (2 * (m / a)) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ (2 * d + 2) * (2 * (m / a)) := Nat.mul_le_mul_right _ hcard

/-- **The small part is `O(m^{3/2}·√d)`.** -/
theorem small_part_le {m d : ℕ} (hm : 0 < m) (hd : 0 < d) :
    ∑ t ∈ (gtTriples m d).filter (fun t => ¬ (d * t.1 * (t.1 + t.2.1) ≤ m)),
        (d * t.1 + (m - t.2.1 * t.2.2) / t.1)
      ≤ (Nat.sqrt ((m - 1) / d) + 1) * ((2 * d + 2) * (2 * m)) := by
  classical
  rw [Finset.sum_filter,
    gtTriples_decompose hm (fun a a' b' =>
      if ¬ (d * a * (a + a') ≤ m) then d * a + (m - a' * b') / a else 0)]
  -- each pair contributes at most `(2d+2) · 2·(m/a)`
  have hpair : ∀ p ∈ (coprimePairs m).filter (fun p => d * p.1 * p.1 < m),
      (∑ b' ∈ (Finset.Ico 1 (gtBound m d p.1 p.2)).filter (fun b' => p.1 ∣ (m - p.2 * b')),
          if ¬ (d * p.1 * (p.1 + p.2) ≤ m) then d * p.1 + (m - p.2 * b') / p.1 else 0)
        ≤ (2 * d + 2) * (2 * (m / p.1)) := by
    rintro ⟨a, a'⟩ hp
    simp only [Finset.mem_filter] at hp
    obtain ⟨hpair', hda⟩ := hp
    obtain ⟨-, ha1, ha2, hgcd⟩ := mem_coprimePairs.1 hpair'
    by_cases hsmall : ¬ (d * a * (a + a') ≤ m)
    · simp only [hsmall, if_true]
      exact small_pair_le (by omega) ha1 hgcd hda ha2 hsmall
    · simp only [hsmall, if_false]
      simp
  refine le_trans (Finset.sum_le_sum hpair) ?_
  -- decompose the pairs by their first component
  rw [sum_coprimePairs_filter (m := m) (d := d)
    (g := fun a _ => (2 * d + 2) * (2 * (m / a)))]
  calc ∑ a ∈ (Finset.range (m + 1)).filter (fun a => d * a * a < m),
        ∑ _a' ∈ (Finset.Ico 1 a).filter (fun x => Nat.gcd a x = 1),
          (2 * d + 2) * (2 * (m / a))
      ≤ ∑ _a ∈ (Finset.range (m + 1)).filter (fun a => d * a * a < m),
          (2 * d + 2) * (2 * m) := by
        refine Finset.sum_le_sum fun a ha => ?_
        rw [Finset.sum_const, smul_eq_mul]
        have hc : ((Finset.Ico 1 a).filter (fun x => Nat.gcd a x = 1)).card ≤ a := by
          calc ((Finset.Ico 1 a).filter (fun x => Nat.gcd a x = 1)).card
              ≤ (Finset.Ico 1 a).card := Finset.card_filter_le _ _
            _ = a - 1 := by simp
            _ ≤ a := Nat.sub_le _ _
        have hma : a * (m / a) ≤ m := Nat.mul_div_le m a
        calc ((Finset.Ico 1 a).filter (fun x => Nat.gcd a x = 1)).card
              * ((2 * d + 2) * (2 * (m / a)))
            ≤ a * ((2 * d + 2) * (2 * (m / a))) := Nat.mul_le_mul_right _ hc
          _ = (2 * d + 2) * (2 * (a * (m / a))) := by ring
          _ ≤ (2 * d + 2) * (2 * m) := by
              exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hma)
    _ = (((Finset.range (m + 1)).filter (fun a => d * a * a < m)).card)
          * ((2 * d + 2) * (2 * m)) := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ (Nat.sqrt ((m - 1) / d) + 1) * ((2 * d + 2) * (2 * m)) :=
        Nat.mul_le_mul_right _ (card_a_le hd)

/-! ## Towards the main term

The main term per pair is `(1/a)·∑_{1 ≤ b' < U} (A + B·b')` with the paper's
coefficients.  Evaluating that sum in closed form and substituting
`U = m/(a+a')`, `A = d·a + m/a`, `B = -a'/a` gives

```
d·m/(a+a')  +  m²·[ 1/(a²(a+a')) - a'/(2a²(a+a')²) ]  =  d·m/(a+a')  +  m²·cTerm(a,a'),
```

by `cTerm_summand_eq`.  Summing over all coprime pairs gives `m²·C`, and over
`d ∣ n` with `m = n/d` gives `C·n²·∑_{d∣n} 1/d²` — Lemma 17. -/

/-- **The closed form of the main term.**  `∑_{1 ≤ b < U} (A + B·b)`. -/
theorem sum_linear_Ico (A B : ℝ) : ∀ U : ℕ, 1 ≤ U →
    ∑ b ∈ Finset.Ico 1 U, (A + B * (b : ℝ))
      = A * ((U : ℝ) - 1) + B * (((U : ℝ) - 1) * (U : ℝ) / 2) := by
  intro U hU
  induction U, hU using Nat.le_induction with
  | base => simp
  | succ U hU ih =>
    rw [Finset.sum_Ico_succ_top hU, ih]
    push_cast
    ring

/-- **Pairs outside the bulk have large `a`.**  If `d·a·(a+a') > m` then
`2d·a² > m`, so `a > √(m/(2d))`.  This is what makes the truncation of the
series for `C` cost only `O(√(d/m))`. -/
theorem excluded_pair_large {m d a a' : ℕ} (ha' : 1 ≤ a') (haa : a' < a)
    (h : m < d * a * (a + a')) : m < 2 * d * (a * a) := by
  nlinarith

/-- **Pairs with small `a` lie in the bulk.**  The contrapositive of
`excluded_pair_large`. -/
theorem bulk_of_small_a {m d a a' : ℕ} (ha' : 1 ≤ a') (haa : a' < a)
    (h : 2 * d * (a * a) ≤ m) : d * a * (a + a') ≤ m := by
  nlinarith

/-- The cut-off `N = √(m/(2d))` puts every pair with `a ≤ N` in the bulk. -/
theorem bulk_of_le_sqrt {m d a a' : ℕ} (ha' : 1 ≤ a') (haa : a' < a)
    (ha : a ≤ Nat.sqrt (m / (2 * d))) (hd : 0 < d) : d * a * (a + a') ≤ m := by
  refine bulk_of_small_a ha' haa ?_
  have h1 : a * a ≤ m / (2 * d) := by
    have := Nat.sqrt_le' (m / (2 * d))
    calc a * a ≤ Nat.sqrt (m / (2 * d)) * Nat.sqrt (m / (2 * d)) :=
          Nat.mul_le_mul ha ha
      _ ≤ m / (2 * d) := by rw [← pow_two]; exact Nat.sqrt_le' _
  calc 2 * d * (a * a) ≤ 2 * d * (m / (2 * d)) := Nat.mul_le_mul_left _ h1
    _ ≤ m := Nat.mul_div_le m (2 * d)

/-! ## The floor analysis

The main term is evaluated at the natural-number bound `U`, but the paper's
computation substitutes the real value `V = m/(a+a')`.  The two differ, and the
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
`A·V + B·V²/2` — with the actual sum `∑_{1 ≤ b' < V} (A + B·b')`, and bounds the
difference by `|A| + |B·V|`.  Writing `K` for the largest admissible `b'`, so
that `K ≤ V < K+1` and the sum is `A·K + B·K(K+1)/2`, that is what is proved
here. -/
theorem main_term_vs_sum (A B V : ℝ) (K : ℕ) (hK : (K : ℝ) ≤ V) (hK1 : V < (K : ℝ) + 1)
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
        have ha := abs_nonneg A
        have hb : (0 : ℝ) ≤ |B| / 2 := by positivity
        nlinarith
    _ = |A| + |B| * V := by ring

/-! ## The lower-order part

After substitution the main term carries a term `d·m/(a+a')`.  Summing it over
`a' < a` gives at most `d·m` per value of `a` — the `a` choices of `a'` cancel
the `1/a` again — and `a` ranges over at most `√((m-1)/d)+1` values, so the
whole thing is `O(m^{3/2}√d)`, the same order as the other errors. -/

/-- **The lower-order part of the main term.** -/
theorem lower_order_le {m d : ℕ} (hm : 0 < m) (hd : 0 < d) :
    ∑ p ∈ (coprimePairs m).filter (fun p => d * p.1 * (p.1 + p.2) ≤ m),
        (d : ℝ) * (m : ℝ) / ((p.1 : ℝ) + (p.2 : ℝ))
      ≤ ((Nat.sqrt ((m - 1) / d) : ℝ) + 1) * ((d : ℝ) * (m : ℝ)) := by
  have hsub : (coprimePairs m).filter (fun p => d * p.1 * (p.1 + p.2) ≤ m)
      ⊆ (coprimePairs m).filter (fun p => d * p.1 * p.1 < m) := by
    rintro ⟨a, a'⟩ hp
    simp only [Finset.mem_filter] at hp ⊢
    obtain ⟨hmem, hbulk⟩ := hp
    obtain ⟨-, ha1, ha2, -⟩ := mem_coprimePairs.1 hmem
    exact ⟨hmem, by nlinarith⟩
  calc ∑ p ∈ (coprimePairs m).filter (fun p => d * p.1 * (p.1 + p.2) ≤ m),
        (d : ℝ) * (m : ℝ) / ((p.1 : ℝ) + (p.2 : ℝ))
      ≤ ∑ p ∈ (coprimePairs m).filter (fun p => d * p.1 * p.1 < m),
          (d : ℝ) * (m : ℝ) / ((p.1 : ℝ) + (p.2 : ℝ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)
    _ = ∑ a ∈ (Finset.range (m + 1)).filter (fun a => d * a * a < m),
          ∑ a' ∈ (Finset.Ico 1 a).filter (fun x => Nat.gcd a x = 1),
            (d : ℝ) * (m : ℝ) / ((a : ℝ) + (a' : ℝ)) :=
        sum_coprimePairs_filter (m := m) (d := d)
          (g := fun a a' => (d : ℝ) * (m : ℝ) / ((a : ℝ) + (a' : ℝ)))
    _ ≤ ∑ _a ∈ (Finset.range (m + 1)).filter (fun a => d * a * a < m), (d : ℝ) * (m : ℝ) := by
        refine Finset.sum_le_sum fun a ha => ?_
        rcases Nat.eq_zero_or_pos a with h0 | h0
        · subst h0
          simp
          positivity
        · have ha1 : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast h0
          have hcard := card_coprimeSecond_lt h0
          calc ∑ a' ∈ (Finset.Ico 1 a).filter (fun x => Nat.gcd a x = 1),
                (d : ℝ) * (m : ℝ) / ((a : ℝ) + (a' : ℝ))
              ≤ ∑ _a' ∈ (Finset.Ico 1 a).filter (fun x => Nat.gcd a x = 1),
                  (d : ℝ) * (m : ℝ) / (a : ℝ) := by
                refine Finset.sum_le_sum fun a' _ => ?_
                have ha'0 : (0 : ℝ) ≤ (a' : ℝ) := by positivity
                apply div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
            _ = (((Finset.Ico 1 a).filter (fun x => Nat.gcd a x = 1)).card : ℝ)
                  * ((d : ℝ) * (m : ℝ) / (a : ℝ)) := by
                rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ (a : ℝ) * ((d : ℝ) * (m : ℝ) / (a : ℝ)) := by
                refine mul_le_mul_of_nonneg_right hcard (by positivity)
            _ = (d : ℝ) * (m : ℝ) := by field_simp
    _ = ((((Finset.range (m + 1)).filter (fun a => d * a * a < m)).card : ℝ))
          * ((d : ℝ) * (m : ℝ)) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((Nat.sqrt ((m - 1) / d) : ℝ) + 1) * ((d : ℝ) * (m : ℝ)) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        have h := card_a_le (m := m) hd
        have hc : ((((Finset.range (m + 1)).filter (fun a => d * a * a < m)).card : ℝ))
            ≤ ((Nat.sqrt ((m - 1) / d) + 1 : ℕ) : ℝ) := by exact_mod_cast h
        push_cast at hc
        linarith

/-! ## Sanity checks -/

-- The `b`-elimination, checked numerically.
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
        ∑ b' ∈ (Finset.Ico 1 (bBound (n / d) p.1 p.2)).filter
          (fun b' => p.1 ∣ (n / d - p.2 * b')), (n / d - p.2 * b') / p.1)
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
