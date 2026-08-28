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
-- `∑ gcd(n,k) ≤ n · d(n)`.
#guard (List.range 30).all (fun m => let n := m + 1
  (∑ k ∈ allShifts n, Nat.gcd n k) ≤ n * n.divisors.card)

end BlockCycleRotation
