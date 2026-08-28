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

/-! ## Sanity checks -/

-- The `b`-elimination, checked numerically.
#guard (List.range 22).all (fun m => let n := m + 1
  (∑ q ∈ quadruplesQ n, q.2.1) = ∑ t ∈ triples n, (n - t.2.1 * t.2.2) / t.1)
-- The triple sum, checked numerically.
#guard (List.range 18).all (fun m => let n := m + 1
  (∑ q ∈ quadruplesQ n, q.2.1)
    = ∑ d ∈ n.divisors, ∑ t ∈ coprimeTriples (n / d), (n / d - t.2.1 * t.2.2) / t.1)
-- `∑ gcd(n,k) ≤ n · d(n)`.
#guard (List.range 30).all (fun m => let n := m + 1
  (∑ k ∈ allShifts n, Nat.gcd n k) ≤ n * n.divisors.card)

end BlockCycleRotation
