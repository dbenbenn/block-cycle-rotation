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

end BlockCycleRotation
