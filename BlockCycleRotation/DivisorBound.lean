/-
# Towards the divisor bound `d(n) = O(n^ε)`

The one input to §4 that Mathlib does not already provide is the divisor bound:
for every `ε > 0` there is a constant `C` with `d(n) ≤ C · n^ε`.  Mathlib has the
factorisation formula `Nat.card_divisors` and multiplicativity, but no
asymptotic statement.

The proof splits the primes dividing `n` at `p^ε = 2`:

* for `p^ε ≥ 2` the factor `k + 1` is already at most `2^k ≤ (p^ε)^k`, costing
  nothing;
* for `p^ε < 2` — finitely many primes, all below `2^(1/ε)` — the factor is at
  most `C₀ · (p^ε)^k` for a constant `C₀` depending only on `ε`.

This file establishes the second ingredient: `k + 1` is `O(t^k)` for any `t > 1`,
with an explicit constant, together with the elementary `k + 1 ≤ 2^k` for the
first.  Bernoulli's inequality is proved here rather than looked up, to keep the
file self-contained.
-/

import BlockCycleRotation.Progression

namespace BlockCycleRotation

open Real

/-! ## Elementary inequalities -/

/-- `k + 1 ≤ 2 ^ k`. -/
theorem succ_le_two_pow (k : ℕ) : k + 1 ≤ 2 ^ k := by
  induction k with
  | zero => simp
  | succ n ih =>
    have h1 : (1 : ℕ) ≤ 2 ^ n := Nat.one_le_two_pow
    rw [pow_succ]
    omega

/-- `1 ≤ (1 + s) ^ k` for `0 ≤ s`. -/
theorem one_le_one_add_pow {s : ℝ} (hs : 0 ≤ s) (k : ℕ) : (1 : ℝ) ≤ (1 + s) ^ k := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    nlinarith

/-- **Bernoulli's inequality**, proved here to keep this file self-contained. -/
theorem one_add_mul_le_one_add_pow {s : ℝ} (hs : 0 ≤ s) (k : ℕ) :
    1 + (k : ℝ) * s ≤ (1 + s) ^ k := by
  induction k with
  | zero => simp
  | succ n ih =>
    have h1 := one_le_one_add_pow hs n
    rw [pow_succ]
    push_cast
    nlinarith [mul_nonneg hs (sub_nonneg.2 h1)]

/-- **`k + 1` is `O(t^k)` for any `t > 1`, with an explicit constant.**

Taking `s = t - 1`, Bernoulli gives `t^k ≥ 1 + k·s`, and `max 1 (2/s)` works:
for `k ≥ 1` we have `k + 1 ≤ 2k ≤ (2/s)·(k·s)`. -/
theorem exists_const_add_one_le {t : ℝ} (ht : 1 < t) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ k : ℕ, (k : ℝ) + 1 ≤ C * t ^ k := by
  have hs0 : 0 < t - 1 := by linarith
  refine ⟨max 1 (2 / (t - 1)), le_max_left _ _, fun k => ?_⟩
  set s := t - 1 with hs
  set C := max 1 (2 / s) with hC
  have hC1 : (1 : ℝ) ≤ C := le_max_left _ _
  have hCge : 2 / s ≤ C := le_max_right _ _
  have hts : t = 1 + s := by rw [hs]; ring
  have hbern : 1 + (k : ℝ) * s ≤ t ^ k := by
    rw [hts]
    exact one_add_mul_le_one_add_pow hs0.le k
  have hstep : (k : ℝ) + 1 ≤ C * (1 + (k : ℝ) * s) := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      simpa using hC1
    · have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      have hks : (0 : ℝ) ≤ (k : ℝ) * s := by positivity
      have hprod : 2 / s * ((k : ℝ) * s) ≤ C * ((k : ℝ) * s) :=
        mul_le_mul_of_nonneg_right hCge hks
      have heq : 2 / s * ((k : ℝ) * s) = 2 * (k : ℝ) := by field_simp
      have hexp : C * (1 + (k : ℝ) * s) = C + C * ((k : ℝ) * s) := by ring
      rw [hexp]
      linarith
  calc (k : ℝ) + 1 ≤ C * (1 + (k : ℝ) * s) := hstep
    _ ≤ C * t ^ k := mul_le_mul_of_nonneg_left hbern (by linarith)

/-! ## Prime powers -/

/-- `(p^k)^ε = (p^ε)^k`. -/
theorem natPow_rpow {p : ℕ} (hp : 0 < p) (k : ℕ) (ε : ℝ) :
    (((p ^ k : ℕ) : ℝ)) ^ ε = (((p : ℝ)) ^ ε) ^ k := by
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := by positivity
  push_cast
  rw [← Real.rpow_natCast ((p : ℝ)) k, ← Real.rpow_mul hp0, mul_comm,
    Real.rpow_mul hp0, Real.rpow_natCast]

/-- **Large primes cost nothing.**  If `2 ≤ p^ε` then `k + 1 ≤ (p^k)^ε`. -/
theorem add_one_le_rpow_of_two_le {p : ℕ} (hp : 0 < p) {ε : ℝ} (h2 : 2 ≤ (p : ℝ) ^ ε)
    (k : ℕ) : ((k : ℝ) + 1) ≤ (((p ^ k : ℕ) : ℝ)) ^ ε := by
  rw [natPow_rpow hp k ε]
  have h1 : ((k : ℝ) + 1) ≤ 2 ^ k := by
    have := succ_le_two_pow k
    have hcast : ((k + 1 : ℕ) : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at hcast
    linarith
  exact h1.trans (pow_le_pow_left₀ (by norm_num) h2 k)

/-- **Small primes cost a constant.**  For `p ≥ 2` and `ε > 0`, `k + 1` is at most
`C · (p^k)^ε` with `C` depending only on `ε`. -/
theorem exists_const_add_one_le_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ p : ℕ, 2 ≤ p → ∀ k : ℕ,
      ((k : ℝ) + 1) ≤ C * (((p ^ k : ℕ) : ℝ)) ^ ε := by
  have h2 : (1 : ℝ) < (2 : ℝ) ^ ε := by
    apply Real.one_lt_rpow_iff_of_pos (by norm_num) |>.2
    exact Or.inl ⟨by norm_num, hε⟩
  obtain ⟨C, hC1, hC⟩ := exists_const_add_one_le h2
  refine ⟨C, hC1, fun p hp k => ?_⟩
  have hp0 : 0 < p := by omega
  rw [natPow_rpow hp0 k ε]
  refine (hC k).trans ?_
  have hple : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hrp : (2 : ℝ) ^ ε ≤ (p : ℝ) ^ ε := Real.rpow_le_rpow (by norm_num) hple hε.le
  have hmono : ((2 : ℝ) ^ ε) ^ k ≤ ((p : ℝ) ^ ε) ^ k :=
    pow_le_pow_left₀ (by positivity) hrp k
  exact mul_le_mul_of_nonneg_left hmono (by linarith)

/-! ## The divisor bound -/

/-- **The divisor bound.**  For every `ε > 0` there is a constant `C` with
`d(n) ≤ C · n^ε` for all `n ≥ 1`.

The primes dividing `n` are split at `p^ε = 2`.  Above the cut each factor
`k + 1 ≤ 2^k ≤ (p^ε)^k` costs nothing; below it — finitely many primes, all
less than `2^(1/ε)` — each costs a constant `C₀`, and their number is bounded
independently of `n`. -/
theorem exists_card_divisors_le {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, n ≠ 0 → ((n.divisors.card : ℝ)) ≤ C * (n : ℝ) ^ ε := by
  classical
  set N := ⌈(2 : ℝ) ^ (1 / ε)⌉₊ + 1 with hN
  set S := (Finset.range N).filter (fun p : ℕ => ¬ (2 ≤ (p : ℝ) ^ ε)) with hS
  obtain ⟨C₀, hC₀1, hC₀⟩ := exists_const_add_one_le_rpow hε
  have hC₀0 : (0 : ℝ) < C₀ := by linarith
  refine ⟨C₀ ^ S.card, by positivity, ?_⟩
  intro n hn
  -- every prime below the cut lies in `S`
  have hmemS : ∀ p : ℕ, 2 ≤ p → ¬ (2 ≤ (p : ℝ) ^ ε) → p ∈ S := by
    intro p hp2 hlt
    have hp0 : (0 : ℝ) ≤ (p : ℝ) := by positivity
    have hlt' : (p : ℝ) ^ ε < 2 := lt_of_not_ge hlt
    have hinv : (0 : ℝ) < 1 / ε := by positivity
    have h1 : ((p : ℝ) ^ ε) ^ (1 / ε) = (p : ℝ) := by
      rw [← Real.rpow_mul hp0, mul_one_div, div_self hε.ne', Real.rpow_one]
    have h2 : ((p : ℝ) ^ ε) ^ (1 / ε) < (2 : ℝ) ^ (1 / ε) :=
      Real.rpow_lt_rpow (by positivity) hlt' hinv
    rw [h1] at h2
    have h3 : (p : ℝ) < (⌈(2 : ℝ) ^ (1 / ε)⌉₊ : ℝ) :=
      lt_of_lt_of_le h2 (Nat.le_ceil _)
    have h4 : p < N := by
      have : p < ⌈(2 : ℝ) ^ (1 / ε)⌉₊ := by exact_mod_cast h3
      omega
    rw [hS, Finset.mem_filter, Finset.mem_range]
    exact ⟨h4, hlt⟩
  rw [Nat.card_divisors hn]
  push_cast
  -- bound each factor
  have hfac : ∀ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1)
      ≤ (if p ∈ S then C₀ else 1) * (((p ^ n.factorization p : ℕ)) : ℝ) ^ ε := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hp2 : 2 ≤ p := hpp.two_le
    by_cases hsm : 2 ≤ (p : ℝ) ^ ε
    · have hnot : p ∉ S := by simp [hS, hsm]
      rw [if_neg hnot, one_mul]
      exact add_one_le_rpow_of_two_le (by omega) hsm _
    · rw [if_pos (hmemS p hp2 hsm)]
      exact hC₀ p hp2 _
  -- the constant part
  have hconst : (∏ p ∈ n.primeFactors, (if p ∈ S then C₀ else 1)) ≤ C₀ ^ S.card := by
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
    refine pow_le_pow_right₀ hC₀1 ?_
    refine Finset.card_le_card ?_
    intro x hx
    exact (Finset.mem_filter.1 hx).2
  -- the `n^ε` part
  have hprod_n : (∏ p ∈ n.primeFactors, (((p ^ n.factorization p : ℕ)) : ℝ)) = (n : ℝ) := by
    rw [← Nat.cast_prod]
    exact congrArg _ (Nat.prod_primeFactors_pow_factorization hn).symm
  have hrpow : (∏ p ∈ n.primeFactors, (((p ^ n.factorization p : ℕ)) : ℝ) ^ ε)
      = (n : ℝ) ^ ε := by
    rw [Real.finsetProd_rpow _ _ (fun p _ => by positivity) ε, hprod_n]
  calc ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1)
      ≤ ∏ p ∈ n.primeFactors,
          ((if p ∈ S then C₀ else 1) * (((p ^ n.factorization p : ℕ)) : ℝ) ^ ε) :=
        Finset.prod_le_prod (fun p _ => by positivity) hfac
    _ = (∏ p ∈ n.primeFactors, (if p ∈ S then C₀ else 1))
          * (∏ p ∈ n.primeFactors, (((p ^ n.factorization p : ℕ)) : ℝ) ^ ε) :=
        Finset.prod_mul_distrib
    _ = (∏ p ∈ n.primeFactors, (if p ∈ S then C₀ else 1)) * (n : ℝ) ^ ε := by rw [hrpow]
    _ ≤ C₀ ^ S.card * (n : ℝ) ^ ε := by
        refine mul_le_mul_of_nonneg_right hconst ?_
        positivity

end BlockCycleRotation
