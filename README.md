# block-cycle-rotation

A Lean 4 / Mathlib formalisation of

> Valentin Blomer and Kai-Uwe Bux,
> *The cost of cyclic permutations and remainder sums in the Euclidean algorithm*,
> AofA 2026, LIPIcs vol. 381, pp. 14:1–14:17.
> [arXiv:2601.00979](https://arxiv.org/abs/2601.00979) ·
> [doi:10.4230/LIPIcs.AofA.2026.14](https://doi.org/10.4230/LIPIcs.AofA.2026.14)

The paper introduces the **block cycle** in-place array rotation algorithm and
analyses its cost. The key structural result (Lemma 12) is that the segment
lengths arising in the algorithm's recursion are exactly the remainders produced
by the Euclidean algorithm, so that the move count is

```
moveCount n k = n - gcd n k + 2 * remSum n k
```

where `remSum n k` is the sum of those remainders. The worst case is `3n` moves,
and the average is `D·n + O(n^(1/2+ε))` with `D ≈ 1.85`.

## Status

| Result | Paper | Lean | State |
| --- | --- | --- | --- |
| Remainder sum `remSum` | Lemma 12 | `BlockCycleRotation.remSum` | ✅ defined |
| Master inequality | (new, see below) | `remSum_add_gcd_le` | ✅ proved |
| Worst case `≤ 3(n − gcd)` | Thm A / Obs. 5 | `moveCount_add_gcd_le` | ✅ proved |
| Worst case `≤ 3n` | Thm A | `moveCount_le_three_mul` | ✅ proved |
| Algorithm's cost recursion | §2 | `BlockCycleRotation.cost` | ✅ defined |
| Lemma 12(1): stops at `gcd` | Lemma 12 | `finalSeg_eq_gcd` | ✅ proved |
| Lemma 12: algorithm ↔ Euclid | Lemma 12 | `remSum_congr_mod` | ✅ proved |
| Eq. (12): move count | Eq. (12) | `cost_add_gcd` | ✅ proved |
| Worst case, for the algorithm | Thm A | `cost_le_three_mul` | ✅ proved |
| Block cycle step is correct | §2, Fig. 1 | `rotate_block_step` | ✅ proved |
| Algorithm on lists | §2 | `BlockCycleRotation.bcRotate` | ✅ defined |
| It computes the rotation | §2 | `bcRotate_eq_rotate` | ✅ proved |
| Continuous cost `Ψ`, scaling | §3 | — | 🚧 planned |
| Average cost `avgCost` | Thm 13 | `BlockCycleRotation.avgCost` | ✅ defined |
| Average `≤ 3n` | (worst case) | `avgCost_le_three_mul` | ✅ proved |
| Obs. 15: Jordan on the circle | Obs. 15 | `mul_abs_le_norm_e_sub_one` | ✅ proved |
| Obs. 15: geometric sum bound | Obs. 15 | `norm_geom_sum_le` | ✅ proved |
| Obs. 15: weighted sum bound | Obs. 15 | `norm_weighted_geom_sum_le` | ✅ proved |
| Chord length `‖e θ − 1‖ = 2\|sin(θ/2)\|` | Obs. 15 | `norm_e_sub_one_eq` | ✅ proved |
| Root-of-unity chord bound | §4 | `four_mul_min_div_le_norm` | ✅ proved |
| Sums at roots of unity | §4 | `norm_geom_sum_root_le` | ✅ proved |
| `log a` factor, `∑ 1/min(m,a−m)` | Lemma 18 | `sum_inv_min_le` | ✅ proved |
| Character orthogonality | §4 | `sum_e_root` | ✅ proved |
| Inner sum `∑(A+Bb)e(2πmb/a)` | §4 | `norm_linear_geom_sum_root_le` | ✅ proved |
| Error term over all `m ≠ 0` | Lemma 18 | `norm_sum_twisted_le` | ✅ proved |
| Indicator via characters | §4 | `indicator_eq` | ✅ proved |
| Sum over an AP | §4 | `sum_ap_sub_main_le` | ✅ proved |
| Same, explicit `log a` | §4 | `sum_ap_sub_main_le_log` | ✅ proved |
| Continuant `K` | Heilbronn 1969 | `BlockCycleRotation.K` | ✅ defined |
| Euler's continuant identity | (gives `n = ab + a'b'`) | `K_append` | ✅ proved |
| Continuants are palindromic | Heilbronn 1969 | `K_reverse` | ✅ proved |
| Consecutive continuants coprime | (gives `gcd(a,a') = 1`) | `K_coprime` | ✅ proved |
| Size conditions `a > a' ≥ 1` | Heilbronn 1969 | `K_dropLast_lt'`, `K_tail_lt'` | ✅ proved |
| Heilbronn, forward direction | Heilbronn 1969 | `heilbronn_forward` | ✅ proved |
| Expansion via Euclid, `cf` | Heilbronn 1969 | `BlockCycleRotation.cf` | ✅ defined |
| Heilbronn, inverse direction | Heilbronn 1969 | `K_cf` | ✅ proved |
| Heilbronn, injectivity | Heilbronn 1969 | `cf_K` | ✅ proved |
| `cf` lands in normalised lists | Heilbronn 1969 | `cf_spec` | ✅ proved |
| **Heilbronn's bijection** | §4, Heilbronn 1969 | `heilbronn_bijection` | ✅ **proved** |
| Heilbronn, surjectivity on quadruples | §4, Heilbronn 1969 | `heilbronn_surjective` | ✅ proved |
| Eq. (RemainderSum): the bridge | Eq. (RemainderSum) | `remSum_eq_sum_K` | ✅ proved |
| Shift ↔ expansion bijection | §4 | `shift_expansion_bijection` | ✅ proved |
| LHS of (eq. heilbron) | §4 | `sum_remSum_eq` | ✅ proved |
| Round trip on a split | §4 | `heilbronn_split_roundtrip` | ✅ proved |
| Splits produce quadruples | §4 | `split_quadruple` | ✅ proved |
| Quadruple index set | §4 | `quadruples`, `split_mem_quadruples` | ✅ proved |
| Expansion attached to a quadruple | §4 | `quadExpansion_spec` | ✅ proved |
| Reindexing by quadruples | §4 | `sum_split_eq_sum_quadruples` | ✅ proved |
| Heilbronn identity, coprime form | §4 (display before eq. heilbron) | `heilbron_coprime` | ✅ proved |
| Remainder sum scales | §4 | `remSum_mul` | ✅ proved |
| Quadruples symmetric, `∑a = ∑b` | §4 | `sum_fst_eq_sum_snd` | ✅ proved |
| Shifts classified by `gcd(n,k)` | §4 | `sum_allShifts_eq` | ✅ proved |
| Quadruples classified by `gcd(b,b')` | §4 | `sum_snd_quadruplesAll` | ✅ proved |
| **Equation (eq. heilbron)** | §4 | `heilbron` | ✅ **proved** |
| Triple sum: inner sum over `b'` | §4 | `inner_sum_sub_main_le` | ✅ proved |
| `Q(n) = ∑_{d∣n} R(d)` | §4 | `sum_Rquad` | ✅ proved |
| Equation (mobius) | Eq. (mobius) | `moebius_Rquad` | ✅ proved |
| `∑ gcd(n,k) ≤ n·d(n)` | §4 | `sum_gcd_le` | ✅ proved |
| Equation (invquant) | Eq. (invquant) | `invquant` | ✅ proved |
| `b`-elimination to triples | §4 | `sum_snd_quadruplesQ_eq_triples` | ✅ proved |
| Coprime `b`-elimination | §4 | `sum_snd_quadruplesAll_eq` | ✅ proved |
| **The triple sum** | §4 | `Q_eq_tripleSum` | ✅ **proved** |
| Congruence → arithmetic progression | §4 | `exists_residue` | ✅ proved |
| Inner sum as an AP sum | §4 | `inner_sum_nat_eq` | ✅ proved |
| Triple sum decomposed by pairs | §4 | `Q_eq_tripleSum_decomposed` | ✅ proved |
| Symmetrisation `b > a` | §4 | `Q_symmetrise` | ✅ proved |
| Diagonal is `O(n^{1+ε})` | §4 | `sum_diag_isBigO` | ✅ proved |
| `b > a` through the classification | §4 | `sum_QGT_classify` | ✅ proved |
| **The paper's triple sum** | §4 | `Q_gt_tripleSum` | ✅ **proved** |
| Key restriction `d·a² < m` | §4 | `gtTriples_sq_lt` | ✅ proved |
| Paper's `U = min(…)` | §4 | `gtBound`, `mem_gtRange` | ✅ proved |
| Triple sum decomposed by pairs | §4 | `gtTriples_decompose` | ✅ proved |
| Progression estimate over `ℝ` | §4 | `sum_ap_sub_main_le_log_real` | ✅ proved |
| **Innermost estimation layer** | Lemmas 18–19 | `inner_gt_estimate` | ✅ **proved** |
| Pairs decomposed by first component | §4 | `sum_coprimePairs_filter` | ✅ proved |
| Admissible `a` number `≤ √((m−1)/d)` | §4 | `card_a_le` | ✅ proved |
| **Middle estimation layer** | Lemmas 18–19 | `middle_layer` | ✅ **proved** |
| **Outer estimation layer** | Lemmas 18–19 | `outer_layer` | ✅ **proved** |
| **Aggregate error `O(n^{3/2+ε})`** | Lemmas 18–19 | `error_isBigO` | ✅ **proved** |
| Constant `C` of eq. (const-c) | Eq. (const-c) | `cTerm`, `cTerm_row_le` | ✅ defined, bounded |
| Convergence of the series for `C` | Eq. (const-c) | `cTerm_summable` | ✅ proved |
| The constants `C` and `D = 1 + 4C` | Eq. (const-c) | `cConst`, `dConst` | ✅ defined |
| Summand identity for Lemma 17 | Lemma 17 | `cTerm_summand_eq` | ✅ proved |
| `C` as iterated / finite-row sums | Eq. (const-c) | `cConst_eq_tsum_finRows` | ✅ proved |
| Tail bound `∑_{a>N} 1/a² ≤ 1/N` | Lemma 17 | `sum_inv_sq_tail_le` | ✅ proved |
| Truncation error for `C` | Lemma 17 | `cConst_le_partial_add` | ✅ proved |
| Bulk/small split condition | Lemma 17 | `gtBound_bulk`, `gtTriples_bulk_small` | ✅ proved |
| Small branch: `2d·a² > m` | Lemma 17 | `small_two_mul_gt` | ✅ proved |
| AP counting `≤ U/a + 1` | Lemma 17 | `card_mod_filter_le` | ✅ proved |
| **Small-part bound `O(m^{3/2}√d)`** | Lemma 17 | `small_part_le` | ✅ **proved** |
| Closed form of the main term | Lemma 17 | `sum_linear_Ico` | ✅ proved |
| **Truncation of the series for `C`** | Lemma 17 | `cConst_le_bulk_add` | ✅ **proved** |
| Rounding term (paper's `G₂` form) | Lemma 17 / §4 | `main_term_vs_sum` | ✅ proved |
| Substitution: `C` appears | Lemma 17 | `main_term_substitute` | ✅ proved |
| Main term splits; partial sums squeezed | Lemma 17 | `G1_split`, `bulk_sum_close` | ✅ proved |
| **Lower-order part `O(m^{3/2}√d)`** | Lemma 17 | `lower_order_le` | ✅ **proved** |
| **Index reconciliation** | Lemma 17 | `bulk_double_le_pairs` | ✅ **proved** |
| Bulk pair sum within `3/(2N)` of `C` | Lemma 17 | `bulk_pairs_close` | ✅ proved |
| **`d`-sum: main terms** | Lemma 17 | `sum_div_sq_eq` | ✅ **proved** |
| `d`-sum: errors `≤ d(n)·n^{3/2}` | Lemma 17 | `error_per_divisor_le`, `sum_divisors_le` | ✅ proved |
| **Lemma 17, at a single divisor** | Lemma 17 | `lemma17_local` | ✅ **proved** |
| **Lemma 17** | Lemma 17 | `lemma17` | ✅ **proved** (errors as `∑_d E d`) |
| Instantiating `E` to get `O(n^{3/2+ε})` | Lemma 17 | — | 🚧 remaining |
| Theorem 13 | Thm 13 | — | 🚧 remaining |
| Theorem 13, constant `D = 1 + 4C` | Thm 13 | — | 🚧 remaining |
| `G₁ + G₂ + G₃` → `O(n^{3/2+ε})` | Lemmas 17–19 | — | 🚧 remaining |
| Theorem 13, constant `D = 1 + 4C` | Thm 13, §4 | — | 🚧 remaining |
| `G₁ + G₂ + G₃` assembly | Lemmas 17–19 | — | 🚧 remaining |
| Divisor bound `d(n) = O(nᵋ)` | §4 | `exists_card_divisors_le` | ✅ proved |
| Möbius/character decomposition | §4 | — | 🚧 planned |
| Limit `D = ∫₀¹ ρ` | Thm 10 | — | 🚧 planned |
| Error term `O(n^(1/2+ε))` | Thm 13 | — | 🚧 planned |
| Constant `D = 1 + 4C` via MZVs | §4 | — | 🚧 planned |

### A note on the worst-case proof

The bound one wants, `remSum n k + gcd n k ≤ n` for `2k ≤ n`, is not directly
provable by induction: the hypothesis `2k ≤ n` is **not** inherited by the
recursive call. For `n = 21`, `k = 8` the algorithm steps to `(8, 5)`, and
`2 · 5 > 8`. The formalisation instead proves the unconditional

```
remSum n k + gcd n k ≤ 2k + n mod k
```

which does propagate through the recursion, and which collapses to the desired
bound exactly when `2k ≤ n` (since then the first quotient is at least 2).

### The mirrored step

The block cycle step is degenerate when `⌊n/k⌋ = 1`, i.e. `k > n/2`: it moves
nothing and recurses on the whole list. This is the case the paper handles
"using symmetry", swapping the roles of the two segments. `bcRotate` implements
it by reversal, and terminates by a lexicographic measure on `(k, length)`: the
left step keeps `k` and shortens the list, the mirrored step decreases `k`.

## Verification against the paper

Observation 6 works out a left segment of length 8 and a right segment of
length 13 — that is `n = 21`, `k = 8` — with remainder sequence `8, 5, 3, 2, 1`
and a cost of 58 moves. Both are checked by `#guard` in `Euclid.lean`.

## Tier 3: the error term

Theorem 13 states `avgCost n = D·n + O(n^(1/2+ε))` with `D = 1 + 4C ≈ 1.85`.
Contrary to first appearances, its proof needs **no Kloosterman or Weil bounds**.
The only analytic input is Observation 15, now formalised in `ExpSum.lean`:

* Jordan's inequality on the circle, `(2/π)|θ| ≤ ‖e(θ) − 1‖` — Mathlib already
  has the hard half as `Real.mul_abs_le_abs_sin`;
* the *trivial* bound on a geometric sum, `‖Σ_{B≤j<T} e(jθ)‖ ≤ π/|θ|`;
* its weighted form, by the paper's double-counting argument.

`Characters.lean` then supplies the quantitative input for removing a congruence
condition `b ≡ c mod a` by additive characters: at a nontrivial `a`-th root of
unity the chord length satisfies `‖e(2πm/a) − 1‖ ≥ 4·min(m, a−m)/a`, so

```
‖∑_{B ≤ j < T} e(2πmj/a)‖ ≤ a / (2·min(m, a−m)).
```

Summing `1/min(m, a−m)` over `0 < m < a` is what produces the `log a` in Lemma 18;
`sum_inv_min_le` bounds that sum by twice a harmonic sum. `Orthogonality.lean`
supplies the identity that justifies the character expansion in the first place:

```
∑_{m < a} e(2πmr/a) = a  if a ∣ r,  and 0 otherwise.
```

`LinearSums.lean` then assembles these into the estimate §4 actually applies.
The sums it must control are `∑_{1≤b<T, b≡c mod a} (A + B·b)`; expanding the
congruence in characters turns the error into a weighted sum of
`∑_b (A + B·b)·e(2πmb/a)` over nontrivial `m`, with phases of modulus one, and

```
‖∑_m w_m ∑_b (A + B·b) e(2πmb/a)‖ ≤ (‖A‖ + ‖B‖(T−1)) · a · ∑_{0<m<a} 1/m,
```

whose harmonic sum is the `log a` of Lemma 18. `Progression.lean` then
instantiates the phases from `sum_e_root`, giving the estimate itself:

```
‖∑_{1≤b<T, b≡c mod a} (A + B·b) − (1/a)·∑_{1≤b<T} (A + B·b)‖
    ≤ (‖A‖ + ‖B‖(T−1)) · ∑_{0<m<a} 1/m.
```

Replacing a sum over an arithmetic progression by its expected value costs a
harmonic sum, i.e. `O(log a)`.

No square-root cancellation is used anywhere. What remains for Theorem 13 is
long rather than deep — there is no missing theorem to invent, just a great many
explicit estimates to carry out. The divisor bound, which Mathlib does not
provide, is proved in `DivisorBound.lean`: for each `ε > 0` there is `C` with
`d(n) ≤ C·n^ε`, by splitting the primes dividing `n` at `p^ε = 2`. Remaining: Möbius inversion over divisors (in Mathlib), additive
character orthogonality (in Mathlib, `AddChar.sum_eq_ite`), harmonic sums (in
Mathlib), and then the assembly of `G₁ + G₂ + G₃`. The one genuine gap is the
divisor bound `d(n) = O(n^ε)`, which is elementary but absent from Mathlib.

## Building

Requires [elan](https://github.com/leanprover/elan). Toolchain and Mathlib
revision are pinned (Lean 4.33.1 / Mathlib v4.33.1).

```sh
lake exe cache get   # fetch prebuilt Mathlib oleans
lake build
```

## Fidelity to the paper

**Formalised as stated.** §2 (the algorithm), Lemma 12, equation (12),
Theorem A's worst case, equation (RemainderSum), Observation 15, Heilbronn's
correspondence, and the coprime form of the Heilbronn identity follow the
paper's statements and proof structure.  Equation (eq. heilbron) itself, the
aggregate of that identity over the gcd, is `heilbron`.

**Deviations, all documented in the sources.** The worst-case bound needed a
strengthening — `remSum n k + gcd n k ≤ 2k + n mod k` — because the paper's
hypothesis `2k ≤ n` is not inherited by the recursion. `norm_sum_twisted_le`
is proved for arbitrary unit-modulus weights and specialised afterwards, and
`norm_geom_sum_le'` drops the `|θ| ≤ π` hypothesis so that it applies at roots
of unity.

**Proved here but not in the paper.** The divisor bound `d(n) = O(n^ε)` (cited
as standard, absent from Mathlib), Bernoulli's inequality, and the correctness
of the algorithm itself — the paper describes the block cycle scheme but never
proves that it computes a rotation, whereas `bcRotate_eq_rotate` does.

**Not attempted.** Everything from Lemma 17 onwards: the `(a,a')` and `d ∣ n`
layers of the triple sum, `G₁ + G₂ + G₃`, the error term of Theorem 13, the
constant `D = 1 + 4C` and its multiple-zeta-value series, Theorem 10's limit,
and the benchmarks of §5. This is the majority of §4 by length.

In short: the paper's structural results are formalised, and every tool its
analytic conclusion needs is proved, but that conclusion itself is not.
