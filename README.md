# block-cycle-rotation

A Lean 4 / Mathlib formalisation of

> Valentin Blomer and Kai-Uwe Bux,
> *The cost of cyclic permutations and remainder sums in the Euclidean algorithm*,
> AofA 2026, LIPIcs vol. 381, pp. 14:1–14:17.
> [arXiv:2601.00979](https://arxiv.org/abs/2601.00979) ·
> [doi:10.4230/LIPIcs.AofA.2026.14](https://doi.org/10.4230/LIPIcs.AofA.2026.14)

The paper introduces the **block cycle** in-place array rotation algorithm and
analyses its cost. The key structural result (Lemma 11) is that the segment
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
| Remainder sum `remSum` | Eq. (def-mbar), Lemma 11 | `BlockCycleRotation.remSum` | ✅ defined |
| Master inequality | (new, see below) | `remSum_add_gcd_le` | ✅ proved |
| Worst case `≤ 3(n − gcd)` | Thm A / Obs. 2 | `moveCount_add_gcd_le` | ✅ proved |
| Worst case `≤ 3n` | Thm A | `moveCount_le_three_mul` | ✅ proved |
| Algorithm's cost recursion | §2 | `BlockCycleRotation.cost` | ✅ defined |
| Lemma 11(1): stops at `gcd` | Lemma 11 | `finalSeg_eq_gcd` | ✅ proved |
| Lemma 11: algorithm ↔ Euclid | Lemma 11 | `remSum_congr_mod` | ✅ proved |
| Move count | Lemma 11(2), eq. (7) | `cost_add_gcd` | ✅ proved |
| Worst case, for the algorithm | Thm A | `cost_le_three_mul` | ✅ proved |
| Euclid step on Fibonacci pairs | Obs. 3 | `fib_mod_fib` | ✅ proved |
| `remSum F_{m+1} F_m = F_{m+2} − 2` | Obs. 3 | `remSum_fib_consec` | ✅ proved |
| `gcd(F_{m+2}, F_m) = 1` | Obs. 3 | `gcd_fib_add_two` | ✅ proved |
| **Obs. 3: Fibonacci worst case `3n − 5`** | Obs. 3 | `remSum_fib`, `moveCount_fib` | ✅ **proved** |
| The block cycle idea (expository) | Remark 1 | — | ➖ nothing to formalize |
| Type A moves number `2(k₁+k₂+⋯)` | Observation 10 | folded into `cost_add_gcd` | ➖ not stated separately |
| Type B moves number `n − gcd(n,k)` | Observation 12 | folded into `cost_add_gcd` | ➖ not stated separately |
| Block cycle step is correct | §2, Fig. 1 | `rotate_block_step` | ✅ proved |
| Algorithm on lists | §2 | `BlockCycleRotation.bcRotate` | ✅ defined |
| It computes the rotation | §2 | `bcRotate_eq_rotate` | ✅ proved |
| Average cost `avgCost` | Thm 14 | `BlockCycleRotation.avgCost` | ✅ defined |
| Average `≤ 3n` | (worst case) | `avgCost_le_three_mul` | ✅ proved |
| Obs. 17: Jordan on the circle | Obs. 17 | `mul_abs_le_norm_e_sub_one` | ✅ proved |
| Obs. 17: geometric sum bound | Obs. 17 | `norm_geom_sum_le` | ✅ proved |
| Obs. 17: weighted sum bound | Obs. 17 | `norm_weighted_geom_sum_le` | ✅ proved |
| Obs. 17: weighted sum, paper's constants | Obs. 17 | `weighted_geom_sum_closed`, `norm_weighted_geom_sum_le_sharp` | ✅ proved |
| Chord length `‖e θ − 1‖ = 2\|sin(θ/2)\|` | Obs. 17 | `norm_e_sub_one_eq` | ✅ proved |
| Root-of-unity chord bound | §4 | `four_mul_min_div_le_norm` | ✅ proved |
| Sums at roots of unity | §4 | `norm_geom_sum_root_le` | ✅ proved |
| `log a` factor, `∑ 1/min(m,a−m)` | Lemma 16 | `sum_inv_min_le` | ✅ proved |
| Character orthogonality | §4 | `sum_e_root` | ✅ proved |
| Inner sum `∑(A+Bb)e(2πmb/a)` | §4 | `norm_linear_geom_sum_root_le` | ✅ proved |
| Error term over all `m ≠ 0` | Lemma 16 | `norm_sum_twisted_le` | ✅ proved |
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
| **Innermost estimation layer** | Lemmas 16 and 18 | `inner_gt_estimate` | ✅ **proved** |
| Pairs decomposed by first component | §4 | `sum_coprimePairs_filter` | ✅ proved |
| Admissible `a` number `≤ √((m−1)/d)` | §4 | `card_a_le` | ✅ proved |
| **Middle estimation layer** | Lemmas 16 and 18 | `middle_layer` | ✅ **proved** |
| **Outer estimation layer** | Lemmas 16 and 18 | `outer_layer` | ✅ **proved** |
| **Aggregate error `O(n^{3/2+ε})`** | Lemmas 16 and 18 | `error_isBigO` | ✅ **proved** |
| Constant `C` of eq. (const-c) | Eq. (const-c) | `cTerm`, `cTerm_row_le` | ✅ defined, bounded |
| Convergence of the series for `C` | Eq. (const-c) | `cTerm_summable` | ✅ proved |
| The constants `C` and `D = 1 + 4C` | Eq. (const-c) | `cConst`, `dConst` | ✅ defined |
| Summand identity for Lemma 19 | Lemma 19 | `cTerm_summand_eq` | ✅ proved |
| `C` as iterated / finite-row sums | Eq. (const-c) | `cConst_eq_tsum_finRows` | ✅ proved |
| Tail bound `∑_{a>N} 1/a² ≤ 1/N` | Lemma 19 | `sum_inv_sq_tail_le` | ✅ proved |
| Truncation error for `C` | Lemma 19 | `cConst_le_partial_add` | ✅ proved |
| Bulk/small split condition | Lemma 19 | `gtBound_bulk`, `gtTriples_bulk_small` | ✅ proved |
| Small branch: `2d·a² > m` | Lemma 19 | `small_two_mul_gt` | ✅ proved |
| AP counting `≤ U/a + 1` | Lemma 19 | `card_mod_filter_le` | ✅ proved |
| **Small-part bound `O(m^{3/2}√d)`** | Lemma 19 | `small_part_le` | ✅ **proved** |
| Closed form of the main term | Lemma 19 | `sum_linear_Ico` | ✅ proved |
| **Truncation of the series for `C`** | Lemma 19 | `cConst_le_bulk_add` | ✅ **proved** |
| Rounding term (paper's `G₂` form) | Lemma 19 / §4 | `main_term_vs_sum` | ✅ proved |
| Substitution: `C` appears | Lemma 19 | `main_term_substitute` | ✅ proved |
| Main term splits; partial sums squeezed | Lemma 19 | `G1_split`, `bulk_sum_close` | ✅ proved |
| **Lower-order part `O(m^{3/2}√d)`** | Lemma 19 | `lower_order_le` | ✅ **proved** |
| **Index reconciliation** | Lemma 19 | `bulk_double_le_pairs` | ✅ **proved** |
| Bulk pair sum within `3/(2N)` of `C` | Lemma 19 | `bulk_pairs_close` | ✅ proved |
| **`d`-sum: main terms** | Lemma 19 | `sum_div_sq_eq` | ✅ **proved** |
| `d`-sum: errors `≤ d(n)·n^{3/2}` | Lemma 19 | `error_per_divisor_le`, `sum_divisors_le` | ✅ proved |
| **Lemma 19, at a single divisor** | Lemma 19 | `lemma17_local` | ✅ **proved** |
| **Lemma 19** | Lemma 19 | `lemma17` | ✅ **proved** (errors as `∑_d E d`) |
| **Lemma 19, error instantiated** | Lemma 19 | `lemma17_final`, `Eterm` | ✅ **proved** |
| Cut-off lower bound `m ≤ 16d·N²` | Lemma 19 | `cutoff_lower`, `sqrt_le_cutoff` | ✅ proved |
| **Per-divisor error `≤ (8+2C)·n^{3/2}`** | Lemma 19 | `Eterm_le` | ✅ **proved** |
| **Lemma 19, `O(n^{3/2+ε})` form** | Lemma 19 | `lemma17_isBigO` | ✅ **proved** |
| Cut-off on the bulk branch | Lemmas 16 and 18 | `gtBound_bulk_eq` | ✅ proved |
| **Estimate at one coprime pair** | Lemmas 16 and 18 | `bulk_pair_estimate` | ✅ **proved** |
| Bulk triple sum, by pairs | Lemmas 16 and 18 | `gtTriples_bulk_decompose` | ✅ proved |
| **Estimate at one divisor** | Lemmas 16 and 18 | `divisor_estimate` | ✅ **proved** |
| **`G₁ + G₂ + G₃`: `Q_gt = G₁ + O(…)`** | Lemmas 16 and 18 | `Qgt_sub_G1_le` | ✅ **proved** |
| Decomposition `G₁ + G₂ + G₃` | Lemmas 16, 18 and 19 | `innerActual_decompose` | ✅ proved |
| **Lemma 16: `G₂(n) = O(n^{3/2+ε})`** | Lemma 16 | `abs_G2term_le`, `lemma_g_two` | ✅ **proved** |
| **Lemma 18: `G₃(n) = O(n^{3/2+ε})`** | Lemma 18 | `abs_G3term_le`, `lemma_g_three` | ✅ **proved** |
| **`Q(n) = C·n²·∑ 1/d² + O(n^{3/2+ε})`** | Thm 14 | `Q_isBigO` | ✅ **proved** |
| Möbius inversion of `∑_{d∣n} d²` | Thm 14 | `moebius_main` | ✅ proved |
| **`R(n) = C·n² + O(n^{3/2+ε})`** | Thm 14 | `R_isBigO` | ✅ **proved** |
| **`∑_{2k≤n} remSum = C·n² + O(…)`** | Thm 14 | `sum_remSum_isBigO` | ✅ **proved** |
| Symmetry `M(n,k) = M(n,n−k)` | Thm 14 | `sum_min_eq`, `sum_algCost_eq` | ✅ proved |
| Cost over shifts via `cost + gcd` | Thm 14 | `sum_cost_allShifts` | ✅ proved |
| **Theorem 14, `D = 1 + 4C ≈ 1.85`** | Thm 14 | `theorem13` | ✅ **proved** |
| Relative recursion `In`, `Out`, and `Out ≤ 2/3` | Observation 4 | `Inn`, `Outt`, `Outt_le` | ✅ proved |
| The series for `ψ` converges; `ψ = lim_β ψ_β` | Eq. (defpsi), Thm 7 | `psi_summable`, `psi_le_three` | ✅ proved |
| Functional equation for `ψ` | Eq. (essential-recurrence) | `psi_eq` | ✅ proved |
| **`n·ψ(k/n) = 2·remSum(n,k)`** | Lemma 11(2) | `psi_rat` | ✅ **proved** |
| **Equation (relation)** | §3 | `relation`, `fCost` | ✅ **proved** |
| **Theorem 7: continuity at irrationals** | Thm 7 | `continuousAt_psi`, `continuousAt_fCost` | ✅ **proved** |
| `μ(N,ℓ,β) ≤ 3N`, i.e. `f ≤ 3` | Observation 5 | `psi_le_two`, `fCost_le_three` | ✅ proved |
| **Theorem 7: Riemann integrability** | Thm 7 | `fBar_hasBoxIntegral` | ✅ **proved** |
| Evenly spaced Riemann sums | Thm 9 | `integralSum_prepartition`, `tendsto_riemann_fBar` | ✅ proved |
| `∑_{k<n} gcd(n,k) = o(n²)` | Thm 9 | `sum_gcd_range_le` | ✅ proved |
| `f(1−x) = f(x)`, `∫₀¹ = 2∫₀^{1/2}` | Thm 9 | `fCost_symm`, `integral_fCost_split` | ✅ proved |
| **Theorem 9** | Thm 9 | `theorem10` | ✅ **proved** |
| `f^j` Riemann integrable | Corollary 8 | `fBar_pow_hasBoxIntegral` | ✅ proved |
| Uniform distribution on `[0,1/2]` | Corollary 8 | `unifHalf` | ✅ defined |
| Moments of all orders exist | Corollary 8 | `integrable_fCost_pow` | ✅ proved |
| **`E[f(X)^j] = (∫₀^{1/2} f^j)/(1/2)`** | Corollary 8 | `moment_fCost` | ✅ **proved** |
| Segments `segᵢ`, buffered cost `f_β` | Remark 13 | `seg`, `psiBuf`, `fCostBuf` | ✅ defined |
| **Recursion, eq. (def-mu-nu)** | Remark 13 | `psiBuf_rec` | ✅ **proved** |
| The buffer never hurts, `f_β ≤ f` | Corollary 6(1) | `fCostBuf_le_fCost` | ✅ proved |
| Monotone in the buffer size | Corollary 6(1) | `psiBuf_antitone` | ✅ proved |
| **Buffer helps though no segment fits** | Remark 13 | `buffer_helps` | ✅ **proved** |
| Figure's `1.25` at a 50% buffer | Fig. 6 caption | `expected_cost_half_buffer` | ✅ proved |
| **Buffered cost `μ(N,ℓ,β)`** | Eq. (continuous) | `muCost` | ✅ **defined** |
| Eq. (def-mu-nu), both branches | Eq. (def-mu-nu) | `muCost_rec_of_le`, `muCost_rec_of_gt` | ✅ proved |
| Observation `μ(N,ℓ,β) ≤ 3N` | Observation 5 | `muCost_le_three_mul` | ✅ proved |
| Corollary 6(1): `μ` decreases in `β` | Corollary 6(1) | `muCost_antitone` | ✅ proved |
| Corollary 6(2): `μ(λN,λℓ,λβ) = λμ(N,ℓ,β)` | Corollary 6(2) | `muCost_homogeneous` | ✅ proved |
| `f_β(ℓ) = μ(1,ℓ,β)` | Remark 13 | `muCost_one` | ✅ proved |
| **Eq. (integral): buffered move count** | Eq. (integral) | `costB` | ✅ **defined** |
| **Corollary 6(3): `Cost(n,k,β) ≤ μ(n,k,β)`** | Corollary 6(3) | `costB_le_muCost` | ✅ **proved** |
| Eq. (integral) at `β = 0` is Lemma 11 | §2–3 | `costB_eq_moveCount` | ✅ proved |
| Corollary 6(3), unbuffered limit | Corollary 6(3) | `cost_le_muCost` | ✅ proved |
| **Segments halve every two steps** | §3 | `seg_add_two_le` | ✅ **proved** |
| **`ψ = lim_{β→0⁺} ψ_β`, with `ψ − ψ_β ≤ 8β`** | §3 | `tendsto_psiBuf` | ✅ **proved** |
| **Reflection `remSum n k = k + remSum n (n−k)`** | Remark 20 | `remSum_reflect` | ✅ **proved** |
| `∑_{k>n/2} k = 3n²/8 + O(n)` | Remark 20 | `sum_bigShifts_id_close` | ✅ proved |
| **Average over `1 ≤ k ≤ n` is `(3/8+2C)n + O(n^{1/2+ε})`** | Remark 20 | `remark_all_shifts` | ✅ **proved** |
| Sharper `cTerm ≤ 1/a³`, tail `≤ 1/N` | §4 | `cTerm_le_cube`, `cConst_le_partial_add_sharp` | ✅ proved |
| Certified `partial(20) ≤ 39/200` | §4 | `cConst_partial_le` | ✅ proved |
| **`D < 2`** (beats trinity rotation on average) | Remark 15 | `dConst_lt_two` | ✅ **proved** |
| `1 < D` | Remark 15 | `one_lt_dConst` | ✅ proved |
| Row bound `∑_{a'<a} gTerm ≤ 5/(8a²)` | §4 | `gTerm_row_le` | ✅ proved |
| `ζ(3) ∈ [1.2018, 1.2023]` | Remark 21 | `zeta3_ge`, `zeta3_le` | ✅ proved |
| **`D ≤ 1.85`**, the paper's value | Thm A / Thm 14 | `dConst_le_185` | ✅ **proved** |
| Row bound from below `≥ 5(a−1)/(9a³)` | §4 | `gTerm_row_ge` | ✅ proved |
| **`1.84 ≤ D ≤ 1.85`** | Thm A / Thm 14 | `dConst_enclosure` | ✅ **proved** |
| Summand rewriting | Remark 21 | `gTerm_eq` | ✅ proved |
| `ζ(3)` removes the coprimality | Remark 21 | `tsum_gTerm_eq`, `zeta3_mul_cConst` | ✅ proved |
| Telescoping `∑_k [1/k − 1/(n+k)] = H_n` | Remark 21 | `tsum_telescope` | ✅ proved |
| `1/(n(n+k)²) + 1/(k(n+k)²) = 1/(nk(n+k))` | Remark 21 | `pTerm_add_swap` | ✅ proved |
| **Euler's `ζ(2,1) = ζ(3)`** | Remark 21 (cited) | `euler_zeta21` | ✅ **proved** |
| **Eq. (const-c-alternative)** | Remark 21 | `cConst_eq_alternative` | ✅ **proved** |
| Truncations bound `C`, `D` above | Remark 21 | `cConst_le_truncation`, `dConst_le_truncation` | ✅ proved |
| Divisor bound `d(n) = O(nᵋ)` | §4 | `exists_card_divisors_le` | ✅ proved |

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

Observation 3 works out a left segment of length 8 and a right segment of
length 13 — that is `n = 21`, `k = 8` — with remainder sequence `8, 5, 3, 2, 1`
and a cost of 58 moves. Both are checked by `#guard` in `Euclid.lean`. The
observation's general claim, that the Fibonacci pairs `k = F_m`, `n = F_{m+2}`
cost `3∑_{j≤m} F_j − 2 = 3n − 3gcd(n,k) − 2` moves, is `moveCount_fib`: those
pairs sit exactly two moves below the worst case of Theorem A.

## Tier 3: the error term

Theorem 14 states `avgCost n = D·n + O(n^(1/2+ε))` with `D = 1 + 4C ≈ 1.85`.
Contrary to first appearances, its proof needs **no Kloosterman or Weil bounds**.
The only analytic input is Observation 17, now formalised in `ExpSum.lean`:

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

Summing `1/min(m, a−m)` over `0 < m < a` is what produces the `log a` in Lemma 16;
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

whose harmonic sum is the `log a` of Lemma 16. `Progression.lean` then
instantiates the phases from `sum_e_root`, giving the estimate itself:

```
‖∑_{1≤b<T, b≡c mod a} (A + B·b) − (1/a)·∑_{1≤b<T} (A + B·b)‖
    ≤ (‖A‖ + ‖B‖(T−1)) · ∑_{0<m<a} 1/m.
```

Replacing a sum over an arithmetic progression by its expected value costs a
harmonic sum, i.e. `O(log a)`.

No square-root cancellation is used anywhere. The divisor bound, which Mathlib
does not provide, is proved in `DivisorBound.lean`: for each `ε > 0` there is
`C` with `d(n) ≤ C·n^ε`, by splitting the primes dividing `n` at `p^ε = 2`.
With that in hand the three pieces of §4 are complete: `lemma17` (the main term
and the constant `C`), `lemma_g_two` and `lemma_g_three` (the two error terms),
and `theorem13` assembles them.

## Citations

Every reference to a numbered result cites **arXiv:2601.00979v1** (32 pages), the
full version that the LIPIcs proceedings entry links to. In that version all
numbered environments share a single counter, running

> Remark 1, Obs. 2, Obs. 3, Obs. 4, Obs. 5, Cor. 6, Thm 7, Cor. 8, Thm 9, Obs. 10,
> Lemma 11, Obs. 12, Rem. 13, Thm 14, Rem. 15, Lemma 16, Obs. 17, Lemma 18,
> Lemma 19, Rem. 20, Rem. 21.

The published LIPIcs version (17 pages) numbers its results differently — its main
theorem is numbered 10 there, not 14 — so numbers here will not match it.
Equations are cited by the paper's own labels, `(relation)`, `(RemainderSum)`,
`(mobius)`, `(const-c)`, `(def-mu-nu)`, `(integral)`, `(continuous)`,
`(invquant)`, `(const-c-alternative)`, which are stable across both versions.

**Identifiers keep their original names.** `theorem13` is the paper's Theorem 14,
`theorem10` is Theorem 9, and the `lemma17*` family is Lemma 19; the files
`Theorem13.lean` and `Theorem10.lean` are named to match those identifiers.
`Remark21.lean` happens to be correct. The names are left alone because they are
published under those identifiers on Prove2me, where names are immutable.

## Building

Requires [elan](https://github.com/leanprover/elan). Toolchain and Mathlib
revision are pinned (Lean 4.33.1 / Mathlib v4.33.1).

```sh
lake exe cache get   # fetch prebuilt Mathlib oleans
lake build
```

## Fidelity to the paper

**Formalised as stated.** §2 (the algorithm), Lemma 11, equation (7),
Theorem A's worst case, equation (RemainderSum), Observation 17, Heilbronn's
correspondence, and the coprime form of the Heilbronn identity follow the
paper's statements and proof structure.  Equation (eq. heilbron) itself, the
aggregate of that identity over the gcd, is `heilbron`.

**Deviations, all documented in the sources.** The paper counts the moves in two halves — the type A moves of Observation 10 and the type B moves of Observation 12 — and adds them. `cost_add_gcd` instead proves the combined identity by one induction on the algorithm's recursion, because `cost` is modelled as a cost recursion rather than as a sequence of individual moves; neither half is stated on its own. Remark 20, on averaging over all
shifts, states the reflection for `n > k ≥ n/2`; the hypothesis must be strict,
since at `2k = n` it would read `k = k + k` (there `remSum n (n/2) = n/2` while
`k + remSum n (n−k) = n`). `remSum_reflect` assumes `n < 2k`, and the
conclusion is unaffected — that one term contributes `O(n)` to a sum of size
`Θ(n²)`. The worst-case bound needed a
strengthening — `remSum n k + gcd n k ≤ 2k + n mod k` — because the paper's
hypothesis `2k ≤ n` is not inherited by the recursion. `norm_sum_twisted_le`
is proved for arbitrary unit-modulus weights and specialised afterwards, and
`norm_geom_sum_le'` drops the `|θ| ≤ π` hypothesis so that it applies at roots
of unity. Observation 17's weighted bound is available both in the paper's
form, `π²/(2θ²) + (T−1)π/(2|θ|)` (`norm_weighted_geom_sum_le_sharp`), and in a
simpler `(T−1)π/|θ|` form (`norm_weighted_geom_sum_le`); the estimation chain
of Lemma 18 uses the latter, which is what the character argument needs and
which yields the same `log a`.

**Proved here but not in the paper.** Euler's `ζ(2,1) = ζ(3)`, which Remark 21
cites and Mathlib does not have (no multiple-zeta-value theory), the divisor
bound `d(n) = O(n^ε)` (cited as standard, absent from Mathlib), Bernoulli's
inequality, and the correctness of the algorithm itself — the paper describes the block cycle scheme but never
proves that it computes a rotation, whereas `bcRotate_eq_rotate` does.

**Not attempted.** The benchmarks of §5, which are C++ listings and wall-clock
timings on a named CPU — empirical claims with no mathematical content a proof
assistant can certify. Also Remark 15's "standard deviation about 0.50", which
the paper itself obtains by numerical approximation rather than proof: the
moment machinery is there (`moment_fCost`, `integrable_fCost_pow`), but no
certified bound on the variance is proved. The measure-theoretic
development uses the crude `f ≤ 4` (from `∑ (2/3)^i = 3`); the sharp `f ≤ 3` is
proved separately as `fCost_le_three`, but the paper's *attainment* of `3` at
`1 - φ` is not formalised. Remark (blend rotation) is a comparison with the
literature, with nothing to certify.

**Theorem 9 is proved independently of Theorem 14**, as the paper has it: from
eq. (relation), the `O(n^{1+ε})` bound on `∑ gcd(n,k)`, and Riemann
integrability applied to the evenly spaced subdivision. The two theorems
therefore give two independent routes to the constant, and they agree
numerically: `2∫₀^{1/2} f = 1.84522 ± 0.00141` by Monte Carlo, against the
rigorous enclosure `D ∈ [1.8455, 1.8459]`.

In short: Theorem 14 — the paper's main theorem — is proved, sorry-free, in the
form `avgCost n = D·n + O(n^{1/2+ε})` with `D = 1 + 4C`, and `C` is available in
both of the paper's forms: the double series of eq. (const-c) and the
`ζ(3)` expression of eq. (const-c-alternative).
