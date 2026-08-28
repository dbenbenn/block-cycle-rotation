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
| Data-level correctness (it rotates) | §2 | — | 🚧 planned |
| Continuous cost `Ψ`, scaling | §3 | — | 🚧 planned |
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

## Verification against the paper

Observation 6 works out a left segment of length 8 and a right segment of
length 13 — that is `n = 21`, `k = 8` — with remainder sequence `8, 5, 3, 2, 1`
and a cost of 58 moves. Both are checked by `#guard` in `Euclid.lean`.

## Building

Requires [elan](https://github.com/leanprover/elan). Toolchain and Mathlib
revision are pinned (Lean 4.33.1 / Mathlib v4.33.1).

```sh
lake exe cache get   # fetch prebuilt Mathlib oleans
lake build
```
