import BlockCycleRotation.Buffer

/-!
# Equation (1): the move count of the block cycle method

**This file is new mathematics, not a transcription of the paper.**  Nothing in
the certification of Blomer--Bux depends on it; deleting this file leaves the
status tables intact.

Blomer--Bux introduce `m(n,k,b)` as *the number of moves the block cycle method
needs* to rotate an array of length `n` by `k` with a buffer of `b` cells, and
then state equation (1), the three-branch recursion, as something they *find* to
hold.  Elsewhere in this development that recursion is the **definition** of
`costB`, so the step from the operational move count to the recursion is assumed.
This file supplies the missing half: an explicit move-level model of the
algorithm, whose move count is *counted* rather than stipulated.

## What counts as a move

§2 of the paper fixes the unit: "a cyclic permutation of order `m` can be
performed using `m+1` moves (using just one additional cell of memory)", and the
block step "moved `(q-1)k` elements into their final position using `(q+1)k`
moves".  So a **move is one element copy**, and copies into and out of auxiliary
memory are counted like any other.  That is what `Move` below is.

## Why this is not circular

A program could be made cheap by doing less work.  The content is that *one*
program is simultaneously
* correct -- running it rotates the array (`bcProg_correct`, still open), and
* buffer-respecting -- it touches no auxiliary cell numbered `≥ b`
  (`bcProg_usesBuffer`),
and *that* program has exactly `costB n k b` moves (`bcProg_length`).  The
recursion is then a theorem about a concrete artifact rather than a definition.

In particular the buffered branch needs no axiom.  "A segment of length `k ≤ b`
goes into the buffer at a cost of `k`" is not assumed here: `bufStep` emits `k`
copies in, `n - k` shifts, and `k` copies out, and its cost `n + k` is the
length of that list.
-/

namespace BlockCycleRotation

/-- A location the algorithm may read or write: a cell of the array, or a cell
of the auxiliary buffer. -/
inductive Loc
  | arr (i : ℕ)
  | buf (j : ℕ)
  deriving DecidableEq, Repr

/-- A move copies the contents of one location into another.  This is the
paper's unit of cost. -/
structure Move where
  src : Loc
  dst : Loc
  deriving DecidableEq, Repr

/-- A program is a finite sequence of moves. -/
abbrev Prog := List Move

/-- The number of moves a program makes. -/
def moves (p : Prog) : ℕ := p.length

@[simp] theorem moves_nil : moves [] = 0 := rfl
@[simp] theorem moves_cons (m : Move) (p : Prog) : moves (m :: p) = moves p + 1 := by
  simp [moves, List.length_cons]
@[simp] theorem moves_append (p q : Prog) : moves (p ++ q) = moves p + moves q := by
  simp [moves]

/-- The machine state: an array and an auxiliary buffer, both modelled as total
functions so that no bounds obligations intrude on the cost accounting. -/
structure State (α : Type*) where
  arr : ℕ → α
  buf : ℕ → α

variable {α : Type*} [DecidableEq α]

/-- Read a location. -/
def State.get (s : State α) : Loc → α
  | .arr i => s.arr i
  | .buf j => s.buf j

/-- Write a value to a location. -/
def State.set (s : State α) : Loc → α → State α
  | .arr i, v => { s with arr := Function.update s.arr i v }
  | .buf j, v => { s with buf := Function.update s.buf j v }

/-- Perform one move. -/
def State.step (s : State α) (m : Move) : State α := s.set m.dst (s.get m.src)

/-- Run a program. -/
def run (p : Prog) (s : State α) : State α := p.foldl State.step s

@[simp] theorem run_nil (s : State α) : run [] s = s := rfl

@[simp] theorem run_cons (m : Move) (p : Prog) (s : State α) :
    run (m :: p) s = run p (s.step m) := rfl

theorem run_append (p q : Prog) (s : State α) : run (p ++ q) s = run q (run p s) := by
  induction p generalizing s with
  | nil => simp
  | cons m p ih => simp [ih]

/-- A program respects a buffer of `b` cells if it never names an auxiliary cell
numbered `b` or higher.  Without this, "using a buffer of size `b`" would be
vacuous: unbounded scratch space makes any rotation cheap. -/
def UsesBuffer (b : ℕ) (p : Prog) : Prop :=
  ∀ m ∈ p, (∀ j, m.src = .buf j → j < b) ∧ (∀ j, m.dst = .buf j → j < b)

theorem usesBuffer_nil (b : ℕ) : UsesBuffer b [] := by simp [UsesBuffer]

theorem usesBuffer_append {b : ℕ} {p q : Prog}
    (hp : UsesBuffer b p) (hq : UsesBuffer b q) : UsesBuffer b (p ++ q) := by
  intro m hm
  rcases List.mem_append.1 hm with h | h
  · exact hp m h
  · exact hq m h

end BlockCycleRotation

namespace BlockCycleRotation

/-! ## The two steps of the algorithm

Each is an explicit list of moves.  Their costs are the lengths of those lists,
not numbers written down by hand. -/

/-- One cycle of the block step, on the positions `i, i+k, …, i+(q-1)k`.

This is the paper's "cyclic permutation of order `q` … using just one additional
cell of memory": save `a i` to the auxiliary cell, shift the `q-1` later entries
of the cycle down one block, and restore the saved entry at the top.  Hence
`q+1` moves. -/
def cycleProg (k q i : ℕ) : Prog :=
  ⟨.arr i, .buf 0⟩ ::
    ((List.range (q - 1)).map (fun j => ⟨.arr (i + (j + 1) * k), .arr (i + j * k)⟩)
      ++ [⟨.buf 0, .arr (i + (q - 1) * k)⟩])

theorem cycleProg_length {q : ℕ} (k i : ℕ) (hq : 1 ≤ q) :
    moves (cycleProg k q i) = q + 1 := by
  simp only [cycleProg, moves, List.length_cons, List.length_append, List.length_map,
    List.length_range, List.length_nil]
  omega

/-- The block step rotates the first `q = ⌊n/k⌋` blocks of length `k` left by one
block, as `k` independent cycles of order `q`. -/
def blockStep (n k : ℕ) : Prog :=
  (List.range k).flatMap (fun i => cycleProg k (n / k) i)

/-- **The paper's `(q+1)k`.**  §2: the block step "moved `(q-1)k` elements into
their final position using `(q+1)k` moves". -/
theorem blockStep_length {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n) :
    moves (blockStep n k) = (n / k + 1) * k := by
  have hq : 1 ≤ n / k := (Nat.one_le_div_iff hk).2 hkn
  have : ∀ i ∈ List.range k, (cycleProg k (n / k) i).length = n / k + 1 := by
    intro i _
    simpa [moves] using cycleProg_length (q := n / k) k i hq
  simp only [blockStep, moves, List.length_flatMap]
  rw [List.map_congr_left this]
  simp [Nat.mul_comm]

/-- The buffered step, available when the shift fits in the buffer.  Copy the
first `k` entries into the buffer, shift the remaining `n-k` down by `k`, and
write the buffer back at the top. -/
def bufStep (n k : ℕ) : Prog :=
  (List.range k).map (fun j => ⟨.arr j, .buf j⟩)
    ++ (List.range (n - k)).map (fun j => ⟨.arr (j + k), .arr j⟩)
    ++ (List.range k).map (fun j => ⟨.buf j, .arr (n - k + j)⟩)

/-- **The paper's `n+k`, counted rather than assumed.**  `k` copies in, `n-k`
shifts, `k` copies out. -/
theorem bufStep_length {n k : ℕ} (hkn : k ≤ n) : moves (bufStep n k) = n + k := by
  simp only [bufStep, moves, List.length_append, List.length_map, List.length_range]
  omega

/-! ## The algorithm -/

/-- The block cycle method as a program: nothing to do when the shift is zero,
one buffered step when the shift fits in the buffer, otherwise a block step
followed by the same method on the shorter remaining segment. -/
def bcProg (n k b : ℕ) : Prog :=
  if h : k = 0 then []
  else if k ≤ b then bufStep n k
  else blockStep n k ++ bcProg (k + n % k) (n % k) b
termination_by k
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero h)

@[simp] theorem bcProg_zero (n b : ℕ) : bcProg n 0 b = [] := by rw [bcProg]; simp

theorem bcProg_of_le {n k b : ℕ} (hk : k ≠ 0) (h : k ≤ b) : bcProg n k b = bufStep n k := by
  rw [bcProg]; simp [hk, h]

theorem bcProg_of_gt {n k b : ℕ} (hk : k ≠ 0) (h : b < k) :
    bcProg n k b = blockStep n k ++ bcProg (k + n % k) (n % k) b := by
  rw [bcProg]; simp [hk, Nat.not_le.2 h]

end BlockCycleRotation

namespace BlockCycleRotation

/-! ## Equation (1), counted

`bcProg_length` is the half of equation (1) this file exists to supply: the
length of the emitted program -- an operational quantity -- satisfies the
paper's recursion. -/

/-- **Equation (1).**  The block cycle method makes exactly `costB n k b` moves. -/
theorem bcProg_length : ∀ k n b : ℕ, k ≤ n → moves (bcProg n k b) = costB n k b := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro n b hkn
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · by_cases hb : k ≤ b
      · rw [bcProg_of_le hk.ne' hb, costB_of_le hk.ne' hb, bufStep_length hkn]
      · push_neg at hb
        have hmod : n % k < k := Nat.mod_lt _ hk
        rw [bcProg_of_gt hk.ne' hb, costB_of_gt hk.ne' hb, moves_append,
          blockStep_length hk hkn, ih (n % k) hmod (k + n % k) b (by omega)]

/-! ## The buffer discipline

Without a bound on which auxiliary cells the program may touch, "with a buffer
of `b` cells" would carry no content.  The block step needs the paper's one
additional cell; the buffered step needs `k ≤ b` of them. -/

theorem cycleProg_usesBuffer {b : ℕ} (hb : 1 ≤ b) (k q i : ℕ) :
    UsesBuffer b (cycleProg k q i) := by
  intro m hm
  simp only [cycleProg, List.mem_cons, List.mem_append, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false] at hm
  refine ⟨?_, ?_⟩ <;> intro j hj <;>
    rcases hm with h | ⟨t, _, h⟩ | h <;> subst h <;> (cases hj <;> omega)

theorem blockStep_usesBuffer {b : ℕ} (hb : 1 ≤ b) (n k : ℕ) :
    UsesBuffer b (blockStep n k) := by
  intro m hm
  simp only [blockStep, List.mem_flatMap, List.mem_range] at hm
  obtain ⟨i, _, hi⟩ := hm
  exact cycleProg_usesBuffer hb k (n / k) i m hi

theorem bufStep_usesBuffer {n k b : ℕ} (h : k ≤ b) : UsesBuffer b (bufStep n k) := by
  intro m hm
  simp only [bufStep, List.mem_append, List.mem_map, List.mem_range] at hm
  refine ⟨?_, ?_⟩ <;> intro i hi <;>
    rcases hm with (⟨j, hj, h⟩ | ⟨j, hj, h⟩) | ⟨j, hj, h⟩ <;> subst h <;> (cases hi <;> omega)

/-- **The program respects its buffer.**  One auxiliary cell is required -- the
paper's own hypothesis for the unbuffered scheme -- and no cell numbered `b` or
higher is ever named. -/
theorem bcProg_usesBuffer : ∀ k n b : ℕ, 1 ≤ b → UsesBuffer b (bcProg n k b) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro n b hb
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simpa using usesBuffer_nil b
    · by_cases hle : k ≤ b
      · rw [bcProg_of_le hk.ne' hle]; exact bufStep_usesBuffer hle
      · push_neg at hle
        rw [bcProg_of_gt hk.ne' hle]
        exact usesBuffer_append (blockStep_usesBuffer hb n k)
          (ih (n % k) (Nat.mod_lt _ hk) (k + n % k) b hb)

end BlockCycleRotation

namespace BlockCycleRotation

/-! ## Sanity checks

Spot checks on the model before anything is proved about it.  The move count
agrees with `costB` and with the unbuffered `cost`, and the buffered branch
does perform the rotation. -/

private def toArr (l : List ℕ) : ℕ → ℕ := fun i => l.getD i 0
private def readBack (n : ℕ) (s : State ℕ) : List ℕ := (List.range n).map s.arr
private def sim (l : List ℕ) (k b : ℕ) : List ℕ :=
  readBack l.length (run (bcProg l.length k b) ⟨toArr l, fun _ => 0⟩)

-- the counted cost agrees with the recursion, and with the unbuffered `cost`
#guard (bcProg 21 8 0).length = costB 21 8 0
#guard (bcProg 21 8 0).length = cost 21 8
#guard (bcProg 100 37 0).length = costB 100 37 0
#guard (bcProg 100 37 5).length = costB 100 37 5

-- the buffered branch rotates
#guard sim [0,1,2,3,4,5,6,7,8,9] 3 5 = ([0,1,2,3,4,5,6,7,8,9] : List ℕ).rotate 3
#guard sim [0,1,2,3,4] 2 4 = ([0,1,2,3,4] : List ℕ).rotate 2

/-! ## What remains open

`bcProg` is **not** yet correct in the unbuffered branch, and the reason is
worth recording precisely, because it is the same subtlety that makes equation
(1) more than bookkeeping.  Two obstacles, both visible by evaluation:

**1. The subproblem is not at the origin.**  After the block step the paper
reduces to a rotation "within the segment `a_{(q-1)k+1}, …, a_n`" -- an interval
starting at offset `(q-1)k`, not at `0`.  `bcProg` recurses without tracking
that offset, so the recursive moves address the wrong cells.  This is a
bookkeeping fix: carry an offset and shift every `Loc.arr` index by it.
`blockStep_length` and `bufStep_length` are offset-independent, so the cost
theorem survives unchanged.

**2. The recursion reflects the shift, and the reflection is not free.**  After
the block step the remaining segment has length `k + n % k` and holds `[A ∣ B]`
with `|A| = k`, `|B| = n % k`; finishing the rotation means sending it to
`[B ∣ A]`, a *left rotation by `k`*.  Equation (1), however, recurses at shift
`n % k`, not `k`.  The two agree because a left rotation by `k` of a segment of
length `k + n % k` is a right rotation by `n % k`, and the block cycle cost is
invariant under that reflection -- which is exactly the step `algCost` builds in
with `min k (n - k)`, and which the paper leaves implicit by stating equation (1)
only for `k ≤ n/2`.

At the level of move sequences that invariance is a theorem, not a definition:
it says the two permutations are realised by programs of equal length.  Closing
equation (1) means proving it.  Note `bcRotate` takes the other route -- it
recurses at the *same* `k` and repairs the orientation with an explicit
`reverse` (its fourth branch), a step with no counterpart in the paper, and
reversals are not free at the move level either.

So the open goal is:

```
theorem bcProg_correct {α} [DecidableEq α] (n k b : ℕ) (h : 2 * k ≤ n) (s : State α) :
    ∀ i < n, (run (bcProg n k b) s).arr i = s.arr ((i + k) % n)
```

with `bcProg` amended per (1), and (2) supplied as a reflection lemma. -/

end BlockCycleRotation
