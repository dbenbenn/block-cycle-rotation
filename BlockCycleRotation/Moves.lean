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
* buffer-respecting -- it names no auxiliary cell numbered `≥ b`
  (`rotProg_usesBuffer`), and
* correct -- running it rotates the array (`rotProg_correct`),

and *that* program has exactly `costB n k b` moves (`rotProg_length`).  The
recursion is then a theorem about a concrete artifact rather than a definition.
`equation_one` states the three together.

In particular the buffered branch needs no axiom.  "A segment of length `k ≤ b`
goes into the buffer at a cost of `k`" is not assumed here: `bufStep` emits `k`
copies in, `n - k` shifts, and `k` copies out, and its cost `n + k` is the
length of that list.

## The reflection

Equation (1) recurses at shift `n % k`, while the geometry after a block step
leaves a segment `[A ∣ B]` with `|A| = k` that must become `[B ∣ A]` -- a left
rotation by `k`, not by `n % k`.  The two agree because §2's method always works
with "the smaller segment", so past the halfway point it works from the other
end.  That is a relabelling of positions, not a reversal of data, and so it is
free: it is the `mirror` branch of `rotProg`, and it is why `algCost` is `cost`
composed with `min k (n - k)`.  It has to be applied *before* the buffer test,
or `rotProg n n b` would cost `2n` rather than `0`.

`bcRotate` takes the other route, recursing at the same `k` and repairing the
orientation with an explicit `reverse`.  That computes the right list, but would
not do here: reversals are not free at the move level.
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

variable {α : Type*}

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

/-! ## Reading the state after a run -/

@[simp] theorem get_arr (s : State α) (i : ℕ) : s.get (.arr i) = s.arr i := rfl
@[simp] theorem get_buf (s : State α) (j : ℕ) : s.get (.buf j) = s.buf j := rfl
@[simp] theorem set_arr_arr (s : State α) (i : ℕ) (v : α) :
    (s.set (.arr i) v).arr = Function.update s.arr i v := rfl
@[simp] theorem set_arr_buf (s : State α) (i : ℕ) (v : α) : (s.set (.arr i) v).buf = s.buf := rfl
@[simp] theorem set_buf_buf (s : State α) (j : ℕ) (v : α) :
    (s.set (.buf j) v).buf = Function.update s.buf j v := rfl
@[simp] theorem set_buf_arr (s : State α) (j : ℕ) (v : α) : (s.set (.buf j) v).arr = s.arr := rfl

/-- A program built by mapping over `List.range` runs one step at a time. -/
theorem run_range_succ (m : ℕ) (f : ℕ → Move) (s : State α) :
    run ((List.range (m + 1)).map f) s = (run ((List.range m).map f) s).step (f m) := by
  rw [List.range_succ, List.map_append, run_append]
  simp [run]

/-! ## The two steps of the algorithm

Each is an explicit list of moves.  Their costs are the lengths of those lists,
not numbers written down by hand. -/

/-- One cycle of the block step, on the positions `i, i+k, …, i+(q-1)k`.

This is the paper's "cyclic permutation of order `q` … using just one additional
cell of memory": save `a i` to the auxiliary cell, shift the `q-1` later entries
of the cycle down one block, and restore the saved entry at the top.  Hence
`q+1` moves. -/
def cycleBody (k i m : ℕ) : Prog :=
  (List.range m).map (fun j => ⟨.arr (i + (j + 1) * k), .arr (i + j * k)⟩)

/-- One cycle: save, shift the cycle down one block, restore. -/
def cycleProg (k q i : ℕ) : Prog :=
  ⟨.arr i, .buf 0⟩ :: (cycleBody k i (q - 1) ++ [⟨.buf 0, .arr (i + (q - 1) * k)⟩])

theorem cycleProg_length {q : ℕ} (k i : ℕ) (hq : 1 ≤ q) :
    moves (cycleProg k q i) = q + 1 := by
  simp only [cycleProg, cycleBody, moves, List.length_cons, List.length_append,
    List.length_map, List.length_range, List.length_nil]
  omega

/-- The block step rotates the first `q = ⌊n/k⌋` blocks of length `k` left by one
block, as `k` independent cycles of order `q`. -/
def blockCycles (n k m : ℕ) : Prog := (List.range m).flatMap (fun i => cycleProg k (n / k) i)

/-- The block step: all `k` cycles. -/
def blockStep (n k : ℕ) : Prog := blockCycles n k k

/-- **The paper's `(q+1)k`.**  §2: the block step "moved `(q-1)k` elements into
their final position using `(q+1)k` moves". -/
theorem blockStep_length {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n) :
    moves (blockStep n k) = (n / k + 1) * k := by
  have hq : 1 ≤ n / k := (Nat.one_le_div_iff hk).2 hkn
  have : ∀ i ∈ List.range k, (cycleProg k (n / k) i).length = n / k + 1 := by
    intro i _
    simpa [moves] using cycleProg_length (q := n / k) k i hq
  simp only [blockStep, blockCycles, moves, List.length_flatMap]
  rw [List.map_congr_left this]
  simp [Nat.mul_comm]

/-- The buffered step, available when the shift fits in the buffer.  Copy the
first `k` entries into the buffer, shift the remaining `n-k` down by `k`, and
write the buffer back at the top. -/
def bufIn (k : ℕ) : Prog := (List.range k).map (fun j => ⟨.arr j, .buf j⟩)

/-- Shift `m` entries down by `k`, lowest first. -/
def shiftDown (k m : ℕ) : Prog := (List.range m).map (fun j => ⟨.arr (j + k), .arr j⟩)

/-- Write `k` buffered entries back, starting at `base`. -/
def writeBack (base k : ℕ) : Prog := (List.range k).map (fun j => ⟨.buf j, .arr (base + j)⟩)

/-- The buffered step. -/
def bufStep (n k : ℕ) : Prog := bufIn k ++ shiftDown k (n - k) ++ writeBack (n - k) k

/-- **The paper's `n+k`, counted rather than assumed.**  `k` copies in, `n-k`
shifts, `k` copies out. -/
theorem bufStep_length {n k : ℕ} (hkn : k ≤ n) : moves (bufStep n k) = n + k := by
  simp only [bufStep, bufIn, shiftDown, writeBack, moves, List.length_append,
    List.length_map, List.length_range]
  omega

/-! ## Correctness of the buffered step

`bufStep` is the base case of the recursion, and the one place a buffer of more
than one cell is used.  It is proved correct here: running it rotates the window
`[0, n)` left by `k`. -/

theorem run_bufIn_succ (m : ℕ) (s : State α) :
    run (bufIn (m + 1)) s = (run (bufIn m) s).step ⟨.arr m, .buf m⟩ := by
  simp only [bufIn]; exact run_range_succ m _ s

theorem run_shiftDown_succ (k m : ℕ) (s : State α) :
    run (shiftDown k (m + 1)) s = (run (shiftDown k m) s).step ⟨.arr (m + k), .arr m⟩ := by
  simp only [shiftDown]; exact run_range_succ m _ s

theorem run_writeBack_succ (base m : ℕ) (s : State α) :
    run (writeBack base (m + 1)) s = (run (writeBack base m) s).step ⟨.buf m, .arr (base + m)⟩ := by
  simp only [writeBack]; exact run_range_succ m _ s

/-- Reading the block into the buffer leaves the array alone. -/
theorem bufIn_arr (k : ℕ) (s : State α) : (run (bufIn k) s).arr = s.arr := by
  induction k with
  | zero => simp [bufIn]
  | succ m ih => rw [run_bufIn_succ]; simpa [State.step] using ih

/-- …and puts `s.arr j` in buffer cell `j`. -/
theorem bufIn_buf {k : ℕ} (s : State α) {j : ℕ} (hj : j < k) :
    (run (bufIn k) s).buf j = s.arr j := by
  induction k with
  | zero => omega
  | succ m ih =>
    rw [run_bufIn_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | rfl
    · simp [State.step, Function.update_of_ne (by omega : j ≠ m), ih h]
    · simp [State.step, bufIn_arr]

/-- The shift writes only below `m`. -/
theorem shiftDown_arr_ge (k : ℕ) : ∀ (m : ℕ) (s : State α) (i : ℕ), m ≤ i →
    (run (shiftDown k m) s).arr i = s.arr i := by
  intro m
  induction m with
  | zero => simp [shiftDown]
  | succ m ih =>
    intro s i hi
    rw [run_shiftDown_succ]
    simp only [State.step, get_arr, set_arr_arr]
    rw [Function.update_of_ne (by omega : i ≠ m)]
    exact ih s i (by omega)

/-- Below `m` it moves each entry down by `k`.  The reads are safe because a
position `j + k` is written only at the later step `j + k`, if at all. -/
theorem shiftDown_arr_lt (k : ℕ) : ∀ (m : ℕ) (s : State α) (i : ℕ), i < m →
    (run (shiftDown k m) s).arr i = s.arr (i + k) := by
  intro m
  induction m with
  | zero => omega
  | succ m ih =>
    intro s i hi
    rw [run_shiftDown_succ]
    simp only [State.step, get_arr, set_arr_arr]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
    · rw [Function.update_of_ne (by omega : i ≠ m)]; exact ih s i h
    · rw [Function.update_self]; exact shiftDown_arr_ge k _ s (i + k) (by omega)

theorem shiftDown_buf (k : ℕ) : ∀ (m : ℕ) (s : State α), (run (shiftDown k m) s).buf = s.buf := by
  intro m
  induction m with
  | zero => simp [shiftDown]
  | succ m ih => intro s; rw [run_shiftDown_succ]; simpa [State.step] using ih s

/-- The write-back touches only `[base, base + k)`. -/
theorem writeBack_arr_lt (base : ℕ) : ∀ (m : ℕ) (s : State α) (i : ℕ), i < base →
    (run (writeBack base m) s).arr i = s.arr i := by
  intro m
  induction m with
  | zero => simp [writeBack]
  | succ m ih =>
    intro s i hi
    rw [run_writeBack_succ]
    simp only [State.step, get_buf, set_arr_arr]
    rw [Function.update_of_ne (by omega : i ≠ base + m)]
    exact ih s i hi

theorem writeBack_buf (base : ℕ) : ∀ (m : ℕ) (s : State α), (run (writeBack base m) s).buf = s.buf := by
  intro m
  induction m with
  | zero => simp [writeBack]
  | succ m ih => intro s; rw [run_writeBack_succ]; simpa [State.step] using ih s

/-- …and puts buffer cell `j` at `base + j`. -/
theorem writeBack_arr_mem (base : ℕ) : ∀ (m : ℕ) (s : State α) (j : ℕ), j < m →
    (run (writeBack base m) s).arr (base + j) = s.buf j := by
  intro m
  induction m with
  | zero => omega
  | succ m ih =>
    intro s j hj
    rw [run_writeBack_succ]
    simp only [State.step, get_buf, set_arr_arr]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | rfl
    · rw [Function.update_of_ne (by omega : base + j ≠ base + m)]; exact ih s j h
    · rw [Function.update_self, writeBack_buf]

/-- **The buffered step rotates.**  Every position of the window ends holding
the entry `k` places to its right, cyclically. -/
theorem bufStep_correct {n k : ℕ} (hkn : k ≤ n) (s : State α) (i : ℕ) (hi : i < n) :
    (run (bufStep n k) s).arr i = s.arr ((i + k) % n) := by
  have hn : 0 < n := by omega
  rw [bufStep, run_append, run_append]
  by_cases h : i < n - k
  · -- the shifted part: position i takes the entry at i + k
    rw [writeBack_arr_lt _ _ _ _ h, shiftDown_arr_lt _ _ _ _ h, bufIn_arr]
    rw [Nat.mod_eq_of_lt (by omega)]
  · -- the buffered block, written back at the top
    push_neg at h
    obtain ⟨j, rfl⟩ : ∃ j, i = n - k + j := ⟨i - (n - k), by omega⟩
    have hj : j < k := by omega
    rw [writeBack_arr_mem _ _ _ _ hj, shiftDown_buf, bufIn_buf _ hj]
    congr 1
    have h1 : n - k + j + k = n + j := by omega
    rw [h1, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega : j < n)]

/-! ## Relabelling

Two ways to move a program to a different part of the array, both of which
preserve its length and its buffer use.  `shift` slides it along; `mirror`
reflects it inside a window.

`mirror` is what lets the method work with the smaller segment.  §2 always
swaps "the smaller segment ... with the adjacent block of the same length", so
when the shift exceeds half the length the method works from the other end.
That is a relabelling of positions, not a reversal of data, so it is free --
which is exactly why `algCost` is `cost` composed with `min k (n - k)`. -/

/-- Relabel the array positions a program touches, leaving buffer cells alone. -/
def Loc.relabel (f : ℕ → ℕ) : Loc → Loc
  | .arr i => .arr (f i)
  | .buf j => .buf j

/-- Relabel every array position in a program. -/
def relabel (f : ℕ → ℕ) (p : Prog) : Prog :=
  p.map (fun m => ⟨m.src.relabel f, m.dst.relabel f⟩)

@[simp] theorem moves_relabel (f : ℕ → ℕ) (p : Prog) : moves (relabel f p) = moves p := by
  simp [relabel, moves]

theorem usesBuffer_relabel {b : ℕ} {p : Prog} (f : ℕ → ℕ) (h : UsesBuffer b p) :
    UsesBuffer b (relabel f p) := by
  intro m hm
  simp only [relabel, List.mem_map] at hm
  obtain ⟨m', hm', rfl⟩ := hm
  obtain ⟨hs, hd⟩ := h m' hm'
  constructor <;> intro j hj <;>
    [ (cases hsrc : m'.src with
       | arr i => simp [Loc.relabel, hsrc] at hj
       | buf i => simp [Loc.relabel, hsrc] at hj; exact hj ▸ hs i hsrc) ;
      (cases hdst : m'.dst with
       | arr i => simp [Loc.relabel, hdst] at hj
       | buf i => simp [Loc.relabel, hdst] at hj; exact hj ▸ hd i hdst) ]

/-- Slide a program along the array by `d`. -/
abbrev shift (d : ℕ) : Prog → Prog := relabel (· + d)

/-- The reflection of `[0, n)`, extended by the identity so that it is an
involution of all of `ℕ` and therefore injective. -/
def refl (n i : ℕ) : ℕ := if i < n then n - 1 - i else i

theorem refl_involutive (n : ℕ) : Function.Involutive (refl n) := by
  intro i
  by_cases h : i < n
  · have : n - 1 - i < n := by omega
    simp only [refl, if_pos h, if_pos this]; omega
  · simp only [refl, if_neg h, if_neg h]

theorem refl_injective (n : ℕ) : Function.Injective (refl n) := (refl_involutive n).injective

/-- Reflect a program inside the window `[0, n)`. -/
abbrev mirror (n : ℕ) : Prog → Prog := relabel (refl n)

/-! ## Correctness of the block step

One cycle at a time.  Within a cycle the reads are safe for the same reason as
in `shiftDown`: position `i + (j+1)k` is written at the later step `j+1`, if at
all.  Distinct cycles touch distinct residues mod `k`, so they do not interfere,
and each leaves the auxiliary cell ready for the next. -/

theorem run_cycleBody_succ (k i m : ℕ) (s : State α) :
    run (cycleBody k i (m + 1)) s
      = (run (cycleBody k i m) s).step ⟨.arr (i + (m + 1) * k), .arr (i + m * k)⟩ := by
  simp only [cycleBody]; exact run_range_succ m _ s

theorem cycleBody_buf (k i : ℕ) : ∀ (m : ℕ) (s : State α),
    (run (cycleBody k i m) s).buf = s.buf := by
  intro m
  induction m with
  | zero => simp [cycleBody]
  | succ m ih => intro s; rw [run_cycleBody_succ]; simpa [State.step] using ih s

theorem cycleBody_arr_ne (k i : ℕ) : ∀ (m : ℕ) (s : State α) (x : ℕ),
    (∀ j < m, x ≠ i + j * k) → (run (cycleBody k i m) s).arr x = s.arr x := by
  intro m
  induction m with
  | zero => simp [cycleBody]
  | succ m ih =>
    intro s x hx
    rw [run_cycleBody_succ]
    simp only [State.step, get_arr, set_arr_arr]
    rw [Function.update_of_ne (hx m (by omega))]
    exact ih s x fun j hj => hx j (by omega)

/-- Distinct multiples of a positive stride give distinct positions. -/
theorem cyc_ne {k : ℕ} (hk : 0 < k) {i j j' : ℕ} (h : j ≠ j') : i + j * k ≠ i + j' * k := by
  intro hc
  exact h (Nat.eq_of_mul_eq_mul_right hk (by omega))

theorem cycleBody_arr_eq {k : ℕ} (hk : 0 < k) (i : ℕ) : ∀ (m : ℕ) (s : State α) (j : ℕ), j < m →
    (run (cycleBody k i m) s).arr (i + j * k) = s.arr (i + (j + 1) * k) := by
  intro m
  induction m with
  | zero => omega
  | succ m ih =>
    intro s j hj
    rw [run_cycleBody_succ]
    simp only [State.step, get_arr, set_arr_arr]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | rfl
    · rw [Function.update_of_ne (cyc_ne hk (by omega))]
      exact ih s j h
    · rw [Function.update_self]
      exact cycleBody_arr_ne k i _ s _ fun j' hj' => cyc_ne hk (by omega)

/-- Everything outside the cycle is untouched. -/
theorem cycleProg_arr_ne {k q i : ℕ} (hq : 1 ≤ q) (s : State α) (x : ℕ)
    (hx : ∀ j < q, x ≠ i + j * k) : (run (cycleProg k q i) s).arr x = s.arr x := by
  simp only [cycleProg, run_cons, run_append, run_cons, run_nil]
  simp only [State.step, get_buf, set_arr_arr]
  rw [Function.update_of_ne (hx (q - 1) (by omega))]
  rw [cycleBody_arr_ne k i _ _ x fun j hj => hx j (by omega)]
  simp [State.step]

/-- Inside the cycle, below the top, each position takes the entry one block up. -/
theorem cycleProg_arr_mid {k q i : ℕ} (hk : 0 < k) (s : State α) {j : ℕ} (hj : j < q - 1) :
    (run (cycleProg k q i) s).arr (i + j * k) = s.arr (i + (j + 1) * k) := by
  simp only [cycleProg, run_cons, run_append, run_cons, run_nil]
  simp only [State.step, get_buf, set_arr_arr]
  rw [Function.update_of_ne (cyc_ne hk (by omega))]
  rw [cycleBody_arr_eq hk i _ _ j hj]
  simp [State.step]

/-- The top of the cycle takes the saved entry. -/
theorem cycleProg_arr_top {k q i : ℕ} (s : State α) :
    (run (cycleProg k q i) s).arr (i + (q - 1) * k) = s.arr i := by
  simp only [cycleProg, run_cons, run_append, run_cons, run_nil]
  simp only [State.step, get_buf, set_arr_arr, Function.update_self]
  rw [cycleBody_buf]
  simp [State.step]

/-- Positions in distinct residue classes mod `k` are distinct. -/
theorem res_ne {k i i' : ℕ} (hi : i < k) (hi' : i' < k) (h : i ≠ i') (j j' : ℕ) :
    i + j * k ≠ i' + j' * k := by
  intro hc
  have h1 : (i + j * k) % k = i := by
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]
  have h2 : (i' + j' * k) % k = i' := by
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi']
  rw [hc, h2] at h1
  exact h h1.symm

theorem run_blockCycles_succ (n k m : ℕ) (s : State α) :
    run (blockCycles n k (m + 1)) s = run (cycleProg k (n / k) m) (run (blockCycles n k m) s) := by
  simp only [blockCycles, List.range_succ, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, run_append]

theorem blockCycles_arr_ne {n k : ℕ} (hq : 1 ≤ n / k) : ∀ (m : ℕ) (s : State α) (x : ℕ),
    (∀ i < m, ∀ j < n / k, x ≠ i + j * k) → (run (blockCycles n k m) s).arr x = s.arr x := by
  intro m
  induction m with
  | zero => simp [blockCycles]
  | succ m ih =>
    intro s x hx
    rw [run_blockCycles_succ, cycleProg_arr_ne hq _ x fun j hj => hx m (by omega) j hj]
    exact ih s x fun i hi j hj => hx i (by omega) j hj

theorem blockCycles_arr_mid {n k : ℕ} (hk : 0 < k) (hq : 1 ≤ n / k) :
    ∀ (m : ℕ), m ≤ k → ∀ (s : State α) (i : ℕ), i < m → ∀ j < n / k - 1,
      (run (blockCycles n k m) s).arr (i + j * k) = s.arr (i + (j + 1) * k) := by
  intro m
  induction m with
  | zero => omega
  | succ m ih =>
    intro hmk s i hi j hj
    rw [run_blockCycles_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
    · rw [cycleProg_arr_ne hq _ _ fun j' _ => res_ne (by omega) (by omega) (by omega) j j']
      exact ih (by omega) s i h j hj
    · rw [cycleProg_arr_mid hk _ hj]
      exact blockCycles_arr_ne hq _ s _ fun i' hi' j' _ =>
        res_ne (by omega) (by omega) (by omega) (j + 1) j'

theorem blockCycles_arr_top {n k : ℕ} (hk : 0 < k) (hq : 1 ≤ n / k) :
    ∀ (m : ℕ), m ≤ k → ∀ (s : State α) (i : ℕ), i < m →
      (run (blockCycles n k m) s).arr (i + (n / k - 1) * k) = s.arr i := by
  intro m
  induction m with
  | zero => omega
  | succ m ih =>
    intro hmk s i hi
    rw [run_blockCycles_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
    · rw [cycleProg_arr_ne hq _ _ fun j' _ =>
        res_ne (by omega) (by omega) (by omega) (n / k - 1) j']
      exact ih (by omega) s i h
    · rw [cycleProg_arr_top]
      exact blockCycles_arr_ne hq _ s i fun i' hi' j' _ => by
        have := res_ne (k := k) (i := i) (i' := i') (by omega) (by omega) (by omega) 0 j'
        simpa using this

/-- **The block step rotates the first `q` blocks left by one block.**  Below
`(q-1)k` each position takes the entry `k` places up; the top block takes the
entry that was saved from position `x - (q-1)k`; the tail is untouched. -/
theorem blockStep_arr_lt {n k : ℕ} (hk : 0 < k) (hq : 1 ≤ n / k) (s : State α) {x : ℕ}
    (hx : x < (n / k - 1) * k) : (run (blockStep n k) s).arr x = s.arr (x + k) := by
  have hmod : x % k < k := Nat.mod_lt _ hk
  have hdvd : x % k + x / k * k = x := Nat.mod_add_div' x k
  have hlt : x / k < n / k - 1 := by
    by_contra hc
    push_neg at hc
    have : (n / k - 1) * k ≤ x / k * k := Nat.mul_le_mul_right _ hc
    omega
  have := blockCycles_arr_mid hk hq k le_rfl s (x % k) hmod (x / k) hlt
  rw [hdvd] at this
  rw [blockStep, this]
  congr 1
  have hexp : (x / k + 1) * k = x / k * k + k := by ring
  rw [hexp, ← Nat.add_assoc, hdvd]

theorem blockStep_arr_top {n k : ℕ} (hk : 0 < k) (hq : 1 ≤ n / k) (s : State α) {x : ℕ}
    (h1 : (n / k - 1) * k ≤ x) (h2 : x < n / k * k) :
    (run (blockStep n k) s).arr x = s.arr (x - (n / k - 1) * k) := by
  have hmod : x % k < k := Nat.mod_lt _ hk
  have hdvd : x % k + x / k * k = x := Nat.mod_add_div' x k
  have hq' : x / k = n / k - 1 := by
    have hu : x / k < n / k := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h2)
    have hl : n / k - 1 ≤ x / k := by
      by_contra hc
      push_neg at hc
      have : x / k * k + k ≤ (n / k - 1) * k := by
        have : x / k + 1 ≤ n / k - 1 := by omega
        calc x / k * k + k = (x / k + 1) * k := by ring
          _ ≤ (n / k - 1) * k := Nat.mul_le_mul_right _ this
      omega
    omega
  have := blockCycles_arr_top hk hq k le_rfl s (x % k) hmod
  rw [← hq', hdvd] at this
  rw [blockStep, this]
  congr 1
  rw [← hq']
  omega

theorem blockStep_arr_ge {n k : ℕ} (hk : 0 < k) (hq : 1 ≤ n / k) (s : State α) {x : ℕ}
    (hx : n / k * k ≤ x) : (run (blockStep n k) s).arr x = s.arr x := by
  refine blockCycles_arr_ne hq k s x fun i hi j hj hc => ?_
  have : i + j * k < n / k * k := by
    have : j + 1 ≤ n / k := by omega
    calc i + j * k < k + j * k := by omega
      _ = (j + 1) * k := by ring
      _ ≤ n / k * k := Nat.mul_le_mul_right _ this
  omega

/-! ## Semantics of relabelling

Running a relabelled program is running the original program on the relabelled
view of the state.  Injectivity is what makes this work, and it is why `mirror`
is defined by an involution of all of `ℕ` rather than a partial reflection. -/

/-- The view of a state through a relabelling of positions. -/
def abst (f : ℕ → ℕ) (s : State α) : State α := ⟨fun j => s.arr (f j), s.buf⟩

theorem abst_step {f : ℕ → ℕ} (hf : Function.Injective f) (s : State α) (m : Move) :
    abst f (s.step ⟨m.src.relabel f, m.dst.relabel f⟩) = (abst f s).step m := by
  have harr : ∀ (d : ℕ) (v : α), abst f (s.set (.arr (f d)) v) = (abst f s).set (.arr d) v := by
    intro d v
    simp only [abst, State.set]
    congr 1
    funext j
    by_cases h : j = d
    · subst h; simp
    · rw [Function.update_of_ne h, Function.update_of_ne (fun hc => h (hf hc))]
  have hbuf : ∀ (d : ℕ) (v : α), abst f (s.set (.buf d) v) = (abst f s).set (.buf d) v := by
    intro d v; simp only [abst, State.set]
  obtain ⟨src, dst⟩ := m
  cases src <;> cases dst <;>
    simp only [State.step, Loc.relabel, State.get] <;>
    first
      | exact harr _ _
      | exact hbuf _ _

theorem abst_run_relabel {f : ℕ → ℕ} (hf : Function.Injective f) :
    ∀ (p : Prog) (s : State α), abst f (run (relabel f p) s) = run p (abst f s) := by
  intro p
  induction p with
  | nil => simp [relabel]
  | cons m p ih =>
    intro s
    simp only [relabel, List.map_cons, run_cons]
    rw [show (List.map (fun m => (⟨m.src.relabel f, m.dst.relabel f⟩ : Move)) p)
          = relabel f p from rfl, ih, abst_step hf]

/-- Positions outside the image of the relabelling are untouched. -/
theorem run_relabel_arr_out {f : ℕ → ℕ} :
    ∀ (p : Prog) (s : State α) (x : ℕ), (∀ i, f i ≠ x) →
      (run (relabel f p) s).arr x = s.arr x := by
  intro p
  induction p with
  | nil => simp [relabel]
  | cons m p ih =>
    intro s x hx
    simp only [relabel, List.map_cons, run_cons]
    rw [show (List.map (fun m => (⟨m.src.relabel f, m.dst.relabel f⟩ : Move)) p)
          = relabel f p from rfl, ih _ x hx]
    cases hd : m.dst with
    | arr d =>
      simp only [State.step, hd, Loc.relabel, State.set, set_arr_arr]
      exact Function.update_of_ne (Ne.symm (hx d)) _ _
    | buf d => simp [State.step, hd, Loc.relabel, State.set]

/-- Reading a mirrored run at `x` is reading the original at `refl n x`. -/
theorem run_mirror_arr (n : ℕ) (p : Prog) (s : State α) (x : ℕ) :
    (run (mirror n p) s).arr x = (run p (abst (refl n) s)).arr (refl n x) := by
  have h := abst_run_relabel (refl_injective n) p s
  have := congrArg (fun t => State.arr t (refl n x)) h
  simpa [abst, refl_involutive n x] using this

/-! ## The algorithm -/

/-- The block cycle method as a program: rotate the window `[0, n)` left by `k`.

Nothing to do when the shift is zero; one buffered step when the shift fits in
the buffer; otherwise the block step, followed by the same method on the segment
it leaves behind -- which starts at offset `(q-1)k`, hence the `shift`.  When the
shift exceeds half the length the method works from the other end, which is the
`mirror` branch and costs nothing. -/
def rotProg (n k b : ℕ) : Prog :=
  if hk : k = 0 then []
  else if h2 : 2 * k ≤ n then
    (if k ≤ b then bufStep n k
      else blockStep n k ++ shift ((n / k - 1) * k) (rotProg (k + n % k) k b))
  else
    mirror n (rotProg n (n - k) b)
termination_by n + k
decreasing_by
  · have := Nat.mod_lt n (Nat.pos_of_ne_zero hk); omega
  · omega

@[simp] theorem rotProg_zero (n b : ℕ) : rotProg n 0 b = [] := by rw [rotProg]; simp

theorem rotProg_of_le {n k b : ℕ} (hk : k ≠ 0) (h2 : 2 * k ≤ n) (h : k ≤ b) :
    rotProg n k b = bufStep n k := by
  rw [rotProg]; simp [hk, h, h2]

theorem rotProg_block {n k b : ℕ} (hk : k ≠ 0) (hb : b < k) (h2 : 2 * k ≤ n) :
    rotProg n k b = blockStep n k ++ shift ((n / k - 1) * k) (rotProg (k + n % k) k b) := by
  rw [rotProg]; simp [hk, Nat.not_le.2 hb, h2]

theorem rotProg_mirror {n k b : ℕ} (hk : k ≠ 0) (h2 : ¬ 2 * k ≤ n) :
    rotProg n k b = mirror n (rotProg n (n - k) b) := by
  rw [rotProg]; simp [hk, h2]

/-! ## Equation (1), counted

The length of the emitted program -- an operational quantity -- satisfies the
paper's recursion. -/

/-- **Equation (1).**  On the paper's range `2k ≤ n`, the block cycle method
makes exactly `costB n k b` moves. -/
theorem rotProg_length : ∀ N n k b : ℕ, n + k ≤ N → 2 * k ≤ n →
    moves (rotProg n k b) = costB n k b := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro n k b hN h2
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · by_cases hb : k ≤ b
      · rw [rotProg_of_le hk.ne' h2 hb, costB_of_le hk.ne' hb, bufStep_length (by omega)]
      · push_neg at hb
        have hmod : n % k < k := Nat.mod_lt _ hk
        have hinner : ¬ 2 * k ≤ k + n % k := by omega
        rw [rotProg_block hk.ne' hb h2, moves_append, blockStep_length hk (by omega),
          rotProg_mirror hk.ne' hinner, moves_relabel, moves_relabel,
          show k + n % k - k = n % k by omega,
          ih (k + n % k + n % k) (by omega) (k + n % k) (n % k) b le_rfl (by omega),
          costB_of_gt hk.ne' hb]

/-- **Equation (1), stated without the range hypothesis.**  Off the paper's
range the method works from the other end, so the count is `costB` at the
reflected shift -- which is exactly how `algCost` packages it. -/
theorem rotProg_length_min {n k b : ℕ} (hkn : k ≤ n) :
    moves (rotProg n k b) = costB n (min k (n - k)) b := by
  by_cases h2 : 2 * k ≤ n
  · rw [min_eq_left (by omega), rotProg_length (n + k) n k b le_rfl h2]
  · push_neg at h2
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · rw [rotProg_mirror hk.ne' (by omega), moves_relabel, min_eq_right (by omega),
        rotProg_length (n + (n - k)) n (n - k) b le_rfl (by omega)]

/-! ## The buffer discipline

Without a bound on which auxiliary cells the program may touch, "with a buffer
of `b` cells" would carry no content: unbounded scratch space makes any rotation
cheap.  The block step needs the paper's one additional cell. -/

theorem cycleProg_usesBuffer {b : ℕ} (hb : 1 ≤ b) (k q i : ℕ) :
    UsesBuffer b (cycleProg k q i) := by
  intro m hm
  simp only [cycleProg, cycleBody, List.mem_cons, List.mem_append, List.mem_map,
    List.mem_range, List.not_mem_nil, or_false] at hm
  refine ⟨?_, ?_⟩ <;> intro j hj <;>
    rcases hm with h | ⟨t, _, h⟩ | h <;> subst h <;> (cases hj <;> omega)

theorem blockStep_usesBuffer {b : ℕ} (hb : 1 ≤ b) (n k : ℕ) :
    UsesBuffer b (blockStep n k) := by
  intro m hm
  simp only [blockStep, blockCycles, List.mem_flatMap, List.mem_range] at hm
  obtain ⟨i, _, hi⟩ := hm
  exact cycleProg_usesBuffer hb k (n / k) i m hi

theorem bufStep_usesBuffer {n k b : ℕ} (h : k ≤ b) : UsesBuffer b (bufStep n k) := by
  intro m hm
  simp only [bufStep, bufIn, shiftDown, writeBack, List.mem_append, List.mem_map,
    List.mem_range] at hm
  refine ⟨?_, ?_⟩ <;> intro i hi <;>
    rcases hm with (⟨j, hj, h⟩ | ⟨j, hj, h⟩) | ⟨j, hj, h⟩ <;> subst h <;> (cases hi <;> omega)

/-- **The program respects its buffer.**  One auxiliary cell is required -- the
paper's own hypothesis for the unbuffered scheme -- and no cell numbered `b` or
higher is ever named. -/
theorem rotProg_usesBuffer : ∀ N n k b : ℕ, n + k ≤ N → 1 ≤ b →
    UsesBuffer b (rotProg n k b) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro n k b hN hb
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simpa using usesBuffer_nil b
    · have hmod : n % k < k := Nat.mod_lt _ hk
      by_cases h2 : 2 * k ≤ n
      · by_cases hle : k ≤ b
        · rw [rotProg_of_le hk.ne' h2 hle]; exact bufStep_usesBuffer hle
        · push_neg at hle
          rw [rotProg_block hk.ne' hle h2]
          exact usesBuffer_append (blockStep_usesBuffer hb n k)
            (usesBuffer_relabel _ (ih (k + n % k + k) (by omega) (k + n % k) k b le_rfl hb))
      · rw [rotProg_mirror hk.ne' h2]
        exact usesBuffer_relabel _ (ih (n + (n - k)) (by omega) n (n - k) b le_rfl hb)

end BlockCycleRotation

namespace BlockCycleRotation

/-! ## Sanity checks

Executable checks on the model, run at compile time.  Redundant now that
`rotProg_correct` is proved, but they were what located the two bugs in the
first version, so they stay. -/

private def toArr (l : List ℕ) : ℕ → ℕ := fun i => l.getD i 0
private def readBack (n : ℕ) (s : State ℕ) : List ℕ := (List.range n).map s.arr
private def sim (l : List ℕ) (k b : ℕ) : List ℕ :=
  readBack l.length (run (rotProg l.length k b) ⟨toArr l, fun _ => 0⟩)
private def rotOk (n k b : ℕ) : Bool :=
  sim (List.range n) k b == (List.range n).rotate k

-- the program rotates, for every shift of every length up to 11, with and
-- without a buffer
#guard (List.range 12).all fun n => (List.range (n + 1)).all fun k => rotOk n k 0
#guard (List.range 12).all fun n => (List.range (n + 1)).all fun k => rotOk n k 3

-- and the counted cost agrees with the recursion and with `algCost`
#guard (rotProg 21 8 0).length = costB 21 8 0
#guard (rotProg 21 8 0).length = algCost 21 8
#guard (rotProg 100 37 0).length = algCost 100 37
#guard (rotProg 100 37 5).length = costB 100 37 5
#guard (rotProg 12 8 0).length = algCost 12 8

end BlockCycleRotation

namespace BlockCycleRotation

variable {α : Type*}

/-- Reflecting, rotating by `n - k`, and reflecting back is rotating by `k`.
This is the arithmetic behind the `mirror` branch. -/
theorem refl_rot {n k x : ℕ} (hk : 0 < k) (hkn : k ≤ n) (hx : x < n) :
    refl n ((refl n x + (n - k)) % n) = (x + k) % n := by
  have hrx : refl n x = n - 1 - x := by simp [refl, hx]
  by_cases h : n - 1 - x < k
  · have h1 : (n - 1 - x + (n - k)) % n = n - 1 - x + (n - k) :=
      Nat.mod_eq_of_lt (by omega)
    have h2 : (x + k) % n = x + k - n := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hrx, h1, h2]
    simp only [refl, if_pos (show n - 1 - x + (n - k) < n by omega)]
    omega
  · push_neg at h
    have h1 : (n - 1 - x + (n - k)) % n = n - 1 - x + (n - k) - n := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    have h2 : (x + k) % n = x + k := Nat.mod_eq_of_lt (by omega)
    rw [hrx, h1, h2]
    simp only [refl, if_pos (show n - 1 - x + (n - k) - n < n by omega)]
    omega

end BlockCycleRotation

namespace BlockCycleRotation

variable {α : Type*}

/-! The block step's effect, restated with the offset `d = (q-1)k` as an opaque
constant so that the surrounding arithmetic stays linear. -/

theorem blockStep_lt' {n k d : ℕ} (hk : 0 < k) (hq : 1 ≤ n / k) (hd : (n / k - 1) * k = d)
    (s : State α) {x : ℕ} (hx : x < d) : (run (blockStep n k) s).arr x = s.arr (x + k) :=
  blockStep_arr_lt hk hq s (by rw [hd]; exact hx)

theorem blockStep_top' {n k d : ℕ} (hk : 0 < k) (hq : 1 ≤ n / k) (hd : (n / k - 1) * k = d)
    (hdk : d + k = n / k * k) (s : State α) {x : ℕ} (h1 : d ≤ x) (h2 : x < d + k) :
    (run (blockStep n k) s).arr x = s.arr (x - d) := by
  rw [blockStep_arr_top hk hq s (by rw [hd]; exact h1) (by rw [← hdk]; exact h2), hd]

theorem blockStep_ge' {n k d : ℕ} (hk : 0 < k) (hq : 1 ≤ n / k) (hdk : d + k = n / k * k)
    (s : State α) {x : ℕ} (hx : d + k ≤ x) : (run (blockStep n k) s).arr x = s.arr x :=
  blockStep_arr_ge hk hq s (by rw [← hdk]; exact hx)

/-- **The block cycle method computes the rotation.**  Running the program on
any state leaves each position of the window `[0, n)` holding the entry `k`
places to its right, cyclically.

With `rotProg_length` this is equation (1): the move count of a program that
provably rotates, and provably respects its buffer, satisfies the paper's
recursion. -/
theorem rotProg_correct : ∀ (N n k b : ℕ), n + k ≤ N → k ≤ n → ∀ (s : State α) (x : ℕ), x < n →
    (run (rotProg n k b) s).arr x = s.arr ((x + k) % n) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro n k b hN hkn s x hx
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [Nat.mod_eq_of_lt hx]
    by_cases h2 : 2 * k ≤ n
    · by_cases hb : k ≤ b
      · rw [rotProg_of_le hk.ne' h2 hb]; exact bufStep_correct hkn s x hx
      · push_neg at hb
        have hmod : n % k < k := Nat.mod_lt _ hk
        have hq : 1 ≤ n / k := (Nat.le_div_iff_mul_le hk).2 (by omega)
        rw [rotProg_block hk.ne' hb h2, run_append]
        set d := (n / k - 1) * k with hd
        set L := k + n % k with hLdef
        have hdk : d + k = n / k * k := by rw [hd, ← Nat.succ_mul]; congr 1; omega
        have hDn : d + L = n := by rw [hLdef, ← Nat.add_assoc, hdk]; exact Nat.div_add_mod' n k
        have hkL : k ≤ L := by rw [hLdef]; omega
        -- package the block step's effect, then discard every nonlinear fact, so
        -- that what remains is linear in `d`, `L`, `k`, `n` and `y`
        have Elt : ∀ z, z < d → (run (blockStep n k) s).arr z = s.arr (z + k) :=
          fun z hz => blockStep_lt' hk hq hd.symm s hz
        have Etop : ∀ z, d ≤ z → z < d + k → (run (blockStep n k) s).arr z = s.arr (z - d) :=
          fun z h1 h3 => blockStep_top' hk hq hd.symm hdk s h1 h3
        have Ege : ∀ z, d + k ≤ z → (run (blockStep n k) s).arr z = s.arr z :=
          fun z hz => blockStep_ge' hk hq hdk s hz
        clear_value d L
        clear hd hdk
        by_cases hxd : x < d
        · rw [show (shift d (rotProg L k b)) = relabel (· + d) _ from rfl,
            run_relabel_arr_out _ _ x (by intro i hc; omega), Elt x hxd,
            Nat.mod_eq_of_lt (by omega)]
        · push_neg at hxd
          obtain ⟨y, rfl⟩ : ∃ y, x = d + y := ⟨x - d, by omega⟩
          have hy : y < L := by omega
          have key := abst_run_relabel (α := α) (f := (· + d)) (add_left_injective d)
            (rotProg L k b) (run (blockStep n k) s)
          have hpt := congrArg (fun t => State.arr t y) key
          simp only [abst] at hpt
          rw [show (shift d (rotProg L k b)) = relabel (· + d) _ from rfl,
            show d + y = y + d from Nat.add_comm d y, hpt,
            ih (L + k) (by omega) L k b le_rfl hkL _ y hy]
          simp only [abst]
          set z := (y + k) % L with hzdef
          have hzL : z < L := by rw [hzdef]; exact Nat.mod_lt _ (by omega)
          by_cases hzk : z < k
          · -- the recursion wrapped around: this position takes a saved entry
            have hyk : L ≤ y + k := by
              by_contra hc
              push_neg at hc
              rw [hzdef, Nat.mod_eq_of_lt hc] at hzk
              omega
            have hzy : z = y + k - L := by
              rw [hzdef, Nat.mod_eq_sub_mod hyk, Nat.mod_eq_of_lt (by omega)]
            clear_value z
            clear hzdef
            rw [Etop _ (by omega) (by omega), show z + d - d = z from by omega,
              show (y + d + k) % n = z from by
                rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega]
          · -- no wraparound: this position takes an entry of the untouched tail
            push_neg at hzk
            have hyk : y + k < L := by
              by_contra hc
              push_neg at hc
              rw [hzdef, Nat.mod_eq_sub_mod hc, Nat.mod_eq_of_lt (by omega)] at hzk
              omega
            have hzy : z = y + k := by rw [hzdef, Nat.mod_eq_of_lt hyk]
            clear_value z
            clear hzdef
            rw [Ege _ (by omega), show (y + d + k) % n = z + d from by
              rw [Nat.mod_eq_of_lt (by omega)]; omega]
    · push_neg at h2
      rw [rotProg_mirror hk.ne' (by omega), run_mirror_arr]
      have hrx : refl n x < n := by simp only [refl, if_pos hx]; omega
      rw [ih (n + (n - k)) (by omega) n (n - k) b le_rfl (by omega) _ _ hrx]
      simp only [abst]
      rw [refl_rot hk hkn hx]

end BlockCycleRotation

namespace BlockCycleRotation

variable {α : Type*}

/-- **Equation (1).**  On the paper's range `2k ≤ n`, with at least the one
auxiliary cell §2 assumes, the block cycle method

* rotates the window `[0, n)` left by `k`,
* names no auxiliary cell numbered `b` or higher, and
* makes exactly `costB n k b` moves.

The third clause is the paper's recursion.  It is a theorem about a program the
first two clauses pin down, rather than the definition of the move count, which
is what closes the gap this file was written for. -/
theorem equation_one {n k b : ℕ} (h2 : 2 * k ≤ n) (hb : 1 ≤ b) :
    (∀ (s : State α) (x : ℕ), x < n →
        (run (rotProg n k b) s).arr x = s.arr ((x + k) % n))
      ∧ UsesBuffer b (rotProg n k b)
      ∧ moves (rotProg n k b) = costB n k b :=
  ⟨fun s x hx => rotProg_correct (n + k) n k b le_rfl (by omega) s x hx,
   rotProg_usesBuffer (n + k) n k b le_rfl hb,
   rotProg_length (n + k) n k b le_rfl h2⟩

end BlockCycleRotation
