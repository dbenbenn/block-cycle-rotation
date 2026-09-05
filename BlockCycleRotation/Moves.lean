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

/-- Reflect a program inside the window `[0, n)`. -/
abbrev mirror (n : ℕ) : Prog → Prog := relabel (fun i => n - 1 - i)

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

Executable checks on the model, run at compile time.  These are evidence, not
proof: `rotProg_correct` below is what remains. -/

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
