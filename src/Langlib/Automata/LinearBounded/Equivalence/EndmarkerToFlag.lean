module

public import Langlib.Automata.LinearBounded.Endmarker
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.Option
import Mathlib.Tactic
@[expose]
public section

/-!
# The endmarker LBA class is contained in the marker-free flag LBA class (`LBA_end ⊆ LBA`)

This is the converse simulation to `Equivalence/EndmarkerTape.lean`: an endmarker LBA `M'` on the
`|w|+2`-cell bracketed tape `⊢ w ⊣` is simulated by a marker-free flag LBA `M` on the `|w|` input
cells. Combined with `LBA ⊆ LBA_end` it gives `LBA_end = LBA`, and with `CS = LBA` it gives
`CS = LBA_end`, making the endmarker model the canonical automaton model for the
context-sensitive languages.

## Construction (the "fold")

`M'` uses `|w|+2` cells; `M` has only `|w|`. We keep `M'`'s **interior** cells `1 … |w|` on `M`'s
cells `0 … |w|-1` (cell `i` ↔ interior cell `i+1`), and **fold** the two read-only-position marker
cells into the boundary cells: cell `0` additionally stores `M'`-cell `0`'s content (the `⊢` cell)
and the last cell additionally stores `M'`-cell `|w|+1`'s content (the `⊣` cell). A work cell is
therefore a `FoldCell = (cur, leftEnd?, rightEnd?)`: the interior content `cur`, plus an optional
`⊢`-cell content (present only at cell `0`) and optional `⊣`-cell content (present only at the last
cell).

`M`'s head is always on the cell holding the content `M'` reads; a finite `FMode` records whether
`M'`'s head is on the folded `⊢` (`onLeft`), the interior (`mid`), or the folded `⊣` (`onRight`).
Because the markers are folded into the *same* boundary cell as the adjacent interior cell, mode
switches at the boundary keep `M`'s head **stationary** — so one `M'`-step is exactly one `M`-step
(no bounce). Boundary clamping of `M'` is reproduced by the `onLeft`/`onRight` transitions staying
put.

## Init phase (`setup`/`scan`/`verify`/`rewind`)

`M` starts at cell `0`, which it knows is the left end, and marks it (`leftEnd := some ⊢`). It then
scans right and **nondeterministically guesses** the last cell, marking it (`rightEnd := some ⊣`);
moving right off that cell *clamps* iff the guess was correct, so re-reading a `rightEnd`-marked
cell **verifies** the guess (a wrong guess reads an unmarked cell and dies). It then rewinds left to
the `leftEnd`-marked cell `0` and enters the simulation at `M'.initial` with the head on `⊢`
(`onLeft`).

The bisimulation (init reaches the encoded `M'` start config; simulation mirrors `M'` steps; a
backward invariant rules out wrong-guess branches reaching acceptance) is the remaining work.
-/

namespace LBA

open DLBA

variable {T Γ : Type*} {Λ : Type*}

/-- A folded work cell of the simulating flag machine: the interior content `cur` of the
corresponding `M'`-interior cell, plus the `⊢`-cell content (`Some` only at cell `0`) and the
`⊣`-cell content (`Some` only at the last cell). -/
abbrev FoldCell (T Γ : Type*) : Type _ :=
  EndAlpha T Γ × Option (EndAlpha T Γ) × Option (EndAlpha T Γ)

/-- Tape alphabet of the simulating flag machine: canonical marker-free alphabet with work
alphabet `FoldCell T Γ`. -/
abbrev FAlpha (T Γ : Type*) : Type _ := Option (T ⊕ FoldCell T Γ)

/-- Where `M'`'s head sits relative to the cell `M` is currently on: on the folded left marker
`⊢`, in the interior, or on the folded right marker `⊣`. -/
inductive FMode | onLeft | mid | onRight
  deriving DecidableEq

instance : Fintype FMode :=
  ⟨{FMode.onLeft, FMode.mid, FMode.onRight}, fun x => by cases x <;> simp⟩

/-- States of the simulating flag machine: the four init-phase states and the simulation states
`sim q mode` carrying the simulated `M'`-state `q` and the head mode. -/
inductive FState (Λ : Type*)
  | setup
  | scan
  | verify
  | rewind
  | sim (q : Λ) (mode : FMode)
  deriving DecidableEq

noncomputable instance [Fintype Λ] : Fintype (FState Λ) := by
  classical
  exact Fintype.ofInjective
    (fun s => match s with
      | FState.setup => Sum.inr (0 : Fin 4)
      | FState.scan => Sum.inr 1
      | FState.verify => Sum.inr 2
      | FState.rewind => Sum.inr 3
      | FState.sim q m => Sum.inl (q, m))
    (by intro a b h; cases a <;> cases b <;> simp_all)

/-- The interior content `M'` would see at this cell: an input cell reads as interior input, a work
cell reads its stored `cur`, a blank reads as interior blank. -/
def cellCur : FAlpha T Γ → EndAlpha T Γ
  | some (Sum.inl t) => Sum.inl (some (Sum.inl t))
  | some (Sum.inr fc) => fc.1
  | none => Sum.inl none

/-- The folded `⊢`-cell content, present only at cell `0`. -/
def cellLeft : FAlpha T Γ → Option (EndAlpha T Γ)
  | some (Sum.inr fc) => fc.2.1
  | _ => none

/-- The folded `⊣`-cell content, present only at the last cell. -/
def cellRight : FAlpha T Γ → Option (EndAlpha T Γ)
  | some (Sum.inr fc) => fc.2.2
  | _ => none

/-- Transition of the simulating flag machine. Init phase: `setup` marks cell `0` (and may mark it
as the last cell too, for `|w|=1`); `scan` moves right, nondeterministically marking the guessed
last cell; `verify` accepts the guess iff the right move clamped back onto the marked cell;
`rewind` returns left to cell `0`. Simulation phase: replay `M'` on the folded tape, switching
`FMode` at the boundaries with the head stationary. -/
def flagTransition (M' : Machine (EndAlpha T Γ) Λ) :
    FState Λ → FAlpha T Γ → Set (FState Λ × FAlpha T Γ × DLBA.Dir) :=
  fun s r => match s with
  | .setup =>
      { (FState.scan, some (Sum.inr (cellCur r, some leftMark, none)), DLBA.Dir.right),
        (FState.verify, some (Sum.inr (cellCur r, some leftMark, some rightMark)), DLBA.Dir.right) }
  | .scan =>
      { (FState.scan, r, DLBA.Dir.right),
        (FState.verify, some (Sum.inr (cellCur r, none, some rightMark)), DLBA.Dir.right) }
  | .verify =>
      if (cellRight r).isSome then {(FState.rewind, r, DLBA.Dir.left)} else ∅
  | .rewind =>
      if (cellLeft r).isSome then {(FState.sim M'.initial FMode.onLeft, r, DLBA.Dir.stay)}
      else {(FState.rewind, r, DLBA.Dir.left)}
  | .sim q FMode.onLeft =>
      { x | ∃ p ∈ M'.transition q ((cellLeft r).getD leftMark),
            x = (FState.sim p.1 (match p.2.2 with | DLBA.Dir.right => FMode.mid | _ => FMode.onLeft),
                 some (Sum.inr (cellCur r, some p.2.1, cellRight r)), DLBA.Dir.stay) }
  | .sim q FMode.mid =>
      { x | ∃ p ∈ M'.transition q (cellCur r),
            x = (FState.sim p.1
                   (match p.2.2 with
                    | DLBA.Dir.stay => FMode.mid
                    | DLBA.Dir.left => if (cellLeft r).isSome then FMode.onLeft else FMode.mid
                    | DLBA.Dir.right => if (cellRight r).isSome then FMode.onRight else FMode.mid),
                 some (Sum.inr (p.2.1, cellLeft r, cellRight r)),
                 match p.2.2 with
                 | DLBA.Dir.stay => DLBA.Dir.stay
                 | DLBA.Dir.left => if (cellLeft r).isSome then DLBA.Dir.stay else DLBA.Dir.left
                 | DLBA.Dir.right => if (cellRight r).isSome then DLBA.Dir.stay else DLBA.Dir.right) }
  | .sim q FMode.onRight =>
      { x | ∃ p ∈ M'.transition q ((cellRight r).getD rightMark),
            x = (FState.sim p.1 (match p.2.2 with | DLBA.Dir.left => FMode.mid | _ => FMode.onRight),
                 some (Sum.inr (cellCur r, cellLeft r, some p.2.1)), DLBA.Dir.stay) }

/-- The marker-free flag machine simulating the endmarker machine `M'` (work alphabet
`FoldCell T Γ`). It accepts exactly when the simulated `M'`-state is accepting. -/
def flagMachine (M' : Machine (EndAlpha T Γ) Λ) : Machine (FAlpha T Γ) (FState Λ) where
  transition := flagTransition M'
  accept := fun s => match s with | .sim q _ => M'.accept q | _ => false
  initial := .setup

end LBA
