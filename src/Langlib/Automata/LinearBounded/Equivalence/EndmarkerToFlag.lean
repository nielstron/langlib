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
      { (FState.scan, some (Sum.inr (cellCur r, none, none)), DLBA.Dir.right),
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

@[simp] theorem flagMachine_accept_sim (M' : Machine (EndAlpha T Γ) Λ) (q : Λ) (mode : FMode) :
    (flagMachine M').accept (.sim q mode) = M'.accept q := rfl

/-! ### The fold encoding of an `M'`-configuration. -/

/-- The folded contents: cell `i` holds the interior cell `i+1`, with the `⊢`/`⊣` cells folded
into cells `0`/`m`. -/
def foldContents {m : ℕ} (c : Fin (m + 3) → EndAlpha T Γ) : Fin (m + 1) → FAlpha T Γ :=
  fun i => some (Sum.inr
    (c ⟨i.val + 1, by have := i.isLt; omega⟩,
     if i.val = 0 then some (c ⟨0, by omega⟩) else none,
     if i.val = m then some (c ⟨m + 2, by omega⟩) else none))

/-- The folded head position: `⊢`→cell `0`, interior cell `p`→cell `p-1`, `⊣`→cell `m`. -/
def foldHead {m : ℕ} (p : Fin (m + 3)) : Fin (m + 1) :=
  if h0 : p.val = 0 then ⟨0, by omega⟩
  else if h2 : p.val = m + 2 then ⟨m, by omega⟩
  else ⟨p.val - 1, by have := p.isLt; omega⟩

/-- The head mode determined by where `M'`'s head sits. -/
def foldMode {m : ℕ} (p : Fin (m + 3)) : FMode :=
  if p.val = 0 then FMode.onLeft else if p.val = m + 2 then FMode.onRight else FMode.mid

/-- Encode an `M'`-configuration (on `m+2` dim, `m+3` cells) as the corresponding `flagMachine`
configuration (on `m` dim, `m+1` cells) in the simulation phase. -/
def fold {m : ℕ} (cfg : DLBA.Cfg (EndAlpha T Γ) Λ (m + 2)) :
    DLBA.Cfg (FAlpha T Γ) (FState Λ) m :=
  ⟨FState.sim cfg.state (foldMode cfg.tape.head),
   ⟨foldContents cfg.tape.contents, foldHead cfg.tape.head⟩⟩

@[simp] theorem cellCur_foldContents {m : ℕ} (c : Fin (m + 3) → EndAlpha T Γ) (i : Fin (m + 1)) :
    cellCur (foldContents c i) = c ⟨i.val + 1, by have := i.isLt; omega⟩ := rfl

@[simp] theorem cellLeft_foldContents {m : ℕ} (c : Fin (m + 3) → EndAlpha T Γ) (i : Fin (m + 1)) :
    cellLeft (foldContents c i) = if i.val = 0 then some (c ⟨0, by omega⟩) else none := rfl

@[simp] theorem cellRight_foldContents {m : ℕ} (c : Fin (m + 3) → EndAlpha T Γ) (i : Fin (m + 1)) :
    cellRight (foldContents c i) = if i.val = m then some (c ⟨m + 2, by omega⟩) else none := rfl

theorem cfg_ext' {Γ' Λ' : Type*} {N : ℕ} {X Y : DLBA.Cfg Γ' Λ' N}
    (hs : X.state = Y.state) (hc : X.tape.contents = Y.tape.contents)
    (hh : X.tape.head = Y.tape.head) : X = Y := by
  obtain ⟨xs, xc, xh⟩ := X; obtain ⟨ys, yc, yh⟩ := Y; simp_all

/-- Writing `M'`'s symbol at its head cell `p` only changes the folded cell at `foldHead p`; every
other folded cell is unaffected (its `cur`/`leftEnd`/`rightEnd` all read `c` away from `p`). -/
theorem foldHead_val {m : ℕ} (p : Fin (m + 3)) :
    (foldHead p).val = (if p.val = 0 then 0 else if p.val = m + 2 then m else p.val - 1) := by
  simp only [foldHead]; split_ifs <;> rfl

theorem foldContents_off {m : ℕ} (c : Fin (m + 3) → EndAlpha T Γ) (p : Fin (m + 3))
    (a' : EndAlpha T Γ) (j : Fin (m + 1)) (hj : j ≠ foldHead p) :
    foldContents (Function.update c p a') j = foldContents c j := by
  have hjlt := j.isLt
  have hplt := p.isLt
  have hjv : j.val ≠ (if p.val = 0 then 0 else if p.val = m + 2 then m else p.val - 1) := by
    rw [← foldHead_val]; exact fun h => hj (Fin.ext h)
  have c1 : ¬ (j.val + 1 = p.val) := by split_ifs at hjv <;> omega
  have c2 : j.val = 0 → ¬ (0 = p.val) := by intro h; split_ifs at hjv <;> omega
  have c3 : j.val = m → ¬ (m + 2 = p.val) := by intro h; split_ifs at hjv <;> omega
  simp only [foldContents, Function.update_apply, Fin.ext_iff]
  by_cases h0 : j.val = 0 <;> by_cases hm : j.val = m <;> simp_all

/-- Writing at the head cell only affects the folded cell at `foldHead p`. -/
theorem foldContents_update {m : ℕ} (c : Fin (m + 3) → EndAlpha T Γ) (p : Fin (m + 3))
    (a' : EndAlpha T Γ) :
    Function.update (foldContents c) (foldHead p) (foldContents (Function.update c p a') (foldHead p))
      = foldContents (Function.update c p a') := by
  funext j
  by_cases hj : j = foldHead p
  · subst hj; rw [Function.update_self]
  · rw [Function.update_of_ne hj]; exact (foldContents_off c p a' j hj).symm

@[simp] theorem foldMode_zero {m : ℕ} {p : Fin (m + 3)} (h : p.val = 0) :
    foldMode p = FMode.onLeft := by simp [foldMode, h]
@[simp] theorem foldMode_last {m : ℕ} {p : Fin (m + 3)} (h : p.val = m + 2) :
    foldMode p = FMode.onRight := by simp [foldMode, h]
theorem foldMode_mid {m : ℕ} {p : Fin (m + 3)} (h0 : p.val ≠ 0) (h2 : p.val ≠ m + 2) :
    foldMode p = FMode.mid := by simp [foldMode, h0, h2]

/-! ### Head-projection lemmas (definitional). -/

@[simp] theorem write_head {Γ' : Type*} {N : ℕ} (t : DLBA.BoundedTape Γ' N) (a : Γ') :
    (t.write a).head = t.head := rfl
@[simp] theorem moveHead_stay_head {Γ' : Type*} {N : ℕ} (t : DLBA.BoundedTape Γ' N) :
    (t.moveHead DLBA.Dir.stay).head = t.head := rfl
theorem moveHead_left_head {Γ' : Type*} {N : ℕ} (t : DLBA.BoundedTape Γ' N) :
    (t.moveHead DLBA.Dir.left).head
      = if h : 0 < t.head.val then ⟨t.head.val - 1, by omega⟩ else t.head := rfl
theorem moveHead_right_head {Γ' : Type*} {N : ℕ} (t : DLBA.BoundedTape Γ' N) :
    (t.moveHead DLBA.Dir.right).head
      = if h : t.head.val < N then ⟨t.head.val + 1, by omega⟩ else t.head := rfl
theorem moveHead_left_head_val {Γ' : Type*} {N : ℕ} (t : DLBA.BoundedTape Γ' N) :
    (t.moveHead DLBA.Dir.left).head.val = if 0 < t.head.val then t.head.val - 1 else t.head.val := by
  rw [moveHead_left_head]; split_ifs <;> rfl
theorem moveHead_right_head_val {Γ' : Type*} {N : ℕ} (t : DLBA.BoundedTape Γ' N) :
    (t.moveHead DLBA.Dir.right).head.val = if t.head.val < N then t.head.val + 1 else t.head.val := by
  rw [moveHead_right_head]; split_ifs <;> rfl

/-! ### Simulation-phase single-step correctness (one `M'`-step = one `flagMachine`-step). -/

/-- One `M'`-step is matched by exactly one `flagMachine`-step on the folded configuration. -/
theorem fold_step (M' : Machine (EndAlpha T Γ) Λ) {m : ℕ}
    {cfg cfg' : DLBA.Cfg (EndAlpha T Γ) Λ (m + 2)} (h : Step M' cfg cfg') :
    Step (flagMachine M') (fold cfg) (fold cfg') := by
  obtain ⟨q', a', d', hmem, rfl⟩ := h
  set cfg' : DLBA.Cfg (EndAlpha T Γ) Λ (m + 2) := ⟨q', (cfg.tape.write a').moveHead d'⟩ with hcfg'
  rw [show cfg.tape.read = cfg.tape.contents cfg.tape.head from rfl] at hmem
  by_cases hp0 : cfg.tape.head.val = 0
  · -- `M'` head on `⊢`: mode `onLeft`, flag head stays at cell 0.
    have hmode : foldMode cfg.tape.head = FMode.onLeft := foldMode_zero hp0
    have hhd : foldHead cfg.tape.head = (⟨0, by omega⟩ : Fin (m + 1)) := by
      apply Fin.ext; rw [foldHead_val]; simp [hp0]
    set wcell : FAlpha T Γ :=
      some (Sum.inr (cellCur (foldContents cfg.tape.contents (foldHead cfg.tape.head)), some a',
        cellRight (foldContents cfg.tape.contents (foldHead cfg.tape.head)))) with hwcell
    have hrd : (cellLeft (foldContents cfg.tape.contents (foldHead cfg.tape.head))).getD leftMark
        = cfg.tape.contents cfg.tape.head := by
      rw [hhd]; simp only [cellLeft_foldContents, if_true, Option.getD_some]
      congr 1; exact Fin.ext hp0.symm
    have hcont : (fold cfg').tape.contents
        = Function.update (foldContents cfg.tape.contents) (foldHead cfg.tape.head)
          (some (Sum.inr (cellCur (foldContents cfg.tape.contents (foldHead cfg.tape.head)), some a',
            cellRight (foldContents cfg.tape.contents (foldHead cfg.tape.head))))) := by
      rw [show (fold cfg').tape.contents
            = foldContents (Function.update cfg.tape.contents cfg.tape.head a') from rfl]
      rw [show (some (Sum.inr (cellCur (foldContents cfg.tape.contents (foldHead cfg.tape.head)),
          some a', cellRight (foldContents cfg.tape.contents (foldHead cfg.tape.head)))) : FAlpha T Γ)
            = foldContents (Function.update cfg.tape.contents cfg.tape.head a') (foldHead cfg.tape.head)
          from by rw [hhd]; simp [foldContents, cellCur, cellRight, Function.update_apply,
            Fin.ext_iff, hp0]]
      exact (foldContents_update cfg.tape.contents cfg.tape.head a').symm
    have hprodhead : ∀ (s' : FState Λ) (w' : FAlpha T Γ),
        (⟨s', ((fold cfg).tape.write w').moveHead DLBA.Dir.stay⟩
          : DLBA.Cfg (FAlpha T Γ) (FState Λ) m).tape.head = (⟨0, by omega⟩ : Fin (m + 1)) := by
      intro s' w'; simp only [moveHead_stay_head, write_head]
      rw [show (fold cfg).tape.head = foldHead cfg.tape.head from rfl, hhd]
    rcases d' with _ | _ | _
    · -- left: clamp keeps head at cell 0
      have hch : cfg'.tape.head = cfg.tape.head := by
        rw [hcfg']; simp only [moveHead_left_head, write_head,
          dif_neg (show ¬ 0 < cfg.tape.head.val by omega)]
      refine ⟨FState.sim q' FMode.onLeft, wcell, DLBA.Dir.stay, ?_, ?_⟩
      · show _ ∈ flagTransition M' (FState.sim cfg.state (foldMode cfg.tape.head))
          (foldContents cfg.tape.contents (foldHead cfg.tape.head))
        rw [hmode]; exact ⟨(q', a', DLBA.Dir.left), by rw [hrd]; exact hmem, rfl⟩
      · refine cfg_ext' ?_ hcont ?_
        · rw [show (fold cfg').state = FState.sim cfg'.state (foldMode cfg'.tape.head) from rfl,
              show cfg'.state = q' from rfl, hch, hmode]
        · rw [show (fold cfg').tape.head = foldHead cfg'.tape.head from rfl, hch, hhd, hprodhead]
    · -- right: head → cell 0+1 = interior
      have hch : cfg'.tape.head = (⟨cfg.tape.head.val + 1, by omega⟩ : Fin (m + 3)) := by
        rw [hcfg']; simp only [moveHead_right_head, write_head,
          dif_pos (show cfg.tape.head.val < m + 2 by omega)]
      refine ⟨FState.sim q' FMode.mid, wcell, DLBA.Dir.stay, ?_, ?_⟩
      · show _ ∈ flagTransition M' (FState.sim cfg.state (foldMode cfg.tape.head))
          (foldContents cfg.tape.contents (foldHead cfg.tape.head))
        rw [hmode]; exact ⟨(q', a', DLBA.Dir.right), by rw [hrd]; exact hmem, rfl⟩
      · refine cfg_ext' ?_ hcont ?_
        · rw [show (fold cfg').state = FState.sim cfg'.state (foldMode cfg'.tape.head) from rfl,
              show cfg'.state = q' from rfl, hch,
              foldMode_mid (by simp only [Fin.val_mk]; omega) (by simp only [Fin.val_mk]; omega)]
        · rw [show (fold cfg').tape.head = foldHead cfg'.tape.head from rfl, hch, hprodhead]
          apply Fin.ext; rw [foldHead_val]; simp only [Fin.val_mk]; split_ifs <;> omega
    · -- stay
      have hch : cfg'.tape.head = cfg.tape.head := by rw [hcfg']; simp
      refine ⟨FState.sim q' FMode.onLeft, wcell, DLBA.Dir.stay, ?_, ?_⟩
      · show _ ∈ flagTransition M' (FState.sim cfg.state (foldMode cfg.tape.head))
          (foldContents cfg.tape.contents (foldHead cfg.tape.head))
        rw [hmode]; exact ⟨(q', a', DLBA.Dir.stay), by rw [hrd]; exact hmem, rfl⟩
      · refine cfg_ext' ?_ hcont ?_
        · rw [show (fold cfg').state = FState.sim cfg'.state (foldMode cfg'.tape.head) from rfl,
              show cfg'.state = q' from rfl, hch, hmode]
        · rw [show (fold cfg').tape.head = foldHead cfg'.tape.head from rfl, hch, hhd, hprodhead]
  · by_cases hpL : cfg.tape.head.val = m + 2
    · -- `M'` head on `⊣`: mode `onRight`, flag head stays at cell `m`.
      have hmode : foldMode cfg.tape.head = FMode.onRight := foldMode_last hpL
      have hhd : foldHead cfg.tape.head = (⟨m, by omega⟩ : Fin (m + 1)) := by
        apply Fin.ext; rw [foldHead_val]; simp [hpL]
      set wcell : FAlpha T Γ :=
        some (Sum.inr (cellCur (foldContents cfg.tape.contents (foldHead cfg.tape.head)),
          cellLeft (foldContents cfg.tape.contents (foldHead cfg.tape.head)), some a')) with hwcell
      have hrd : (cellRight (foldContents cfg.tape.contents (foldHead cfg.tape.head))).getD rightMark
          = cfg.tape.contents cfg.tape.head := by
        rw [hhd]; simp only [cellRight_foldContents, if_true, Option.getD_some]
        congr 1; exact Fin.ext hpL.symm
      have hcont : (fold cfg').tape.contents
          = Function.update (foldContents cfg.tape.contents) (foldHead cfg.tape.head) wcell := by
        rw [show (fold cfg').tape.contents
              = foldContents (Function.update cfg.tape.contents cfg.tape.head a') from rfl]
        rw [show wcell = foldContents (Function.update cfg.tape.contents cfg.tape.head a')
              (foldHead cfg.tape.head) from by
            rw [hwcell, hhd]; simp [foldContents, cellCur, cellLeft, Function.update_apply,
              Fin.ext_iff, hpL]]
        exact (foldContents_update cfg.tape.contents cfg.tape.head a').symm
      have hprodhead : ∀ (s' : FState Λ) (w' : FAlpha T Γ),
          (⟨s', ((fold cfg).tape.write w').moveHead DLBA.Dir.stay⟩
            : DLBA.Cfg (FAlpha T Γ) (FState Λ) m).tape.head = (⟨m, by omega⟩ : Fin (m + 1)) := by
        intro s' w'; simp only [moveHead_stay_head, write_head]
        rw [show (fold cfg).tape.head = foldHead cfg.tape.head from rfl, hhd]
      rcases d' with _ | _ | _
      · -- left: head → m+1 = interior
        have hch : cfg'.tape.head = (⟨cfg.tape.head.val - 1, by omega⟩ : Fin (m + 3)) := by
          rw [hcfg']; simp only [moveHead_left_head, write_head,
            dif_pos (show 0 < cfg.tape.head.val by omega)]
        refine ⟨FState.sim q' FMode.mid, wcell, DLBA.Dir.stay, ?_, ?_⟩
        · show _ ∈ flagTransition M' (FState.sim cfg.state (foldMode cfg.tape.head))
            (foldContents cfg.tape.contents (foldHead cfg.tape.head))
          rw [hmode]; exact ⟨(q', a', DLBA.Dir.left), by rw [hrd]; exact hmem, rfl⟩
        · refine cfg_ext' ?_ hcont ?_
          · rw [show (fold cfg').state = FState.sim cfg'.state (foldMode cfg'.tape.head) from rfl,
                show cfg'.state = q' from rfl, hch,
                foldMode_mid (by simp only [Fin.val_mk]; omega) (by simp only [Fin.val_mk]; omega)]
          · rw [show (fold cfg').tape.head = foldHead cfg'.tape.head from rfl, hch, hprodhead]
            apply Fin.ext; rw [foldHead_val]; simp only [Fin.val_mk]; split_ifs <;> omega
      · -- right: clamp keeps head at cell m+2
        have hch : cfg'.tape.head = cfg.tape.head := by
          rw [hcfg']; simp only [moveHead_right_head, write_head,
            dif_neg (show ¬ cfg.tape.head.val < m + 2 by omega)]
        refine ⟨FState.sim q' FMode.onRight, wcell, DLBA.Dir.stay, ?_, ?_⟩
        · show _ ∈ flagTransition M' (FState.sim cfg.state (foldMode cfg.tape.head))
            (foldContents cfg.tape.contents (foldHead cfg.tape.head))
          rw [hmode]; exact ⟨(q', a', DLBA.Dir.right), by rw [hrd]; exact hmem, rfl⟩
        · refine cfg_ext' ?_ hcont ?_
          · rw [show (fold cfg').state = FState.sim cfg'.state (foldMode cfg'.tape.head) from rfl,
                show cfg'.state = q' from rfl, hch, hmode]
          · rw [show (fold cfg').tape.head = foldHead cfg'.tape.head from rfl, hch, hhd, hprodhead]
      · -- stay
        have hch : cfg'.tape.head = cfg.tape.head := by rw [hcfg']; simp
        refine ⟨FState.sim q' FMode.onRight, wcell, DLBA.Dir.stay, ?_, ?_⟩
        · show _ ∈ flagTransition M' (FState.sim cfg.state (foldMode cfg.tape.head))
            (foldContents cfg.tape.contents (foldHead cfg.tape.head))
          rw [hmode]; exact ⟨(q', a', DLBA.Dir.stay), by rw [hrd]; exact hmem, rfl⟩
        · refine cfg_ext' ?_ hcont ?_
          · rw [show (fold cfg').state = FState.sim cfg'.state (foldMode cfg'.tape.head) from rfl,
                show cfg'.state = q' from rfl, hch, hmode]
          · rw [show (fold cfg').tape.head = foldHead cfg'.tape.head from rfl, hch, hhd, hprodhead]
    · -- interior: mode `mid`. The head moves; boundary detection via the folded marks.
      have hmode : foldMode cfg.tape.head = FMode.mid := foldMode_mid hp0 hpL
      have hcl := cfg.tape.head.isLt
      have hhd : foldHead cfg.tape.head = (⟨cfg.tape.head.val - 1, by omega⟩ : Fin (m + 1)) := by
        apply Fin.ext; rw [foldHead_val]; simp [hp0, hpL]
      have hLval : (foldHead cfg.tape.head).val = cfg.tape.head.val - 1 := by rw [hhd]
      have hfh : (fold cfg).tape.head.val = cfg.tape.head.val - 1 := hLval
      have hrd : cellCur (foldContents cfg.tape.contents (foldHead cfg.tape.head))
          = cfg.tape.contents cfg.tape.head := by
        rw [cellCur_foldContents]; congr 1; apply Fin.ext; simp only [Fin.val_mk]; rw [hLval]; omega
      have hLsome : (cellLeft (foldContents cfg.tape.contents (foldHead cfg.tape.head))).isSome
          = decide (cfg.tape.head.val = 1) := by
        rw [cellLeft_foldContents, hLval]
        by_cases h : cfg.tape.head.val = 1
        · simp [h]
        · rw [if_neg (show cfg.tape.head.val - 1 ≠ 0 by omega)]; simp [h]
      have hRsome : (cellRight (foldContents cfg.tape.contents (foldHead cfg.tape.head))).isSome
          = decide (cfg.tape.head.val = m + 1) := by
        rw [cellRight_foldContents, hLval]
        by_cases h : cfg.tape.head.val = m + 1
        · simp [h]
        · rw [if_neg (show cfg.tape.head.val - 1 ≠ m by omega)]; simp [h]
      set wcell : FAlpha T Γ :=
        some (Sum.inr (a', cellLeft (foldContents cfg.tape.contents (foldHead cfg.tape.head)),
          cellRight (foldContents cfg.tape.contents (foldHead cfg.tape.head)))) with hwcell
      have hwc : wcell = foldContents (Function.update cfg.tape.contents cfg.tape.head a')
          (foldHead cfg.tape.head) := by
        rw [hwcell]
        simp only [foldContents, cellLeft, cellRight, Function.update_apply,
          if_pos (show (⟨(foldHead cfg.tape.head).val + 1, by have := cfg.tape.head.isLt; omega⟩
            : Fin (m + 3)) = cfg.tape.head from by apply Fin.ext; simp only [Fin.val_mk]; rw [hLval]; omega),
          if_neg (show ¬ (⟨0, by omega⟩ : Fin (m + 3)) = cfg.tape.head from by
            simp only [Fin.ext_iff, Fin.val_mk]; omega),
          if_neg (show ¬ (⟨m + 2, by omega⟩ : Fin (m + 3)) = cfg.tape.head from by
            simp only [Fin.ext_iff, Fin.val_mk]; omega)]
      have hcont : (fold cfg').tape.contents
          = Function.update (foldContents cfg.tape.contents) (foldHead cfg.tape.head) wcell := by
        rw [show (fold cfg').tape.contents
              = foldContents (Function.update cfg.tape.contents cfg.tape.head a') from rfl, hwc]
        exact (foldContents_update cfg.tape.contents cfg.tape.head a').symm
      rcases d' with _ | _ | _
      · -- left
        have hch : cfg'.tape.head = (⟨cfg.tape.head.val - 1, by omega⟩ : Fin (m + 3)) := by
          rw [hcfg']; simp only [moveHead_left_head, write_head,
            dif_pos (show 0 < cfg.tape.head.val by omega)]
        refine ⟨FState.sim q'
            (if (cellLeft (foldContents cfg.tape.contents (foldHead cfg.tape.head))).isSome
              then FMode.onLeft else FMode.mid), wcell,
            (if (cellLeft (foldContents cfg.tape.contents (foldHead cfg.tape.head))).isSome
              then DLBA.Dir.stay else DLBA.Dir.left), ?_, ?_⟩
        · show _ ∈ flagTransition M' (FState.sim cfg.state (foldMode cfg.tape.head))
            (foldContents cfg.tape.contents (foldHead cfg.tape.head))
          rw [hmode]; exact ⟨(q', a', DLBA.Dir.left), by rw [hrd]; exact hmem, rfl⟩
        · refine cfg_ext' ?_ hcont ?_
          · rw [show (fold cfg').state = FState.sim cfg'.state (foldMode cfg'.tape.head) from rfl,
                show cfg'.state = q' from rfl, hch, hLsome]
            by_cases hb : cfg.tape.head.val = 1
            · rw [foldMode_zero (by simp only [Fin.val_mk]; omega),
                show (if decide (cfg.tape.head.val = 1) then FMode.onLeft else FMode.mid)
                  = FMode.onLeft from by simp [hb]]
            · rw [foldMode_mid (by simp only [Fin.val_mk]; omega) (by simp only [Fin.val_mk]; omega),
                show (if decide (cfg.tape.head.val = 1) then FMode.onLeft else FMode.mid)
                  = FMode.mid from by simp [hb]]
          · rw [show (fold cfg').tape.head = foldHead cfg'.tape.head from rfl, hch, hLsome]
            by_cases hb : cfg.tape.head.val = 1
            · rw [show (if decide (cfg.tape.head.val = 1) then DLBA.Dir.stay else DLBA.Dir.left)
                  = DLBA.Dir.stay from by simp [hb]]
              apply Fin.ext; rw [foldHead_val]
              simp only [moveHead_stay_head, write_head, hfh]; split_ifs <;> simp_all <;> omega
            · rw [show (if decide (cfg.tape.head.val = 1) then DLBA.Dir.stay else DLBA.Dir.left)
                  = DLBA.Dir.left from by simp [hb]]
              apply Fin.ext; rw [foldHead_val]
              simp only [moveHead_left_head_val, write_head, hfh]; split_ifs <;> simp_all <;> omega
      · -- right
        have hch : cfg'.tape.head = (⟨cfg.tape.head.val + 1, by omega⟩ : Fin (m + 3)) := by
          rw [hcfg']; simp only [moveHead_right_head, write_head,
            dif_pos (show cfg.tape.head.val < m + 2 by omega)]
        refine ⟨FState.sim q'
            (if (cellRight (foldContents cfg.tape.contents (foldHead cfg.tape.head))).isSome
              then FMode.onRight else FMode.mid), wcell,
            (if (cellRight (foldContents cfg.tape.contents (foldHead cfg.tape.head))).isSome
              then DLBA.Dir.stay else DLBA.Dir.right), ?_, ?_⟩
        · show _ ∈ flagTransition M' (FState.sim cfg.state (foldMode cfg.tape.head))
            (foldContents cfg.tape.contents (foldHead cfg.tape.head))
          rw [hmode]; exact ⟨(q', a', DLBA.Dir.right), by rw [hrd]; exact hmem, rfl⟩
        · refine cfg_ext' ?_ hcont ?_
          · rw [show (fold cfg').state = FState.sim cfg'.state (foldMode cfg'.tape.head) from rfl,
                show cfg'.state = q' from rfl, hch, hRsome]
            by_cases hb : cfg.tape.head.val = m + 1
            · rw [foldMode_last (by simp only [Fin.val_mk]; omega),
                show (if decide (cfg.tape.head.val = m + 1) then FMode.onRight else FMode.mid)
                  = FMode.onRight from by simp [hb]]
            · rw [foldMode_mid (by simp only [Fin.val_mk]; omega) (by simp only [Fin.val_mk]; omega),
                show (if decide (cfg.tape.head.val = m + 1) then FMode.onRight else FMode.mid)
                  = FMode.mid from by simp [hb]]
          · rw [show (fold cfg').tape.head = foldHead cfg'.tape.head from rfl, hch, hRsome]
            by_cases hb : cfg.tape.head.val = m + 1
            · rw [show (if decide (cfg.tape.head.val = m + 1) then DLBA.Dir.stay else DLBA.Dir.right)
                  = DLBA.Dir.stay from by simp [hb]]
              apply Fin.ext; rw [foldHead_val]
              simp only [moveHead_stay_head, write_head, hfh]; split_ifs <;> simp_all <;> omega
            · rw [show (if decide (cfg.tape.head.val = m + 1) then DLBA.Dir.stay else DLBA.Dir.right)
                  = DLBA.Dir.right from by simp [hb]]
              apply Fin.ext; rw [foldHead_val]
              show (if cfg.tape.head.val + 1 = 0 then 0
                else if cfg.tape.head.val + 1 = m + 2 then m else cfg.tape.head.val + 1 - 1) = _
              simp only [moveHead_right_head_val, write_head, hfh]
              rw [if_pos (show cfg.tape.head.val - 1 < m by omega)]
              split_ifs <;> omega
      · -- stay
        have hch : cfg'.tape.head = cfg.tape.head := by rw [hcfg']; simp
        refine ⟨FState.sim q' FMode.mid, wcell, DLBA.Dir.stay, ?_, ?_⟩
        · show _ ∈ flagTransition M' (FState.sim cfg.state (foldMode cfg.tape.head))
            (foldContents cfg.tape.contents (foldHead cfg.tape.head))
          rw [hmode]; exact ⟨(q', a', DLBA.Dir.stay), by rw [hrd]; exact hmem, rfl⟩
        · refine cfg_ext' ?_ hcont ?_
          · rw [show (fold cfg').state = FState.sim cfg'.state (foldMode cfg'.tape.head) from rfl,
                show cfg'.state = q' from rfl, hch, hmode]
          · rw [show (fold cfg').tape.head = foldHead cfg'.tape.head from rfl, hch]
            apply Fin.ext; rw [foldHead_val]
            simp only [moveHead_stay_head, write_head, hfh]; split_ifs <;> simp_all <;> omega
/-- The simulation extends to whole `M'`-computations. -/
theorem fold_reaches (M' : Machine (EndAlpha T Γ) Λ) {m : ℕ}
    {cfg cfg' : DLBA.Cfg (EndAlpha T Γ) Λ (m + 2)} (h : Reaches M' cfg cfg') :
    Reaches (flagMachine M') (fold cfg) (fold cfg') := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail (fold_step M' hbc)

end LBA


