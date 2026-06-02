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
      { (FState.scan, some (Sum.inr (cellCur r, some leftMark, none)), DLBA.Dir.right) }
  | .scan =>
      { (FState.scan, some (Sum.inr (cellCur r, cellLeft r, none)), DLBA.Dir.right),
        (FState.verify, some (Sum.inr (cellCur r, cellLeft r, some rightMark)), DLBA.Dir.right) }
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
          apply Fin.ext; rw [foldHead_val]; simp only [Fin.val_mk]; split_ifs <;> simp_all <;> omega
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
            apply Fin.ext; rw [foldHead_val]; simp only [Fin.val_mk]; split_ifs <;> simp_all <;> omega
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

set_option maxRecDepth 4000 in
/-- **Backward simulation.** Every `flagMachine` step out of a folded configuration `fold cfg`
decodes to a genuine `M'`-step: it lands on `fold cfg'` for some `cfg'` with `Step M' cfg cfg'`. -/
theorem sim_step_inv (M' : Machine (EndAlpha T Γ) Λ) {m : ℕ}
    {cfg : DLBA.Cfg (EndAlpha T Γ) Λ (m + 2)} {X : DLBA.Cfg (FAlpha T Γ) (FState Λ) m}
    (h : Step (flagMachine M') (fold cfg) X) :
    ∃ cfg' : DLBA.Cfg (EndAlpha T Γ) Λ (m + 2), Step M' cfg cfg' ∧ X = fold cfg' := by
  obtain ⟨s', a'flag, d'flag, hmem, hX⟩ := h
  rw [show (fold cfg).state = FState.sim cfg.state (foldMode cfg.tape.head) from rfl,
     show (fold cfg).tape.read = foldContents cfg.tape.contents (foldHead cfg.tape.head)
       from rfl] at hmem
  by_cases hp0 : cfg.tape.head.val = 0
  · -- `M'` head on `⊢`: mode `onLeft`.
    have hmode : foldMode cfg.tape.head = FMode.onLeft := foldMode_zero hp0
    have hhd : foldHead cfg.tape.head = (⟨0, by omega⟩ : Fin (m + 1)) := by
      apply Fin.ext; rw [foldHead_val]; simp [hp0]
    have hrd : (cellLeft (foldContents cfg.tape.contents (foldHead cfg.tape.head))).getD leftMark
        = cfg.tape.contents cfg.tape.head := by
      rw [hhd]; simp only [cellLeft_foldContents, if_true, Option.getD_some]
      congr 1; exact Fin.ext hp0.symm
    have hprodhead : ∀ (s2 : FState Λ) (w2 : FAlpha T Γ),
        (⟨s2, ((fold cfg).tape.write w2).moveHead DLBA.Dir.stay⟩
          : DLBA.Cfg (FAlpha T Γ) (FState Λ) m).tape.head = (⟨0, by omega⟩ : Fin (m + 1)) := by
      intro s2 w2; simp only [moveHead_stay_head, write_head]
      rw [show (fold cfg).tape.head = foldHead cfg.tape.head from rfl, hhd]
    rw [hmode] at hmem
    simp only [flagMachine, flagTransition, Set.mem_setOf_eq] at hmem
    obtain ⟨⟨q', a', d'⟩, hp, hpeq⟩ := hmem
    rw [hrd] at hp
    set wcell : FAlpha T Γ :=
      some (Sum.inr (cellCur (foldContents cfg.tape.contents (foldHead cfg.tape.head)), some a',
        cellRight (foldContents cfg.tape.contents (foldHead cfg.tape.head)))) with hwcell
    have hcontGen : foldContents (Function.update cfg.tape.contents cfg.tape.head a')
        = Function.update (foldContents cfg.tape.contents) (foldHead cfg.tape.head) wcell := by
      rw [hwcell, show (some (Sum.inr (cellCur (foldContents cfg.tape.contents (foldHead cfg.tape.head)),
          some a', cellRight (foldContents cfg.tape.contents (foldHead cfg.tape.head)))) : FAlpha T Γ)
            = foldContents (Function.update cfg.tape.contents cfg.tape.head a') (foldHead cfg.tape.head)
          from by rw [hhd]; simp [foldContents, cellCur, cellRight, Function.update_apply,
            Fin.ext_iff, hp0]]
      exact (foldContents_update cfg.tape.contents cfg.tape.head a').symm
    rcases d' with _ | _ | _
    · -- left: clamp keeps `M'` head at `⊢`
      refine ⟨⟨q', (cfg.tape.write a').moveHead DLBA.Dir.left⟩, ⟨q', a', DLBA.Dir.left, hp, rfl⟩, ?_⟩
      set cfg' : DLBA.Cfg (EndAlpha T Γ) Λ (m + 2) :=
        ⟨q', (cfg.tape.write a').moveHead DLBA.Dir.left⟩ with hcfg'
      have hch : cfg'.tape.head = cfg.tape.head := by
        rw [hcfg']; simp only [moveHead_left_head, write_head,
          dif_neg (show ¬ 0 < cfg.tape.head.val by omega)]
      have hcont : (fold cfg').tape.contents
          = Function.update (foldContents cfg.tape.contents) (foldHead cfg.tape.head) wcell :=
        hcontGen
      clear hcontGen hp
      simp only [Prod.mk.injEq] at hpeq; obtain ⟨rfl, rfl, rfl⟩ := hpeq
      subst hX; symm
      refine cfg_ext' ?_ hcont ?_
      · rw [show (fold cfg').state = FState.sim cfg'.state (foldMode cfg'.tape.head) from rfl,
            show cfg'.state = q' from rfl, hch, hmode]
      · rw [show (fold cfg').tape.head = foldHead cfg'.tape.head from rfl, hch, hhd, hprodhead]
    · -- right: head → interior cell `1`
      refine ⟨⟨q', (cfg.tape.write a').moveHead DLBA.Dir.right⟩, ⟨q', a', DLBA.Dir.right, hp, rfl⟩, ?_⟩
      set cfg' : DLBA.Cfg (EndAlpha T Γ) Λ (m + 2) :=
        ⟨q', (cfg.tape.write a').moveHead DLBA.Dir.right⟩ with hcfg'
      have hch : cfg'.tape.head = (⟨cfg.tape.head.val + 1, by omega⟩ : Fin (m + 3)) := by
        rw [hcfg']; simp only [moveHead_right_head, write_head,
          dif_pos (show cfg.tape.head.val < m + 2 by omega)]
      have hcont : (fold cfg').tape.contents
          = Function.update (foldContents cfg.tape.contents) (foldHead cfg.tape.head) wcell :=
        hcontGen
      clear hcontGen hp
      simp only [Prod.mk.injEq] at hpeq; obtain ⟨rfl, rfl, rfl⟩ := hpeq
      subst hX; symm
      refine cfg_ext' ?_ hcont ?_
      · rw [show (fold cfg').state = FState.sim cfg'.state (foldMode cfg'.tape.head) from rfl,
            show cfg'.state = q' from rfl, hch,
            foldMode_mid (by simp only [Fin.val_mk]; omega) (by simp only [Fin.val_mk]; omega)]
      · rw [show (fold cfg').tape.head = foldHead cfg'.tape.head from rfl, hch, hprodhead]
        apply Fin.ext; rw [foldHead_val]; simp only [Fin.val_mk]; split_ifs <;> simp_all <;> omega
    · -- stay
      refine ⟨⟨q', (cfg.tape.write a').moveHead DLBA.Dir.stay⟩, ⟨q', a', DLBA.Dir.stay, hp, rfl⟩, ?_⟩
      set cfg' : DLBA.Cfg (EndAlpha T Γ) Λ (m + 2) :=
        ⟨q', (cfg.tape.write a').moveHead DLBA.Dir.stay⟩ with hcfg'
      have hch : cfg'.tape.head = cfg.tape.head := by rw [hcfg']; simp
      have hcont : (fold cfg').tape.contents
          = Function.update (foldContents cfg.tape.contents) (foldHead cfg.tape.head) wcell :=
        hcontGen
      clear hcontGen hp
      simp only [Prod.mk.injEq] at hpeq; obtain ⟨rfl, rfl, rfl⟩ := hpeq
      subst hX; symm
      refine cfg_ext' ?_ hcont ?_
      · rw [show (fold cfg').state = FState.sim cfg'.state (foldMode cfg'.tape.head) from rfl,
            show cfg'.state = q' from rfl, hch, hmode]
      · rw [show (fold cfg').tape.head = foldHead cfg'.tape.head from rfl, hch, hhd, hprodhead]
  · by_cases hpL : cfg.tape.head.val = m + 2
    · -- `M'` head on `⊣`: mode `onRight`.
      have hmode : foldMode cfg.tape.head = FMode.onRight := foldMode_last hpL
      have hhd : foldHead cfg.tape.head = (⟨m, by omega⟩ : Fin (m + 1)) := by
        apply Fin.ext; rw [foldHead_val]; simp [hpL]
      have hrd : (cellRight (foldContents cfg.tape.contents (foldHead cfg.tape.head))).getD rightMark
          = cfg.tape.contents cfg.tape.head := by
        rw [hhd]; simp only [cellRight_foldContents, if_true, Option.getD_some]
        congr 1; exact Fin.ext hpL.symm
      have hprodhead : ∀ (s2 : FState Λ) (w2 : FAlpha T Γ),
          (⟨s2, ((fold cfg).tape.write w2).moveHead DLBA.Dir.stay⟩
            : DLBA.Cfg (FAlpha T Γ) (FState Λ) m).tape.head = (⟨m, by omega⟩ : Fin (m + 1)) := by
        intro s2 w2; simp only [moveHead_stay_head, write_head]
        rw [show (fold cfg).tape.head = foldHead cfg.tape.head from rfl, hhd]
      rw [hmode] at hmem
      simp only [flagMachine, flagTransition, Set.mem_setOf_eq] at hmem
      obtain ⟨⟨q', a', d'⟩, hp, hpeq⟩ := hmem
      rw [hrd] at hp
      set wcell : FAlpha T Γ :=
        some (Sum.inr (cellCur (foldContents cfg.tape.contents (foldHead cfg.tape.head)),
          cellLeft (foldContents cfg.tape.contents (foldHead cfg.tape.head)), some a')) with hwcell
      have hcontGen : foldContents (Function.update cfg.tape.contents cfg.tape.head a')
          = Function.update (foldContents cfg.tape.contents) (foldHead cfg.tape.head) wcell := by
        rw [hwcell, show (some (Sum.inr (cellCur (foldContents cfg.tape.contents (foldHead cfg.tape.head)),
            cellLeft (foldContents cfg.tape.contents (foldHead cfg.tape.head)), some a')) : FAlpha T Γ)
              = foldContents (Function.update cfg.tape.contents cfg.tape.head a') (foldHead cfg.tape.head)
            from by rw [hhd]; simp [foldContents, cellCur, cellLeft, Function.update_apply,
              Fin.ext_iff, hpL]]
        exact (foldContents_update cfg.tape.contents cfg.tape.head a').symm
      rcases d' with _ | _ | _
      · -- left: head → interior cell `m+1`
        refine ⟨⟨q', (cfg.tape.write a').moveHead DLBA.Dir.left⟩, ⟨q', a', DLBA.Dir.left, hp, rfl⟩, ?_⟩
        set cfg' : DLBA.Cfg (EndAlpha T Γ) Λ (m + 2) :=
          ⟨q', (cfg.tape.write a').moveHead DLBA.Dir.left⟩ with hcfg'
        have hch : cfg'.tape.head = (⟨cfg.tape.head.val - 1, by omega⟩ : Fin (m + 3)) := by
          rw [hcfg']; simp only [moveHead_left_head, write_head,
            dif_pos (show 0 < cfg.tape.head.val by omega)]
        have hcont : (fold cfg').tape.contents
            = Function.update (foldContents cfg.tape.contents) (foldHead cfg.tape.head) wcell :=
          hcontGen
        clear hcontGen hp
        simp only [Prod.mk.injEq] at hpeq; obtain ⟨rfl, rfl, rfl⟩ := hpeq
        subst hX; symm
        refine cfg_ext' ?_ hcont ?_
        · rw [show (fold cfg').state = FState.sim cfg'.state (foldMode cfg'.tape.head) from rfl,
              show cfg'.state = q' from rfl, hch,
              foldMode_mid (by simp only [Fin.val_mk]; omega) (by simp only [Fin.val_mk]; omega)]
        · rw [show (fold cfg').tape.head = foldHead cfg'.tape.head from rfl, hch, hprodhead]
          apply Fin.ext; rw [foldHead_val]; simp only [Fin.val_mk]; split_ifs <;> simp_all <;> omega
      · -- right: clamp keeps `M'` head at `⊣`
        refine ⟨⟨q', (cfg.tape.write a').moveHead DLBA.Dir.right⟩, ⟨q', a', DLBA.Dir.right, hp, rfl⟩, ?_⟩
        set cfg' : DLBA.Cfg (EndAlpha T Γ) Λ (m + 2) :=
          ⟨q', (cfg.tape.write a').moveHead DLBA.Dir.right⟩ with hcfg'
        have hch : cfg'.tape.head = cfg.tape.head := by
          rw [hcfg']; simp only [moveHead_right_head, write_head,
            dif_neg (show ¬ cfg.tape.head.val < m + 2 by omega)]
        have hcont : (fold cfg').tape.contents
            = Function.update (foldContents cfg.tape.contents) (foldHead cfg.tape.head) wcell :=
          hcontGen
        clear hcontGen hp
        simp only [Prod.mk.injEq] at hpeq; obtain ⟨rfl, rfl, rfl⟩ := hpeq
        subst hX; symm
        refine cfg_ext' ?_ hcont ?_
        · rw [show (fold cfg').state = FState.sim cfg'.state (foldMode cfg'.tape.head) from rfl,
              show cfg'.state = q' from rfl, hch, hmode]
        · rw [show (fold cfg').tape.head = foldHead cfg'.tape.head from rfl, hch, hhd, hprodhead]
      · -- stay
        refine ⟨⟨q', (cfg.tape.write a').moveHead DLBA.Dir.stay⟩, ⟨q', a', DLBA.Dir.stay, hp, rfl⟩, ?_⟩
        set cfg' : DLBA.Cfg (EndAlpha T Γ) Λ (m + 2) :=
          ⟨q', (cfg.tape.write a').moveHead DLBA.Dir.stay⟩ with hcfg'
        have hch : cfg'.tape.head = cfg.tape.head := by rw [hcfg']; simp
        have hcont : (fold cfg').tape.contents
            = Function.update (foldContents cfg.tape.contents) (foldHead cfg.tape.head) wcell :=
          hcontGen
        clear hcontGen hp
        simp only [Prod.mk.injEq] at hpeq; obtain ⟨rfl, rfl, rfl⟩ := hpeq
        subst hX; symm
        refine cfg_ext' ?_ hcont ?_
        · rw [show (fold cfg').state = FState.sim cfg'.state (foldMode cfg'.tape.head) from rfl,
              show cfg'.state = q' from rfl, hch, hmode]
        · rw [show (fold cfg').tape.head = foldHead cfg'.tape.head from rfl, hch, hhd, hprodhead]
    · -- interior: mode `mid`.
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
      rw [hmode] at hmem
      simp only [flagMachine, flagTransition, Set.mem_setOf_eq] at hmem
      obtain ⟨⟨q', a', d'⟩, hp, hpeq⟩ := hmem
      rw [hrd] at hp
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
      have hcontGen : foldContents (Function.update cfg.tape.contents cfg.tape.head a')
          = Function.update (foldContents cfg.tape.contents) (foldHead cfg.tape.head) wcell := by
        rw [hwc]; exact (foldContents_update cfg.tape.contents cfg.tape.head a').symm
      rcases d' with _ | _ | _
      · -- left
        refine ⟨⟨q', (cfg.tape.write a').moveHead DLBA.Dir.left⟩, ⟨q', a', DLBA.Dir.left, hp, rfl⟩, ?_⟩
        set cfg' : DLBA.Cfg (EndAlpha T Γ) Λ (m + 2) :=
          ⟨q', (cfg.tape.write a').moveHead DLBA.Dir.left⟩ with hcfg'
        have hch : cfg'.tape.head = (⟨cfg.tape.head.val - 1, by omega⟩ : Fin (m + 3)) := by
          rw [hcfg']; simp only [moveHead_left_head, write_head,
            dif_pos (show 0 < cfg.tape.head.val by omega)]
        have hcont : (fold cfg').tape.contents
            = Function.update (foldContents cfg.tape.contents) (foldHead cfg.tape.head) wcell :=
          hcontGen
        clear hcontGen hp
        simp only [Prod.mk.injEq] at hpeq; obtain ⟨rfl, rfl, rfl⟩ := hpeq
        subst hX; symm
        refine cfg_ext' ?_ hcont ?_
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
        refine ⟨⟨q', (cfg.tape.write a').moveHead DLBA.Dir.right⟩, ⟨q', a', DLBA.Dir.right, hp, rfl⟩, ?_⟩
        set cfg' : DLBA.Cfg (EndAlpha T Γ) Λ (m + 2) :=
          ⟨q', (cfg.tape.write a').moveHead DLBA.Dir.right⟩ with hcfg'
        have hch : cfg'.tape.head = (⟨cfg.tape.head.val + 1, by omega⟩ : Fin (m + 3)) := by
          rw [hcfg']; simp only [moveHead_right_head, write_head,
            dif_pos (show cfg.tape.head.val < m + 2 by omega)]
        have hcont : (fold cfg').tape.contents
            = Function.update (foldContents cfg.tape.contents) (foldHead cfg.tape.head) wcell :=
          hcontGen
        clear hcontGen hp
        simp only [Prod.mk.injEq] at hpeq; obtain ⟨rfl, rfl, rfl⟩ := hpeq
        subst hX; symm
        refine cfg_ext' ?_ hcont ?_
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
        refine ⟨⟨q', (cfg.tape.write a').moveHead DLBA.Dir.stay⟩, ⟨q', a', DLBA.Dir.stay, hp, rfl⟩, ?_⟩
        set cfg' : DLBA.Cfg (EndAlpha T Γ) Λ (m + 2) :=
          ⟨q', (cfg.tape.write a').moveHead DLBA.Dir.stay⟩ with hcfg'
        have hch : cfg'.tape.head = cfg.tape.head := by rw [hcfg']; simp
        have hcont : (fold cfg').tape.contents
            = Function.update (foldContents cfg.tape.contents) (foldHead cfg.tape.head) wcell :=
          hcontGen
        clear hcontGen hp
        simp only [Prod.mk.injEq] at hpeq; obtain ⟨rfl, rfl, rfl⟩ := hpeq
        subst hX; symm
        refine cfg_ext' ?_ hcont ?_
        · rw [show (fold cfg').state = FState.sim cfg'.state (foldMode cfg'.tape.head) from rfl,
              show cfg'.state = q' from rfl, hch, hmode]
        · rw [show (fold cfg').tape.head = foldHead cfg'.tape.head from rfl, hch]
          apply Fin.ext; rw [foldHead_val]
          simp only [moveHead_stay_head, write_head, hfh]; split_ifs <;> simp_all <;> omega

/-! ### Init phase: the flag machine sets up the folded tape.

From the input tape `c`, `M` converts each cell to its folded form (`foldedTape`), marking cell `0`
with `⊢` and the last cell with `⊣`, then rewinds to cell `0` and enters the simulation. -/

/-- The fully folded tape obtained from an input tape `c`: each cell carries its interior content
`cellCur (c i)` plus the boundary marks at cells `0` and `m`. -/
def foldedTape {m : ℕ} (c : Fin (m + 1) → FAlpha T Γ) : Fin (m + 1) → FAlpha T Γ :=
  fun i => some (Sum.inr (cellCur (c i),
    (if i.val = 0 then some leftMark else none), (if i.val = m then some rightMark else none)))

/-- The tape with cells `< k` folded and cells `≥ k` still raw input. -/
def partialTape {m : ℕ} (c : Fin (m + 1) → FAlpha T Γ) (k : ℕ) : Fin (m + 1) → FAlpha T Γ :=
  fun i => if i.val < k then foldedTape c i else c i

/-- The over-scanned tape: every cell folded, the `⊢` mark on cell `0`, but **no** `⊣` mark (the
right-end guess has not yet been committed). Reached when `scan` keeps moving at the clamped last
cell. -/
def scanLast {m : ℕ} (c : Fin (m + 1) → FAlpha T Γ) : Fin (m + 1) → FAlpha T Γ :=
  fun i => some (Sum.inr (cellCur (c i), (if i.val = 0 then some leftMark else none), none))

/-- One `scan` step converts the cell at an interior position `k` and moves right. -/
theorem scan_step (M' : Machine (EndAlpha T Γ) Λ) {m : ℕ} (c : Fin (m + 1) → FAlpha T Γ)
    (hraw : ∀ i : Fin (m + 1), cellLeft (c i) = none)
    (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k < m) :
    Step (flagMachine M')
      ⟨FState.scan, ⟨partialTape c k, ⟨k, by omega⟩⟩⟩
      ⟨FState.scan, ⟨partialTape c (k + 1), ⟨k + 1, by omega⟩⟩⟩ := by
  have hr : (partialTape c k) ⟨k, by omega⟩ = c ⟨k, by omega⟩ := by simp [partialTape]
  have hl : cellLeft (c ⟨k, by omega⟩) = none := hraw _
  refine ⟨FState.scan,
    some (Sum.inr (cellCur ((partialTape c k) ⟨k, by omega⟩),
      cellLeft ((partialTape c k) ⟨k, by omega⟩), none)),
    DLBA.Dir.right, ?_, ?_⟩
  · show _ ∈ flagTransition M' FState.scan ((partialTape c k) ⟨k, by omega⟩)
    left; rfl
  · apply cfg_ext'
    · rfl
    · -- contents
      show partialTape c (k + 1)
        = Function.update (partialTape c k) ⟨k, by omega⟩
          (some (Sum.inr (cellCur ((partialTape c k) ⟨k, by omega⟩),
            cellLeft ((partialTape c k) ⟨k, by omega⟩), none)))
      rw [hr, hl]
      funext j
      rw [Function.update_apply]
      by_cases hj : j = (⟨k, by omega⟩ : Fin (m + 1))
      · subst hj
        rw [if_pos rfl]
        simp only [partialTape, foldedTape, Fin.val_mk]
        rw [if_pos (show k < k + 1 by omega), if_neg (show ¬ k = 0 by omega),
          if_neg (show ¬ k = m by omega)]
      · rw [if_neg hj]
        have hjk : j.val ≠ k := fun h => hj (Fin.ext h)
        simp only [partialTape]
        by_cases hjlt : j.val < k
        · rw [if_pos hjlt, if_pos (by omega)]
        · rw [if_neg hjlt, if_neg (by omega)]
    · -- head
      apply Fin.ext
      simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write]
      rw [dif_pos (show k < m by omega)]

theorem partialTape_full {m : ℕ} (c : Fin (m + 1) → FAlpha T Γ) :
    partialTape c (m + 1) = foldedTape c := by
  funext j; simp only [partialTape]; rw [if_pos (by have := j.isLt; omega)]

/-- The `scan` phase: from cell `1` to the last cell `m`, converting each interior cell. -/
theorem scan_reach (M' : Machine (EndAlpha T Γ) Λ) {m : ℕ} (c : Fin (m + 1) → FAlpha T Γ)
    (hraw : ∀ i : Fin (m + 1), cellLeft (c i) = none)
    (j : ℕ) (hj : 1 ≤ j) (hjm : j ≤ m) :
    Reaches (flagMachine M')
      ⟨FState.scan, ⟨partialTape c 1, ⟨1, by omega⟩⟩⟩
      ⟨FState.scan, ⟨partialTape c j, ⟨j, by omega⟩⟩⟩ := by
  induction j, hj using Nat.le_induction with
  | base => exact Relation.ReflTransGen.refl
  | succ j hj ih => exact (ih (by omega)).tail (scan_step M' c hraw j hj (by omega))

/-- `setup`: mark cell `0` with `⊢` and step right (case `m ≥ 1`, so cell `0` is not the last). -/
theorem setup_step (M' : Machine (EndAlpha T Γ) Λ) {m : ℕ} (c : Fin (m + 1) → FAlpha T Γ)
    (hm : 1 ≤ m) :
    Step (flagMachine M')
      ⟨FState.setup, ⟨c, ⟨0, by omega⟩⟩⟩
      ⟨FState.scan, ⟨partialTape c 1, ⟨1, by omega⟩⟩⟩ := by
  refine ⟨FState.scan, some (Sum.inr (cellCur (c ⟨0, by omega⟩), some leftMark, none)),
    DLBA.Dir.right, ?_, ?_⟩
  · show _ ∈ flagTransition M' FState.setup (c ⟨0, by omega⟩)
    rfl
  · apply cfg_ext'
    · rfl
    · show partialTape c 1 = Function.update c ⟨0, by omega⟩
        (some (Sum.inr (cellCur (c ⟨0, by omega⟩), some leftMark, none)))
      funext j
      rw [Function.update_apply]
      by_cases hj : j = (⟨0, by omega⟩ : Fin (m + 1))
      · subst hj
        rw [if_pos rfl]
        simp [partialTape, foldedTape, show ¬ (0 : ℕ) = m from by omega]
      · rw [if_neg hj]; simp only [partialTape]
        rw [if_neg (show ¬ j.val < 1 by have : j.val ≠ 0 := fun h => hj (Fin.ext h); omega)]
    · apply Fin.ext
      simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write]
      rw [dif_pos (show (0 : ℕ) < m by omega)]

/-- The last `scan` step (at cell `m`): mark it `⊣` and clamp, entering `verify`. -/
theorem lastscan_step (M' : Machine (EndAlpha T Γ) Λ) {m : ℕ} (c : Fin (m + 1) → FAlpha T Γ)
    (hraw : ∀ i : Fin (m + 1), cellLeft (c i) = none) (hm : 1 ≤ m) :
    Step (flagMachine M')
      ⟨FState.scan, ⟨partialTape c m, ⟨m, by omega⟩⟩⟩
      ⟨FState.verify, ⟨foldedTape c, ⟨m, by omega⟩⟩⟩ := by
  have hr : (partialTape c m) ⟨m, by omega⟩ = c ⟨m, by omega⟩ := by simp [partialTape]
  have hl : cellLeft (c ⟨m, by omega⟩) = none := hraw _
  refine ⟨FState.verify,
    some (Sum.inr (cellCur ((partialTape c m) ⟨m, by omega⟩),
      cellLeft ((partialTape c m) ⟨m, by omega⟩), some rightMark)),
    DLBA.Dir.right, ?_, ?_⟩
  · show _ ∈ flagTransition M' FState.scan ((partialTape c m) ⟨m, by omega⟩)
    right; rfl
  · apply cfg_ext'
    · rfl
    · show foldedTape c = Function.update (partialTape c m) ⟨m, by omega⟩
        (some (Sum.inr (cellCur ((partialTape c m) ⟨m, by omega⟩),
          cellLeft ((partialTape c m) ⟨m, by omega⟩), some rightMark)))
      rw [hr, hl]
      funext j
      rw [Function.update_apply]
      by_cases hj : j = (⟨m, by omega⟩ : Fin (m + 1))
      · subst hj
        rw [if_pos rfl]
        simp [foldedTape, show ¬ m = 0 from by omega]
      · rw [if_neg hj]; simp only [partialTape, foldedTape]
        have hjk : j.val ≠ m := fun h => hj (Fin.ext h)
        have := j.isLt
        rw [if_pos (show j.val < m by omega)]
    · apply Fin.ext
      simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write]
      rw [dif_neg (show ¬ m < m by omega)]

/-- `verify` confirms the guess (the right move clamped back onto the `⊣`-marked cell). -/
theorem verify_step (M' : Machine (EndAlpha T Γ) Λ) {m : ℕ} (c : Fin (m + 1) → FAlpha T Γ)
    (hm : 1 ≤ m) :
    Step (flagMachine M')
      ⟨FState.verify, ⟨foldedTape c, ⟨m, by omega⟩⟩⟩
      ⟨FState.rewind, ⟨foldedTape c, ⟨m - 1, by omega⟩⟩⟩ := by
  have hrt : (cellRight (foldedTape c ⟨m, by omega⟩)).isSome = true := by
    simp [foldedTape, cellRight]
  refine ⟨FState.rewind, foldedTape c ⟨m, by omega⟩, DLBA.Dir.left, ?_, ?_⟩
  · show _ ∈ flagTransition M' FState.verify (foldedTape c ⟨m, by omega⟩)
    simp only [flagTransition, hrt, if_true]; rfl
  · apply cfg_ext'
    · rfl
    · show foldedTape c = Function.update (foldedTape c) ⟨m, by omega⟩ (foldedTape c ⟨m, by omega⟩)
      rw [Function.update_eq_self]
    · apply Fin.ext
      simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write]
      rw [dif_pos (show 0 < m by omega)]

/-- One `rewind` step at an interior cell `k ≥ 1` (no left marker): move left. -/
theorem rewind_step (M' : Machine (EndAlpha T Γ) Λ) {m : ℕ} (c : Fin (m + 1) → FAlpha T Γ)
    (k : ℕ) (hk1 : 1 ≤ k) (hkm : k ≤ m) :
    Step (flagMachine M')
      ⟨FState.rewind, ⟨foldedTape c, ⟨k, by omega⟩⟩⟩
      ⟨FState.rewind, ⟨foldedTape c, ⟨k - 1, by omega⟩⟩⟩ := by
  have hlf : (cellLeft (foldedTape c ⟨k, by omega⟩)).isSome = false := by
    simp [foldedTape, cellLeft]; omega
  refine ⟨FState.rewind, foldedTape c ⟨k, by omega⟩, DLBA.Dir.left, ?_, ?_⟩
  · show _ ∈ flagTransition M' FState.rewind (foldedTape c ⟨k, by omega⟩)
    simp only [flagTransition, hlf, Bool.false_eq_true, if_false]; rfl
  · apply cfg_ext'
    · rfl
    · show foldedTape c = Function.update (foldedTape c) ⟨k, by omega⟩ (foldedTape c ⟨k, by omega⟩)
      rw [Function.update_eq_self]
    · apply Fin.ext
      simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write]
      rw [dif_pos (show 0 < k by omega)]

/-- The `rewind` phase: from cell `j` back down to cell `0`. -/
theorem rewind_reach (M' : Machine (EndAlpha T Γ) Λ) {m : ℕ} (c : Fin (m + 1) → FAlpha T Γ)
    (j : ℕ) (hjm : j ≤ m) :
    Reaches (flagMachine M')
      ⟨FState.rewind, ⟨foldedTape c, ⟨j, by omega⟩⟩⟩
      ⟨FState.rewind, ⟨foldedTape c, ⟨0, by omega⟩⟩⟩ := by
  induction j with
  | zero => exact Relation.ReflTransGen.refl
  | succ j ih =>
      exact Relation.ReflTransGen.head (rewind_step M' c (j + 1) (by omega) (by omega)) (ih (by omega))

/-- The final `rewind` step at cell `0`: the `⊢` mark is found, entering the simulation. -/
theorem rewind0_step (M' : Machine (EndAlpha T Γ) Λ) {m : ℕ} (c : Fin (m + 1) → FAlpha T Γ) :
    Step (flagMachine M')
      ⟨FState.rewind, ⟨foldedTape c, ⟨0, by omega⟩⟩⟩
      ⟨FState.sim M'.initial FMode.onLeft, ⟨foldedTape c, ⟨0, by omega⟩⟩⟩ := by
  have hls : (cellLeft (foldedTape c ⟨0, by omega⟩)).isSome = true := by simp [foldedTape, cellLeft]
  refine ⟨FState.sim M'.initial FMode.onLeft, foldedTape c ⟨0, by omega⟩, DLBA.Dir.stay, ?_, ?_⟩
  · show _ ∈ flagTransition M' FState.rewind (foldedTape c ⟨0, by omega⟩)
    simp only [flagTransition, hls, if_true]; rfl
  · apply cfg_ext'
    · rfl
    · show foldedTape c = Function.update (foldedTape c) ⟨0, by omega⟩ (foldedTape c ⟨0, by omega⟩)
      rw [Function.update_eq_self]
    · apply Fin.ext; simp [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write]

/-- The whole init phase: from the input tape `c`, reach the simulation start at `M'.initial`
on the head (`⊢`), with the tape fully folded. -/
theorem init_reach (M' : Machine (EndAlpha T Γ) Λ) {m : ℕ} (c : Fin (m + 1) → FAlpha T Γ)
    (hraw : ∀ i : Fin (m + 1), cellLeft (c i) = none) :
    Reaches (flagMachine M')
      ⟨FState.setup, ⟨c, ⟨0, by omega⟩⟩⟩
      ⟨FState.sim M'.initial FMode.onLeft, ⟨foldedTape c, ⟨0, by omega⟩⟩⟩ := by
  by_cases hm0 : m = 0
  · subst hm0
    -- single cell: setup marks `⊢`, scan guesses `⊣` (preserving `⊢`), then verify→rewind→sim.
    have h1 : Step (flagMachine M') ⟨FState.setup, ⟨c, ⟨0, by omega⟩⟩⟩
        ⟨FState.scan, ⟨scanLast c, ⟨0, by omega⟩⟩⟩ := by
      refine ⟨FState.scan, some (Sum.inr (cellCur (c ⟨0, by omega⟩), some leftMark, none)),
        DLBA.Dir.right, ?_, ?_⟩
      · show _ ∈ flagTransition M' FState.setup (c ⟨0, by omega⟩); rfl
      · apply cfg_ext'
        · rfl
        · show scanLast c = Function.update c ⟨0, by omega⟩
            (some (Sum.inr (cellCur (c ⟨0, by omega⟩), some leftMark, none)))
          funext j
          have hj0 : j = (⟨0, by omega⟩ : Fin (0 + 1)) := Fin.ext (by have := j.isLt; omega)
          subst hj0; rw [Function.update_apply, if_pos rfl]; simp [scanLast]
        · apply Fin.ext; simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write]
          rw [dif_neg (show ¬ (0 : ℕ) < 0 by omega)]
    have h2 : Step (flagMachine M') ⟨FState.scan, ⟨scanLast c, ⟨0, by omega⟩⟩⟩
        ⟨FState.verify, ⟨foldedTape c, ⟨0, by omega⟩⟩⟩ := by
      refine ⟨FState.verify,
        some (Sum.inr (cellCur (scanLast c ⟨0, by omega⟩), cellLeft (scanLast c ⟨0, by omega⟩),
          some rightMark)), DLBA.Dir.right, ?_, ?_⟩
      · show _ ∈ flagTransition M' FState.scan (scanLast c ⟨0, by omega⟩); right; rfl
      · apply cfg_ext'
        · rfl
        · show foldedTape c = Function.update (scanLast c) ⟨0, by omega⟩
            (some (Sum.inr (cellCur (scanLast c ⟨0, by omega⟩), cellLeft (scanLast c ⟨0, by omega⟩),
              some rightMark)))
          funext j
          have hj0 : j = (⟨0, by omega⟩ : Fin (0 + 1)) := Fin.ext (by have := j.isLt; omega)
          subst hj0; rw [Function.update_apply, if_pos rfl]; simp [scanLast, foldedTape, cellCur, cellLeft]
        · apply Fin.ext; simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write]
          rw [dif_neg (show ¬ (0 : ℕ) < 0 by omega)]
    have h3 : Step (flagMachine M') ⟨FState.verify, ⟨foldedTape c, ⟨0, by omega⟩⟩⟩
        ⟨FState.rewind, ⟨foldedTape c, ⟨0, by omega⟩⟩⟩ := by
      have hrt : (cellRight (foldedTape c ⟨0, by omega⟩)).isSome = true := by
        simp [foldedTape, cellRight]
      refine ⟨FState.rewind, foldedTape c ⟨0, by omega⟩, DLBA.Dir.left, ?_, ?_⟩
      · show _ ∈ flagTransition M' FState.verify (foldedTape c ⟨0, by omega⟩)
        simp only [flagTransition, hrt, if_true]; rfl
      · apply cfg_ext'
        · rfl
        · show foldedTape c = Function.update (foldedTape c) ⟨0, by omega⟩ (foldedTape c ⟨0, by omega⟩)
          rw [Function.update_eq_self]
        · apply Fin.ext; simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write]
          rw [dif_neg (show ¬ (0 : ℕ) < 0 by omega)]
    exact Relation.ReflTransGen.head h1 (Relation.ReflTransGen.head h2
      (Relation.ReflTransGen.head h3 (Relation.ReflTransGen.single (rewind0_step M' c))))
  · have hm : 1 ≤ m := by omega
    refine Relation.ReflTransGen.head (setup_step M' c hm)
      ((scan_reach M' c hraw m hm le_rfl).trans
        (Relation.ReflTransGen.head (lastscan_step M' c hraw hm)
          (Relation.ReflTransGen.head (verify_step M' c hm)
            ((rewind_reach M' c (m - 1) (by omega)).trans
              (Relation.ReflTransGen.single (rewind0_step M' c))))))

/-! ### Backward invariant: every reachable `flagMachine` configuration is sound.

`GoodF` enumerates the configurations reachable from the start `⟨setup, c₀⟩`: the init-phase
configurations (all non-accepting — `setup`, the partial/over scans, the dead and successful
`verify`, the `rewind`), and the simulation-phase configurations, which are exactly `fold`-images
of `M'`-configurations reachable from `M'`'s start on `e₀`. -/
def GoodF (M' : Machine (EndAlpha T Γ) Λ) {m : ℕ}
    (e₀ : Fin (m + 3) → EndAlpha T Γ) (c₀ : Fin (m + 1) → FAlpha T Γ)
    (X : DLBA.Cfg (FAlpha T Γ) (FState Λ) m) : Prop :=
  (X = ⟨FState.setup, ⟨c₀, ⟨0, by omega⟩⟩⟩)
  ∨ (∃ k : Fin (m + 1), 1 ≤ k.val ∧ X = ⟨FState.scan, ⟨partialTape c₀ k.val, k⟩⟩)
  ∨ (X = ⟨FState.scan, ⟨scanLast c₀, ⟨m, by omega⟩⟩⟩)
  ∨ (X.state = FState.verify ∧ cellRight (X.tape.contents X.tape.head) = none)
  ∨ (X = ⟨FState.verify, ⟨foldedTape c₀, ⟨m, by omega⟩⟩⟩)
  ∨ (∃ k : Fin (m + 1), X = ⟨FState.rewind, ⟨foldedTape c₀, k⟩⟩)
  ∨ (∃ cfg : DLBA.Cfg (EndAlpha T Γ) Λ (m + 2),
        Reaches M' ⟨M'.initial, ⟨e₀, ⟨0, by omega⟩⟩⟩ cfg ∧ X = fold cfg)

/-- The start configuration satisfies the invariant. -/
theorem goodF_init (M' : Machine (EndAlpha T Γ) Λ) {m : ℕ}
    (e₀ : Fin (m + 3) → EndAlpha T Γ) (c₀ : Fin (m + 1) → FAlpha T Γ) :
    GoodF M' e₀ c₀ ⟨FState.setup, ⟨c₀, ⟨0, by omega⟩⟩⟩ := Or.inl rfl

/-- An accepting `GoodF` configuration yields an accepting `M'`-run from `M'`'s start on `e₀`. -/
theorem goodF_accepts (M' : Machine (EndAlpha T Γ) Λ) {m : ℕ}
    (e₀ : Fin (m + 3) → EndAlpha T Γ) (c₀ : Fin (m + 1) → FAlpha T Γ)
    {X : DLBA.Cfg (FAlpha T Γ) (FState Λ) m} (hg : GoodF M' e₀ c₀ X)
    (hacc : (flagMachine M').accept X.state = true) :
    Accepts M' ⟨M'.initial, ⟨e₀, ⟨0, by omega⟩⟩⟩ := by
  rcases hg with rfl | ⟨k, _, rfl⟩ | rfl | ⟨hs, _⟩ | rfl | ⟨k, rfl⟩ | ⟨cfg, hreach, rfl⟩
  · simp [flagMachine] at hacc
  · simp [flagMachine] at hacc
  · simp [flagMachine] at hacc
  · rw [hs] at hacc; simp [flagMachine] at hacc
  · simp [flagMachine] at hacc
  · simp [flagMachine] at hacc
  · refine ⟨cfg, hreach, ?_⟩
    rw [show (fold cfg).state = FState.sim cfg.state (foldMode cfg.tape.head) from rfl] at hacc
    rwa [flagMachine_accept_sim] at hacc

set_option maxRecDepth 4000 in
/-- The invariant is preserved by a `flagMachine` step. -/
theorem goodF_step (M' : Machine (EndAlpha T Γ) Λ) {m : ℕ}
    (e₀ : Fin (m + 3) → EndAlpha T Γ) (c₀ : Fin (m + 1) → FAlpha T Γ)
    (hbridge : foldedTape c₀ = foldContents e₀)
    (hrawL : ∀ i : Fin (m + 1), cellLeft (c₀ i) = none)
    (hrawR : ∀ i : Fin (m + 1), cellRight (c₀ i) = none)
    {X X' : DLBA.Cfg (FAlpha T Γ) (FState Λ) m}
    (hg : GoodF M' e₀ c₀ X) (hstep : Step (flagMachine M') X X') :
    GoodF M' e₀ c₀ X' := by
  rcases hg with rfl | ⟨k, hk, rfl⟩ | rfl | ⟨hvs, hvr⟩ | rfl | ⟨k, rfl⟩ | ⟨cfg, hreach, rfl⟩
  · -- `setup`: deterministic step onto the scan phase.
    obtain ⟨s, a, d, hmem, rfl⟩ := hstep
    simp only [flagMachine, flagTransition, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    by_cases hm0 : m = 0
    · subst hm0
      refine Or.inr (Or.inr (Or.inl ?_))
      apply cfg_ext'
      · rfl
      · show Function.update c₀ ⟨0, by omega⟩
          (some (Sum.inr (cellCur (c₀ ⟨0, by omega⟩), some leftMark, none))) = scanLast c₀
        funext j
        have hj0 : j = (⟨0, by omega⟩ : Fin (0 + 1)) := Fin.ext (by have := j.isLt; omega)
        subst hj0; rw [Function.update_apply, if_pos rfl]; simp [scanLast]
      · apply Fin.ext; simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write]
        rw [dif_neg (show ¬ (0 : ℕ) < 0 by omega)]
    · have hm : 1 ≤ m := by omega
      refine Or.inr (Or.inl ⟨⟨1, by omega⟩, by simp, ?_⟩)
      apply cfg_ext'
      · rfl
      · show Function.update c₀ ⟨0, by omega⟩
          (some (Sum.inr (cellCur (c₀ ⟨0, by omega⟩), some leftMark, none))) = partialTape c₀ 1
        funext j
        rw [Function.update_apply]
        by_cases hj : j = (⟨0, by omega⟩ : Fin (m + 1))
        · subst hj; rw [if_pos rfl]
          simp [partialTape, foldedTape, show ¬ (0 : ℕ) = m from by omega]
        · rw [if_neg hj]; simp only [partialTape]
          rw [if_neg (show ¬ j.val < 1 by have : j.val ≠ 0 := fun h => hj (Fin.ext h); omega)]
      · apply Fin.ext; simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write]
        rw [dif_pos (show (0 : ℕ) < m by omega)]
  · -- `scan` at cell `k` (`1 ≤ k`): continue (fold) or guess (mark `⊣`).
    obtain ⟨s, a, d, hmem, rfl⟩ := hstep
    have hrk : (partialTape c₀ k.val) k = c₀ k := by simp [partialTape]
    simp only [flagMachine, flagTransition, DLBA.BoundedTape.read, hrk, Set.mem_insert_iff,
      Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    have hklt := k.isLt
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · -- continue
      by_cases hkm : k.val < m
      · -- still interior: → `partialTape (k+1)`
        refine Or.inr (Or.inl ⟨⟨k.val + 1, by omega⟩, Nat.le_add_left 1 k.val, ?_⟩)
        apply cfg_ext'
        · rfl
        · show Function.update (partialTape c₀ k.val) k
            (some (Sum.inr (cellCur (c₀ k), cellLeft (c₀ k), none))) = partialTape c₀ (k.val + 1)
          rw [hrawL k]
          funext j; rw [Function.update_apply]
          by_cases hj : j = k
          · rw [if_pos hj, hj]; simp only [partialTape, foldedTape]
            rw [if_pos (show k.val < k.val + 1 by omega), if_neg (show ¬ k.val = 0 by omega),
              if_neg (show ¬ k.val = m by omega)]
          · rw [if_neg hj]; simp only [partialTape]
            have hjk : j.val ≠ k.val := fun h => hj (Fin.ext h)
            by_cases hjlt : j.val < k.val
            · rw [if_pos hjlt, if_pos (by omega)]
            · rw [if_neg hjlt, if_neg (by omega)]
        · apply Fin.ext
          simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, moveHead_right_head_val]
          rw [dif_pos (show k.val < m by omega)]
      · -- clamped at the last cell: → `scanLast`
        refine Or.inr (Or.inr (Or.inl ?_))
        have hkeq : k.val = m := by omega
        apply cfg_ext'
        · rfl
        · show Function.update (partialTape c₀ k.val) k
            (some (Sum.inr (cellCur (c₀ k), cellLeft (c₀ k), none))) = scanLast c₀
          rw [hrawL k]
          funext j; rw [Function.update_apply]
          by_cases hj : j = k
          · rw [if_pos hj, hj]; simp [scanLast, show ¬ k.val = 0 from by omega]
          · rw [if_neg hj]; simp only [partialTape, scanLast]
            have hjk : j.val ≠ k.val := fun h => hj (Fin.ext h)
            have hjlt : j.val < k.val := by have := j.isLt; omega
            rw [if_pos hjlt]; simp only [foldedTape]
            rw [if_neg (show ¬ j.val = m by omega)]
        · apply Fin.ext
          simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, moveHead_right_head_val]
          rw [dif_neg (show ¬ k.val < m by omega)]; exact hkeq
    · -- guess
      by_cases hkm : k.val < m
      · -- guessed too early: dead `verify` (head on a raw cell, `cellRight = none`)
        refine Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, ?_⟩)))
        have hne : (⟨k.val + 1, by omega⟩ : Fin (m + 1)) ≠ k := by
          rw [ne_eq, Fin.ext_iff]; show ¬ k.val + 1 = k.val; omega
        have hhead : ((((⟨partialTape c₀ k.val, k⟩ : DLBA.BoundedTape (FAlpha T Γ) m).write
            (some (Sum.inr (cellCur (c₀ k), cellLeft (c₀ k), some rightMark)))).moveHead
            DLBA.Dir.right).head) = (⟨k.val + 1, by omega⟩ : Fin (m + 1)) := by
          apply Fin.ext
          simp only [moveHead_right_head_val, write_head, Fin.val_mk]
          rw [if_pos (show k.val < m by omega)]
        show cellRight (((⟨partialTape c₀ k.val, k⟩ : DLBA.BoundedTape (FAlpha T Γ) m).write
            (some (Sum.inr (cellCur (c₀ k), cellLeft (c₀ k), some rightMark)))).moveHead
            DLBA.Dir.right).read = none
        rw [DLBA.BoundedTape.read, hhead]
        simp only [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]
        rw [Function.update_of_ne hne]
        simp only [partialTape]
        rw [if_neg (show ¬ (⟨k.val + 1, by omega⟩ : Fin (m + 1)).val < k.val from by
          show ¬ k.val + 1 < k.val; omega)]
        exact hrawR _
      · -- guessed at the last cell: successful `verify` on the fully folded tape
        refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
        have hkeq : k.val = m := by omega
        apply cfg_ext'
        · rfl
        · show Function.update (partialTape c₀ k.val) k
            (some (Sum.inr (cellCur (c₀ k), cellLeft (c₀ k), some rightMark))) = foldedTape c₀
          rw [hrawL k]
          funext j; rw [Function.update_apply]
          by_cases hj : j = k
          · rw [if_pos hj, hj]; simp only [foldedTape]
            rw [if_neg (show ¬ k.val = 0 by omega), if_pos hkeq]
          · rw [if_neg hj]; simp only [partialTape]
            have hjk : j.val ≠ k.val := fun h => hj (Fin.ext h)
            have hjlt : j.val < k.val := by have := j.isLt; omega
            rw [if_pos hjlt]
        · apply Fin.ext
          simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, moveHead_right_head_val]
          rw [dif_neg (show ¬ k.val < m by omega)]; exact hkeq
  · -- `scanLast`: continue (self-loop) or guess (→ `verify` good)
    obtain ⟨s, a, d, hmem, rfl⟩ := hstep
    have hrk : (scanLast c₀) ⟨m, by omega⟩ = some (Sum.inr (cellCur (c₀ ⟨m, by omega⟩),
        (if m = 0 then some leftMark else none), none)) := rfl
    simp only [flagMachine, flagTransition, DLBA.BoundedTape.read, hrk, Set.mem_insert_iff,
      Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · -- continue: stays at `scanLast`
      refine Or.inr (Or.inr (Or.inl ?_))
      apply cfg_ext'
      · rfl
      · show Function.update (scanLast c₀) ⟨m, by omega⟩
          (some (Sum.inr (cellCur (some (Sum.inr (cellCur (c₀ ⟨m, by omega⟩),
            (if m = 0 then some leftMark else none), none))),
            cellLeft (some (Sum.inr (cellCur (c₀ ⟨m, by omega⟩),
            (if m = 0 then some leftMark else none), none))), none))) = scanLast c₀
        rw [show cellCur (some (Sum.inr (cellCur (c₀ ⟨m, by omega⟩),
              (if m = 0 then some leftMark else none), none))) = cellCur (c₀ ⟨m, by omega⟩) from rfl,
            show cellLeft (some (Sum.inr (cellCur (c₀ ⟨m, by omega⟩),
              (if m = 0 then some leftMark else none), none)))
              = (if m = 0 then some leftMark else none) from rfl]
        rw [show (some (Sum.inr (cellCur (c₀ ⟨m, by omega⟩),
              (if m = 0 then some leftMark else none), none)) : FAlpha T Γ)
            = scanLast c₀ ⟨m, by omega⟩ from rfl, Function.update_eq_self]
      · apply Fin.ext
        simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, moveHead_right_head_val]
        rw [dif_neg (show ¬ m < m by omega)]
    · -- guess: commits `⊣`, reaching the fully folded tape
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
      apply cfg_ext'
      · rfl
      · show Function.update (scanLast c₀) ⟨m, by omega⟩
          (some (Sum.inr (cellCur (some (Sum.inr (cellCur (c₀ ⟨m, by omega⟩),
            (if m = 0 then some leftMark else none), none))),
            cellLeft (some (Sum.inr (cellCur (c₀ ⟨m, by omega⟩),
            (if m = 0 then some leftMark else none), none))), some rightMark))) = foldedTape c₀
        rw [show cellCur (some (Sum.inr (cellCur (c₀ ⟨m, by omega⟩),
              (if m = 0 then some leftMark else none), none))) = cellCur (c₀ ⟨m, by omega⟩) from rfl,
            show cellLeft (some (Sum.inr (cellCur (c₀ ⟨m, by omega⟩),
              (if m = 0 then some leftMark else none), none)))
              = (if m = 0 then some leftMark else none) from rfl]
        funext j; rw [Function.update_apply]
        by_cases hj : j = (⟨m, by omega⟩ : Fin (m + 1))
        · subst hj; rw [if_pos rfl]; simp [foldedTape]
        · rw [if_neg hj]; simp only [scanLast, foldedTape]
          have hjm : j.val ≠ m := fun h => hj (Fin.ext h)
          rw [if_neg hjm]
      · apply Fin.ext
        simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, moveHead_right_head_val]
        rw [dif_neg (show ¬ m < m by omega)]
  · -- dead `verify`: no successor.
    exfalso
    obtain ⟨s, a, d, hmem, rfl⟩ := hstep
    rw [hvs] at hmem
    simp only [flagMachine, flagTransition, DLBA.BoundedTape.read, hvr, Option.isSome_none,
      Bool.false_eq_true, if_false, Set.mem_empty_iff_false] at hmem
  · -- successful `verify`: → `rewind` at the last cell.
    obtain ⟨s, a, d, hmem, rfl⟩ := hstep
    have hrt : (cellRight (foldedTape c₀ ⟨m, by omega⟩)).isSome = true := by
      simp [foldedTape, cellRight]
    simp only [flagMachine, flagTransition, DLBA.BoundedTape.read, hrt, if_true,
      Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨m - 1, by omega⟩, ?_⟩)))))
    apply cfg_ext'
    · rfl
    · show Function.update (foldedTape c₀) ⟨m, by omega⟩ (foldedTape c₀ ⟨m, by omega⟩) = foldedTape c₀
      rw [Function.update_eq_self]
    · apply Fin.ext
      simp only [moveHead_left_head_val, write_head, Fin.val_mk]
      split_ifs <;> omega
  · -- `rewind` at cell `k`: continue left, or (at cell `0`) enter the simulation.
    obtain ⟨s, a, d, hmem, rfl⟩ := hstep
    by_cases hk0 : k.val = 0
    · -- found `⊢`: enter simulation at `M'.initial`, head on `⊢`.
      have hk0' : k = (⟨0, by omega⟩ : Fin (m + 1)) := Fin.ext hk0
      have hls : (cellLeft (foldedTape c₀ k)).isSome = true := by
        rw [hk0']; simp [foldedTape, cellLeft]
      simp only [flagMachine, flagTransition, DLBA.BoundedTape.read, hls, if_true,
        Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      obtain ⟨rfl, rfl, rfl⟩ := hmem
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨⟨M'.initial, ⟨e₀, ⟨0, by omega⟩⟩⟩, Relation.ReflTransGen.refl, ?_⟩)))))
      apply cfg_ext'
      · rw [show (fold ⟨M'.initial, ⟨e₀, ⟨0, by omega⟩⟩⟩ : DLBA.Cfg (FAlpha T Γ) (FState Λ) m).state
            = FState.sim M'.initial (foldMode (⟨0, by omega⟩ : Fin (m + 3))) from rfl,
            foldMode_zero rfl]
      · show Function.update (foldedTape c₀) k (foldedTape c₀ k)
          = (fold ⟨M'.initial, ⟨e₀, ⟨0, by omega⟩⟩⟩).tape.contents
        rw [Function.update_eq_self,
          show (fold ⟨M'.initial, ⟨e₀, ⟨0, by omega⟩⟩⟩).tape.contents = foldContents e₀ from rfl,
          hbridge]
      · simp only [moveHead_stay_head, write_head]
        exact hk0'
    · -- no `⊢`: keep rewinding left.
      have hls : (cellLeft (foldedTape c₀ k)).isSome = false := by
        simp only [foldedTape, cellLeft]; rw [if_neg hk0]; rfl
      simp only [flagMachine, flagTransition, DLBA.BoundedTape.read, hls, Bool.false_eq_true,
        if_false, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      obtain ⟨rfl, rfl, rfl⟩ := hmem
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨k.val - 1, by omega⟩, ?_⟩)))))
      apply cfg_ext'
      · rfl
      · show Function.update (foldedTape c₀) k (foldedTape c₀ k) = foldedTape c₀
        rw [Function.update_eq_self]
      · apply Fin.ext
        simp only [moveHead_left_head_val, write_head, Fin.val_mk]
        rw [if_pos (show 0 < k.val by omega)]
  · -- simulation phase: backward simulation gives the `M'`-step.
    obtain ⟨cfg', hstepM, rfl⟩ := sim_step_inv M' hstep
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨cfg', hreach.tail hstepM, rfl⟩)))))

/-- Every configuration reachable from the start satisfies the invariant. -/
theorem goodF_reaches (M' : Machine (EndAlpha T Γ) Λ) {m : ℕ}
    (e₀ : Fin (m + 3) → EndAlpha T Γ) (c₀ : Fin (m + 1) → FAlpha T Γ)
    (hbridge : foldedTape c₀ = foldContents e₀)
    (hrawL : ∀ i : Fin (m + 1), cellLeft (c₀ i) = none)
    (hrawR : ∀ i : Fin (m + 1), cellRight (c₀ i) = none)
    {X : DLBA.Cfg (FAlpha T Γ) (FState Λ) m}
    (h : Reaches (flagMachine M') ⟨FState.setup, ⟨c₀, ⟨0, by omega⟩⟩⟩ X) :
    GoodF M' e₀ c₀ X := by
  induction h with
  | refl => exact goodF_init M' e₀ c₀
  | tail _ hbc ih => exact goodF_step M' e₀ c₀ hbridge hrawL hrawR ih hbc

end LBA


