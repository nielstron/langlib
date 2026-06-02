module

public import Langlib.Automata.LinearBounded.Definition
import Mathlib.Tactic
@[expose]
public section

/-!
# Endmarker linear bounded automata

This file gives the **endmarker** presentation of a linear bounded automaton, which decides the
empty word with the machine itself rather than via an external `acceptEmpty` flag.

The input `w` is written bracketed between a left endmarker `⊢` and a right endmarker `⊣`, so the
tape is `⊢ w ⊣` and has `|w| + 2` cells. In particular the empty word has the genuine two-cell
tape `⊢⊣`, on which the machine runs like any other input — it accepts `ε` exactly when its
transitions accept with the two markers adjacent. The head is confined to the bracketed region by
the usual boundary clamping.

The canonical tape alphabet is `Option (T ⊕ Γ) ⊕ Bool`: the `Sum.inl` part is the marker-free
interior alphabet (`none` = blank, `inl t` = input, `inr γ` = work over a finite work alphabet
`Γ`), and `Sum.inr false`/`Sum.inr true` are the two endmarkers. As in the marker-free model the
input is written canonically, so the recognizer cannot do hidden preprocessing.

`is_LBA_end` is shown equal to the marker-free class `is_LBA` in
`Equivalence/EndmarkerTape.lean`.
-/

namespace LBA

variable {T Γ : Type*} {Λ : Type*}

/-- Canonical tape alphabet of an endmarker LBA over input alphabet `T` and work alphabet `Γ`.
The `Sum.inl` part is the marker-free interior alphabet `Option (T ⊕ Γ)` (blank / input / work);
`Sum.inr false` is the left endmarker `⊢` and `Sum.inr true` the right endmarker `⊣`. -/
abbrev EndAlpha (T Γ : Type*) : Type _ := Option (T ⊕ Γ) ⊕ Bool

/-- The left endmarker `⊢`. -/
abbrev leftMark : EndAlpha T Γ := Sum.inr false

/-- The right endmarker `⊣`. -/
abbrev rightMark : EndAlpha T Γ := Sum.inr true

/-- The bracketed input tape `⊢ w ⊣` for an endmarker LBA: `|w| + 2` cells, with the head at the
left endmarker. Even the empty word gets the genuine two-cell tape `⊢⊣`, so no separate
empty-word flag is needed. -/
@[expose]
public noncomputable def loadEnd (w : List T) : DLBA.BoundedTape (EndAlpha T Γ) (w.length + 1) :=
  ⟨fun k => if k.val = 0 then leftMark
            else if h : k.val - 1 < w.length then
              Sum.inl (some (Sum.inl (w.get ⟨k.val - 1, h⟩)))
            else rightMark,
   ⟨0, Nat.succ_pos _⟩⟩

/-- The initial configuration of an endmarker LBA on input `w`: start state, head on `⊢`. -/
@[expose]
public noncomputable def initCfgEnd (M : Machine (EndAlpha T Γ) Λ) (w : List T) :
    DLBA.Cfg (EndAlpha T Γ) Λ (w.length + 1) :=
  ⟨M.initial, loadEnd w⟩

/-- The language recognized by an endmarker LBA: the input is bracketed `⊢ w ⊣` and the machine
accepts by an ordinary accepting run (it can accept `ε` by inspecting the adjacent `⊢⊣`). -/
@[expose]
public noncomputable def LanguageEnd (M : Machine (EndAlpha T Γ) Λ) : Language T :=
  fun w => Accepts M (initCfgEnd M w)

end LBA

/-- A language over a finite alphabet `T` is **endmarker-LBA**-recognizable if some finite
nondeterministic LBA over the canonical endmarker alphabet `Option (T ⊕ Γ) ⊕ Bool` recognizes it
with its input bracketed by endmarkers. The empty word is handled by the machine itself (it runs
on the two-cell tape `⊢⊣`), with no external accept-empty flag. -/
@[expose]
public def is_LBA_end {T : Type} [Fintype T] [DecidableEq T] (L : Language T) : Prop :=
  ∃ (Γ Λ : Type) (_ : Fintype Γ) (_ : Fintype Λ) (_ : DecidableEq Γ) (_ : DecidableEq Λ)
    (M : LBA.Machine (LBA.EndAlpha T Γ) Λ),
    LBA.LanguageEnd M = L

@[expose]
public def LBA_end {T : Type} [Fintype T] [DecidableEq T] : Set (Language T) := setOf is_LBA_end
