module

public import Langlib.Automata.DeterministicLinearBounded.Definition
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Height.Basic
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
@[expose]
public section



/-!
# Linearly Bounded Automata

A **linearly bounded automaton** (LBA) is a nondeterministic Turing machine whose read/write
head is confined to a region of the tape whose length is bounded by a *linear function of
the input length*.

The canonical model used here is the **endmarker** presentation `is_LBA`/`LBA` (below): the
input `w` is written bracketed between a left endmarker `⊢` and a right endmarker `⊣`, so the
tape is `⊢ w ⊣` (with `|w| + 2` cells). The empty word gets the genuine two-cell tape `⊢⊣`, on
which the machine runs like any other input — so the machine itself decides `ε`, with no
external flag. The head is confined to the bracketed region by the usual boundary clamping.

The tape alphabet is `EndAlpha T Γ = Option (T ⊕ Γ) ⊕ Bool`: the `Sum.inl` part is the
marker-free interior alphabet (`none` = blank, `some (Sum.inl t)` = input symbol,
`some (Sum.inr γ)` = a *work* symbol over an arbitrary finite work alphabet `Γ`), and
`Sum.inr false`/`Sum.inr true` are the endmarkers `⊢`/`⊣`. The input is written canonically, so
the recognizer cannot do hidden preprocessing. Because `Γ` is an arbitrary finite type, the
interior provides `Θ(|w|)` bits of read/write working space — genuine linear space, the standard
Kuroda/Hopcroft–Ullman LBA, for which the recognised languages are exactly the context-sensitive
ones (`CS = LBA`, see `Equivalence/EndmarkerToFlag.lean`).

The shared machine/configuration vocabulary (`Machine`, `Step`, `Reaches`, `Accepts`) and the
plain list-loading helpers (`loadList`, `initCfgList`, `LanguageViaEmbed`) live here too; they
are reused by the internal marker-free *flag* model (`Automata/LinearBounded/FlagModel.lean`),
which the `CS = LBA` development uses as a convenient intermediary and which is proved equal to
the canonical model in `Equivalence/EndmarkerTape.lean` and `Equivalence/EndmarkerToFlag.lean`.

This is a separate automaton class from deterministic DLBAs. It reuses the bounded tape and
configuration types from `Langlib.Automata.DeterministicLinearBounded.Definition`.
-/

namespace LBA

/-- A nondeterministic linearly bounded automaton. -/
public structure Machine (Γ : Type*) (Λ : Type*) where
  transition : Λ → Γ → Set (Λ × Γ × DLBA.Dir)
  accept : Λ → Bool
  initial : Λ

/-- One step of nondeterministic computation. -/
@[expose]
public def Step {Γ : Type*} {Λ : Type*} {n : ℕ}
    (M : Machine Γ Λ) (cfg cfg' : DLBA.Cfg Γ Λ n) : Prop :=
  ∃ q' a d, (q', a, d) ∈ M.transition cfg.state cfg.tape.read ∧
    cfg' = ⟨q', (cfg.tape.write a).moveHead d⟩

/-- Multi-step reachability: the reflexive-transitive closure of `Step`. -/
@[expose]
public def Reaches {Γ : Type*} {Λ : Type*} {n : ℕ}
    (M : Machine Γ Λ) : DLBA.Cfg Γ Λ n → DLBA.Cfg Γ Λ n → Prop :=
  Relation.ReflTransGen (Step M)

/-- The LBA accepts from configuration `cfg` if some computation path reaches an accepting state. -/
@[expose]
public def Accepts {Γ : Type*} {Λ : Type*} {n : ℕ}
    (M : Machine Γ Λ) (cfg : DLBA.Cfg Γ Λ n) : Prop :=
  ∃ cfg' : DLBA.Cfg Γ Λ n, Reaches M cfg cfg' ∧ M.accept cfg'.state = true

/-- Load a non-empty list onto a bounded tape. -/
@[expose]
public noncomputable def loadList {Γ : Type*} (w : List Γ) (hw : w ≠ []) :
    DLBA.BoundedTape Γ (w.length - 1) :=
  ⟨fun i => w.get ⟨i.val, by have := i.isLt; have := List.length_pos_of_ne_nil hw; omega⟩,
   ⟨0, by have := List.length_pos_of_ne_nil hw; omega⟩⟩

/-- Initial configuration for a non-empty list input. -/
@[expose]
public noncomputable def initCfgList {Γ : Type*} {Λ : Type*}
    (M : Machine Γ Λ) (w : List Γ) (hw : w ≠ []) :
    DLBA.Cfg Γ Λ (w.length - 1) :=
  ⟨M.initial, loadList w hw⟩

/-- The language recognized by an LBA, defined on non-empty lists. -/
noncomputable def LanguageOfMachine {Γ : Type*} {Λ : Type*}
    (M : Machine Γ Λ) : Language Γ :=
  fun w => ∃ (hw : w ≠ []), Accepts M (initCfgList M w hw)

/-- Recognition via an embedding from the input alphabet into the tape alphabet. -/
@[expose]
public noncomputable def LanguageViaEmbed {T Γ : Type*} {Λ : Type*}
    (M : Machine Γ Λ) (embed : T → Γ) : Language T :=
  fun w => ∃ (hw : w.map embed ≠ []),
    Accepts M (initCfgList M (w.map embed) hw)

/-! ### The canonical endmarker model

The input is bracketed `⊢ w ⊣` (`|w| + 2` cells); the empty word gets the two-cell tape `⊢⊣`,
so the machine decides `ε` itself. -/

variable {T Γ : Type*}

/-- Canonical tape alphabet of an endmarker LBA over input alphabet `T` and work alphabet `Γ`.
The `Sum.inl` part is the marker-free interior alphabet `Option (T ⊕ Γ)` (blank / input / work);
`Sum.inr false` is the left endmarker `⊢` and `Sum.inr true` the right endmarker `⊣`. -/
abbrev EndAlpha (T Γ : Type*) : Type _ := Option (T ⊕ Γ) ⊕ Bool

/-- The left endmarker `⊢`. -/
abbrev leftMark : EndAlpha T Γ := Sum.inr false

/-- The right endmarker `⊣`. -/
abbrev rightMark : EndAlpha T Γ := Sum.inr true

/-- The bracketed input tape `⊢ w ⊣`: `|w| + 2` cells, with the head at the left endmarker.
Even the empty word gets the genuine two-cell tape `⊢⊣`, so no separate empty-word flag is
needed. -/
@[expose]
public noncomputable def loadEnd (w : List T) : DLBA.BoundedTape (EndAlpha T Γ) (w.length + 1) :=
  ⟨fun k => if k.val = 0 then leftMark
            else if h : k.val - 1 < w.length then
              Sum.inl (some (Sum.inl (w.get ⟨k.val - 1, h⟩)))
            else rightMark,
   ⟨0, Nat.succ_pos _⟩⟩

/-- The initial configuration of an endmarker LBA on input `w`: start state, head on `⊢`. -/
@[expose]
public noncomputable def initCfgEnd {Λ : Type*} (M : Machine (EndAlpha T Γ) Λ) (w : List T) :
    DLBA.Cfg (EndAlpha T Γ) Λ (w.length + 1) :=
  ⟨M.initial, loadEnd w⟩

/-- The language recognized by an endmarker LBA: the input is bracketed `⊢ w ⊣` and the machine
accepts by an ordinary accepting run (it can accept `ε` by inspecting the adjacent `⊢⊣`). -/
@[expose]
public noncomputable def LanguageEnd {Λ : Type*} (M : Machine (EndAlpha T Γ) Λ) : Language T :=
  fun w => Accepts M (initCfgEnd M w)

end LBA

/-- A language over a finite alphabet `T` is **LBA**-recognizable if some finite nondeterministic
linearly bounded automaton over the canonical endmarker alphabet `Option (T ⊕ Γ) ⊕ Bool`
recognizes it with its input bracketed by endmarkers (`⊢ w ⊣`). The empty word is handled by the
machine itself (it runs on the two-cell tape `⊢⊣`), with no external accept-empty flag. -/
@[expose]
public def is_LBA {T : Type} [Fintype T] [DecidableEq T] (L : Language T) : Prop :=
  ∃ (Γ Λ : Type) (_ : Fintype Γ) (_ : Fintype Λ) (_ : DecidableEq Γ) (_ : DecidableEq Λ)
    (M : LBA.Machine (LBA.EndAlpha T Γ) Λ),
    LBA.LanguageEnd M = L

@[expose]
public def LBA {T : Type} [Fintype T] [DecidableEq T] : Set (Language T) := setOf is_LBA
