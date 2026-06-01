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

We adopt the same tape convention as the Turing-machine and recursive-language definitions
(`Langlib.Automata.Recursive`, `is_Recursive`): the tape alphabet is `Option (T ⊕ Γ)`, where
`none` is the blank, `some (Sum.inl t)` is an input symbol, and `some (Sum.inr γ)` is a
*work* symbol drawn from an arbitrary finite work alphabet `Γ`. The input `w : List T` is
written canonically as `w.map (fun t => some (Sum.inl t))` — there is no opaque embedding of
the input alphabet that could hide computation.

The head is confined to exactly the `|w|` input cells, but those cells may be freely
overwritten with work symbols `some (Sum.inr γ)`. Because `Γ` is an arbitrary finite type,
this provides `|w| · log|Γ| = Θ(|w|)` bits of read/write working space — i.e. genuine linear
space (a constant number of "tracks"). This is the standard Kuroda/Hopcroft–Ullman LBA model,
for which the recognised languages are exactly the context-sensitive languages.

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

/-- Recognition with an explicit decision for the empty word.

The bounded tape requires at least one cell, so an LBA cannot run on the empty
input the way a Turing machine can.  We therefore pair the machine with a Boolean
`acceptEmpty` that decides membership of `ε` directly.  This mirrors the standard
context-sensitive-grammar convention, where the optional distinguished rule `S → ε`
decides membership of `ε` independently of the (non-contracting) core of the grammar.

On non-empty words this coincides with `LanguageViaEmbed`. -/
@[expose]
public noncomputable def LanguageRecognized {T Γ : Type*} {Λ : Type*}
    (M : Machine Γ Λ) (embed : T → Γ) (acceptEmpty : Bool) : Language T :=
  fun w => (acceptEmpty = true ∧ w = []) ∨ LanguageViaEmbed M embed w

end LBA

/-- A language over a finite alphabet `T` is `LBA`-recognizable if it is accepted by some
finite nondeterministic linearly bounded automaton over the tape alphabet `Option (T ⊕ Γ)`
(for an arbitrary finite work alphabet `Γ`), with the input written canonically via
`some ∘ Sum.inl`, together with an explicit decision `acceptEmpty` for the empty word.

Using the fixed canonical input map `some ∘ Sum.inl` (rather than an arbitrary embedding
`T ↪ Γ`) ensures the recognizer cannot do hidden preprocessing of the input; the only
working power is the finite work alphabet `Γ`, which supplies linear working space.

The `acceptEmpty` flag plays exactly the role of the optional `S → ε` rule in the
definition of a context-sensitive grammar: it decides membership of `ε` and is otherwise
irrelevant to the (genuinely space-bounded) computation on non-empty inputs.  Without it
no LBA language could contain `ε`, whereas `{ε}` is context-sensitive — so the flag is
exactly what is needed for `CS = LBA` to hold. -/
@[expose]
public def is_LBA {T : Type} [Fintype T] [DecidableEq T] (L : Language T) : Prop :=
  ∃ (Γ Λ : Type) (_ : Fintype Γ) (_ : Fintype Λ)
    (_ : DecidableEq Γ) (_ : DecidableEq Λ)
    (acceptEmpty : Bool)
    (M : LBA.Machine (Option (T ⊕ Γ)) Λ),
    LBA.LanguageRecognized M (fun t => some (Sum.inl t)) acceptEmpty = L

@[expose]
public def LBA [Fintype T] [DecidableEq T] : Set (Language T) := setOf is_LBA
