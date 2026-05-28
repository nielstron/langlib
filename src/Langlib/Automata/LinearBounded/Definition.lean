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

A **linearly bounded automaton** (LBA) is a nondeterministic Turing machine
whose read/write head is restricted to the portion of the tape containing the input.

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

end LBA

/-- A language is `LBA`-recognizable if it is accepted by some finite nondeterministic
linearly bounded automaton after embedding the input alphabet into the tape alphabet. -/
@[expose]
public def is_LBA {T : Type} (L : Language T) : Prop :=
  ∃ (Γ Λ : Type) (_ : Fintype Γ) (_ : Fintype Λ)
    (_ : DecidableEq Γ) (_ : DecidableEq Λ)
    (embed : T ↪ Γ)
    (M : LBA.Machine Γ Λ),
    LBA.LanguageViaEmbed M embed = L

@[expose]
public def LBA : Set (Language T) := setOf is_LBA
