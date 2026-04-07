import Mathlib
import Langlib.Automata.DeterministicLinearBounded.Definition

/-!
# Linearly Bounded Automata

A **linearly bounded automaton** (LBA) is a nondeterministic Turing machine
whose read/write head is restricted to the portion of the tape containing the input.

This is a separate automaton class from deterministic DLBAs. It reuses the bounded tape and
configuration types from `Langlib.Automata.DeterministicLinearBounded.Definition`.
-/

namespace LBA

/-- A nondeterministic linearly bounded automaton. -/
structure Machine (Γ : Type*) (Λ : Type*) where
  transition : Λ → Γ → Set (Λ × Γ × DLBA.Dir)
  accept : Λ → Bool
  initial : Λ

/-- One step of nondeterministic computation. -/
def Step {Γ : Type*} {Λ : Type*} {n : ℕ}
    (M : Machine Γ Λ) (cfg cfg' : DLBA.Cfg Γ Λ n) : Prop :=
  ∃ q' a d, (q', a, d) ∈ M.transition cfg.state cfg.tape.read ∧
    cfg' = ⟨q', (cfg.tape.write a).moveHead d⟩

/-- Multi-step reachability: the reflexive-transitive closure of `Step`. -/
def Reaches {Γ : Type*} {Λ : Type*} {n : ℕ}
    (M : Machine Γ Λ) : DLBA.Cfg Γ Λ n → DLBA.Cfg Γ Λ n → Prop :=
  Relation.ReflTransGen (Step M)

/-- The LBA accepts from configuration `cfg` if some computation path reaches an accepting state. -/
def Accepts {Γ : Type*} {Λ : Type*} {n : ℕ}
    (M : Machine Γ Λ) (cfg : DLBA.Cfg Γ Λ n) : Prop :=
  ∃ cfg' : DLBA.Cfg Γ Λ n, Reaches M cfg cfg' ∧ M.accept cfg'.state = true

/-- Load a non-empty list onto a bounded tape. -/
noncomputable def loadList {Γ : Type*} (w : List Γ) (hw : w ≠ []) :
    DLBA.BoundedTape Γ (w.length - 1) :=
  ⟨fun i => w.get ⟨i.val, by have := i.isLt; have := List.length_pos_of_ne_nil hw; omega⟩,
   ⟨0, by have := List.length_pos_of_ne_nil hw; omega⟩⟩

/-- Initial configuration for a non-empty list input. -/
noncomputable def initCfgList {Γ : Type*} {Λ : Type*}
    (M : Machine Γ Λ) (w : List Γ) (hw : w ≠ []) :
    DLBA.Cfg Γ Λ (w.length - 1) :=
  ⟨M.initial, loadList w hw⟩

/-- The language recognized by an LBA, defined on non-empty lists. -/
noncomputable def LanguageOfMachine {Γ : Type*} {Λ : Type*}
    (M : Machine Γ Λ) : Language Γ :=
  fun w => ∃ (hw : w ≠ []), Accepts M (initCfgList M w hw)

/-- Recognition via an embedding from the input alphabet into the tape alphabet. -/
noncomputable def LanguageViaEmbed {T Γ : Type*} {Λ : Type*}
    (M : Machine Γ Λ) (embed : T → Γ) : Language T :=
  fun w => ∃ (hw : w.map embed ≠ []),
    Accepts M (initCfgList M (w.map embed) hw)

end LBA

/-- A language is `LBA`-recognizable if it is accepted by some finite nondeterministic
linearly bounded automaton after embedding the input alphabet into the tape alphabet. -/
def is_LBA {T : Type} (L : Language T) : Prop :=
  ∃ (Γ Λ : Type) (_ : Fintype Γ) (_ : Fintype Λ)
    (_ : DecidableEq Γ) (_ : DecidableEq Λ)
    (embed : T ↪ Γ)
    (M : LBA.Machine Γ Λ),
    LBA.LanguageViaEmbed M embed = L

def LBA : Set (Language T) := setOf is_LBA
