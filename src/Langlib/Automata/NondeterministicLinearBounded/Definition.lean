import Mathlib
import Langlib.Automata.LinearBounded.Definition

/-!
# Nondeterministic Linear Bounded Automata

A **nondeterministic linear bounded automaton** (NLBA) is a nondeterministic Turing machine
whose read/write head is restricted to the portion of the tape containing the input.

This is a separate automaton class from deterministic LBAs. It reuses the bounded tape and
configuration types from `Langlib.Automata.LinearBounded.Definition`.
-/

namespace NLBA

/-- A nondeterministic linearly bounded automaton. -/
structure Machine (Γ : Type*) (Λ : Type*) where
  transition : Λ → Γ → Set (Λ × Γ × LBA.Dir)
  accept : Λ → Bool
  initial : Λ

/-- One step of nondeterministic computation. -/
def Step {Γ : Type*} {Λ : Type*} {n : ℕ}
    (M : Machine Γ Λ) (cfg cfg' : LBA.Cfg Γ Λ n) : Prop :=
  ∃ q' a d, (q', a, d) ∈ M.transition cfg.state cfg.tape.read ∧
    cfg' = ⟨q', (cfg.tape.write a).moveHead d⟩

/-- Multi-step reachability: the reflexive-transitive closure of `Step`. -/
def Reaches {Γ : Type*} {Λ : Type*} {n : ℕ}
    (M : Machine Γ Λ) : LBA.Cfg Γ Λ n → LBA.Cfg Γ Λ n → Prop :=
  Relation.ReflTransGen (Step M)

/-- The NLBA accepts from configuration `cfg` if some computation path reaches an accepting state. -/
def Accepts {Γ : Type*} {Λ : Type*} {n : ℕ}
    (M : Machine Γ Λ) (cfg : LBA.Cfg Γ Λ n) : Prop :=
  ∃ cfg' : LBA.Cfg Γ Λ n, Reaches M cfg cfg' ∧ M.accept cfg'.state = true

/-- Load a non-empty list onto a bounded tape. -/
noncomputable def loadList {Γ : Type*} (w : List Γ) (hw : w ≠ []) :
    LBA.BoundedTape Γ (w.length - 1) :=
  ⟨fun i => w.get ⟨i.val, by have := i.isLt; have := List.length_pos_of_ne_nil hw; omega⟩,
   ⟨0, by have := List.length_pos_of_ne_nil hw; omega⟩⟩

/-- Initial configuration for a non-empty list input. -/
noncomputable def initCfgList {Γ : Type*} {Λ : Type*}
    (M : Machine Γ Λ) (w : List Γ) (hw : w ≠ []) :
    LBA.Cfg Γ Λ (w.length - 1) :=
  ⟨M.initial, loadList w hw⟩

/-- The language recognized by an NLBA, defined on non-empty lists. -/
noncomputable def LanguageOfMachine {Γ : Type*} {Λ : Type*}
    (M : Machine Γ Λ) : Language Γ :=
  fun w => ∃ (hw : w ≠ []), Accepts M (initCfgList M w hw)

/-- Recognition via an embedding from the input alphabet into the tape alphabet. -/
noncomputable def LanguageViaEmbed {T Γ : Type*} {Λ : Type*}
    (M : Machine Γ Λ) (embed : T → Γ) : Language T :=
  fun w => ∃ (hw : w.map embed ≠ []),
    Accepts M (initCfgList M (w.map embed) hw)

end NLBA

/-- A language is `NLBA`-recognizable if it is accepted by some finite nondeterministic
linearly bounded automaton after embedding the input alphabet into the tape alphabet. -/
def is_NLBA {T : Type} (L : Language T) : Prop :=
  ∃ (Γ Λ : Type) (_ : Fintype Γ) (_ : Fintype Λ)
    (_ : DecidableEq Γ) (_ : DecidableEq Λ)
    (embed : T ↪ Γ)
    (M : NLBA.Machine Γ Λ),
    NLBA.LanguageViaEmbed M embed = L
