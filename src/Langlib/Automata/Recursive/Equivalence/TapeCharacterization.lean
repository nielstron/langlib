module

public import Langlib.Automata.Recursive.Basic.TapeCharacterization
public import Langlib.Classes.Recursive.Definition
import Mathlib.Tactic
@[expose]
public section

/-! # Tape-symbol acceptance equals state acceptance

This file proves that the tape-acceptance characterization `is_Recursive_byTape`
(defined in `Automata.Recursive.Basic.TapeCharacterization`) agrees with the
state-based `is_Recursive`: `is_Recursive_byTape L → is_Recursive L`.

The forward direction is the useful one — it lets a construction that produces the
decision *on the tape* (which is what the `Code → TM` translation chain exposes) be
repackaged into the state-based `is_Recursive`.

## Construction

Given a machine `M` that halts with the answer under the head, `readerMachine M
acceptSym` runs `M`; the instant `M` would halt it instead reads the current symbol
`γ` and moves to the distinguished halting state `Sum.inr (decide (γ = acceptSym))`,
which records the verdict. The acceptance predicate just reads that Boolean off the
state.
-/

open Turing Relation

namespace AcceptByTape

variable {Γ : Type} [Inhabited Γ] [DecidableEq Γ] {Λ : Type} [Inhabited Λ]

/-- Lift a TM0 configuration to the reader's state space `Λ ⊕ Bool`. -/
@[expose]
public def liftCfg (c : TM0.Cfg Γ Λ) : @TM0.Cfg Γ (Λ ⊕ Bool) _ :=
  ⟨Sum.inl c.q, c.Tape⟩

/-- Turn a machine that signals acceptance by leaving `acceptSym` under the head into
one that signals acceptance by its final state. When `M` would halt, the reader reads
the current symbol and halts in state `Sum.inr b` where `b` records whether the symbol
was `acceptSym`. -/
@[expose]
public def readerMachine (M : TM0.Machine Γ Λ) (acceptSym : Γ) :
    @TM0.Machine Γ (Λ ⊕ Bool) ⟨Sum.inl default⟩ :=
  fun q γ =>
    match q with
    | Sum.inl q =>
      match M q γ with
      | some (q', stmt) => some (Sum.inl q', stmt)
      | none => some (Sum.inr (decide (γ = acceptSym)), TM0.Stmt.write γ)
    | Sum.inr _ => none

/-- The state-based acceptance predicate of the reader. -/
@[expose]
public def readerAccept : Λ ⊕ Bool → Bool
  | Sum.inl _ => false
  | Sum.inr b => b

variable (M : TM0.Machine Γ Λ) (acceptSym : Γ)

public lemma reader_step_of_step (c c' : TM0.Cfg Γ Λ) (hs : c' ∈ TM0.step M c) :
    @TM0.step _ _ ⟨Sum.inl default⟩ _ (readerMachine M acceptSym) (liftCfg c) =
      some (liftCfg c') := by
  unfold TM0.step at *
  unfold readerMachine liftCfg at *
  grind

public lemma reader_reaches_of_reaches (c c' : TM0.Cfg Γ Λ)
    (hr : Reaches (TM0.step M) c c') :
    @Reaches _ (@TM0.step _ _ ⟨Sum.inl default⟩ _ (readerMachine M acceptSym))
      (liftCfg c) (liftCfg c') := by
  induction hr with
  | refl => constructor
  | tail =>
      rename_i c' hc' ih
      exact ih.tail (by
        convert reader_step_of_step M acceptSym _ _ hc')

public lemma reader_halt_step (c : TM0.Cfg Γ Λ) (hstep : TM0.step M c = none) :
    @TM0.step _ _ ⟨Sum.inl default⟩ _ (readerMachine M acceptSym) (liftCfg c) =
      some ⟨Sum.inr (decide (c.Tape.head = acceptSym)), c.Tape.write c.Tape.head⟩ := by
  unfold TM0.step at *
  unfold readerMachine liftCfg
  simp_all

public lemma reader_inr_step (b : Bool) (tape : Tape Γ) :
    @TM0.step _ _ ⟨Sum.inl default⟩ _ (readerMachine M acceptSym)
      (⟨Sum.inr b, tape⟩ : @TM0.Cfg _ (Λ ⊕ Bool) _) = none := by
  unfold readerMachine TM0.step
  grind

/-- The reader halts whenever `M` does, and its final state records whether the
symbol under the head at `M`'s halting configuration was `acceptSym`. -/
public lemma reader_eval (l : List Γ)
    (hdom : (Turing.eval (TM0.step M) (TM0.init l)).Dom) :
    (@Turing.eval _ (@TM0.step _ _ ⟨Sum.inl default⟩ _ (readerMachine M acceptSym))
      (@TM0.init _ _ ⟨Sum.inl default⟩ _ l)).Dom ∧
    ∀ h : (@Turing.eval _ (@TM0.step _ _ ⟨Sum.inl default⟩ _ (readerMachine M acceptSym))
      (@TM0.init _ _ ⟨Sum.inl default⟩ _ l)).Dom,
      ((@Turing.eval _ (@TM0.step _ _ ⟨Sum.inl default⟩ _ (readerMachine M acceptSym))
        (@TM0.init _ _ ⟨Sum.inl default⟩ _ l)).get h).q =
        Sum.inr (decide (((Turing.eval (TM0.step M) (TM0.init l)).get hdom).Tape.head =
          acceptSym)) := by
  set cM := (Turing.eval (TM0.step M) (TM0.init l)).get hdom with hcM
  have hmem := Part.get_mem hdom
  have heval := Turing.mem_eval.mp hmem
  -- The reader reaches `liftCfg cM`, then steps once to the verdict state and halts.
  have hreach := reader_reaches_of_reaches M acceptSym (TM0.init l) cM heval.1
  have hstepHalt := reader_halt_step M acceptSym cM heval.2
  set b := decide (cM.Tape.head = acceptSym) with hb
  set finalCfg : @TM0.Cfg _ (Λ ⊕ Bool) _ :=
    ⟨Sum.inr b, cM.Tape.write cM.Tape.head⟩ with hfinal
  have hreach' :
      @Reaches _ (@TM0.step _ _ ⟨Sum.inl default⟩ _ (readerMachine M acceptSym))
        (@TM0.init _ _ ⟨Sum.inl default⟩ _ l) finalCfg := by
    refine hreach.tail ?_
    have : liftCfg (Γ := Γ) (Λ := Λ) (TM0.init l) = (@TM0.init _ _ ⟨Sum.inl default⟩ _ l) := by
      rfl
    rw [this] at hreach
    exact hstepHalt
  have hhalt : @TM0.step _ _ ⟨Sum.inl default⟩ _ (readerMachine M acceptSym) finalCfg = none :=
    reader_inr_step M acceptSym b _
  have hmem' : finalCfg ∈ @Turing.eval _ (@TM0.step _ _ ⟨Sum.inl default⟩ _
      (readerMachine M acceptSym)) (@TM0.init _ _ ⟨Sum.inl default⟩ _ l) := by
    rw [Turing.mem_eval]; exact ⟨hreach', hhalt⟩
  refine ⟨Part.dom_iff_mem.mpr ⟨finalCfg, hmem'⟩, fun h => ?_⟩
  have := Part.mem_unique (Part.get_mem h) hmem'
  rw [this]

end AcceptByTape

/-! ## The two conventions agree -/

variable {T : Type}

/-- **Tape acceptance implies state acceptance:** every `is_Recursive_byTape` language is
`is_Recursive`. -/
public theorem is_Recursive_of_byTape {L : Language T} (h : is_Recursive_byTape L) :
    is_Recursive L := by
  classical
  obtain ⟨Γ, hΓf, hΓd, Λ, hΛi, hΛf, M, acceptSym, hHalt, hCorrect⟩ := h
  refine ⟨Γ, hΓf, Λ ⊕ Bool, ⟨Sum.inl default⟩, inferInstance,
    AcceptByTape.readerMachine M acceptSym, AcceptByTape.readerAccept, ?_, ?_⟩
  · intro w
    exact (AcceptByTape.reader_eval M acceptSym _ (hHalt w)).1
  · intro w h
    obtain ⟨_, hq⟩ := AcceptByTape.reader_eval M acceptSym
      (w.map fun t => some (Sum.inl t)) (hHalt w)
    rw [hq h]
    simp only [AcceptByTape.readerAccept, decide_eq_true_eq]
    rw [hCorrect w (hHalt w)]
