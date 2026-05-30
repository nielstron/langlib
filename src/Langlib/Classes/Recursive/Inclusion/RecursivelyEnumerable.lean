module

public import Langlib.Classes.Recursive.Definition
public import Langlib.Classes.RecursivelyEnumerable.Definition
public import Langlib.Automata.Turing.Definition
import Langlib.Automata.Turing.Equivalence.TMToGrammar
import Mathlib.Tactic
@[expose]
public section



/-! # Recursive Inclusions

This file proves that recursive languages are Turing-recognisable and hence
recursively enumerable.

## Main results

- `is_Recursive_implies_is_TM` — every recursive language is TM-recognisable.
- `is_Recursive_implies_is_RE` — every recursive language is recursively enumerable.
- `Recursive_subset_RE` — the class of recursive languages is contained in `RE`.
-/

open Turing

variable {T : Type}

section RecognizerConstruction

variable {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ]

/-- Lift a TM0 configuration from state type `Λ` to `Λ ⊕ Unit` by wrapping the
state in `Sum.inl`. -/
@[expose]
public def liftCfg (c : TM0.Cfg Γ Λ) :
    @TM0.Cfg Γ (Λ ⊕ Unit) _ :=
  ⟨Sum.inl c.q, c.Tape⟩

/-- Construct a recogniser TM from a decider TM with acceptance predicate.
The recogniser halts iff the decider would halt in an accepting state;
when the decider rejects, the recogniser enters an infinite loop. -/
@[expose]
public def decider_to_recognizer
    (M : TM0.Machine Γ Λ) (accept : Λ → Bool) :
    @TM0.Machine Γ (Λ ⊕ Unit) ⟨Sum.inl default⟩ :=
  fun q γ =>
    match q with
    | Sum.inl q =>
      match M q γ with
      | some (q', stmt) => some (Sum.inl q', stmt)
      | none =>
        if accept q then none
        else some (Sum.inr (), TM0.Stmt.move Dir.right)
    | Sum.inr () =>
      some (Sum.inr (), TM0.Stmt.move Dir.right)

variable (M : TM0.Machine Γ Λ) (accept : Λ → Bool)

public lemma recognizer_step_of_decider_step
    (c c' : TM0.Cfg Γ Λ)
    (hs : c' ∈ TM0.step M c) :
    @TM0.step _ _ ⟨Sum.inl default⟩ _ (decider_to_recognizer M accept) (liftCfg c) =
      some (liftCfg c') := by
  unfold TM0.step at *
  unfold decider_to_recognizer at *
  unfold liftCfg at *
  grind

public lemma recognizer_reaches_of_decider_reaches
    (c c' : TM0.Cfg Γ Λ)
    (hr : Reaches (TM0.step M) c c') :
    @Reaches _ (@TM0.step _ _ ⟨Sum.inl default⟩ _ (decider_to_recognizer M accept))
      (liftCfg c) (liftCfg c') := by
  induction hr with
  | refl =>
      constructor
  | tail =>
      rename_i c' hc' ih
      convert ih.tail _
      convert recognizer_step_of_decider_step M accept _ _ hc'

public lemma recognizer_halts_of_accept
    (c : TM0.Cfg Γ Λ)
    (hstep : TM0.step M c = none)
    (hacc : accept c.q = true) :
    @TM0.step _ _ ⟨Sum.inl default⟩ _ (decider_to_recognizer M accept) (liftCfg c) = none := by
  unfold TM0.step at *
  simp_all +decide [liftCfg]
  unfold decider_to_recognizer
  aesop

private lemma recognizer_inr_step (tape : Tape Γ) :
    @TM0.step _ _ ⟨Sum.inl default⟩ _ (decider_to_recognizer M accept)
      (⟨Sum.inr (), tape⟩ : @TM0.Cfg _ (Λ ⊕ Unit) _) =
      some ⟨Sum.inr (), tape.move Dir.right⟩ := by
  unfold decider_to_recognizer TM0.step
  grind

public lemma recognizer_inr_reaches_inr (tape : Tape Γ)
    (c' : @TM0.Cfg Γ (Λ ⊕ Unit) _)
    (hr : @Reaches _ (@TM0.step _ _ ⟨Sum.inl default⟩ _ (decider_to_recognizer M accept))
      ⟨Sum.inr (), tape⟩ c') :
    c'.q = Sum.inr () := by
  induction' hr with c'' c''' h₁ h₂ ih <;> simp_all +decide
  unfold decider_to_recognizer at h₂
  unfold TM0.step at h₂
  aesop

public lemma recognizer_inr_never_halts (tape : Tape Γ) :
    ¬ (@Turing.eval _ (@TM0.step _ _ ⟨Sum.inl default⟩ _
      (decider_to_recognizer M accept))
      (⟨Sum.inr (), tape⟩ : @TM0.Cfg _ (Λ ⊕ Unit) _)).Dom := by
  intro h
  obtain ⟨c, hc⟩ := Part.dom_iff_mem.mp h
  rw [Turing.mem_eval] at hc
  have := recognizer_inr_reaches_inr M accept tape c hc.1
  simp_all +decide [TM0.step]
  unfold decider_to_recognizer at hc
  aesop

public lemma recognizer_diverges_of_reject
    (c : TM0.Cfg Γ Λ)
    (l : List Γ)
    (hreach : Reaches (TM0.step M) (TM0.init l) c)
    (hstep : TM0.step M c = none)
    (hrej : accept c.q = false) :
    ¬ (@Turing.eval _ (@TM0.step _ _ ⟨Sum.inl default⟩ _
          (decider_to_recognizer M accept))
        (@TM0.init _ _ ⟨Sum.inl default⟩ _ l)).Dom := by
  have hrecognizer_step :
      @TM0.step _ _ ⟨Sum.inl default⟩ _ (decider_to_recognizer M accept) (liftCfg c) =
        some (⟨Sum.inr (), c.Tape.move Dir.right⟩ : @TM0.Cfg _ (Λ ⊕ Unit) _) := by
    unfold decider_to_recognizer
    unfold liftCfg
    unfold TM0.step at *
    aesop
  have hrecognizer_never_halts :
      ¬ (@Turing.eval _ (@TM0.step _ _ ⟨Sum.inl default⟩ _ (decider_to_recognizer M accept))
        (⟨Sum.inr (), c.Tape.move Dir.right⟩ : @TM0.Cfg _ (Λ ⊕ Unit) _)).Dom := by
    apply recognizer_inr_never_halts
  convert hrecognizer_never_halts using 1
  rw [Turing.reaches_eval]
  exact Relation.ReflTransGen.trans
    (recognizer_reaches_of_decider_reaches M accept _ _ hreach)
    (by exact Relation.ReflTransGen.single hrecognizer_step)

public lemma recognizer_eval_dom_of_accept
    (l : List Γ)
    (hdom : (Turing.eval (TM0.step M) (TM0.init l)).Dom)
    (hacc : accept ((Turing.eval (TM0.step M) (TM0.init l)).get hdom).q = true) :
    (@Turing.eval _ (@TM0.step _ _ ⟨Sum.inl default⟩ _
      (decider_to_recognizer M accept))
      (@TM0.init _ _ ⟨Sum.inl default⟩ _ l)).Dom := by
  have hmem := Part.get_mem hdom
  have heval := Turing.mem_eval.mp hmem
  have hreach := recognizer_reaches_of_decider_reaches M accept
    (TM0.init l) ((eval (TM0.step M) (TM0.init l)).get hdom) heval.1
  have hhalt := recognizer_halts_of_accept M accept
    ((eval (TM0.step M) (TM0.init l)).get hdom) heval.2 hacc
  rw [Part.dom_iff_mem]
  use liftCfg ((eval (TM0.step M) (TM0.init l)).get hdom)
  rw [Turing.mem_eval]
  exact ⟨hreach, hhalt⟩

public lemma recognizer_eval_not_dom_of_reject
    (l : List Γ)
    (hdom : (Turing.eval (TM0.step M) (TM0.init l)).Dom)
    (hrej : accept ((Turing.eval (TM0.step M) (TM0.init l)).get hdom).q = false) :
    ¬ (@Turing.eval _ (@TM0.step _ _ ⟨Sum.inl default⟩ _
      (decider_to_recognizer M accept))
      (@TM0.init _ _ ⟨Sum.inl default⟩ _ l)).Dom := by
  exact recognizer_diverges_of_reject M accept
    ((eval (TM0.step M) (TM0.init l)).get hdom) l
    (Turing.mem_eval.mp (Part.get_mem hdom)).1
    (Turing.mem_eval.mp (Part.get_mem hdom)).2
    hrej

public lemma recognizer_tm0_eval_iff
    (L : Language T)
    (input : List T → List Γ)
    (M : TM0.Machine Γ Λ) (accept : Λ → Bool)
    (halts : ∀ w : List T,
      (Turing.eval (TM0.step M) (TM0.init (input w))).Dom)
    (hmem : ∀ w : List T,
      ∀ h : (Turing.eval (TM0.step M) (TM0.init (input w))).Dom,
        w ∈ L ↔ accept ((Turing.eval (TM0.step M)
          (TM0.init (input w))).get h).q = true)
    (w : List T) :
    w ∈ L ↔
    (@TM0.eval _ (Λ ⊕ Unit) ⟨Sum.inl default⟩ _
      (decider_to_recognizer M accept) (input w)).Dom := by
  constructor
  · intro hwL
    have haccept : accept ((eval (TM0.step M) (TM0.init (input w))).get (halts w)).q = true :=
      (hmem w (halts w)).1 hwL
    exact recognizer_eval_dom_of_accept M accept (input w) (halts w) haccept
  · contrapose!
    intro hw
    convert recognizer_eval_not_dom_of_reject M accept (input w) (halts w) _
    simpa [hw] using hmem w (halts w)

end RecognizerConstruction

public theorem is_Recursive_implies_is_TM
    [Fintype T] {L : Language T} (hL : is_Recursive L) : is_TM L := by
  obtain ⟨Γ, hΓf, Λ, hΛ, hΛf, M, accept, halts, hmem⟩ := hL
  refine ⟨Γ, hΓf, Λ ⊕ Unit, ⟨Sum.inl default⟩, inferInstance,
    decider_to_recognizer M accept, ?_⟩
  exact recognizer_tm0_eval_iff L (fun w : List T => w.map fun t => some (Sum.inl t))
    M accept halts hmem

/-- Every recursive language is recursively enumerable. -/
public theorem is_Recursive_implies_is_RE [DecidableEq T] [Fintype T]
    {L : Language T} (hL : is_Recursive L) : is_RE L :=
  tm_recognizable_implies_re L (is_Recursive_implies_is_TM hL)

/-- The class of recursive languages is a subset of the class of RE languages. -/
public theorem Recursive_subset_RE [DecidableEq T] [Fintype T] :
    (Recursive : Set (Language T)) ⊆ RE :=
  fun _ hL => is_Recursive_implies_is_RE hL
