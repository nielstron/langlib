import Mathlib
import Langlib.Automata.Turing.Equivalence.TMToGrammar
import Langlib.Automata.Turing.DSL.AlphabetSim
import Langlib.Classes.Recursive.Definition
import Langlib.Classes.RecursivelyEnumerable.Definition

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

variable {Λ : Type} [Inhabited Λ]

/-- Lift a TM0 configuration from state type `Λ` to `Λ ⊕ Unit` by wrapping the
state in `Sum.inl`. -/
def liftCfg (c : TM0.Cfg (Option T) Λ) :
    @TM0.Cfg (Option T) (Λ ⊕ Unit) _ :=
  ⟨Sum.inl c.q, c.Tape⟩

/-- Construct a recogniser TM from a decider TM with acceptance predicate.
The recogniser halts iff the decider would halt in an accepting state;
when the decider rejects, the recogniser enters an infinite loop. -/
def decider_to_recognizer
    (M : TM0.Machine (Option T) Λ) (accept : Λ → Bool) :
    @TM0.Machine (Option T) (Λ ⊕ Unit) ⟨Sum.inl default⟩ :=
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

variable (M : TM0.Machine (Option T) Λ) (accept : Λ → Bool)

lemma recognizer_step_of_decider_step
    (c c' : TM0.Cfg (Option T) Λ)
    (hs : c' ∈ TM0.step M c) :
    @TM0.step _ _ ⟨Sum.inl default⟩ _ (decider_to_recognizer M accept) (liftCfg c) =
      some (liftCfg c') := by
  unfold TM0.step at *
  unfold decider_to_recognizer at *
  unfold liftCfg at *
  grind

lemma recognizer_reaches_of_decider_reaches
    (c c' : TM0.Cfg (Option T) Λ)
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

lemma recognizer_halts_of_accept
    (c : TM0.Cfg (Option T) Λ)
    (hstep : TM0.step M c = none)
    (hacc : accept c.q = true) :
    @TM0.step _ _ ⟨Sum.inl default⟩ _ (decider_to_recognizer M accept) (liftCfg c) = none := by
  unfold TM0.step at *
  simp_all +decide [liftCfg]
  unfold decider_to_recognizer
  aesop

lemma recognizer_inr_step (tape : Tape (Option T)) :
    @TM0.step _ _ ⟨Sum.inl default⟩ _ (decider_to_recognizer M accept)
      (⟨Sum.inr (), tape⟩ : @TM0.Cfg _ (Λ ⊕ Unit) _) =
      some ⟨Sum.inr (), tape.move Dir.right⟩ := by
  unfold decider_to_recognizer TM0.step
  grind

lemma recognizer_inr_reaches_inr (tape : Tape (Option T))
    (c' : @TM0.Cfg (Option T) (Λ ⊕ Unit) _)
    (hr : @Reaches _ (@TM0.step _ _ ⟨Sum.inl default⟩ _ (decider_to_recognizer M accept))
      ⟨Sum.inr (), tape⟩ c') :
    c'.q = Sum.inr () := by
  induction' hr with c'' c''' h₁ h₂ ih <;> simp_all +decide [Reaches]
  unfold decider_to_recognizer at h₂
  unfold TM0.step at h₂
  aesop

lemma recognizer_inr_never_halts (tape : Tape (Option T)) :
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

lemma recognizer_diverges_of_reject
    (c : TM0.Cfg (Option T) Λ)
    (w : List T)
    (hreach : Reaches (TM0.step M) (TM0.init (w.map Option.some)) c)
    (hstep : TM0.step M c = none)
    (hrej : accept c.q = false) :
    ¬ (@Turing.eval _ (@TM0.step _ _ ⟨Sum.inl default⟩ _
          (decider_to_recognizer M accept))
        (@TM0.init _ _ ⟨Sum.inl default⟩ _ (w.map Option.some))).Dom := by
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

/-! ### Recognizer Eval Dom Correspondence -/

/-
If the decider halts in an accepting state, the recognizer's `Turing.eval` is Dom.
-/
lemma recognizer_eval_dom_of_accept
    (w : List T)
    (hdom : (Turing.eval (TM0.step M) (TM0.init (w.map Option.some))).Dom)
    (hacc : accept ((Turing.eval (TM0.step M) (TM0.init (w.map Option.some))).get hdom).q
      = true) :
    (@Turing.eval _ (@TM0.step _ _ ⟨Sum.inl default⟩ _
      (decider_to_recognizer M accept))
      (@TM0.init _ _ ⟨Sum.inl default⟩ _ (w.map Option.some))).Dom := by
  have := Part.get_mem hdom;
  have := Turing.mem_eval.mp this;
  have := recognizer_reaches_of_decider_reaches M accept (TM0.init (List.map some w)) ((eval (TM0.step M) (TM0.init (List.map some w))).get hdom) this.1;
  have := recognizer_halts_of_accept M accept ((eval (TM0.step M) (TM0.init (List.map some w))).get hdom) (by tauto) (by tauto);
  rw [ Part.dom_iff_mem ];
  use liftCfg ((eval (TM0.step M) (TM0.init (List.map some w))).get hdom);
  convert Turing.mem_eval.mpr _;
  unfold liftCfg; aesop;

/-
If the decider halts in a rejecting state, the recognizer's `Turing.eval` is not Dom.
-/
lemma recognizer_eval_not_dom_of_reject
    (w : List T)
    (hdom : (Turing.eval (TM0.step M) (TM0.init (w.map Option.some))).Dom)
    (hrej : accept ((Turing.eval (TM0.step M) (TM0.init (w.map Option.some))).get hdom).q
      = false) :
    ¬ (@Turing.eval _ (@TM0.step _ _ ⟨Sum.inl default⟩ _
      (decider_to_recognizer M accept))
      (@TM0.init _ _ ⟨Sum.inl default⟩ _ (w.map Option.some))).Dom := by
  convert recognizer_diverges_of_reject M accept _ _ _ _ _;
  exact ( eval ( TM0.step M ) ( TM0.init ( List.map some w ) ) ).get hdom;
  · convert hdom;
    grind +suggestions;
  · grind +suggestions;
  · exact hrej

end RecognizerConstruction

/-! ### Alphabet Lifting: Option T → Option (T ⊕ Empty) -/

section AlphabetLift

/-- Embed `Option T` into `Option (T ⊕ Empty)` by mapping `some t ↦ some (Sum.inl t)`
and `none ↦ none`. -/
def optionSumEmptyEmb (T : Type) : Option T → Option (T ⊕ Empty) :=
  Option.map Sum.inl

/-- Inverse of `optionSumEmptyEmb`: map `some (Sum.inl t) ↦ some t`, `none ↦ none`.
The `Sum.inr` case is vacuous since `Empty` is uninhabited. -/
def optionSumEmptyInv (T : Type) : Option (T ⊕ Empty) → Option T :=
  fun x => match x with
  | none => none
  | some (Sum.inl t) => some t
  | some (Sum.inr e) => e.elim

lemma optionSumEmptyInv_emb (a : Option T) :
    optionSumEmptyInv T (optionSumEmptyEmb T a) = a := by
  cases a <;> simp [optionSumEmptyEmb, optionSumEmptyInv]

lemma optionSumEmptyEmb_default :
    optionSumEmptyEmb T (default : Option T) = (default : Option (T ⊕ Empty)) := by
  rfl

lemma map_option_some_map_emb (w : List T) :
    (w.map Option.some).map (optionSumEmptyEmb T) =
    w.map (fun x => some (Sum.inl x)) := by
  simp [optionSumEmptyEmb, List.map_map]

end AlphabetLift

/-! ### Connecting TM0.eval.Dom and Turing.eval.Dom -/

/-- `TM0.eval` Dom is equivalent to `Turing.eval` Dom on configs. -/
lemma tm0_eval_dom_iff_eval_dom {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ]
    (M : TM0.Machine Γ Λ) (l : List Γ) :
    (TM0.eval M l).Dom ↔ (Turing.eval (TM0.step M) (TM0.init l)).Dom := by
  simp [TM0.eval, Part.map]

/-! ### Main Theorem -/

/-
The recognizer TM over `Option T` recognizes exactly `L`: it halts iff `w ∈ L`.
-/
lemma recognizer_tm0_eval_iff {Λ : Type} [Inhabited Λ]
    (L : Language T)
    (M : TM0.Machine (Option T) Λ) (accept : Λ → Bool)
    (halts : ∀ w : List T,
      (Turing.eval (TM0.step M) (TM0.init (w.map Option.some))).Dom)
    (hmem : ∀ w : List T,
      ∀ h : (Turing.eval (TM0.step M) (TM0.init (w.map Option.some))).Dom,
        w ∈ L ↔ accept ((Turing.eval (TM0.step M)
          (TM0.init (w.map Option.some))).get h).q = true)
    (w : List T) :
    w ∈ L ↔
    (@TM0.eval _ (Λ ⊕ Unit) ⟨Sum.inl default⟩ _
      (decider_to_recognizer M accept) (w.map Option.some)).Dom := by
  -- By definition of `decider_to_recognizer`, if the original TM halts and accepts, then the recognizer also halts and accepts.
  apply Iff.intro;
  · intro hwL
    have haccept : accept ((eval (TM0.step M) (TM0.init (w.map Option.some))).get (halts w)).q = true := by
      exact hmem w ( halts w ) |>.1 hwL
    exact (recognizer_eval_dom_of_accept M accept w (halts w)) haccept;
  · contrapose!;
    intro hw;
    convert recognizer_eval_not_dom_of_reject M accept w ( halts w ) _;
    simpa [ hw ] using hmem w ( halts w )

/-- Every recursive language is TM-recognisable.

**Proof**: The decider `M` is converted to a recognizer `M_rec` over
`Option T` (via `decider_to_recognizer`). With `Γ = T` and `encode = id`,
the recognizer directly satisfies the generalized `is_TM` definition. -/
theorem is_Recursive_implies_is_TM
    [Fintype T] {L : Language T} (hL : is_Recursive L) : is_TM L := by
  obtain ⟨Λ, hΛ, hΛf, M, accept, halts, hmem⟩ := hL
  letI : Inhabited (Λ ⊕ Unit) := ⟨Sum.inl default⟩
  exact ⟨T, inferInstance, Λ ⊕ Unit, inferInstance, inferInstance,
    decider_to_recognizer M accept, id, fun w => by
    show w ∈ L ↔ (TM0.eval (decider_to_recognizer M accept) (w.map some)).Dom
    exact recognizer_tm0_eval_iff L M accept halts hmem w⟩

/-- Every recursive language is recursively enumerable. -/
theorem is_Recursive_implies_is_RE [DecidableEq T] [Fintype T]
    {L : Language T} (hL : is_Recursive L) : is_RE L :=
  tm_recognizable_implies_re L (is_Recursive_implies_is_TM hL)

/-- The class of recursive languages is a subset of the class of RE languages. -/
theorem Recursive_subset_RE [DecidableEq T] [Fintype T] :
    (Recursive : Set (Language T)) ⊆ RE :=
  fun _ hL => is_Recursive_implies_is_RE hL