import Mathlib
import Langlib.Automata.Turing.Definition
import Langlib.Automata.Turing.Equivalence.TMToGrammar
import Langlib.Classes.RecursivelyEnumerable.Definition

/-! # Recursive (Decidable) Languages

This file defines the class of **recursive** (decidable) languages, characterised
by the existence of a Turing machine that *decides* the language: the machine always
halts, and it accepts exactly the words in the language.

## Main definitions

- `is_Recursive` — a language is recursive if there exists a TM₀ machine that always
  halts together with a Boolean acceptance predicate on states, such that `w ∈ L` iff
  the machine halts in a state `q` with `accept q = true`.
- `Recursive` — the class of all recursive languages.

## Main results

- `Recursive_membership_decidable` — membership in a recursive language is decidable.
- `is_Recursive_implies_is_TM` — every recursive language is TM-recognisable.
- `Recursive_subset_RE` — every recursive language is recursively enumerable.
-/

open Turing

variable {T : Type}

/-! ## Definition -/

/-- A language `L` over alphabet `T` is **recursive** (decidable) if there exists a
finite-state Turing machine (in Mathlib's `Turing.TM0` model) that **always halts**,
together with a Boolean predicate `accept` on states, such that `w ∈ L` iff the
machine halts in a state `q` with `accept q = true`.

The machine uses `Option T` as the tape alphabet (`none` = blank) and encodes the
input word `w : List T` as `w.map some` on the tape. -/
def is_Recursive {T : Type} (L : Language T) : Prop :=
  ∃ (Λ : Type) (_ : Inhabited Λ) (_ : Fintype Λ)
    (M : TM0.Machine (Option T) Λ) (accept : Λ → Bool),
    (∀ w : List T,
      (Turing.eval (TM0.step M) (TM0.init (w.map Option.some))).Dom) ∧
    (∀ w : List T,
      ∀ h : (Turing.eval (TM0.step M) (TM0.init (w.map Option.some))).Dom,
        w ∈ L ↔
          accept
            ((Turing.eval (TM0.step M) (TM0.init (w.map Option.some))).get h).q = true)

/-- The class of recursive (decidable) languages. -/
def Recursive : Set (Language T) := setOf is_Recursive

/-! ## Membership decidability -/

/-- Membership in a recursive language is decidable.

The TM that decides `L` always halts, and tells us whether `w ∈ L` via its
acceptance predicate.  Since `is_Recursive` is an existential proposition the
witness is extracted using `Classical.choice`, making this definition
`noncomputable`. -/
noncomputable def Recursive_membership_decidable
    {L : Language T} (hL : is_Recursive L) (w : List T) :
    Decidable (w ∈ L) :=
  letI := Classical.dec
  inferInstance

/-! ## Recogniser construction -/

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

/-
The recogniser's step function on a lifted config mirrors the decider's step
when the decider does not halt.
-/
lemma recognizer_step_of_decider_step
    (c c' : TM0.Cfg (Option T) Λ)
    (hs : c' ∈ TM0.step M c) :
    @TM0.step _ _ ⟨Sum.inl default⟩ _ (decider_to_recognizer M accept) (liftCfg c) =
      some (liftCfg c') := by
  unfold TM0.step at *;
  unfold decider_to_recognizer at *;
  unfold liftCfg at *;
  grind

/-
The recogniser reaches any config that the decider reaches (lifted).
-/
lemma recognizer_reaches_of_decider_reaches
    (c c' : TM0.Cfg (Option T) Λ)
    (hr : Reaches (TM0.step M) c c') :
    @Reaches _ (@TM0.step _ _ ⟨Sum.inl default⟩ _ (decider_to_recognizer M accept))
      (liftCfg c) (liftCfg c') := by
  induction hr;
  · constructor;
  · rename_i c' hc' ih;
    convert ih.tail _;
    convert recognizer_step_of_decider_step M accept _ _ hc'

/-
When the decider halts in an accepting state the recogniser also halts.
-/
lemma recognizer_halts_of_accept
    (c : TM0.Cfg (Option T) Λ)
    (hstep : TM0.step M c = none)
    (hacc : accept c.q = true) :
    @TM0.step _ _ ⟨Sum.inl default⟩ _ (decider_to_recognizer M accept) (liftCfg c) = none := by
  unfold TM0.step at *; simp_all +decide [ liftCfg ] ;
  unfold decider_to_recognizer; aesop;

/-
The recogniser never halts while in the reject-loop state `inr ()`.
-/
lemma recognizer_inr_step (tape : Tape (Option T)) :
    @TM0.step _ _ ⟨Sum.inl default⟩ _ (decider_to_recognizer M accept)
      (⟨Sum.inr (), tape⟩ : @TM0.Cfg _ (Λ ⊕ Unit) _) =
      some ⟨Sum.inr (), tape.move Dir.right⟩ := by
  unfold decider_to_recognizer TM0.step;
  grind

/-
Every configuration reachable from an `inr` state is again `inr`.
-/
lemma recognizer_inr_reaches_inr (tape : Tape (Option T))
    (c' : @TM0.Cfg (Option T) (Λ ⊕ Unit) _)
    (hr : @Reaches _ (@TM0.step _ _ ⟨Sum.inl default⟩ _ (decider_to_recognizer M accept))
      ⟨Sum.inr (), tape⟩ c') :
    c'.q = Sum.inr () := by
  induction' hr with c'' c''' h₁ h₂ ih <;> simp_all +decide [ Reaches ];
  unfold decider_to_recognizer at h₂;
  unfold TM0.step at h₂; aesop;

/-
The recogniser never terminates from the reject-loop.
-/
lemma recognizer_inr_never_halts (tape : Tape (Option T)) :
    ¬ (@Turing.eval _ (@TM0.step _ _ ⟨Sum.inl default⟩ _
      (decider_to_recognizer M accept))
      (⟨Sum.inr (), tape⟩ : @TM0.Cfg _ (Λ ⊕ Unit) _)).Dom := by
  intro h;
  obtain ⟨ c, hc ⟩ := Part.dom_iff_mem.mp h;
  rw [ Turing.mem_eval ] at hc;
  have := recognizer_inr_reaches_inr M accept tape c hc.1; simp_all +decide [ TM0.step ] ;
  unfold decider_to_recognizer at hc; aesop;

/-
When the decider halts in a rejecting state the recogniser loops forever.
-/
lemma recognizer_diverges_of_reject
    (c : TM0.Cfg (Option T) Λ)
    (w : List T)
    (hreach : Reaches (TM0.step M) (TM0.init (w.map Option.some)) c)
    (hstep : TM0.step M c = none)
    (hrej : accept c.q = false) :
    ¬ (@Turing.eval _ (@TM0.step _ _ ⟨Sum.inl default⟩ _
          (decider_to_recognizer M accept))
        (@TM0.init _ _ ⟨Sum.inl default⟩ _ (w.map Option.some))).Dom := by
  have hrecognizer_step : @TM0.step _ _ ⟨Sum.inl default⟩ _ (decider_to_recognizer M accept) (liftCfg c) = some (⟨Sum.inr (), c.Tape.move Dir.right⟩ : @TM0.Cfg _ (Λ ⊕ Unit) _) := by
    unfold decider_to_recognizer;
    unfold liftCfg;
    unfold TM0.step at *; aesop;
  -- By Lemma `recognizer_inr_never_halts`, the configuration ⟨inr (), ...⟩ never halts.
  have hrecognizer_never_halts : ¬(@Turing.eval _ (@TM0.step _ _ ⟨Sum.inl default⟩ _ (decider_to_recognizer M accept)) (⟨Sum.inr (), c.Tape.move Dir.right⟩ : @TM0.Cfg _ (Λ ⊕ Unit) _)).Dom := by
    apply recognizer_inr_never_halts;
  convert hrecognizer_never_halts using 1;
  rw [ Turing.reaches_eval ];
  exact Relation.ReflTransGen.trans ( recognizer_reaches_of_decider_reaches M accept _ _ hreach ) ( by exact Relation.ReflTransGen.single hrecognizer_step )

end RecognizerConstruction

/-! ## Recursive ⊆ TM -/

/-
Every recursive language is TM-recognisable.
-/
theorem is_Recursive_implies_is_TM
    {L : Language T} (hL : is_Recursive L) : is_TM L := by
  obtain ⟨ Λ, hΛ₁, hΛ₂, M, hM ⟩ := hL;
  refine' ⟨ Λ ⊕ Unit, _, _, _, _ ⟩;
  exact ⟨ Sum.inl hΛ₁.default ⟩;
  infer_instance;
  exact decider_to_recognizer M hM.choose;
  intro w;
  by_cases hw : w ∈ L <;> simp +decide [ hw ];
  · obtain ⟨b, hb⟩ : ∃ b, Reaches (TM0.step M) (TM0.init (w.map Option.some)) b ∧ TM0.step M b = none ∧ hM.choose b.q = true := by
      have := hM.choose_spec.1 w;
      obtain ⟨b, hb⟩ : ∃ b, b ∈ eval (TM0.step M) (TM0.init (w.map Option.some)) := by
        exact ⟨ _, Part.get_mem this ⟩;
      grind +suggestions;
    have h_recognizer_reaches : @Reaches _ (@TM0.step _ _ ⟨Sum.inl hΛ₁.default⟩ _ (decider_to_recognizer M hM.choose)) (liftCfg (TM0.init (w.map Option.some))) (liftCfg b) := by
      apply recognizer_reaches_of_decider_reaches; exact hb.left;
    have h_recognizer_halts : @TM0.step _ _ ⟨Sum.inl hΛ₁.default⟩ _ (decider_to_recognizer M hM.choose) (liftCfg b) = none := by
      exact recognizer_halts_of_accept M hM.choose b hb.2.1 hb.2.2;
    have h_recognizer_halts : @Turing.eval _ (@TM0.step _ _ ⟨Sum.inl hΛ₁.default⟩ _ (decider_to_recognizer M hM.choose)) (liftCfg (TM0.init (w.map Option.some))) ≠ Part.none := by
      rw [ Ne.eq_def, Part.eq_none_iff ];
      simp +decide [ mem_eval, h_recognizer_reaches, h_recognizer_halts ];
      exact ⟨ _, h_recognizer_reaches, h_recognizer_halts ⟩;
    convert h_recognizer_halts using 1;
    simp +decide [ Part.eq_none_iff, Part.mem_eq ];
    rfl;
  · apply recognizer_diverges_of_reject;
    rotate_right;
    exact ( Turing.eval ( TM0.step M ) ( TM0.init ( List.map some w ) ) ).get ( hM.choose_spec.1 w );
    · have := hM.choose_spec.1 w;
      have := mem_eval.mp ( Part.get_mem this );
      exact this.1;
    · have := ( Turing.eval ( TM0.step M ) ( TM0.init ( List.map some w ) ) ).get_mem ( hM.choose_spec.1 w );
      rw [ mem_eval ] at this;
      exact this.2;
    · exact Classical.not_not.1 fun h => hw <| hM.choose_spec.2 w ( hM.choose_spec.1 w ) |>.2 <| by simpa using h;

/-! ## Recursive ⊆ RE -/

/-- Every recursive language is recursively enumerable. -/
theorem is_Recursive_implies_is_RE [DecidableEq T] [Fintype T]
    {L : Language T} (hL : is_Recursive L) : is_RE L :=
  tm_recognizable_implies_re L (is_Recursive_implies_is_TM hL)

/-- The class of recursive languages is a subset of the class of RE languages. -/
theorem Recursive_subset_RE [DecidableEq T] [Fintype T] :
    (Recursive : Set (Language T)) ⊆ RE :=
  fun _ hL => is_Recursive_implies_is_RE hL