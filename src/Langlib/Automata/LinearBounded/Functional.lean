module

public import Langlib.Automata.DeterministicLinearBounded.Inclusion.LinearBounded
import Mathlib.Tactic

@[expose]
public section

/-!
# Functional linearly bounded automata

This file proves the restricted deterministic converse for an LBA whose local transition
relation is already single-valued.  Such a machine can be viewed as a DLBA: halt immediately
upon reaching an accepting state, and otherwise follow its unique transition when one exists.

This isolates the acceptance-convention difference between `LBA` and `DLBA`; it does **not**
determinize a genuinely nondeterministic LBA and therefore does not resolve the open
`LBA = DLBA` problem.

## Main results

* `LBA.Machine.Functional` — every state/symbol pair has at most one transition.
* `LBA.Machine.toDLBA` — the corresponding deterministic machine.
* `LBA.Machine.accepts_toDLBA_iff` — acceptance equivalence on every bounded configuration.
* `LBA.Machine.languageEnd_toDLBA_eq` — equality on canonical endmarker inputs.
* `LBA.Machine.languageRecognized_toDLBA_eq` — equality of the recognized languages,
  including the same explicit empty-word bit.
* `DLBA.toLBA'_functional` — the existing embedding of a DLBA into an LBA is functional.
* `is_DLBA_languageRecognized_of_functional` — the class-facing restricted converse.
* `is_DLBA_iff_exists_functional_lba` — exact characterization by finite functional
  marker-free LBA presentations.
-/

namespace LBA

variable {Γ Λ : Type*}

/-- An LBA is functional when every state/symbol pair has at most one outgoing move. -/
public def Machine.Functional (M : Machine Γ Λ) : Prop :=
  ∀ q a, (M.transition q a).Subsingleton

/-- View a functional LBA as a DLBA.

The deterministic machine halts immediately in an accepting state.  At a nonaccepting state it
takes the unique LBA transition, if one exists, and otherwise halts rejecting. -/
public noncomputable def Machine.toDLBA (M : Machine Γ Λ) : DLBA.Machine Γ Λ := by
  classical
  exact {
    transition := fun q a =>
      if M.accept q = true then none
      else if h : ∃ move, move ∈ M.transition q a then some (Classical.choose h)
      else none
    accept := M.accept
    initial := M.initial }

@[simp]
theorem Machine.toDLBA_accept (M : Machine Γ Λ) (q : Λ) :
    M.toDLBA.accept q = M.accept q := rfl

@[simp]
theorem Machine.toDLBA_initial (M : Machine Γ Λ) :
    M.toDLBA.initial = M.initial := rfl

private theorem Machine.toDLBA_step_none_of_accept
    (M : Machine Γ Λ) {n : ℕ} (cfg : DLBA.Cfg Γ Λ n)
    (hacc : M.accept cfg.state = true) :
    DLBA.step M.toDLBA cfg = none := by
  simp [DLBA.step, Machine.toDLBA, hacc]

private theorem Machine.toDLBA_step_of_step
    (M : Machine Γ Λ) (hfun : M.Functional) {n : ℕ}
    {cfg cfg' : DLBA.Cfg Γ Λ n}
    (hacc : M.accept cfg.state ≠ true) (hstep : Step M cfg cfg') :
    DLBA.step M.toDLBA cfg = some cfg' := by
  rcases hstep with ⟨q', a, d, hmem, rfl⟩
  let hex : ∃ move, move ∈ M.transition cfg.state (cfg.tape.contents cfg.tape.head) :=
    ⟨(q', a, d), hmem⟩
  have hchoice : Classical.choose hex = (q', a, d) :=
    hfun cfg.state (cfg.tape.contents cfg.tape.head) (Classical.choose_spec hex) hmem
  have haccfalse : M.accept cfg.state = false := Bool.eq_false_of_not_eq_true hacc
  simp [DLBA.step, Machine.toDLBA, haccfalse, hex, hchoice]

private theorem Machine.step_of_toDLBA_step
    (M : Machine Γ Λ) {n : ℕ} {cfg cfg' : DLBA.Cfg Γ Λ n}
    (hstep : DLBA.step M.toDLBA cfg = some cfg') :
    Step M cfg cfg' := by
  cases htrans : M.toDLBA.transition cfg.state cfg.tape.read with
  | none =>
      unfold DLBA.step at hstep
      change M.toDLBA.transition cfg.state cfg.tape.read = none at htrans
      rw [htrans] at hstep
      simp at hstep
  | some move =>
      rcases move with ⟨q', a, d⟩
      unfold DLBA.step at hstep
      change M.toDLBA.transition cfg.state cfg.tape.read = some (q', a, d) at htrans
      rw [htrans] at hstep
      simp only [Option.some.injEq] at hstep
      subst cfg'
      have htrans' := htrans
      simp only [Machine.toDLBA] at htrans'
      split at htrans'
      · simp at htrans'
      · split at htrans'
        · next hex =>
            simp only [Option.some.injEq] at htrans'
            have hmem : (q', a, d) ∈ M.transition cfg.state cfg.tape.read := by
              rw [← htrans']
              exact Classical.choose_spec hex
            exact ⟨q', a, d, hmem, rfl⟩
        · simp at htrans'

private theorem Machine.reaches_of_toDLBA_iterateStep
    (M : Machine Γ Λ) {n k : ℕ} {cfg cfg' : DLBA.Cfg Γ Λ n}
    (hiter : DLBA.iterateStep M.toDLBA cfg k = some cfg') :
    Reaches M cfg cfg' := by
  induction k generalizing cfg cfg' with
  | zero =>
      simp only [DLBA.iterateStep] at hiter
      cases hiter
      exact .refl
  | succ k ih =>
      rw [DLBA.iterateStep_succ] at hiter
      obtain ⟨middle, hmiddle, hlast⟩ := Option.bind_eq_some_iff.mp hiter
      exact (ih hmiddle).tail (M.step_of_toDLBA_step hlast)

private theorem Machine.reaches_toDLBA_dichotomy
    (M : Machine Γ Λ) (hfun : M.Functional) {n : ℕ}
    {cfg cfg' : DLBA.Cfg Γ Λ n} (hreach : Reaches M cfg cfg') :
    DLBA.Accepts M.toDLBA cfg ∨
      ∃ k, DLBA.iterateStep M.toDLBA cfg k = some cfg' := by
  induction hreach with
  | refl => exact Or.inr ⟨0, rfl⟩
  | @tail middle target hreach hstep ih =>
      rcases ih with haccepted | ⟨k, hk⟩
      · exact Or.inl haccepted
      · by_cases hacc : M.accept middle.state = true
        · exact Or.inl ⟨k, by
            rw [DLBA.iterateStep_succ, hk]
            exact M.toDLBA_step_none_of_accept middle hacc,
            middle, hk, hacc⟩
        · exact Or.inr ⟨k + 1, by
            rw [DLBA.iterateStep_succ, hk]
            exact M.toDLBA_step_of_step hfun hacc hstep⟩

/-- A functional LBA and its canonical deterministic presentation accept exactly the same
bounded configurations. -/
public theorem Machine.accepts_toDLBA_iff
    (M : Machine Γ Λ) (hfun : M.Functional) {n : ℕ}
    (cfg : DLBA.Cfg Γ Λ n) :
    DLBA.Accepts M.toDLBA cfg ↔ Accepts M cfg := by
  constructor
  · rintro ⟨k, _, cfg', hk, hacc⟩
    exact ⟨cfg', M.reaches_of_toDLBA_iterateStep hk, hacc⟩
  · rintro ⟨cfg', hreach, hacc⟩
    rcases M.reaches_toDLBA_dichotomy hfun hreach with haccepted | ⟨k, hk⟩
    · exact haccepted
    · exact ⟨k, by
        rw [DLBA.iterateStep_succ, hk]
        exact M.toDLBA_step_none_of_accept cfg' hacc,
        cfg', hk, hacc⟩

/-- Converting a functional LBA to a DLBA preserves its language on nonempty embedded inputs. -/
public theorem Machine.languageViaEmbed_toDLBA_eq
    {T : Type*} (M : Machine Γ Λ) (hfun : M.Functional) (embed : T → Γ) :
    DLBA.LanguageViaEmbed M.toDLBA embed = LBA.LanguageViaEmbed M embed := by
  funext w
  apply propext
  constructor
  · rintro ⟨hne, hacc⟩
    exact ⟨hne, (M.accepts_toDLBA_iff hfun _).mp hacc⟩
  · rintro ⟨hne, hacc⟩
    exact ⟨hne, (M.accepts_toDLBA_iff hfun _).mpr hacc⟩

/-- Converting a functional LBA to a DLBA preserves the recognized language when both
presentations use the same explicit decision for the empty word. -/
public theorem Machine.languageRecognized_toDLBA_eq
    {T : Type*} (M : Machine Γ Λ) (hfun : M.Functional) (embed : T → Γ)
    (acceptEmpty : Bool) :
    DLBA.LanguageRecognized M.toDLBA embed acceptEmpty =
      LBA.LanguageRecognized M embed acceptEmpty := by
  funext w
  apply propext
  simp only [DLBA.LanguageRecognized, LBA.LanguageRecognized]
  rw [M.languageViaEmbed_toDLBA_eq hfun embed]

/-- Converting a functional canonical endmarker LBA to a DLBA preserves its language on
the actual bracketed inputs `⊢ w ⊣`, including the empty word. -/
public theorem Machine.languageEnd_toDLBA_eq
    {T : Type*} (M : Machine (EndAlpha T Γ) Λ) (hfun : M.Functional) :
    (fun w : List T => DLBA.Accepts M.toDLBA (initCfgEnd M w)) = LanguageEnd M := by
  funext w
  apply propext
  exact M.accepts_toDLBA_iff hfun (initCfgEnd M w)

end LBA

namespace DLBA

/-- The existing embedding of a DLBA into an LBA has single-valued transitions. -/
public theorem toLBA'_functional {Γ Λ : Type*} [DecidableEq Γ]
    (M : DLBA.Machine Γ Λ) :
    (DLBA.toLBA' M).Functional := by
  intro q a x hx y hy
  cases q with
  | none => simp [DLBA.toLBA'] at hx
  | some q =>
      cases htrans : M.transition q a with
      | none =>
          by_cases hacc : M.accept q = true
          · simp [DLBA.toLBA', htrans, hacc] at hx hy
            exact hx.trans hy.symm
          · have hfalse : M.accept q = false := Bool.eq_false_of_not_eq_true hacc
            simp [DLBA.toLBA', htrans, hfalse] at hx
      | some move =>
          simp [DLBA.toLBA', htrans] at hx hy
          exact hx.trans hy.symm

end DLBA

variable {T Γ Λ : Type}
  [Fintype T] [DecidableEq T]
  [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]

/-- A finite functional marker-free LBA over the canonical tape alphabet, together with an
explicit empty-word decision, presents a deterministic-LBA language. -/
public theorem is_DLBA_languageRecognized_of_functional
    (M : LBA.Machine (Option (T ⊕ Γ)) Λ)
    (hfun : M.Functional) (acceptEmpty : Bool) :
    is_DLBA (LBA.LanguageRecognized M (fun t => some (Sum.inl t)) acceptEmpty) := by
  refine ⟨Γ, Λ, inferInstance, inferInstance, inferInstance, inferInstance,
    acceptEmpty, M.toDLBA, ?_⟩
  exact M.languageRecognized_toDLBA_eq hfun _ acceptEmpty

/-- A language is recognized by a DLBA exactly when it has a presentation by a finite
functional marker-free LBA, with the same explicit decision for the empty word. -/
public theorem is_DLBA_iff_exists_functional_lba (L : Language T) :
    is_DLBA L ↔
      ∃ (Γ' Λ' : Type) (_ : Fintype Γ') (_ : Fintype Λ')
        (_ : DecidableEq Γ') (_ : DecidableEq Λ')
        (acceptEmpty : Bool)
        (M : LBA.Machine (Option (T ⊕ Γ')) Λ'),
        M.Functional ∧
          LBA.LanguageRecognized M (fun t => some (Sum.inl t)) acceptEmpty = L := by
  constructor
  · rintro ⟨Γ', Λ', hΓ', hΛ', hdecΓ', hdecΛ', acceptEmpty, M, hM⟩
    letI := hΓ'
    letI := hΛ'
    letI := hdecΓ'
    letI := hdecΛ'
    refine ⟨Γ', Option Λ', inferInstance, inferInstance, inferInstance, inferInstance,
      acceptEmpty, DLBA.toLBA' M, DLBA.toLBA'_functional M, ?_⟩
    rw [← hM]
    have key :
        DLBA.LanguageViaEmbed M (fun t => some (Sum.inl t)) =
          LBA.LanguageViaEmbed (DLBA.toLBA' M) (fun t => some (Sum.inl t)) :=
      dlba_language_eq_lba_language M (fun t => some (Sum.inl t))
    funext w
    apply propext
    simp only [LBA.LanguageRecognized, DLBA.LanguageRecognized, key]
  · rintro ⟨Γ', Λ', hΓ', hΛ', hdecΓ', hdecΛ', acceptEmpty, M, hfun, hM⟩
    letI := hΓ'
    letI := hΛ'
    letI := hdecΓ'
    letI := hdecΛ'
    rw [← hM]
    exact is_DLBA_languageRecognized_of_functional M hfun acceptEmpty
