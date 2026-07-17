module

public import Langlib.Automata.LinearBounded.AcyclicClock.Initialization
public import Langlib.Automata.LinearBounded.AcyclicClock.EffectiveClock
import Mathlib.Tactic

@[expose]
public section

/-!
# Soundness of the canonical initialization protocol

`Initialization` constructs the complete rightward conversion sweep and leftward cleanup sweep
from the raw target input to the canonical zero-clock Ready configuration.  This file proves the
converse structural fact needed for language reflection: every computation from that raw input
which reaches any Ready configuration passes through exactly that canonical checkpoint.

The proof stops transitions at their first Ready source.  The initialization protocol is
deterministic before that boundary, so its explicitly constructed sweep is the unique stopped
path.  Finally, strict Ready-to-Ready clock growth rules out an earlier Ready configuration on the
constructed zero-clock path.
-/

open Classical Relation

namespace LBA.AcyclicClock

variable {T Γ Λ : Type*}
variable [Fintype T] [Fintype Γ] [Fintype Λ]

set_option maxHeartbeats 1000000 in
private theorem initialization_transition_right_unique_of_not_ready
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    (state : State Λ) (symbol : TapeAlpha T Γ Λ)
    (hstate : ¬state.IsReady)
    {left right : State Λ × TapeAlpha T Γ Λ × DLBA.Dir}
    (hleft : left ∈ transition M state symbol)
    (hright : right ∈ transition M state symbol) :
    left = right := by
  letI : Nonempty Λ := ⟨M.initial⟩
  rcases symbol with (inner | boundary)
  · rcases inner with (_ | tagged)
    · cases state <;> simp_all [transition]
    · rcases tagged with (input | cell)
      · cases state <;> simp_all [transition]
      · by_cases hready : state.IsReady
        · exact (hstate hready).elim
        · cases state <;> simp_all [State.IsReady, transition] <;>
            repeat' first
              | split at hleft
              | split at hright <;>
            simp_all
  · cases boundary <;> cases state <;> simp_all [transition]

/-- Every non-Ready source configuration has at most one compiled-machine successor. -/
private theorem initialization_nonready_step_right_unique
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ}
    {source left right : DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n}
    (hsource : ¬source.state.IsReady)
    (hleft : LBA.Step (machine M) source left)
    (hright : LBA.Step (machine M) source right) :
    left = right := by
  rcases hleft with ⟨leftState, leftWritten, leftDirection, hleftMem, rfl⟩
  rcases hright with
    ⟨rightState, rightWritten, rightDirection, hrightMem, rfl⟩
  have htriple :
      (leftState, leftWritten, leftDirection) =
        (rightState, rightWritten, rightDirection) :=
    initialization_transition_right_unique_of_not_ready M source.state
      source.tape.read hsource hleftMem hrightMem
  cases htriple
  rfl

/-- The compiled transition relation, stopped as soon as a Ready source is reached. -/
private def InitializationBeforeReadyStep
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ}
    (source target : DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n) : Prop :=
  LBA.Step (machine M) source target ∧ ¬source.state.IsReady

private theorem initializationBeforeReadyStep_rightUnique
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} :
    Relator.RightUnique
      (InitializationBeforeReadyStep M :
        DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n →
          DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n → Prop) := by
  intro source left right hleft hright
  exact initialization_nonready_step_right_unique M hleft.2 hleft.1 hright.1

private theorem reflTransGen_tail_of_rightUnique_head
    {A : Type*} {relation : A → A → Prop}
    (hunique : Relator.RightUnique relation)
    {start next finish : A}
    (hstep : relation start next)
    (hpath : ReflTransGen relation start finish)
    (hterminal : ∀ after, ¬relation finish after) :
    ReflTransGen relation next finish := by
  rcases hpath.cases_head with heq | ⟨middle, hfirst, hrest⟩
  · subst finish
    exact (hterminal next hstep).elim
  · have hnext : next = middle := hunique hstep hfirst
    simpa [hnext] using hrest

private theorem reflTransGen_terminal_unique_of_rightUnique
    {A : Type*} {relation : A → A → Prop}
    (hunique : Relator.RightUnique relation)
    {start left right : A}
    (hleft : ReflTransGen relation start left)
    (hright : ReflTransGen relation start right)
    (hleftTerminal : ∀ after, ¬relation left after)
    (hrightTerminal : ∀ after, ¬relation right after) :
    left = right := by
  refine ReflTransGen.head_induction_on
    (motive := fun source hpath =>
      ∀ {right}, ReflTransGen relation source right →
        (∀ after, ¬relation left after) →
        (∀ after, ¬relation right after) → left = right)
    hleft ?_ ?_ hright hleftTerminal hrightTerminal
  · intro right hright hleftTerminal _
    rcases hright.cases_head with heq | ⟨middle, hfirst, _⟩
    · exact heq
    · exact (hleftTerminal middle hfirst).elim
  · intro source middle hfirst hrest ih right hright
      hleftTerminal hrightTerminal
    have htail : ReflTransGen relation middle right :=
      reflTransGen_tail_of_rightUnique_head hunique hfirst hright
        hrightTerminal
    exact ih htail hleftTerminal hrightTerminal

/-- Any path ending in Ready factors at its first Ready configuration. -/
private theorem reaches_factor_first_ready
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ}
    {source target : DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n}
    (hpath : LBA.Reaches (machine M) source target)
    (htarget : target.state.IsReady) :
    ∃ first,
      ReflTransGen (InitializationBeforeReadyStep M) source first ∧
        first.state.IsReady ∧
        LBA.Reaches (machine M) first target := by
  refine ReflTransGen.head_induction_on
    (motive := fun source hpath =>
      target.state.IsReady →
        ∃ first,
          ReflTransGen (InitializationBeforeReadyStep M) source first ∧
            first.state.IsReady ∧
            LBA.Reaches (machine M) first target)
    hpath ?_ ?_ htarget
  · intro htarget
    exact ⟨target, .refl, htarget, .refl⟩
  · intro source middle hfirst hrest ih htarget
    by_cases hsource : source.state.IsReady
    · exact ⟨source, .refl, hsource, ReflTransGen.head hfirst hrest⟩
    · obtain ⟨first, hprefix, hfirstReady, hsuffix⟩ := ih htarget
      exact
        ⟨first, ReflTransGen.head ⟨hfirst, hsource⟩ hprefix,
          hfirstReady, hsuffix⟩

/-- Every Ready-reaching computation from a canonical target input passes through the exact
zero-clock canonical source-initial checkpoint. -/
public theorem reaches_from_canonicalCfg_of_reaches_ready_init
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    (input : List T)
    {target :
      DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) (input.length + 1)}
    (hreach : LBA.Reaches (machine M)
      (LBA.initCfgEnd (machine M) input) target)
    (htarget : target.state.IsReady) :
    LBA.Reaches (machine M)
      (canonicalCfg M (LBA.initCfgEnd M input)) target := by
  let canonical := canonicalCfg M (LBA.initCfgEnd M input)
  have hcanonicalReady : canonical.state.IsReady := by
    change (State.ready M.initial).IsReady
    trivial

  obtain ⟨constructedFirst, hconstructedPrefix, hconstructedReady,
      hconstructedSuffix⟩ :=
    reaches_factor_first_ready M (reaches_canonicalCfg_init M input)
      hcanonicalReady
  have hconstructedFirst : constructedFirst = canonical := by
    rcases reflTransGen_iff_eq_or_transGen.mp hconstructedSuffix with
      heq | hstrict
    · exact heq.symm
    · have hgrowth := ready_transGen_clockValue_lt M hconstructedReady
          hcanonicalReady hstrict
      have hzero : clockValue M canonical.tape = 0 := by
        change clockValue M
          (canonicalTape M (LBA.initCfgEnd M input).tape) = 0
        exact clockValue_canonicalTape M _
      rw [hzero] at hgrowth
      exact (Nat.not_lt_zero _ hgrowth).elim
  subst constructedFirst

  obtain ⟨first, hfirstPrefix, hfirstReady, hfirstSuffix⟩ :=
    reaches_factor_first_ready M hreach htarget
  have hcanonicalTerminal :
      ∀ after, ¬InitializationBeforeReadyStep M canonical after := by
    intro after hstep
    exact hstep.2 hcanonicalReady
  have hfirstTerminal :
      ∀ after, ¬InitializationBeforeReadyStep M first after := by
    intro after hstep
    exact hstep.2 hfirstReady
  have hfirstEq : canonical = first :=
    reflTransGen_terminal_unique_of_rightUnique
      (initializationBeforeReadyStep_rightUnique M)
      hconstructedPrefix hfirstPrefix hcanonicalTerminal hfirstTerminal
  subst first
  exact hfirstSuffix

end LBA.AcyclicClock

end
