import Mathlib
import Langlib.Automata.Turing.DSL.HetFoldDecomp
import Langlib.Automata.Turing.DSL.SepPresenceMachine

/-! # Separator-presence invariant handoff

This file packages `sepPresenceMachine` in the conditional-body shape used by
the invariant while-loop combinator.  The machine scans a default-delimited
block, rewinds to the start, and halts in one of two states:

* `SepPresenceSt.done true` when `chainConsBottom` occurs in the block;
* `SepPresenceSt.done false` otherwise.

The tape is unchanged in both cases.  This is the small "establisher" layer
needed before handing control to bodies that are only correct under a paired
separator invariant.
-/

open Turing PartrecToTM2 TM2to1

/-- Predicate recognized by `sepPresenceMachine`. -/
def sepPresent (block : List ChainΓ) : Prop :=
  chainConsBottom ∈ block

noncomputable instance sepPresent_decidablePred : DecidablePred sepPresent :=
  fun block => inferInstanceAs (Decidable (chainConsBottom ∈ block))

/-- Separator presence as a conditional invariant-establisher body.

When the separator is present, the body halts at `q_cont`; otherwise it halts
at a different state and leaves the block unchanged. -/
theorem tm0_hasConsBottom_blockCondInv :
    TM0RealizesBlockCondInv (Γ := ChainΓ) (fun block => block)
      sepPresent (fun _block => True) := by
  refine ⟨SepPresenceSt, inferInstance, inferInstance, sepPresenceMachine,
    SepPresenceSt.done true, ?_⟩
  intro block _hInv hblock _hstep_nd
  obtain ⟨hdom, hspec⟩ := sepPresenceMachine_correct block [] hblock (by simp)
  refine ⟨?_, ?_⟩
  · simpa using hdom
  · intro h
    have h' : (TM0Seq.evalCfg sepPresenceMachine (block ++ default :: [])).Dom := by
      simpa using h
    have hout := hspec h'
    have hcfg :
        (TM0Seq.evalCfg sepPresenceMachine (block ++ [default])).get h =
          (TM0Seq.evalCfg sepPresenceMachine (block ++ default :: [])).get h' := by
      apply Part.get_eq_get_of_eq
      simp
    unfold sepPresent
    by_cases hsep : chainConsBottom ∈ block
    · simp [hsep, hcfg, hout.1, hout.2.1 hsep]
    · have hfalse := hout.2.2 hsep
      simp [hsep, hcfg, hout.1, hfalse]
