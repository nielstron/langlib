import Mathlib
import Langlib.Automata.Turing.DSL.SplitAtSep
import Langlib.Automata.Turing.DSL.BinaryPredecessor

/-! # Decrement-Before-Separator Machine

`incBeforeSep` decrements the block before the first `chainConsBottom`
separator. The raw predecessor machine already has the right operational
shape: it borrows through binary cells and stops on the first non-bit, so
it can stop at `chainConsBottom` without a bespoke borrow implementation.

The remaining distinction is semantic: `incBeforeSep` uses normalized
`binPred`, while the machine phase below realizes the reusable raw
predecessor component before the separator.
-/

open Turing PartrecToTM2 TM2to1

/-- The raw predecessor machine decrements the prefix before
    `chainConsBottom`, preserves the separator and the right side, and
    rewinds to the start. -/
theorem binPredRaw_before_consBottom_reaches
    (left right suffix : List ChainΓ)
    (hleft : ∀ g ∈ left, g ≠ default) :
    Reaches (TM0.step binPredRawMachine)
      (TM0.init (left ++ chainConsBottom :: right ++ default :: suffix))
      ⟨.done, Tape.mk₁ (binPredRaw left ++ chainConsBottom :: right ++ default :: suffix)⟩ := by
  simpa [TM0.init, List.append_assoc] using
    binPredRaw_borrow_until_nonbit left (right ++ default :: suffix) []
      chainConsBottom (by decide) (by decide) hleft (by simp)

theorem tm0_incBeforeSep_block : TM0RealizesBlock ChainΓ incBeforeSep := by
  sorry
