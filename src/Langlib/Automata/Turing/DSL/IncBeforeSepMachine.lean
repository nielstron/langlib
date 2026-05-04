import Mathlib
import Langlib.Automata.Turing.DSL.SplitAtSep
import Langlib.Automata.Turing.DSL.BinaryArithmeticSep
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

/-- `normalizeBlock` cannot introduce the paired-block separator. -/
theorem normalizeBlock_no_consBottom (block : List ChainΓ) :
    ∀ g ∈ normalizeBlock block, g ≠ chainConsBottom := by
  unfold normalizeBlock
  exact chainBinaryRepr_no_consBottom _

/-- `binPredRaw` only writes binary cells, so it cannot introduce the
    paired-block separator when the input block has no such separator. -/
theorem binPredRaw_no_consBottom (block : List ChainΓ)
    (hblock : ∀ g ∈ block, g ≠ chainConsBottom) :
    ∀ g ∈ binPredRaw block, g ≠ chainConsBottom := by
  induction block with
  | nil => simp [binPredRaw]
  | cons c rest ih =>
      have hrest : ∀ g ∈ rest, g ≠ chainConsBottom := by
        intro g hg
        exact hblock g (List.mem_cons_of_mem c hg)
      have hbit0 : γ'ToChainΓ Γ'.bit0 ≠ chainConsBottom := by decide
      have hbit1 : γ'ToChainΓ Γ'.bit1 ≠ chainConsBottom := by decide
      have hbit01 : γ'ToChainΓ Γ'.bit0 ≠ γ'ToChainΓ Γ'.bit1 := by decide
      by_cases hc0 : c = γ'ToChainΓ Γ'.bit0
      · intro g hg
        simp [binPredRaw, hc0, hbit01] at hg
        rcases hg with rfl | hg
        · exact hbit1
        · exact ih hrest g hg
      · by_cases hc1 : c = γ'ToChainΓ Γ'.bit1
        · intro g hg
          simp [binPredRaw, hc1] at hg
          rcases hg with rfl | hg
          · exact hbit0
          · exact hrest g hg
        · intro g hg
          simp [binPredRaw, hc0, hc1] at hg
          rcases hg with rfl | hg
          · exact hblock _ (by simp)
          · exact hrest g hg

/-- The normalized binary predecessor is realizable before the paired-block
    separator by composing the separator-aware normalization machines around
    the raw predecessor machine. -/
theorem tm0_binPred_blockSep_consBottom :
    TM0RealizesBlockSep ChainΓ chainConsBottom binPred := by
  rw [binPred_eq_comp]
  exact tm0RealizesBlockSep_comp
    (tm0RealizesBlockSep_comp
      (tm0_normalizeBlockSep (sep := chainConsBottom) (by decide) (by decide))
      (tm0_binPredRaw_blockSep chainConsBottom (by decide) (by decide))
      (fun _ _ => normalizeBlock_ne_default _)
      (fun _ _ => normalizeBlock_no_consBottom _))
    (tm0_normalizeBlockSep (sep := chainConsBottom) (by decide) (by decide))
    (fun block _hblock => binPredRaw_ne_default _ (normalizeBlock_ne_default block))
    (fun block _hblock => binPredRaw_no_consBottom _ (normalizeBlock_no_consBottom block))

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

/-- On a known paired block, `incBeforeSep` reduces to `binPred` before
    `chainConsBottom`. The total `incBeforeSep` function also specifies
    identity behavior when the separator is absent; that extra scan/identity
    wrapper is intentionally not part of this theorem. -/
theorem tm0_incBeforeSep_present_blockSep :
    TM0RealizesBlockSep ChainΓ chainConsBottom binPred :=
  tm0_binPred_blockSep_consBottom
