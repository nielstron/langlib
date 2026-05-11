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

theorem chainBinaryRepr_no_of_ne_bits (sep : ChainΓ)
    (hsep0 : sep ≠ γ'ToChainΓ Γ'.bit0) (hsep1 : sep ≠ γ'ToChainΓ Γ'.bit1)
    (n : ℕ) :
    ∀ g ∈ chainBinaryRepr n, g ≠ sep := by
  intro g hg
  have hpos : ∀ p : PosNum, ∀ g ∈ (trPosNum p).map γ'ToChainΓ, g ≠ sep := by
    intro p
    induction p with
    | one =>
        intro g hg
        simp [trPosNum] at hg
        subst hg
        exact hsep1.symm
    | bit0 p ih =>
        intro g hg
        simp [trPosNum] at hg
        rcases hg with rfl | hg
        · exact hsep0.symm
        · exact ih g (List.mem_map.mpr hg)
    | bit1 p ih =>
        intro g hg
        simp [trPosNum] at hg
        rcases hg with rfl | hg
        · exact hsep1.symm
        · exact ih g (List.mem_map.mpr hg)
  simp only [chainBinaryRepr, trNat] at hg
  cases hn : (n : Num) with
  | zero =>
      rw [hn] at hg
      simp [trNum] at hg
  | pos p =>
      rw [hn] at hg
      exact hpos p g (by simpa [trNum] using hg)

theorem normalizeBlock_no_of_ne_bits (sep : ChainΓ)
    (hsep0 : sep ≠ γ'ToChainΓ Γ'.bit0) (hsep1 : sep ≠ γ'ToChainΓ Γ'.bit1)
    (block : List ChainΓ) :
    ∀ g ∈ normalizeBlock block, g ≠ sep := by
  unfold normalizeBlock
  exact chainBinaryRepr_no_of_ne_bits sep hsep0 hsep1 _

theorem binPredRaw_no_of_ne_bits (sep : ChainΓ)
    (hsep0 : sep ≠ γ'ToChainΓ Γ'.bit0) (hsep1 : sep ≠ γ'ToChainΓ Γ'.bit1)
    (block : List ChainΓ) (hblock : ∀ g ∈ block, g ≠ sep) :
    ∀ g ∈ binPredRaw block, g ≠ sep := by
  induction block with
  | nil =>
      simp [binPredRaw]
  | cons c rest ih =>
      intro g hg
      have hc : c ≠ sep := hblock c (by simp)
      have hrest : ∀ g ∈ rest, g ≠ sep := by
        intro g hg
        exact hblock g (List.mem_cons_of_mem c hg)
      have hbit01 : γ'ToChainΓ Γ'.bit0 ≠ γ'ToChainΓ Γ'.bit1 := by decide
      by_cases hbit0 : c = γ'ToChainΓ Γ'.bit0
      · simp [binPredRaw, hbit0, hbit01] at hg
        rcases hg with rfl | hg
        · exact hsep1.symm
        · exact ih hrest g hg
      · by_cases hbit1 : c = γ'ToChainΓ Γ'.bit1
        · simp [binPredRaw, hbit1] at hg
          rcases hg with rfl | hg
          · exact hsep0.symm
          · exact hrest g hg
        · simp [binPredRaw, hbit0, hbit1] at hg
          rcases hg with rfl | hg
          · exact hc
          · exact hrest g hg

theorem tm0_binPred_blockSep_of_ne_bits {sep : ChainΓ}
    (hsep0 : sep ≠ γ'ToChainΓ Γ'.bit0) (hsep1 : sep ≠ γ'ToChainΓ Γ'.bit1) :
    TM0RealizesBlockSep ChainΓ sep binPred := by
  rw [binPred_eq_comp]
  exact tm0RealizesBlockSep_comp
    (tm0RealizesBlockSep_comp
      (tm0_normalizeBlockSep (sep := sep) hsep0 hsep1)
      (tm0_binPredRaw_blockSep sep hsep1 hsep0)
      (fun _ _ => normalizeBlock_ne_default _)
      (fun _ _ => normalizeBlock_no_of_ne_bits sep hsep0 hsep1 _))
    (tm0_normalizeBlockSep (sep := sep) hsep0 hsep1)
    (fun block _hblock => binPredRaw_ne_default _ (normalizeBlock_ne_default block))
    (fun block _hblock =>
      binPredRaw_no_of_ne_bits sep hsep0 hsep1 _
        (normalizeBlock_no_of_ne_bits sep hsep0 hsep1 block))

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
