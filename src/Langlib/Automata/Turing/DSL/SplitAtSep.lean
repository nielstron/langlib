import Mathlib
import Langlib.Automata.Turing.DSL.ChainAlphabet
import Langlib.Automata.Turing.DSL.BlockRealizability
import Langlib.Automata.Turing.DSL.BinarySuccessor
import Langlib.Automata.Turing.DSL.BinaryPredecessor

/-! # Split-at-separator helpers

Definitions and lemmas about splitting a ChainΓ block at the first
`chainConsBottom` separator. These are factored out so that sub-block
machine files can import them without creating circular dependencies.
-/

open Turing PartrecToTM2 TM2to1

/-! ### splitAtConsBottom -/

/-- Split a block at the first `chainConsBottom` cell.
    Returns (prefix before sep, suffix after sep). -/
noncomputable def splitAtConsBottom : List ChainΓ → List ChainΓ × List ChainΓ
  | [] => ([], [])
  | c :: rest =>
    if c = chainConsBottom then ([], rest)
    else let (l, r) := splitAtConsBottom rest; (c :: l, r)

/-- Splitting a list with no `chainConsBottom` returns the full list and `[]`. -/
theorem splitAtConsBottom_no_sep (l : List ChainΓ)
    (h : ∀ c ∈ l, c ≠ chainConsBottom) :
    splitAtConsBottom l = (l, []) := by
  induction' l with c l ih
  · rfl
  · unfold splitAtConsBottom; aesop

/-- Splitting `chainBinaryRepr n ++ [chainConsBottom] ++ rest` yields
    `(chainBinaryRepr n, rest)`. -/
@[simp]
theorem splitAtConsBottom_binary_sep (n : ℕ) (rest : List ChainΓ) :
    splitAtConsBottom (chainBinaryRepr n ++ [chainConsBottom] ++ rest) =
      (chainBinaryRepr n, rest) := by
  have h_ind : ∀ (l : List ChainΓ), (∀ c ∈ l, c ≠ chainConsBottom) →
      splitAtConsBottom (l ++ [chainConsBottom] ++ rest) = (l, rest) := by
    intro l hl
    induction' l with c l ih
    · aesop
    · unfold splitAtConsBottom; aesop
  exact h_ind _ fun c hc => chainBinaryRepr_no_consBottom n c hc

/-- Splitting `l ++ [sep] ++ r` when l has no chainConsBottom. -/
@[simp]
theorem splitAtConsBottom_general (l r : List ChainΓ)
    (hl : ∀ c ∈ l, c ≠ chainConsBottom) :
    splitAtConsBottom (l ++ [chainConsBottom] ++ r) = (l, r) := by
  induction' l with c l ih
  · aesop
  · unfold splitAtConsBottom; aesop

/-- Left part of splitAtConsBottom has no chainConsBottom. -/
theorem splitAtConsBottom_fst_no_sep (block : List ChainΓ) :
    ∀ c ∈ (splitAtConsBottom block).1, c ≠ chainConsBottom := by
  induction block with
  | nil => simp [splitAtConsBottom]
  | cons c rest ih =>
    unfold splitAtConsBottom
    split_ifs with h
    · simp
    · intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · exact h
      · exact ih g hg

/-- Elements of splitAtConsBottom.1 come from the original block. -/
theorem splitAtConsBottom_fst_subset (block : List ChainΓ) :
    ∀ g ∈ (splitAtConsBottom block).1, g ∈ block := by
  intro g hg; induction block with
  | nil => simp [splitAtConsBottom] at hg
  | cons c rest ih =>
    simp only [splitAtConsBottom] at hg
    split_ifs at hg with h
    · simp at hg
    · simp only [List.mem_cons] at hg ⊢
      rcases hg with rfl | hg
      · left; rfl
      · right; exact ih hg

/-- Elements of splitAtConsBottom.2 come from the original block. -/
theorem splitAtConsBottom_snd_subset (block : List ChainΓ) :
    ∀ g ∈ (splitAtConsBottom block).2, g ∈ block := by
  intro g hg; induction block with
  | nil => simp [splitAtConsBottom] at hg
  | cons c rest ih =>
    simp only [splitAtConsBottom] at hg
    split_ifs at hg with h
    · exact List.mem_cons_of_mem _ hg
    · exact List.mem_cons_of_mem _ (ih hg)

/-- `binSucc` preserves the no-chainConsBottom property. -/
theorem binSucc_no_consBottom (l : List ChainΓ) (hl : ∀ c ∈ l, c ≠ chainConsBottom) :
    ∀ c ∈ binSucc l, c ≠ chainConsBottom := by
  induction' l with c l ih
  · simp [binSucc, chainConsBottom]; simp +decide
  · by_cases hc : c = γ'ToChainΓ Γ'.bit0 <;> by_cases hc' : c = γ'ToChainΓ Γ'.bit1
      <;> simp_all +decide [binSucc]

theorem binPred_no_consBottom (l : List ChainΓ) :
    ∀ c ∈ binPred l, c ≠ chainConsBottom := by
  unfold binPred
  exact chainBinaryRepr_no_consBottom _

@[simp]
theorem splitAtConsBottom_binPred_sep (left right : List ChainΓ) :
    splitAtConsBottom (binPred left ++ chainConsBottom :: right) =
      (binPred left, right) := by
  simpa using splitAtConsBottom_general (binPred left) right (binPred_no_consBottom left)

/-! ### Paired-side arithmetic around `chainConsBottom` -/

/-- Decrement the sub-block before the first `chainConsBottom` separator,
    normalizing it with `binPred`. Identity when no separator is present. -/
noncomputable def incBeforeSep (block : List ChainΓ) : List ChainΓ :=
  if chainConsBottom ∈ block then
    let (left, right) := splitAtConsBottom block
    binPred left ++ [chainConsBottom] ++ right
  else block

/-- Increment the sub-block after the first `chainConsBottom` separator using
    the existing binary successor. Identity when no separator is present. -/
noncomputable def decAfterSep (block : List ChainΓ) : List ChainΓ :=
  if chainConsBottom ∈ block then
    let (left, right) := splitAtConsBottom block
    left ++ [chainConsBottom] ++ binSucc right
  else block

/-- One paired-addition transfer step: decrement left and increment right. -/
noncomputable def incLeftDecRight (block : List ChainΓ) : List ChainΓ :=
  if chainConsBottom ∈ block then
    let (left, right) := splitAtConsBottom block
    binPred left ++ [chainConsBottom] ++ binSucc right
  else block

/-- `incLeftDecRight = decAfterSep ∘ incBeforeSep` -/
theorem incLeftDecRight_eq_comp :
    incLeftDecRight = decAfterSep ∘ incBeforeSep := by
  funext block
  simp only [Function.comp, incLeftDecRight, incBeforeSep, decAfterSep]
  by_cases h : chainConsBottom ∈ block
  · rw [if_pos h]
    rcases hsplit : splitAtConsBottom block with ⟨left, right⟩
    have hmem : chainConsBottom ∈ binPred left ++ [chainConsBottom] ++ right := by simp
    rw [if_pos h, if_pos hmem]
    simp
  · simp [h]

theorem incBeforeSep_ne_default (block : List ChainΓ)
    (hblock : ∀ g ∈ block, g ≠ default) :
    ∀ g ∈ incBeforeSep block, g ≠ default := by
  intro g hg
  simp only [incBeforeSep] at hg
  split_ifs at hg with h
  · rcases List.mem_append.mp hg with hg | hg
    · rcases List.mem_append.mp hg with hg | hg
      · exact binPred_ne_default _ (fun g hg => hblock g (splitAtConsBottom_fst_subset block g hg)) g hg
      · simp only [List.mem_singleton] at hg; subst hg; exact chainConsBottom_ne_default
    · exact hblock g (splitAtConsBottom_snd_subset block g hg)
  · exact hblock g hg

theorem decAfterSep_ne_default (block : List ChainΓ)
    (hblock : ∀ g ∈ block, g ≠ default) :
    ∀ g ∈ decAfterSep block, g ≠ default := by
  intro g hg
  simp only [decAfterSep] at hg
  split_ifs at hg with h
  · rcases List.mem_append.mp hg with hg | hg
    · rcases List.mem_append.mp hg with hg | hg
      · exact hblock g (splitAtConsBottom_fst_subset block g hg)
      · simp only [List.mem_singleton] at hg; subst hg; exact chainConsBottom_ne_default
    · exact binSucc_ne_default _ (fun g hg => hblock g (splitAtConsBottom_snd_subset block g hg)) g hg
  · exact hblock g hg

theorem incLeftDecRight_ne_default (block : List ChainΓ)
    (hblock : ∀ g ∈ block, g ≠ default) :
    ∀ g ∈ incLeftDecRight block, g ≠ default := by
  intro g hg
  simp only [incLeftDecRight] at hg
  split_ifs at hg with h
  · rcases List.mem_append.mp hg with hg | hg
    · rcases List.mem_append.mp hg with hg | hg
      · exact binPred_ne_default _ (fun g hg => hblock g (splitAtConsBottom_fst_subset block g hg)) g hg
      · simp only [List.mem_singleton] at hg; subst hg; exact chainConsBottom_ne_default
    · exact binSucc_ne_default _ (fun g hg => hblock g (splitAtConsBottom_snd_subset block g hg)) g hg
  · exact hblock g hg
