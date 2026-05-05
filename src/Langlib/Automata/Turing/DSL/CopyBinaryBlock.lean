import Mathlib
import Langlib.Automata.Turing.DSL.ChainAlphabet
import Langlib.Automata.Turing.DSL.BlockRealizability

/-! # Copy Block with Separator — General Machine

This file defines a **general copy-with-separator machine** that copies
everything before a boundary separator, inserting a different separator
`sep2` between the original and the copy:

  `copyWithSep sep2 block = block ++ [sep2] ++ block`

## Machine Construction

The TM0 copy machine `CopyBlock.M` uses `default` as a position marker.
Since blocks never contain `default`, the marker is unambiguous.

### Algorithm

**Phase 0 (setup — non-empty blocks only):**
Scan right to the first `default` (position `n`). Shift suffix right by
one cell via cascade, creating two adjacent `default`s at positions `n`
and `n+1`. Rewind to position 0 using a three-phase left scan.

**Phase 1 (copy loop, left-to-right):**
For each source element `bᵢ`:
1. Replace `bᵢ` with `default` (marker).
2. Scan right to the 1st `default` (source–copy boundary).
3. Cross it; scan right to the 2nd `default` (copy–suffix boundary).
4. Write `bᵢ` there and shift suffix right by one (cascade).
5. Three-phase return: cross copy–suffix `default`, cross source–copy
   `default`, find marker `default`.
6. Restore `bᵢ`; advance right.
When `grab` reads `default`, the copy is complete.

**Phase 2:** Write `sep2` over the source–copy `default`.

**Phase 3:** Rewind left to the tape boundary; halt.

**Empty-block path:** Write `sep2` at position 0, shift suffix, rewind
to position 0, halt.

## Specialization

`copyBinaryWithSep` is the specialization to `ChainΓ` with
`sep2 = chainConsBottom`, used by `duplicateNormalizedPaired` for squaring.
-/

open Turing PartrecToTM2 TM2to1

/-! ### General Copy-with-Separator -/

/-- Copy a block and insert separator `sep2` between the original and the copy. -/
def copyWithSep {Γ : Type} (sep2 : Γ) (block : List Γ) : List Γ :=
  block ++ [sep2] ++ block

theorem copyWithSep_ne_default {Γ : Type} [Inhabited Γ] {sep2 : Γ}
    (hsep2 : sep2 ≠ default) (block : List Γ)
    (hblock : ∀ g ∈ block, g ≠ default) :
    ∀ g ∈ copyWithSep sep2 block, g ≠ default := by
  unfold copyWithSep
  intro g hg
  have hmem : g ∈ block ∨ g = sep2 := by
    simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hg
    tauto
  rcases hmem with hmem | rfl
  · exact hblock g hmem
  · exact hsep2

/-! ### TM0 Copy Machine -/

namespace CopyBlock

variable {Γ : Type} [Inhabited Γ] [DecidableEq Γ] [Fintype Γ]

/-- Phases that carry no alphabet value. -/
inductive NPhase where
  | start   -- initial check (empty vs non-empty block)
  | scan0   -- scan right for end of block
  | rw0a    -- Phase 0 rewind: past suffix (non-default → default)
  | rw0b    -- Phase 0 rewind: past defaults (default → non-default)
  | rw0c    -- Phase 0 rewind: past source (non-default → default)
  | grab    -- copy loop: read current cell
  | adv     -- after restore: move right to next source cell
  | wSep    -- Phase 2: just wrote sep2, start final rewind
  | rwF     -- Phase 3: final rewind (scan left)
  | done    -- halt
  | emAW    -- empty block: after writing sep2, move right
  | emCk    -- empty block: check if suffix is empty
  | emRw    -- empty block: rewind after shift
  deriving DecidableEq, Repr

instance : Fintype NPhase where
  elems := {.start, .scan0, .rw0a, .rw0b, .rw0c, .grab, .adv,
            .wSep, .rwF, .done, .emAW, .emCk, .emRw}
  complete x := by cases x <;> simp

/-- Phases that carry one alphabet value (the source char being copied,
    or a shift-cascade carry). -/
inductive C1Phase where
  | p0shW   -- Phase 0 shift write (carry = cascade value)
  | p0shM   -- Phase 0 shift move
  | markMv  -- after marking source cell (carry = source char)
  | scanR   -- scan right for 1st default
  | scanR2  -- scan right for 2nd default
  | ret1    -- return: past suffix
  | ret2    -- return: past copy
  | ret2b   -- return: past remaining source to marker
  | ret3    -- return: past remaining source to marker
  | emShW   -- empty: shift write
  | emShM   -- empty: shift move
  deriving DecidableEq, Repr

instance : Fintype C1Phase where
  elems := {.p0shW, .p0shM, .markMv, .scanR, .scanR2,
            .ret1, .ret2, .ret2b, .ret3, .emShW, .emShM}
  complete x := by cases x <;> simp

/-- Phases that carry two alphabet values (source char + cascade carry). -/
inductive C2Phase where
  | shW0  -- first shift-cascade write after inserting source char
  | shM0  -- first shift-cascade move after inserting source char
  | shW   -- shift-cascade write
  | shM   -- shift-cascade move
  deriving DecidableEq, Repr

instance : Fintype C2Phase where
  elems := {.shW0, .shM0, .shW, .shM}
  complete x := by cases x <;> simp

/-- Full state type for the copy machine. -/
abbrev CSt (Γ : Type) := (Γ × Γ × C2Phase) ⊕ (Γ × C1Phase) ⊕ NPhase

instance : Inhabited (CSt Γ) := ⟨Sum.inr (Sum.inr .start)⟩

/-- The TM0 copy machine.

Given `sep2 ≠ default`, transforms
`block ++ [default] ++ suffix` into
`(block ++ [sep2] ++ block) ++ [default] ++ suffix`. -/
noncomputable def M (sep2 : Γ) : @TM0.Machine Γ (CSt Γ) ⟨Sum.inr (Sum.inr .start)⟩ :=
  fun q a => match q with
  -- ═══════════════════════════════════════════
  --  INITIAL CHECK
  -- ═══════════════════════════════════════════
  | .inr (.inr .start) =>
      if a = default then
        -- empty block → write sep2 immediately
        some (.inr (.inr .emAW), TM0.Stmt.write sep2)
      else
        -- non-empty block → scan right
        some (.inr (.inr .scan0), TM0.Stmt.move Dir.right)
  -- ═══════════════════════════════════════════
  --  PHASE 0: SETUP (non-empty block)
  -- ═══════════════════════════════════════════
  | .inr (.inr .scan0) =>
      if a = default then
        -- end of block → start Phase 0 shift cascade
        some (.inr (.inl (default, .p0shW)), TM0.Stmt.move Dir.right)
      else
        some (.inr (.inr .scan0), TM0.Stmt.move Dir.right)
  | .inr (.inl (c, .p0shW)) =>
      if c = default ∧ a = default then
        -- cascade done (writing default over default = no-op)
        some (.inr (.inr .rw0a), TM0.Stmt.move Dir.left)
      else
        -- write carry, remember old cell value
        some (.inr (.inl (a, .p0shM)), TM0.Stmt.write c)
  | .inr (.inl (c, .p0shM)) =>
      some (.inr (.inl (c, .p0shW)), TM0.Stmt.move Dir.right)
  -- Phase 0 rewind: three-phase left scan
  | .inr (.inr .rw0a) =>
      if a = default then some (.inr (.inr .rw0b), TM0.Stmt.move Dir.left)
      else some (.inr (.inr .rw0a), TM0.Stmt.move Dir.left)
  | .inr (.inr .rw0b) =>
      if a = default then some (.inr (.inr .rw0b), TM0.Stmt.move Dir.left)
      else some (.inr (.inr .rw0c), TM0.Stmt.move Dir.left)
  | .inr (.inr .rw0c) =>
      if a = default then some (.inr (.inr .grab), TM0.Stmt.move Dir.right)
      else some (.inr (.inr .rw0c), TM0.Stmt.move Dir.left)
  -- ═══════════════════════════════════════════
  --  PHASE 1: COPY LOOP
  -- ═══════════════════════════════════════════
  | .inr (.inr .grab) =>
      if a = default then
        -- end of source → Phase 2: write sep2
        some (.inr (.inr .wSep), TM0.Stmt.write sep2)
      else
        -- mark source cell, carry its value
        some (.inr (.inl (a, .markMv)), TM0.Stmt.write default)
  | .inr (.inl (s, .markMv)) =>
      some (.inr (.inl (s, .scanR)), TM0.Stmt.move Dir.right)
  | .inr (.inl (s, .scanR)) =>
      if a = default then
        -- 1st default (source-copy boundary) → cross into copy area
        some (.inr (.inl (s, .scanR2)), TM0.Stmt.move Dir.right)
      else
        some (.inr (.inl (s, .scanR)), TM0.Stmt.move Dir.right)
  | .inr (.inl (s, .scanR2)) =>
      if a = default then
        -- 2nd default (copy-suffix boundary) → write s, start shift cascade
        some (.inl (s, default, .shM0), TM0.Stmt.write s)
      else
        some (.inr (.inl (s, .scanR2)), TM0.Stmt.move Dir.right)
  -- Shift cascade (carries source char s and cascade value c)
  | .inl (s, c, .shW0) =>
      if c = default ∧ a = default then
        -- empty suffix: start return at the padding default to the right of the copy
        some (.inr (.inl (s, .ret1)), TM0.Stmt.write default)
      else
        some (.inl (s, a, .shM), TM0.Stmt.write c)
  | .inl (s, c, .shM0) =>
      some (.inl (s, c, .shW0), TM0.Stmt.move Dir.right)
  | .inl (s, c, .shW) =>
      if c = default ∧ a = default then
        -- cascade done → start three-phase return
        some (.inr (.inl (s, .ret1)), TM0.Stmt.move Dir.left)
      else
        -- write cascade carry, remember old cell value
        some (.inl (s, a, .shM), TM0.Stmt.write c)
  | .inl (s, c, .shM) =>
      some (.inl (s, c, .shW), TM0.Stmt.move Dir.right)
  -- Three-phase return
  | .inr (.inl (s, .ret1)) =>
      if a = default then
        some (.inr (.inl (s, .ret2)), TM0.Stmt.move Dir.left)
      else
        some (.inr (.inl (s, .ret1)), TM0.Stmt.move Dir.left)
  | .inr (.inl (s, .ret2)) =>
      if a = default then
        some (.inr (.inl (s, .ret2b)), TM0.Stmt.move Dir.left)
      else
        some (.inr (.inl (s, .ret2)), TM0.Stmt.move Dir.left)
  | .inr (.inl (s, .ret2b)) =>
      if a = default then
        some (.inr (.inr .adv), TM0.Stmt.write s)
      else
        some (.inr (.inl (s, .ret2b)), TM0.Stmt.move Dir.left)
  | .inr (.inl (s, .ret3)) =>
      if a = default then
        -- found marker → restore source char and advance
        some (.inr (.inr .adv), TM0.Stmt.write s)
      else
        some (.inr (.inl (s, .ret3)), TM0.Stmt.move Dir.left)
  | .inr (.inr .adv) =>
      some (.inr (.inr .grab), TM0.Stmt.move Dir.right)
  -- ═══════════════════════════════════════════
  --  PHASE 2: INSERT SEP2
  -- ═══════════════════════════════════════════
  | .inr (.inr .wSep) =>
      -- sep2 was just written by grab; now rewind
      some (.inr (.inr .rwF), TM0.Stmt.move Dir.left)
  -- ═══════════════════════════════════════════
  --  PHASE 3: FINAL REWIND
  -- ═══════════════════════════════════════════
  | .inr (.inr .rwF) =>
      if a = default then
        some (.inr (.inr .done), TM0.Stmt.move Dir.right)
      else
        some (.inr (.inr .rwF), TM0.Stmt.move Dir.left)
  | .inr (.inr .done) => none
  -- ═══════════════════════════════════════════
  --  EMPTY BLOCK PATH
  -- ═══════════════════════════════════════════
  | .inr (.inr .emAW) =>
      -- sep2 was written at position 0; move right to check suffix
      some (.inr (.inr .emCk), TM0.Stmt.move Dir.right)
  | .inr (.inr .emCk) =>
      if a = default then
        -- empty suffix → already done, move left to position 0
        some (.inr (.inr .done), TM0.Stmt.move Dir.left)
      else
        -- non-empty suffix → shift right by 1
        some (.inr (.inl (a, .emShM)), TM0.Stmt.write default)
  | .inr (.inl (c, .emShW)) =>
      if c = default ∧ a = default then
        some (.inr (.inr .emRw), TM0.Stmt.move Dir.left)
      else
        some (.inr (.inl (a, .emShM)), TM0.Stmt.write c)
  | .inr (.inl (c, .emShM)) =>
      some (.inr (.inl (c, .emShW)), TM0.Stmt.move Dir.right)
  | .inr (.inr .emRw) =>
      if a = default then
        -- found default at position 1 → move left to position 0
        some (.inr (.inr .done), TM0.Stmt.move Dir.left)
      else
        some (.inr (.inr .emRw), TM0.Stmt.move Dir.left)

end CopyBlock

/-! ### Specialization to `ChainΓ` with `chainConsBottom` -/

/-- Copy a block and insert `chainConsBottom` between the original and the copy. -/
noncomputable def copyBinaryWithSep (block : List ChainΓ) : List ChainΓ :=
  copyWithSep chainConsBottom block

theorem copyBinaryWithSep_eq_copyWithSep :
    copyBinaryWithSep = copyWithSep (Γ := ChainΓ) chainConsBottom := by
  rfl

theorem copyBinaryWithSep_unfold (block : List ChainΓ) :
    copyBinaryWithSep block = block ++ [chainConsBottom] ++ block := by
  rfl

theorem copyBinaryWithSep_ne_default (block : List ChainΓ)
    (hblock : ∀ g ∈ block, g ≠ default) :
    ∀ g ∈ copyBinaryWithSep block, g ≠ default :=
  copyWithSep_ne_default chainConsBottom_ne_default block hblock
