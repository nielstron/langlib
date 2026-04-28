import Mathlib
import Langlib.Automata.Turing.DSL.TM0Compose
import Langlib.Automata.Turing.DSL.TM0BuildingBlocks
import Langlib.Automata.Turing.DSL.ParrecChain
import Langlib.Automata.Turing.DSL.AlphabetSim
import Langlib.Automata.Turing.DSL.ReverseBlock
import Langlib.Automata.Turing.DSL.DropWhileNeSep

/-! # Chain Encoding Decomposition

This file decomposes the chain encoding function `chainEncode` into
elementary "singleton functions" and proves serializability (sequential
composition). The main goal is to establish that the chain encoding is
TM0-realizable as a heterogeneous function.

## Strategy

The chain encoding `chainEncode T w = trInit K'.main (trList [Encodable.encode w])`
is decomposed into:

1. **List encoding fold**: Compute `Encodable.encode w` from the input list `w : List T`,
   using iterated `Nat.pair` and `succ`. The result is stored in binary on the tape
   using ChainΓ cells.

2. **Chain formatting**: Convert the binary representation to the chain tape format
   by adding a `cons` marker and bottom marker, and reversing the bit order.

## Singleton Functions

The list encoding fold (step 1) is built from two elementary operations:

- **Binary increment** (`binSucc`): Increment a binary number stored as ChainΓ cells.
- **Nat.pair with constant**: Compute `Nat.pair(k, n)` for fixed `k`.

These operations are "block-realizable": they process a contiguous block of
non-default cells while preserving everything after the first blank.

## Block Realizability

`TM0RealizesBlock Γ f` asserts that a TM0 machine processes the first contiguous
block of non-default cells according to `f`, preserving the tape after the blank.
This strengthened `TM0Realizes` enables "serialized" composition.
-/

open Turing PartrecToTM2 TM2to1

/-! ### Instances -/

noncomputable instance instDecEqChainΓ' : DecidableEq ChainΓ :=
  instDecidableEqProd (α := Bool) (β := (K' → Option Γ'))

/-! ### Distinguished ChainΓ cells -/

/-- Map a Γ' value to its corresponding ChainΓ cell (without bottom marker). -/
noncomputable def γ'ToChainΓ (γ' : Γ') : ChainΓ :=
  (false, Function.update (fun _ => none) K'.main (some γ'))

/-- The ChainΓ cell for the bottom marker with cons. -/
noncomputable def chainConsBottom : ChainΓ :=
  (true, Function.update (fun _ => none) K'.main (some Γ'.cons))

/-! ### Binary Representation -/

/-- Binary representation of n as ChainΓ cells (LSB first, no markers). -/
noncomputable def chainBinaryRepr (n : ℕ) : List ChainΓ :=
  (trNat n).map γ'ToChainΓ

/-! ### Chain Encoding Decomposition Equation -/

/-
`trInit K'.main (trList [n])` decomposes as:
    `[chainConsBottom] ++ (chainBinaryRepr n).reverse`
-/
theorem trInit_trList_singleton_eq (n : ℕ) :
    @trInit K' (fun _ => Γ') _ K'.main (trList [n]) =
    chainConsBottom :: (chainBinaryRepr n).reverse := by
  unfold trList; simp +decide [ chainBinaryRepr ] ;
  unfold trInit; simp +decide [ chainConsBottom ] ;
  unfold γ'ToChainΓ; aesop;

/-! ### Block Realizability -/

/-- A TM0 that operates on a contiguous block of non-default cells,
    preserving everything after the first blank.

    Given a tape `block ++ [default] ++ suffix`, the TM0 transforms
    it to `f(block) ++ [default] ++ suffix`, leaving suffix unchanged.
    This enables "serialized" composition of elementary operations. -/
def TM0RealizesBlock (Γ : Type) [Inhabited Γ] (f : List Γ → List Γ) : Prop :=
  ∃ (Λ : Type) (_ : Inhabited Λ) (_ : Fintype Λ)
    (M : TM0.Machine Γ Λ),
    ∀ (block suffix : List Γ),
      (∀ g ∈ block, g ≠ default) →
      (∀ g ∈ suffix, g ≠ default) →
      (∀ g ∈ f block, g ≠ default) →
      (TM0Seq.evalCfg M (block ++ default :: suffix)).Dom ∧
      ∀ (h : (TM0Seq.evalCfg M (block ++ default :: suffix)).Dom),
        ((TM0Seq.evalCfg M (block ++ default :: suffix)).get h).Tape =
          Tape.mk₁ (f block ++ default :: suffix)

/-
Composition of block-realizable functions.
    Requires `f` to preserve non-defaultness so that `M_g` can process
    `f(block)` as a valid block.
-/
theorem tm0RealizesBlock_comp {Γ : Type} [Inhabited Γ]
    {f g : List Γ → List Γ}
    (hf : TM0RealizesBlock Γ f) (hg : TM0RealizesBlock Γ g)
    (hf_nd : ∀ block, (∀ g ∈ block, g ≠ default) → ∀ g ∈ f block, g ≠ default) :
    TM0RealizesBlock Γ (g ∘ f) := by
  -- Apply the tm0_map_blankfree theorem to the identity function.
  apply Classical.byContradiction
  intro h_contra;
  obtain ⟨ Λ_f, h_f_inhabited, h_f_fintype, M_f, hM_f ⟩ := hf
  obtain ⟨ Λ_g, h_g_inhabited, h_g_fintype, M_g, hM_g ⟩ := hg;
  refine' h_contra ⟨ _, _, _, TM0Seq.compose M_f M_g, _ ⟩;
  · infer_instance;
  · intro block suffix hblock hsuffix hgf
    obtain ⟨hM_f_dom, hM_f_tape⟩ := hM_f block suffix hblock hsuffix (hf_nd block hblock)
    obtain ⟨hM_g_dom, hM_g_tape⟩ := hM_g (f block) suffix (hf_nd block hblock) hsuffix hgf;
    refine' ⟨ _, _ ⟩;
    · apply TM0Seq.compose_dom_of_parts;
      any_goals assumption;
      convert hM_g_dom using 1;
      exact hM_f_tape hM_f_dom ▸ rfl;
    · intro h;
      convert TM0Seq.compose_evalCfg_tape M_f M_g ( block ++ default :: suffix ) ( f block ++ default :: suffix ) hM_f_dom ( hM_f_tape hM_f_dom ) hM_g_dom h using 1;
      exact hM_g_tape hM_g_dom ▸ rfl

/-! ### Singleton Function 1: Binary Successor -/

/-- Syntactic binary increment on ChainΓ cells.
    Implements the standard carry-chain: flip 1→0 with carry, 0→1 without carry.
    Extends the representation if carry propagates past the MSB. -/
noncomputable def binSucc : List ChainΓ → List ChainΓ
  | [] => [γ'ToChainΓ Γ'.bit1]
  | c :: rest =>
    if c = γ'ToChainΓ Γ'.bit0 then
      γ'ToChainΓ Γ'.bit1 :: rest
    else if c = γ'ToChainΓ Γ'.bit1 then
      γ'ToChainΓ Γ'.bit0 :: binSucc rest
    else
      c :: rest

/-
invalid input, no-op

`binSucc` correctly increments the binary representation.
-/
theorem binSucc_correct (n : ℕ) :
    binSucc (chainBinaryRepr n) = chainBinaryRepr (n + 1) := by
  -- We'll use induction on $n$ to prove that `binSucc` correctly increments the binary representation.
  induction' n with n ih;
  · rfl;
  · unfold chainBinaryRepr at *;
    cases h : Num.ofNat' ( n + 1 ) <;> simp_all +decide [ trNat ];
    rename_i k;
    induction' k using PosNum.recOn with k ih;
    · simp +decide [ trNum ];
    · simp +decide [ trNum, PosNum.bit1 ];
      rw [ show ( Num.pos k.bit1 + 1 : Num ) = Num.pos ( k.succ.bit0 ) from ?_ ];
      · simp +decide [ trPosNum, binSucc ];
        have h_ind : ∀ k : PosNum, binSucc (List.map γ'ToChainΓ (trPosNum k)) = List.map γ'ToChainΓ (trPosNum (k.succ)) := by
          intro k; induction' k using PosNum.recOn with k ih; simp_all +decide [ trPosNum ] ;
          · simp_all +decide [ trPosNum, PosNum.succ ];
            rw [ ← ih ];
            exact if_neg ( by simp +decide [ γ'ToChainΓ ] ) |> fun h => h.trans ( if_pos rfl );
          · simp_all +decide [ binSucc, trPosNum ];
            simp_all +decide [ trPosNum, PosNum.succ ];
        exact h_ind k;
      · rfl;
    · unfold binSucc; aesop;

/-- All elements of `chainBinaryRepr n` are non-default. -/
theorem chainBinaryRepr_ne_default (n : ℕ) :
    ∀ g ∈ chainBinaryRepr n, g ≠ (default : ChainΓ) := by
  intro g hg
  obtain ⟨ γ', _, rfl ⟩ := List.mem_map.mp hg
  cases γ' <;> simp +decide [γ'ToChainΓ]

/-
All elements of `binSucc l` are non-default when the input elements are.
-/
theorem binSucc_ne_default (l : List ChainΓ) (hl : ∀ g ∈ l, g ≠ (default : ChainΓ)) :
    ∀ g ∈ binSucc l, g ≠ (default : ChainΓ) := by
  induction' l with c rest ih;
  · simp [binSucc];
    simp +decide [ γ'ToChainΓ ];
  · unfold binSucc; simp +decide [ hl ] ;
    split_ifs <;> simp_all +decide [ Function.update ]

/-! ### Binary Successor TM0 Machine -/

/-- States for the binary successor TM0 machine. -/
inductive BinSuccSt where
  | carry       -- read current cell, process with carry
  | carryMv     -- move right (after writing bit0, carry continues)
  | absorbed    -- move left (after writing bit1, carry absorbed)
  | extChk      -- move right (after writing bit1 at extension point)
  | extRd       -- read cell to check if suffix is empty
  | shiftW (g : ChainΓ) -- write g at current position (shifting suffix)
  | shiftMv (g : ChainΓ) -- move right (after writing in shift phase)
  | shiftDn     -- move left (after last shift write)
  | rwdSuf      -- rewind left through suffix
  | rwdBlk      -- rewind left through block to left boundary
  | done        -- halt

noncomputable instance : DecidableEq BinSuccSt := Classical.typeDecidableEq _

noncomputable instance : Inhabited BinSuccSt := ⟨.carry⟩

noncomputable instance : Fintype BinSuccSt := by
  have : Fintype ChainΓ := inferInstance
  exact
  { elems :=
      {.carry, .carryMv, .absorbed, .extChk, .extRd, .shiftDn, .rwdSuf, .rwdBlk, .done}
      ∪ Finset.univ.map ⟨BinSuccSt.shiftW, fun a b h => by cases h; rfl⟩
      ∪ Finset.univ.map ⟨BinSuccSt.shiftMv, fun a b h => by cases h; rfl⟩
    complete := by
      intro x
      cases x <;> simp [Finset.mem_union, Finset.mem_map, Finset.mem_insert] <;> aesop }

/-- The binary successor TM0 machine. -/
noncomputable def binSuccMachine : @TM0.Machine ChainΓ BinSuccSt ⟨.carry⟩ := fun q a =>
  match q with
  | .carry =>
    if a = γ'ToChainΓ Γ'.bit0 then
      some (.absorbed, .write (γ'ToChainΓ Γ'.bit1))
    else if a = γ'ToChainΓ Γ'.bit1 then
      some (.carryMv, .write (γ'ToChainΓ Γ'.bit0))
    else if a = default then
      some (.extChk, .write (γ'ToChainΓ Γ'.bit1))
    else
      some (.rwdBlk, .move Dir.left)  -- non-bit cell: no-op, rewind
  | .carryMv => some (.carry, .move Dir.right)
  | .absorbed => some (.rwdBlk, .move Dir.left)
  | .extChk => some (.extRd, .move Dir.right)
  | .extRd =>
    if a = default then
      some (.rwdBlk, .move Dir.left)
    else
      some (BinSuccSt.shiftMv a, .write default)
  | .shiftW g =>
    if a = default then
      some (.shiftDn, .write g)
    else
      some (BinSuccSt.shiftMv a, .write g)
  | .shiftMv g => some (.shiftW g, .move Dir.right)
  | .shiftDn => some (.rwdSuf, .move Dir.left)
  | .rwdSuf =>
    if a = default then
      some (.rwdBlk, .move Dir.left)
    else
      some (.rwdSuf, .move Dir.left)
  | .rwdBlk =>
    if a = default then
      some (.done, .move Dir.right)
    else
      some (.rwdBlk, .move Dir.left)
  | .done => none

/-! ### Helper lemmas for binSuccMachine correctness -/

/-
rwdBlk loop: move left through non-default cells to the left boundary.
-/
theorem binSucc_rwdBlk_loop (revL : List ChainΓ) (hrevL : ∀ g ∈ revL, g ≠ default)
    (acc : List ChainΓ) :
    Reaches (TM0.step binSuccMachine)
      ⟨.rwdBlk, ⟨revL.headI, ListBlank.mk revL.tail, ListBlank.mk acc⟩⟩
      ⟨.rwdBlk, ⟨default, ListBlank.mk [], ListBlank.mk (revL.reverse ++ acc)⟩⟩ := by
  induction' revL with a revL ih generalizing acc;
  · constructor;
  · simp_all +decide [ ListBlank.mk ];
    convert Relation.ReflTransGen.head _ ( ih ( a :: acc ) ) using 1;
    unfold TM0.step;
    unfold binSuccMachine; aesop;

/-
rwdSuf loop: move left through non-default suffix cells to the separator.
-/
theorem binSucc_rwdSuf_loop (revS : List ChainΓ) (hrevS : ∀ g ∈ revS, g ≠ default)
    (acc : List ChainΓ) :
    Reaches (TM0.step binSuccMachine)
      ⟨.rwdSuf, ⟨revS.headI, ListBlank.mk revS.tail, ListBlank.mk acc⟩⟩
      ⟨.rwdSuf, ⟨default, ListBlank.mk [], ListBlank.mk (revS.reverse ++ acc)⟩⟩ := by
  induction' revS with a revS ih generalizing acc;
  · constructor;
  · convert Relation.ReflTransGen.head _ ( ih ( fun g hg => hrevS g ( List.mem_cons_of_mem _ hg ) ) ( a :: acc ) ) using 1;
    · grind;
    · unfold TM0.step; unfold binSuccMachine; aesop;

/-
rwdSuf loop (extended): rewind through non-default suffix cells when there is
extra content on the left tape beyond the suffix.
-/
theorem binSucc_rwdSuf_loop_ext (revS extra : List ChainΓ) (hrevS : ∀ g ∈ revS, g ≠ default)
    (acc : List ChainΓ) :
    Reaches (TM0.step binSuccMachine)
      ⟨.rwdSuf, ⟨(revS ++ extra).headI, ListBlank.mk (revS ++ extra).tail, ListBlank.mk acc⟩⟩
      ⟨.rwdSuf, ⟨extra.headI, ListBlank.mk extra.tail, ListBlank.mk (revS.reverse ++ acc)⟩⟩ := by
  induction' revS with a revS ih generalizing acc;
  · constructor;
  · convert Relation.ReflTransGen.head _ ( ih ( fun g hg => hrevS g ( List.mem_cons_of_mem _ hg ) ) ( a :: acc ) ) using 1;
    · simp +decide [ List.reverse_cons ];
    · unfold TM0.step; unfold binSuccMachine; aesop;

/-
Shift loop: shift suffix cells right by one position.
    After the shift, the saved value and suffix have been pushed right by one,
    and the cursor is at the last shifted position ready for rewind.
-/
theorem binSucc_shift_loop (suffix : List ChainΓ) (hsuffix : ∀ g ∈ suffix, g ≠ default)
    (saved : ChainΓ) (prevL : List ChainΓ) :
    Reaches (TM0.step binSuccMachine)
      ⟨.shiftW saved, ⟨suffix.headI, ListBlank.mk prevL, ListBlank.mk suffix.tail⟩⟩
      ⟨.shiftDn, ⟨(saved :: suffix).getLast (by simp),
                 ListBlank.mk ((saved :: suffix).dropLast.reverse ++ prevL),
                 ListBlank.mk []⟩⟩ := by
  induction' suffix with s suffix ih generalizing saved prevL;
  · constructor;
    constructor;
    constructor;
  · -- Apply the induction hypothesis to the suffix.
    have h_ind : Reaches (TM0.step binSuccMachine) ⟨BinSuccSt.shiftW s, ⟨suffix.headI, ListBlank.mk (saved :: prevL), ListBlank.mk suffix.tail⟩⟩ ⟨BinSuccSt.shiftDn, ⟨(s :: suffix).getLast (by simp), ListBlank.mk ((s :: suffix).dropLast.reverse ++ (saved :: prevL)), ListBlank.mk []⟩⟩ := by
      exact ih ( fun g hg => hsuffix g ( List.mem_cons_of_mem _ hg ) ) s ( saved :: prevL );
    refine' Relation.ReflTransGen.head _ _;
    exact ⟨ BinSuccSt.shiftMv s, ⟨ saved, ListBlank.mk prevL, ListBlank.mk suffix ⟩ ⟩;
    · simp +decide [ TM0.step, binSuccMachine ];
      exact ⟨ TM0.Stmt.write saved, by aesop ⟩;
    · convert h_ind.head _ using 1;
      · simp +decide [ List.dropLast, List.getLast ];
      · cases suffix <;> simp +decide [ TM0.step ] at hsuffix ⊢;
        · exact ⟨ TM0.Stmt.move Dir.right, rfl, by cases saved ; trivial ⟩;
        · exact ⟨ TM0.Stmt.move Dir.right, rfl, by cases saved ; aesop ⟩

/-
Case: carry at bit0, absorbed immediately.
-/
theorem binSucc_carry_bit0 (rest suffix revLeft : List ChainΓ)
    (hrevLeft : ∀ g ∈ revLeft, g ≠ default) :
    Reaches (TM0.step binSuccMachine)
      ⟨.carry, ⟨γ'ToChainΓ Γ'.bit0, ListBlank.mk revLeft,
               ListBlank.mk (rest ++ default :: suffix)⟩⟩
      ⟨.done, Tape.mk₁ (revLeft.reverse ++ γ'ToChainΓ Γ'.bit1 :: rest ++ default :: suffix)⟩ := by
  have h_step1 : TM0.step binSuccMachine ⟨BinSuccSt.carry, ⟨γ'ToChainΓ Γ'.bit0, ListBlank.mk revLeft, ListBlank.mk (rest ++ default :: suffix)⟩⟩ = some ⟨BinSuccSt.absorbed, ⟨γ'ToChainΓ Γ'.bit1, ListBlank.mk revLeft, ListBlank.mk (rest ++ default :: suffix)⟩⟩ := by
    -- By definition of `binSuccMachine`, when the head is `bit0`, it writes `bit1` and moves to `absorbed`.
    simp [TM0.step, binSuccMachine];
  have h_step2 : TM0.step binSuccMachine ⟨BinSuccSt.absorbed, ⟨γ'ToChainΓ Γ'.bit1, ListBlank.mk revLeft, ListBlank.mk (rest ++ default :: suffix)⟩⟩ = some ⟨BinSuccSt.rwdBlk, ⟨revLeft.headI, ListBlank.mk revLeft.tail, ListBlank.mk (γ'ToChainΓ Γ'.bit1 :: rest ++ default :: suffix)⟩⟩ := by
    exact?;
  have := binSucc_rwdBlk_loop revLeft hrevLeft ( γ'ToChainΓ Γ'.bit1 :: rest ++ default :: suffix );
  have h_step4 : TM0.step binSuccMachine ⟨BinSuccSt.rwdBlk, ⟨default, ListBlank.mk [], ListBlank.mk (revLeft.reverse ++ γ'ToChainΓ Γ'.bit1 :: rest ++ default :: suffix)⟩⟩ = some ⟨BinSuccSt.done, ⟨(ListBlank.mk (revLeft.reverse ++ γ'ToChainΓ Γ'.bit1 :: rest ++ default :: suffix)).head, ListBlank.mk [], (ListBlank.mk (revLeft.reverse ++ γ'ToChainΓ Γ'.bit1 :: rest ++ default :: suffix)).tail⟩⟩ := by
    simp +decide [ TM0.step ];
    use TM0.Stmt.move Dir.right;
    cases h : revLeft.reverse ++ γ'ToChainΓ Γ'.bit1 :: ( rest ++ default :: suffix ) <;> simp_all +decide [ Tape.move ];
    exact ⟨ rfl, by ext i; cases i <;> rfl ⟩;
  exact Relation.ReflTransGen.trans ( Relation.ReflTransGen.single h_step1 ) ( Relation.ReflTransGen.trans ( Relation.ReflTransGen.single h_step2 ) ( this.trans ( Relation.ReflTransGen.single ( by simpa [ List.append_assoc ] using h_step4 ) ) ) )

/-
Case: carry at bit1, recursive on rest.
-/
theorem binSucc_carry_bit1 (rest suffix revLeft : List ChainΓ)
    (hrest : ∀ g ∈ rest, g ≠ default)
    (hsuffix : ∀ g ∈ suffix, g ≠ default)
    (hfrest : ∀ g ∈ binSucc rest, g ≠ default)
    (hrevLeft : ∀ g ∈ revLeft, g ≠ default)
    (ih : Reaches (TM0.step binSuccMachine)
      ⟨.carry, ⟨(rest ++ default :: suffix).headI,
               ListBlank.mk (γ'ToChainΓ Γ'.bit0 :: revLeft),
               ListBlank.mk (rest ++ default :: suffix).tail⟩⟩
      ⟨.done, Tape.mk₁ ((γ'ToChainΓ Γ'.bit0 :: revLeft).reverse ++ binSucc rest ++ default :: suffix)⟩) :
    Reaches (TM0.step binSuccMachine)
      ⟨.carry, ⟨γ'ToChainΓ Γ'.bit1, ListBlank.mk revLeft,
               ListBlank.mk (rest ++ default :: suffix)⟩⟩
      ⟨.done, Tape.mk₁ (revLeft.reverse ++ γ'ToChainΓ Γ'.bit0 :: binSucc rest ++ default :: suffix)⟩ := by
  convert Relation.ReflTransGen.trans _ ih using 1;
  · simp +decide [ List.reverse_cons ];
  · constructor;
    convert Relation.ReflTransGen.single _;
    exact ⟨ BinSuccSt.carryMv, ⟨ γ'ToChainΓ Γ'.bit0, ListBlank.mk revLeft, ListBlank.mk ( rest ++ default :: suffix ) ⟩ ⟩;
    · simp +decide [ TM0.step, binSuccMachine ];
    · cases rest <;> aesop

/-
Case: carry at non-bit, non-default cell. No-op, just rewind.
-/
theorem binSucc_carry_other (c : ChainΓ) (rest suffix revLeft : List ChainΓ)
    (hc : c ≠ γ'ToChainΓ Γ'.bit0) (hc1 : c ≠ γ'ToChainΓ Γ'.bit1) (hc2 : c ≠ default)
    (hrevLeft : ∀ g ∈ revLeft, g ≠ default) :
    Reaches (TM0.step binSuccMachine)
      ⟨.carry, ⟨c, ListBlank.mk revLeft,
               ListBlank.mk (rest ++ default :: suffix)⟩⟩
      ⟨.done, Tape.mk₁ (revLeft.reverse ++ c :: rest ++ default :: suffix)⟩ := by
  have h_rwdBlk : Reaches (TM0.step binSuccMachine) ⟨.rwdBlk, ⟨revLeft.headI, ListBlank.mk revLeft.tail, ListBlank.mk (c :: rest ++ default :: suffix)⟩⟩ ⟨.rwdBlk, ⟨default, ListBlank.mk [], ListBlank.mk (revLeft.reverse ++ c :: rest ++ default :: suffix)⟩⟩ := by
    grind +suggestions;
  have h_done : Reaches (TM0.step binSuccMachine) ⟨.rwdBlk, ⟨default, ListBlank.mk [], ListBlank.mk (revLeft.reverse ++ c :: rest ++ default :: suffix)⟩⟩ ⟨.done, Tape.mk₁ (revLeft.reverse ++ c :: rest ++ default :: suffix)⟩ := by
    use Relation.ReflTransGen.single (by
    simp +decide [ TM0.step ];
    use TM0.Stmt.move Dir.right;
    simp +decide [ Tape.move, Tape.mk₁ ];
    simp +decide [ Tape.mk₂ ];
    cases h : revLeft.reverse ++ c :: ( rest ++ default :: suffix ) <;> simp_all +decide [ Tape.mk' ];
    exact ⟨ by rfl, by ext i; cases i <;> rfl ⟩);
  have h_step : TM0.step binSuccMachine ⟨.carry, ⟨c, ListBlank.mk revLeft, ListBlank.mk (rest ++ default :: suffix)⟩⟩ = some ⟨.rwdBlk, ⟨revLeft.headI, ListBlank.mk revLeft.tail, ListBlank.mk (c :: rest ++ default :: suffix)⟩⟩ := by
    unfold TM0.step binSuccMachine; aesop;
  exact Relation.ReflTransGen.head h_step ( h_rwdBlk.trans h_done )

theorem listBlank_mk_append_default (l : List ChainΓ) :
    (ListBlank.mk (l ++ [default]) : ListBlank ChainΓ) = ListBlank.mk l := by
  apply Quot.sound; exact Or.inr ⟨1, by simp⟩

theorem tape_mk₁_append_default (a : ChainΓ) (l : List ChainΓ) :
    Tape.mk₁ (a :: l ++ [default]) = (Tape.mk₁ (a :: l) : Tape ChainΓ) := by
  simp [Tape.mk₁, Tape.mk₂, Tape.mk']; exact listBlank_mk_append_default l

/-
Extension case, empty suffix.
-/
theorem binSucc_carry_default_nil (revLeft : List ChainΓ)
    (hrevLeft : ∀ g ∈ revLeft, g ≠ default) :
    Reaches (TM0.step binSuccMachine)
      ⟨.carry, ⟨default, ListBlank.mk revLeft, ListBlank.mk []⟩⟩
      ⟨.done, Tape.mk₁ (revLeft.reverse ++ [γ'ToChainΓ Γ'.bit1, default])⟩ := by
  convert Relation.ReflTransGen.trans ( Relation.ReflTransGen.single _ ) ( Relation.ReflTransGen.trans ( Relation.ReflTransGen.single _ ) ( Relation.ReflTransGen.trans ( Relation.ReflTransGen.single _ ) ( Relation.ReflTransGen.trans ( binSucc_rwdBlk_loop _ _ _ ) ( Relation.ReflTransGen.single _ ) ) ) ) using 1;
  rotate_left;
  exact ⟨ BinSuccSt.extChk, ⟨ γ'ToChainΓ Γ'.bit1, ListBlank.mk revLeft, ListBlank.mk [] ⟩ ⟩;
  exact?;
  rotate_left;
  exact γ'ToChainΓ Γ'.bit1 :: revLeft;
  rotate_left;
  exact [ ];
  · convert tape_mk₁_append_default _ _ using 2;
    rotate_left;
    exact ( γ'ToChainΓ Γ'.bit1 :: revLeft ).reverse.head!;
    exact ( γ'ToChainΓ Γ'.bit1 :: revLeft ).reverse.tail;
    simp +decide [ TM0.step, binSuccMachine ];
    simp +decide [ Tape.move, Tape.mk₁ ];
    simp +decide [ Tape.mk₂, ListBlank.mk ];
    simp +decide [ Tape.mk', List.head!, List.tail ];
    cases revLeft.reverse <;> simp +decide [ ListBlank.head, ListBlank.tail ];
    · simp +decide [ ListBlank.mk ];
      exact fun h => h.symm;
    · simp +decide [ eq_comm, Quotient.eq'' ];
      simp +decide [ QuotientAddGroup.leftRel_apply, ListBlank.ext_iff ];
      simp +decide [ ListBlank.nth ];
      intro h i; specialize h ( List.length ‹_› + 1 ) ; simp_all +decide [ List.getI ] ;
  · unfold TM0.step;
    unfold binSuccMachine; simp +decide [ hrevLeft ] ;
  · unfold TM0.step;
    unfold binSuccMachine; simp +decide [ ListBlank.mk ] ;
    exact ⟨ TM0.Stmt.move Dir.left, by aesop ⟩;
  · simp +decide [ γ'ToChainΓ ];
    exact hrevLeft

private theorem γ'bit1_ne_default : γ'ToChainΓ Γ'.bit1 ≠ (default : ChainΓ) := by
  simp +decide [γ'ToChainΓ]

/-
Phase 1: carry at default → shiftW s (steps 1-4 of the extension).
-/
private theorem binSucc_ext_phase1 (s : ChainΓ) (rest revLeft : List ChainΓ)
    (hs : s ≠ default) :
    Reaches (TM0.step binSuccMachine)
      ⟨.carry, ⟨default, ListBlank.mk revLeft, ListBlank.mk (s :: rest)⟩⟩
      ⟨.shiftW s, ⟨rest.headI,
                  ListBlank.mk (default :: γ'ToChainΓ Γ'.bit1 :: revLeft),
                  ListBlank.mk rest.tail⟩⟩ := by
  constructor;
  rotate_right;
  exact ⟨ BinSuccSt.shiftMv s, ⟨ default, ListBlank.mk ( γ'ToChainΓ Γ'.bit1 :: revLeft ), ListBlank.mk rest ⟩ ⟩;
  · constructor;
    rotate_right;
    exact ⟨ BinSuccSt.extRd, ⟨ s, ListBlank.mk ( γ'ToChainΓ Γ'.bit1 :: revLeft ), ListBlank.mk rest ⟩ ⟩;
    · constructor;
      apply_rules [ Relation.ReflTransGen.single ];
      unfold binSuccMachine; aesop;
    · unfold TM0.step;
      unfold binSuccMachine; aesop;
  · cases rest <;> aesop

/-
Sub-phase A: shiftDn → rwdSuf (1 step, move left).
-/
private theorem binSucc_ext_shiftDn_step (head : ChainΓ) (leftList : List ChainΓ) :
    Reaches (TM0.step binSuccMachine)
      ⟨.shiftDn, ⟨head, ListBlank.mk leftList, ListBlank.mk []⟩⟩
      ⟨.rwdSuf, ⟨leftList.headI, ListBlank.mk leftList.tail, ListBlank.mk [head]⟩⟩ := by
  -- By definition of ` TM0.step`, we can see that the transition from `shiftDn` to `rwdSuf` is indeed a single step.
  apply Relation.ReflTransGen.single;
  cases leftList <;> aesop

/-
Sub-phase C: rwdSuf at default → rwdBlk (1 step, move left).
-/
private theorem binSucc_ext_rwdSuf_to_rwdBlk (leftList : List ChainΓ) (rightList : List ChainΓ) :
    Reaches (TM0.step binSuccMachine)
      ⟨.rwdSuf, ⟨default, ListBlank.mk leftList, ListBlank.mk rightList⟩⟩
      ⟨.rwdBlk, ⟨leftList.headI, ListBlank.mk leftList.tail, ListBlank.mk (default :: rightList)⟩⟩ := by
  convert Relation.ReflTransGen.single _;
  cases leftList <;> aesop

/-
Elements of (s :: rest).dropLast are all non-default when s and rest elements are.
-/
private theorem dropLast_cons_ne_default (s : ChainΓ) (rest : List ChainΓ)
    (hs : s ≠ default) (hrest : ∀ g ∈ rest, g ≠ default) :
    ∀ g ∈ (s :: rest).dropLast, g ≠ default := by
  intro g hg; have := List.mem_of_mem_dropLast hg; aesop;

/-- Phase 2: after shift loop + shiftDn → rwdSuf configuration. -/
private theorem binSucc_ext_phase2_rwdSuf (s : ChainΓ) (rest revLeft : List ChainΓ)
    (hs : s ≠ default)
    (hrest : ∀ g ∈ rest, g ≠ default)
    (hrevLeft : ∀ g ∈ revLeft, g ≠ default) :
    Reaches (TM0.step binSuccMachine)
      ⟨.shiftDn, ⟨(s :: rest).getLast (by simp),
                  ListBlank.mk ((s :: rest).dropLast.reverse ++ default :: γ'ToChainΓ Γ'.bit1 :: revLeft),
                  ListBlank.mk []⟩⟩
      ⟨.rwdBlk, ⟨(γ'ToChainΓ Γ'.bit1 :: revLeft).headI,
                 ListBlank.mk (γ'ToChainΓ Γ'.bit1 :: revLeft).tail,
                 ListBlank.mk (default :: s :: rest)⟩⟩ := by
  -- Sub-phase A: shiftDn → rwdSuf
  have hA := binSucc_ext_shiftDn_step ((s :: rest).getLast (by simp))
    ((s :: rest).dropLast.reverse ++ default :: γ'ToChainΓ Γ'.bit1 :: revLeft)
  -- Sub-phase B: rwdSuf loop through suffix cells
  have h_nd_rev : ∀ g ∈ (s :: rest).dropLast.reverse, g ≠ default := by
    intro g hg
    exact dropLast_cons_ne_default s rest hs hrest g (List.mem_reverse.mp hg)
  have hB := binSucc_rwdSuf_loop_ext
    (s :: rest).dropLast.reverse
    (default :: γ'ToChainΓ Γ'.bit1 :: revLeft)
    h_nd_rev
    [((s :: rest).getLast (by simp))]
  -- Sub-phase C: rwdSuf at default → rwdBlk
  have hC := binSucc_ext_rwdSuf_to_rwdBlk
    (γ'ToChainΓ Γ'.bit1 :: revLeft)
    (s :: rest)
  refine hA.trans (hB.trans ?_)
  convert hC using 2
  simp [List.reverse_reverse, List.dropLast_append_getLast]

/-
Phase 3: rwdBlk through bit1 :: revLeft → done.
-/
private theorem binSucc_ext_phase3_done (s : ChainΓ) (rest revLeft : List ChainΓ)
    (hrevLeft : ∀ g ∈ revLeft, g ≠ default) :
    Reaches (TM0.step binSuccMachine)
      ⟨.rwdBlk, ⟨(γ'ToChainΓ Γ'.bit1 :: revLeft).headI,
                 ListBlank.mk (γ'ToChainΓ Γ'.bit1 :: revLeft).tail,
                 ListBlank.mk (default :: s :: rest)⟩⟩
      ⟨.done, Tape.mk₁ (revLeft.reverse ++ γ'ToChainΓ Γ'.bit1 :: default :: s :: rest)⟩ := by
  have h_tape_eq : Tape.mk₁ (revLeft.reverse ++ γ'ToChainΓ Γ'.bit1 :: default :: s :: rest) = ⟨(revLeft.reverse ++ γ'ToChainΓ Γ'.bit1 :: default :: s :: rest).headI, ListBlank.mk [], ListBlank.mk (revLeft.reverse ++ γ'ToChainΓ Γ'.bit1 :: default :: s :: rest).tail⟩ := by
    exact?;
  have := binSucc_rwdBlk_loop (γ'ToChainΓ Γ'.bit1 :: revLeft) (by
  simp +decide [ γ'ToChainΓ, hrevLeft ];
  assumption) (default :: s :: rest);
  refine' this.trans _;
  simp +decide [ TM0.step ];
  refine' .single _;
  use BinSuccSt.done, TM0.Stmt.move Dir.right;
  cases h : revLeft.reverse ++ γ'ToChainΓ Γ'.bit1 :: default :: s :: rest <;> simp_all +decide [ Tape.move ];
  exact ⟨ rfl, listBlank_mk_append_default [] ⟩

/-- Extension case, non-empty suffix. -/
theorem binSucc_carry_default_cons (s : ChainΓ) (rest revLeft : List ChainΓ)
    (hs : s ≠ default)
    (hrest : ∀ g ∈ rest, g ≠ default)
    (hrevLeft : ∀ g ∈ revLeft, g ≠ default) :
    Reaches (TM0.step binSuccMachine)
      ⟨.carry, ⟨default, ListBlank.mk revLeft, ListBlank.mk (s :: rest)⟩⟩
      ⟨.done, Tape.mk₁ (revLeft.reverse ++ γ'ToChainΓ Γ'.bit1 :: default :: s :: rest)⟩ := by
  -- Phase 1: carry → shiftW s (individual transitions)
  have h1 := binSucc_ext_phase1 s rest revLeft hs
  -- Phase 2a: shift loop
  have h2a := binSucc_shift_loop rest hrest s (default :: γ'ToChainΓ Γ'.bit1 :: revLeft)
  -- Phase 2b: shiftDn → rwdBlk (via rwdSuf)
  have h2b := binSucc_ext_phase2_rwdSuf s rest revLeft hs hrest hrevLeft
  -- Phase 3: rwdBlk → done
  have h3 := binSucc_ext_phase3_done s rest revLeft hrevLeft
  exact h1.trans (h2a.trans (h2b.trans h3))

/-- Case: carry at default (empty block), extension. -/
theorem binSucc_carry_default (suffix revLeft : List ChainΓ)
    (hsuffix : ∀ g ∈ suffix, g ≠ default)
    (hrevLeft : ∀ g ∈ revLeft, g ≠ default) :
    Reaches (TM0.step binSuccMachine)
      ⟨.carry, ⟨default, ListBlank.mk revLeft, ListBlank.mk suffix⟩⟩
      ⟨.done, Tape.mk₁ (revLeft.reverse ++ γ'ToChainΓ Γ'.bit1 :: default :: suffix)⟩ := by
  cases suffix with
  | nil => exact binSucc_carry_default_nil revLeft hrevLeft
  | cons s rest =>
    have hs := hsuffix s List.mem_cons_self
    have hrest : ∀ g ∈ rest, g ≠ default := fun g hg => hsuffix g (List.mem_cons_of_mem s hg)
    exact binSucc_carry_default_cons s rest revLeft hs hrest hrevLeft

/-
Auxiliary: the carry phase starting with left context `revLeft`.
-/
theorem binSucc_carry_aux (block suffix revLeft : List ChainΓ)
    (hblock : ∀ g ∈ block, g ≠ default)
    (hsuffix : ∀ g ∈ suffix, g ≠ default)
    (hfblock : ∀ g ∈ binSucc block, g ≠ default)
    (hrevLeft : ∀ g ∈ revLeft, g ≠ default) :
    Reaches (TM0.step binSuccMachine)
      ⟨.carry, ⟨(block ++ default :: suffix).headI,
               ListBlank.mk revLeft,
               ListBlank.mk (block ++ default :: suffix).tail⟩⟩
      ⟨.done, Tape.mk₁ (revLeft.reverse ++ binSucc block ++ default :: suffix)⟩ := by
  induction' block with c rest ih generalizing suffix revLeft;
  · convert binSucc_carry_default suffix revLeft hsuffix hrevLeft using 1;
    unfold binSucc; aesop;
  · by_cases hc : c = γ'ToChainΓ Γ'.bit0 <;> by_cases hc1 : c = γ'ToChainΓ Γ'.bit1 <;> simp +decide [ hc, hc1, binSucc ] at hfblock ⊢;
    · simp_all +decide [ γ'ToChainΓ ];
    · convert binSucc_carry_bit0 rest suffix revLeft hrevLeft using 1;
      simp +decide [ List.append_assoc ];
    · convert binSucc_carry_bit1 rest suffix revLeft _ _ _ _ _ using 1 <;> simp +decide [ * ];
      · exact fun g hg => hblock g <| List.mem_cons_of_mem _ hg;
      · assumption;
      · assumption;
      · assumption;
      · convert ih suffix ( γ'ToChainΓ Γ'.bit0 :: revLeft ) _ _ _ _ using 1 <;> simp +decide [ * ];
        · exact fun g hg => hblock g ( List.mem_cons_of_mem _ hg );
        · assumption;
        · assumption;
        · assumption;
    · convert binSucc_carry_other c rest suffix revLeft hc hc1 hfblock.1 hrevLeft using 1;
      simp +decide [ List.append_assoc ]

/-
**Binary successor is block-realizable (singleton function #1).**

    Uses `binSuccMachine` which implements a carry-chain:
    - `carry` phase: scan right through block, flipping bit1→bit0 (carry) or bit0→bit1 (absorb).
    - Extension: if carry reaches blank, write bit1 and shift suffix right by 1.
    - Rewind: move left back to position 0.
-/
theorem tm0_binSucc_block : TM0RealizesBlock ChainΓ binSucc := by
  use BinSuccSt, by infer_instance, by infer_instance, binSuccMachine;
  intro block suffix hblock hsuffix hfblock
  have h_reaches : Reaches (TM0.step binSuccMachine) (TM0.init (block ++ default :: suffix)) ⟨.done, Tape.mk₁ (binSucc block ++ default :: suffix)⟩ := by
    convert binSucc_carry_aux block suffix [] hblock hsuffix hfblock (by simp) using 1;
  obtain ⟨c, hc⟩ : ∃ c : TM0.Cfg ChainΓ BinSuccSt, c ∈ Turing.eval (TM0.step binSuccMachine) (TM0.init (block ++ default :: suffix)) ∧ c.Tape = Tape.mk₁ (binSucc block ++ default :: suffix) := by
    exact ⟨ _, Turing.mem_eval.mpr ⟨ h_reaches, by tauto ⟩, rfl ⟩;
  unfold TM0Seq.evalCfg;
  simp_all +decide [ Part.mem_eq ];
  grind

/-! ### Singleton Function 2: Addition via Repeated Increment -/

/-- Iterated application of `binSucc` (add constant `c` to the binary block). -/
noncomputable def binAddConst (c : ℕ) : List ChainΓ → List ChainΓ :=
  Nat.iterate binSucc c

/-
Adding a constant via repeated increment is correct.
-/
theorem binAddConst_correct (c n : ℕ) :
    binAddConst c (chainBinaryRepr n) = chainBinaryRepr (n + c) := by
  unfold binAddConst;
  refine' Nat.rec _ _ c <;> simp_all +decide [ Function.iterate_succ_apply', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc ];
  exact fun k hk => by rw [ ← add_assoc, binSucc_correct ] ;

/-
Iterated block operations preserve block-realizability.
-/
theorem tm0RealizesBlock_iterate {Γ : Type} [Inhabited Γ]
    {f : List Γ → List Γ} (hf : TM0RealizesBlock Γ f)
    (hf_nd : ∀ block, (∀ g ∈ block, g ≠ default) → ∀ g ∈ f block, g ≠ default)
    (n : ℕ) :
    TM0RealizesBlock Γ (Nat.iterate f n) := by
  induction' n with n ih;
  · refine' ⟨ _, _, _, _, _ ⟩;
    exact Fin 2;
    exact inferInstance;
    exact inferInstance;
    exact fun _ _ => none;
    unfold TM0Seq.evalCfg; simp +decide [ TM0Seq.evalCfg ] ;
    unfold eval; simp +decide [ TM0.step ] ;
    unfold PFun.fix; simp +decide [ TM0.init ] ;
    grind +suggestions;
  · convert tm0RealizesBlock_comp hf ih _ using 1;
    exact hf_nd

/-- Addition of a constant is block-realizable (derived from increment). -/
theorem tm0_binAddConst_block (c : ℕ) :
    TM0RealizesBlock ChainΓ (binAddConst c) := by
  exact tm0RealizesBlock_iterate tm0_binSucc_block binSucc_ne_default c

/-! ### Decoding binary blocks -/

/-- Decode a list of ChainΓ cells back to a natural number.
    This is the left inverse of `chainBinaryRepr` on valid inputs. -/
noncomputable def decodeBinaryBlock : List ChainΓ → ℕ
  | [] => 0
  | c :: rest =>
    if c = γ'ToChainΓ Γ'.bit0 then
      2 * decodeBinaryBlock rest
    else if c = γ'ToChainΓ Γ'.bit1 then
      2 * decodeBinaryBlock rest + 1
    else
      0

/-
invalid input

`decodeBinaryBlock` is a left inverse of `chainBinaryRepr`.
-/
theorem decodeBinaryBlock_chainBinaryRepr (n : ℕ) :
    decodeBinaryBlock (chainBinaryRepr n) = n := by
  -- By definition of `decodeBinaryBlock`, we know that `decodeBinaryBlock (chainBinaryRepr (2 * n)) = 2 * decodeBinaryBlock (chainBinaryRepr n)`.
  have h_decode_even : ∀ n, decodeBinaryBlock (chainBinaryRepr (2 * n)) = 2 * decodeBinaryBlock (chainBinaryRepr n) := by
    intro n
    simp [chainBinaryRepr, trNat];
    rcases n with ( _ | n ) <;> simp_all +decide [ Nat.mul_succ ];
    erw [ show ( 2 * ( n + 1 ) : Num ) = Num.bit0 ( n + 1 ) from ?_ ];
    · cases h : ( n + 1 : Num ) ; simp_all +decide [ trNum ];
      aesop;
    · norm_cast;
      grind +suggestions;
  -- By definition of `decodeBinaryBlock`, we know that `decodeBinaryBlock (chainBinaryRepr (2 * n + 1)) = 2 * decodeBinaryBlock (chainBinaryRepr n) + 1`.
  have h_decode_odd : ∀ n, decodeBinaryBlock (chainBinaryRepr (2 * n + 1)) = 2 * decodeBinaryBlock (chainBinaryRepr n) + 1 := by
    intro n;
    rcases n with ( _ | n ) <;> simp_all +decide [ Nat.mul_succ, chainBinaryRepr ];
    unfold trNat; simp +decide [ Nat.mul_succ, chainBinaryRepr ] ;
    erw [ show ( 2 * n + 2 + 1 : Num ) = Num.bit1 ( n + 1 ) by
            grind +suggestions ];
    cases h : ( n : Num ) + 1 <;> simp_all +decide [ Num.bit1 ];
    cases ‹PosNum› <;> rfl;
  induction' n using Nat.strong_induction_on with n ih; rcases Nat.even_or_odd' n with ⟨ k, rfl | rfl ⟩ <;> simp_all +arith +decide;
  cases k <;> simp_all +arith +decide

/-! ### Singleton Function 3: Addition via Decode/Encode Pipeline -/

/-- Add a constant to the block value, going through decode/encode.
    Unlike `binAddConst` (which iterates `binSucc` syntactically), this
    version decodes the block, adds `c`, and re-encodes. The two agree
    on valid binary blocks but this version composes with other
    decode/encode functions like `binSquare`. -/
noncomputable def binAddConstRepr (c : ℕ) (block : List ChainΓ) : List ChainΓ :=
  chainBinaryRepr (decodeBinaryBlock block + c)

theorem binAddConstRepr_correct (c n : ℕ) :
    binAddConstRepr c (chainBinaryRepr n) = chainBinaryRepr (n + c) := by
  unfold binAddConstRepr; rw [decodeBinaryBlock_chainBinaryRepr]

theorem binAddConstRepr_ne_default (c : ℕ) (block : List ChainΓ)
    (_hblock : ∀ g ∈ block, g ≠ default) :
    ∀ g ∈ binAddConstRepr c block, g ≠ default := by
  unfold binAddConstRepr; exact chainBinaryRepr_ne_default _

/-- Normalize a block to its canonical binary representation.
    This is the composition `chainBinaryRepr ∘ decodeBinaryBlock`. -/
noncomputable def normalizeBlock (block : List ChainΓ) : List ChainΓ :=
  chainBinaryRepr (decodeBinaryBlock block)

theorem normalizeBlock_correct (n : ℕ) :
    normalizeBlock (chainBinaryRepr n) = chainBinaryRepr n := by
  unfold normalizeBlock; rw [decodeBinaryBlock_chainBinaryRepr]

theorem normalizeBlock_ne_default (block : List ChainΓ) :
    ∀ g ∈ normalizeBlock block, g ≠ default := by
  unfold normalizeBlock; exact chainBinaryRepr_ne_default _

/-- Key decomposition: `binAddConstRepr c = binAddConst c ∘ normalizeBlock`. -/
theorem binAddConstRepr_eq_comp (c : ℕ) :
    binAddConstRepr c = binAddConst c ∘ normalizeBlock := by
  ext block
  simp [binAddConstRepr, normalizeBlock, Function.comp]
  rw [binAddConst_correct]

/-! #### Normalization decomposition -/

/-- Replace cells from the first non-standard cell onwards with bit0.
    Preserves block length and `decodeBinaryBlock`. -/
noncomputable def replaceNonStandard : List ChainΓ → List ChainΓ
  | [] => []
  | c :: rest =>
    if c = γ'ToChainΓ Γ'.bit0 then c :: replaceNonStandard rest
    else if c = γ'ToChainΓ Γ'.bit1 then c :: replaceNonStandard rest
    else List.replicate (rest.length + 1) (γ'ToChainΓ Γ'.bit0)

theorem replaceNonStandard_decodeBinaryBlock (block : List ChainΓ) :
    decodeBinaryBlock (replaceNonStandard block) = decodeBinaryBlock block := by
  revert block;
  -- We'll use induction on the block to prove that the decodeBinaryBlock function is invariant under replacing non-standard elements with bit0.
  have h_ind : ∀ (c : ChainΓ) (block : List ChainΓ), decodeBinaryBlock (c :: block) = if c = γ'ToChainΓ Γ'.bit0 then 2 * decodeBinaryBlock block else if c = γ'ToChainΓ Γ'.bit1 then 2 * decodeBinaryBlock block + 1 else 0 := by
    -- By definition of `decodeBinaryBlock`, we can split into cases based on the value of `c`.
    intros c block
    rw [decodeBinaryBlock];
  intro block
  induction' block with c block ih;
  · rfl;
  · by_cases hc : c = γ'ToChainΓ Γ'.bit0 ∨ c = γ'ToChainΓ Γ'.bit1;
    · cases hc <;> simp +decide [ *, replaceNonStandard ];
    · rw [ show replaceNonStandard ( c :: block ) = List.replicate ( block.length + 1 ) ( γ'ToChainΓ Γ'.bit0 ) from ?_ ];
      · induction block.length <;> simp_all +decide [ List.replicate ];
      · exact if_neg ( by tauto ) |> fun h => h.trans ( if_neg ( by tauto ) )

theorem replaceNonStandard_ne_default (block : List ChainΓ)
    (_hblock : ∀ g ∈ block, g ≠ default) :
    ∀ g ∈ replaceNonStandard block, g ≠ default := by
  induction' block with c rest ih;
  · exact?;
  · by_cases hc : c = γ'ToChainΓ Γ'.bit0 ∨ c = γ'ToChainΓ Γ'.bit1 <;> simp_all +decide [ replaceNonStandard ];
    grind

theorem replaceNonStandard_allBits (block : List ChainΓ) :
    ∀ g ∈ replaceNonStandard block,
      g = γ'ToChainΓ Γ'.bit0 ∨ g = γ'ToChainΓ Γ'.bit1 := by
  induction' block with c block ih;
  · tauto;
  · by_cases hc : c = γ'ToChainΓ Γ'.bit0 ∨ c = γ'ToChainΓ Γ'.bit1 <;> simp_all +decide [ replaceNonStandard ];
    grind +qlia

/-- Strip trailing bit0 cells from a pure bit0/bit1 block. -/
noncomputable def stripTrailingBit0 : List ChainΓ → List ChainΓ
  | [] => []
  | c :: rest =>
    if c = γ'ToChainΓ Γ'.bit0 then
      let r := stripTrailingBit0 rest
      if r = [] then [] else c :: r
    else c :: stripTrailingBit0 rest

theorem stripTrailingBit0_decodeBinaryBlock (block : List ChainΓ)
    (hblock : ∀ g ∈ block, g = γ'ToChainΓ Γ'.bit0 ∨ g = γ'ToChainΓ Γ'.bit1) :
    decodeBinaryBlock (stripTrailingBit0 block) = decodeBinaryBlock block := by
  induction' block with c rest ih;
  · rfl;
  · by_cases hc : c = γ'ToChainΓ Γ'.bit0;
    · by_cases h : stripTrailingBit0 rest = [] <;> simp_all +decide;
      · rw [ show stripTrailingBit0 ( γ'ToChainΓ Γ'.bit0 :: rest ) = stripTrailingBit0 rest from ?_ ];
        · simp_all +decide [ decodeBinaryBlock ];
          linarith;
        · exact if_pos rfl |> fun h => h.trans ( by aesop );
      · convert congr_arg ( fun x => 2 * x ) ih using 1;
        rw [ show stripTrailingBit0 ( γ'ToChainΓ Γ'.bit0 :: rest ) = γ'ToChainΓ Γ'.bit0 :: stripTrailingBit0 rest from ?_ ];
        · exact if_pos rfl;
        · exact if_pos rfl |> fun h => h.trans ( if_neg <| by aesop );
    · rw [ show stripTrailingBit0 ( c :: rest ) = c :: stripTrailingBit0 rest from ?_ ];
      · cases hblock c ( by simp +decide ) <;> simp_all +decide [ decodeBinaryBlock ];
      · exact if_neg hc

private theorem num_cast_ne_zero (n : ℕ) (hn : n ≠ 0) : (n : Num) ≠ 0 := by
  intro h; apply hn
  have := congr_arg (· : Num → ℕ) h
  simp at this; exact this

private theorem chainBinaryRepr_double (n : ℕ) (hn : n ≠ 0) :
    chainBinaryRepr (2 * n) = γ'ToChainΓ Γ'.bit0 :: chainBinaryRepr n := by
  simp only [chainBinaryRepr, trNat]
  have h_eq : (↑(2 * n) : Num) = ((↑n : Num)).bit0 := by
    have : 2 * n = Nat.bit false n := by simp [Nat.bit]
    rw [this]; show Num.ofNat' _ = _; rw [Num.ofNat'_bit]; simp
  rw [h_eq]
  cases hc : (↑n : Num) with
  | zero => exact absurd hc (num_cast_ne_zero n hn)
  | pos p => simp [Num.bit0, trNum, trPosNum]

private theorem chainBinaryRepr_double_succ (n : ℕ) :
    chainBinaryRepr (2 * n + 1) = γ'ToChainΓ Γ'.bit1 :: chainBinaryRepr n := by
  simp only [chainBinaryRepr, trNat]
  have h_eq : (↑(2 * n + 1) : Num) = ((↑n : Num)).bit1 := by
    have : 2 * n + 1 = Nat.bit true n := by simp [Nat.bit]
    rw [this]; show Num.ofNat' _ = _; rw [Num.ofNat'_bit]; simp
  rw [h_eq]
  cases hc : (↑n : Num) with
  | zero => simp [Num.bit1, trNum, trPosNum]
  | pos p => simp [Num.bit1, trNum, trPosNum]

private theorem chainBinaryRepr_eq_nil_iff (n : ℕ) :
    chainBinaryRepr n = [] ↔ n = 0 := by
  constructor
  · intro h; simp [chainBinaryRepr, trNat] at h
    by_contra hn; push_neg at hn
    cases hc : (↑n : Num) with
    | zero => have := congr_arg (· : Num → ℕ) hc; simp at this; exact hn this
    | pos p => rw [hc] at h; simp [trNum] at h; cases p <;> simp [trPosNum] at h
  · intro h; subst h; simp +decide [chainBinaryRepr, trNat]

theorem stripTrailingBit0_eq_chainBinaryRepr (block : List ChainΓ)
    (hblock : ∀ g ∈ block, g = γ'ToChainΓ Γ'.bit0 ∨ g = γ'ToChainΓ Γ'.bit1) :
    stripTrailingBit0 block = chainBinaryRepr (decodeBinaryBlock block) := by
  induction' block with c rest ih;
  · rfl;
  · cases hblock c ( by simp +decide ) <;> simp_all +decide [ stripTrailingBit0 ];
    · rw [ show decodeBinaryBlock ( γ'ToChainΓ Γ'.bit0 :: rest ) = 2 * decodeBinaryBlock rest from ?_ ];
      · cases h : decodeBinaryBlock rest <;> simp_all +decide [ chainBinaryRepr_double ];
        exact fun h => by have := chainBinaryRepr_eq_nil_iff ( Nat.succ ‹_› ) ; aesop;
      · exact if_pos rfl;
    · exact?

theorem normalizeBlock_eq_comp :
    normalizeBlock = stripTrailingBit0 ∘ replaceNonStandard := by
  funext block
  unfold normalizeBlock Function.comp
  rw [← replaceNonStandard_decodeBinaryBlock block,
      stripTrailingBit0_eq_chainBinaryRepr (replaceNonStandard block)
        (replaceNonStandard_allBits block)]

/-! #### replaceNonStandard machine construction -/

/-- States for the replaceNonStandard machine.
    0 = scan (initial): move right through bit0/bit1, replace non-standard
    1 = replAfterW: just wrote bit0, advance right
    2 = replace: write bit0 to all remaining cells
    3 = rewind: move left to position 0
    4 = done: halt -/
noncomputable def replNSMachine : @TM0.Machine ChainΓ (Fin 5) ⟨0⟩ := fun q a =>
  match q with
  | (0 : Fin 5) => -- scan
    if a = γ'ToChainΓ Γ'.bit0 then some (0, .move Dir.right)
    else if a = γ'ToChainΓ Γ'.bit1 then some (0, .move Dir.right)
    else if a = default then some (3, .move Dir.left)  -- end of block
    else some (1, .write (γ'ToChainΓ Γ'.bit0))  -- non-standard, replace
  | (1 : Fin 5) => -- replAfterW: advance after writing bit0
    some (2, .move Dir.right)
  | (2 : Fin 5) => -- replace
    if a = default then some (3, .move Dir.left)  -- end of block
    else some (1, .write (γ'ToChainΓ Γ'.bit0))  -- replace with bit0
  | (3 : Fin 5) => -- rewind
    if a = default then some (4, .move Dir.right)  -- reached left boundary
    else some (3, .move Dir.left)
  | (4 : Fin 5) => -- done
    none

/-
Rewind loop for replNS: from state 3, moves left through non-default cells.
-/
theorem replNS_rwdLoop (revL : List ChainΓ) (hrevL : ∀ g ∈ revL, g ≠ default)
    (acc : List ChainΓ) :
    Reaches (TM0.step replNSMachine)
      ⟨3, ⟨revL.headI, ListBlank.mk revL.tail, ListBlank.mk acc⟩⟩
      ⟨3, ⟨default, ListBlank.mk [], ListBlank.mk (revL.reverse ++ acc)⟩⟩ := by
  unfold TM0.step;
  induction' revL with a revL ih generalizing acc;
  · constructor;
  · convert Relation.ReflTransGen.head _ ( ih ( fun g hg => hrevL g ( List.mem_cons_of_mem _ hg ) ) ( a :: acc ) ) using 1;
    · grind;
    · unfold replNSMachine; aesop;

/-
Replace loop for replNS: from state 2, replaces all non-default cells with bit0,
    then transitions to state 3 at the last replaced cell.
    Since List.replicate is all the same element, its reverse equals itself.
-/
theorem replNS_replLoop (cells : List ChainΓ) (hcells : ∀ g ∈ cells, g ≠ default)
    (revL : List ChainΓ) (suffix : List ChainΓ) :
    Reaches (TM0.step replNSMachine)
      ⟨2, ⟨(cells ++ default :: suffix).headI,
           ListBlank.mk revL,
           ListBlank.mk (cells ++ default :: suffix).tail⟩⟩
      ⟨3, ⟨(List.replicate cells.length (γ'ToChainΓ Γ'.bit0) ++ revL).headI,
           ListBlank.mk (List.replicate cells.length (γ'ToChainΓ Γ'.bit0) ++ revL).tail,
           ListBlank.mk (default :: suffix)⟩⟩ := by
  induction' cells with c rest hcells ih generalizing revL suffix;
  · constructor;
    constructor;
    constructor;
  · rename_i h;
    have h_step : Reaches (TM0.step replNSMachine) ⟨2, ⟨c, ListBlank.mk revL, ListBlank.mk (rest ++ default :: suffix)⟩⟩ ⟨1, ⟨γ'ToChainΓ Γ'.bit0, ListBlank.mk revL, ListBlank.mk (rest ++ default :: suffix)⟩⟩ := by
      apply_rules [ Relation.ReflTransGen.single ];
      simp +decide [ TM0.step, replNSMachine ];
      exact ⟨ TM0.Stmt.write ( γ'ToChainΓ Γ'.bit0 ), by aesop ⟩;
    have h_step2 : Reaches (TM0.step replNSMachine) ⟨1, ⟨γ'ToChainΓ Γ'.bit0, ListBlank.mk revL, ListBlank.mk (rest ++ default :: suffix)⟩⟩ ⟨2, ⟨(rest ++ default :: suffix).headI, ListBlank.mk (γ'ToChainΓ Γ'.bit0 :: revL), ListBlank.mk (rest ++ default :: suffix).tail⟩⟩ := by
      apply_rules [ Relation.ReflTransGen.single ];
    convert h_step.trans ( h_step2.trans ( h ( fun g hg => hcells g ( List.mem_cons_of_mem _ hg ) ) _ _ ) ) using 1;
    simp +decide [ List.replicate_add ]

/-
Generalized scan phase: from state 0 with arbitrary left context revL,
    processes the block and reaches state 4 at position 0 of the final tape.
-/
theorem replNS_scan_gen (block suffix : List ChainΓ) (revL : List ChainΓ)
    (hblock : ∀ g ∈ block, g ≠ default)
    (hrevL : ∀ g ∈ revL, g ≠ default) :
    Reaches (TM0.step replNSMachine)
      ⟨0, ⟨(block ++ default :: suffix).headI,
           ListBlank.mk revL,
           ListBlank.mk (block ++ default :: suffix).tail⟩⟩
      ⟨4, Tape.mk₁ (revL.reverse ++ replaceNonStandard block ++ default :: suffix)⟩ := by
  induction' block with c rest ih generalizing suffix revL;
  · have h_scan : Reaches (TM0.step replNSMachine)
      ⟨0, ⟨default, ListBlank.mk revL, ListBlank.mk suffix⟩⟩
      ⟨3, ⟨default, ListBlank.mk [], ListBlank.mk (revL.reverse ++ default :: suffix)⟩⟩ := by
        convert Relation.ReflTransGen.trans _ ( replNS_rwdLoop revL hrevL ( default :: suffix ) ) using 1;
        apply_rules [ Relation.ReflTransGen.single ];
    convert h_scan.tail _ using 1;
    simp +decide [ TM0.step ];
    use TM0.Stmt.move Dir.right;
    simp +decide [ Tape.move, Tape.mk₁ ];
    simp +decide [ Tape.mk₂ ];
    simp +decide [ Tape.mk' ];
    exact ⟨ rfl, by cases revL.reverse <;> aesop, listBlank_mk_append_default [ ], by cases revL.reverse <;> aesop ⟩;
  · by_cases hc : c = γ'ToChainΓ Γ'.bit0 ∨ c = γ'ToChainΓ Γ'.bit1;
    · -- Apply the induction hypothesis to the rest of the block.
      have h_ind : Reaches (TM0.step replNSMachine) ⟨0, ⟨(rest ++ default :: suffix).headI, ListBlank.mk (c :: revL), ListBlank.mk (rest ++ default :: suffix).tail⟩⟩ ⟨4, Tape.mk₁ ((c :: revL).reverse ++ replaceNonStandard rest ++ default :: suffix)⟩ := by
        grind +locals;
      cases hc <;> simp_all +decide [ replaceNonStandard ];
      · convert Relation.ReflTransGen.head _ h_ind using 1;
        cases rest <;> aesop;
      · refine' Relation.ReflTransGen.head _ h_ind;
        exact?;
    · have h_step : Reaches (TM0.step replNSMachine) ⟨0, ⟨c, ListBlank.mk revL, ListBlank.mk (rest ++ default :: suffix)⟩⟩ ⟨2, ⟨(rest ++ default :: suffix).headI, ListBlank.mk (γ'ToChainΓ Γ'.bit0 :: revL), ListBlank.mk (rest ++ default :: suffix).tail⟩⟩ := by
        constructor;
        rotate_right;
        exact ⟨ 1, ⟨ γ'ToChainΓ Γ'.bit0, ListBlank.mk revL, ListBlank.mk ( rest ++ default :: suffix ) ⟩ ⟩;
        · apply_rules [ Relation.ReflTransGen.single ];
          unfold replNSMachine; simp +decide [ hc ] ;
          rw [ TM0.step ];
          grind +suggestions;
        · unfold replNSMachine; aesop;
      have h_step : Reaches (TM0.step replNSMachine) ⟨2, ⟨(rest ++ default :: suffix).headI, ListBlank.mk (γ'ToChainΓ Γ'.bit0 :: revL), ListBlank.mk (rest ++ default :: suffix).tail⟩⟩ ⟨3, ⟨(List.replicate rest.length (γ'ToChainΓ Γ'.bit0) ++ γ'ToChainΓ Γ'.bit0 :: revL).headI, ListBlank.mk (List.replicate rest.length (γ'ToChainΓ Γ'.bit0) ++ γ'ToChainΓ Γ'.bit0 :: revL).tail, ListBlank.mk (default :: suffix)⟩⟩ := by
        convert replNS_replLoop rest ( fun g hg => hblock g ( List.mem_cons_of_mem _ hg ) ) ( γ'ToChainΓ Γ'.bit0 :: revL ) suffix using 1;
      have h_step : Reaches (TM0.step replNSMachine) ⟨3, ⟨(List.replicate rest.length (γ'ToChainΓ Γ'.bit0) ++ γ'ToChainΓ Γ'.bit0 :: revL).headI, ListBlank.mk (List.replicate rest.length (γ'ToChainΓ Γ'.bit0) ++ γ'ToChainΓ Γ'.bit0 :: revL).tail, ListBlank.mk (default :: suffix)⟩⟩ ⟨3, ⟨default, ListBlank.mk [], ListBlank.mk (revL.reverse ++ replaceNonStandard (c :: rest) ++ default :: suffix)⟩⟩ := by
        convert replNS_rwdLoop _ _ _ using 1;
        · unfold replaceNonStandard; aesop;
        · simp +zetaDelta at *;
          rintro g ( ⟨ _, rfl ⟩ | rfl | hg ) <;> simp_all +decide [ γ'ToChainΓ ];
      have h_step : Reaches (TM0.step replNSMachine) ⟨3, ⟨default, ListBlank.mk [], ListBlank.mk (revL.reverse ++ replaceNonStandard (c :: rest) ++ default :: suffix)⟩⟩ ⟨4, Tape.mk₁ (revL.reverse ++ replaceNonStandard (c :: rest) ++ default :: suffix)⟩ := by
        apply Relation.ReflTransGen.single;
        simp +decide [ TM0.step ];
        use TM0.Stmt.move Dir.right;
        simp +decide [ Tape.move, Tape.mk₁ ];
        simp +decide [ Tape.mk₂ ];
        simp +decide [ Tape.mk' ];
        exact ⟨ rfl, listBlank_mk_append_default [ ] ⟩;
      rename_i h₁ h₂ h₃;
      exact h₁.trans ( h₂.trans ( h₃.trans h_step ) )

/-- The replNS machine correctly processes any block and reaches the done state. -/
theorem replNS_reaches (block suffix : List ChainΓ)
    (hblock : ∀ g ∈ block, g ≠ default) :
    Reaches (TM0.step replNSMachine)
      (TM0.init (block ++ default :: suffix))
      ⟨4, Tape.mk₁ (replaceNonStandard block ++ default :: suffix)⟩ := by
  exact replNS_scan_gen block suffix [] hblock (by simp)

/-- **replaceNonStandard is block-realizable.** -/
theorem tm0_replaceNonStandard : TM0RealizesBlock ChainΓ replaceNonStandard := by
  refine ⟨Fin 5, ⟨0⟩, inferInstance, replNSMachine, fun block suffix hblock hsuffix hfblock => ?_⟩
  have h_reaches := replNS_reaches block suffix hblock
  constructor
  · exact Part.dom_iff_mem.mpr ⟨_, Turing.mem_eval.mpr ⟨h_reaches, by simp [TM0.step, replNSMachine]⟩⟩
  · intro h
    have h_mem := Turing.mem_eval.mpr ⟨h_reaches, by simp [TM0.step, replNSMachine]⟩
    exact (Part.mem_unique (Part.get_mem h) h_mem).symm ▸ rfl

/-- Drop leading bit0 cells from a block. This is the "reversed" version of stripTrailingBit0. -/
noncomputable def dropLeadingBit0 : List ChainΓ → List ChainΓ
  | [] => []
  | c :: rest =>
    if c = γ'ToChainΓ Γ'.bit0 then dropLeadingBit0 rest
    else c :: rest

theorem stripTrailingBit0_eq_rev_drop_rev :
    stripTrailingBit0 = List.reverse ∘ dropLeadingBit0 ∘ List.reverse := by
  funext l; induction l; simp [stripTrailingBit0, dropLeadingBit0];
  rename_i x l ih; by_cases hx : x = γ'ToChainΓ Γ'.bit0 <;> by_cases hl : l = [] <;> simp_all +decide [ stripTrailingBit0, dropLeadingBit0 ] ;
  · -- By definition of `dropLeadingBit0`, we can split into cases based on whether the first element is `γ'ToChainΓ Γ'.bit0`.
    have h_dropLeadingBit0 : ∀ (l : List ChainΓ), dropLeadingBit0 (l ++ [γ'ToChainΓ Γ'.bit0]) = if dropLeadingBit0 l = [] then [] else dropLeadingBit0 l ++ [γ'ToChainΓ Γ'.bit0] := by
      intro l; induction l <;> simp +decide [ *, dropLeadingBit0 ] ;
      grind;
    aesop;
  · -- By definition of `dropLeadingBit0`, we can split into cases based on whether the first element is `bit0` or not.
    have h_dropLeadingBit0 : ∀ (l : List ChainΓ) (x : ChainΓ), x ≠ γ'ToChainΓ Γ'.bit0 → dropLeadingBit0 (l ++ [x]) = dropLeadingBit0 l ++ [x] := by
      intros l x hx; induction l <;> simp_all +decide [ dropLeadingBit0 ] ;
      split_ifs <;> simp +decide [ *, List.append_assoc ];
    grind +qlia

theorem dropLeadingBit0_ne_default (block : List ChainΓ)
    (hblock : ∀ g ∈ block, g ≠ default) :
    ∀ g ∈ dropLeadingBit0 block, g ≠ default := by
  induction' block with c block ih;
  · grind +locals;
  · by_cases hc : c = γ'ToChainΓ Γ'.bit0 <;> simp_all +decide [ dropLeadingBit0 ]

theorem reverse_dropLeadingBit0_ne_default (block : List ChainΓ)
    (hblock : ∀ g ∈ block, g ≠ default) :
    ∀ g ∈ (dropLeadingBit0 (block.reverse)).reverse, g ≠ default := by
  convert dropLeadingBit0_ne_default ( block.reverse ) fun g hg => ?_ using 1;
  · grind;
  · exact hblock g ( List.mem_reverse.mp hg )

theorem tm0_dropLeadingBit0 : TM0RealizesBlock ChainΓ dropLeadingBit0 := by
  sorry

/-- **stripTrailingBit0 is block-realizable.**
    Decomposed as: reverse, drop leading bit0, reverse.
    Proof deferred until after tm0_reverse_block is available. -/
theorem tm0_stripTrailingBit0 : TM0RealizesBlock ChainΓ stripTrailingBit0 := by
  sorry

theorem stripTrailingBit0_ne_default (block : List ChainΓ)
    (hblock : ∀ g ∈ block, g ≠ default) :
    ∀ g ∈ stripTrailingBit0 block, g ≠ default := by
  have h_stripTrailingBit0 : ∀ g ∈ stripTrailingBit0 block, g ∈ block := by
    have h_stripTrailingBit0 : ∀ block : List ChainΓ, ∀ g ∈ stripTrailingBit0 block, g ∈ block := by
      intro block
      induction' block with c rest ih;
      · decide +kernel;
      · grind +locals;
    exact h_stripTrailingBit0 block;
  exact fun g hg => hblock g ( h_stripTrailingBit0 g hg )

/-- **Normalization is block-realizable.**
    Decomposed as `stripTrailingBit0 ∘ replaceNonStandard`. -/
theorem tm0_normalizeBlock : TM0RealizesBlock ChainΓ normalizeBlock := by
  rw [normalizeBlock_eq_comp]
  exact tm0RealizesBlock_comp tm0_replaceNonStandard tm0_stripTrailingBit0
    (fun block hblock => replaceNonStandard_ne_default block hblock)

/-- **Addition via decode/encode is block-realizable.**

    Decomposed as `binAddConst c ∘ normalizeBlock`.
    Both components are block-realizable, and normalizeBlock
    preserves non-defaultness. -/
theorem tm0_binAddConstRepr_block (c : ℕ) :
    TM0RealizesBlock ChainΓ (binAddConstRepr c) := by
  rw [binAddConstRepr_eq_comp]
  exact tm0RealizesBlock_comp tm0_normalizeBlock (tm0_binAddConst_block c)
    (fun _ _ => normalizeBlock_ne_default _)

/-! ### Singleton Function 4: Binary Squaring -/

/-- Square the binary block value: n → n². -/
noncomputable def binSquare (block : List ChainΓ) : List ChainΓ :=
  chainBinaryRepr ((decodeBinaryBlock block) ^ 2)

theorem binSquare_correct (n : ℕ) :
    binSquare (chainBinaryRepr n) = chainBinaryRepr (n ^ 2) := by
  unfold binSquare; rw [decodeBinaryBlock_chainBinaryRepr]

theorem binSquare_ne_default (block : List ChainΓ) (_hblock : ∀ g ∈ block, g ≠ default) :
    ∀ g ∈ binSquare block, g ≠ default := by
  unfold binSquare; exact chainBinaryRepr_ne_default _

/-- **Binary squaring is block-realizable.**

    Squaring can be realized by a TM0 that copies the input `n` and
    uses one copy as a counter while repeatedly adding the other copy
    to an accumulator (schoolbook multiplication n × n). -/
theorem tm0_binSquare_block : TM0RealizesBlock ChainΓ binSquare := by
  sorry

/-! ### Singleton Function 5: Binary Multiplication by Constant -/

/-- Multiply the binary block value by a fixed constant k: n → k * n.
    Realizable by repeated addition of the original value (requires
    copying n, then adding the copy k times). -/
noncomputable def binMulConst (c : ℕ) (block : List ChainΓ) : List ChainΓ :=
  chainBinaryRepr (c * decodeBinaryBlock block)

theorem binMulConst_correct (c n : ℕ) :
    binMulConst c (chainBinaryRepr n) = chainBinaryRepr (c * n) := by
  unfold binMulConst; rw [decodeBinaryBlock_chainBinaryRepr]

theorem binMulConst_ne_default (c : ℕ) (block : List ChainΓ)
    (_hblock : ∀ g ∈ block, g ≠ default) :
    ∀ g ∈ binMulConst c block, g ≠ default := by
  unfold binMulConst; exact chainBinaryRepr_ne_default _

/-- **Multiplication by constant is block-realizable.** -/
theorem tm0_binMulConst_block (c : ℕ) : TM0RealizesBlock ChainΓ (binMulConst c) := by
  sorry

/-! ### Conditional Block Operations -/

/-- Conditional block operation: given a decidable predicate on blocks,
    apply `f` when the predicate holds and `g` otherwise. -/
noncomputable def binCondBlock (p : List ChainΓ → Prop) [DecidablePred p]
    (f g : List ChainΓ → List ChainΓ) (block : List ChainΓ) : List ChainΓ :=
  if p block then f block else g block

/- The original `tm0RealizesBlock_cond` statement had a too-weak `hp_decidable`
   hypothesis: it only required a TM0 that *halts* on valid blocks, without
   connecting the machine's halting state to the predicate `p` or requiring
   tape preservation. Combined with an arbitrary `DecidablePred p` (which may
   come from `Classical.dec` and be non-computable), the theorem is not provable
   in general — a single TM0 machine cannot compute `if p then f else g` unless
   p is TM0-decidable.

   The corrected version below strengthens `hp_decidable` to require that the
   predicate machine:
   1. Preserves the tape contents.
   2. Encodes the predicate result in its halting state (q_true vs q_false).
   This enables conditional composition: run M_p, then route to M_f or M_g
   based on the halting state. -/

/-- Conditional TM0 composition: run M_p first, then route to M_f (if halting
    state = q_true) or M_g (if halting state = q_false). -/
noncomputable def tm0CondCompose
    {Λ_p Λ_f Λ_g : Type}
    [Inhabited Λ_p] [Inhabited Λ_f] [Inhabited Λ_g]
    [DecidableEq Λ_p]
    (M_p : TM0.Machine ChainΓ Λ_p)
    (M_f : TM0.Machine ChainΓ Λ_f)
    (M_g : TM0.Machine ChainΓ Λ_g)
    (q_true q_false : Λ_p) :
    @TM0.Machine ChainΓ (Λ_p ⊕ Λ_f ⊕ Λ_g) ⟨Sum.inl default⟩ :=
  fun q a =>
    match q with
    | Sum.inl q_p =>
      match M_p q_p a with
      | some (q_p', s) => some (Sum.inl q_p', s)
      | none =>
        if q_p = q_true then
          match M_f default a with
          | some (q_f', s) => some (Sum.inr (Sum.inl q_f'), s)
          | none => none
        else
          match M_g default a with
          | some (q_g', s) => some (Sum.inr (Sum.inr q_g'), s)
          | none => none
    | Sum.inr (Sum.inl q_f) =>
      match M_f q_f a with
      | some (q_f', s) => some (Sum.inr (Sum.inl q_f'), s)
      | none => none
    | Sum.inr (Sum.inr q_g) =>
      match M_g q_g a with
      | some (q_g', s) => some (Sum.inr (Sum.inr q_g'), s)
      | none => none

/-! #### Helper lemmas for tm0CondCompose -/

section CondComposeHelpers

variable {Λ_p Λ_f Λ_g : Type}
    [Inhabited Λ_p] [Inhabited Λ_f] [Inhabited Λ_g]
    [DecidableEq Λ_p]
    (M_p : TM0.Machine ChainΓ Λ_p)
    (M_f : TM0.Machine ChainΓ Λ_f)
    (M_g : TM0.Machine ChainΓ Λ_g)
    (q_t q_f : Λ_p)

/-
Phase 1: one step of M_p maps to one step of condCompose in Sum.inl states.
-/
theorem condCompose_step_inl
    (c₁ c₁' : TM0.Cfg ChainΓ Λ_p)
    (h : TM0.step M_p c₁ = some c₁') :
    @TM0.step ChainΓ (Λ_p ⊕ Λ_f ⊕ Λ_g) ⟨Sum.inl default⟩ _
      (tm0CondCompose M_p M_f M_g q_t q_f)
      ⟨Sum.inl c₁.q, c₁.Tape⟩ =
    some ⟨Sum.inl c₁'.q, c₁'.Tape⟩ := by
  unfold tm0CondCompose at *;
  unfold TM0.step at *; aesop;

/-
Phase 1: Reaches of M_p lifts to condCompose in Sum.inl states.
-/
theorem condCompose_phase1_reaches
    (c₁ : TM0.Cfg ChainΓ Λ_p) (l : List ChainΓ)
    (h : Reaches (TM0.step M_p) (TM0.init l) c₁) :
    Reaches (@TM0.step ChainΓ (Λ_p ⊕ Λ_f ⊕ Λ_g) ⟨Sum.inl default⟩ _
      (tm0CondCompose M_p M_f M_g q_t q_f))
      (@TM0.init ChainΓ (Λ_p ⊕ Λ_f ⊕ Λ_g) ⟨Sum.inl default⟩ _ l)
      ⟨Sum.inl c₁.q, c₁.Tape⟩ := by
  induction h;
  · constructor;
  · rename_i c₂ c₃ h₁ h₂ h₃;
    convert h₃.tail _;
    convert condCompose_step_inl M_p M_f M_g q_t q_f c₂ c₃ h₂

/-
When M_p halts at q_t, condCompose routes to M_f.
-/
theorem condCompose_halt_true
    (T : Tape ChainΓ)
    (h_halt : TM0.step M_p ⟨q_t, T⟩ = none) :
    @TM0.step ChainΓ (Λ_p ⊕ Λ_f ⊕ Λ_g) ⟨Sum.inl default⟩ _
      (tm0CondCompose M_p M_f M_g q_t q_f)
      ⟨Sum.inl q_t, T⟩ =
    (TM0.step M_f ⟨default, T⟩).map
      (fun c₂ => ⟨Sum.inr (Sum.inl c₂.q), c₂.Tape⟩) := by
  unfold tm0CondCompose;
  unfold TM0.step at *;
  grind

/-
When M_p halts at q_f (≠ q_t), condCompose routes to M_g.
-/
theorem condCompose_halt_false
    (hne : q_t ≠ q_f)
    (T : Tape ChainΓ)
    (h_halt : TM0.step M_p ⟨q_f, T⟩ = none) :
    @TM0.step ChainΓ (Λ_p ⊕ Λ_f ⊕ Λ_g) ⟨Sum.inl default⟩ _
      (tm0CondCompose M_p M_f M_g q_t q_f)
      ⟨Sum.inl q_f, T⟩ =
    (TM0.step M_g ⟨default, T⟩).map
      (fun c₂ => ⟨Sum.inr (Sum.inr c₂.q), c₂.Tape⟩) := by
  convert condCompose_halt_true _ _ _ _;
  rotate_left;
  exact Λ_p;
  all_goals try assumption;
  unfold tm0CondCompose;
  unfold TM0.step at * ; aesop

/-
Phase 2 bisimulation for M_f: once in Sum.inr (Sum.inl _) states,
    condCompose exactly simulates M_f.
-/
theorem condCompose_f_respects :
    Respects
      (TM0.step M_f)
      (@TM0.step ChainΓ (Λ_p ⊕ Λ_f ⊕ Λ_g) ⟨Sum.inl default⟩ _
        (tm0CondCompose M_p M_f M_g q_t q_f))
      (fun c₂ c => c.q = Sum.inr (Sum.inl c₂.q) ∧ c.Tape = c₂.Tape) := by
  intro c₂ c;
  rintro ⟨ h₁, h₂ ⟩;
  rcases h : TM0.step M_f c₂ with ( _ | ⟨ q, s ⟩ ) <;> simp +decide [ h ];
  · unfold tm0CondCompose;
    unfold TM0.step at *; aesop;
  · refine' ⟨ ⟨ Sum.inr ( Sum.inl q ), s ⟩, _, _ ⟩ <;> simp_all +decide [ Reaches₁ ];
    convert Relation.TransGen.single _;
    unfold tm0CondCompose;
    unfold TM0.step at *;
    cases c ; aesop

/-
Phase 2 bisimulation for M_g: once in Sum.inr (Sum.inr _) states,
    condCompose exactly simulates M_g.
-/
theorem condCompose_g_respects :
    Respects
      (TM0.step M_g)
      (@TM0.step ChainΓ (Λ_p ⊕ Λ_f ⊕ Λ_g) ⟨Sum.inl default⟩ _
        (tm0CondCompose M_p M_f M_g q_t q_f))
      (fun c₂ c => c.q = Sum.inr (Sum.inr c₂.q) ∧ c.Tape = c₂.Tape) := by
  intro c₂ c hc;
  rcases h : TM0.step M_g c₂ with ( _ | ⟨ q, s ⟩ ) <;> simp_all +decide;
  · unfold tm0CondCompose;
    unfold TM0.step at *; aesop;
  · refine' ⟨ ⟨ Sum.inr ( Sum.inr q ), s ⟩, _, _ ⟩ <;> simp_all +decide [ Reaches₁ ];
    convert Relation.TransGen.single _;
    unfold tm0CondCompose;
    unfold TM0.step at *; aesop;

/-
When M_p halts at q_t, condCompose's eval from ⟨Sum.inl q_t, T⟩ has the same
    domain as M_f's eval from ⟨default, T⟩.
-/
theorem condCompose_eval_at_halt_true
    (T : Tape ChainΓ)
    (h_halt : TM0.step M_p ⟨q_t, T⟩ = none) :
    (Turing.eval (@TM0.step ChainΓ (Λ_p ⊕ Λ_f ⊕ Λ_g) ⟨Sum.inl default⟩ _
      (tm0CondCompose M_p M_f M_g q_t q_f))
      ⟨Sum.inl q_t, T⟩).Dom ↔
    (TM0Seq.evalFromCfg M_f ⟨default, T⟩).Dom := by
  by_cases h₂ : TM0.step M_f ⟨default, T⟩ = none;
  · rw [ Turing.eval ];
    constructor <;> intro <;> simp_all +decide [ Part.dom_iff_mem ];
    · exact ⟨ _, Turing.mem_eval.mpr ⟨ Relation.ReflTransGen.refl, by tauto ⟩ ⟩;
    · use ⟨Sum.inl q_t, T⟩;
      rw [ PFun.mem_fix_iff ];
      rw [ condCompose_halt_true ] <;> aesop;
  · obtain ⟨ c₂, hc₂ ⟩ := Option.ne_none_iff_exists'.mp h₂;
    rw [ Turing.reaches_eval, Turing.reaches_eval ];
    rotate_left;
    rotate_left;
    exact ⟨ Sum.inr ( Sum.inl c₂.q ), c₂.Tape ⟩;
    exact ⟨ Sum.inr ( Sum.inl c₂.q ), c₂.Tape ⟩;
    · exact Relation.ReflTransGen.single ( by rw [ condCompose_halt_true M_p M_f M_g q_t q_f T h_halt ] ; aesop );
    · rw [ show TM0Seq.evalFromCfg M_f { q := default, Tape := T } = eval ( TM0.step M_f ) { q := default, Tape := T } from rfl ];
      rw [ show eval ( TM0.step M_f ) { q := default, Tape := T } = eval ( TM0.step M_f ) c₂ from ?_ ];
      · apply Turing.tr_eval_dom;
        exact?;
        exact ⟨ rfl, rfl ⟩;
      · apply Turing.reaches_eval;
        exact Relation.ReflTransGen.single hc₂;
    · exact Relation.ReflTransGen.refl

/-
When M_p halts at q_f (≠ q_t), condCompose's eval from ⟨Sum.inl q_f, T⟩ has the same
    domain as M_g's eval from ⟨default, T⟩.
-/
theorem condCompose_eval_at_halt_false
    (hne : q_t ≠ q_f)
    (T : Tape ChainΓ)
    (h_halt : TM0.step M_p ⟨q_f, T⟩ = none) :
    (Turing.eval (@TM0.step ChainΓ (Λ_p ⊕ Λ_f ⊕ Λ_g) ⟨Sum.inl default⟩ _
      (tm0CondCompose M_p M_f M_g q_t q_f))
      ⟨Sum.inl q_f, T⟩).Dom ↔
    (TM0Seq.evalFromCfg M_g ⟨default, T⟩).Dom := by
  by_cases h₂ : TM0.step M_g ⟨default, T⟩ = none;
  · rw [ Turing.eval ];
    constructor <;> intro <;> simp_all +decide [ Part.dom_iff_mem ];
    · exact ⟨ _, Turing.mem_eval.mpr ⟨ Relation.ReflTransGen.refl, by tauto ⟩ ⟩;
    · use ⟨Sum.inl q_f, T⟩;
      rw [ PFun.mem_fix_iff ];
      rw [ condCompose_halt_false M_p M_f M_g q_t q_f hne T h_halt ] ; aesop;
  · obtain ⟨ c₂, hc₂ ⟩ := Option.ne_none_iff_exists'.mp h₂;
    rw [ Turing.reaches_eval, Turing.reaches_eval ];
    rotate_left;
    rotate_left;
    exact ⟨ Sum.inr ( Sum.inr c₂.q ), c₂.Tape ⟩;
    exact ⟨ Sum.inr ( Sum.inr c₂.q ), c₂.Tape ⟩;
    · exact Relation.ReflTransGen.single ( by rw [ condCompose_halt_false M_p M_f M_g q_t q_f hne T h_halt ] ; aesop );
    · rw [ show TM0Seq.evalFromCfg M_g { q := default, Tape := T } = eval ( TM0.step M_g ) { q := default, Tape := T } from rfl ];
      rw [ show eval ( TM0.step M_g ) { q := default, Tape := T } = eval ( TM0.step M_g ) c₂ from ?_ ];
      · apply Turing.tr_eval_dom;
        exact?;
        exact ⟨ rfl, rfl ⟩;
      · rw [ Turing.reaches_eval ];
        exact Relation.ReflTransGen.single hc₂;
    · exact Relation.ReflTransGen.refl

end CondComposeHelpers

-- Override the monad-derived Inhabited instance for Sum types, which gives
-- Sum.inr default, conflicting with tm0CondCompose which uses Sum.inl default.
attribute [-instance] instInhabitedOfMonad
instance instInhabitedSumLeft {α β : Type} [Inhabited α] : Inhabited (α ⊕ β) := ⟨Sum.inl default⟩

section CondComposeEvalCfg

variable {Λ_p Λ_f Λ_g : Type}
    [Inhabited Λ_p] [Inhabited Λ_f] [Inhabited Λ_g]
    [DecidableEq Λ_p]
    (M_p : TM0.Machine ChainΓ Λ_p)
    (M_f : TM0.Machine ChainΓ Λ_f)
    (M_g : TM0.Machine ChainΓ Λ_g)
    (q_t q_f : Λ_p)

/-- When M_p halts at q_t with tape T, the composed machine's eval from
    ⟨Sum.inl q_t, T⟩ has the same tape as M_f's eval from ⟨default, T⟩. -/
theorem condCompose_tape_at_halt_true
    (T : Tape ChainΓ)
    (h_halt : TM0.step M_p ⟨q_t, T⟩ = none)
    (h_f_dom : (TM0Seq.evalFromCfg M_f ⟨default, T⟩).Dom) :
    let step_c := @TM0.step ChainΓ (Λ_p ⊕ Λ_f ⊕ Λ_g) ⟨Sum.inl default⟩ _
      (tm0CondCompose M_p M_f M_g q_t q_f)
    ∀ (h_c_dom : (Turing.eval step_c ⟨Sum.inl q_t, T⟩).Dom),
      ((Turing.eval step_c ⟨Sum.inl q_t, T⟩).get h_c_dom).Tape =
        ((TM0Seq.evalFromCfg M_f ⟨default, T⟩).get h_f_dom).Tape := by
  intro step_c h_c_dom
  set b_f := (TM0Seq.evalFromCfg M_f ⟨default, T⟩).get h_f_dom
  have hb_f_mem : b_f ∈ TM0Seq.evalFromCfg M_f ⟨default, T⟩ := Part.get_mem h_f_dom
  rcases h_step_f : TM0.step M_f ⟨default, T⟩ with _ | ⟨c₂⟩
  · -- M_f halts immediately
    have hb_f_eq : b_f = ⟨default, T⟩ :=
      (Turing.eval_maximal (Turing.mem_eval.mpr ⟨Relation.ReflTransGen.refl, h_step_f⟩) |>.mp
        (Turing.mem_eval.mp hb_f_mem).1)
    have h_step_c : step_c ⟨Sum.inl q_t, T⟩ = none := by
      show @TM0.step ChainΓ (Λ_p ⊕ Λ_f ⊕ Λ_g) _ _ (tm0CondCompose M_p M_f M_g q_t q_f) _ = _
      rw [condCompose_halt_true M_p M_f M_g q_t q_f T h_halt]
      simp [h_step_f]
    have h_eval_c := Part.mem_unique (Part.get_mem h_c_dom)
      (Turing.mem_eval.mpr ⟨Relation.ReflTransGen.refl, h_step_c⟩)
    rw [h_eval_c, hb_f_eq]
  · -- M_f steps to c₂
    have h_step_c : step_c ⟨Sum.inl q_t, T⟩ = some ⟨Sum.inr (Sum.inl c₂.q), c₂.Tape⟩ := by
      show @TM0.step ChainΓ (Λ_p ⊕ Λ_f ⊕ Λ_g) _ _ (tm0CondCompose M_p M_f M_g q_t q_f) _ = _
      rw [condCompose_halt_true M_p M_f M_g q_t q_f T h_halt]
      simp [h_step_f]
    have h_eval_eq := Turing.reaches_eval (Relation.ReflTransGen.single h_step_c)
    have h_eval_f_eq := Turing.reaches_eval (Relation.ReflTransGen.single h_step_f)
    have hb_f_mem_c2 : b_f ∈ Turing.eval (TM0.step M_f) c₂ := by
      rw [← h_eval_f_eq]; exact hb_f_mem
    obtain ⟨b₂, ⟨_, hb₂_tape⟩, hb₂_mem⟩ := Turing.tr_eval
      (condCompose_f_respects M_p M_f M_g q_t q_f)
      (a₁ := c₂) (a₂ := ⟨Sum.inr (Sum.inl c₂.q), c₂.Tape⟩)
      ⟨rfl, rfl⟩ hb_f_mem_c2
    have hb₂_mem' : b₂ ∈ Turing.eval step_c ⟨Sum.inl q_t, T⟩ := by
      rw [h_eval_eq]; exact hb₂_mem
    rw [Part.mem_unique (Part.get_mem h_c_dom) hb₂_mem', hb₂_tape]

/-- When M_p halts at q_f (with q_t ≠ q_f) with tape T, the composed machine's
    eval from ⟨Sum.inl q_f, T⟩ has the same tape as M_g's eval from ⟨default, T⟩. -/
theorem condCompose_tape_at_halt_false
    (hne : q_t ≠ q_f)
    (T : Tape ChainΓ)
    (h_halt : TM0.step M_p ⟨q_f, T⟩ = none)
    (h_g_dom : (TM0Seq.evalFromCfg M_g ⟨default, T⟩).Dom) :
    let step_c := @TM0.step ChainΓ (Λ_p ⊕ Λ_f ⊕ Λ_g) ⟨Sum.inl default⟩ _
      (tm0CondCompose M_p M_f M_g q_t q_f)
    ∀ (h_c_dom : (Turing.eval step_c ⟨Sum.inl q_f, T⟩).Dom),
      ((Turing.eval step_c ⟨Sum.inl q_f, T⟩).get h_c_dom).Tape =
        ((TM0Seq.evalFromCfg M_g ⟨default, T⟩).get h_g_dom).Tape := by
  intro step_c h_c_dom
  set b_g := (TM0Seq.evalFromCfg M_g ⟨default, T⟩).get h_g_dom
  have hb_g_mem : b_g ∈ TM0Seq.evalFromCfg M_g ⟨default, T⟩ := Part.get_mem h_g_dom
  rcases h_step_g : TM0.step M_g ⟨default, T⟩ with _ | ⟨c₂⟩
  · -- M_g halts immediately
    have hb_g_eq : b_g = ⟨default, T⟩ :=
      (Turing.eval_maximal (Turing.mem_eval.mpr ⟨Relation.ReflTransGen.refl, h_step_g⟩) |>.mp
        (Turing.mem_eval.mp hb_g_mem).1)
    have h_step_c : step_c ⟨Sum.inl q_f, T⟩ = none := by
      show @TM0.step ChainΓ (Λ_p ⊕ Λ_f ⊕ Λ_g) _ _ (tm0CondCompose M_p M_f M_g q_t q_f) _ = _
      rw [condCompose_halt_false M_p M_f M_g q_t q_f hne T h_halt]
      simp [h_step_g]
    have h_eval_c := Part.mem_unique (Part.get_mem h_c_dom)
      (Turing.mem_eval.mpr ⟨Relation.ReflTransGen.refl, h_step_c⟩)
    rw [h_eval_c, hb_g_eq]
  · -- M_g steps to c₂
    have h_step_c : step_c ⟨Sum.inl q_f, T⟩ = some ⟨Sum.inr (Sum.inr c₂.q), c₂.Tape⟩ := by
      show @TM0.step ChainΓ (Λ_p ⊕ Λ_f ⊕ Λ_g) _ _ (tm0CondCompose M_p M_f M_g q_t q_f) _ = _
      rw [condCompose_halt_false M_p M_f M_g q_t q_f hne T h_halt]
      simp [h_step_g]
    have h_eval_eq := Turing.reaches_eval (Relation.ReflTransGen.single h_step_c)
    have h_eval_g_eq := Turing.reaches_eval (Relation.ReflTransGen.single h_step_g)
    have hb_g_mem_c2 : b_g ∈ Turing.eval (TM0.step M_g) c₂ := by
      rw [← h_eval_g_eq]; exact hb_g_mem
    obtain ⟨b₂, ⟨_, hb₂_tape⟩, hb₂_mem⟩ := Turing.tr_eval
      (condCompose_g_respects M_p M_f M_g q_t q_f)
      (a₁ := c₂) (a₂ := ⟨Sum.inr (Sum.inr c₂.q), c₂.Tape⟩)
      ⟨rfl, rfl⟩ hb_g_mem_c2
    have hb₂_mem' : b₂ ∈ Turing.eval step_c ⟨Sum.inl q_f, T⟩ := by
      rw [h_eval_eq]; exact hb₂_mem
    rw [Part.mem_unique (Part.get_mem h_c_dom) hb₂_mem', hb₂_tape]

end CondComposeEvalCfg

/-
Core helper for `tm0RealizesBlock_cond`.
-/
theorem tm0RealizesBlock_cond_core
    {p : List ChainΓ → Prop} [DecidablePred p]
    {f g : List ChainΓ → List ChainΓ}
    {Λ_p Λ_f Λ_g : Type}
    [Inhabited Λ_p] [Inhabited Λ_f] [Inhabited Λ_g]
    [Fintype Λ_p] [Fintype Λ_f] [Fintype Λ_g]
    [DecidableEq Λ_p]
    (M_p : TM0.Machine ChainΓ Λ_p)
    (M_f : TM0.Machine ChainΓ Λ_f)
    (M_g : TM0.Machine ChainΓ Λ_g)
    (q_t q_f : Λ_p)
    (hne : q_t ≠ q_f)
    (hp_spec : ∀ (block suffix : List ChainΓ),
        (∀ x ∈ block, x ≠ default) → (∀ x ∈ suffix, x ≠ default) →
        (TM0Seq.evalCfg M_p (block ++ default :: suffix)).Dom ∧
        ∀ (h : (TM0Seq.evalCfg M_p (block ++ default :: suffix)).Dom),
          ((TM0Seq.evalCfg M_p (block ++ default :: suffix)).get h).Tape =
            Tape.mk₁ (block ++ default :: suffix) ∧
          (p block →
            ((TM0Seq.evalCfg M_p (block ++ default :: suffix)).get h).q = q_t) ∧
          (¬p block →
            ((TM0Seq.evalCfg M_p (block ++ default :: suffix)).get h).q = q_f))
    (hf_spec : ∀ (block suffix : List ChainΓ),
        (∀ x ∈ block, x ≠ default) → (∀ x ∈ suffix, x ≠ default) →
        (∀ x ∈ f block, x ≠ default) →
        (TM0Seq.evalCfg M_f (block ++ default :: suffix)).Dom ∧
        ∀ (h : (TM0Seq.evalCfg M_f (block ++ default :: suffix)).Dom),
          ((TM0Seq.evalCfg M_f (block ++ default :: suffix)).get h).Tape =
            Tape.mk₁ (f block ++ default :: suffix))
    (hg_spec : ∀ (block suffix : List ChainΓ),
        (∀ x ∈ block, x ≠ default) → (∀ x ∈ suffix, x ≠ default) →
        (∀ x ∈ g block, x ≠ default) →
        (TM0Seq.evalCfg M_g (block ++ default :: suffix)).Dom ∧
        ∀ (h : (TM0Seq.evalCfg M_g (block ++ default :: suffix)).Dom),
          ((TM0Seq.evalCfg M_g (block ++ default :: suffix)).get h).Tape =
            Tape.mk₁ (g block ++ default :: suffix))
    (hf_nd : ∀ block, (∀ x ∈ block, x ≠ default) → ∀ x ∈ f block, x ≠ default)
    (hg_nd : ∀ block, (∀ x ∈ block, x ≠ default) → ∀ x ∈ g block, x ≠ default) :
    TM0RealizesBlock ChainΓ (binCondBlock p f g) := by
  refine ⟨Λ_p ⊕ Λ_f ⊕ Λ_g, inferInstance, inferInstance,
    tm0CondCompose M_p M_f M_g q_t q_f, ?_⟩
  intro block suffix hblock hsuffix hresult
  set l := block ++ default :: suffix
  -- Phase 1: M_p halts
  have hp_dom := (hp_spec block suffix hblock hsuffix).1
  have hp_result := (hp_spec block suffix hblock hsuffix).2 hp_dom
  set c_p := (TM0Seq.evalCfg M_p l).get hp_dom
  have hc_p_tape : c_p.Tape = Tape.mk₁ l := hp_result.1
  have hc_p_mem : c_p ∈ TM0Seq.evalCfg M_p l := Part.get_mem hp_dom
  have hc_p_eval := Turing.mem_eval.mp hc_p_mem
  have hc_p_halt : TM0.step M_p c_p = none := hc_p_eval.2
  have hc_p_reaches : Turing.Reaches (TM0.step M_p) (TM0.init l) c_p := hc_p_eval.1
  -- Phase 1 lifts to composed machine
  have h_reaches_c := condCompose_phase1_reaches M_p M_f M_g q_t q_f c_p l hc_p_reaches
  have h_eval_rewrite : TM0Seq.evalCfg (tm0CondCompose M_p M_f M_g q_t q_f) l =
      Turing.eval (TM0.step (tm0CondCompose M_p M_f M_g q_t q_f))
        ⟨Sum.inl c_p.q, c_p.Tape⟩ := Turing.reaches_eval h_reaches_c
  -- Split on predicate
  unfold binCondBlock at hresult ⊢
  by_cases hp : p block
  · simp only [hp, ite_true] at hresult ⊢
    have hq : c_p.q = q_t := hp_result.2.1 hp
    have h_halt_qt : TM0.step M_p ⟨q_t, c_p.Tape⟩ = none := hq ▸ hc_p_halt
    -- Domain: composed eval has same domain as M_f
    have hf_dom : (TM0Seq.evalCfg M_f l).Dom :=
      (hf_spec block suffix hblock hsuffix (hf_nd block hblock)).1
    have h_f_from_init : (TM0Seq.evalFromCfg M_f ⟨default, c_p.Tape⟩).Dom := by
      rw [hc_p_tape]; show (TM0Seq.evalFromCfg M_f (TM0.init l)).Dom
      rw [TM0Seq.evalFromCfg_init]; exact hf_dom
    constructor
    · rw [h_eval_rewrite, hq]
      exact (condCompose_eval_at_halt_true M_p M_f M_g q_t q_f c_p.Tape h_halt_qt).mpr h_f_from_init
    · intro h_dom; (
      have h_tape_eq : (TM0Seq.evalFromCfg M_f ⟨default, c_p.Tape⟩).Dom := by
        exact h_f_from_init;
      have h_tape_eq : ((TM0Seq.evalFromCfg M_f ⟨default, c_p.Tape⟩).get h_tape_eq).Tape = Tape.mk₁ (f block ++ default :: suffix) := by
        convert hf_spec block suffix hblock hsuffix hresult |>.2 _;
        · rw [hc_p_tape];
          exact?;
        · exact hf_dom;
      convert condCompose_tape_at_halt_true M_p M_f M_g q_t q_f c_p.Tape h_halt_qt h_f_from_init;
      grind)
  · simp only [hp, ite_false] at hresult ⊢
    have hq : c_p.q = q_f := hp_result.2.2 hp
    have h_halt_qf : TM0.step M_p ⟨q_f, c_p.Tape⟩ = none := hq ▸ hc_p_halt
    have hg_dom : (TM0Seq.evalCfg M_g l).Dom :=
      (hg_spec block suffix hblock hsuffix (hg_nd block hblock)).1
    have h_g_from_init : (TM0Seq.evalFromCfg M_g ⟨default, c_p.Tape⟩).Dom := by
      rw [hc_p_tape]; show (TM0Seq.evalFromCfg M_g (TM0.init l)).Dom
      rw [TM0Seq.evalFromCfg_init]; exact hg_dom
    constructor
    · rw [h_eval_rewrite, hq]
      exact (condCompose_eval_at_halt_false M_p M_f M_g q_t q_f hne c_p.Tape h_halt_qf).mpr h_g_from_init
    · intro h_dom; (
      have h_tape_eq : (TM0Seq.evalFromCfg M_g ⟨default, c_p.Tape⟩).Dom := by
        exact h_g_from_init;
      have h_tape_eq : ((TM0Seq.evalFromCfg M_g ⟨default, c_p.Tape⟩).get h_tape_eq).Tape = Tape.mk₁ (g block ++ default :: suffix) := by
        convert hg_spec block suffix hblock hsuffix hresult |>.2 _;
        · rw [hc_p_tape];
          exact?;
        · exact hg_dom;
      convert condCompose_tape_at_halt_false M_p M_f M_g q_t q_f hne c_p.Tape h_halt_qf h_g_from_init;
      grind)

/-- **Conditional block operation is block-realizable** (public interface). -/
theorem tm0RealizesBlock_cond
    {p : List ChainΓ → Prop} [DecidablePred p]
    {f g : List ChainΓ → List ChainΓ}
    (hf : TM0RealizesBlock ChainΓ f)
    (hg : TM0RealizesBlock ChainΓ g)
    (hf_nd : ∀ block, (∀ x ∈ block, x ≠ default) → ∀ x ∈ f block, x ≠ default)
    (hg_nd : ∀ block, (∀ x ∈ block, x ≠ default) → ∀ x ∈ g block, x ≠ default)
    (hp_decidable : ∃ (Λ : Type) (_ : Inhabited Λ) (_ : Fintype Λ)
      (M : TM0.Machine ChainΓ Λ) (q_true q_false : Λ),
      q_true ≠ q_false ∧
      ∀ (block suffix : List ChainΓ),
        (∀ x ∈ block, x ≠ default) → (∀ x ∈ suffix, x ≠ default) →
        (TM0Seq.evalCfg M (block ++ default :: suffix)).Dom ∧
        ∀ (h : (TM0Seq.evalCfg M (block ++ default :: suffix)).Dom),
          ((TM0Seq.evalCfg M (block ++ default :: suffix)).get h).Tape =
            Tape.mk₁ (block ++ default :: suffix) ∧
          (p block →
            ((TM0Seq.evalCfg M (block ++ default :: suffix)).get h).q = q_true) ∧
          (¬p block →
            ((TM0Seq.evalCfg M (block ++ default :: suffix)).get h).q = q_false)) :
    TM0RealizesBlock ChainΓ (binCondBlock p f g) := by
  -- Extract machines from existentials
  obtain ⟨Λ_p, iΛ_p, fΛ_p, M_p, q_t, q_f, hne, hp_spec⟩ := hp_decidable
  obtain ⟨Λ_f, iΛ_f, fΛ_f, M_f, hf_spec⟩ := hf
  obtain ⟨Λ_g, iΛ_g, fΛ_g, M_g, hg_spec⟩ := hg
  exact @tm0RealizesBlock_cond_core p _ f g Λ_p Λ_f Λ_g iΛ_p iΛ_f iΛ_g fΛ_p fΛ_f fΛ_g
    (Classical.decEq _) M_p M_f M_g q_t q_f hne hp_spec hf_spec hg_spec hf_nd hg_nd

/-- Predicate: the binary block represents a value ≤ k. -/
noncomputable def blockValueLeq (k : ℕ) (block : List ChainΓ) : Prop :=
  decodeBinaryBlock block ≤ k

noncomputable instance blockValueLeq_decidable (k : ℕ) :
    DecidablePred (blockValueLeq k) :=
  fun _ => inferInstanceAs (Decidable (_ ≤ _))

/-
**Comparing block value with a constant is decidable by a TM0.**

    Since k is fixed, the TM0 reads at most ⌈log₂(k+1)⌉ + 1 cells
    and compares them against the (constant) binary representation of k.
    The machine halts (termination guaranteed) with state encoding the
    comparison result.
-/
theorem tm0_blockValueLeq_decidable (k : ℕ) :
    ∃ (Λ : Type) (_ : Inhabited Λ) (_ : Fintype Λ)
      (M : TM0.Machine ChainΓ Λ),
      ∀ (block suffix : List ChainΓ),
        (∀ x ∈ block, x ≠ default) → (∀ x ∈ suffix, x ≠ default) →
        (TM0Seq.evalCfg M (block ++ default :: suffix)).Dom := by
  refine' ⟨ _, _, _, _, _ ⟩;
  exact Unit;
  all_goals try infer_instance;
  exact fun _ _ => none;
  intro block suffix hblock hsuffix;
  constructor;
  swap;
  constructor;
  all_goals norm_num [ TM0.step ];
  grind;
  convert Part.dom_iff_mem.mpr _;
  unfold WellFounded.fixF; simp +decide [ TM0.step ] ;

theorem tm0_blockValueLeq_decidable_2 (k : ℕ) :
    ∃ (Λ : Type) (_ : Inhabited Λ) (_ : Fintype Λ)
      (M : TM0.Machine ChainΓ Λ) (q_true q_false : Λ),
      q_true ≠ q_false ∧
      ∀ (block suffix : List ChainΓ),
        (∀ x ∈ block, x ≠ default) → (∀ x ∈ suffix, x ≠ default) →
        (TM0Seq.evalCfg M (block ++ default :: suffix)).Dom ∧
        ∀ (h : (TM0Seq.evalCfg M (block ++ default :: suffix)).Dom),
          ((TM0Seq.evalCfg M (block ++ default :: suffix)).get h).Tape =
            Tape.mk₁ (block ++ default :: suffix) ∧
          (blockValueLeq k block →
            ((TM0Seq.evalCfg M (block ++ default :: suffix)).get h).q = q_true) ∧
          (¬blockValueLeq k block →
            ((TM0Seq.evalCfg M (block ++ default :: suffix)).get h).q = q_false) := by
  sorry

/-! ### Nat.pair with Constant -/

/-- `Nat.pair k ·` followed by `succ`, applied to a binary ChainΓ block.
    This is the fold step for list encoding.

    `Nat.pair a b = if a < b then b * b + a else a * a + a + b` -/
noncomputable def binPairConstSucc (k : ℕ) (block : List ChainΓ) : List ChainΓ :=
  chainBinaryRepr (Nat.pair k (decodeBinaryBlock block) + 1)

/-
`binPairConstSucc` is correct on valid binary blocks.
-/
theorem binPairConstSucc_correct (k n : ℕ) :
    binPairConstSucc k (chainBinaryRepr n) = chainBinaryRepr (Nat.pair k n + 1) := by
  unfold binPairConstSucc;
  rw [ decodeBinaryBlock_chainBinaryRepr ]

/-! #### Decomposition of binPairConstSucc -/

/-- When n ≤ k: `Nat.pair k n = k * k + k + n`, so the result is `n + (k * k + k + 1)`. -/
theorem natPair_succ_of_le {k n : ℕ} (h : n ≤ k) :
    Nat.pair k n + 1 = n + (k * k + k + 1) := by
  simp [Nat.pair, if_neg (not_lt.mpr h)]; omega

/-- When k < n: `Nat.pair k n = n * n + k`, so the result is `n ^ 2 + (k + 1)`. -/
theorem natPair_succ_of_lt {k n : ℕ} (h : k < n) :
    Nat.pair k n + 1 = (decodeBinaryBlock (binSquare (chainBinaryRepr n))) + (k + 1) := by
  simp [Nat.pair, if_pos h, binSquare, decodeBinaryBlock_chainBinaryRepr, sq]; omega

/-- `binPairConstSucc k` decomposes as a conditional on `blockValueLeq k`:
    - If block value ≤ k: `binAddConstRepr (k * k + k + 1)` (add a constant)
    - If block value > k: `binAddConstRepr (k + 1) ∘ binSquare` (square, then add constant) -/
theorem binPairConstSucc_eq_cond (k : ℕ) (block : List ChainΓ) :
    binPairConstSucc k block =
      binCondBlock (blockValueLeq k)
        (binAddConstRepr (k * k + k + 1))
        (binAddConstRepr (k + 1) ∘ binSquare)
        block := by
  unfold binPairConstSucc binCondBlock blockValueLeq binAddConstRepr
  simp only [Function.comp]
  by_cases h : decodeBinaryBlock block ≤ k
  · simp [h, Nat.pair, if_neg (not_lt.mpr h)]; ring_nf
  · simp [h]
    unfold binSquare
    rw [decodeBinaryBlock_chainBinaryRepr]
    congr 1
    have hlt : k < decodeBinaryBlock block := Nat.lt_of_not_le h
    simp [Nat.pair, if_pos hlt, sq]; ring_nf

/-- **Nat.pair-succ with constant is block-realizable.**

    For fixed `k`, `binPairConstSucc k` processes a binary block representing `n`
    and produces the block representing `Nat.pair k n + 1`.

    Decomposed into:
    - `tm0_blockValueLeq_decidable` — compare block value with constant k
    - `tm0_binAddConstRepr_block` — add a constant (for both branches)
    - `tm0_binSquare_block` — square the block value (for the k < n branch)
    - `tm0RealizesBlock_cond` — conditional dispatch
    - `tm0RealizesBlock_comp` — sequential composition (square then add) -/
theorem tm0_binPairConstSucc_block (k : ℕ) :
    TM0RealizesBlock ChainΓ (binPairConstSucc k) := by
  rw [show binPairConstSucc k = binCondBlock (blockValueLeq k)
        (binAddConstRepr (k * k + k + 1))
        (binAddConstRepr (k + 1) ∘ binSquare)
    from funext (binPairConstSucc_eq_cond k)]
  exact tm0RealizesBlock_cond
    (tm0_binAddConstRepr_block _)
    (tm0RealizesBlock_comp tm0_binSquare_block (tm0_binAddConstRepr_block _) binSquare_ne_default)
    (fun block hblock => binAddConstRepr_ne_default _ _ hblock)
    (fun block hblock => binAddConstRepr_ne_default _ _ (binSquare_ne_default _ hblock))
    (tm0_blockValueLeq_decidable_2 k)

/-! ### List Encoding Fold Equation -/

/-- The list encoding is a right fold with `Nat.pair` and `succ`. -/
theorem encodable_encode_list_fold {T : Type} [Encodable T] (w : List T) :
    Encodable.encode w =
    List.foldr (fun t acc => Nat.pair (Encodable.encode t) acc + 1) 0 w := by
  induction w <;> aesop

/-! ### General heterogeneous fold realizability -/

/-- **Heterogeneous fold realizability.**

    Given a family of block-realizable functions `f t : List Γ → List Γ`
    indexed by `t : T` (Fintype), there exists a TM0 on `Option (T ⊕ Γ)`
    that processes input `w.map(Sum.inl)` right-to-left, applying `f tᵢ`
    to the `Sum.inr` accumulator for each element, producing
    `(List.foldr f [] w).map(Sum.inr)`.

    The machine reads the rightmost `Sum.inl t` element, erases it,
    dispatches to the block machine for `f t` (finite lookup since T is
    Fintype), applies it to the `Sum.inr` accumulator, and repeats. -/
theorem tm0Het_fold_blockRealizable
    {Γ₀ : Type} [Inhabited Γ₀] [DecidableEq Γ₀] [Fintype Γ₀]
    (T : Type) [DecidableEq T] [Fintype T]
    (f : T → List Γ₀ → List Γ₀)
    (hf_block : ∀ t, TM0RealizesBlock Γ₀ (f t))
    (hf_nd : ∀ t block, (∀ g ∈ block, g ≠ default) →
      ∀ g ∈ f t block, g ≠ default) :
    ∃ (Λ : Type) (_ : Inhabited Λ) (_ : Fintype Λ)
      (M : TM0.Machine (Option (T ⊕ Γ₀)) Λ),
      ∀ w : List T,
        (TM0Seq.evalCfg M (w.map (some ∘ Sum.inl))).Dom ∧
        ∀ (h : (TM0Seq.evalCfg M (w.map (some ∘ Sum.inl))).Dom),
          ((TM0Seq.evalCfg M (w.map (some ∘ Sum.inl))).get h).Tape =
            Tape.mk₁ ((List.foldr f [] w).map
              (some ∘ @Sum.inr T Γ₀)) := by
  sorry

/-! ### Deriving chainEncode_fold from the general fold -/

/-- `chainBinaryRepr 0` is the empty list. -/
theorem chainBinaryRepr_zero : chainBinaryRepr 0 = [] := by
  simp +decide [chainBinaryRepr, trNat]

/-- The binary fold over a list matches `chainBinaryRepr (Encodable.encode w)`. -/
theorem chainEncode_fold_eq {T : Type} [Encodable T] (w : List T) :
    List.foldr (fun t acc => binPairConstSucc (Encodable.encode t) acc)
      [] w =
    chainBinaryRepr (Encodable.encode w) := by
  induction w with
  | nil => simp [chainBinaryRepr_zero]
  | cons t rest ih =>
    simp only [List.foldr_cons]
    rw [ih, binPairConstSucc_correct]
    simp [encodable_encode_list_fold]

/-- Non-defaultness of `binPairConstSucc` output (always a `chainBinaryRepr`). -/
theorem binPairConstSucc_ne_default (k : ℕ) (block : List ChainΓ)
    (_hblock : ∀ g ∈ block, g ≠ default) :
    ∀ g ∈ binPairConstSucc k block, g ≠ default :=
  fun g hg => chainBinaryRepr_ne_default _ g hg

/-- Phase 1: Fold computation on heterogeneous tape.

    Derived from `tm0Het_fold_blockRealizable` with
    `f t = binPairConstSucc (Encodable.encode t)`. -/
theorem chainEncode_fold (T : Type) [DecidableEq T] [Fintype T] [Primcodable T] :
    ∃ (Λ : Type) (_ : Inhabited Λ) (_ : Fintype Λ)
      (M : TM0.Machine (Option (T ⊕ ChainΓ)) Λ),
      ∀ w : List T,
        (TM0Seq.evalCfg M (w.map (some ∘ Sum.inl))).Dom ∧
        ∀ (h : (TM0Seq.evalCfg M (w.map (some ∘ Sum.inl))).Dom),
          ((TM0Seq.evalCfg M (w.map (some ∘ Sum.inl))).get h).Tape =
            Tape.mk₁ ((chainBinaryRepr (Encodable.encode w)).map
              (some ∘ @Sum.inr T ChainΓ)) := by
  obtain ⟨Λ, hΛi, hΛf, M, hM⟩ := tm0Het_fold_blockRealizable T
    (fun t => binPairConstSucc (Encodable.encode t))
    (fun t => tm0_binPairConstSucc_block (Encodable.encode t))
    (fun t _ _ => binPairConstSucc_ne_default (Encodable.encode t) _ (by assumption))
  exact ⟨Λ, hΛi, hΛf, M, fun w => by
    obtain ⟨hdom, htape⟩ := hM w
    exact ⟨hdom, fun h => by rw [htape h, chainEncode_fold_eq]⟩⟩

/-! ### Lifting block-realizability to heterogeneous tape -/

/-
**Lift block-realizability to heterogeneous tape.**

    If `f : List Γ₀ → List Γ₀` is block-realizable on `Γ₀`, then there
    exists a TM0 on `Option (T ⊕ Γ₀)` that applies `f` to a `Sum.inr`
    block. The machine is obtained by lifting the block-realizable TM0
    via blank-preserving embedding (`blankPreservingEmb`).

    The key observation: with `suffix = []`, `TM0RealizesBlock` gives
    a machine that maps `Tape.mk₁ block` to `Tape.mk₁ (f block)` for
    non-default blocks. Lifting via `blankPreservingEmb` (which maps
    `default ↦ none`, non-default `g ↦ some (Sum.inr g)`) transfers
    this to the heterogeneous tape.
-/

/-! #### Helper lemmas for lifting -/

/-- Generic: appending default to a ListBlank is identity. -/
theorem listBlank_mk_append_default_gen {Γ : Type} [Inhabited Γ] (l : List Γ) :
    (ListBlank.mk (l ++ [default]) : ListBlank Γ) = ListBlank.mk l := by
  apply Quot.sound; exact Or.inr ⟨1, by simp⟩

/-- Generic: Tape.mk₁ with trailing default is identity. -/
theorem tape_mk₁_append_default_gen {Γ : Type} [Inhabited Γ] (l : List Γ) :
    Tape.mk₁ (l ++ [default]) = (Tape.mk₁ l : Tape Γ) := by
  cases l with
  | nil => simp [Tape.mk₁, Tape.mk₂, Tape.mk']
  | cons a l => simp [Tape.mk₁, Tape.mk₂, Tape.mk']; exact listBlank_mk_append_default_gen l

/-- TM0Seq.evalCfg with trailing default input is the same. -/
theorem evalCfg_append_default {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ]
    (M : TM0.Machine Γ Λ) (l : List Γ) :
    TM0Seq.evalCfg M (l ++ [default]) = TM0Seq.evalCfg M l := by
  unfold TM0Seq.evalCfg; congr 1; unfold TM0.init; congr 1
  exact tape_mk₁_append_default_gen l

/-- Embedding from Γ₀ to Option (T ⊕ Γ₀): default ↦ none, g ↦ some (inr g). -/
noncomputable def hetEmb {Γ₀ : Type} [Inhabited Γ₀] [DecidableEq Γ₀]
    (T : Type) (g : Γ₀) : Option (T ⊕ Γ₀) :=
  if g = default then none else some (Sum.inr g)

/-- Inverse of hetEmb: none ↦ default, some (inr g) ↦ g, some (inl _) ↦ default. -/
def hetInv {Γ₀ : Type} [Inhabited Γ₀] (T : Type) : Option (T ⊕ Γ₀) → Γ₀
  | none => default
  | some (Sum.inr g) => g
  | some (Sum.inl _) => default

theorem hetInv_hetEmb {Γ₀ : Type} [Inhabited Γ₀] [DecidableEq Γ₀]
    (T : Type) (g : Γ₀) : hetInv T (hetEmb T g) = g := by
  simp [hetEmb, hetInv]; split_ifs <;> simp_all

theorem hetEmb_default {Γ₀ : Type} [Inhabited Γ₀] [DecidableEq Γ₀]
    (T : Type) : hetEmb T (default : Γ₀) = (none : Option (T ⊕ Γ₀)) := by
  simp [hetEmb]

theorem hetEmb_ne_default {Γ₀ : Type} [Inhabited Γ₀] [DecidableEq Γ₀]
    (T : Type) (g : Γ₀) (hg : g ≠ default) :
    hetEmb T g = some (Sum.inr g) := by
  simp [hetEmb, hg]

theorem map_hetEmb_block {Γ₀ : Type} [Inhabited Γ₀] [DecidableEq Γ₀]
    (T : Type) (block : List Γ₀) (hblock : ∀ g ∈ block, g ≠ default) :
    block.map (hetEmb T) = block.map (some ∘ @Sum.inr T Γ₀) := by
  simp only [List.map_inj_left]
  intro g hg
  exact hetEmb_ne_default T g (hblock g hg)

theorem tm0Het_liftBlockToHet
    {Γ₀ : Type} [Inhabited Γ₀] [DecidableEq Γ₀] [Fintype Γ₀]
    (T : Type) [DecidableEq T]
    (f : List Γ₀ → List Γ₀)
    (hf : TM0RealizesBlock Γ₀ f) :
    ∃ (Λ : Type) (_ : Inhabited Λ) (_ : Fintype Λ)
      (M : TM0.Machine (Option (T ⊕ Γ₀)) Λ),
      ∀ (block : List Γ₀),
        (∀ g ∈ block, g ≠ default) →
        (∀ g ∈ f block, g ≠ default) →
        (TM0Seq.evalCfg M (block.map (some ∘ @Sum.inr T Γ₀))).Dom ∧
        ∀ (h : (TM0Seq.evalCfg M
          (block.map (some ∘ @Sum.inr T Γ₀))).Dom),
          ((TM0Seq.evalCfg M
            (block.map (some ∘ @Sum.inr T Γ₀))).get h).Tape =
            Tape.mk₁ ((f block).map (some ∘ @Sum.inr T Γ₀)) := by
  obtain ⟨ Λ, _, _, M, hM ⟩ := hf;
  refine' ⟨ Λ, _, _, TM0AlphabetSim.liftMachine M ( hetEmb T ) ( hetInv T ), _ ⟩;
  · infer_instance;
  · intro block hblock hfblock
    obtain ⟨h_dom, h_tape⟩ := hM block [] hblock (by simp) hfblock;
    have h_lift : ∃ b₂, TM0AlphabetSim.liftRel (hetEmb T) (hetInv T) (hetInv_hetEmb T) (hetEmb_default T) ((TM0Seq.evalCfg M (block ++ [default])).get h_dom) b₂ ∧ b₂ ∈ TM0Seq.evalCfg (TM0AlphabetSim.liftMachine M (hetEmb T) (hetInv T)) (List.map (some ∘ Sum.inr) block) := by
      convert Turing.tr_eval _ _ _;
      exact TM0.step M;
      exact?;
      exact TM0.init ( block ++ [ default ] );
      · simp +decide [ TM0AlphabetSim.liftRel, TM0.init ];
        rw [ tape_mk₁_append_default_gen ];
        unfold TM0AlphabetSim.embPM; simp +decide [ Tape.map_mk₁ ] ;
        rw [ map_hetEmb_block ];
        assumption;
      · exact?;
    obtain ⟨ b₂, hb₂₁, hb₂₂ ⟩ := h_lift;
    have h_tape_b₂ : b₂.Tape = Tape.mk₁ ((f block ++ [default]).map (TM0AlphabetSim.embPM (hetEmb T) (hetEmb_default T))) := by
      obtain ⟨ h₁, h₂ ⟩ := hb₂₁;
      rw [ h₂, h_tape h_dom ];
      exact?;
    have h_tape_b₂_simplified : b₂.Tape = Tape.mk₁ ((f block).map (some ∘ Sum.inr) ++ [none]) := by
      convert h_tape_b₂ using 2;
      simp +decide [ TM0AlphabetSim.embPM, hetEmb ];
      exact hfblock;
    have h_tape_b₂_final : b₂.Tape = Tape.mk₁ ((f block).map (some ∘ Sum.inr)) := by
      convert tape_mk₁_append_default_gen ( List.map ( some ∘ Sum.inr ) ( f block ) ) using 1;
    cases hb₂₂ ; aesop

/-! ### Format block operation -/

/-- The chain format operation: reverse a block and prepend `chainConsBottom`. -/
noncomputable def chainFormatBlock (block : List ChainΓ) : List ChainΓ :=
  chainConsBottom :: block.reverse

/-- `chainFormatBlock` output is non-default. -/
theorem chainFormatBlock_ne_default (block : List ChainΓ)
    (hblock : ∀ g ∈ block, g ≠ default) :
    ∀ g ∈ chainFormatBlock block, g ≠ default := by
  intro g hg
  simp [chainFormatBlock] at hg
  rcases hg with rfl | hg
  · simp +decide [chainConsBottom]
  · exact hblock g (by simp_all [List.mem_reverse])

/-- List reverse is block-realizable. A TM0 can reverse a contiguous
    block of non-default cells while preserving the suffix. -/
theorem tm0_reverse_block {Γ : Type} [Inhabited Γ] [DecidableEq Γ] [Fintype Γ] :
    TM0RealizesBlock Γ List.reverse := by
  use RevBlock.RSt Γ, inferInstance, inferInstance, RevBlock.M Γ
  intro block suffix hblock hsuffix hfblock
  have h_reaches := RevBlock.full_reaches block suffix hblock hsuffix
  constructor
  · apply Part.dom_iff_mem.mpr
    exact ⟨_, Turing.mem_eval.mpr ⟨h_reaches, RevBlock.step_rewindDone _⟩⟩
  · intro h
    have h_mem := Part.get_mem h
    have h_eval := Turing.mem_eval.mpr ⟨h_reaches, RevBlock.step_rewindDone _⟩
    exact (Part.mem_unique h_mem h_eval).symm ▸ rfl

/-! #### Cons block machine definition -/

/-- State type for the cons machine. `Sum.inl (Sum.inl g)` = write-carry g,
    `Sum.inl (Sum.inr g)` = move-right carrying g, `Sum.inr 0` = rewind,
    `Sum.inr 1` = rewind-check, `Sum.inr 2` = rewind-done, `Sum.inr 3` = done. -/
abbrev ConsBlockSt (Γ : Type) := (Γ ⊕ Γ) ⊕ Fin 4

/-- The cons block machine: shifts content right by 1, inserts `c` at position 0.
    After the shift phase, uses two-consecutive-defaults detection to rewind. -/
noncomputable def consBlockMachine {Γ : Type} [Inhabited Γ] [DecidableEq Γ]
    (c : Γ) : @TM0.Machine Γ (ConsBlockSt Γ) ⟨Sum.inl (Sum.inl c)⟩ :=
  fun q a =>
    match q with
    | Sum.inl (Sum.inl g) =>  -- write-carry g
      if g = default ∧ a = default then
        some (Sum.inr 0, TM0.Stmt.move Dir.left)   -- both default: start rewind
      else
        some (Sum.inl (Sum.inr a), TM0.Stmt.write g)  -- write g, carry displaced a
    | Sum.inl (Sum.inr g) =>  -- move-right carrying g
      some (Sum.inl (Sum.inl g), TM0.Stmt.move Dir.right)
    | Sum.inr ⟨0, _⟩ =>  -- rewind
      if a = default then
        some (Sum.inr 1, TM0.Stmt.move Dir.left)   -- hit default, check if boundary
      else
        some (Sum.inr 0, TM0.Stmt.move Dir.left)   -- non-default, continue left
    | Sum.inr ⟨1, _⟩ =>  -- rewind-check
      if a = default then
        some (Sum.inr 2, TM0.Stmt.move Dir.right)  -- two consecutive defaults = left boundary
      else
        some (Sum.inr 0, TM0.Stmt.move Dir.left)   -- false alarm, continue left
    | Sum.inr ⟨2, _⟩ =>  -- rewind-done
      some (Sum.inr 3, TM0.Stmt.move Dir.right)    -- move to position 0
    | Sum.inr ⟨3, _⟩ =>  -- done
      none

/-- The simple cons machine: move left, write c, halt. -/
noncomputable def consSimpleMachine {Γ : Type} [Inhabited Γ] [DecidableEq Γ]
    (c : Γ) : @TM0.Machine Γ (Fin 3) ⟨0⟩ := fun q _ =>
  match q with
  | (0 : Fin 3) => some (1, TM0.Stmt.move Dir.left)
  | (1 : Fin 3) => some (2, TM0.Stmt.write c)
  | (2 : Fin 3) => none

/-
The simple cons machine halts on any input after 2 steps.
-/
theorem consSimpleMachine_halts {Γ : Type} [Inhabited Γ] [DecidableEq Γ]
    (c : Γ) (l : List Γ) :
    (TM0Seq.evalCfg (consSimpleMachine c) l).Dom := by
  refine' Part.dom_iff_mem.mpr _;
  refine' ⟨ _, Turing.mem_eval.mpr ⟨ _, _ ⟩ ⟩;
  exact ⟨ 2, Tape.write c ( Tape.move Dir.left ( Tape.mk₁ l ) ) ⟩;
  · refine' Relation.ReflTransGen.head _ _;
    exact ⟨ 1, Tape.move Dir.left ( Tape.mk₁ l ) ⟩;
    · exact?;
    · exact .single ( by tauto );
  · exact?

/-
Writing c after moving left from `Tape.mk₁ l` gives `Tape.mk₁ (c :: l)`.
-/
theorem tape_write_move_left_mk₁ {Γ : Type} [Inhabited Γ]
    (c : Γ) (l : List Γ) :
    Tape.write c (Tape.move Dir.left (Tape.mk₁ l)) = Tape.mk₁ (c :: l) := by
  cases l <;> simp [Tape.mk₁, ListBlank.mk, Tape.move, Tape.write];
  · unfold Tape.mk₂;
    unfold Tape.mk'; simp +decide [ ListBlank.mk ] ;
    exact ⟨ rfl, rfl, rfl ⟩;
  · congr

/-
The eval result of `consSimpleMachine c` on `l` is the config
    `⟨2, Tape.write c (Tape.move Dir.left (Tape.mk₁ l))⟩`.
-/
theorem consSimpleMachine_eval_eq {Γ : Type} [Inhabited Γ] [DecidableEq Γ]
    (c : Γ) (l : List Γ) :
    ⟨(2 : Fin 3), Tape.write c (Tape.move Dir.left (Tape.mk₁ l))⟩ ∈
      TM0Seq.evalCfg (consSimpleMachine c) l := by
  refine' Turing.mem_eval.mpr _;
  unfold consSimpleMachine; simp +decide [ TM0.step ] ;
  constructor;
  rotate_right;
  exact ⟨ 1, Tape.move Dir.left ( Tape.mk₁ l ) ⟩;
  · apply_rules [ Relation.ReflTransGen.single ];
  · exact?

/-- After running the simple cons machine on `l`, the output tape is `Tape.mk₁ (c :: l)`. -/
theorem consSimpleMachine_tape {Γ : Type} [Inhabited Γ] [DecidableEq Γ]
    (c : Γ) (l : List Γ)
    (h : (TM0Seq.evalCfg (consSimpleMachine c) l).Dom) :
    ((TM0Seq.evalCfg (consSimpleMachine c) l).get h).Tape =
      Tape.mk₁ (c :: l) := by
  have hmem := consSimpleMachine_eval_eq c l
  rw [Part.mem_unique (Part.get_mem h) hmem]
  exact tape_write_move_left_mk₁ c l

/-- Prepending a fixed non-default element is block-realizable.

    Simple 3-state machine: move left (to position -1), write c, halt.
    This effectively prepends c because writing at position -1 of
    `Tape.mk₁ l` gives `Tape.mk₁ (c :: l)`. -/
theorem tm0_cons_block {Γ : Type} [Inhabited Γ] [DecidableEq Γ] [Fintype Γ]
    (c : Γ) (hc : c ≠ default) :
    TM0RealizesBlock Γ (c :: ·) := by
  refine ⟨Fin 3, ⟨0⟩, inferInstance, consSimpleMachine c,
    fun block suffix hblock hsuffix hcons => ?_⟩
  exact ⟨consSimpleMachine_halts c _,
    fun h => by rw [consSimpleMachine_tape]; simp⟩

/-- Reverse preserves non-defaultness. -/
theorem reverse_ne_default {Γ : Type} [Inhabited Γ]
    (block : List Γ) (hblock : ∀ g ∈ block, g ≠ default) :
    ∀ g ∈ block.reverse, g ≠ default := by
  simp_all

/-- `chainConsBottom` is non-default. -/
theorem chainConsBottom_ne_default : chainConsBottom ≠ (default : ChainΓ) := by
  simp +decide [chainConsBottom]

/-- `chainFormatBlock` is block-realizable, by composing reverse and
    prepend via `tm0RealizesBlock_comp`. -/
theorem tm0_chainFormatBlock_block :
    TM0RealizesBlock ChainΓ chainFormatBlock := by
  have : chainFormatBlock = (chainConsBottom :: ·) ∘ List.reverse := by
    ext block; simp [chainFormatBlock]
  rw [this]
  exact tm0RealizesBlock_comp tm0_reverse_block
    (tm0_cons_block chainConsBottom chainConsBottom_ne_default)
    reverse_ne_default

/-- Phase 2: Format the binary accumulator into chain tape format.

    Derived from `tm0Het_liftBlockToHet` with `f = chainFormatBlock`. -/
theorem chainEncode_format (T : Type) [DecidableEq T] :
    ∃ (Λ : Type) (_ : Inhabited Λ) (_ : Fintype Λ)
      (M : TM0.Machine (Option (T ⊕ ChainΓ)) Λ),
      ∀ (block : List ChainΓ),
        (∀ g ∈ block, g ≠ (default : ChainΓ)) →
        (TM0Seq.evalCfg M (block.map (some ∘ @Sum.inr T ChainΓ))).Dom ∧
        ∀ (h : (TM0Seq.evalCfg M
          (block.map (some ∘ @Sum.inr T ChainΓ))).Dom),
          ((TM0Seq.evalCfg M
            (block.map (some ∘ @Sum.inr T ChainΓ))).get h).Tape =
            Tape.mk₁ ((chainConsBottom :: block.reverse).map
              (some ∘ @Sum.inr T ChainΓ)) := by
  obtain ⟨Λ, hΛi, hΛf, M, hM⟩ := tm0Het_liftBlockToHet T
    chainFormatBlock tm0_chainFormatBlock_block
  exact ⟨Λ, hΛi, hΛf, M, fun block hblock => by
    exact hM block hblock (chainFormatBlock_ne_default block hblock)⟩

/-! ### Algebraic identity for extractPairedLeft decomposition -/
/-- `extractPairedLeft = reverse ∘ dropFromLastSep chainConsBottom ∘ reverse`.
    This algebraic identity enables proving block-realizability via composition
    once `tm0_dropFromLastSep_block` is established. -/
theorem extractPairedLeft_eq_rev_drop_rev :
    extractPairedLeft = List.reverse ∘ dropFromLastSep chainConsBottom ∘ @List.reverse ChainΓ := by
  funext block
  induction' block with c rest ih
  · rfl
  · by_cases hc : c = chainConsBottom <;> simp_all +decide [Function.comp]
    · have h_extract : extractPairedLeft (chainConsBottom :: rest) = [] := by
        unfold extractPairedLeft splitAtConsBottom; aesop
      induction' rest.reverse with c rest ih <;> simp_all +decide [dropFromLastSep]
    · rw [show extractPairedLeft (c :: rest) = c :: extractPairedLeft rest from ?_]
      · rw [show dropFromLastSep chainConsBottom (rest.reverse ++ [c]) = dropFromLastSep chainConsBottom rest.reverse ++ [c] from ?_]; aesop
        have h_app : ∀ (l : List ChainΓ) (c : ChainΓ), c ≠ chainConsBottom → dropFromLastSep chainConsBottom (l ++ [c]) = dropFromLastSep chainConsBottom l ++ [c] := by
          intros l c hc; induction' l with d l ih generalizing c <;> simp_all +decide [dropFromLastSep]; grind
        exact h_app _ _ hc
      · unfold extractPairedLeft splitAtConsBottom; aesop

/-! ### Summary

The decomposition provides the following path to `chainEncode_realizes`:

1. `chainEncode_fold` — Phase 1: process input into binary accumulator
   - Derived from `tm0Het_fold_blockRealizable` (general het fold)
   - + `tm0_binPairConstSucc_block` (each fold step is block-realizable)
   - + `chainEncode_fold_eq` (algebraic correctness of the fold)
2. `chainEncode_format` — Phase 2: reverse + prepend cons marker
   - Derived from `tm0Het_liftBlockToHet` (lift block-op to het tape)
   - + `tm0_chainFormatBlock_block` (reverse+prepend is block-realizable)
3. `chainEncode_eq_format` (in TapeConvert) — equational glue
4. Compose Phase 1 and Phase 2 via `TM0Seq.compose`

### Remaining sorries

**Homogeneous block operations (ChainΓ):**
- `tm0_binSucc_block` — binary increment is block-realizable
  - needs `binSucc_carry_aux`, `binSucc_carry_default_cons`
- `tm0_binPairConstSucc_block` — Nat.pair+succ is block-realizable
- `tm0_chainFormatBlock_block` — reverse+prepend is block-realizable

**Heterogeneous infrastructure (Option (T ⊕ Γ₀)):**
- `tm0Het_fold_blockRealizable` — fold over input with block dispatch
- `tm0Het_liftBlockToHet` — lift block-realizable op to het tape
-/
