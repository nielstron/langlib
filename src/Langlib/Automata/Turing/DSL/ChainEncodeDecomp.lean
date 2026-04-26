import Mathlib
import Langlib.Automata.Turing.DSL.TM0Compose
import Langlib.Automata.Turing.DSL.TM0BuildingBlocks
import Langlib.Automata.Turing.DSL.ParrecChain

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

/-- Extension case, non-empty suffix. -/
theorem binSucc_carry_default_cons (s : ChainΓ) (rest revLeft : List ChainΓ)
    (hs : s ≠ default)
    (hrest : ∀ g ∈ rest, g ≠ default)
    (hrevLeft : ∀ g ∈ revLeft, g ≠ default) :
    Reaches (TM0.step binSuccMachine)
      ⟨.carry, ⟨default, ListBlank.mk revLeft, ListBlank.mk (s :: rest)⟩⟩
      ⟨.done, Tape.mk₁ (revLeft.reverse ++ γ'ToChainΓ Γ'.bit1 :: default :: s :: rest)⟩ := by
  sorry

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

/-- Auxiliary: the carry phase starting with left context `revLeft`. -/
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
  sorry

/-- **Binary successor is block-realizable (singleton function #1).**

    Uses `binSuccMachine` which implements a carry-chain:
    - `carry` phase: scan right through block, flipping bit1→bit0 (carry) or bit0→bit1 (absorb).
    - Extension: if carry reaches blank, write bit1 and shift suffix right by 1.
    - Rewind: move left back to position 0. -/
theorem tm0_binSucc_block : TM0RealizesBlock ChainΓ binSucc := by
  sorry

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

/-- **Nat.pair-succ with constant is block-realizable.**

    For fixed `k`, `binPairConstSucc k` processes a binary block representing `n`
    and produces the block representing `Nat.pair k n + 1`.

    Decomposition into singleton functions:
    - If k < n: compute n² (squaring via repeated addition of n),
      then add k + 1 (constant addition via repeated increment)
    - If k ≥ n: add k² + k + 1 (constant) to n (via repeated increment) -/
theorem tm0_binPairConstSucc_block (k : ℕ) :
    TM0RealizesBlock ChainΓ (binPairConstSucc k) := by
  sorry

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

/-- **Lift block-realizability to heterogeneous tape.**

    If `f : List Γ₀ → List Γ₀` is block-realizable on `Γ₀`, then there
    exists a TM0 on `Option (T ⊕ Γ₀)` that applies `f` to a `Sum.inr`
    block. The machine is obtained by lifting the block-realizable TM0
    via blank-preserving embedding (`blankPreservingEmb`).

    The key observation: with `suffix = []`, `TM0RealizesBlock` gives
    a machine that maps `Tape.mk₁ block` to `Tape.mk₁ (f block)` for
    non-default blocks. Lifting via `blankPreservingEmb` (which maps
    `default ↦ none`, non-default `g ↦ some (Sum.inr g)`) transfers
    this to the heterogeneous tape. -/
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
  sorry

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
  sorry

/-- Prepending a fixed non-default element is block-realizable. -/
theorem tm0_cons_block {Γ : Type} [Inhabited Γ] [DecidableEq Γ] [Fintype Γ]
    (c : Γ) (hc : c ≠ default) :
    TM0RealizesBlock Γ (c :: ·) := by
  sorry

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