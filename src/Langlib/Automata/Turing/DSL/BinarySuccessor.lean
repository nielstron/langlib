import Mathlib
import Langlib.Automata.Turing.DSL.ChainAlphabet
import Langlib.Automata.Turing.DSL.BlockRealizability

/-! # Binary Successor — TM0 Machine for Incrementing Binary Blocks

This file defines the binary successor operation `binSucc` on ChainΓ blocks
and proves it is block-realizable via a TM0 machine (`binSuccMachine`).

## Main definitions

- `binSucc`: syntactic binary increment on lists of ChainΓ cells
- `binSuccMachine`: the TM0 machine implementing binary increment

## Main results

- `binSucc_correct`: `binSucc (chainBinaryRepr n) = chainBinaryRepr (n + 1)`
- `tm0_binSucc_block`: binary successor is block-realizable
-/

open Turing PartrecToTM2 TM2to1

/-! ### Binary Successor Function -/

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
      c :: rest  -- invalid input, no-op

/-- `binSucc` correctly increments the binary representation. -/
theorem binSucc_correct (n : ℕ) :
    binSucc (chainBinaryRepr n) = chainBinaryRepr (n + 1) := by
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

/-- All elements of `binSucc l` are non-default when the input elements are. -/
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

/-- rwdBlk loop: move left through non-default cells to the left boundary. -/
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

/-- rwdSuf loop: move left through non-default suffix cells to the separator. -/
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

/-- rwdSuf loop (extended): rewind through non-default suffix cells when there is
    extra content on the left tape beyond the suffix. -/
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

/-- Shift loop: shift suffix cells right by one position. -/
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
  · have h_ind : Reaches (TM0.step binSuccMachine) ⟨BinSuccSt.shiftW s, ⟨suffix.headI, ListBlank.mk (saved :: prevL), ListBlank.mk suffix.tail⟩⟩ ⟨BinSuccSt.shiftDn, ⟨(s :: suffix).getLast (by simp), ListBlank.mk ((s :: suffix).dropLast.reverse ++ (saved :: prevL)), ListBlank.mk []⟩⟩ := by
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

/-- Case: carry at bit0, absorbed immediately. -/
theorem binSucc_carry_bit0 (rest suffix revLeft : List ChainΓ)
    (hrevLeft : ∀ g ∈ revLeft, g ≠ default) :
    Reaches (TM0.step binSuccMachine)
      ⟨.carry, ⟨γ'ToChainΓ Γ'.bit0, ListBlank.mk revLeft,
               ListBlank.mk (rest ++ default :: suffix)⟩⟩
      ⟨.done, Tape.mk₁ (revLeft.reverse ++ γ'ToChainΓ Γ'.bit1 :: rest ++ default :: suffix)⟩ := by
  have h_step1 : TM0.step binSuccMachine ⟨BinSuccSt.carry, ⟨γ'ToChainΓ Γ'.bit0, ListBlank.mk revLeft, ListBlank.mk (rest ++ default :: suffix)⟩⟩ = some ⟨BinSuccSt.absorbed, ⟨γ'ToChainΓ Γ'.bit1, ListBlank.mk revLeft, ListBlank.mk (rest ++ default :: suffix)⟩⟩ := by
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

/-- Case: carry at bit1, recursive on rest. -/
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

/-- Case: carry at non-bit, non-default cell. No-op, just rewind. -/
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

/-! ### Extension case helpers -/

private theorem γ'bit1_ne_default : γ'ToChainΓ Γ'.bit1 ≠ (default : ChainΓ) := by
  simp +decide [γ'ToChainΓ]

/-- Phase 1: carry at default → shiftW s (steps 1-4 of the extension). -/
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

/-- Sub-phase A: shiftDn → rwdSuf (1 step, move left). -/
private theorem binSucc_ext_shiftDn_step (head : ChainΓ) (leftList : List ChainΓ) :
    Reaches (TM0.step binSuccMachine)
      ⟨.shiftDn, ⟨head, ListBlank.mk leftList, ListBlank.mk []⟩⟩
      ⟨.rwdSuf, ⟨leftList.headI, ListBlank.mk leftList.tail, ListBlank.mk [head]⟩⟩ := by
  apply Relation.ReflTransGen.single;
  cases leftList <;> aesop

/-- Sub-phase C: rwdSuf at default → rwdBlk (1 step, move left). -/
private theorem binSucc_ext_rwdSuf_to_rwdBlk (leftList : List ChainΓ) (rightList : List ChainΓ) :
    Reaches (TM0.step binSuccMachine)
      ⟨.rwdSuf, ⟨default, ListBlank.mk leftList, ListBlank.mk rightList⟩⟩
      ⟨.rwdBlk, ⟨leftList.headI, ListBlank.mk leftList.tail, ListBlank.mk (default :: rightList)⟩⟩ := by
  convert Relation.ReflTransGen.single _;
  cases leftList <;> aesop

/-- Elements of (s :: rest).dropLast are all non-default when s and rest elements are. -/
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
  have hA := binSucc_ext_shiftDn_step ((s :: rest).getLast (by simp))
    ((s :: rest).dropLast.reverse ++ default :: γ'ToChainΓ Γ'.bit1 :: revLeft)
  have h_nd_rev : ∀ g ∈ (s :: rest).dropLast.reverse, g ≠ default := by
    intro g hg
    exact dropLast_cons_ne_default s rest hs hrest g (List.mem_reverse.mp hg)
  have hB := binSucc_rwdSuf_loop_ext
    (s :: rest).dropLast.reverse
    (default :: γ'ToChainΓ Γ'.bit1 :: revLeft)
    h_nd_rev
    [((s :: rest).getLast (by simp))]
  have hC := binSucc_ext_rwdSuf_to_rwdBlk
    (γ'ToChainΓ Γ'.bit1 :: revLeft)
    (s :: rest)
  refine hA.trans (hB.trans ?_)
  convert hC using 2
  simp [List.reverse_reverse, List.dropLast_append_getLast]

/-- Phase 3: rwdBlk through bit1 :: revLeft → done. -/
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

/-- Extension case, empty suffix. -/
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
  · convert tape_mk₁_append_default (( γ'ToChainΓ Γ'.bit1 :: revLeft ).reverse) using 2;
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
  have h1 := binSucc_ext_phase1 s rest revLeft hs
  have h2a := binSucc_shift_loop rest hrest s (default :: γ'ToChainΓ Γ'.bit1 :: revLeft)
  have h2b := binSucc_ext_phase2_rwdSuf s rest revLeft hs hrest hrevLeft
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

/-! ### Main result -/

/-- **Binary successor is block-realizable.**

    Uses `binSuccMachine` which implements a carry-chain:
    - `carry` phase: scan right through block, flipping bit1→bit0 (carry) or bit0→bit1 (absorb).
    - Extension: if carry reaches blank, write bit1 and shift suffix right by 1.
    - Rewind: move left back to position 0. -/
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
