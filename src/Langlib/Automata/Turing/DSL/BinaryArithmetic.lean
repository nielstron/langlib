import Mathlib
import Langlib.Automata.Turing.DSL.ChainAlphabet
import Langlib.Automata.Turing.DSL.BlockRealizability
import Langlib.Automata.Turing.DSL.BinarySuccessor

/-! # Binary Arithmetic — Addition, Normalization, and Derived Operations

This file builds on binary successor to provide:

- `binAddConst`: addition of a constant via iterated increment
- `binAddConstRepr`: addition via decode/encode pipeline
- `normalizeBlock`: canonical binary representation via `stripTrailingBit0 ∘ replaceNonStandard`

All operations are proved block-realizable.

## Design principle

All arithmetic operations ultimately reduce to `binSucc` (increment).
Addition of a constant `c` is `binSucc^[c]`. The decode/encode pipeline
(`binAddConstRepr`) is equivalent but composes better with operations
like squaring and multiplication that work via `decodeBinaryBlock`.
-/

open Turing PartrecToTM2 TM2to1

/-! ### Addition via Repeated Increment -/

/-- Iterated application of `binSucc` (add constant `c` to the binary block). -/
noncomputable def binAddConst (c : ℕ) : List ChainΓ → List ChainΓ :=
  Nat.iterate binSucc c

/-- Adding a constant via repeated increment is correct. -/
theorem binAddConst_correct (c n : ℕ) :
    binAddConst c (chainBinaryRepr n) = chainBinaryRepr (n + c) := by
  unfold binAddConst;
  refine' Nat.rec _ _ c <;> simp_all +decide [ Function.iterate_succ_apply', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc ];
  exact fun k hk => by rw [ ← add_assoc, binSucc_correct ] ;

/-- Addition of a constant is block-realizable (derived from increment). -/
theorem tm0_binAddConst_block (c : ℕ) :
    TM0RealizesBlock ChainΓ (binAddConst c) := by
  exact tm0RealizesBlock_iterate tm0_binSucc_block binSucc_ne_default c

/-! ### Addition via Decode/Encode Pipeline -/

/-- Add a constant to the block value, going through decode/encode.
    Unlike `binAddConst` (which iterates `binSucc` syntactically), this
    version decodes the block, adds `c`, and re-encodes. The two agree
    on valid binary blocks but this version composes better with other
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

/-! ### Normalization -/

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

theorem normalizeBlock_append_nonbit (left tail : List ChainΓ) (terminator : ChainΓ)
    (hterminator_bit0 : terminator ≠ γ'ToChainΓ Γ'.bit0)
    (hterminator_bit1 : terminator ≠ γ'ToChainΓ Γ'.bit1) :
    normalizeBlock (left ++ terminator :: tail) = normalizeBlock left := by
  unfold normalizeBlock
  rw [decodeBinaryBlock_append_nonbit left tail terminator hterminator_bit0 hterminator_bit1]

theorem normalizeBlock_append_consBottom (left tail : List ChainΓ) :
    normalizeBlock (left ++ chainConsBottom :: tail) = normalizeBlock left := by
  exact normalizeBlock_append_nonbit left tail chainConsBottom (by decide) (by decide)

/-- Key decomposition: `binAddConstRepr c = binAddConst c ∘ normalizeBlock`. -/
theorem binAddConstRepr_eq_comp (c : ℕ) :
    binAddConstRepr c = binAddConst c ∘ normalizeBlock := by
  ext block
  simp [binAddConstRepr, normalizeBlock, Function.comp]
  rw [binAddConst_correct]

/-! ### Normalization Decomposition -/

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
  have h_ind : ∀ (c : ChainΓ) (block : List ChainΓ), decodeBinaryBlock (c :: block) = if c = γ'ToChainΓ Γ'.bit0 then 2 * decodeBinaryBlock block else if c = γ'ToChainΓ Γ'.bit1 then 2 * decodeBinaryBlock block + 1 else 0 := by
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

/-! ### replaceNonStandard Machine -/

/-- States for the replaceNonStandard machine.
    0 = scan, 1 = replAfterW, 2 = replace, 3 = rewind, 4 = done -/
noncomputable def replNSMachine : @TM0.Machine ChainΓ (Fin 5) ⟨0⟩ := fun q a =>
  match q with
  | (0 : Fin 5) =>
    if a = γ'ToChainΓ Γ'.bit0 then some (0, .move Dir.right)
    else if a = γ'ToChainΓ Γ'.bit1 then some (0, .move Dir.right)
    else if a = default then some (3, .move Dir.left)
    else some (1, .write (γ'ToChainΓ Γ'.bit0))
  | (1 : Fin 5) =>
    some (2, .move Dir.right)
  | (2 : Fin 5) =>
    if a = default then some (3, .move Dir.left)
    else some (1, .write (γ'ToChainΓ Γ'.bit0))
  | (3 : Fin 5) =>
    if a = default then some (4, .move Dir.right)
    else some (3, .move Dir.left)
  | (4 : Fin 5) =>
    none

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
    · have h_ind : Reaches (TM0.step replNSMachine) ⟨0, ⟨(rest ++ default :: suffix).headI, ListBlank.mk (c :: revL), ListBlank.mk (rest ++ default :: suffix).tail⟩⟩ ⟨4, Tape.mk₁ ((c :: revL).reverse ++ replaceNonStandard rest ++ default :: suffix)⟩ := by
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

/-! ### stripTrailingBit0 via reverse + dropLeadingBit0 + reverse -/

/-- Drop leading bit0 cells from a block. -/
noncomputable def dropLeadingBit0 : List ChainΓ → List ChainΓ
  | [] => []
  | c :: rest =>
    if c = γ'ToChainΓ Γ'.bit0 then dropLeadingBit0 rest
    else c :: rest

theorem stripTrailingBit0_eq_rev_drop_rev :
    stripTrailingBit0 = List.reverse ∘ dropLeadingBit0 ∘ List.reverse := by
  funext l; induction l; simp [stripTrailingBit0, dropLeadingBit0];
  rename_i x l ih; by_cases hx : x = γ'ToChainΓ Γ'.bit0 <;> by_cases hl : l = [] <;> simp_all +decide [ stripTrailingBit0, dropLeadingBit0 ] ;
  · have h_dropLeadingBit0 : ∀ (l : List ChainΓ), dropLeadingBit0 (l ++ [γ'ToChainΓ Γ'.bit0]) = if dropLeadingBit0 l = [] then [] else dropLeadingBit0 l ++ [γ'ToChainΓ Γ'.bit0] := by
      intro l; induction l <;> simp +decide [ *, dropLeadingBit0 ] ;
      grind;
    aesop;
  · have h_dropLeadingBit0 : ∀ (l : List ChainΓ) (x : ChainΓ), x ≠ γ'ToChainΓ Γ'.bit0 → dropLeadingBit0 (l ++ [x]) = dropLeadingBit0 l ++ [x] := by
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

/-- Machine for dropLeadingBit0: scan right, overwriting bit0 with default.
    State 0: if head = bit0, write default → state 1; else halt.
    State 1: move right → state 0. -/
noncomputable def dropLBMachine : @TM0.Machine ChainΓ (Fin 2) ⟨0⟩ := fun q a =>
  match q with
  | (0 : Fin 2) =>
    if a = γ'ToChainΓ Γ'.bit0 then some (1, .write default)
    else none
  | (1 : Fin 2) =>
    some (0, .move Dir.right)

theorem dropLB_step_halt {t : Tape ChainΓ} (h : t.head ≠ γ'ToChainΓ Γ'.bit0) :
    TM0.step dropLBMachine ⟨0, t⟩ = none := by
  simp [TM0.step, dropLBMachine, h]

theorem dropLeadingBit0_head_ne_bit0 (block : List ChainΓ)
    (hblock : ∀ g ∈ block, g ≠ default) :
    (dropLeadingBit0 block ++ default :: suffix).headI ≠ γ'ToChainΓ Γ'.bit0 := by
  induction block with
  | nil => simp [dropLeadingBit0]; decide
  | cons c rest ih =>
    by_cases hc : c = γ'ToChainΓ Γ'.bit0
    · simp [dropLeadingBit0, hc]
      exact ih (fun g hg => hblock g (List.mem_cons_of_mem _ hg))
    · simp [dropLeadingBit0, hc, hc]

theorem tape_write_default_move_right_mk1 (rest suffix : List ChainΓ) :
    Tape.move Dir.right (Tape.write default (Tape.mk₁ (γ'ToChainΓ Γ'.bit0 :: rest ++ default :: suffix))) =
    Tape.mk₁ (rest ++ default :: suffix) := by
  convert Quot.sound ?_;
  all_goals norm_num [ Tape.mk₁, Tape.mk₂, Tape.mk', Tape.write, Tape.move ];
  exact?;
  constructor;
  constructor;
  swap;
  exacts [ 1, rfl ]

theorem dropLB_reaches (block suffix : List ChainΓ)
    (hblock : ∀ g ∈ block, g ≠ default) :
    Reaches (TM0.step dropLBMachine)
      (TM0.init (block ++ default :: suffix))
      ⟨0, Tape.mk₁ (dropLeadingBit0 block ++ default :: suffix)⟩ := by
  -- We'll use induction on the block to prove this.
  induction' block with c rest ih;
  · constructor;
  · unfold dropLeadingBit0;
    split_ifs <;> simp_all +decide [ List.append_assoc ];
    · have h_step2 : TM0.step dropLBMachine ⟨1, Tape.write default (Tape.mk₁ (γ'ToChainΓ Γ'.bit0 :: (rest ++ default :: suffix)))⟩ = some ⟨0, Tape.mk₁ (rest ++ default :: suffix)⟩ := by
        convert tape_write_default_move_right_mk1 rest suffix using 1;
        simp +decide [ TM0.step, dropLBMachine ]
      generalize_proofs at *; (
      exact .trans ( .single <| by aesop ) ( .trans ( .single <| by aesop ) ih ));
    · constructor

theorem tm0_dropLeadingBit0 : TM0RealizesBlock ChainΓ dropLeadingBit0 := by
  refine' ⟨ _, _, _, _, _ ⟩;
  exact Fin 2;
  all_goals try infer_instance;
  exact?;
  intro block suffix hblock hsuffix hfblock
  refine' ⟨ _, _ ⟩;
  · exact Part.dom_iff_mem.mpr ⟨ _, Turing.mem_eval.mpr ⟨ dropLB_reaches block suffix hblock, dropLB_step_halt ( dropLeadingBit0_head_ne_bit0 block hblock ) ⟩ ⟩;
  · have h_reaches := dropLB_reaches block suffix hblock;
    intro h
    have h_mem := Turing.mem_eval.mpr ⟨h_reaches, by
      apply dropLB_step_halt;
      convert dropLeadingBit0_head_ne_bit0 block hblock using 1⟩
    generalize_proofs at *;
    exact ( Part.mem_unique ( Part.get_mem h ) h_mem ).symm ▸ rfl

/-
**stripTrailingBit0 is block-realizable.**
    Decomposed as: reverse, drop leading bit0, reverse.
-/
theorem tm0_stripTrailingBit0 : TM0RealizesBlock ChainΓ stripTrailingBit0 := by
  grind +suggestions

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

/-! ### Normalization is block-realizable -/

/-- **Normalization is block-realizable.**
    Decomposed as `stripTrailingBit0 ∘ replaceNonStandard`. -/
theorem tm0_normalizeBlock : TM0RealizesBlock ChainΓ normalizeBlock := by
  rw [normalizeBlock_eq_comp]
  exact tm0RealizesBlock_comp tm0_replaceNonStandard tm0_stripTrailingBit0
    (fun block hblock => replaceNonStandard_ne_default block hblock)

/-- **Addition via decode/encode is block-realizable.** -/
theorem tm0_binAddConstRepr_block (c : ℕ) :
    TM0RealizesBlock ChainΓ (binAddConstRepr c) := by
  rw [binAddConstRepr_eq_comp]
  exact tm0RealizesBlock_comp tm0_normalizeBlock (tm0_binAddConst_block c)
    (fun _ _ => normalizeBlock_ne_default _)
