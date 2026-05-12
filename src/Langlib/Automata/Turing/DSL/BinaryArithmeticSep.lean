import Mathlib
import Langlib.Automata.Turing.DSL.BinaryArithmetic
import Langlib.Automata.Turing.DSL.BlockSepPrefix

/-! # Separator-parameterized versions of normalize and related block operations

This file provides `TM0RealizesBlockSep` versions of the machines in
`BinaryArithmetic.lean`. The machines are parameterized by an arbitrary
separator `sep` that is distinct from the block content.

For `normalizeBlock` and `binSucc`, the content consists of binary
digits (`bit0`, `bit1`), so the separator must differ from both.
-/

open Turing PartrecToTM2 TM2to1

/-! ## replaceNonStandard — sep-parameterized machine -/

/-- replaceNonStandard machine parameterized by separator.
    **Important:** The `sep` check comes before `bit0`/`bit1` checks
    so that when `sep` happens to equal `bit0` or `bit1`, the machine
    still correctly detects the block boundary.
    State 3 (rewind) uses `default` for left edge detection. -/
noncomputable def replNSMachineSep (sep : ChainΓ) : @TM0.Machine ChainΓ (Fin 5) ⟨0⟩ :=
  fun q a =>
  match q with
  | (0 : Fin 5) =>
    if a = sep then some (3, .move Dir.left)
    else if a = γ'ToChainΓ Γ'.bit0 then some (0, .move Dir.right)
    else if a = γ'ToChainΓ Γ'.bit1 then some (0, .move Dir.right)
    else some (1, .write (γ'ToChainΓ Γ'.bit0))
  | (1 : Fin 5) =>
    some (2, .move Dir.right)
  | (2 : Fin 5) =>
    if a = sep then some (3, .move Dir.left)
    else some (1, .write (γ'ToChainΓ Γ'.bit0))
  | (3 : Fin 5) =>
    if a = default then some (4, .move Dir.right)
    else some (3, .move Dir.left)
  | (4 : Fin 5) =>
    none

theorem replNS_rwdLoop_sep (sep : ChainΓ) (revL : List ChainΓ)
    (hrevL : ∀ g ∈ revL, g ≠ default) (acc : List ChainΓ) :
    Reaches (TM0.step (replNSMachineSep sep))
      ⟨3, ⟨revL.headI, ListBlank.mk revL.tail, ListBlank.mk acc⟩⟩
      ⟨3, ⟨default, ListBlank.mk [], ListBlank.mk (revL.reverse ++ acc)⟩⟩ := by
  unfold replNSMachineSep;
  induction' revL with a revL ih generalizing acc;
  · constructor;
  · convert Relation.ReflTransGen.head _ ( ih ( fun g hg => hrevL g ( List.mem_cons_of_mem _ hg ) ) ( a :: acc ) ) using 1;
    · simp +decide [ List.reverse_cons ];
    · unfold TM0.step; aesop;

theorem replNS_replLoop_sep (sep : ChainΓ) (cells : List ChainΓ)
    (hcells : ∀ g ∈ cells, g ≠ default) (hcells_nsep : ∀ g ∈ cells, g ≠ sep)
    (revL : List ChainΓ) (suffix : List ChainΓ) :
    Reaches (TM0.step (replNSMachineSep sep))
      ⟨2, ⟨(cells ++ sep :: suffix).headI,
           ListBlank.mk revL,
           ListBlank.mk (cells ++ sep :: suffix).tail⟩⟩
      ⟨3, ⟨(List.replicate cells.length (γ'ToChainΓ Γ'.bit0) ++ revL).headI,
           ListBlank.mk (List.replicate cells.length (γ'ToChainΓ Γ'.bit0) ++ revL).tail,
           ListBlank.mk (sep :: suffix)⟩⟩ := by
  revert cells hcells hcells_nsep revL suffix;
  intro cells hcells hcells_nsep;
  induction' cells with c cells ih generalizing sep;
  · intro revL suffix;
    constructor;
    constructor;
    simp +decide [ TM0.step, replNSMachineSep ];
    cases revL <;> aesop;
  · intro revL suffix
    have h_step : TM0.step (replNSMachineSep sep) ⟨2, ⟨(c :: cells ++ sep :: suffix).headI, ListBlank.mk revL, ListBlank.mk (c :: cells ++ sep :: suffix).tail⟩⟩ = some ⟨1, ⟨γ'ToChainΓ Γ'.bit0, ListBlank.mk revL, ListBlank.mk (cells ++ sep :: suffix)⟩⟩ := by
      unfold replNSMachineSep; simp +decide [ hcells, hcells_nsep ] ;
      unfold TM0.step; simp +decide [ hcells, hcells_nsep ] ;
    convert Relation.ReflTransGen.trans _ ( ih sep _ _ _ _ ) using 1;
    rotate_left;
    exact .single ( by tauto ) |> Relation.ReflTransGen.trans <| .single ( by tauto );
    · exact fun g hg => hcells g <| List.mem_cons_of_mem _ hg;
    · exact fun g hg => hcells_nsep g <| List.mem_cons_of_mem _ hg;
    · cases cells <;> simp +decide [ List.replicate ];
      exact congr_arg _ ( by induction' ( List.length ‹_› ) with n ih <;> simp +decide [ List.replicate ] at * ; tauto )

/-- Base case helper: after rewind, state 3 at default transitions to
    state 4 with the correct Tape.mk₁ result. -/
private theorem replNS_final_step_sep (data : List ChainΓ) :
    Reaches (TM0.step (replNSMachineSep sep))
      ⟨3, ⟨default, ListBlank.mk [], ListBlank.mk data⟩⟩
      ⟨4, Tape.mk₁ data⟩ := by
  apply Relation.ReflTransGen.single
  simp only [TM0.step]
  simp only [replNSMachineSep]
  simp +decide
  simp [Tape.move, Tape.mk₁, Tape.mk₂, Tape.mk']
  exact listBlank_mk_append_default []

theorem replNS_scan_gen_sep (sep : ChainΓ) (block suffix : List ChainΓ)
    (revL : List ChainΓ)
    (hblock : ∀ g ∈ block, g ≠ default)
    (hblock_nsep : ∀ g ∈ block, g ≠ sep)
    (hrevL : ∀ g ∈ revL, g ≠ default) :
    Reaches (TM0.step (replNSMachineSep sep))
      ⟨0, ⟨(block ++ sep :: suffix).headI,
           ListBlank.mk revL,
           ListBlank.mk (block ++ sep :: suffix).tail⟩⟩
      ⟨4, Tape.mk₁ (revL.reverse ++ replaceNonStandard block ++ sep :: suffix)⟩ := by
  -- Apply the induction hypothesis to the block.
  have h_ind : ∀ (block : List ChainΓ) (revL : List ChainΓ) (suffix : List ChainΓ), (∀ g ∈ block, g ≠ default) → (∀ g ∈ block, g ≠ sep) → (∀ g ∈ revL, g ≠ default) → Reaches (TM0.step (replNSMachineSep sep)) ⟨0, ⟨(block ++ sep :: suffix).headI, ListBlank.mk revL, ListBlank.mk (block ++ sep :: suffix).tail⟩⟩ ⟨4, Tape.mk₁ (revL.reverse ++ replaceNonStandard block ++ sep :: suffix)⟩ := by
    intros block revL suffix hblock hblock_nsep hrevL
    induction' block with c block ih generalizing revL suffix;
    · -- In the base case, when the block is empty, the machine should transition to state 3 and then to state 4.
      have h_base : Reaches (TM0.step (replNSMachineSep sep)) ⟨0, ⟨sep, ListBlank.mk revL, ListBlank.mk suffix⟩⟩ ⟨3, ⟨default, ListBlank.mk [], ListBlank.mk (revL.reverse ++ sep :: suffix)⟩⟩ := by
        have h_base : Reaches (TM0.step (replNSMachineSep sep)) ⟨0, ⟨sep, ListBlank.mk revL, ListBlank.mk suffix⟩⟩ ⟨3, ⟨revL.headI, ListBlank.mk revL.tail, ListBlank.mk (sep :: suffix)⟩⟩ := by
          constructor;
          constructor;
          unfold replNSMachineSep; simp +decide [ TM0.step ] ;
          cases revL <;> simp +decide [ Tape.move ];
        exact h_base.trans ( replNS_rwdLoop_sep sep revL hrevL ( sep :: suffix ) );
      convert h_base.trans _ using 1;
      convert replNS_final_step_sep ( revL.reverse ++ sep :: suffix ) using 1;
      simp +decide [ replaceNonStandard ];
    · by_cases hc : c = γ'ToChainΓ Γ'.bit0 ∨ c = γ'ToChainΓ Γ'.bit1;
      · specialize ih ( c :: revL ) suffix ; simp_all +decide [ replaceNonStandard ];
        cases hc <;> simp_all +decide [ ListBlank.mk ];
        · refine' Relation.ReflTransGen.head _ ih;
          unfold TM0.step;
          unfold replNSMachineSep; simp +decide [ hblock_nsep ] ;
          cases block <;> aesop;
        · refine' Relation.ReflTransGen.trans _ ih;
          apply_rules [ Relation.ReflTransGen.single ];
          unfold replNSMachineSep; simp +decide [ TM0.step ] ;
          exact ⟨ _, if_neg hblock_nsep.1, by cases block <;> cases suffix <;> rfl ⟩;
      · have h_replace : Reaches (TM0.step (replNSMachineSep sep)) ⟨0, ⟨c, ListBlank.mk revL, ListBlank.mk (block ++ sep :: suffix)⟩⟩ ⟨2, ⟨(block ++ sep :: suffix).headI, ListBlank.mk (γ'ToChainΓ Γ'.bit0 :: revL), ListBlank.mk (block ++ sep :: suffix).tail⟩⟩ := by
          have h_replace : TM0.step (replNSMachineSep sep) ⟨0, ⟨c, ListBlank.mk revL, ListBlank.mk (block ++ sep :: suffix)⟩⟩ = some ⟨1, ⟨γ'ToChainΓ Γ'.bit0, ListBlank.mk revL, ListBlank.mk (block ++ sep :: suffix)⟩⟩ := by
            unfold TM0.step;
            unfold replNSMachineSep; simp +decide [ hc, hblock_nsep ] ;
            split_ifs <;> tauto;
          have h_replace : TM0.step (replNSMachineSep sep) ⟨1, ⟨γ'ToChainΓ Γ'.bit0, ListBlank.mk revL, ListBlank.mk (block ++ sep :: suffix)⟩⟩ = some ⟨2, ⟨(block ++ sep :: suffix).headI, ListBlank.mk (γ'ToChainΓ Γ'.bit0 :: revL), ListBlank.mk (block ++ sep :: suffix).tail⟩⟩ := by
            unfold TM0.step; simp +decide [ replNSMachineSep ] ;
            cases block <;> simp +decide [ Tape.move ];
          exact Relation.ReflTransGen.tail ( Relation.ReflTransGen.single ‹_› ) ‹_›;
        have h_replace_loop : Reaches (TM0.step (replNSMachineSep sep)) ⟨2, ⟨(block ++ sep :: suffix).headI, ListBlank.mk (γ'ToChainΓ Γ'.bit0 :: revL), ListBlank.mk (block ++ sep :: suffix).tail⟩⟩ ⟨3, ⟨(List.replicate block.length (γ'ToChainΓ Γ'.bit0) ++ γ'ToChainΓ Γ'.bit0 :: revL).headI, ListBlank.mk (List.replicate block.length (γ'ToChainΓ Γ'.bit0) ++ γ'ToChainΓ Γ'.bit0 :: revL).tail, ListBlank.mk (sep :: suffix)⟩⟩ := by
          apply replNS_replLoop_sep;
          · exact fun g hg => hblock g <| List.mem_cons_of_mem _ hg;
          · exact fun g hg => hblock_nsep g <| List.mem_cons_of_mem _ hg;
        have h_rewrite : Reaches (TM0.step (replNSMachineSep sep)) ⟨3, ⟨(List.replicate block.length (γ'ToChainΓ Γ'.bit0) ++ γ'ToChainΓ Γ'.bit0 :: revL).headI, ListBlank.mk (List.replicate block.length (γ'ToChainΓ Γ'.bit0) ++ γ'ToChainΓ Γ'.bit0 :: revL).tail, ListBlank.mk (sep :: suffix)⟩⟩ ⟨3, ⟨default, ListBlank.mk [], ListBlank.mk (revL.reverse ++ List.replicate (block.length + 1) (γ'ToChainΓ Γ'.bit0) ++ sep :: suffix)⟩⟩ := by
          convert replNS_rwdLoop_sep sep ( List.replicate block.length ( γ'ToChainΓ Γ'.bit0 ) ++ γ'ToChainΓ Γ'.bit0 :: revL ) _ _ using 1;
          · simp +decide [ List.replicate ];
          · simp +zetaDelta at *;
            rintro g ( ⟨ _, rfl ⟩ | rfl | hg ) <;> simp_all +decide [ ChainΓ ];
        have h_final : Reaches (TM0.step (replNSMachineSep sep)) ⟨3, ⟨default, ListBlank.mk [], ListBlank.mk (revL.reverse ++ List.replicate (block.length + 1) (γ'ToChainΓ Γ'.bit0) ++ sep :: suffix)⟩⟩ ⟨4, Tape.mk₁ (revL.reverse ++ List.replicate (block.length + 1) (γ'ToChainΓ Γ'.bit0) ++ sep :: suffix)⟩ := by
          apply replNS_final_step_sep;
        convert h_replace.trans ( h_replace_loop.trans ( h_rewrite.trans h_final ) ) using 1;
        simp +decide [ replaceNonStandard, hc ];
        grind;
  exact h_ind block revL suffix hblock hblock_nsep hrevL

theorem replNS_reaches_sep (sep : ChainΓ) (block suffix : List ChainΓ)
    (hblock : ∀ g ∈ block, g ≠ default) (hblock_nsep : ∀ g ∈ block, g ≠ sep) :
    Reaches (TM0.step (replNSMachineSep sep))
      (TM0.init (block ++ sep :: suffix))
      ⟨4, Tape.mk₁ (replaceNonStandard block ++ sep :: suffix)⟩ :=
  replNS_scan_gen_sep sep block suffix [] hblock hblock_nsep (by simp)

/-- **replaceNonStandard is block-realizable before any separator**, with an
unrestricted suffix after the separator. -/
theorem tm0_replaceNonStandard_blockSep_anySuffix {sep : ChainΓ} :
    TM0RealizesBlockSepAnySuffix ChainΓ sep replaceNonStandard := by
  refine ⟨Fin 5, ⟨0⟩, inferInstance, replNSMachineSep sep,
    fun block suffix hblock hblock_nsep _hfblock _hfblock_nsep => ?_⟩
  have h_reaches := replNS_reaches_sep sep block suffix hblock hblock_nsep
  constructor
  · exact Part.dom_iff_mem.mpr ⟨_, Turing.mem_eval.mpr
      ⟨h_reaches, by simp [TM0.step, replNSMachineSep]⟩⟩
  · intro h
    exact (Part.mem_unique (Part.get_mem h) (Turing.mem_eval.mpr
      ⟨h_reaches, by simp [TM0.step, replNSMachineSep]⟩)).symm ▸ rfl

/-- **replaceNonStandard is block-realizable before any separator.** -/
theorem tm0_replaceNonStandard_blockSep {sep : ChainΓ} :
    TM0RealizesBlockSep ChainΓ sep replaceNonStandard :=
  tm0RealizesBlockSep_of_anySuffix tm0_replaceNonStandard_blockSep_anySuffix

/-! ## dropLeadingBit0 — sep version -/

/-- dropLeadingBit0 machine parameterized by separator.
    Checks `sep` first so that when `sep = bit0`, the machine halts
    at the separator instead of erasing it. -/
noncomputable def dropLBMachineSep (sep : ChainΓ) :
    @TM0.Machine ChainΓ (Fin 2) ⟨0⟩ := fun q a =>
  match q with
  | (0 : Fin 2) =>
    if a = sep then none
    else if a = γ'ToChainΓ Γ'.bit0 then some (1, .write default)
    else none
  | (1 : Fin 2) =>
    some (0, .move Dir.right)

/-
Single step: erase bit0 at head, move right.
-/
private theorem dropLBSep_erase_step (sep : ChainΓ) (rest suffix : List ChainΓ)
    (hsep : γ'ToChainΓ Γ'.bit0 ≠ sep) :
    Reaches (TM0.step (dropLBMachineSep sep))
      ⟨0, Tape.mk₁ (γ'ToChainΓ Γ'.bit0 :: rest ++ sep :: suffix)⟩
      ⟨0, Tape.mk₁ (rest ++ sep :: suffix)⟩ := by
  have h_step : Reaches (TM0.step (dropLBMachineSep sep)) ⟨0, Tape.mk₁ (γ'ToChainΓ Γ'.bit0 :: rest ++ sep :: suffix)⟩ ⟨1, Tape.write default (Tape.mk₁ (γ'ToChainΓ Γ'.bit0 :: rest ++ sep :: suffix))⟩ := by
    apply Relation.ReflTransGen.single;
    unfold TM0.step;
    unfold dropLBMachineSep; aesop;
  refine' h_step.trans _;
  apply Relation.ReflTransGen.single;
  convert tape_write_default_move_right_mk1 rest ( sep :: suffix ) using 1;
  unfold dropLBMachineSep; simp +decide [ TM0.step ] ;
  simp +decide [ Tape.mk₁ ];
  simp +decide [ Tape.mk₂, Tape.write ];
  simp +decide [ Tape.move, Tape.mk' ]

theorem dropLB_reaches_sep (sep : ChainΓ) (block suffix : List ChainΓ)
    (hblock : ∀ g ∈ block, g ≠ default)
    (hblock_nsep : ∀ g ∈ block, g ≠ sep) :
    Reaches (TM0.step (dropLBMachineSep sep))
      (TM0.init (block ++ sep :: suffix))
      ⟨0, Tape.mk₁ (dropLeadingBit0 block ++ sep :: suffix)⟩ := by
  induction' block with c block ih generalizing suffix;
  · constructor;
  · by_cases hc : c = γ'ToChainΓ Γ'.bit0 <;> simp_all +decide [ Reaches ];
    · convert Relation.ReflTransGen.trans ( dropLBSep_erase_step sep block suffix hblock_nsep.1 ) ( ih ( suffix ) ) using 1;
    · rw [ show dropLeadingBit0 ( c :: block ) = c :: block from _ ];
      · cases c ; aesop;
      · exact if_neg hc

theorem dropLBSep_step_halt (sep : ChainΓ) (block suffix : List ChainΓ)
    (hblock_nsep : ∀ g ∈ block, g ≠ sep) :
    TM0.step (dropLBMachineSep sep)
      ⟨0, Tape.mk₁ (dropLeadingBit0 block ++ sep :: suffix)⟩ = none := by
  unfold TM0.step;
  unfold dropLBMachineSep; simp +decide [ Tape.mk₁ ] ;
  cases h : dropLeadingBit0 block <;> simp_all +decide [ Tape.mk₂ ];
  contrapose! h; induction block <;> simp_all +decide [ dropLeadingBit0 ] ;
  grind

/-- **dropLeadingBit0 is block-realizable before any separator**, with an
unrestricted suffix after the separator. -/
theorem tm0_dropLeadingBit0_blockSep_anySuffix {sep : ChainΓ} :
    TM0RealizesBlockSepAnySuffix ChainΓ sep dropLeadingBit0 := by
  refine ⟨Fin 2, ⟨0⟩, inferInstance, dropLBMachineSep sep,
    fun block suffix _hblock hblock_nsep _hfblock _hfblock_nsep => ?_⟩
  have h_reaches := dropLB_reaches_sep sep block suffix _hblock hblock_nsep
  have h_halt := dropLBSep_step_halt sep block suffix hblock_nsep
  constructor
  · exact Part.dom_iff_mem.mpr ⟨_, Turing.mem_eval.mpr ⟨h_reaches, h_halt⟩⟩
  · intro h
    exact (Part.mem_unique (Part.get_mem h)
      (Turing.mem_eval.mpr ⟨h_reaches, h_halt⟩)).symm ▸ rfl

/-- **dropLeadingBit0 is block-realizable before any separator.** -/
theorem tm0_dropLeadingBit0_blockSep {sep : ChainΓ} :
    TM0RealizesBlockSep ChainΓ sep dropLeadingBit0 :=
  tm0RealizesBlockSep_of_anySuffix tm0_dropLeadingBit0_blockSep_anySuffix

/-! ## stripTrailingBit0 — sep version -/

theorem dropLeadingBit0_ne_sep (block : List ChainΓ)
    (hblock_nsep : ∀ g ∈ block, g ≠ sep) :
    ∀ g ∈ dropLeadingBit0 block, g ≠ sep := by
  intro g hg
  have : g ∈ block := by
    induction block with
    | nil => simp [dropLeadingBit0] at hg
    | cons c rest ih =>
      simp [dropLeadingBit0] at hg
      split_ifs at hg with hc
      · exact List.mem_cons_of_mem _ (ih (fun g hg => hblock_nsep g (List.mem_cons_of_mem _ hg)) hg)
      · exact hg
  exact hblock_nsep g this

/-- **stripTrailingBit0 is block-realizable before any separator**, with an
    unrestricted suffix after the separator.
    Decomposed as: reverse, drop leading bit0, reverse. -/
theorem tm0_stripTrailingBit0_blockSep_anySuffix {sep : ChainΓ} :
    TM0RealizesBlockSepAnySuffix ChainΓ sep stripTrailingBit0 := by
  rw [stripTrailingBit0_eq_rev_drop_rev]
  have h1 : TM0RealizesBlockSepAnySuffix ChainΓ sep
      (dropLeadingBit0 ∘ List.reverse) :=
    tm0RealizesBlockSepAnySuffix_comp
      tm0_reverse_blockSep_anySuffix tm0_dropLeadingBit0_blockSep_anySuffix
      (fun block hblock => reverse_ne_default block hblock)
      (fun block hblock => reverse_ne_sep block hblock)
  exact tm0RealizesBlockSepAnySuffix_comp h1 tm0_reverse_blockSep_anySuffix
    (fun block hblock =>
      dropLeadingBit0_ne_default _ (fun g hg => reverse_ne_default block hblock g hg))
    (fun block hblock =>
      dropLeadingBit0_ne_sep _ (fun g hg => reverse_ne_sep block hblock g hg))

/-- **stripTrailingBit0 is block-realizable before any separator.**
    Decomposed as: reverse, drop leading bit0, reverse. -/
theorem tm0_stripTrailingBit0_blockSep {sep : ChainΓ} :
    TM0RealizesBlockSep ChainΓ sep stripTrailingBit0 :=
  tm0RealizesBlockSep_of_anySuffix tm0_stripTrailingBit0_blockSep_anySuffix

/-! ## Normalization — sep version -/

/-- replaceNonStandard produces only bit0 and bit1, so if `sep` differs from
    both, the output is ≠ sep. -/
theorem replaceNonStandard_ne_sep_of_bits
    {sep : ChainΓ} (hsep0 : sep ≠ γ'ToChainΓ Γ'.bit0)
    (hsep1 : sep ≠ γ'ToChainΓ Γ'.bit1) (block : List ChainΓ) :
    ∀ g ∈ replaceNonStandard block, g ≠ sep := by
  intro g hg
  have := replaceNonStandard_allBits block g hg
  rcases this with h | h <;> (rw [h]; exact Ne.symm ‹_›)

/-- Binary numerals contain only `bit0` and `bit1`, so they avoid any
separator distinct from both bits. -/
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

/-- Normalization produces only binary digits, so it cannot introduce a
separator that is distinct from both bits. -/
theorem normalizeBlock_no_of_ne_bits (sep : ChainΓ)
    (hsep0 : sep ≠ γ'ToChainΓ Γ'.bit0)
    (hsep1 : sep ≠ γ'ToChainΓ Γ'.bit1) (block : List ChainΓ) :
    ∀ g ∈ normalizeBlock block, g ≠ sep := by
  unfold normalizeBlock
  intro g hg
  exact chainBinaryRepr_no_of_ne_bits sep hsep0 hsep1 _ g hg

/-- **Normalization is block-realizable before any separator that differs
    from `bit0` and `bit1`**, with an unrestricted suffix after the separator. -/
theorem tm0_normalizeBlockSep_anySuffix {sep : ChainΓ}
    (hsep0 : sep ≠ γ'ToChainΓ Γ'.bit0) (hsep1 : sep ≠ γ'ToChainΓ Γ'.bit1) :
    TM0RealizesBlockSepAnySuffix ChainΓ sep normalizeBlock := by
  rw [normalizeBlock_eq_comp]
  exact tm0RealizesBlockSepAnySuffix_comp
    tm0_replaceNonStandard_blockSep_anySuffix
    tm0_stripTrailingBit0_blockSep_anySuffix
    (fun block hblock => replaceNonStandard_ne_default block hblock)
    (fun _block _hblock => replaceNonStandard_ne_sep_of_bits hsep0 hsep1 _)

/-- **Normalization is block-realizable before any separator that differs
    from `bit0` and `bit1`.**

    The constraint `sep ≠ bit0 ∧ sep ≠ bit1` is necessary because the
    intermediate result of `replaceNonStandard` contains only binary digits;
    if the separator were a binary digit, the composed machine could not
    distinguish block content from the separator in the intermediate state. -/
theorem tm0_normalizeBlockSep {sep : ChainΓ}
    (hsep0 : sep ≠ γ'ToChainΓ Γ'.bit0) (hsep1 : sep ≠ γ'ToChainΓ Γ'.bit1) :
    TM0RealizesBlockSep ChainΓ sep normalizeBlock :=
  tm0RealizesBlockSep_of_anySuffix
    (tm0_normalizeBlockSep_anySuffix hsep0 hsep1)

/-! ## Binary successor — sep version -/

/-- Binary successor machine parameterized by separator `sep`.
    Designed for `sep ≠ default`. Key differences from `binSuccMachine`:
    * `carry` checks `sep` (not `default`) for block boundary / extension
    * `extRd` writes `sep` (not `default`) as the new separator
    * `shiftDn` goes to `rwdBlk` directly (not through `rwdSuf`)
    * `rwdSuf` is a simple redirect to `rwdBlk` (never entered in normal operation) -/
noncomputable def binSuccMachineSep (sep : ChainΓ) :
    @TM0.Machine ChainΓ BinSuccSt ⟨.carry⟩ := fun q a =>
  match q with
  | .carry =>
    if a = γ'ToChainΓ Γ'.bit0 then
      some (.absorbed, .write (γ'ToChainΓ Γ'.bit1))
    else if a = γ'ToChainΓ Γ'.bit1 then
      some (.carryMv, .write (γ'ToChainΓ Γ'.bit0))
    else if a = sep then
      some (.extChk, .write (γ'ToChainΓ Γ'.bit1))
    else
      some (.rwdBlk, .move Dir.left)
  | .carryMv => some (.carry, .move Dir.right)
  | .absorbed => some (.rwdBlk, .move Dir.left)
  | .extChk => some (.extRd, .move Dir.right)
  | .extRd =>
    if a = default then
      some (.rwdBlk, .write sep)
    else
      some (BinSuccSt.shiftMv a, .write sep)
  | .shiftW g =>
    if a = default then
      some (.shiftDn, .write g)
    else
      some (BinSuccSt.shiftMv a, .write g)
  | .shiftMv g => some (.shiftW g, .move Dir.right)
  | .shiftDn => some (.rwdBlk, .move Dir.left)
  | .rwdSuf => some (.rwdBlk, .move Dir.left)
  | .rwdBlk =>
    if a = default then
      some (.done, .move Dir.right)
    else
      some (.rwdBlk, .move Dir.left)
  | .done => none

/-
rwdBlk loop for sep machine (identical behavior to original).
-/
theorem binSuccSep_rwdBlk_loop (sep : ChainΓ) (revL : List ChainΓ)
    (hrevL : ∀ g ∈ revL, g ≠ default) (acc : List ChainΓ) :
    Reaches (TM0.step (binSuccMachineSep sep))
      ⟨.rwdBlk, ⟨revL.headI, ListBlank.mk revL.tail, ListBlank.mk acc⟩⟩
      ⟨.rwdBlk, ⟨default, ListBlank.mk [], ListBlank.mk (revL.reverse ++ acc)⟩⟩ := by
  -- By definition of `rwdBlk`, it will move left until it reaches the end of the list.
  have h_rwdBlk : ∀ (revL : List ChainΓ) (acc : List ChainΓ), (∀ g ∈ revL, g ≠ default) → Reaches (TM0.step (binSuccMachineSep sep)) ⟨BinSuccSt.rwdBlk, ⟨revL.headI, ListBlank.mk revL.tail, ListBlank.mk acc⟩⟩ ⟨BinSuccSt.rwdBlk, ⟨default, ListBlank.mk [], ListBlank.mk (revL.reverse ++ acc)⟩⟩ := by
    intros revL acc hrevL
    induction' revL with g revL ih generalizing acc;
    · constructor;
    · convert Relation.ReflTransGen.head _ ( ih ( g :: acc ) fun x hx => hrevL x <| List.mem_cons_of_mem _ hx ) using 1;
      · simp +decide [ List.reverse_cons ];
      · unfold binSuccMachineSep; simp +decide [ ListBlank.mk ] ;
        unfold TM0.step; simp +decide [ ListBlank.mk ] ;
        exact ⟨ TM0.Stmt.move Dir.left, by aesop, by cases revL <;> aesop ⟩;
  exact h_rwdBlk revL acc hrevL

/-
Shift loop for sep machine (identical behavior to original).
-/
theorem binSuccSep_shift_loop (sep : ChainΓ) (suffix : List ChainΓ)
    (hsuffix : ∀ g ∈ suffix, g ≠ default)
    (saved : ChainΓ) (prevL : List ChainΓ) :
    Reaches (TM0.step (binSuccMachineSep sep))
      ⟨.shiftW saved, ⟨suffix.headI, ListBlank.mk prevL, ListBlank.mk suffix.tail⟩⟩
      ⟨.shiftDn, ⟨(saved :: suffix).getLast (by simp),
                 ListBlank.mk ((saved :: suffix).dropLast.reverse ++ prevL),
                 ListBlank.mk []⟩⟩ := by
  induction' suffix with s suffix ih generalizing saved prevL;
  · constructor;
    constructor;
    constructor;
  · have h_ind := ih ( fun g hg => hsuffix g ( List.mem_cons_of_mem _ hg ) ) s ( saved :: prevL );
    refine' Relation.ReflTransGen.head _ _;
    exact ⟨ BinSuccSt.shiftMv s, ⟨ saved, ListBlank.mk prevL, ListBlank.mk suffix ⟩ ⟩;
    · simp +decide [ TM0.step, binSuccMachineSep ];
      exact ⟨ TM0.Stmt.write saved, by aesop ⟩;
    · convert h_ind.head _ using 1;
      · simp +decide [ List.dropLast, List.getLast ];
      · simp +decide [ TM0.step, binSuccMachineSep ];
        cases suffix <;> simp +decide [ Tape.move ]

/-
Case: carry at bit0, absorbed immediately.
-/
theorem binSuccSep_carry_bit0 (sep : ChainΓ)
    (hsep0 : sep ≠ γ'ToChainΓ Γ'.bit0)
    (rest suffix revLeft : List ChainΓ)
    (hrevLeft : ∀ g ∈ revLeft, g ≠ default) :
    Reaches (TM0.step (binSuccMachineSep sep))
      ⟨.carry, ⟨γ'ToChainΓ Γ'.bit0, ListBlank.mk revLeft,
               ListBlank.mk (rest ++ sep :: suffix)⟩⟩
      ⟨.done, Tape.mk₁ (revLeft.reverse ++ γ'ToChainΓ Γ'.bit1 :: rest ++ sep :: suffix)⟩ := by
  have h_absorbed : Reaches (TM0.step (binSuccMachineSep sep))
    ⟨BinSuccSt.carry, ⟨γ'ToChainΓ Γ'.bit0, ListBlank.mk revLeft, ListBlank.mk (rest ++ sep :: suffix)⟩⟩
    ⟨BinSuccSt.absorbed, ⟨γ'ToChainΓ Γ'.bit1, ListBlank.mk revLeft, ListBlank.mk (rest ++ sep :: suffix)⟩⟩ := by
      exact Relation.ReflTransGen.single ( by unfold binSuccMachineSep; aesop );
  have h_rwdBlk : Reaches (TM0.step (binSuccMachineSep sep))
    ⟨BinSuccSt.absorbed, ⟨γ'ToChainΓ Γ'.bit1, ListBlank.mk revLeft, ListBlank.mk (rest ++ sep :: suffix)⟩⟩
    ⟨BinSuccSt.rwdBlk, ⟨revLeft.headI, ListBlank.mk revLeft.tail, ListBlank.mk (γ'ToChainΓ Γ'.bit1 :: rest ++ sep :: suffix)⟩⟩ := by
      convert Relation.ReflTransGen.single _;
      cases revLeft <;> aesop;
  have h_rwdBlk_loop : Reaches (TM0.step (binSuccMachineSep sep))
    ⟨BinSuccSt.rwdBlk, ⟨revLeft.headI, ListBlank.mk revLeft.tail, ListBlank.mk (γ'ToChainΓ Γ'.bit1 :: rest ++ sep :: suffix)⟩⟩
    ⟨BinSuccSt.rwdBlk, ⟨default, ListBlank.mk [], ListBlank.mk (revLeft.reverse ++ γ'ToChainΓ Γ'.bit1 :: rest ++ sep :: suffix)⟩⟩ := by
      convert binSuccSep_rwdBlk_loop sep revLeft hrevLeft ( γ'ToChainΓ Γ'.bit1 :: rest ++ sep :: suffix ) using 1;
      simp +decide [ ListBlank.mk ];
  have h_rwdBlk_done : TM0.step (binSuccMachineSep sep) ⟨BinSuccSt.rwdBlk, ⟨default, ListBlank.mk [], ListBlank.mk (revLeft.reverse ++ γ'ToChainΓ Γ'.bit1 :: rest ++ sep :: suffix)⟩⟩ = some ⟨BinSuccSt.done, Tape.mk₁ (revLeft.reverse ++ γ'ToChainΓ Γ'.bit1 :: rest ++ sep :: suffix)⟩ := by
    simp +decide [ TM0.step, BinSuccSt ];
    use TM0.Stmt.move Dir.right;
    simp +decide [ Tape.move, Tape.mk₁ ];
    simp +decide [ Tape.mk₂ ];
    simp +decide [ Tape.mk' ];
    exact ⟨ rfl, listBlank_mk_append_default [ ] ⟩;
  convert h_absorbed.trans ( h_rwdBlk.trans ( h_rwdBlk_loop.trans ( Relation.ReflTransGen.single h_rwdBlk_done ) ) ) using 1

/-
Case: carry at bit1, recursive on rest.
-/
theorem binSuccSep_carry_bit1 (sep : ChainΓ)
    (hsep1 : sep ≠ γ'ToChainΓ Γ'.bit1)
    (rest suffix revLeft : List ChainΓ)
    (ih : Reaches (TM0.step (binSuccMachineSep sep))
      ⟨.carry, ⟨(rest ++ sep :: suffix).headI,
               ListBlank.mk (γ'ToChainΓ Γ'.bit0 :: revLeft),
               ListBlank.mk (rest ++ sep :: suffix).tail⟩⟩
      ⟨.done, Tape.mk₁ ((γ'ToChainΓ Γ'.bit0 :: revLeft).reverse ++ binSucc rest ++ sep :: suffix)⟩) :
    Reaches (TM0.step (binSuccMachineSep sep))
      ⟨.carry, ⟨γ'ToChainΓ Γ'.bit1, ListBlank.mk revLeft,
               ListBlank.mk (rest ++ sep :: suffix)⟩⟩
      ⟨.done, Tape.mk₁ (revLeft.reverse ++ γ'ToChainΓ Γ'.bit0 :: binSucc rest ++ sep :: suffix)⟩ := by
  cases' h : rest <;> simp_all +decide [ Reaches ];
  · refine' Relation.ReflTransGen.head _ _;
    exact ⟨ BinSuccSt.carryMv, ⟨ γ'ToChainΓ Γ'.bit0, ListBlank.mk revLeft, ListBlank.mk ( sep :: suffix ) ⟩ ⟩;
    · unfold binSuccMachineSep; aesop;
    · convert ih.head _ using 1;
      unfold binSuccMachineSep; aesop;
  · convert Relation.ReflTransGen.trans _ ih using 1;
    constructor;
    exact .single rfl;
    simp +decide [ TM0.step, binSuccMachineSep ];
    simp +decide [ Tape.move ]

/-
Case: carry at non-bit, non-sep cell. No-op, just rewind.
-/
theorem binSuccSep_carry_other (sep : ChainΓ)
    (c : ChainΓ) (rest suffix revLeft : List ChainΓ)
    (hc : c ≠ γ'ToChainΓ Γ'.bit0) (hc1 : c ≠ γ'ToChainΓ Γ'.bit1) (hc2 : c ≠ sep)
    (hrevLeft : ∀ g ∈ revLeft, g ≠ default) :
    Reaches (TM0.step (binSuccMachineSep sep))
      ⟨.carry, ⟨c, ListBlank.mk revLeft,
               ListBlank.mk (rest ++ sep :: suffix)⟩⟩
      ⟨.done, Tape.mk₁ (revLeft.reverse ++ c :: rest ++ sep :: suffix)⟩ := by
  have h_rwdBlk : Reaches (TM0.step (binSuccMachineSep sep))
    ⟨.rwdBlk, ⟨revLeft.headI, ListBlank.mk revLeft.tail, ListBlank.mk (c :: rest ++ sep :: suffix)⟩⟩
    ⟨.rwdBlk, ⟨default, ListBlank.mk [], ListBlank.mk (revLeft.reverse ++ c :: rest ++ sep :: suffix)⟩⟩ := by
      convert binSuccSep_rwdBlk_loop sep revLeft hrevLeft ( c :: rest ++ sep :: suffix ) using 1;
      simp +decide [ List.append_assoc ];
  have h_done : TM0.step (binSuccMachineSep sep) ⟨.rwdBlk, ⟨default, ListBlank.mk [], ListBlank.mk (revLeft.reverse ++ c :: rest ++ sep :: suffix)⟩⟩ = some ⟨.done, Tape.mk₁ (revLeft.reverse ++ c :: rest ++ sep :: suffix)⟩ := by
    unfold binSuccMachineSep; simp +decide [ TM0.step ] ;
    unfold Tape.move; simp +decide [ ListBlank.mk ] ;
    unfold Tape.mk₁; simp +decide [ ListBlank.head, ListBlank.tail ] ;
    unfold Tape.mk₂; simp +decide [ ListBlank.cons, ListBlank.mk ] ;
    unfold Tape.mk'; simp +decide [ ListBlank.head, ListBlank.tail ] ;
    exact ⟨ listBlank_mk_append_default [], rfl ⟩;
  have h_step : Reaches (TM0.step (binSuccMachineSep sep))
    ⟨.carry, ⟨c, ListBlank.mk revLeft, ListBlank.mk (rest ++ sep :: suffix)⟩⟩
    ⟨.rwdBlk, ⟨revLeft.headI, ListBlank.mk revLeft.tail, ListBlank.mk (c :: rest ++ sep :: suffix)⟩⟩ := by
      constructor;
      constructor;
      unfold binSuccMachineSep; simp +decide [ hc, hc1, hc2 ] ;
      unfold TM0.step; simp +decide [ hc, hc1, hc2 ] ;
      cases revLeft <;> aesop;
  exact h_step.trans ( h_rwdBlk.trans ( Relation.ReflTransGen.single h_done ) )

/-
After rwdBlk reaches default, transition to done gives Tape.mk₁.
-/
theorem binSuccSep_rwdBlk_done (sep : ChainΓ) (data : List ChainΓ) :
    Reaches (TM0.step (binSuccMachineSep sep))
      ⟨.rwdBlk, ⟨default, ListBlank.mk [], ListBlank.mk data⟩⟩
      ⟨.done, Tape.mk₁ data⟩ := by
  convert Relation.ReflTransGen.single _;
  unfold binSuccMachineSep; simp +decide [ Tape.mk₁ ] ;
  unfold TM0.step;
  unfold ListBlank.mk; simp +decide [ Tape.mk₁ ] ;
  unfold Tape.move; simp +decide [ Tape.mk₂ ] ;
  unfold ListBlank.cons; simp +decide [ Tape.mk' ] ;
  exact ⟨ rfl, listBlank_mk_append_default [ ], rfl ⟩

/-- Case: carry at sep (extension), empty suffix.
    Requires `sep ≠ default` so that `rwdBlk` correctly traverses past `sep`. -/
theorem binSuccSep_carry_ext_nil (sep : ChainΓ)
    (hsep0 : sep ≠ γ'ToChainΓ Γ'.bit0) (hsep1 : sep ≠ γ'ToChainΓ Γ'.bit1)
    (hsep_nd : sep ≠ default)
    (revLeft : List ChainΓ)
    (hrevLeft : ∀ g ∈ revLeft, g ≠ default) :
    Reaches (TM0.step (binSuccMachineSep sep))
      ⟨.carry, ⟨sep, ListBlank.mk revLeft, ListBlank.mk []⟩⟩
      ⟨.done, Tape.mk₁ (revLeft.reverse ++ [γ'ToChainΓ Γ'.bit1, sep])⟩ := by
  -- Step 1: carry at sep → extChk, write bit1
  have h1 : Reaches (TM0.step (binSuccMachineSep sep))
    ⟨.carry, ⟨sep, ListBlank.mk revLeft, ListBlank.mk []⟩⟩
    ⟨.extChk, ⟨γ'ToChainΓ Γ'.bit1, ListBlank.mk revLeft, ListBlank.mk []⟩⟩ :=
    .single (by unfold TM0.step binSuccMachineSep; simp +decide [hsep0, hsep1])
  -- Step 2: extChk → extRd, move right
  have h2 : Reaches (TM0.step (binSuccMachineSep sep))
    ⟨.extChk, ⟨γ'ToChainΓ Γ'.bit1, ListBlank.mk revLeft, ListBlank.mk []⟩⟩
    ⟨.extRd, ⟨default, ListBlank.mk (γ'ToChainΓ Γ'.bit1 :: revLeft), ListBlank.mk []⟩⟩ :=
    .single (by simp +decide [TM0.step, binSuccMachineSep, Tape.move])
  -- Step 3: extRd at default → rwdBlk, write sep
  have h3 : Reaches (TM0.step (binSuccMachineSep sep))
    ⟨.extRd, ⟨default, ListBlank.mk (γ'ToChainΓ Γ'.bit1 :: revLeft), ListBlank.mk []⟩⟩
    ⟨.rwdBlk, ⟨sep, ListBlank.mk (γ'ToChainΓ Γ'.bit1 :: revLeft), ListBlank.mk []⟩⟩ :=
    .single (by unfold TM0.step binSuccMachineSep; aesop)
  -- Phase 4: rwdBlk loop through [sep, bit1] ++ revLeft
  have h4 := binSuccSep_rwdBlk_loop sep (sep :: γ'ToChainΓ Γ'.bit1 :: revLeft)
    (by intro g hg; simp at hg; rcases hg with rfl | rfl | hg
        <;> [exact hsep_nd; decide; exact hrevLeft g hg]) []
  simp [List.reverse_cons] at h4
  exact h1.trans (h2.trans (h3.trans (h4.trans (binSuccSep_rwdBlk_done sep _))))

/-- Case: carry at sep (extension), non-empty suffix.
    Requires `sep ≠ default` so that `rwdBlk` correctly traverses past `sep`. -/
theorem binSuccSep_carry_ext_cons (sep : ChainΓ)
    (hsep0 : sep ≠ γ'ToChainΓ Γ'.bit0) (hsep1 : sep ≠ γ'ToChainΓ Γ'.bit1)
    (hsep_nd : sep ≠ default)
    (s : ChainΓ) (rest revLeft : List ChainΓ)
    (hs : s ≠ default)
    (hrest : ∀ g ∈ rest, g ≠ default)
    (hrevLeft : ∀ g ∈ revLeft, g ≠ default) :
    Reaches (TM0.step (binSuccMachineSep sep))
      ⟨.carry, ⟨sep, ListBlank.mk revLeft, ListBlank.mk (s :: rest)⟩⟩
      ⟨.done, Tape.mk₁ (revLeft.reverse ++ γ'ToChainΓ Γ'.bit1 :: sep :: s :: rest)⟩ := by
  -- Step 1: carry at sep → extChk, write bit1
  have h1 : Reaches (TM0.step (binSuccMachineSep sep))
    ⟨.carry, ⟨sep, ListBlank.mk revLeft, ListBlank.mk (s :: rest)⟩⟩
    ⟨.extChk, ⟨γ'ToChainΓ Γ'.bit1, ListBlank.mk revLeft, ListBlank.mk (s :: rest)⟩⟩ :=
    .single (by unfold TM0.step binSuccMachineSep; simp +decide [hsep0, hsep1])
  -- Step 2: extChk → extRd, move right
  have h2 : Reaches (TM0.step (binSuccMachineSep sep))
    ⟨.extChk, ⟨γ'ToChainΓ Γ'.bit1, ListBlank.mk revLeft, ListBlank.mk (s :: rest)⟩⟩
    ⟨.extRd, ⟨s, ListBlank.mk (γ'ToChainΓ Γ'.bit1 :: revLeft), ListBlank.mk rest⟩⟩ :=
    .single (by simp +decide [TM0.step, binSuccMachineSep, Tape.move])
  -- Step 3: extRd at s (≠ default) → shiftMv s, write sep
  have h3 : Reaches (TM0.step (binSuccMachineSep sep))
    ⟨.extRd, ⟨s, ListBlank.mk (γ'ToChainΓ Γ'.bit1 :: revLeft), ListBlank.mk rest⟩⟩
    ⟨.shiftMv s, ⟨sep, ListBlank.mk (γ'ToChainΓ Γ'.bit1 :: revLeft), ListBlank.mk rest⟩⟩ :=
    .single (by unfold TM0.step binSuccMachineSep; simp +decide [hs])
  -- Step 4: shiftMv s → shiftW s, move right
  have h4 : Reaches (TM0.step (binSuccMachineSep sep))
    ⟨.shiftMv s, ⟨sep, ListBlank.mk (γ'ToChainΓ Γ'.bit1 :: revLeft), ListBlank.mk rest⟩⟩
    ⟨.shiftW s, ⟨rest.headI, ListBlank.mk (sep :: γ'ToChainΓ Γ'.bit1 :: revLeft), ListBlank.mk rest.tail⟩⟩ :=
    .single (by cases rest <;> simp +decide [TM0.step, binSuccMachineSep, Tape.move])
  -- Step 5: shift loop
  have h5 := binSuccSep_shift_loop sep rest hrest s (sep :: γ'ToChainΓ Γ'.bit1 :: revLeft)
  -- Step 6: shiftDn → rwdBlk, move left
  have h6 : Reaches (TM0.step (binSuccMachineSep sep))
    ⟨.shiftDn, ⟨(s :: rest).getLast (by simp),
      ListBlank.mk ((s :: rest).dropLast.reverse ++ sep :: γ'ToChainΓ Γ'.bit1 :: revLeft),
      ListBlank.mk []⟩⟩
    ⟨.rwdBlk, ⟨((s :: rest).dropLast.reverse ++ sep :: γ'ToChainΓ Γ'.bit1 :: revLeft).headI,
      ListBlank.mk ((s :: rest).dropLast.reverse ++ sep :: γ'ToChainΓ Γ'.bit1 :: revLeft).tail,
      ListBlank.mk [(s :: rest).getLast (by simp)]⟩⟩ :=
    .single (by cases (s :: rest).dropLast.reverse ++ sep :: γ'ToChainΓ Γ'.bit1 :: revLeft
                <;> simp +decide [TM0.step, binSuccMachineSep, Tape.move])
  -- Step 7: rwdBlk loop through all non-default cells
  have h7 := binSuccSep_rwdBlk_loop sep
    ((s :: rest).dropLast.reverse ++ sep :: γ'ToChainΓ Γ'.bit1 :: revLeft)
    (by intro g hg
        simp [List.mem_append, List.mem_reverse] at hg
        rcases hg with hg | rfl | rfl | hg
        · have hmem := List.mem_of_mem_dropLast hg
          cases hmem with
          | head => exact hs
          | tail _ h => exact hrest g h
        · exact hsep_nd
        · decide
        · exact hrevLeft g hg)
    [(s :: rest).getLast (by simp)]
  -- Combine everything
  have hfinal : ((s :: rest).dropLast.reverse ++ sep :: γ'ToChainΓ Γ'.bit1 :: revLeft).reverse ++
    [(s :: rest).getLast (by simp)] =
    revLeft.reverse ++ γ'ToChainΓ Γ'.bit1 :: sep :: s :: rest := by
      simp [List.reverse_append, List.reverse_reverse]
      rw [List.dropLast_append_getLast (show s :: rest ≠ [] from by simp)]
  rw [hfinal] at h7
  exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans (h7.trans
    (binSuccSep_rwdBlk_done sep _)))))))

/-- Main correctness lemma for `binSuccMachineSep`: the carry phase
    starting with left context `revLeft` reaches the correct final state.
    Requires `sep ≠ default`. -/
theorem binSucc_carry_aux_sep (sep : ChainΓ)
    (hsep0 : sep ≠ γ'ToChainΓ Γ'.bit0) (hsep1 : sep ≠ γ'ToChainΓ Γ'.bit1)
    (hsep_nd : sep ≠ default)
    (block suffix revLeft : List ChainΓ)
    (hblock : ∀ g ∈ block, g ≠ default)
    (hblock_nsep : ∀ g ∈ block, g ≠ sep)
    (hsuffix : ∀ g ∈ suffix, g ≠ default)
    (hfblock : ∀ g ∈ binSucc block, g ≠ default)
    (hrevLeft : ∀ g ∈ revLeft, g ≠ default) :
    Reaches (TM0.step (binSuccMachineSep sep))
      ⟨.carry, ⟨(block ++ sep :: suffix).headI,
               ListBlank.mk revLeft,
               ListBlank.mk (block ++ sep :: suffix).tail⟩⟩
      ⟨.done, Tape.mk₁ (revLeft.reverse ++ binSucc block ++ sep :: suffix)⟩ := by
  induction block generalizing suffix revLeft with
  | nil =>
    cases suffix with
    | nil =>
      convert binSuccSep_carry_ext_nil sep hsep0 hsep1 hsep_nd revLeft hrevLeft using 2 <;> simp [binSucc]
    | cons s rest =>
      convert binSuccSep_carry_ext_cons sep hsep0 hsep1 hsep_nd s rest revLeft
        (hsuffix s (.head _)) (fun g hg => hsuffix g (.tail _ hg)) hrevLeft using 2 <;> simp [binSucc]
  | cons c rest ih =>
    by_cases hc0 : c = γ'ToChainΓ Γ'.bit0
    · subst hc0
      convert binSuccSep_carry_bit0 sep hsep0 rest suffix revLeft hrevLeft using 2 <;>
        simp [binSucc, List.append_assoc]
    · by_cases hc1 : c = γ'ToChainΓ Γ'.bit1
      · subst hc1
        have hih := ih suffix (γ'ToChainΓ Γ'.bit0 :: revLeft)
          (fun g hg => hblock g (List.mem_cons_of_mem _ hg))
          (fun g hg => hblock_nsep g (List.mem_cons_of_mem _ hg))
          hsuffix
          (by intro g hg; simp [binSucc, show γ'ToChainΓ Γ'.bit1 ≠ γ'ToChainΓ Γ'.bit0 from by decide] at hfblock; exact hfblock.2 g hg)
          (by intro g hg; simp at hg; rcases hg with rfl | hg; decide; exact hrevLeft g hg)
        convert binSuccSep_carry_bit1 sep hsep1 rest suffix revLeft hih using 2 <;>
          simp [binSucc, List.append_assoc, List.reverse_cons,
                show γ'ToChainΓ Γ'.bit1 ≠ γ'ToChainΓ Γ'.bit0 from by decide]
      · have hc_nsep := hblock_nsep c (.head _)
        convert binSuccSep_carry_other sep c rest suffix revLeft hc0 hc1 hc_nsep hrevLeft using 2 <;>
          simp [binSucc, hc0, hc1, List.append_assoc]

/-- **Binary successor is block-realizable before any separator that differs
    from `bit0` and `bit1`.**
    For `sep = default`, this follows from `tm0_binSucc_block`.
    For `sep ≠ default`, uses `binSuccMachineSep sep`. -/
theorem tm0_binSucc_blockSep {sep : ChainΓ}
    (hsep0 : sep ≠ γ'ToChainΓ Γ'.bit0) (hsep1 : sep ≠ γ'ToChainΓ Γ'.bit1) :
    TM0RealizesBlockSep ChainΓ sep binSucc := by
  by_cases hsep_def : sep = default
  · subst hsep_def; exact tm0RealizesBlockSep_default_of_block tm0_binSucc_block
  · refine ⟨BinSuccSt, inferInstance, inferInstance, binSuccMachineSep sep,
      fun block suffix hblock hblock_nsep hsuffix hfblock _hfblock_nsep => ?_⟩
    have h_reaches := binSucc_carry_aux_sep sep hsep0 hsep1 hsep_def
      block suffix [] hblock hblock_nsep hsuffix hfblock (by simp)
    constructor
    · exact Part.dom_iff_mem.mpr ⟨_, Turing.mem_eval.mpr
        ⟨h_reaches, by simp [TM0.step, binSuccMachineSep]⟩⟩
    · intro h
      exact (Part.mem_unique (Part.get_mem h) (Turing.mem_eval.mpr
        ⟨h_reaches, by simp [TM0.step, binSuccMachineSep]⟩)).symm ▸ rfl

/-! ## LSB-last successor — opaque suffix version -/

/-- Binary successor for blocks whose least-significant bit is at the end of
the list. This is ordinary `binSucc` conjugated by list reversal. -/
noncomputable def binSuccLsbLast : List ChainΓ → List ChainΓ :=
  List.reverse ∘ binSucc ∘ List.reverse

theorem binSuccLsbLast_ne_default (block : List ChainΓ)
    (hblock : ∀ g ∈ block, g ≠ default) :
    ∀ g ∈ binSuccLsbLast block, g ≠ default := by
  intro g hg
  unfold binSuccLsbLast at hg
  simp only [Function.comp_apply] at hg
  exact reverse_ne_default _ (binSucc_ne_default _ (reverse_ne_default block hblock))
    g hg

theorem binSucc_no_of_ne_bits {sep : ChainΓ}
    (hsep0 : sep ≠ γ'ToChainΓ Γ'.bit0)
    (hsep1 : sep ≠ γ'ToChainΓ Γ'.bit1)
    (block : List ChainΓ) (hblock : ∀ g ∈ block, g ≠ sep) :
    ∀ g ∈ binSucc block, g ≠ sep := by
  induction block with
  | nil =>
      intro g hg
      simp [binSucc] at hg
      rw [hg]
      exact Ne.symm hsep1
  | cons c rest ih =>
      have hc : c ≠ sep := hblock c (by simp)
      have hrest : ∀ g ∈ rest, g ≠ sep := by
        intro g hg
        exact hblock g (List.mem_cons_of_mem c hg)
      intro g hg
      by_cases hc0 : c = γ'ToChainΓ Γ'.bit0
      · have hmem : g = γ'ToChainΓ Γ'.bit1 ∨ g ∈ rest := by
          simpa [binSucc, hc0] using hg
        rcases hmem with rfl | hg
        · exact Ne.symm hsep1
        · exact hrest g hg
      · by_cases hc1 : c = γ'ToChainΓ Γ'.bit1
        · have hmem : g = γ'ToChainΓ Γ'.bit0 ∨ g ∈ binSucc rest := by
            simpa +decide [binSucc, hc0, hc1] using hg
          rcases hmem with rfl | hg
          · exact Ne.symm hsep0
          · exact ih hrest g hg
        · have hmem : g = c ∨ g ∈ rest := by
            simpa [binSucc, hc0, hc1] using hg
          rcases hmem with rfl | hg
          · exact hc
          · exact hrest g hg

theorem binSuccLsbLast_ne_sep {sep : ChainΓ}
    (hsep0 : sep ≠ γ'ToChainΓ Γ'.bit0)
    (hsep1 : sep ≠ γ'ToChainΓ Γ'.bit1)
    (block : List ChainΓ) (hblock : ∀ g ∈ block, g ≠ sep) :
    ∀ g ∈ binSuccLsbLast block, g ≠ sep := by
  intro g hg
  unfold binSuccLsbLast at hg
  simp only [Function.comp_apply] at hg
  have hsucc :
      ∀ g ∈ binSucc block.reverse, g ≠ sep := by
    exact binSucc_no_of_ne_bits hsep0 hsep1 block.reverse
      (reverse_ne_sep block hblock)
  exact reverse_ne_sep _ hsucc g hg

inductive BinSuccLsbLastSt where
  | scan | carry | carryMove | rewind | done

noncomputable instance : DecidableEq BinSuccLsbLastSt :=
  Classical.typeDecidableEq _

noncomputable instance : Inhabited BinSuccLsbLastSt := ⟨.scan⟩

noncomputable instance : Fintype BinSuccLsbLastSt := by
  exact
  { elems := {.scan, .carry, .carryMove, .rewind, .done}
    complete := by intro x; cases x <;> simp }

/-- Increment a separator-bounded block whose least-significant bit is the
rightmost cell. The machine never moves right of the separator, so the suffix
after `sep` is completely opaque. -/
noncomputable def binSuccLsbLastMachine (sep : ChainΓ) :
    @TM0.Machine ChainΓ BinSuccLsbLastSt ⟨.scan⟩ := fun q a =>
  match q with
  | .scan =>
      if a = sep then some (.carry, .move Dir.left)
      else some (.scan, .move Dir.right)
  | .carry =>
      if a = γ'ToChainΓ Γ'.bit0 then
        some (.rewind, .write (γ'ToChainΓ Γ'.bit1))
      else if a = γ'ToChainΓ Γ'.bit1 then
        some (.carryMove, .write (γ'ToChainΓ Γ'.bit0))
      else if a = default then
        some (.done, .write (γ'ToChainΓ Γ'.bit1))
      else
        some (.rewind, .move Dir.left)
  | .carryMove => some (.carry, .move Dir.left)
  | .rewind =>
      if a = default then some (.done, .move Dir.right)
      else some (.rewind, .move Dir.left)
  | .done => none

theorem binSuccLsbLast_step_done (sep : ChainΓ) (T : Tape ChainΓ) :
    TM0.step (binSuccLsbLastMachine sep) ⟨.done, T⟩ = none := by
  simp [TM0.step, binSuccLsbLastMachine]

private theorem listBlank_mk_headI_tail_chainΓ (R : List ChainΓ) :
    ListBlank.mk (R.headI :: R.tail) = ListBlank.mk R := by
  apply ListBlank.ext
  intro i
  simp only [ListBlank.nth_mk]
  cases R with
  | nil => cases i <;> simp [List.getI, List.getD, List.headI]
  | cons _ _ => rfl

theorem binSuccLsbLast_scan_reaches_aux
    (sep : ChainΓ) (block suffix revLeft : List ChainΓ)
    (hblock_nsep : ∀ g ∈ block, g ≠ sep) :
    Reaches (TM0.step (binSuccLsbLastMachine sep))
      ⟨.scan, Tape.mk₂ revLeft (block ++ sep :: suffix)⟩
      ⟨.carry,
        Tape.move Dir.left (Tape.mk₂ (block.reverse ++ revLeft) (sep :: suffix))⟩ := by
  induction block generalizing revLeft with
  | nil =>
      exact Relation.ReflTransGen.single (by
        simp [TM0.step, binSuccLsbLastMachine, RevBlock.mk₂_head])
  | cons c rest ih =>
      have hc_nsep : c ≠ sep := hblock_nsep c (by simp)
      have hrest_nsep : ∀ g ∈ rest, g ≠ sep := by
        intro g hg
        exact hblock_nsep g (List.mem_cons_of_mem c hg)
      have hstep : Reaches (TM0.step (binSuccLsbLastMachine sep))
          ⟨.scan, Tape.mk₂ revLeft (c :: rest ++ sep :: suffix)⟩
          ⟨.scan, Tape.mk₂ (c :: revLeft) (rest ++ sep :: suffix)⟩ := by
        exact Relation.ReflTransGen.single (by
          simp [TM0.step, binSuccLsbLastMachine, hc_nsep,
            RevBlock.mk₂_head, RevBlock.mk₂_move_right])
      convert hstep.trans (ih (c :: revLeft) hrest_nsep) using 1
      simp [List.append_assoc]

theorem binSuccLsbLast_scan_reaches
    (sep : ChainΓ) (block suffix : List ChainΓ)
    (hblock_nsep : ∀ g ∈ block, g ≠ sep) :
    Reaches (TM0.step (binSuccLsbLastMachine sep))
      (TM0.init (block ++ sep :: suffix))
      ⟨.carry, Tape.move Dir.left (Tape.mk₂ block.reverse (sep :: suffix))⟩ := by
  convert binSuccLsbLast_scan_reaches_aux sep block suffix [] hblock_nsep using 1
  simp [Tape.mk₁, RevBlock.mk₂_nil_eq_mk₁]

theorem binSuccLsbLast_rewind_reaches
    (sep : ChainΓ) (left : List ChainΓ) (head : ChainΓ) (right : List ChainΓ)
    (hleft_nd : ∀ g ∈ left, g ≠ default)
    (hhead_nd : head ≠ default) :
    Reaches (TM0.step (binSuccLsbLastMachine sep))
      ⟨.rewind, Tape.mk₂ left (head :: right)⟩
      ⟨.done, Tape.mk₁ (left.reverse ++ head :: right)⟩ := by
  induction left generalizing head right with
  | nil =>
      have h1 : Reaches (TM0.step (binSuccLsbLastMachine sep))
          ⟨.rewind, Tape.mk₂ [] (head :: right)⟩
          ⟨.rewind, Tape.move Dir.left (Tape.mk₂ [] (head :: right))⟩ :=
        Relation.ReflTransGen.single (by
          simp [TM0.step, binSuccLsbLastMachine, hhead_nd, RevBlock.mk₂_head])
      have h2 : Reaches (TM0.step (binSuccLsbLastMachine sep))
          ⟨.rewind, Tape.move Dir.left (Tape.mk₂ [] (head :: right))⟩
          ⟨.done, Tape.mk₁ (head :: right)⟩ :=
        Relation.ReflTransGen.single (by
          simp [TM0.step, binSuccLsbLastMachine, Tape.move, Tape.mk₁,
            Tape.mk₂, Tape.mk']
          exact listBlank_mk_append_default [])
      simpa using h1.trans h2
  | cons c rest ih =>
      have hc_nd : c ≠ default := hleft_nd c (by simp)
      have hrest_nd : ∀ g ∈ rest, g ≠ default := by
        intro g hg
        exact hleft_nd g (List.mem_cons_of_mem c hg)
      have hstep : Reaches (TM0.step (binSuccLsbLastMachine sep))
          ⟨.rewind, Tape.mk₂ (c :: rest) (head :: right)⟩
          ⟨.rewind, Tape.mk₂ rest (c :: head :: right)⟩ :=
        Relation.ReflTransGen.single (by
          simp [TM0.step, binSuccLsbLastMachine, hhead_nd, RevBlock.mk₂_head,
            RevBlock.mk₂_move_left])
      convert hstep.trans (ih c (head :: right) hrest_nd hc_nd) using 1
      simp [List.append_assoc]

theorem binSuccLsbLast_rewind_after_left_reaches
    (sep : ChainΓ) (left tail : List ChainΓ)
    (hleft_nd : ∀ g ∈ left, g ≠ default) :
    Reaches (TM0.step (binSuccLsbLastMachine sep))
      ⟨.rewind, Tape.move Dir.left (Tape.mk₂ left tail)⟩
      ⟨.done, Tape.mk₁ (left.reverse ++ tail)⟩ := by
  cases left with
  | nil =>
      exact Relation.ReflTransGen.single (by
        simp [TM0.step, binSuccLsbLastMachine, Tape.move, Tape.mk₁,
          Tape.mk₂, Tape.mk']
        exact listBlank_mk_append_default [])
  | cons c rest =>
      have hc_nd : c ≠ default := hleft_nd c (by simp)
      have hrest_nd : ∀ g ∈ rest, g ≠ default := by
        intro g hg
        exact hleft_nd g (List.mem_cons_of_mem c hg)
      simpa [RevBlock.mk₂_move_left, List.reverse_cons, List.append_assoc] using
        binSuccLsbLast_rewind_reaches sep rest c tail hrest_nd hc_nd

theorem binSuccLsbLast_carry_reaches_tail
    (sep : ChainΓ) (revBlock tail : List ChainΓ)
    (hrev_nd : ∀ g ∈ revBlock, g ≠ default) :
    Reaches (TM0.step (binSuccLsbLastMachine sep))
      ⟨.carry, Tape.move Dir.left (Tape.mk₂ revBlock tail)⟩
      ⟨.done, Tape.mk₁ ((binSucc revBlock).reverse ++ tail)⟩ := by
  induction revBlock generalizing tail with
  | nil =>
      exact Relation.ReflTransGen.single (by
        simp +decide [TM0.step, binSuccLsbLastMachine, binSucc, Tape.move,
          Tape.write, Tape.mk₁, Tape.mk₂, Tape.mk']
        exact listBlank_mk_headI_tail_chainΓ tail)
  | cons c rest ih =>
      have hc_nd : c ≠ default := hrev_nd c (by simp)
      have hrest_nd : ∀ g ∈ rest, g ≠ default := by
        intro g hg
        exact hrev_nd g (List.mem_cons_of_mem c hg)
      by_cases hc0 : c = γ'ToChainΓ Γ'.bit0
      · subst hc0
        have hstep : Reaches (TM0.step (binSuccLsbLastMachine sep))
            ⟨.carry,
              Tape.move Dir.left (Tape.mk₂ (γ'ToChainΓ Γ'.bit0 :: rest) tail)⟩
            ⟨.rewind, Tape.mk₂ rest (γ'ToChainΓ Γ'.bit1 :: tail)⟩ :=
          Relation.ReflTransGen.single (by
            simp [TM0.step, binSuccLsbLastMachine, RevBlock.mk₂_move_left,
              RevBlock.mk₂_write, RevBlock.mk₂_head])
        convert hstep.trans (binSuccLsbLast_rewind_reaches sep rest
            (γ'ToChainΓ Γ'.bit1) tail hrest_nd (by decide)) using 1
        simp [binSucc, List.append_assoc]
      · by_cases hc1 : c = γ'ToChainΓ Γ'.bit1
        · subst hc1
          have hwrite : Reaches (TM0.step (binSuccLsbLastMachine sep))
              ⟨.carry,
                Tape.move Dir.left (Tape.mk₂ (γ'ToChainΓ Γ'.bit1 :: rest) tail)⟩
              ⟨.carryMove, Tape.mk₂ rest (γ'ToChainΓ Γ'.bit0 :: tail)⟩ :=
            Relation.ReflTransGen.single (by
              simp [TM0.step, binSuccLsbLastMachine, hc0, RevBlock.mk₂_move_left,
                RevBlock.mk₂_write, RevBlock.mk₂_head])
          have hmove : Reaches (TM0.step (binSuccLsbLastMachine sep))
              ⟨.carryMove, Tape.mk₂ rest (γ'ToChainΓ Γ'.bit0 :: tail)⟩
              ⟨.carry, Tape.move Dir.left
                (Tape.mk₂ rest (γ'ToChainΓ Γ'.bit0 :: tail))⟩ :=
            Relation.ReflTransGen.single (by
              simp [TM0.step, binSuccLsbLastMachine])
          convert hwrite.trans (hmove.trans (ih (γ'ToChainΓ Γ'.bit0 :: tail) hrest_nd)) using 1
          simp [binSucc, hc0, List.append_assoc]
        · have hstep : Reaches (TM0.step (binSuccLsbLastMachine sep))
              ⟨.carry, Tape.move Dir.left (Tape.mk₂ (c :: rest) tail)⟩
              ⟨.rewind, Tape.move Dir.left (Tape.mk₂ rest (c :: tail))⟩ :=
            Relation.ReflTransGen.single (by
              simp [TM0.step, binSuccLsbLastMachine, hc0, hc1, hc_nd,
                RevBlock.mk₂_move_left, RevBlock.mk₂_head])
          convert hstep.trans
            (binSuccLsbLast_rewind_after_left_reaches sep rest (c :: tail) hrest_nd)
            using 1
          simp [binSucc, hc0, hc1, List.append_assoc]

theorem binSuccLsbLast_carry_reaches
    (sep : ChainΓ) (revBlock suffix : List ChainΓ)
    (hrev_nd : ∀ g ∈ revBlock, g ≠ default) :
    Reaches (TM0.step (binSuccLsbLastMachine sep))
      ⟨.carry, Tape.move Dir.left (Tape.mk₂ revBlock (sep :: suffix))⟩
      ⟨.done, Tape.mk₁ ((binSucc revBlock).reverse ++ sep :: suffix)⟩ := by
  simpa using binSuccLsbLast_carry_reaches_tail sep revBlock (sep :: suffix) hrev_nd

theorem tm0_binSuccLsbLast_blockSepAnySuffix {sep : ChainΓ}
    (hsep0 : sep ≠ γ'ToChainΓ Γ'.bit0)
    (hsep1 : sep ≠ γ'ToChainΓ Γ'.bit1) :
    TM0RealizesBlockSepAnySuffix ChainΓ sep binSuccLsbLast := by
  refine ⟨BinSuccLsbLastSt, inferInstance, inferInstance,
    binSuccLsbLastMachine sep, ?_⟩
  intro block suffix hblock_nd hblock_nsep hfblock_nd hfblock_nsep
  have hscan := binSuccLsbLast_scan_reaches sep block suffix hblock_nsep
  have hcarry := binSuccLsbLast_carry_reaches sep block.reverse suffix
    (reverse_ne_default block hblock_nd)
  have h_reaches : Reaches (TM0.step (binSuccLsbLastMachine sep))
      (TM0.init (block ++ sep :: suffix))
      ⟨.done, Tape.mk₁ (binSuccLsbLast block ++ sep :: suffix)⟩ := by
    simpa [binSuccLsbLast, Function.comp_def] using hscan.trans hcarry
  constructor
  · exact Part.dom_iff_mem.mpr ⟨_, Turing.mem_eval.mpr
      ⟨h_reaches, binSuccLsbLast_step_done sep _⟩⟩
  · intro h
    exact (Part.mem_unique (Part.get_mem h) (Turing.mem_eval.mpr
      ⟨h_reaches, binSuccLsbLast_step_done sep _⟩)).symm ▸ rfl

theorem tm0_binSucc_blockSepAnySuffix {sep : ChainΓ}
    (hsep0 : sep ≠ γ'ToChainΓ Γ'.bit0)
    (hsep1 : sep ≠ γ'ToChainΓ Γ'.bit1) :
    TM0RealizesBlockSepAnySuffix ChainΓ sep binSucc := by
  have hlsb := tm0_binSuccLsbLast_blockSepAnySuffix
    (sep := sep) hsep0 hsep1
  have hrev := tm0RealizesBlockSepAnySuffix_revFRev hlsb
    (fun block hblock => binSuccLsbLast_ne_default block hblock)
    (fun block hblock => binSuccLsbLast_ne_sep hsep0 hsep1 block hblock)
  obtain ⟨Λ, hΛi, hΛf, M, hM⟩ := hrev
  refine ⟨Λ, hΛi, hΛf, M, ?_⟩
  intro block suffix hblock_nd hblock_nsep hf_nd hf_nsep
  have hf_nd' :
      ∀ g ∈ (List.reverse ∘ binSuccLsbLast ∘ List.reverse) block,
        g ≠ default := by
    simpa [binSuccLsbLast, Function.comp_def] using hf_nd
  have hf_nsep' :
      ∀ g ∈ (List.reverse ∘ binSuccLsbLast ∘ List.reverse) block,
        g ≠ sep := by
    simpa [binSuccLsbLast, Function.comp_def] using hf_nsep
  obtain ⟨hdom, htape⟩ :=
    hM block suffix hblock_nd hblock_nsep hf_nd' hf_nsep'
  refine ⟨hdom, ?_⟩
  intro h
  simpa [binSuccLsbLast, Function.comp_def] using htape h

/-- Constant addition is separator-realizable with an unrestricted suffix. -/
theorem tm0_binAddConst_blockSepAnySuffix {sep : ChainΓ}
    (hsep0 : sep ≠ γ'ToChainΓ Γ'.bit0)
    (hsep1 : sep ≠ γ'ToChainΓ Γ'.bit1) (c : ℕ) :
    TM0RealizesBlockSepAnySuffix ChainΓ sep (binAddConst c) := by
  unfold binAddConst
  exact tm0RealizesBlockSepAnySuffix_iterate
    (tm0_binSucc_blockSepAnySuffix hsep0 hsep1)
    binSucc_ne_default
    (fun block hblock => binSucc_no_of_ne_bits hsep0 hsep1 block hblock)
    c

/-- Decode/re-encode constant addition is separator-realizable with an
unrestricted suffix. -/
theorem tm0_binAddConstRepr_blockSepAnySuffix {sep : ChainΓ}
    (hsep0 : sep ≠ γ'ToChainΓ Γ'.bit0)
    (hsep1 : sep ≠ γ'ToChainΓ Γ'.bit1) (c : ℕ) :
    TM0RealizesBlockSepAnySuffix ChainΓ sep (binAddConstRepr c) := by
  rw [binAddConstRepr_eq_comp]
  exact tm0RealizesBlockSepAnySuffix_comp
    (tm0_normalizeBlockSep_anySuffix hsep0 hsep1)
    (tm0_binAddConst_blockSepAnySuffix hsep0 hsep1 c)
    (fun _block _hblock => normalizeBlock_ne_default _)
    (fun block _hblock =>
      normalizeBlock_no_of_ne_bits sep hsep0 hsep1 block)
