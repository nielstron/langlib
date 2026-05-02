import Mathlib
import Langlib.Automata.Turing.DSL.ChainAlphabet
import Langlib.Automata.Turing.DSL.BlockRealizability
import Langlib.Automata.Turing.DSL.BinaryArithmetic
import Langlib.Automata.Turing.DSL.BinarySuccessor

/-! # Binary Predecessor — TM0 Machine for Decrementing Binary Blocks -/

open Turing PartrecToTM2 TM2to1

/-! ### Binary Predecessor Function -/

/-- Raw binary decrement without normalization. -/
noncomputable def binPredRaw : List ChainΓ → List ChainΓ
  | [] => []
  | c :: rest =>
    if c = γ'ToChainΓ Γ'.bit1 then
      γ'ToChainΓ Γ'.bit0 :: rest
    else if c = γ'ToChainΓ Γ'.bit0 then
      γ'ToChainΓ Γ'.bit1 :: binPredRaw rest
    else
      c :: rest

/-- Normalized binary decrement. -/
noncomputable def binPred (block : List ChainΓ) : List ChainΓ :=
  chainBinaryRepr (decodeBinaryBlock block - 1)

theorem binPredRaw_ne_default (block : List ChainΓ)
    (hblock : ∀ g ∈ block, g ≠ default) :
    ∀ g ∈ binPredRaw block, g ≠ default := by
  induction block with
  | nil => simp [binPredRaw]
  | cons c rest ih =>
    unfold binPredRaw; split_ifs <;> simp_all +decide [γ'ToChainΓ]

theorem binPred_ne_default (block : List ChainΓ)
    (_hblock : ∀ g ∈ block, g ≠ default) :
    ∀ g ∈ binPred block, g ≠ default := by
  unfold binPred; exact chainBinaryRepr_ne_default _

theorem binPred_correct (n : ℕ) :
    binPred (chainBinaryRepr n) = chainBinaryRepr (n - 1) := by
  unfold binPred; rw [decodeBinaryBlock_chainBinaryRepr]

/-! ### TM0 Machine States -/

inductive BinPredSt where
  | borrow | borrowMv | absorbed | rewind | done
  deriving DecidableEq

noncomputable instance : Inhabited BinPredSt := ⟨.borrow⟩

instance : Fintype BinPredSt where
  elems := {.borrow, .borrowMv, .absorbed, .rewind, .done}
  complete := by intro x; cases x <;> simp

/-! ### TM0 Machine Definition -/

noncomputable def binPredRawMachine : @TM0.Machine ChainΓ BinPredSt ⟨.borrow⟩ :=
  fun q a =>
    match q with
    | .borrow =>
      if a = γ'ToChainΓ Γ'.bit1 then
        some (.absorbed, .write (γ'ToChainΓ Γ'.bit0))
      else if a = γ'ToChainΓ Γ'.bit0 then
        some (.borrowMv, .write (γ'ToChainΓ Γ'.bit1))
      else
        some (.absorbed, .write a)  -- no-op: write same value, route to done via rewind
    | .borrowMv => some (.borrow, .move Dir.right)
    | .absorbed => some (.rewind, .move Dir.left)
    | .rewind =>
      if a = default then some (.done, .move Dir.right)
      else some (.rewind, .move Dir.left)
    | .done => none

/-! ### Rewind Phase -/

/-
Rewind loop: moves left through non-default cells, accumulating them on the right.
-/
theorem binPredRaw_rewind_collect (revLeft : List ChainΓ)
    (hrevLeft : ∀ g ∈ revLeft, g ≠ default)
    (acc : List ChainΓ) :
    Reaches (TM0.step binPredRawMachine)
      ⟨.rewind, ⟨revLeft.headI, ListBlank.mk revLeft.tail, ListBlank.mk acc⟩⟩
      ⟨.rewind, ⟨default, ListBlank.mk [], ListBlank.mk (revLeft.reverse ++ acc)⟩⟩ := by
  induction' revLeft with a revLeft ih generalizing acc;
  · constructor;
  · have h_step : TM0.step binPredRawMachine ⟨BinPredSt.rewind, ⟨a, ListBlank.mk revLeft, ListBlank.mk acc⟩⟩ = some ⟨BinPredSt.rewind, ⟨revLeft.headI, ListBlank.mk revLeft.tail, ListBlank.mk (a :: acc)⟩⟩ := by
      unfold TM0.step;
      unfold binPredRawMachine; aesop;
    exact Relation.ReflTransGen.head h_step ( by simpa using ih ( fun g hg => hrevLeft g ( List.mem_cons_of_mem _ hg ) ) ( a :: acc ) )

/-
Final rewind step: at default, transition to done.
-/
theorem binPredRaw_rewind_final (rightList : List ChainΓ) :
    Reaches (TM0.step binPredRawMachine)
      ⟨.rewind, ⟨default, ListBlank.mk [], ListBlank.mk rightList⟩⟩
      ⟨.done, Tape.mk₁ rightList⟩ := by
  -- Apply the definition of the machine's step function for the rewind state.
  have h_step : TM0.step binPredRawMachine ⟨BinPredSt.rewind, ⟨default, ListBlank.mk [], ListBlank.mk rightList⟩⟩ = some ⟨BinPredSt.done, Tape.mk₁ rightList⟩ := by
    unfold TM0.step binPredRawMachine;
    cases rightList <;> simp +decide [ Tape.mk₁ ];
    · unfold Tape.move; simp +decide [ Tape.mk₂ ] ;
      -- By definition of `Tape.mk'`, we have `Tape.mk' (ListBlank.mk []) (ListBlank.mk []) = ⟨default, ListBlank.mk [], ListBlank.mk []⟩`.
      simp [Tape.mk'];
      nontriviality;
      -- By definition of `ListBlank.mk`, we have `ListBlank.mk [default] = ListBlank.mk []`.
      apply ListBlank.ext;
      intro i; cases i <;> simp +decide [ ListBlank.nth ] ;
      simp +decide [ ListBlank.mk ];
    · -- By definition of `Tape.move`, moving right from the default position results in the same tape as the original.
      simp [Tape.move, Tape.mk₂];
      simp +decide [ Tape.mk' ];
      unfold ListBlank.mk; simp +decide [ ListBlank.ext_iff ] ;
      intro i; induction i <;> simp +decide [ ListBlank.nth ] ;
  exact Relation.ReflTransGen.single h_step

/-- The rewind phase correctly returns to the block start. -/
theorem binPredRaw_rewind_loop (revLeft : List ChainΓ)
    (hrevLeft : ∀ g ∈ revLeft, g ≠ default)
    (rightList : List ChainΓ) :
    Reaches (TM0.step binPredRawMachine)
      ⟨.rewind, ⟨revLeft.headI, ListBlank.mk revLeft.tail, ListBlank.mk rightList⟩⟩
      ⟨.done, Tape.mk₁ (revLeft.reverse ++ rightList)⟩ :=
  (binPredRaw_rewind_collect revLeft hrevLeft rightList).trans
    (binPredRaw_rewind_final _)

/-! ### Borrow Phase — Step Lemmas -/

/-
Reading bit1: write bit0, borrow absorbed.
-/
theorem binPredRaw_borrow_bit1 (rest suffix revLeft : List ChainΓ)
    (hrevLeft : ∀ g ∈ revLeft, g ≠ default) :
    Reaches (TM0.step binPredRawMachine)
      ⟨.borrow, ⟨γ'ToChainΓ Γ'.bit1, ListBlank.mk revLeft, ListBlank.mk (rest ++ default :: suffix)⟩⟩
      ⟨.done, Tape.mk₁ (revLeft.reverse ++ γ'ToChainΓ Γ'.bit0 :: rest ++ default :: suffix)⟩ := by
  have h_step1 : Reaches (TM0.step binPredRawMachine)
    ⟨.borrow, ⟨γ'ToChainΓ Γ'.bit1, ListBlank.mk revLeft, ListBlank.mk (rest ++ default :: suffix)⟩⟩
    ⟨.absorbed, ⟨γ'ToChainΓ Γ'.bit0, ListBlank.mk revLeft, ListBlank.mk (rest ++ default :: suffix)⟩⟩ := by
      exact Relation.ReflTransGen.single ( by unfold binPredRawMachine; aesop )
  generalize_proofs at *; (
  refine' h_step1.trans _;
  have h_step2 : Reaches (TM0.step binPredRawMachine)
    ⟨.absorbed, ⟨γ'ToChainΓ Γ'.bit0, ListBlank.mk revLeft, ListBlank.mk (rest ++ default :: suffix)⟩⟩
    ⟨.rewind, ⟨revLeft.headI, ListBlank.mk revLeft.tail, ListBlank.mk (γ'ToChainΓ Γ'.bit0 :: rest ++ default :: suffix)⟩⟩ := by
      constructor;
      constructor;
      cases revLeft <;> aesop
  generalize_proofs at *; (
  exact h_step2.trans ( binPredRaw_rewind_loop revLeft hrevLeft _ ) |> fun h => h |> fun h => by simpa [ Tape.mk₁ ] using h;))

/-
Reading bit0: write bit1, propagate borrow.
-/
theorem binPredRaw_borrow_bit0_step (rest suffix revLeft : List ChainΓ) :
    Reaches (TM0.step binPredRawMachine)
      ⟨.borrow, ⟨γ'ToChainΓ Γ'.bit0, ListBlank.mk revLeft, ListBlank.mk (rest ++ default :: suffix)⟩⟩
      ⟨.borrow, ⟨(rest ++ default :: suffix).headI,
                 ListBlank.mk (γ'ToChainΓ Γ'.bit1 :: revLeft),
                 ListBlank.mk (rest ++ default :: suffix).tail⟩⟩ := by
  convert Relation.ReflTransGen.head _ _ using 1;
  exact ⟨ BinPredSt.borrowMv, ⟨ γ'ToChainΓ Γ'.bit1, ListBlank.mk revLeft, ListBlank.mk ( rest ++ default :: suffix ) ⟩ ⟩;
  · simp +decide [ TM0.step, binPredRawMachine ];
  · convert Relation.ReflTransGen.single _;
    cases rest <;> aesop

/-! ### Main Borrow Phase -/

/-
The borrow phase correctly computes `binPredRaw` with accumulated reversed prefix.
-/
theorem binPredRaw_borrow_aux (block suffix revLeft : List ChainΓ)
    (hblock : ∀ g ∈ block, g ≠ default)
    (hsuffix : ∀ g ∈ suffix, g ≠ default)
    (hrevLeft : ∀ g ∈ revLeft, g ≠ default) :
    Reaches (TM0.step binPredRawMachine)
      ⟨.borrow, ⟨(block ++ default :: suffix).headI,
                 ListBlank.mk revLeft,
                 ListBlank.mk (block ++ default :: suffix).tail⟩⟩
      ⟨.done, Tape.mk₁ (revLeft.reverse ++ binPredRaw block ++ default :: suffix)⟩ := by
  induction' block with c rest ih generalizing suffix revLeft;
  · -- In the base case, when the block is empty, the binPredRaw function returns the empty list.
    have h_base : binPredRaw [] = [] := by
      rfl;
    simp +decide [ h_base, TM0.step ];
    have h_borrow_default : Reaches (TM0.step binPredRawMachine) ⟨BinPredSt.borrow, ⟨default, ListBlank.mk revLeft, ListBlank.mk suffix⟩⟩ ⟨BinPredSt.absorbed, ⟨default, ListBlank.mk revLeft, ListBlank.mk suffix⟩⟩ := by
      exact Relation.ReflTransGen.single ( by unfold binPredRawMachine; aesop );
    have h_absorbed_rewind : Reaches (TM0.step binPredRawMachine) ⟨BinPredSt.absorbed, ⟨default, ListBlank.mk revLeft, ListBlank.mk suffix⟩⟩ ⟨BinPredSt.rewind, ⟨revLeft.headI, ListBlank.mk revLeft.tail, ListBlank.mk (default :: suffix)⟩⟩ := by
      exact .single ( by rfl );
    convert h_borrow_default.trans h_absorbed_rewind |> fun h => h.trans _ using 1;
    convert binPredRaw_rewind_loop revLeft hrevLeft ( default :: suffix ) using 1;
  · by_cases hc : c = γ'ToChainΓ Γ'.bit1;
    · rw [ hc ];
      convert binPredRaw_borrow_bit1 rest suffix revLeft hrevLeft using 1;
    · by_cases hc : c = γ'ToChainΓ Γ'.bit0;
      · convert binPredRaw_borrow_bit0_step rest suffix revLeft |> fun h => h.trans ( ih suffix ( γ'ToChainΓ Γ'.bit1 :: revLeft ) ?_ ?_ ?_ ) using 1 <;> simp_all +decide [ binPredRaw ];
      · have h_absorbed : Reaches (TM0.step binPredRawMachine) ⟨BinPredSt.borrow, ⟨c, ListBlank.mk revLeft, ListBlank.mk (rest ++ default :: suffix)⟩⟩ ⟨BinPredSt.absorbed, ⟨c, ListBlank.mk revLeft, ListBlank.mk (rest ++ default :: suffix)⟩⟩ := by
          constructor;
          constructor;
          simp +decide [ TM0.step, binPredRawMachine ];
          split_ifs ; tauto;
        have h_rewind : Reaches (TM0.step binPredRawMachine) ⟨BinPredSt.absorbed, ⟨c, ListBlank.mk revLeft, ListBlank.mk (rest ++ default :: suffix)⟩⟩ ⟨BinPredSt.rewind, ⟨revLeft.headI, ListBlank.mk revLeft.tail, ListBlank.mk (c :: rest ++ default :: suffix)⟩⟩ := by
          constructor;
          constructor;
          cases revLeft <;> aesop;
        convert h_absorbed.trans h_rewind |> fun h => h.trans ( binPredRaw_rewind_loop _ _ _ ) using 1;
        · simp +decide [ binPredRaw ];
          grind;
        · assumption

theorem binPredRaw_preserves_prefix_reaches (pfx block suffix : List ChainΓ)
    (hpfx : ∀ g ∈ pfx, g ≠ default)
    (hblock : ∀ g ∈ block, g ≠ default)
    (hsuffix : ∀ g ∈ suffix, g ≠ default) :
    Reaches (TM0.step binPredRawMachine)
      ⟨.borrow, ⟨(block ++ default :: suffix).headI,
                 ListBlank.mk pfx.reverse,
                 ListBlank.mk (block ++ default :: suffix).tail⟩⟩
      ⟨.done, Tape.mk₁ (pfx ++ binPredRaw block ++ default :: suffix)⟩ := by
  convert binPredRaw_borrow_aux block suffix pfx.reverse hblock hsuffix
    (fun g hg => hpfx g (List.mem_reverse.mp hg)) using 1
  rw [List.reverse_reverse]

/-! ### Main Block-Realizability Result -/

/-- `binPredRaw` is block-realizable. -/
theorem tm0_binPredRaw_block : TM0RealizesBlock ChainΓ binPredRaw := by
  use BinPredSt, inferInstance, inferInstance, binPredRawMachine
  intro block suffix hblock hsuffix hfblock
  have h_reaches : Reaches (TM0.step binPredRawMachine)
      (TM0.init (block ++ default :: suffix))
      ⟨.done, Tape.mk₁ (binPredRaw block ++ default :: suffix)⟩ := by
    convert binPredRaw_borrow_aux block suffix [] hblock hsuffix (by simp) using 1
  constructor
  · exact Part.dom_iff_mem.mpr ⟨_, Turing.mem_eval.mpr ⟨h_reaches, by simp [TM0.step, binPredRawMachine]⟩⟩
  · intro h
    have h_mem := Turing.mem_eval.mpr ⟨h_reaches, by simp [TM0.step, binPredRawMachine]⟩
    exact (Part.mem_unique (Part.get_mem h) h_mem).symm ▸ rfl

/-
Key lemma: binPredRaw correctly decrements on normalized blocks.
-/
theorem decodeBinaryBlock_binPredRaw (n : ℕ) :
    decodeBinaryBlock (binPredRaw (chainBinaryRepr n)) = n - 1 := by
  by_cases hn : n = 0;
  · aesop;
  · induction' n using Nat.strongRecOn with n ih;
    rcases Nat.even_or_odd' n with ⟨ k, rfl | rfl ⟩ <;> simp_all +decide [ Nat.mul_succ ];
    · rw [ show chainBinaryRepr ( 2 * k ) = γ'ToChainΓ Γ'.bit0 :: chainBinaryRepr k from chainBinaryRepr_double k hn ];
      rw [ show binPredRaw ( γ'ToChainΓ Γ'.bit0 :: chainBinaryRepr k ) = γ'ToChainΓ Γ'.bit1 :: binPredRaw ( chainBinaryRepr k ) from ?_ ];
      · rw [ show decodeBinaryBlock ( γ'ToChainΓ Γ'.bit1 :: binPredRaw ( chainBinaryRepr k ) ) = 2 * decodeBinaryBlock ( binPredRaw ( chainBinaryRepr k ) ) + 1 from ?_ ];
        · rw [ ih k ( by linarith [ Nat.pos_of_ne_zero hn ] ) hn ] ; omega;
        · exact if_neg ( by simp +decide [ γ'ToChainΓ ] ) |> fun h => h.trans ( if_pos rfl );
      · exact if_neg ( by simp +decide [ γ'ToChainΓ ] ) |> fun h => h.trans ( if_pos rfl );
    · rw [ chainBinaryRepr_double_succ ];
      exact congr_arg _ ( decodeBinaryBlock_chainBinaryRepr k )

/-- binPred = normalizeBlock ∘ binPredRaw ∘ normalizeBlock -/
theorem binPred_eq_comp :
    binPred = normalizeBlock ∘ binPredRaw ∘ normalizeBlock := by
  funext block
  simp [Function.comp, binPred, normalizeBlock, decodeBinaryBlock_binPredRaw]

/-- `binPred` is block-realizable. Decomposed as `normalizeBlock ∘ binPredRaw ∘ normalizeBlock`. -/
theorem tm0_binPred_block : TM0RealizesBlock ChainΓ binPred := by
  rw [binPred_eq_comp]
  exact tm0RealizesBlock_comp
    (tm0RealizesBlock_comp tm0_normalizeBlock tm0_binPredRaw_block
      (fun _ _ => normalizeBlock_ne_default _))
    tm0_normalizeBlock
    (fun block hblock => binPredRaw_ne_default _ (normalizeBlock_ne_default _))
