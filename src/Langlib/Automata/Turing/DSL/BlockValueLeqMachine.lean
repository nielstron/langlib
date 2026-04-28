import Mathlib
import Langlib.Automata.Turing.DSL.ChainAlphabet
import Langlib.Automata.Turing.DSL.TM0Compose

/-! # TM0 Machine for Block Value Comparison

This file constructs a TM0 machine that decides whether the binary value
of a ChainΓ block is ≤ k, preserving the tape and halting in distinct
states for the true/false outcomes.

## Architecture

The machine uses states `Fin (k+3) ⊕ Bool ⊕ Bool`:
- `Sum.inl ⟨b, _⟩` with b ≤ k: scanning right, budget remaining is b
- `Sum.inl ⟨k+1, _⟩`: scanning right, budget exceeded (answer will be false)
- `Sum.inl ⟨k+2, _⟩`: scanning right, decided true (non-bit symbol seen)
- `Sum.inr (Sum.inl b)`: rewinding left, b = answer
- `Sum.inr (Sum.inr b)`: halted, b = answer (true = q_true, false = q_false)

The machine only uses `Stmt.move`, never writes, so the tape is preserved.

## Scanning Budget

The budget tracks: `decodeBinaryBlock block ≤ k` iff scanning with initial
budget k through the block doesn't reach the "exceeded" state (k+1).
-/

open Turing PartrecToTM2 TM2to1

/-! ### Budget Update Function -/

/-- Update the scanning budget after reading one symbol. -/
noncomputable def bvlBudgetUpdate (k : ℕ) (b : Fin (k + 3)) (a : ChainΓ) : Fin (k + 3) :=
  if hle : b.val ≤ k then
    if a = γ'ToChainΓ Γ'.bit0 then
      ⟨b.val / 2, by omega⟩
    else if a = γ'ToChainΓ Γ'.bit1 then
      if b.val > 0 then ⟨(b.val - 1) / 2, by omega⟩
      else ⟨k + 1, by omega⟩
    else
      ⟨k + 2, by omega⟩
  else
    b

/-- Final budget after scanning through a block. -/
noncomputable def bvlScanFinal (k : ℕ) (block : List ChainΓ) : Fin (k + 3) :=
  block.foldl (bvlBudgetUpdate k) ⟨k, by omega⟩

/-! ### Budget Correctness -/

/-- Once the budget exceeds k, it stays fixed. -/
theorem bvlBudgetUpdate_fixed (k : ℕ) (b : Fin (k + 3)) (a : ChainΓ) (hb : b.val > k) :
    bvlBudgetUpdate k b a = b := by
  unfold bvlBudgetUpdate; split <;> omega

/-- Folding over a block preserves a fixed budget. -/
theorem bvlFoldl_fixed (k : ℕ) (b : Fin (k + 3)) (block : List ChainΓ) (hb : b.val > k) :
    block.foldl (bvlBudgetUpdate k) b = b := by
  induction block generalizing b with
  | nil => simp
  | cons c rest ih =>
    simp only [List.foldl_cons]
    rw [bvlBudgetUpdate_fixed k b c hb]
    exact ih b hb

/-
General budget invariant: `decodeBinaryBlock block ≤ b` iff scanning
    with initial budget b doesn't reach the exceeded state (k+1).
-/
theorem bvlBudget_correct (k : ℕ) (b : Fin (k + 3)) (block : List ChainΓ)
    (hb : b.val ≤ k) :
    decodeBinaryBlock block ≤ b.val ↔
    (block.foldl (bvlBudgetUpdate k) b).val ≠ k + 1 := by
  have h_ind : ∀ block : List ChainΓ, ∀ b : Fin (k + 3), b.val ≤ k → (decodeBinaryBlock block ≤ b.val ↔ (block.foldl (bvlBudgetUpdate k) b).val ≠ k + 1) := by
    intro block b hb;
    induction' block with c rest ih generalizing b;
    · simp +decide [ decodeBinaryBlock ];
      grind +locals;
    · by_cases hc : c = γ'ToChainΓ Γ'.bit0 <;> by_cases hc' : c = γ'ToChainΓ Γ'.bit1 <;> simp +decide [ hc, hc', bvlBudgetUpdate ];
      · simp_all +decide [ γ'ToChainΓ ];
      · split_ifs ; simp_all +decide [ decodeBinaryBlock ];
        grind;
      · split_ifs <;> simp_all +decide [ decodeBinaryBlock ];
        · grind;
        · rw [ bvlFoldl_fixed ] ; aesop;
      · rw [ show decodeBinaryBlock ( c :: rest ) = 0 from _ ];
        · rw [ bvlFoldl_fixed ] <;> aesop;
        · exact if_neg hc |> fun h => h.trans ( if_neg hc' );
  exact h_ind block b hb

/-- Main budget theorem: `decodeBinaryBlock block ≤ k` iff the final scan
    budget doesn't reach the exceeded state. -/
theorem bvlScanFinal_correct (k : ℕ) (block : List ChainΓ) :
    decodeBinaryBlock block ≤ k ↔ (bvlScanFinal k block).val ≠ k + 1 :=
  bvlBudget_correct k ⟨k, by omega⟩ block (by simp)

/-! ### TM0 Machine Definition -/

/-- State type for the blockValueLeq deciding machine. -/
abbrev BVLState (k : ℕ) := Fin (k + 3) ⊕ Bool ⊕ Bool

/-- Custom Inhabited instance: initial state has budget k. -/
instance bvlInhabited (k : ℕ) : Inhabited (BVLState k) := ⟨Sum.inl ⟨k, by omega⟩⟩

/-- The TM0 machine that decides whether `decodeBinaryBlock block ≤ k`. -/
noncomputable def bvlMachine (k : ℕ) :
    @TM0.Machine ChainΓ (BVLState k) (bvlInhabited k) :=
  fun q a =>
    match q with
    | Sum.inl b =>
      if a = (default : ChainΓ) then
        if b.val = k + 1 then
          some (Sum.inr (Sum.inl false), TM0.Stmt.move Dir.left)
        else
          some (Sum.inr (Sum.inl true), TM0.Stmt.move Dir.left)
      else
        some (Sum.inl (bvlBudgetUpdate k b a), TM0.Stmt.move Dir.right)
    | Sum.inr (Sum.inl result) =>
      if a = (default : ChainΓ) then
        some (Sum.inr (Sum.inr result), TM0.Stmt.move Dir.right)
      else
        some (Sum.inr (Sum.inl result), TM0.Stmt.move Dir.left)
    | Sum.inr (Sum.inr _) => none

/-! ### Step Lemmas -/

theorem bvlMachine_scan_nondefault (k : ℕ) (b : Fin (k + 3)) (a : ChainΓ)
    (ha : a ≠ (default : ChainΓ)) (L R : ListBlank ChainΓ) :
    @TM0.step ChainΓ (BVLState k) (bvlInhabited k) _
      (bvlMachine k) ⟨Sum.inl b, ⟨a, L, R⟩⟩ =
    some ⟨Sum.inl (bvlBudgetUpdate k b a), ⟨R.head, ListBlank.cons a L, R.tail⟩⟩ := by
  simp [TM0.step, bvlMachine, ha, Tape.move]

theorem bvlMachine_scan_default (k : ℕ) (b : Fin (k + 3))
    (L R : ListBlank ChainΓ) :
    @TM0.step ChainΓ (BVLState k) (bvlInhabited k) _
      (bvlMachine k) ⟨Sum.inl b, ⟨default, L, R⟩⟩ =
    some ⟨Sum.inr (Sum.inl (b.val ≠ k + 1)),
          ⟨L.head, L.tail, ListBlank.cons default R⟩⟩ := by
  simp only [TM0.step, bvlMachine, Tape.move]
  simp only [ite_true]
  by_cases hb : b.val = k + 1 <;> simp [hb]

theorem bvlMachine_rewind_nondefault (k : ℕ) (result : Bool) (a : ChainΓ)
    (ha : a ≠ (default : ChainΓ)) (L R : ListBlank ChainΓ) :
    @TM0.step ChainΓ (BVLState k) (bvlInhabited k) _
      (bvlMachine k) ⟨Sum.inr (Sum.inl result), ⟨a, L, R⟩⟩ =
    some ⟨Sum.inr (Sum.inl result), ⟨L.head, L.tail, ListBlank.cons a R⟩⟩ := by
  simp [TM0.step, bvlMachine, ha, Tape.move]

theorem bvlMachine_rewind_default (k : ℕ) (result : Bool)
    (L R : ListBlank ChainΓ) :
    @TM0.step ChainΓ (BVLState k) (bvlInhabited k) _
      (bvlMachine k) ⟨Sum.inr (Sum.inl result), ⟨default, L, R⟩⟩ =
    some ⟨Sum.inr (Sum.inr result), ⟨R.head, ListBlank.cons default L, R.tail⟩⟩ := by
  simp [TM0.step, bvlMachine, Tape.move]

theorem bvlMachine_halt (k : ℕ) (result : Bool) (T : Tape ChainΓ) :
    @TM0.step ChainΓ (BVLState k) (bvlInhabited k) _
      (bvlMachine k) ⟨Sum.inr (Sum.inr result), T⟩ = none := by
  simp [TM0.step, bvlMachine]

/-! ### Scanning Phase -/

/-
Generalized scanning lemma: scanning through `remaining` cells with
    budget `b` and already-processed cells `processed_rev` on the left.
-/
theorem bvlMachine_scan_gen (k : ℕ) (b : Fin (k + 3))
    (remaining : List ChainΓ) (processed_rev : List ChainΓ) (suffix : List ChainΓ)
    (hremaining : ∀ x ∈ remaining, x ≠ (default : ChainΓ)) :
    @Reaches (TM0.Cfg ChainΓ (BVLState k)) (@TM0.step ChainΓ (BVLState k) (bvlInhabited k) _
      (bvlMachine k))
      ⟨Sum.inl b,
       Tape.mk' (ListBlank.mk processed_rev)
                (ListBlank.mk (remaining ++ default :: suffix))⟩
      ⟨Sum.inl (remaining.foldl (bvlBudgetUpdate k) b),
       Tape.mk' (ListBlank.mk (remaining.reverse ++ processed_rev))
                (ListBlank.mk (default :: suffix))⟩ := by
  revert b processed_rev suffix;
  induction' remaining with a remaining ih generalizing k;
  · exact fun _ _ _ => Relation.ReflTransGen.refl;
  · intro b processed_rev suffix;
    convert Relation.ReflTransGen.trans _ ( ih k ( fun x hx => hremaining x ( List.mem_cons_of_mem _ hx ) ) ( bvlBudgetUpdate k b a ) ( a :: processed_rev ) suffix ) using 1;
    · simp +decide [ List.reverse_cons ];
    · convert Relation.ReflTransGen.single _;
      convert bvlMachine_scan_nondefault k b a ( hremaining a ( by simp +decide ) ) ( ListBlank.mk processed_rev ) ( ListBlank.mk ( remaining ++ default :: suffix ) ) using 1

/-- After scanning through block, the machine reaches the end of the block
    with the correct budget state. -/
theorem bvlMachine_scan_phase (k : ℕ) (block suffix : List ChainΓ)
    (hblock : ∀ x ∈ block, x ≠ (default : ChainΓ)) :
    @Reaches (TM0.Cfg ChainΓ (BVLState k)) (@TM0.step ChainΓ (BVLState k) (bvlInhabited k) _
      (bvlMachine k))
      (@TM0.init ChainΓ (BVLState k) (bvlInhabited k) _ (block ++ default :: suffix))
      ⟨Sum.inl (bvlScanFinal k block),
       Tape.mk' (ListBlank.mk block.reverse)
                (ListBlank.mk (default :: suffix))⟩ := by
  have h := bvlMachine_scan_gen k ⟨k, by omega⟩ block [] suffix hblock
  simp at h
  exact h

/-! ### Rewind Phase -/

/-
Rewind loop: moves left through a non-default list.
-/
theorem bvlMachine_rewind_loop (k : ℕ) (result : Bool) (revBlock : List ChainΓ)
    (hrevBlock : ∀ x ∈ revBlock, x ≠ (default : ChainΓ)) (acc : List ChainΓ) :
    @Reaches (TM0.Cfg ChainΓ (BVLState k)) (@TM0.step ChainΓ (BVLState k) (bvlInhabited k) _
      (bvlMachine k))
      ⟨Sum.inr (Sum.inl result),
       ⟨revBlock.headI, ListBlank.mk revBlock.tail, ListBlank.mk acc⟩⟩
      ⟨Sum.inr (Sum.inl result),
       ⟨default, ListBlank.mk [], ListBlank.mk (revBlock.reverse ++ acc)⟩⟩ := by
  induction' revBlock with a revBlock ih generalizing acc;
  · constructor;
  · specialize ih ( fun x hx => hrevBlock x ( List.mem_cons_of_mem _ hx ) ) ( a :: acc );
    convert Relation.ReflTransGen.head _ ih using 1;
    · simp +decide [ List.reverse_cons ];
    · convert bvlMachine_rewind_nondefault k result a ( hrevBlock a ( by simp +decide ) ) _ _ using 1

/-! ### ListBlank helper -/

@[simp] theorem listBlank_cons_default_nil_chainΓ :
    (ListBlank.mk ([] : List ChainΓ)).cons default = ListBlank.mk [] := by
  apply Quot.sound; exact Or.inr ⟨1, by simp⟩

/-! ### Main Result -/

/-
The full machine execution: scan, transition, rewind, transition, halt.
-/
theorem bvlMachine_correct (k : ℕ) (block suffix : List ChainΓ)
    (hblock : ∀ x ∈ block, x ≠ (default : ChainΓ))
    (hsuffix : ∀ x ∈ suffix, x ≠ (default : ChainΓ)) :
    let M := bvlMachine k
    let l := block ++ default :: suffix
    (@TM0Seq.evalCfg ChainΓ _ (BVLState k) (bvlInhabited k) M l).Dom ∧
    ∀ (h : (@TM0Seq.evalCfg ChainΓ _ (BVLState k) (bvlInhabited k) M l).Dom),
      ((@TM0Seq.evalCfg ChainΓ _ (BVLState k) (bvlInhabited k) M l).get h).Tape = Tape.mk₁ l ∧
      (decodeBinaryBlock block ≤ k →
        ((@TM0Seq.evalCfg ChainΓ _ (BVLState k) (bvlInhabited k) M l).get h).q =
          Sum.inr (Sum.inr true)) ∧
      (¬decodeBinaryBlock block ≤ k →
        ((@TM0Seq.evalCfg ChainΓ _ (BVLState k) (bvlInhabited k) M l).get h).q =
          Sum.inr (Sum.inr false)) := by
  set M := bvlMachine k
  set l := block ++ default :: suffix
  set result := ((bvlScanFinal k block).val ≠ k + 1)
  -- Step 1: Scanning phase reaches end of block
  have h_scan := bvlMachine_scan_phase k block suffix hblock
  -- Step 2: Transition from end-of-block to rewind
  have h_trans1 := bvlMachine_scan_default k (bvlScanFinal k block)
    (ListBlank.mk block.reverse) (ListBlank.mk suffix)
  -- Note: Tape.mk' L (ListBlank.mk (default :: suffix)) has
  -- head = default, so scan_default applies
  -- Step 3: Rewind through block.reverse
  have hblock_rev : ∀ x ∈ block.reverse, x ≠ (default : ChainΓ) := by
    intro x hx; exact hblock x (List.mem_reverse.mp hx)
  have h_rewind := bvlMachine_rewind_loop k result block.reverse hblock_rev
    (default :: suffix)
  -- Step 4: Transition from rewind-end to halt
  have h_trans2 := bvlMachine_rewind_default k result
    (ListBlank.mk []) (ListBlank.mk (block ++ default :: suffix))
  -- Step 5: Halt
  have h_halt : @TM0.step ChainΓ (BVLState k) (bvlInhabited k) _
    M ⟨Sum.inr (Sum.inr result), Tape.mk₁ l⟩ = none := bvlMachine_halt k result _
  -- Now chain all the steps
  -- First, we need to establish that the overall execution chain is valid by composing the phase steps (scan, rewind, +2 transitions).
  have h_chain :
    Reaches (TM0.step M) (TM0.init l)
      ⟨Sum.inr (Sum.inr (decide result)), Tape.mk₁ l⟩ := by
    refine' h_scan.trans ( _ : Reaches _ _ _ );
    refine' Relation.ReflTransGen.trans _ ( h_rewind.trans _ );
    · refine' Relation.ReflTransGen.single _;
      cases h : block.reverse <;> aesop;
    · convert Relation.ReflTransGen.single _ using 1;
      simp_all +decide [ ListBlank.cons ];
      congr;
      grind +suggestions;
  refine' ⟨ _, fun h => _ ⟩;
  · refine' Part.dom_iff_mem.mpr _;
    use ⟨Sum.inr (Sum.inr (decide result)), Tape.mk₁ l⟩;
    -- Apply the `mem_eval.mpr` lemma to conclude that the configuration is in the evaluation.
    apply mem_eval.mpr;
    exact ⟨ h_chain, h_halt ⟩;
  · have h_eval : (TM0Seq.evalCfg M l).get h = ⟨Sum.inr (Sum.inr (decide result)), Tape.mk₁ l⟩ := by
      obtain ⟨c, hc⟩ : ∃ c, c ∈ TM0Seq.evalCfg M l ∧ c = ⟨Sum.inr (Sum.inr (decide result)), Tape.mk₁ l⟩ := by
        simp +decide [ TM0Seq.evalCfg, h_chain ];
        grind +suggestions;
      convert hc.2;
      have := hc.1;
      exact?;
    grind +suggestions