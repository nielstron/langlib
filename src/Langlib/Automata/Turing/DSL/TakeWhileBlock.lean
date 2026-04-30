import Mathlib
import Langlib.Automata.Turing.DSL.BlockRealizability
import Langlib.Automata.Turing.DSL.DropWhileNeSep

/-! # TakeWhile (· ≠ sep) is Block-Realizable

We prove `List.takeWhile (· ≠ sep)` is block-realizable by showing:

  `takeWhile (· ≠ sep) = reverse ∘ dropFromLastSep sep ∘ reverse`

and proving `dropFromLastSep sep` is block-realizable via a simple 7-state
TM0 machine that iteratively scans for `sep` and erases the block prefix
up to (and including) the first `sep`, repeating until no `sep` remains.
-/

open Turing

/-! ### Mathematical lemmas -/

theorem takeWhile_eq_rev_dropFromLastSep_rev' {Γ : Type} [Inhabited Γ] [DecidableEq Γ]
    (sep : Γ) (l : List Γ) :
    l.takeWhile (fun x => !decide (x = sep)) =
      (dropFromLastSep sep l.reverse).reverse := by
  have h_takeWhile : dropFromLastSep sep l.reverse = (l.takeWhile (· ≠ sep)).reverse := by
    have h_dropFromLastSep_rev : ∀ (l : List Γ), dropFromLastSep sep l.reverse = (l.takeWhile (· ≠ sep)).reverse := by
      intro l;
      induction' l with x l ih;
      · rfl;
      · by_cases hx : x = sep <;> simp_all +decide [ List.takeWhile_cons ];
        · induction' l.reverse <;> simp_all +decide [ dropFromLastSep ];
        · have h_split : ∀ (l : List Γ) (x : Γ), x ≠ sep → dropFromLastSep sep (l ++ [x]) = dropFromLastSep sep l ++ [x] := by
            intros l x hx; induction' l with y l ih generalizing x <;> simp_all +decide [ dropFromLastSep ] ;
            split_ifs <;> simp_all +decide [ List.append_assoc ];
          rw [ h_split _ _ hx, ih ];
    exact h_dropFromLastSep_rev l;
  grind +splitIndPred

theorem takeWhile_eq_comp_rev_drop_rev {Γ : Type} [Inhabited Γ] [DecidableEq Γ] (sep : Γ) :
    (fun l => List.takeWhile (fun x => !decide (x = sep)) l) =
      List.reverse ∘ (dropFromLastSep sep) ∘ @List.reverse Γ := by
  funext l; simp only [Function.comp]
  exact takeWhile_eq_rev_dropFromLastSep_rev' sep l

/-! ### dropUntilFirstSep -/

/-- Drop everything up to and including the FIRST occurrence of `sep`.
    If `sep ∉ l`, returns `[]`. -/
def dropUntilFirstSep {Γ : Type} [DecidableEq Γ] (sep : Γ) : List Γ → List Γ
  | [] => []
  | c :: rest => if c = sep then rest else dropUntilFirstSep sep rest

theorem dropUntilFirstSep_length_lt {Γ : Type} [DecidableEq Γ]
    (sep : Γ) (block : List Γ) (hmem : sep ∈ block) :
    (dropUntilFirstSep sep block).length < block.length := by
  induction block with
  | nil => simp at hmem
  | cons c rest ih =>
    simp only [dropUntilFirstSep]
    split_ifs with h
    · simp
    · have : sep ∈ rest := by
        cases hmem with
        | head => exact absurd rfl h
        | tail _ h' => exact h'
      have := ih this
      simp only [List.length_cons]
      omega

theorem dropUntilFirstSep_ne_default {Γ : Type} [Inhabited Γ] [DecidableEq Γ]
    (sep : Γ) (block : List Γ)
    (hblock : ∀ g ∈ block, g ≠ default) :
    ∀ g ∈ dropUntilFirstSep sep block, g ≠ default := by
  induction block with
  | nil => simp [dropUntilFirstSep]
  | cons c rest ih =>
    simp only [dropUntilFirstSep]
    split_ifs
    · exact fun g hg => hblock g (List.mem_cons_of_mem _ hg)
    · exact ih (fun g hg => hblock g (List.mem_cons_of_mem _ hg))

/-
Key connection: `dropFromLastSep` applied to a block with `sep` equals
    `dropFromLastSep` applied after removing the first occurrence via
    `dropUntilFirstSep`.
-/
theorem dropFromLastSep_eq_of_dropUntilFirstSep {Γ : Type} [Inhabited Γ] [DecidableEq Γ]
    (sep : Γ) (block : List Γ) (hmem : sep ∈ block) :
    dropFromLastSep sep block =
      dropFromLastSep sep (dropUntilFirstSep sep block) := by
  induction' block with c rest ih;
  · contradiction;
  · by_cases h : sep ∈ rest <;> simp_all +decide [ dropFromLastSep, dropUntilFirstSep ];
    · grind;
    · exact?

/-
Block decomposition at first `sep`.
-/
theorem block_first_sep_decomp {Γ : Type} [DecidableEq Γ]
    (sep : Γ) (block : List Γ) (hmem : sep ∈ block) :
    ∃ pfx rest, block = pfx ++ sep :: rest ∧
      (∀ g ∈ pfx, g ≠ sep) ∧
      dropUntilFirstSep sep block = rest := by
  induction' block with c block ih;
  · contradiction;
  · by_cases h : c = sep <;> simp_all +decide [ dropUntilFirstSep ];
    grind

/-! ### Machine definition -/

/-- State type for the dropFromLastSep TM0 machine. Only 7 plain states. -/
inductive DFLState where
  | scan     -- scanning right for sep
  | goBack   -- going left to find start of block (default cell)
  | erase    -- erasing cells from left to first sep
  | wSep     -- just wrote default over sep cell
  | wOther   -- just wrote default over non-sep cell
  | rewind   -- no sep found, rewinding left to start
  | done     -- halted
  deriving DecidableEq

instance : Inhabited DFLState := ⟨.scan⟩

instance : Fintype DFLState where
  elems := {.scan, .goBack, .erase, .wSep, .wOther, .rewind, .done}
  complete := by intro x; cases x <;> simp

/-- The dropFromLastSep TM0 machine. -/
noncomputable def dflMachine {Γ : Type} [Inhabited Γ] [DecidableEq Γ]
    (sep : Γ) : @TM0.Machine Γ DFLState ⟨.scan⟩ := fun q a =>
  match q with
  | .scan =>
    if a = sep then some (.goBack, .move Dir.left)
    else if a = default then some (.rewind, .move Dir.left)
    else some (.scan, .move Dir.right)
  | .goBack =>
    if a = default then some (.erase, .move Dir.right)
    else some (.goBack, .move Dir.left)
  | .erase =>
    if a = sep then some (.wSep, .write default)
    else if a = default then none
    else some (.wOther, .write default)
  | .wSep => some (.scan, .move Dir.right)
  | .wOther => some (.erase, .move Dir.right)
  | .rewind =>
    if a = default then some (.done, .move Dir.right)
    else some (.rewind, .move Dir.left)
  | .done => none

/-! ### Key tape lemma -/

/-
Writing default at head and moving right on `Tape.mk₁ (c :: rest)`
gives `Tape.mk₁ rest`. The leading default is absorbed by ListBlank.
-/
theorem tape_erase_step {Γ : Type} [Inhabited Γ]
    (c : Γ) (rest : List Γ) :
    Tape.move Dir.right (Tape.write default (Tape.mk₁ (c :: rest))) =
      Tape.mk₁ rest := by
  -- By definition of `Tape.move` and `Tape.write`, we can simplify the expression.
  simp [Tape.move, Tape.write, Tape.mk₁];
  unfold Tape.mk₂;
  unfold Tape.mk';
  congr;
  exact?

/-
Moving left then right from `Tape.mk₁ l` is the identity.
-/
theorem tape_move_left_right_mk₁ {Γ : Type} [Inhabited Γ] (l : List Γ) :
    Tape.move Dir.right (Tape.move Dir.left (Tape.mk₁ l)) = Tape.mk₁ l := by
  cases l <;> simp +decide [ Tape.move ]

/-! ### Phase lemmas -/

/-
Scan right loop: scan moves right through non-sep, non-default cells.
-/
theorem dfl_scan_right {Γ : Type} [Inhabited Γ] [DecidableEq Γ]
    (sep : Γ) (hsep : sep ≠ default)
    (L : List Γ) (pfx rest : List Γ)
    (hpfx_nsep : ∀ g ∈ pfx, g ≠ sep)
    (hpfx_nd : ∀ g ∈ pfx, g ≠ default) :
    Reaches (TM0.step (dflMachine sep))
      ⟨.scan, Tape.mk₂ L (pfx ++ rest)⟩
      ⟨.scan, Tape.mk₂ (pfx.reverse ++ L) rest⟩ := by
  induction' pfx with c pfx ih generalizing L;
  · constructor;
  · have h_step : TM0.step (dflMachine sep) ⟨DFLState.scan, Tape.mk₂ L (c :: pfx ++ rest)⟩ = some ⟨DFLState.scan, Tape.mk₂ (c :: L) (pfx ++ rest)⟩ := by
      unfold dflMachine; simp +decide [ RevBlock.mk₂_head, RevBlock.mk₂_move_right ] ;
      unfold TM0.step; simp +decide [ RevBlock.mk₂_head, RevBlock.mk₂_move_right ] ;
      exact ⟨ TM0.Stmt.move Dir.right, by aesop, by exact RevBlock.mk₂_move_right _ _ _ ⟩;
    have h_reach : Reaches (TM0.step (dflMachine sep)) ⟨DFLState.scan, Tape.mk₂ (c :: L) (pfx ++ rest)⟩ ⟨DFLState.scan, Tape.mk₂ (pfx.reverse ++ (c :: L)) rest⟩ := by
      exact ih _ ( fun g hg => hpfx_nsep g ( List.mem_cons_of_mem _ hg ) ) ( fun g hg => hpfx_nd g ( List.mem_cons_of_mem _ hg ) );
    convert Relation.ReflTransGen.trans _ h_reach using 1;
    · grind;
    · exact .single ( by aesop )

/-
GoBack loop starting from the tape after scan moved left.
    Goes left through non-default cells, finds default, moves right → erase.
-/
theorem dfl_goBack_after_left {Γ : Type} [Inhabited Γ] [DecidableEq Γ]
    (sep : Γ)
    (L R : List Γ) (hL : ∀ g ∈ L, g ≠ default) :
    Reaches (TM0.step (dflMachine sep))
      ⟨.goBack, Tape.move Dir.left (Tape.mk₂ L R)⟩
      ⟨.erase, Tape.mk₁ (L.reverse ++ R)⟩ := by
  induction' L with x L ih generalizing R <;> simp_all +decide [ Tape.mk₂ ];
  · refine' Relation.ReflTransGen.single _;
    unfold dflMachine; simp +decide [ Tape.mk₁, Tape.mk' ] ;
    convert tape_move_left_right_mk₁ R using 1;
    unfold TM0.step; simp +decide [ Tape.mk₁, Tape.mk₂ ] ;
    unfold Tape.move; aesop;
  · have h_step : TM0.step (dflMachine sep) ⟨DFLState.goBack, Tape.mk' (ListBlank.mk L) (ListBlank.mk (x :: R))⟩ = some ⟨DFLState.goBack, Tape.mk' (ListBlank.mk L.tail) (ListBlank.mk (L.headI :: x :: R))⟩ := by
      unfold TM0.step;
      cases L <;> simp_all +decide [ dflMachine ];
    exact Relation.ReflTransGen.head h_step ( by simpa using ih ( x :: R ) )

/-
Erase loop: erases all pfx cells and sep, reaching scan at rest.
-/
theorem dfl_erase_loop {Γ : Type} [Inhabited Γ] [DecidableEq Γ]
    (sep : Γ) (hsep : sep ≠ default)
    (pfx rest : List Γ)
    (hpfx_nsep : ∀ g ∈ pfx, g ≠ sep)
    (hpfx_nd : ∀ g ∈ pfx, g ≠ default) :
    Reaches (TM0.step (dflMachine sep))
      ⟨.erase, Tape.mk₁ (pfx ++ sep :: rest)⟩
      ⟨.scan, Tape.mk₁ rest⟩ := by
  have h_erase : ∀ (c : Γ) (rest : List Γ), c ≠ sep → c ≠ default → Reaches (TM0.step (dflMachine sep)) ⟨.erase, Tape.mk₁ (c :: rest)⟩ ⟨.erase, Tape.mk₁ rest⟩ := by
    intros c rest hc hc';
    constructor;
    rotate_right;
    exact ⟨ .wOther, Tape.write default ( Tape.mk₁ ( c :: rest ) ) ⟩;
    · apply_rules [ Relation.ReflTransGen.single ];
      unfold dflMachine; simp +decide [ hc, hc' ] ;
      unfold TM0.step; simp +decide [ hc, hc' ] ;
      exact ⟨ _, if_neg ( by unfold Tape.mk₁; aesop ) |> fun h => h.trans ( if_neg ( by unfold Tape.mk₁; aesop ) ), rfl ⟩;
    · unfold TM0.step;
      unfold dflMachine; simp +decide [ hc, hc' ] ;
      exact?;
  induction' pfx with c pfx ih;
  · constructor;
    rotate_right;
    exact ⟨ DFLState.wSep, Tape.write default ( Tape.mk₁ ( sep :: rest ) ) ⟩;
    · apply_rules [ Relation.ReflTransGen.single ];
      unfold dflMachine; simp +decide [ hsep ] ;
      unfold TM0.step; simp +decide [ hsep ] ;
      exact ⟨ _, if_pos rfl, rfl ⟩;
    · unfold TM0.step; simp +decide [ dflMachine ] ;
      exact?;
  · have := h_erase c ( pfx ++ sep :: rest ) ( hpfx_nsep c ( by simp +decide ) ) ( hpfx_nd c ( by simp +decide ) );
    simpa only [ List.cons_append ] using this.trans ( ih ( fun g hg => hpfx_nsep g ( List.mem_cons_of_mem _ hg ) ) ( fun g hg => hpfx_nd g ( List.mem_cons_of_mem _ hg ) ) )

/-
Rewind loop starting from the tape after scan moved left.
    Goes left through non-default cells, finds default, moves right → done.
-/
theorem dfl_rewind_after_left {Γ : Type} [Inhabited Γ] [DecidableEq Γ]
    (sep : Γ)
    (L R : List Γ) (hL : ∀ g ∈ L, g ≠ default) :
    Reaches (TM0.step (dflMachine sep))
      ⟨.rewind, Tape.move Dir.left (Tape.mk₂ L R)⟩
      ⟨.done, Tape.mk₁ (L.reverse ++ R)⟩ := by
  induction' L with x L ih generalizing R;
  · convert Relation.ReflTransGen.single _;
    convert Set.mem_singleton _ using 1;
    rotate_left;
    exact TM0.Cfg Γ DFLState;
    exact ⟨ DFLState.done, Tape.mk₁ R ⟩;
    unfold TM0.step; simp +decide [ dflMachine ] ;
    exact ⟨ _, if_pos ( by cases R <;> rfl ), tape_move_left_right_mk₁ _ ⟩;
  · have h_rewind_step : Reaches (TM0.step (dflMachine sep)) ⟨DFLState.rewind, Tape.mk₂ L (x :: R)⟩ ⟨DFLState.rewind, Tape.move Dir.left (Tape.mk₂ L (x :: R))⟩ := by
      constructor;
      constructor;
      unfold TM0.step;
      unfold dflMachine; aesop;
    convert h_rewind_step.trans ( ih ( x :: R ) fun g hg => hL g <| List.mem_cons_of_mem _ hg ) using 1;
    · exact congr_arg _ ( RevBlock.mk₂_move_left _ _ _ );
    · simp +decide [ List.reverse_cons ]

/-! ### Combined iteration lemmas -/

/-
One cycle: if `sep ∈ block'`, the machine performs scan → goBack → erase → scan,
    reducing the block by `dropUntilFirstSep`.
-/
theorem dfl_one_cycle {Γ : Type} [Inhabited Γ] [DecidableEq Γ]
    (sep : Γ) (hsep : sep ≠ default)
    (block' suffix : List Γ)
    (hblock : ∀ g ∈ block', g ≠ default)
    (hmem : sep ∈ block') :
    Reaches (TM0.step (dflMachine sep))
      ⟨.scan, Tape.mk₁ (block' ++ default :: suffix)⟩
      ⟨.scan, Tape.mk₁ (dropUntilFirstSep sep block' ++ default :: suffix)⟩ := by
  obtain ⟨ pfx, rest, h₁, h₂, h₃ ⟩ := block_first_sep_decomp sep block' hmem;
  have h_scan : Reaches (TM0.step (dflMachine sep)) ⟨DFLState.scan, Tape.mk₁ ((pfx ++ sep :: rest) ++ default :: suffix)⟩ ⟨DFLState.scan, Tape.mk₂ pfx.reverse (sep :: rest ++ default :: suffix)⟩ := by
    convert dfl_scan_right sep hsep [] pfx ( sep :: rest ++ default :: suffix ) _ _ using 1 <;> simp +decide [ * ];
    · exact?;
    · assumption;
    · exact fun g hg => hblock g <| h₁.symm ▸ List.mem_append_left _ hg;
  have h_goBack : Reaches (TM0.step (dflMachine sep)) ⟨DFLState.scan, Tape.mk₂ pfx.reverse (sep :: rest ++ default :: suffix)⟩ ⟨DFLState.erase, Tape.mk₁ (pfx ++ sep :: rest ++ default :: suffix)⟩ := by
    have h_goBack : Reaches (TM0.step (dflMachine sep)) ⟨DFLState.scan, Tape.mk₂ pfx.reverse (sep :: rest ++ default :: suffix)⟩ ⟨DFLState.goBack, Tape.move Dir.left (Tape.mk₂ pfx.reverse (sep :: rest ++ default :: suffix))⟩ := by
      apply Relation.ReflTransGen.single;
      simp +decide [ TM0.step, dflMachine ];
      use TM0.Stmt.move Dir.left;
      simp +decide [ Tape.mk₂, Tape.head ];
    convert h_goBack.trans _;
    convert dfl_goBack_after_left sep pfx.reverse ( sep :: rest ++ default :: suffix ) _ using 1;
    · simp +decide [ List.reverse_reverse ];
    · grind;
  have h_erase : Reaches (TM0.step (dflMachine sep)) ⟨DFLState.erase, Tape.mk₁ (pfx ++ sep :: rest ++ default :: suffix)⟩ ⟨DFLState.scan, Tape.mk₁ (rest ++ default :: suffix)⟩ := by
    convert dfl_erase_loop sep hsep pfx ( rest ++ default :: suffix ) h₂ _ using 1;
    · simp +decide [ List.append_assoc ];
    · exact fun g hg => hblock g <| h₁.symm ▸ List.mem_append_left _ hg;
  convert h_scan.trans ( h_goBack.trans h_erase ) using 1;
  · rw [ h₁ ];
  · rw [ h₃ ]

/-
No-sep cycle: if `sep ∉ block'`, the machine scans through and halts.
-/
theorem dfl_no_sep_cycle {Γ : Type} [Inhabited Γ] [DecidableEq Γ]
    (sep : Γ) (hsep : sep ≠ default)
    (block' suffix : List Γ)
    (hblock : ∀ g ∈ block', g ≠ default)
    (hnot : sep ∉ block') :
    Reaches (TM0.step (dflMachine sep))
      ⟨.scan, Tape.mk₁ (block' ++ default :: suffix)⟩
      ⟨.done, Tape.mk₁ (block' ++ default :: suffix)⟩ := by
  -- Apply `dfl_scan_right` with L=[], prefix=block', and rest=(default :: suffix).
  have h_scan : Reaches (TM0.step (dflMachine sep)) ⟨.scan, Tape.mk₁ (block' ++ default :: suffix)⟩ ⟨.scan, Tape.mk₂ block'.reverse (default :: suffix)⟩ := by
    convert dfl_scan_right sep hsep [] block' ( default :: suffix ) _ _ using 1;
    · rw [ List.append_nil ];
    · exact fun g hg => fun h => hnot <| h ▸ hg;
    · assumption;
  refine' h_scan.trans _;
  have h_scan_default : TM0.step (dflMachine sep) ⟨.scan, Tape.mk₂ block'.reverse (default :: suffix)⟩ = some ⟨.rewind, Tape.move Dir.left (Tape.mk₂ block'.reverse (default :: suffix))⟩ := by
    unfold dflMachine; simp +decide [ *, TM0.step ] ;
    rw [ if_neg, if_pos ];
    · exact ⟨ _, rfl, rfl ⟩;
    · exact?;
    · unfold Tape.mk₂; aesop;
  have h_rewind : Reaches (TM0.step (dflMachine sep)) ⟨.rewind, Tape.move Dir.left (Tape.mk₂ block'.reverse (default :: suffix))⟩ ⟨.done, Tape.mk₁ (block'.reverse.reverse ++ default :: suffix)⟩ := by
    apply dfl_rewind_after_left;
    aesop;
  simpa using Relation.ReflTransGen.head ( by simp +decide [ h_scan_default ] ) h_rewind

/-! ### Full computation -/

/-- The machine halts in state `done`. -/
theorem dfl_step_done {Γ : Type} [Inhabited Γ] [DecidableEq Γ]
    (sep : Γ) (T : Tape Γ) :
    TM0.step (dflMachine sep) ⟨DFLState.done, T⟩ = none := by
  simp [TM0.step, dflMachine]

/-
Full machine correctness.
-/
theorem dfl_full_reaches {Γ : Type} [Inhabited Γ] [DecidableEq Γ]
    (sep : Γ) (hsep : sep ≠ default)
    (block suffix : List Γ)
    (hblock : ∀ g ∈ block, g ≠ default) (hsuffix : ∀ g ∈ suffix, g ≠ default) :
    Reaches (TM0.step (dflMachine sep))
      (TM0.init (block ++ default :: suffix))
      ⟨DFLState.done, Tape.mk₁ (dropFromLastSep sep block ++ default :: suffix)⟩ := by
  induction' n : block.length using Nat.strong_induction_on with n ih generalizing block;
  by_cases h : sep ∈ block;
  · have h_ind : Reaches (TM0.step (dflMachine sep)) (⟨.scan, Tape.mk₁ (dropUntilFirstSep sep block ++ default :: suffix)⟩) ⟨.done, Tape.mk₁ (dropFromLastSep sep (dropUntilFirstSep sep block) ++ default :: suffix)⟩ := by
      convert ih _ _ _ _ rfl using 1;
      · exact n ▸ dropUntilFirstSep_length_lt sep block h;
      · exact?;
    convert dfl_one_cycle sep hsep block suffix hblock h |> fun h => h.trans h_ind using 1;
    rw [ dropFromLastSep_eq_of_dropUntilFirstSep sep block h ];
  · rw [ dropFromLastSep_not_mem _ _ h ];
    convert dfl_no_sep_cycle sep hsep block suffix hblock h using 1

/-! ### Main results -/

/-- `dropFromLastSep sep` is block-realizable. -/
theorem tm0_dropFromLastSep_direct {Γ : Type} [Inhabited Γ] [DecidableEq Γ] [Fintype Γ]
    (sep : Γ) (hsep : sep ≠ default) :
    TM0RealizesBlock Γ (dropFromLastSep sep) := by
  refine ⟨DFLState, inferInstance, inferInstance, dflMachine sep, ?_⟩
  intro block suffix hblock hsuffix hfblock
  have h_reaches := dfl_full_reaches sep hsep block suffix hblock hsuffix
  constructor
  · exact Part.dom_iff_mem.mpr ⟨_, Turing.mem_eval.mpr ⟨h_reaches, dfl_step_done sep _⟩⟩
  · intro h
    have h_mem := Turing.mem_eval.mpr ⟨h_reaches, dfl_step_done sep _⟩
    exact (Part.mem_unique (Part.get_mem h) h_mem).symm ▸ rfl

/-- `takeWhile (· ≠ sep)` is block-realizable. -/
theorem tm0_takeWhileNeSep' {Γ : Type} [Inhabited Γ] [DecidableEq Γ] [Fintype Γ]
    (sep : Γ) (hsep : sep ≠ default) :
    TM0RealizesBlock Γ (List.takeWhile (fun x => !decide (x = sep))) := by
  have heq : (List.takeWhile (fun x => !decide (x = sep)) : List Γ → List Γ) =
      List.reverse ∘ (dropFromLastSep sep) ∘ @List.reverse Γ :=
    takeWhile_eq_comp_rev_drop_rev sep
  rw [heq]
  apply tm0RealizesBlock_comp
  · apply tm0RealizesBlock_comp
    · exact tm0_reverse_block
    · exact tm0_dropFromLastSep_direct sep hsep
    · exact reverse_ne_default
  · exact tm0_reverse_block
  · intro block hblock
    simp only [Function.comp]
    exact dropFromLastSep_ne_default sep _ (reverse_ne_default block hblock)