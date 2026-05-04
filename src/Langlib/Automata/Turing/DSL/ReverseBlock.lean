import Mathlib
import Langlib.Automata.Turing.DSL.TM0Compose

/-! # TM0 Reverse Block Machine -/

open Turing

namespace RevBlock

variable {Γ : Type} [Inhabited Γ] [DecidableEq Γ]

/-! ### State type -/

inductive CarryPhase where | carryRight | shifting | returning deriving DecidableEq
inductive NoCarryPhase where | grab | advance | rewind | rewindDone deriving DecidableEq

instance : Fintype CarryPhase where
  elems := {.carryRight, .shifting, .returning}; complete x := by cases x <;> simp

instance : Fintype NoCarryPhase where
  elems := {.grab, .advance, .rewind, .rewindDone}; complete x := by cases x <;> simp

abbrev RSt (Γ : Type) := (Γ × CarryPhase) ⊕ NoCarryPhase
instance [Inhabited Γ] : Inhabited (RSt Γ) := ⟨Sum.inr .grab⟩

/-! ### Machine definition -/

noncomputable def M (Γ : Type) [Inhabited Γ] [DecidableEq Γ] :
    @TM0.Machine Γ (RSt Γ) ⟨Sum.inr .grab⟩ :=
  fun q a => match q with
    | Sum.inr .grab =>
      if a = default then some (Sum.inr .rewind, TM0.Stmt.move Dir.left)
      else some (Sum.inl (a, .carryRight), TM0.Stmt.write default)
    | Sum.inl (g, .carryRight) => some (Sum.inl (g, .shifting), TM0.Stmt.move Dir.right)
    | Sum.inl (g, .shifting) =>
      if a = default then some (Sum.inl (g, .returning), TM0.Stmt.move Dir.left)
      else some (Sum.inl (a, .carryRight), TM0.Stmt.write g)
    | Sum.inl (g, .returning) =>
      if a = default then some (Sum.inr .advance, TM0.Stmt.write g)
      else some (Sum.inl (g, .returning), TM0.Stmt.move Dir.left)
    | Sum.inr .advance => some (Sum.inr .grab, TM0.Stmt.move Dir.right)
    | Sum.inr .rewind =>
      if a = default then some (Sum.inr .rewindDone, TM0.Stmt.move Dir.right)
      else some (Sum.inr .rewind, TM0.Stmt.move Dir.left)
    | Sum.inr .rewindDone => none

/-! ### Tape.mk₂ helpers -/

omit [DecidableEq Γ] in
private theorem listBlank_mk_headI_tail (R : List Γ) :
    ListBlank.mk (R.headI :: R.tail) = ListBlank.mk R := by
  apply ListBlank.ext; intro i; simp only [ListBlank.nth_mk]
  cases R with | nil => cases i <;> simp [List.getI, List.getD, List.headI] | cons _ _ => rfl

omit [DecidableEq Γ] in
theorem mk₂_move_right (L : List Γ) (x : Γ) (R : List Γ) :
    Tape.move Dir.right (Tape.mk₂ L (x :: R)) = Tape.mk₂ (x :: L) R := by
  simp [Tape.mk₂, Tape.mk', Tape.move, ListBlank.head_mk, ListBlank.tail_mk, ListBlank.cons_mk]

omit [DecidableEq Γ] in
theorem mk₂_move_left (x : Γ) (L R : List Γ) :
    Tape.move Dir.left (Tape.mk₂ (x :: L) R) = Tape.mk₂ L (x :: R) := by
  simp only [Tape.mk₂, Tape.mk', Tape.move, ListBlank.head_mk, ListBlank.tail_mk,
    ListBlank.cons_mk, List.headI, List.tail_cons]
  congr 1; exact listBlank_mk_headI_tail R

omit [DecidableEq Γ] in
theorem mk₂_write (a : Γ) (L : List Γ) (x : Γ) (R : List Γ) :
    Tape.write a (Tape.mk₂ L (x :: R)) = Tape.mk₂ L (a :: R) := by
  simp [Tape.mk₂, Tape.mk', Tape.write, ListBlank.tail_mk]

omit [DecidableEq Γ] in
theorem mk₂_head (L : List Γ) (x : Γ) (R : List Γ) :
    (Tape.mk₂ L (x :: R)).head = x := by
  simp [Tape.mk₂, Tape.mk', ListBlank.head_mk]

omit [DecidableEq Γ] in
theorem mk₂_nil_eq_mk₁ (R : List Γ) : Tape.mk₂ [] R = Tape.mk₁ R := by
  simp [Tape.mk₂, Tape.mk₁, Tape.mk']

/-! ### Return loop -/

/-
Return loop: from returning(carry), move left through non-default head elements.
    Each step pops from the left and pushes the old head onto the right.
-/
theorem return_loop (carry h : Γ) (elems L_orig R : List Γ)
    (hh : h ≠ default) (helems : ∀ y ∈ elems, y ≠ default) :
    Reaches (TM0.step (M Γ))
      ⟨Sum.inl (carry, .returning), Tape.mk₂ (elems ++ default :: L_orig) (h :: R)⟩
      ⟨Sum.inl (carry, .returning), Tape.mk₂ L_orig (default :: elems.reverse ++ h :: R)⟩ := by
  revert elems L_orig R h hh helems;
  intro h elems L_orig R hh helems
  induction' elems with e elems ih generalizing L_orig R h;
  · constructor;
    constructor;
    unfold TM0.step M; simp +decide [ hh ] ;
    rw [ if_neg ];
    · exact ⟨ TM0.Stmt.move Dir.left, rfl, by exact? ⟩;
    · exact?;
  · refine' Relation.ReflTransGen.head _ _;
    exact ⟨ Sum.inl ( carry, CarryPhase.returning ), Tape.mk₂ ( elems ++ default :: L_orig ) ( e :: h :: R ) ⟩;
    · simp +decide [ TM0.step, M ];
      rw [ if_neg ];
      · exact ⟨ TM0.Stmt.move Dir.left, rfl, by exact? ⟩;
      · exact?;
    · convert ih e L_orig ( h :: R ) ( helems e ( by simp +decide ) ) ( fun y hy => helems y ( by simp +decide [ hy ] ) ) using 1;
      simp +decide [ List.reverse_cons ]

/-! ### Shift-to-grab -/

/-
From shifting(carry) to grab: complete shift + return + deposit + advance.
    `shifted` tracks elements already pushed onto the left during previous shift steps.
-/
theorem shift_to_grab (carry : Γ) (rest shifted L_orig suffix : List Γ)
    (hcarry : carry ≠ default) (hrest : ∀ y ∈ rest, y ≠ default)
    (hshifted : ∀ y ∈ shifted, y ≠ default) (hsuf : ∀ y ∈ suffix, y ≠ default) :
    Reaches (TM0.step (M Γ))
      ⟨Sum.inl (carry, .shifting),
       Tape.mk₂ (shifted ++ default :: L_orig) (rest ++ default :: suffix)⟩
      ⟨Sum.inr .grab,
       Tape.mk₂ ((carry :: rest).getLast (by simp) :: L_orig)
         (shifted.reverse ++ (carry :: rest).dropLast ++ default :: suffix)⟩ := by
  induction' rest with r rest ih generalizing carry shifted L_orig suffix;
  · cases shifted <;> simp_all +decide [ List.getLast ];
    · convert Relation.ReflTransGen.trans _ _ using 1;
      exact ⟨ Sum.inl ( carry, .returning ), Tape.mk₂ L_orig ( default :: default :: suffix ) ⟩;
      · convert Relation.ReflTransGen.single _ using 1;
        simp +decide [ TM0.step ];
        use TM0.Stmt.move Dir.left;
        exact ⟨ by unfold M; aesop, by unfold Tape.move; aesop ⟩;
      · convert Relation.ReflTransGen.trans _ _ using 1;
        exact ⟨ Sum.inr NoCarryPhase.advance, Tape.mk₂ L_orig ( carry :: default :: suffix ) ⟩;
        · convert Relation.ReflTransGen.single _ using 1;
          simp +decide [ TM0.step, M ];
          exact ⟨ TM0.Stmt.write carry, by rw [ if_pos ( by exact? ) ], by exact? ⟩;
        · apply_rules [ Relation.ReflTransGen.single ];
    · rename_i x xs;
      -- Apply the return loop to the current state.
      have h_return : Reaches (TM0.step (M Γ)) ⟨Sum.inl (carry, .returning), Tape.mk₂ (xs ++ default :: L_orig) (x :: default :: suffix)⟩ ⟨Sum.inl (carry, .returning), Tape.mk₂ L_orig (default :: xs.reverse ++ x :: default :: suffix)⟩ := by
        convert return_loop carry x xs L_orig ( default :: suffix ) hshifted.1 hshifted.2 using 1;
      refine' Relation.ReflTransGen.trans _ ( Relation.ReflTransGen.trans h_return _ );
      · apply_rules [ Relation.ReflTransGen.single ];
        unfold TM0.step; simp +decide [ *, List.append_assoc ] ;
        exact ⟨ TM0.Stmt.move Dir.left, by unfold M; aesop, by unfold Tape.move; aesop ⟩;
      · refine' Relation.ReflTransGen.trans _ _;
        exact ⟨ Sum.inr NoCarryPhase.advance, Tape.mk₂ L_orig ( carry :: xs.reverse ++ x :: default :: suffix ) ⟩;
        · refine' Relation.ReflTransGen.single _;
          unfold TM0.step; simp +decide [ M ] ;
          exact ⟨ _, if_pos ( by exact? ), by exact? ⟩;
        · apply_rules [ Relation.ReflTransGen.single ];
  · -- Apply the step_shifting_nondefault lemma to move to the next state.
    have h_step : TM0.step (M Γ) ⟨Sum.inl (carry, .shifting), Tape.mk₂ (shifted ++ default :: L_orig) (r :: rest ++ default :: suffix)⟩ =
      some ⟨Sum.inl (r, .carryRight), Tape.mk₂ (shifted ++ default :: L_orig) (carry :: rest ++ default :: suffix)⟩ := by
        unfold TM0.step M; aesop;
    have := ih r ( carry :: shifted ) L_orig suffix ( hrest r ( by simp +decide ) ) ( fun y hy => hrest y ( by simp +decide [ hy ] ) ) ( by aesop ) ( by aesop );
    convert Relation.ReflTransGen.trans _ this using 1;
    · simp +decide [ List.getLast, List.dropLast ];
    · exact .single ( by aesop ) |> Relation.ReflTransGen.trans <| .single ( by aesop )

/-! ### One iteration -/

theorem one_iteration (x : Γ) (rest L_orig suffix : List Γ)
    (hx : x ≠ default) (hrest : ∀ y ∈ rest, y ≠ default) (hsuf : ∀ y ∈ suffix, y ≠ default) :
    Reaches (TM0.step (M Γ))
      ⟨Sum.inr .grab, Tape.mk₂ L_orig ((x :: rest) ++ default :: suffix)⟩
      ⟨Sum.inr .grab,
       Tape.mk₂ ((x :: rest).getLast (by simp) :: L_orig)
         ((x :: rest).dropLast ++ default :: suffix)⟩ := by
  by_contra h_contra;
  obtain ⟨c₁, hc₁⟩ : ∃ c₁, TM0.step (M Γ) ⟨Sum.inr .grab, Tape.mk₂ L_orig (x :: rest ++ default :: suffix)⟩ = some c₁ ∧ TM0.step (M Γ) c₁ = some ⟨Sum.inl (x, .shifting), Tape.mk₂ (default :: L_orig) (rest ++ default :: suffix)⟩ := by
    unfold M;
    simp +decide [ hx, hrest, hsuf, TM0.step, Tape.mk₂ ];
  apply h_contra;
  convert Relation.ReflTransGen.trans _ ( shift_to_grab x rest [] L_orig suffix hx hrest ( by simp ) hsuf ) using 1;
  exact .single ( by aesop ) |> Relation.ReflTransGen.trans <| .single ( by aesop )

/-! ### Iteration loop -/

theorem iteration_loop (block suffix : List Γ)
    (hblock : ∀ y ∈ block, y ≠ default) (hsuf : ∀ y ∈ suffix, y ≠ default) :
    Reaches (TM0.step (M Γ))
      ⟨Sum.inr .grab, Tape.mk₂ [] (block ++ default :: suffix)⟩
      ⟨Sum.inr .grab, Tape.mk₂ block (default :: suffix)⟩ := by
  have h_ind : ∀ (block : List Γ) (L : List Γ) (suffix : List Γ), (∀ y ∈ block, y ≠ default) → (∀ y ∈ suffix, y ≠ default) → Reaches (TM0.step (M Γ)) ⟨Sum.inr NoCarryPhase.grab, Tape.mk₂ L (block ++ default :: suffix)⟩ ⟨Sum.inr NoCarryPhase.grab, Tape.mk₂ (block ++ L) (default :: suffix)⟩ := by
    intros block L suffix hblock hsuf
    induction' block using List.reverseRecOn with x block ih generalizing L;
    · constructor;
    · cases x <;> simp_all +decide [ List.append_assoc ];
      · convert one_iteration block [] L suffix hblock ( by simp +decide ) hsuf using 1;
      · have := one_iteration ‹_› ( ‹_› ++ [block] ) L suffix; simp_all +decide [ List.append_assoc ] ;
        simp_all +decide [ List.dropLast ];
        exact this.trans ( by simpa [ List.append_assoc ] using ih ( block :: L ) );
  simpa using h_ind block [] suffix hblock hsuf

/-! ### Rewind loop -/

theorem rewind_loop (s : Γ) (rest R_rest : List Γ)
    (hs : s ≠ default) (hrest : ∀ y ∈ rest, y ≠ default) :
    Reaches (TM0.step (M Γ))
      ⟨Sum.inr .rewind, Tape.mk₂ rest (s :: R_rest)⟩
      ⟨Sum.inr .rewind, Tape.mk₂ [] (default :: rest.reverse ++ s :: R_rest)⟩ := by
  contrapose! hs;
  contrapose! hs with h;
  induction' rest with x rest ih generalizing s R_rest <;> simp_all +decide [ Tape.mk₂ ];
  · constructor;
    constructor;
    unfold TM0.step M; simp +decide [ h ] ;
  · have h_step : TM0.step (M Γ) ⟨Sum.inr .rewind, Tape.mk' (ListBlank.mk (x :: rest)) (ListBlank.mk (s :: R_rest))⟩ = some ⟨Sum.inr .rewind, Tape.mk' (ListBlank.mk rest) (ListBlank.mk (x :: s :: R_rest))⟩ := by
      unfold TM0.step;
      unfold M; simp +decide [ h, hrest ] ;
    exact Relation.ReflTransGen.head h_step ( by simpa using ih x ( s :: R_rest ) hrest.1 )

/-! ### Rewind phase -/

theorem rewind_phase (block suffix : List Γ)
    (hblock : ∀ y ∈ block, y ≠ default) :
    Reaches (TM0.step (M Γ))
      ⟨Sum.inr .grab, Tape.mk₂ block (default :: suffix)⟩
      ⟨Sum.inr .rewindDone, Tape.mk₂ [] (block.reverse ++ default :: suffix)⟩ := by
  constructor;
  rotate_right;
  exact ⟨ Sum.inr NoCarryPhase.rewind, Tape.mk₂ [] ( default :: block.reverse ++ default :: suffix ) ⟩;
  · cases block <;> simp_all +decide [ ListBlank.mk ];
    · refine' .single _;
      unfold TM0.step;
      unfold M; simp +decide [ Tape.mk₂ ] ;
    · rename_i k hk;
      convert Relation.ReflTransGen.trans _ ( rewind_loop k hk ( default :: suffix ) hblock.1 hblock.2 ) using 1;
      apply_rules [ Relation.ReflTransGen.single ];
      unfold M; simp +decide [ hblock ] ;
      unfold TM0.step; simp +decide [ Tape.mk₂ ] ;
  · simp +decide [ Tape.mk₂ ];
    unfold M; simp +decide [ Tape.mk' ] ;
    unfold TM0.step; simp +decide [ Tape.move ] ;
    ext i; simp [ListBlank.mk];
    cases i <;> simp +decide [ ListBlank.nth ]

/-! ### Full computation -/

theorem full_reaches (block suffix : List Γ)
    (hblock : ∀ y ∈ block, y ≠ default) (hsuf : ∀ y ∈ suffix, y ≠ default) :
    Reaches (TM0.step (M Γ))
      (TM0.init (block ++ default :: suffix))
      ⟨Sum.inr .rewindDone, Tape.mk₁ (block.reverse ++ default :: suffix)⟩ := by
  unfold TM0.init
  rw [← mk₂_nil_eq_mk₁, ← mk₂_nil_eq_mk₁]
  exact (iteration_loop block suffix hblock hsuf).trans (rewind_phase block suffix hblock)

theorem step_rewindDone (T : Tape Γ) :
    TM0.step (M Γ) ⟨Sum.inr .rewindDone, T⟩ = none := by
  simp [TM0.step, M]

end RevBlock