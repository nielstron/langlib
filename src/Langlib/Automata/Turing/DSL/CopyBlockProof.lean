import Mathlib
import Langlib.Automata.Turing.DSL.CopyBinaryBlock
import Langlib.Automata.Turing.DSL.ReverseBlock
import Langlib.Automata.Turing.DSL.BlockSepPrefix

/-! # Copy Block Correctness Proof -/

open Turing

namespace CopyBlock

variable {Γ : Type} [Inhabited Γ] [DecidableEq Γ] [Fintype Γ]

/-- The done state halts. -/
theorem step_done (sep2 : Γ) (T : Tape Γ) :
    TM0.step (M sep2) ⟨Sum.inr (Sum.inr NPhase.done), T⟩ = none := by
  simp [TM0.step, M]

/-! ### Generic scan loops -/

theorem generic_scan_left (sep2 : Γ) (q : CSt Γ) (h : Γ) (elems L R : List Γ)
    (hh : h ≠ default) (helems : ∀ g ∈ elems, g ≠ default)
    (h_loop : ∀ a : Γ, a ≠ default →
      M sep2 q a = some (q, TM0.Stmt.move Dir.left)) :
    Reaches (TM0.step (M sep2))
      ⟨q, Tape.mk₂ (elems ++ L) (h :: R)⟩
      ⟨q, Tape.mk₂ L (elems.reverse ++ h :: R)⟩ := by
  revert q h hh helems h_loop;
  induction' elems with elems ih generalizing L R;
  · exact fun q h hh _ _ => Relation.ReflTransGen.refl;
  · intros q h hh helems h_loop
    have h_step : Reaches (TM0.step (M sep2)) ⟨q, Tape.mk₂ (elems :: ih ++ L) (h :: R)⟩ ⟨q, Tape.mk₂ (ih ++ L) (elems :: h :: R)⟩ := by
      apply Relation.ReflTransGen.single;
      unfold TM0.step;
      simp +decide [ h_loop, hh, Tape.mk₂ ];
    rename_i ih';
    convert h_step.trans ( ih' L ( h :: R ) q elems ( helems elems ( by simp +decide ) ) ( fun g hg => helems g ( by simp +decide [ hg ] ) ) ( fun a ha => h_loop a ( by aesop ) ) ) using 1;
    simp +decide [ List.reverse_cons ]

omit [Fintype Γ] in
theorem generic_scan_right (sep2 : Γ) (q : CSt Γ) (elems L R : List Γ)
    (helems : ∀ g ∈ elems, g ≠ default)
    (h_loop : ∀ a : Γ, a ≠ default →
      M sep2 q a = some (q, TM0.Stmt.move Dir.right)) :
    Reaches (TM0.step (M sep2))
      ⟨q, Tape.mk₂ L (elems ++ R)⟩
      ⟨q, Tape.mk₂ (elems.reverse ++ L) R⟩ := by
  induction' elems with e elems ih generalizing L R q;
  · constructor;
  · specialize ih q ( e :: L ) R ; simp_all +decide;
    refine' ih.head _;
    unfold TM0.step; simp +decide [ *, Tape.mk₂ ] ;

/-! ### Phase 0 shift cascade helpers -/

/-
One step of the p0 shift cascade: write carry, pick up current element, move right.
    Two TM0 transitions: p0shW → p0shM → p0shW.
-/
theorem p0shW_step (sep2 : Γ) (c e : Γ) (L R : List Γ)
    (h : ¬(c = default ∧ e = default)) :
    Reaches (TM0.step (M sep2))
      ⟨.inr (.inl (c, .p0shW)), Tape.mk₂ L (e :: R)⟩
      ⟨.inr (.inl (e, .p0shW)), Tape.mk₂ (c :: L) R⟩ := by
  constructor;
  apply Relation.ReflTransGen.single;
  rotate_right;
  exact ⟨ Sum.inr ( Sum.inl ( e, C1Phase.p0shM ) ), Tape.mk₂ L ( c :: R ) ⟩;
  · unfold M;
    unfold TM0.step; aesop;
  · unfold M; aesop;

/-
Terminal step of the p0 cascade: carry ≠ default, head = default (from padding).
    Three TM0 transitions: p0shW(c) → write c → p0shM(default) → move right →
    p0shW(default) → terminate (both default) → rw0a, move left.
-/
theorem p0shW_end (sep2 : Γ) (c : Γ) (L : List Γ)
    (hc : c ≠ default) :
    Reaches (TM0.step (M sep2))
      ⟨.inr (.inl (c, .p0shW)), Tape.mk₂ L []⟩
      ⟨.inr (.inr .rw0a), Tape.mk₂ L [c]⟩ := by
  have h_step1 : TM0.step (M sep2) ⟨Sum.inr (Sum.inl (c, .p0shW)), Tape.mk₂ L []⟩ = some ⟨Sum.inr (Sum.inl (default, .p0shM)), Tape.mk₂ L [c]⟩ := by
    unfold M; simp +decide [ hc, Tape.mk₂ ] ;
    unfold TM0.step; simp +decide [ hc ] ;
  generalize_proofs at *; (
  have h_step2 : TM0.step (M sep2) ⟨Sum.inr (Sum.inl (default, .p0shM)), Tape.mk₂ L [c]⟩ = some ⟨Sum.inr (Sum.inl (default, .p0shW)), Tape.mk₂ (c :: L) []⟩ := by
    unfold M; simp +decide [ hc, TM0.step ] ;
    grind +suggestions
  generalize_proofs at *; (
  have h_step3 : TM0.step (M sep2) ⟨Sum.inr (Sum.inl (default, .p0shW)), Tape.mk₂ (c :: L) []⟩ = some ⟨Sum.inr (Sum.inr NPhase.rw0a), Tape.mk₂ L [c]⟩ := by
    unfold TM0.step M; simp +decide [ hc ] ;
    use TM0.Stmt.move Dir.left; simp +decide [ hc, RevBlock.mk₂_head, RevBlock.mk₂_move_left ] ;
    exact?
  generalize_proofs at *; (
  exact .trans (.single h_step1) (.trans (.single h_step2) (.single h_step3)))))

/-
Immediate termination: carry = default, head = default (from padding).
    One TM0 transition: p0shW(default) → rw0a, move left.
-/
theorem p0shW_terminate (sep2 : Γ) (x : Γ) (L : List Γ) :
    Reaches (TM0.step (M sep2))
      ⟨.inr (.inl (default, .p0shW)), Tape.mk₂ (x :: L) []⟩
      ⟨.inr (.inr .rw0a), Tape.mk₂ L [x]⟩ := by
  constructor;
  constructor;
  unfold TM0.step M;
  simp +decide [ Tape.mk₂ ]

/-
Full p0 shift cascade with carry ≠ default.
    Shifts all elements right by one, placing carry at position 0.
    By induction on elems.

    Final state: left = (carry :: elems).dropLast.reverse ++ L,
                 right = [(carry :: elems).getLast].
-/
theorem p0_cascade (sep2 : Γ) (carry : Γ) (hcarry : carry ≠ default)
    (L : List Γ) (elems : List Γ) (helems : ∀ g ∈ elems, g ≠ default) :
    Reaches (TM0.step (M sep2))
      ⟨.inr (.inl (carry, .p0shW)), Tape.mk₂ L elems⟩
      ⟨.inr (.inr .rw0a),
       Tape.mk₂ ((carry :: elems).dropLast.reverse ++ L)
                 [(carry :: elems).getLast (List.cons_ne_nil carry elems)]⟩ := by
  induction' elems with e elems ih generalizing L carry <;> simp_all +decide [ Tape.mk₂ ];
  · convert p0shW_end sep2 carry L hcarry using 1;
  · have h_step : Reaches (TM0.step (M sep2)) ⟨Sum.inr (Sum.inl (carry, C1Phase.p0shW)), Tape.mk₂ L (e :: elems)⟩ ⟨Sum.inr (Sum.inl (e, C1Phase.p0shW)), Tape.mk₂ (carry :: L) elems⟩ := by
      apply p0shW_step; simp [hcarry, helems]
    generalize_proofs at *; (
    convert h_step.trans ( ih e helems.1 ( carry :: L ) ) using 1)

/-! ### Tape boundary helpers -/

omit [DecidableEq Γ] [Fintype Γ] in
theorem mk₂_move_left_nil (sep2 : Γ) (x : Γ) (R : List Γ) :
    Tape.move Dir.left (Tape.mk₂ ([] : List Γ) (x :: R)) = Tape.mk₂ [] (default :: x :: R) := by
  simp [Tape.mk₂, Tape.mk', Tape.move]

omit [DecidableEq Γ] [Fintype Γ] in
theorem mk₂_default_left (sep2 : Γ) (R : List Γ) :
    Tape.mk₂ ([default] : List Γ) R = Tape.mk₂ [] R := by
  simp [Tape.mk₂, Tape.mk']
  apply ListBlank.ext; intro i; simp [ListBlank.nth_mk]; cases i <;> simp [List.getI, List.getD]

/-! ### Generic boundary transition (scan_left state at empty left) -/

/-
When a scan-left state reads non-default at mk₂ [] (x :: R) and moves left,
    then reads default (from padding) and transitions to a new state with move right,
    the result is the original tape mk₂ [] (x :: R).
-/
theorem boundary_transition (sep2 : Γ) (q q' : CSt Γ) (x : Γ) (R : List Γ)
    (hx : x ≠ default)
    (h_loop : M sep2 q x = some (q, TM0.Stmt.move Dir.left))
    (h_stop : M sep2 q default = some (q', TM0.Stmt.move Dir.right)) :
    Reaches (TM0.step (M sep2))
      ⟨q, Tape.mk₂ [] (x :: R)⟩
      ⟨q', Tape.mk₂ [] (x :: R)⟩ := by
  unfold Reaches;
  unfold TM0.step;
  convert Relation.ReflTransGen.trans _ _;
  exact ⟨ q, Tape.mk₂ [] ( default :: x :: R ) ⟩;
  · convert Relation.ReflTransGen.single _;
    unfold Tape.mk₂; aesop;
  · convert Relation.ReflTransGen.single _;
    simp +decide [ h_stop, Tape.mk₂ ];
    convert mk₂_default_left sep2 ( x :: R ) using 1

/-! ### Phase 0 sub-lemmas -/

/-
rw0b reads non-default head, transitions to rw0c, scans left through remaining
    block elements, then boundary_transition to grab.
-/
theorem rw0b_to_grab (sep2 : Γ) (b : Γ) (brest : List Γ) (R : List Γ)
    (hb : b ≠ default) (hbrest : ∀ g ∈ brest, g ≠ default) :
    Reaches (TM0.step (M sep2))
      ⟨.inr (.inr .rw0b), Tape.mk₂ brest (b :: R)⟩
      ⟨.inr (.inr .grab), Tape.mk₂ [] (brest.reverse ++ b :: R)⟩ := by
  by_cases h : brest = [];
  · constructor;
    rotate_right;
    exact ⟨ Sum.inr ( Sum.inr NPhase.rw0c ), Tape.mk₂ [] ( default :: b :: R ) ⟩;
    · apply_rules [ Relation.ReflTransGen.single ];
      unfold TM0.step;
      unfold M; aesop;
    · unfold M;
      unfold Tape.mk₂; simp +decide [ TM0.step ] ;
      convert mk₂_default_left sep2 ( b :: R ) using 1;
      unfold Tape.mk₂; aesop;
  · obtain ⟨x, rest, hx⟩ : ∃ x rest, brest = x :: rest := by
      exact List.exists_cons_of_ne_nil h;
    have h_scan : Reaches (TM0.step (M sep2)) ⟨Sum.inr (Sum.inr NPhase.rw0c), Tape.mk₂ rest (x :: b :: R)⟩ ⟨Sum.inr (Sum.inr NPhase.rw0c), Tape.mk₂ [] (rest.reverse ++ x :: b :: R)⟩ := by
      convert generic_scan_left sep2 ( Sum.inr ( Sum.inr NPhase.rw0c ) ) x rest [] ( b :: R ) _ _ _ using 1;
      · aesop;
      · exact hbrest x ( hx.symm ▸ List.mem_cons_self );
      · exact fun g hg => hbrest g <| hx.symm ▸ List.mem_cons_of_mem _ hg;
      · unfold M; aesop;
    have h_boundary : Reaches (TM0.step (M sep2)) ⟨Sum.inr (Sum.inr NPhase.rw0c), Tape.mk₂ [] (rest.reverse ++ x :: b :: R)⟩ ⟨Sum.inr (Sum.inr NPhase.grab), Tape.mk₂ [] (rest.reverse ++ x :: b :: R)⟩ := by
      apply boundary_transition;
      · cases h : rest.reverse <;> simp_all +decide;
      · cases h : rest.reverse <;> simp_all +decide [ M ];
      · unfold M; aesop;
    have h_step : TM0.step (M sep2) ⟨Sum.inr (Sum.inr NPhase.rw0b), Tape.mk₂ (x :: rest) (b :: R)⟩ = some ⟨Sum.inr (Sum.inr NPhase.rw0c), Tape.mk₂ rest (x :: b :: R)⟩ := by
      unfold M; simp +decide [ TM0.step ] ;
      exact ⟨ _, if_neg ( by simp +decide [ Tape.mk₂, Tape.head ] ; aesop ), by rfl ⟩;
    simp_all +decide [ Reaches ];
    grind +suggestions

omit [DecidableEq Γ] [Fintype Γ] in
/-- Trailing default equivalence for mk₂. -/
theorem mk₂_trailing_default (L : List Γ) (R : List Γ) :
    Tape.mk₂ L (R ++ [default]) = Tape.mk₂ L R := by
  -- By definition of `ListBlank.mk`, appending a default to the list does not change the ListBlank value.
  apply congr_arg (fun x => Tape.mk' (ListBlank.mk L) x) (listBlank_mk_append_default R)

/-! ### Phase 0: from start to grab -/

/-
Phase 0 part 1: from start to cascade position (p0shW default).
-/
theorem phase0_start_to_cascade (sep2 : Γ) (b : Γ) (brest : List Γ) (suffix : List Γ)
    (hb : b ≠ default) (hbrest : ∀ g ∈ brest, g ≠ default) :
    Reaches (TM0.step (M sep2))
      ⟨.inr (.inr .start), Tape.mk₂ [] (b :: brest ++ default :: suffix)⟩
      ⟨.inr (.inl (default, .p0shW)), Tape.mk₂ (default :: (brest.reverse ++ [b])) suffix⟩ := by
  have h_step1 : TM0.step (M sep2) ⟨Sum.inr (Sum.inr NPhase.start), Tape.mk₂ [] (b :: (brest ++ default :: suffix))⟩ = some ⟨Sum.inr (Sum.inr NPhase.scan0), Tape.mk₂ [b] (brest ++ default :: suffix)⟩ := by
    simp +decide [ TM0.step, M ];
    use TM0.Stmt.move Dir.right; simp +decide [ hb, Tape.mk₂ ] ;
  have h_step2 : Reaches (TM0.step (M sep2)) ⟨Sum.inr (Sum.inr NPhase.scan0), Tape.mk₂ [b] (brest ++ default :: suffix)⟩ ⟨Sum.inr (Sum.inr NPhase.scan0), Tape.mk₂ (brest.reverse ++ [b]) (default :: suffix)⟩ := by
    apply generic_scan_right;
    · assumption;
    · unfold M; aesop;
  have h_step3 : TM0.step (M sep2) ⟨Sum.inr (Sum.inr NPhase.scan0), Tape.mk₂ (brest.reverse ++ [b]) (default :: suffix)⟩ = some ⟨Sum.inr (Sum.inl (default, C1Phase.p0shW)), Tape.mk₂ (default :: brest.reverse ++ [b]) suffix⟩ := by
    unfold TM0.step M; simp +decide [ Tape.mk₂, hb, hbrest ] ;
  generalize_proofs at *;
  exact Relation.ReflTransGen.head h_step1 ( h_step2.trans ( Relation.ReflTransGen.single h_step3 ) )

/-
Phase 0 part 2: cascade + rewind for empty suffix.
-/
theorem phase0_cascade_rewind_empty (sep2 : Γ) (block : List Γ)
    (hblock : ∀ g ∈ block, g ≠ default) (hne : block ≠ []) :
    Reaches (TM0.step (M sep2))
      ⟨.inr (.inl (default, .p0shW)), Tape.mk₂ (default :: block.reverse) []⟩
      ⟨.inr (.inr .grab), Tape.mk₂ [] (block ++ [default])⟩ := by
  have h_step1 : Reaches (TM0.step (M sep2))
      ⟨.inr (.inl (default, .p0shW)), Tape.mk₂ (default :: block.reverse) []⟩
      ⟨.inr (.inr .rw0a), Tape.mk₂ block.reverse [default]⟩ := by
        exact?;
  have h_step2 : Reaches (TM0.step (M sep2))
      ⟨.inr (.inr .rw0a), Tape.mk₂ block.reverse [default]⟩
      ⟨.inr (.inr .rw0b), Tape.mk₂ (block.reverse.tail) [block.reverse.head!, default]⟩ := by
        cases h : block.reverse <;> simp_all +decide [ Tape.mk₂ ];
        convert Relation.ReflTransGen.single _;
        unfold M; simp +decide [ TM0.step ] ;
  have h_step3 : Reaches (TM0.step (M sep2))
      ⟨.inr (.inr .rw0b), Tape.mk₂ block.reverse.tail [block.reverse.head!, default]⟩
      ⟨.inr (.inr .grab), Tape.mk₂ [] (block.reverse.reverse ++ [default])⟩ := by
        convert rw0b_to_grab sep2 _ _ _ _ _ using 1;
        · cases h : block.reverse <;> aesop;
        · cases h : block.reverse <;> aesop;
        · exact fun g hg => hblock g <| List.mem_reverse.mp <| List.mem_of_mem_tail hg;
  simpa using h_step1.trans ( h_step2.trans h_step3 )

/-
Rewind rw0a through suffix back to block boundary, then through to grab.
    From rw0a with suffix on the right and two defaults + block.reverse on the left,
    rewind to grab at position 0.
-/
theorem phase0_rw0a_to_grab (sep2 : Γ) (block : List Γ) (s : Γ) (srest : List Γ)
    (hblock : ∀ g ∈ block, g ≠ default) (hne : block ≠ [])
    (hs : s ≠ default) (hsrest : ∀ g ∈ srest, g ≠ default) :
    Reaches (TM0.step (M sep2))
      ⟨.inr (.inr .rw0a), Tape.mk₂ (default :: default :: block.reverse) (s :: srest)⟩
      ⟨.inr (.inr .grab), Tape.mk₂ [] (block ++ default :: default :: s :: srest)⟩ := by
  obtain ⟨br, brest, hbr, hbrest⟩ : ∃ br brest, block.reverse = br :: brest ∧ br ≠ default ∧ ∀ g ∈ brest, g ≠ default := by
    cases h : block.reverse <;> aesop;
  have h_step1 : Reaches (TM0.step (M sep2)) ⟨.inr (.inr .rw0a), Tape.mk₂ (default :: default :: block.reverse) (s :: srest)⟩ ⟨.inr (.inr .rw0a), Tape.mk₂ (default :: block.reverse) (default :: s :: srest)⟩ := by
    convert Relation.ReflTransGen.single _ using 1;
    unfold M; simp +decide [ TM0.step ] ;
    use TM0.Stmt.move Dir.left; simp +decide [ Tape.mk₂ ] ;
    exact hs;
  have h_step2 : Reaches (TM0.step (M sep2)) ⟨.inr (.inr .rw0a), Tape.mk₂ (default :: block.reverse) (default :: s :: srest)⟩ ⟨.inr (.inr .rw0b), Tape.mk₂ block.reverse (default :: default :: s :: srest)⟩ := by
    apply Relation.ReflTransGen.single;
    unfold TM0.step;
    unfold M; simp +decide [ hbr, hbrest ] ;
    exact ⟨ _, if_pos ( by rfl ), by rfl ⟩;
  have h_step3 : Reaches (TM0.step (M sep2)) ⟨.inr (.inr .rw0b), Tape.mk₂ block.reverse (default :: default :: s :: srest)⟩ ⟨.inr (.inr .rw0b), Tape.mk₂ brest (br :: default :: default :: s :: srest)⟩ := by
    convert Relation.ReflTransGen.single _ using 1;
    unfold M; simp +decide [ hbr ] ;
    unfold TM0.step; simp +decide [ Tape.mk₂ ] ;
  have h_step4 : Reaches (TM0.step (M sep2)) ⟨.inr (.inr .rw0b), Tape.mk₂ brest (br :: default :: default :: s :: srest)⟩ ⟨.inr (.inr .grab), Tape.mk₂ [] (brest.reverse ++ br :: default :: default :: s :: srest)⟩ := by
    apply rw0b_to_grab;
    · exact hbrest.1;
    · exact hbrest.2;
  convert h_step1.trans ( h_step2.trans ( h_step3.trans h_step4 ) ) using 1;
  rw [ show block = brest.reverse ++ [ br ] by rw [ ← List.reverse_inj ] ; aesop ] ; simp +decide [ List.reverse_append ]

/-
Phase 0 part 2: cascade + rewind for non-empty suffix.
-/
theorem phase0_cascade_rewind_nonempty (sep2 : Γ) (block : List Γ) (s : Γ) (srest : List Γ)
    (hblock : ∀ g ∈ block, g ≠ default) (hne : block ≠ [])
    (hs : s ≠ default) (hsrest : ∀ g ∈ srest, g ≠ default) :
    Reaches (TM0.step (M sep2))
      ⟨.inr (.inl (default, .p0shW)), Tape.mk₂ (default :: block.reverse) (s :: srest)⟩
      ⟨.inr (.inr .grab), Tape.mk₂ [] (block ++ default :: default :: s :: srest)⟩ := by
  have h_step1 : Reaches (TM0.step (M sep2))
    ⟨Sum.inr (Sum.inl (default, C1Phase.p0shW)), Tape.mk₂ (default :: block.reverse) (s :: srest)⟩
    ⟨Sum.inr (Sum.inl (s, C1Phase.p0shW)), Tape.mk₂ (default :: default :: block.reverse) srest⟩ := by
      convert p0shW_step sep2 default s ( default :: block.reverse ) srest _ using 1;
      aesop;
  have h_step2 := p0_cascade sep2 s hs ( default :: default :: block.reverse ) srest hsrest;
  have h_step3 := generic_scan_left sep2 ( Sum.inr ( Sum.inr NPhase.rw0a ) ) ( ( s :: srest ).getLast ( List.cons_ne_nil s srest ) ) ( ( s :: srest ).dropLast.reverse ) ( default :: default :: block.reverse ) [ ] ( by
    grind ) ( by
    simp +zetaDelta at *;
    exact fun g hg => by have := List.mem_of_mem_dropLast hg; aesop; ) ( by
    unfold M; aesop; );
  convert h_step1.trans ( h_step2.trans ( h_step3.trans _ ) ) using 1;
  convert phase0_rw0a_to_grab sep2 block s srest hblock hne hs hsrest using 1;
  simp +decide [ List.dropLast_append_getLast ]

/-
Full Phase 0 for non-empty blocks.
-/
theorem phase0_reaches (sep2 : Γ) (block suffix : List Γ)
    (hblock : ∀ g ∈ block, g ≠ default)
    (hne : block ≠ [])
    (hsuffix : ∀ g ∈ suffix, g ≠ default) :
    Reaches (TM0.step (M sep2))
      ⟨Sum.inr (Sum.inr NPhase.start),
       Tape.mk₁ (block ++ default :: suffix)⟩
      ⟨Sum.inr (Sum.inr NPhase.grab),
       Tape.mk₂ [] (block ++ default :: default :: suffix)⟩ := by
  induction' suffix with s suffix ih generalizing block;
  · have h_reach : Reaches (TM0.step (M sep2)) ⟨.inr (.inr .start), Tape.mk₁ (block ++ [default])⟩ ⟨.inr (.inl (default, .p0shW)), Tape.mk₂ (default :: block.reverse) []⟩ := by
      obtain ⟨b, brest, rfl⟩ : ∃ b brest, block = b :: brest := by
        exact List.exists_cons_of_ne_nil hne;
      convert phase0_start_to_cascade sep2 b brest [] ( hblock b ( by simp +decide ) ) ( fun g hg => hblock g ( by simp +decide [ hg ] ) ) using 1;
      simp +decide [ List.reverse_cons ];
    convert h_reach.trans _;
    convert phase0_cascade_rewind_empty sep2 block hblock hne using 1;
    simp +decide [ Tape.mk₂ ];
    grind +suggestions;
  · have h_step : Reaches (TM0.step (M sep2)) ⟨.inr (.inr NPhase.start), Tape.mk₁ (block ++ default :: s :: suffix)⟩ ⟨.inr (.inl (default, .p0shW)), Tape.mk₂ (default :: block.reverse) (s :: suffix)⟩ := by
      rcases block with ( _ | ⟨ b, block ⟩ ) <;> simp_all +decide [ Tape.mk₁ ];
      convert phase0_start_to_cascade sep2 b block ( s :: suffix ) hblock.1 hblock.2 using 1;
    exact h_step.trans ( phase0_cascade_rewind_nonempty sep2 block s suffix hblock hne ( hsuffix s ( by simp +decide ) ) ( fun g hg => hsuffix g ( by simp +decide [ hg ] ) ) )

/-! ### Copy loop shift cascade helpers -/

/-
One step of the copy-loop shift cascade (shW/shM in Sum.inl).
    Two TM0 transitions.
-/
theorem shW_step (sep2 : Γ) (s c e : Γ) (L R : List Γ)
    (h : ¬(c = default ∧ e = default)) :
    Reaches (TM0.step (M sep2))
      ⟨.inl (s, c, .shW), Tape.mk₂ L (e :: R)⟩
      ⟨.inl (s, e, .shW), Tape.mk₂ (c :: L) R⟩ := by
  have h_step : TM0.step (M sep2) ⟨Sum.inl (s, c, C2Phase.shW), Tape.mk₂ L (e :: R)⟩ = some ⟨Sum.inl (s, e, C2Phase.shM), Tape.mk₂ L (c :: R)⟩ := by
    unfold M;
    unfold TM0.step; aesop;
  have h_step2 : TM0.step (M sep2) ⟨Sum.inl (s, e, C2Phase.shM), Tape.mk₂ L (c :: R)⟩ = some ⟨Sum.inl (s, e, C2Phase.shW), Tape.mk₂ (c :: L) R⟩ := by
    -- By definition of `M`, we know that `M sep2` transitions from `shM(s,e)` to `shW(s,e)` when the head is `c`.
    simp [TM0.step, M];
    -- Apply the definition of Tape.move to the tape mk₂ L (c :: R).
    apply RevBlock.mk₂_move_right;
  exact Relation.ReflTransGen.head h_step ( Relation.ReflTransGen.head h_step2 ( Relation.ReflTransGen.refl ) )

/-
Terminal step of the copy-loop cascade.
    When carry ≠ default and head = default.
-/
theorem shW_end (sep2 : Γ) (s c : Γ) (L : List Γ)
    (hc : c ≠ default) :
    Reaches (TM0.step (M sep2))
      ⟨.inl (s, c, .shW), Tape.mk₂ L []⟩
      ⟨.inr (.inl (s, .ret1)), Tape.mk₂ L [c]⟩ := by
  -- First, apply `shW_step` to get the new state `shW(s,default)` with the tape `mk₂ (c :: L) []`.
  have h1 : Reaches (TM0.step (M sep2)) ⟨.inl (s, c, .shW), Tape.mk₂ L []⟩ ⟨.inl (s, default, .shW), Tape.mk₂ (c :: L) []⟩ := by
    convert shW_step sep2 s c default L [] _ using 1;
    aesop;
  refine' h1.trans _;
  unfold M;
  convert Relation.ReflTransGen.single _;
  unfold TM0.step; simp +decide [ Tape.mk₂ ] ;

/-
Immediate termination of copy-loop cascade (carry=default, head=default).
-/
theorem shW_terminate (sep2 : Γ) (s x : Γ) (L : List Γ) :
    Reaches (TM0.step (M sep2))
      ⟨.inl (s, default, .shW), Tape.mk₂ (x :: L) []⟩
      ⟨.inr (.inl (s, .ret1)), Tape.mk₂ L [x]⟩ := by
  have h_shW_step : TM0.step (M sep2) ⟨.inl (s, default, .shW), Tape.mk₂ (x :: L) []⟩ = some ⟨.inr (.inl (s, .ret1)), Tape.mk₂ L [x]⟩ := by
    unfold M;
    simp +decide [ TM0.step, Tape.mk₂ ];
  exact Relation.ReflTransGen.single h_shW_step

/-
Full copy-loop shift cascade.
-/
theorem sh_cascade (sep2 : Γ) (s carry : Γ) (hcarry : carry ≠ default)
    (L : List Γ) (elems : List Γ) (helems : ∀ g ∈ elems, g ≠ default) :
    Reaches (TM0.step (M sep2))
      ⟨.inl (s, carry, .shW), Tape.mk₂ L elems⟩
      ⟨.inr (.inl (s, .ret1)),
       Tape.mk₂ ((carry :: elems).dropLast.reverse ++ L)
                 [(carry :: elems).getLast (List.cons_ne_nil carry elems)]⟩ := by
  induction' elems with e elems ih generalizing L carry;
  · simpa using shW_end sep2 s carry L hcarry
  · have h_step : Reaches (TM0.step (M sep2)) ⟨Sum.inl (s, carry, .shW), Tape.mk₂ L (e :: elems)⟩ ⟨Sum.inl (s, e, .shW), Tape.mk₂ (carry :: L) elems⟩ := by
      apply shW_step;
      tauto;
    convert h_step.trans ( ih e ( helems e ( by simp +decide ) ) ( carry :: L ) ( fun g hg => helems g ( by simp +decide [ hg ] ) ) ) using 1;
    simp +decide [ List.dropLast, List.getLast ]

/-! ### One Copy Iteration -/

/-- Phase 1a: from grab to the shift cascade start (after pasting x). -/
theorem grab_to_shW (sep2 : Γ) (x : Γ) (rest copied L : List Γ)
    (suffix : List Γ)
    (hx : x ≠ default)
    (hrest : ∀ g ∈ rest, g ≠ default)
    (hcopied : ∀ g ∈ copied, g ≠ default) :
    Reaches (TM0.step (M sep2))
      ⟨.inr (.inr .grab), Tape.mk₂ L (x :: rest ++ default :: copied ++ default :: suffix)⟩
      ⟨.inl (x, default, .shW0),
       Tape.mk₂ (x :: copied.reverse ++ default :: rest.reverse ++ default :: L) suffix⟩ := by
  have h_grab : TM0.step (M sep2)
      ⟨.inr (.inr .grab),
       Tape.mk₂ L (x :: rest ++ default :: copied ++ default :: suffix)⟩ =
      some ⟨.inr (.inl (x, .markMv)),
       Tape.mk₂ L (default :: rest ++ default :: copied ++ default :: suffix)⟩ := by
    unfold TM0.step M
    simp +decide [hx, Tape.mk₂]
  have h_mark : TM0.step (M sep2)
      ⟨.inr (.inl (x, .markMv)),
       Tape.mk₂ L (default :: rest ++ default :: copied ++ default :: suffix)⟩ =
      some ⟨.inr (.inl (x, .scanR)),
       Tape.mk₂ (default :: L) (rest ++ default :: copied ++ default :: suffix)⟩ := by
    unfold TM0.step M
    simp +decide [Tape.mk₂]
  have h_scanR : Reaches (TM0.step (M sep2))
      ⟨.inr (.inl (x, .scanR)),
       Tape.mk₂ (default :: L) (rest ++ default :: copied ++ default :: suffix)⟩
      ⟨.inr (.inl (x, .scanR)),
       Tape.mk₂ (rest.reverse ++ default :: L) (default :: copied ++ default :: suffix)⟩ := by
    simpa [List.append_assoc] using
      generic_scan_right sep2 (.inr (.inl (x, .scanR))) rest (default :: L)
      (default :: copied ++ default :: suffix) hrest (by
        intro a ha
        unfold M
        simp +decide [ha])
  have h_cross : TM0.step (M sep2)
      ⟨.inr (.inl (x, .scanR)),
       Tape.mk₂ (rest.reverse ++ default :: L) (default :: copied ++ default :: suffix)⟩ =
      some ⟨.inr (.inl (x, .scanR2)),
       Tape.mk₂ (default :: rest.reverse ++ default :: L) (copied ++ default :: suffix)⟩ := by
    unfold TM0.step M
    simp +decide [Tape.mk₂]
  have h_scanR2 : Reaches (TM0.step (M sep2))
      ⟨.inr (.inl (x, .scanR2)),
       Tape.mk₂ (default :: rest.reverse ++ default :: L) (copied ++ default :: suffix)⟩
      ⟨.inr (.inl (x, .scanR2)),
       Tape.mk₂ (copied.reverse ++ default :: rest.reverse ++ default :: L)
         (default :: suffix)⟩ := by
    simpa [List.append_assoc] using
      generic_scan_right sep2 (.inr (.inl (x, .scanR2))) copied
      (default :: rest.reverse ++ default :: L) (default :: suffix) hcopied (by
        intro a ha
        unfold M
        simp +decide [ha])
  have h_write : TM0.step (M sep2)
      ⟨.inr (.inl (x, .scanR2)),
       Tape.mk₂ (copied.reverse ++ default :: rest.reverse ++ default :: L)
         (default :: suffix)⟩ =
      some ⟨.inl (x, default, .shM0),
       Tape.mk₂ (copied.reverse ++ default :: rest.reverse ++ default :: L)
         (x :: suffix)⟩ := by
    unfold TM0.step M
    simp +decide [Tape.mk₂]
  have h_move : TM0.step (M sep2)
      ⟨.inl (x, default, .shM0),
       Tape.mk₂ (copied.reverse ++ default :: rest.reverse ++ default :: L)
         (x :: suffix)⟩ =
      some ⟨.inl (x, default, .shW0),
       Tape.mk₂ (x :: copied.reverse ++ default :: rest.reverse ++ default :: L)
         suffix⟩ := by
    unfold TM0.step M
    simp +decide [Tape.mk₂]
  exact Relation.ReflTransGen.head h_grab
    (Relation.ReflTransGen.head h_mark
      (h_scanR.trans
        (Relation.ReflTransGen.head h_cross
      (h_scanR2.trans
            (Relation.ReflTransGen.head h_write
              (Relation.ReflTransGen.single h_move))))))

theorem ret3_scan_restore (sep2 : Γ) (x cur : Γ) (leftRest L R : List Γ)
    (hcur : cur ≠ default)
    (hleftRest : ∀ g ∈ leftRest, g ≠ default) :
    Reaches (TM0.step (M sep2))
      ⟨.inr (.inl (x, .ret3)), Tape.mk₂ (leftRest ++ default :: L) (cur :: R)⟩
      ⟨.inr (.inr .grab), Tape.mk₂ (x :: L) (leftRest.reverse ++ cur :: R)⟩ := by
  induction' leftRest with a leftRest ih generalizing cur R
  · have h_move : TM0.step (M sep2)
        ⟨.inr (.inl (x, .ret3)), Tape.mk₂ (default :: L) (cur :: R)⟩ =
        some ⟨.inr (.inl (x, .ret3)), Tape.mk₂ L (default :: cur :: R)⟩ := by
      unfold TM0.step M
      simp +decide [hcur, Tape.mk₂]
    have h_write : TM0.step (M sep2)
        ⟨.inr (.inl (x, .ret3)), Tape.mk₂ L (default :: cur :: R)⟩ =
        some ⟨.inr (.inr .adv), Tape.mk₂ L (x :: cur :: R)⟩ := by
      unfold TM0.step M
      simp +decide [Tape.mk₂]
    have h_adv : TM0.step (M sep2)
        ⟨.inr (.inr .adv), Tape.mk₂ L (x :: cur :: R)⟩ =
        some ⟨.inr (.inr .grab), Tape.mk₂ (x :: L) (cur :: R)⟩ := by
      unfold TM0.step M
      simp +decide [Tape.mk₂]
    have h_move_reaches : Reaches (TM0.step (M sep2))
        ⟨.inr (.inl (x, .ret3)), Tape.mk₂ (default :: L) (cur :: R)⟩
        ⟨.inr (.inl (x, .ret3)), Tape.mk₂ L (default :: cur :: R)⟩ :=
      Relation.ReflTransGen.single h_move
    have h_write_reaches : Reaches (TM0.step (M sep2))
        ⟨.inr (.inl (x, .ret3)), Tape.mk₂ L (default :: cur :: R)⟩
        ⟨.inr (.inr .adv), Tape.mk₂ L (x :: cur :: R)⟩ :=
      Relation.ReflTransGen.single h_write
    have h_adv_reaches : Reaches (TM0.step (M sep2))
        ⟨.inr (.inr .adv), Tape.mk₂ L (x :: cur :: R)⟩
        ⟨.inr (.inr .grab), Tape.mk₂ (x :: L) (cur :: R)⟩ :=
      Relation.ReflTransGen.single h_adv
    simpa using
      h_move_reaches.trans (h_write_reaches.trans h_adv_reaches)
  · have ha : a ≠ default := hleftRest a (by simp)
    have htail : ∀ g ∈ leftRest, g ≠ default := by
      intro g hg
      exact hleftRest g (by simp [hg])
    have h_move : TM0.step (M sep2)
        ⟨.inr (.inl (x, .ret3)),
         Tape.mk₂ (a :: leftRest ++ default :: L) (cur :: R)⟩ =
        some ⟨.inr (.inl (x, .ret3)),
         Tape.mk₂ (leftRest ++ default :: L) (a :: cur :: R)⟩ := by
      unfold TM0.step M
      simp +decide [hcur, Tape.mk₂]
    have hrec := ih a (cur :: R) ha htail
    have h_move_reaches : Reaches (TM0.step (M sep2))
        ⟨.inr (.inl (x, .ret3)),
         Tape.mk₂ (a :: leftRest ++ default :: L) (cur :: R)⟩
        ⟨.inr (.inl (x, .ret3)),
         Tape.mk₂ (leftRest ++ default :: L) (a :: cur :: R)⟩ :=
      Relation.ReflTransGen.single h_move
    convert h_move_reaches.trans hrec using 1
    simp [List.append_assoc]

theorem generic_scan_left_to_default (sep2 : Γ) (q : CSt Γ) (h : Γ)
    (elems L R : List Γ)
    (hh : h ≠ default)
    (helems : ∀ g ∈ elems, g ≠ default)
    (h_loop : ∀ a : Γ, a ≠ default →
      M sep2 q a = some (q, TM0.Stmt.move Dir.left)) :
    Reaches (TM0.step (M sep2))
      ⟨q, Tape.mk₂ (elems ++ default :: L) (h :: R)⟩
      ⟨q, Tape.mk₂ L (default :: elems.reverse ++ h :: R)⟩ := by
  induction' elems with a elems ih generalizing h R
  · have h_step : TM0.step (M sep2)
        ⟨q, Tape.mk₂ (default :: L) (h :: R)⟩ =
        some ⟨q, Tape.mk₂ L (default :: h :: R)⟩ := by
      unfold TM0.step
      simp +decide [h_loop h hh, Tape.mk₂]
    exact Relation.ReflTransGen.single h_step
  · have ha : a ≠ default := helems a (by simp)
    have htail : ∀ g ∈ elems, g ≠ default := by
      intro g hg
      exact helems g (by simp [hg])
    have h_step : TM0.step (M sep2)
        ⟨q, Tape.mk₂ (a :: elems ++ default :: L) (h :: R)⟩ =
        some ⟨q, Tape.mk₂ (elems ++ default :: L) (a :: h :: R)⟩ := by
      unfold TM0.step
      simp +decide [h_loop h hh, Tape.mk₂]
    have hrec := ih a (h :: R) ha htail
    have h_step_reaches : Reaches (TM0.step (M sep2))
        ⟨q, Tape.mk₂ (a :: elems ++ default :: L) (h :: R)⟩
        ⟨q, Tape.mk₂ (elems ++ default :: L) (a :: h :: R)⟩ :=
      Relation.ReflTransGen.single h_step
    convert h_step_reaches.trans hrec using 1
    simp [List.append_assoc]

theorem ret2b_scan_restore (sep2 : Γ) (x cur : Γ) (leftRest L R : List Γ)
    (hcur : cur ≠ default)
    (hleftRest : ∀ g ∈ leftRest, g ≠ default) :
    Reaches (TM0.step (M sep2))
      ⟨.inr (.inl (x, .ret2b)), Tape.mk₂ (leftRest ++ default :: L) (cur :: R)⟩
      ⟨.inr (.inr .grab), Tape.mk₂ (x :: L) (leftRest.reverse ++ cur :: R)⟩ := by
  induction' leftRest with a leftRest ih generalizing cur R
  · have h_move : TM0.step (M sep2)
        ⟨.inr (.inl (x, .ret2b)), Tape.mk₂ (default :: L) (cur :: R)⟩ =
        some ⟨.inr (.inl (x, .ret2b)), Tape.mk₂ L (default :: cur :: R)⟩ := by
      unfold TM0.step M
      simp +decide [hcur, Tape.mk₂]
    have h_write : TM0.step (M sep2)
        ⟨.inr (.inl (x, .ret2b)), Tape.mk₂ L (default :: cur :: R)⟩ =
        some ⟨.inr (.inr .adv), Tape.mk₂ L (x :: cur :: R)⟩ := by
      unfold TM0.step M
      simp +decide [Tape.mk₂]
    have h_adv : TM0.step (M sep2)
        ⟨.inr (.inr .adv), Tape.mk₂ L (x :: cur :: R)⟩ =
        some ⟨.inr (.inr .grab), Tape.mk₂ (x :: L) (cur :: R)⟩ := by
      unfold TM0.step M
      simp +decide [Tape.mk₂]
    have h_move_reaches : Reaches (TM0.step (M sep2))
        ⟨.inr (.inl (x, .ret2b)), Tape.mk₂ (default :: L) (cur :: R)⟩
        ⟨.inr (.inl (x, .ret2b)), Tape.mk₂ L (default :: cur :: R)⟩ :=
      Relation.ReflTransGen.single h_move
    have h_write_reaches : Reaches (TM0.step (M sep2))
        ⟨.inr (.inl (x, .ret2b)), Tape.mk₂ L (default :: cur :: R)⟩
        ⟨.inr (.inr .adv), Tape.mk₂ L (x :: cur :: R)⟩ :=
      Relation.ReflTransGen.single h_write
    have h_adv_reaches : Reaches (TM0.step (M sep2))
        ⟨.inr (.inr .adv), Tape.mk₂ L (x :: cur :: R)⟩
        ⟨.inr (.inr .grab), Tape.mk₂ (x :: L) (cur :: R)⟩ :=
      Relation.ReflTransGen.single h_adv
    exact h_move_reaches.trans (h_write_reaches.trans h_adv_reaches)
  · have ha : a ≠ default := hleftRest a (by simp)
    have htail : ∀ g ∈ leftRest, g ≠ default := by
      intro g hg
      exact hleftRest g (by simp [hg])
    have h_move : TM0.step (M sep2)
        ⟨.inr (.inl (x, .ret2b)),
         Tape.mk₂ (a :: leftRest ++ default :: L) (cur :: R)⟩ =
        some ⟨.inr (.inl (x, .ret2b)),
         Tape.mk₂ (leftRest ++ default :: L) (a :: cur :: R)⟩ := by
      unfold TM0.step M
      simp +decide [hcur, Tape.mk₂]
    have hrec := ih a (cur :: R) ha htail
    have h_move_reaches : Reaches (TM0.step (M sep2))
        ⟨.inr (.inl (x, .ret2b)),
         Tape.mk₂ (a :: leftRest ++ default :: L) (cur :: R)⟩
        ⟨.inr (.inl (x, .ret2b)),
         Tape.mk₂ (leftRest ++ default :: L) (a :: cur :: R)⟩ :=
      Relation.ReflTransGen.single h_move
    convert h_move_reaches.trans hrec using 1
    simp [List.append_assoc]

theorem ret2_to_grab (sep2 : Γ) (x : Γ) (rest copied L suffix : List Γ)
    (hx : x ≠ default)
    (hrest : ∀ g ∈ rest, g ≠ default)
    (hcopied : ∀ g ∈ copied, g ≠ default) :
    Reaches (TM0.step (M sep2))
      ⟨.inr (.inl (x, .ret2)),
       Tape.mk₂ (copied.reverse ++ default :: rest.reverse ++ default :: L)
                 (x :: default :: suffix)⟩
      ⟨.inr (.inr .grab),
       Tape.mk₂ (x :: L) (rest ++ default :: copied ++ [x] ++ default :: suffix)⟩ := by
  have hcopied_rev : ∀ g ∈ copied.reverse, g ≠ default := by
    intro g hg
    exact hcopied g (List.mem_reverse.mp hg)
  have h_scan_copy : Reaches (TM0.step (M sep2))
      ⟨.inr (.inl (x, .ret2)),
       Tape.mk₂ (copied.reverse ++ default :: rest.reverse ++ default :: L)
         (x :: default :: suffix)⟩
      ⟨.inr (.inl (x, .ret2)),
       Tape.mk₂ (rest.reverse ++ default :: L)
         (default :: copied ++ x :: default :: suffix)⟩ := by
    simpa [List.append_assoc] using
      generic_scan_left_to_default sep2 (.inr (.inl (x, .ret2))) x copied.reverse
        (rest.reverse ++ default :: L) (default :: suffix) hx hcopied_rev (by
          intro a ha
          unfold M
          simp +decide [ha])
  by_cases hrest_cases : rest.reverse = []
  · have hrest_nil : rest = [] := by
      simpa using congrArg List.reverse hrest_cases
    subst rest
    have h_cross : TM0.step (M sep2)
        ⟨.inr (.inl (x, .ret2)),
         Tape.mk₂ (default :: L) (default :: copied ++ x :: default :: suffix)⟩ =
        some ⟨.inr (.inl (x, .ret2b)),
         Tape.mk₂ L (default :: default :: copied ++ x :: default :: suffix)⟩ := by
      unfold TM0.step M
      simp +decide [Tape.mk₂]
    have h_write : TM0.step (M sep2)
        ⟨.inr (.inl (x, .ret2b)),
         Tape.mk₂ L (default :: default :: copied ++ x :: default :: suffix)⟩ =
        some ⟨.inr (.inr .adv),
         Tape.mk₂ L (x :: default :: copied ++ x :: default :: suffix)⟩ := by
      unfold TM0.step M
      simp +decide [Tape.mk₂]
    have h_adv : TM0.step (M sep2)
        ⟨.inr (.inr .adv),
         Tape.mk₂ L (x :: default :: copied ++ x :: default :: suffix)⟩ =
        some ⟨.inr (.inr .grab),
         Tape.mk₂ (x :: L) (default :: copied ++ x :: default :: suffix)⟩ := by
      unfold TM0.step M
      simp +decide [Tape.mk₂]
    have h_cross_reaches : Reaches (TM0.step (M sep2))
        ⟨.inr (.inl (x, .ret2)),
         Tape.mk₂ (default :: L) (default :: copied ++ x :: default :: suffix)⟩
        ⟨.inr (.inl (x, .ret2b)),
         Tape.mk₂ L (default :: default :: copied ++ x :: default :: suffix)⟩ :=
      Relation.ReflTransGen.single h_cross
    have h_write_reaches : Reaches (TM0.step (M sep2))
        ⟨.inr (.inl (x, .ret2b)),
         Tape.mk₂ L (default :: default :: copied ++ x :: default :: suffix)⟩
        ⟨.inr (.inr .adv),
         Tape.mk₂ L (x :: default :: copied ++ x :: default :: suffix)⟩ :=
      Relation.ReflTransGen.single h_write
    have h_adv_reaches : Reaches (TM0.step (M sep2))
        ⟨.inr (.inr .adv),
         Tape.mk₂ L (x :: default :: copied ++ x :: default :: suffix)⟩
        ⟨.inr (.inr .grab),
         Tape.mk₂ (x :: L) (default :: copied ++ x :: default :: suffix)⟩ :=
      Relation.ReflTransGen.single h_adv
    convert h_scan_copy.trans
      (h_cross_reaches.trans (h_write_reaches.trans h_adv_reaches)) using 1 <;>
      simp [List.append_assoc]
  · obtain ⟨cur, leftRest, hrev⟩ : ∃ cur leftRest, rest.reverse = cur :: leftRest :=
      List.exists_cons_of_ne_nil hrest_cases
    have hrest_eq : rest = leftRest.reverse ++ [cur] := by
      calc
        rest = (rest.reverse).reverse := by simp
        _ = (cur :: leftRest).reverse := by rw [hrev]
        _ = leftRest.reverse ++ [cur] := by simp
    have hcur : cur ≠ default := by
      exact hrest cur (by rw [hrest_eq]; simp)
    have hleftRest : ∀ g ∈ leftRest, g ≠ default := by
      intro g hg
      exact hrest g (by rw [hrest_eq]; simp [hg])
    have h_cross : TM0.step (M sep2)
        ⟨.inr (.inl (x, .ret2)),
         Tape.mk₂ (rest.reverse ++ default :: L)
           (default :: copied ++ x :: default :: suffix)⟩ =
        some ⟨.inr (.inl (x, .ret2b)),
         Tape.mk₂ (leftRest ++ default :: L)
           (cur :: default :: copied ++ x :: default :: suffix)⟩ := by
      rw [hrev]
      unfold TM0.step M
      simp +decide [Tape.mk₂]
    have h_restore := ret2b_scan_restore sep2 x cur leftRest L
      (default :: copied ++ x :: default :: suffix) hcur hleftRest
    have h_cross_reaches : Reaches (TM0.step (M sep2))
        ⟨.inr (.inl (x, .ret2)),
         Tape.mk₂ (rest.reverse ++ default :: L)
           (default :: copied ++ x :: default :: suffix)⟩
        ⟨.inr (.inl (x, .ret2b)),
         Tape.mk₂ (leftRest ++ default :: L)
           (cur :: default :: copied ++ x :: default :: suffix)⟩ :=
      Relation.ReflTransGen.single h_cross
    convert h_scan_copy.trans (h_cross_reaches.trans h_restore) using 1 <;>
      simp [hrest_eq, List.append_assoc]

theorem shW0_suffix_to_ret2 (sep2 : Γ) (x : Γ) (A suffix : List Γ)
    (hsuffix : ∀ g ∈ suffix, g ≠ default) :
    Reaches (TM0.step (M sep2))
      ⟨.inl (x, default, .shW0), Tape.mk₂ (x :: A) suffix⟩
      ⟨.inr (.inl (x, .ret2)), Tape.mk₂ A (x :: default :: suffix)⟩ := by
  cases suffix with
  | nil =>
    have h_start : TM0.step (M sep2)
        ⟨.inl (x, default, .shW0), Tape.mk₂ (x :: A) []⟩ =
        some ⟨.inr (.inl (x, .ret1)), Tape.mk₂ (x :: A) [default]⟩ := by
      unfold TM0.step M
      simp +decide [Tape.mk₂]
    have h_ret1 : TM0.step (M sep2)
        ⟨.inr (.inl (x, .ret1)), Tape.mk₂ (x :: A) [default]⟩ =
        some ⟨.inr (.inl (x, .ret2)), Tape.mk₂ A [x, default]⟩ := by
      unfold TM0.step M
      simp +decide [Tape.mk₂]
    have h_start_reaches : Reaches (TM0.step (M sep2))
        ⟨.inl (x, default, .shW0), Tape.mk₂ (x :: A) []⟩
        ⟨.inr (.inl (x, .ret1)), Tape.mk₂ (x :: A) [default]⟩ :=
      Relation.ReflTransGen.single h_start
    have h_ret1_reaches : Reaches (TM0.step (M sep2))
        ⟨.inr (.inl (x, .ret1)), Tape.mk₂ (x :: A) [default]⟩
        ⟨.inr (.inl (x, .ret2)), Tape.mk₂ A [x, default]⟩ :=
      Relation.ReflTransGen.single h_ret1
    simpa using h_start_reaches.trans h_ret1_reaches
  | cons s ss =>
    have hs : s ≠ default := hsuffix s (by simp)
    have hss : ∀ g ∈ ss, g ≠ default := by
      intro g hg
      exact hsuffix g (by simp [hg])
    have h_start : TM0.step (M sep2)
        ⟨.inl (x, default, .shW0), Tape.mk₂ (x :: A) (s :: ss)⟩ =
        some ⟨.inl (x, s, .shM), Tape.mk₂ (x :: A) (default :: ss)⟩ := by
      unfold TM0.step M
      simp +decide [hs, Tape.mk₂]
    have h_move : TM0.step (M sep2)
        ⟨.inl (x, s, .shM), Tape.mk₂ (x :: A) (default :: ss)⟩ =
        some ⟨.inl (x, s, .shW), Tape.mk₂ (default :: x :: A) ss⟩ := by
      unfold TM0.step M
      simp +decide [Tape.mk₂]
    have h_cascade := sh_cascade sep2 x s hs (default :: x :: A) ss hss
    have h_suffix_ne : (s :: ss).getLast (List.cons_ne_nil s ss) ≠ default :=
      hsuffix ((s :: ss).getLast (List.cons_ne_nil s ss))
        (List.getLast_mem (l := s :: ss) (List.cons_ne_nil s ss))
    have h_drop_ne : ∀ g ∈ (s :: ss).dropLast.reverse, g ≠ default := by
      intro g hg
      exact hsuffix g (by
        exact List.mem_of_mem_dropLast (List.mem_reverse.mp hg))
    have h_scan : Reaches (TM0.step (M sep2))
        ⟨.inr (.inl (x, .ret1)),
         Tape.mk₂ ((s :: ss).dropLast.reverse ++ default :: x :: A)
           [(s :: ss).getLast (List.cons_ne_nil s ss)]⟩
        ⟨.inr (.inl (x, .ret1)),
         Tape.mk₂ (x :: A) (default :: s :: ss)⟩ := by
      have h := generic_scan_left_to_default sep2 (.inr (.inl (x, .ret1)))
        ((s :: ss).getLast (List.cons_ne_nil s ss))
        (s :: ss).dropLast.reverse (x :: A) [] h_suffix_ne h_drop_ne (by
          intro a ha
          unfold M
          simp +decide [ha])
      convert h using 1
      simpa [List.reverse_reverse] using
        congrArg (fun t => Tape.mk₂ (x :: A) (default :: t))
          (List.dropLast_append_getLast (List.cons_ne_nil s ss)).symm
    have h_cross : TM0.step (M sep2)
        ⟨.inr (.inl (x, .ret1)), Tape.mk₂ (x :: A) (default :: s :: ss)⟩ =
        some ⟨.inr (.inl (x, .ret2)), Tape.mk₂ A (x :: default :: s :: ss)⟩ := by
      unfold TM0.step M
      simp +decide [Tape.mk₂]
    have h_start_reaches : Reaches (TM0.step (M sep2))
        ⟨.inl (x, default, .shW0), Tape.mk₂ (x :: A) (s :: ss)⟩
        ⟨.inl (x, s, .shM), Tape.mk₂ (x :: A) (default :: ss)⟩ :=
      Relation.ReflTransGen.single h_start
    have h_move_reaches : Reaches (TM0.step (M sep2))
        ⟨.inl (x, s, .shM), Tape.mk₂ (x :: A) (default :: ss)⟩
        ⟨.inl (x, s, .shW), Tape.mk₂ (default :: x :: A) ss⟩ :=
      Relation.ReflTransGen.single h_move
    have h_cross_reaches : Reaches (TM0.step (M sep2))
        ⟨.inr (.inl (x, .ret1)), Tape.mk₂ (x :: A) (default :: s :: ss)⟩
        ⟨.inr (.inl (x, .ret2)), Tape.mk₂ A (x :: default :: s :: ss)⟩ :=
      Relation.ReflTransGen.single h_cross
    exact h_start_reaches.trans (h_move_reaches.trans (h_cascade.trans (h_scan.trans h_cross_reaches)))

/-- One complete iteration of the copy loop. -/
theorem one_iter_reaches (sep2 : Γ) (x : Γ) (rest copied L : List Γ)
    (suffix : List Γ)
    (hx : x ≠ default)
    (hrest : ∀ g ∈ rest, g ≠ default)
    (hcopied : ∀ g ∈ copied, g ≠ default)
    (hsuffix : ∀ g ∈ suffix, g ≠ default)
    (hL : ∀ g ∈ L, g ≠ default) :
    Reaches (TM0.step (M sep2))
      ⟨Sum.inr (Sum.inr NPhase.grab),
       Tape.mk₂ L (x :: rest ++ default :: copied ++ default :: suffix)⟩
      ⟨Sum.inr (Sum.inr NPhase.grab),
       Tape.mk₂ (x :: L) (rest ++ default :: copied ++ [x] ++ default :: suffix)⟩ := by
  have h_grab := grab_to_shW sep2 x rest copied L suffix hx hrest hcopied
  have h_shift := shW0_suffix_to_ret2 sep2 x
    (copied.reverse ++ default :: rest.reverse ++ default :: L) suffix hsuffix
  have h_ret := ret2_to_grab sep2 x rest copied L suffix hx hrest hcopied
  exact h_grab.trans (h_shift.trans h_ret)

/-! ### Copy Loop -/

theorem copy_loop_reaches_aux (sep2 : Γ) (block copied L suffix : List Γ)
    (hblock : ∀ g ∈ block, g ≠ default)
    (hcopied : ∀ g ∈ copied, g ≠ default)
    (hL : ∀ g ∈ L, g ≠ default)
    (hsuffix : ∀ g ∈ suffix, g ≠ default) :
    Reaches (TM0.step (M sep2))
      ⟨Sum.inr (Sum.inr NPhase.grab),
       Tape.mk₂ L (block ++ default :: copied ++ default :: suffix)⟩
      ⟨Sum.inr (Sum.inr NPhase.grab),
       Tape.mk₂ (block.reverse ++ L) (default :: copied ++ block ++ default :: suffix)⟩ := by
  induction' block with x rest ih generalizing copied L
  · simpa [List.append_assoc] using
      (Relation.ReflTransGen.refl :
        Reaches (TM0.step (M sep2))
          ⟨Sum.inr (Sum.inr NPhase.grab),
           Tape.mk₂ L (default :: copied ++ default :: suffix)⟩
          ⟨Sum.inr (Sum.inr NPhase.grab),
           Tape.mk₂ L (default :: copied ++ default :: suffix)⟩)
  · have hx : x ≠ default := hblock x (by simp)
    have hrest : ∀ g ∈ rest, g ≠ default := by
      intro g hg
      exact hblock g (by simp [hg])
    have hone := one_iter_reaches sep2 x rest copied L suffix hx hrest hcopied
      hsuffix hL
    have hcopied' : ∀ g ∈ copied ++ [x], g ≠ default := by
      intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · exact hcopied g hg
      · rw [List.mem_singleton.mp hg]
        exact hx
    have hL' : ∀ g ∈ x :: L, g ≠ default := by
      intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · exact hx
      · exact hL g hg
    have hrest_loop := ih (copied ++ [x]) (x :: L) hrest hcopied' hL'
    have hrest_loop' : Reaches (TM0.step (M sep2))
        ⟨Sum.inr (Sum.inr NPhase.grab),
         Tape.mk₂ (x :: L) (rest ++ default :: copied ++ [x] ++ default :: suffix)⟩
        ⟨Sum.inr (Sum.inr NPhase.grab),
         Tape.mk₂ (rest.reverse ++ x :: L)
           (default :: copied ++ x :: rest ++ default :: suffix)⟩ := by
      simpa [List.append_assoc] using hrest_loop
    convert hone.trans hrest_loop' using 1 <;> simp [List.append_assoc]

/-- The full copy loop. -/
theorem copy_loop_reaches (sep2 : Γ) (block suffix : List Γ)
    (hblock : ∀ g ∈ block, g ≠ default)
    (hsuffix : ∀ g ∈ suffix, g ≠ default) :
    Reaches (TM0.step (M sep2))
      ⟨Sum.inr (Sum.inr NPhase.grab),
       Tape.mk₂ [] (block ++ default :: default :: suffix)⟩
      ⟨Sum.inr (Sum.inr NPhase.grab),
       Tape.mk₂ block.reverse (default :: block ++ default :: suffix)⟩ := by
  simpa using
    copy_loop_reaches_aux sep2 block [] [] suffix hblock (by simp) (by simp) hsuffix

/-! ### Phase 2-3: write sep2, rewind, and halt -/

/-
Combined Phase 2-3: from grab at end of copy to done.
-/
theorem phase23_reaches (sep2 : Γ) (hsep2 : sep2 ≠ default)
    (block suffix : List Γ) (hblock : ∀ g ∈ block, g ≠ default) :
    Reaches (TM0.step (M sep2))
      ⟨Sum.inr (Sum.inr NPhase.grab),
       Tape.mk₂ block.reverse (default :: block ++ default :: suffix)⟩
      ⟨Sum.inr (Sum.inr NPhase.done),
       Tape.mk₁ (block ++ sep2 :: block ++ default :: suffix)⟩ := by
  by_cases h : block = [] <;> simp_all +decide [ Tape.mk₂ ];
  · revert hsep2;
    intro hsep2
    have h_step : TM0.step (M sep2) ⟨Sum.inr (Sum.inr NPhase.grab), Tape.mk' (ListBlank.mk []) (ListBlank.mk (default :: default :: suffix))⟩ = some ⟨Sum.inr (Sum.inr NPhase.wSep), Tape.mk' (ListBlank.mk []) (ListBlank.mk (sep2 :: default :: suffix))⟩ := by
      unfold M; simp +decide [ TM0.step ] ;
    have h_step : TM0.step (M sep2) ⟨Sum.inr (Sum.inr NPhase.rwF), Tape.mk' (ListBlank.mk []) (ListBlank.mk (default :: sep2 :: default :: suffix))⟩ = some ⟨Sum.inr (Sum.inr NPhase.done), Tape.mk' (ListBlank.mk []) (ListBlank.mk (default :: sep2 :: default :: suffix)) |> Tape.move Dir.right⟩ := by
      unfold TM0.step;
      unfold M; simp +decide [ hsep2 ] ;
    have h_step : Reaches (TM0.step (M sep2)) ⟨Sum.inr (Sum.inr NPhase.grab), Tape.mk' (ListBlank.mk []) (ListBlank.mk (default :: default :: suffix))⟩ ⟨Sum.inr (Sum.inr NPhase.rwF), Tape.mk' (ListBlank.mk []) (ListBlank.mk (default :: sep2 :: default :: suffix))⟩ := by
      have h_step : Reaches (TM0.step (M sep2)) ⟨Sum.inr (Sum.inr NPhase.wSep), Tape.mk' (ListBlank.mk []) (ListBlank.mk (sep2 :: default :: suffix))⟩ ⟨Sum.inr (Sum.inr NPhase.rwF), Tape.mk' (ListBlank.mk []) (ListBlank.mk (default :: sep2 :: default :: suffix))⟩ := by
        apply Relation.ReflTransGen.single;
        aesop;
      exact Relation.ReflTransGen.head ‹_› h_step;
    convert h_step.tail _ using 1;
    convert ‹TM0.step ( M sep2 ) _ = _› using 1;
    constructor <;> intro h <;> simp_all +decide [ Tape.mk₁ ];
    convert mk₂_default_left sep2 ( sep2 :: default :: suffix ) using 1;
  · obtain ⟨x, rest, hx⟩ : ∃ x rest, block.reverse = x :: rest := by
      exact List.exists_cons_of_ne_nil ( by simpa using h );
    have h_scan : Reaches (TM0.step (M sep2)) ⟨Sum.inr (Sum.inr NPhase.rwF), Tape.mk₂ rest (x :: sep2 :: block ++ default :: suffix)⟩ ⟨Sum.inr (Sum.inr NPhase.rwF), Tape.mk₂ [] (block ++ sep2 :: block ++ default :: suffix)⟩ := by
      convert generic_scan_left sep2 ( Sum.inr ( Sum.inr NPhase.rwF ) ) x rest [] ( sep2 :: block ++ default :: suffix ) _ _ _ using 1 <;> simp_all +decide [ List.mem_reverse ];
      unfold M; aesop;
    have h_boundary : Reaches (TM0.step (M sep2)) ⟨Sum.inr (Sum.inr NPhase.rwF), Tape.mk₂ [] (block ++ sep2 :: block ++ default :: suffix)⟩ ⟨Sum.inr (Sum.inr NPhase.done), Tape.mk₂ [] (block ++ sep2 :: block ++ default :: suffix)⟩ := by
      apply boundary_transition;
      · cases block <;> aesop;
      · cases block <;> simp_all +decide [ M ];
      · unfold M; aesop;
    have h_grab : Reaches (TM0.step (M sep2)) ⟨Sum.inr (Sum.inr NPhase.grab), Tape.mk₂ block.reverse (default :: block ++ default :: suffix)⟩ ⟨Sum.inr (Sum.inr NPhase.wSep), Tape.mk₂ block.reverse (sep2 :: block ++ default :: suffix)⟩ := by
      apply Relation.ReflTransGen.single;
      unfold M; simp +decide [ hx ] ;
      unfold TM0.step; simp +decide [ Tape.mk₂ ] ;
    have h_wSep : Reaches (TM0.step (M sep2)) ⟨Sum.inr (Sum.inr NPhase.wSep), Tape.mk₂ block.reverse (sep2 :: block ++ default :: suffix)⟩ ⟨Sum.inr (Sum.inr NPhase.rwF), Tape.mk₂ rest (x :: sep2 :: block ++ default :: suffix)⟩ := by
      convert Relation.ReflTransGen.single _ using 1;
      unfold M; simp +decide [ hx ] ;
      unfold TM0.step; simp +decide [ Tape.mk₂ ] ;
    convert h_grab.trans ( h_wSep.trans ( h_scan.trans h_boundary ) ) using 1;
    simp +decide [ Tape.mk₁, Tape.mk₂ ]

/-! ### Empty Block path helpers -/

/-
One step of the empty shift cascade (emShW/emShM).
    Two TM0 transitions.
-/
theorem emShW_step (sep2 : Γ) (c e : Γ) (L R : List Γ)
    (h : ¬(c = default ∧ e = default)) :
    Reaches (TM0.step (M sep2))
      ⟨.inr (.inl (c, .emShW)), Tape.mk₂ L (e :: R)⟩
      ⟨.inr (.inl (e, .emShW)), Tape.mk₂ (c :: L) R⟩ := by
  constructor;
  unfold TM0.step;
  rotate_right;
  exact ⟨ Sum.inr ( Sum.inl ( e, C1Phase.emShM ) ), Tape.mk₂ L ( c :: R ) ⟩;
  · apply_rules [ Relation.ReflTransGen.single ];
    unfold M; aesop;
  · unfold M; aesop;

/-
Terminal step of the empty cascade.
-/
theorem emShW_end (sep2 : Γ) (c : Γ) (L : List Γ)
    (hc : c ≠ default) :
    Reaches (TM0.step (M sep2))
      ⟨.inr (.inl (c, .emShW)), Tape.mk₂ L []⟩
      ⟨.inr (.inr .emRw), Tape.mk₂ L [c]⟩ := by
  constructor;
  swap;
  rotate_right;
  exact ⟨ Sum.inr ( Sum.inl ( default, C1Phase.emShW ) ), Tape.mk₂ ( c :: L ) [ ] ⟩;
  · unfold M; simp +decide [ hc ] ;
    unfold TM0.step; simp +decide [ Tape.mk₂ ] ;
  · convert emShW_step sep2 c default L [] _ using 1;
    grind +revert

/-
Immediate termination of empty cascade.
-/
theorem emShW_terminate (sep2 : Γ) (x : Γ) (L : List Γ) :
    Reaches (TM0.step (M sep2))
      ⟨.inr (.inl (default, .emShW)), Tape.mk₂ (x :: L) []⟩
      ⟨.inr (.inr .emRw), Tape.mk₂ L [x]⟩ := by
  convert Relation.ReflTransGen.single _;
  unfold M;
  unfold Tape.mk₂; simp +decide [ TM0.step ] ;

/-
Full empty shift cascade.
-/
theorem em_cascade (sep2 : Γ) (carry : Γ) (hcarry : carry ≠ default)
    (L : List Γ) (elems : List Γ) (helems : ∀ g ∈ elems, g ≠ default) :
    Reaches (TM0.step (M sep2))
      ⟨.inr (.inl (carry, .emShW)), Tape.mk₂ L elems⟩
      ⟨.inr (.inr .emRw),
       Tape.mk₂ ((carry :: elems).dropLast.reverse ++ L)
                 [(carry :: elems).getLast (List.cons_ne_nil carry elems)]⟩ := by
  induction' elems with e elems ih generalizing L carry <;> simp_all +decide [ Tape.mk₂ ];
  · convert emShW_end sep2 carry L hcarry using 1;
  · have h_step := emShW_step sep2 carry e L elems (by simp [hcarry, helems.1])
    convert h_step.trans (ih e helems.1 (carry :: L)) using 1

/-
Empty block path.
-/
theorem empty_block_reaches (sep2 : Γ) (hsep2 : sep2 ≠ default)
    (suffix : List Γ) (hsuffix : ∀ g ∈ suffix, g ≠ default) :
    Reaches (TM0.step (M sep2))
      ⟨Sum.inr (Sum.inr NPhase.start), Tape.mk₁ (default :: suffix)⟩
      ⟨Sum.inr (Sum.inr NPhase.done), Tape.mk₁ (sep2 :: default :: suffix)⟩ := by
  cases suffix <;> simp_all +decide [ ListBlank.mk ];
  · -- After the first three steps, the machine reaches the done state with the tape [sep2, default].
    have h_reaches : Reaches (TM0.step (M sep2)) ⟨Sum.inr (Sum.inr NPhase.emAW), Tape.mk₂ [] [sep2]⟩ ⟨Sum.inr (Sum.inr NPhase.emCk), Tape.mk₂ [sep2] []⟩ := by
      convert Relation.ReflTransGen.single _;
      unfold M; aesop;
    have h_reaches : Reaches (TM0.step (M sep2)) ⟨Sum.inr (Sum.inr NPhase.emCk), Tape.mk₂ [sep2] []⟩ ⟨Sum.inr (Sum.inr NPhase.done), Tape.mk₂ [] [sep2]⟩ := by
      constructor;
      constructor;
      unfold M; simp +decide [ hsep2 ] ;
      unfold TM0.step; simp +decide [ Tape.mk₂ ] ;
    have h_reaches : Reaches (TM0.step (M sep2)) ⟨Sum.inr (Sum.inr NPhase.start), Tape.mk₁ [default]⟩ ⟨Sum.inr (Sum.inr NPhase.emCk), Tape.mk₂ [sep2] []⟩ := by
      apply Relation.ReflTransGen.trans;
      rotate_right;
      exact ⟨ Sum.inr ( Sum.inr NPhase.emAW ), Tape.mk₂ [] [ sep2 ] ⟩;
      · apply_rules [ Relation.ReflTransGen.single ];
        simp +decide [ Tape.mk₁, Tape.mk₂ ];
        simp +decide [ TM0.step, M ];
      · assumption;
    convert h_reaches.trans ‹_› using 1;
    congr! 1;
    -- By definition of `Tape.mk₁` and `Tape.mk₂`, we can see that they are equal when the list is `[sep2, default]`.
    simp [Tape.mk₁, Tape.mk₂];
    unfold Tape.mk' ListBlank.mk; simp +decide [ ListBlank.ext_iff ] ;
    exact ⟨ rfl, fun i => by cases i <;> rfl ⟩;
  · rename_i h t;
    -- Apply the em_cascade lemma to handle the case where the suffix is non-empty.
    have h_em_cascade : Reaches (TM0.step (M sep2))
      ⟨.inr (.inl (h, .emShW)), Tape.mk₂ [default, sep2] t⟩
      ⟨.inr (.inr NPhase.emRw), Tape.mk₂ ((h :: t).dropLast.reverse ++ [default, sep2]) [(h :: t).getLast (List.cons_ne_nil h t)]⟩ := by
        convert em_cascade sep2 h hsuffix.1 [ default, sep2 ] t hsuffix.2 using 1;
    have h_emRw : Reaches (TM0.step (M sep2))
      ⟨.inr (.inr NPhase.emRw), Tape.mk₂ ((h :: t).dropLast.reverse ++ [default, sep2]) [(h :: t).getLast (List.cons_ne_nil h t)]⟩
      ⟨.inr (.inr NPhase.emRw), Tape.mk₂ [default, sep2] (h :: t)⟩ := by
        have h_emRw : Reaches (TM0.step (M sep2))
          ⟨.inr (.inr NPhase.emRw), Tape.mk₂ ((h :: t).dropLast.reverse ++ [default, sep2]) [(h :: t).getLast (List.cons_ne_nil h t)]⟩
          ⟨.inr (.inr NPhase.emRw), Tape.mk₂ [default, sep2] ((h :: t).dropLast.reverse.reverse ++ [(h :: t).getLast (List.cons_ne_nil h t)])⟩ := by
            apply generic_scan_left;
            · grind;
            · grind +suggestions;
            · unfold M; aesop;
        convert h_emRw using 1;
        rw [ List.reverse_reverse, List.dropLast_append_getLast ];
    have h_emRw_final : Reaches (TM0.step (M sep2))
      ⟨.inr (.inr NPhase.emRw), Tape.mk₂ [default, sep2] (h :: t)⟩
      ⟨.inr (.inr NPhase.done), Tape.mk₁ (sep2 :: default :: h :: t)⟩ := by
        have h_emRw_final : TM0.step (M sep2) ⟨.inr (.inr NPhase.emRw), Tape.mk₂ [default, sep2] (h :: t)⟩ = some ⟨.inr (.inr NPhase.emRw), Tape.mk₂ [sep2] (default :: h :: t)⟩ := by
          simp +decide [ TM0.step, M ];
          exact ⟨ TM0.Stmt.move Dir.left, by unfold Tape.mk₂; aesop, by unfold Tape.mk₂; aesop ⟩;
        have h_emRw_final : TM0.step (M sep2) ⟨.inr (.inr NPhase.emRw), Tape.mk₂ [sep2] (default :: h :: t)⟩ = some ⟨.inr (.inr NPhase.done), Tape.mk₂ [] (sep2 :: default :: h :: t)⟩ := by
          unfold TM0.step; simp +decide [ M ] ;
          exact ⟨ _, if_pos rfl, by rfl ⟩;
        exact Relation.ReflTransGen.head ( by aesop ) ( Relation.ReflTransGen.single ( by aesop ) );
    have h_start : Reaches (TM0.step (M sep2))
      ⟨.inr (.inr NPhase.start), Tape.mk₁ (default :: h :: t)⟩
      ⟨.inr (.inr NPhase.emAW), Tape.mk₂ [] (sep2 :: h :: t)⟩ := by
        apply Relation.ReflTransGen.single;
        unfold M; simp +decide [ hsep2 ] ;
        unfold TM0.step; simp +decide [ Tape.mk₁, Tape.mk₂ ] ;
    have h_emAW : Reaches (TM0.step (M sep2))
      ⟨.inr (.inr NPhase.emAW), Tape.mk₂ [] (sep2 :: h :: t)⟩
      ⟨.inr (.inr NPhase.emCk), Tape.mk₂ [sep2] (h :: t)⟩ := by
        apply Relation.ReflTransGen.single;
        unfold M; simp +decide [ hsep2, hsuffix ] ;
        unfold TM0.step; simp +decide [ Tape.mk₂ ] ;
    have h_emCk : Reaches (TM0.step (M sep2))
      ⟨.inr (.inr NPhase.emCk), Tape.mk₂ [sep2] (h :: t)⟩
      ⟨.inr (.inl (h, .emShM)), Tape.mk₂ [sep2] (default :: t)⟩ := by
        apply Relation.ReflTransGen.single;
        unfold M; simp +decide [ hsuffix ] ;
        unfold TM0.step; simp +decide [ hsuffix ] ;
        exact ⟨ TM0.Stmt.write default, by simp +decide [ Tape.mk₂, hsuffix ], by simp +decide [ Tape.mk₂, hsuffix ] ⟩;
    have h_emShM : Reaches (TM0.step (M sep2))
      ⟨.inr (.inl (h, .emShM)), Tape.mk₂ [sep2] (default :: t)⟩
      ⟨.inr (.inl (h, .emShW)), Tape.mk₂ [default, sep2] t⟩ := by
        apply Relation.ReflTransGen.single;
        unfold M; aesop;
    exact h_start.trans ( h_emAW.trans ( h_emCk.trans ( h_emShM.trans ( h_em_cascade.trans ( h_emRw.trans h_emRw_final ) ) ) ) )

/-! ### Full Computation -/

/-- Full correctness. -/
theorem full_reaches (sep2 : Γ) (hsep2 : sep2 ≠ default)
    (block suffix : List Γ)
    (hblock : ∀ g ∈ block, g ≠ default)
    (hsuffix : ∀ g ∈ suffix, g ≠ default) :
    Reaches (TM0.step (M sep2))
      (TM0.init (block ++ default :: suffix))
      ⟨Sum.inr (Sum.inr NPhase.done),
       Tape.mk₁ (copyWithSep sep2 block ++ default :: suffix)⟩ := by
  cases block with
  | nil =>
    simp only [copyWithSep, List.nil_append]
    exact empty_block_reaches sep2 hsep2 suffix hsuffix
  | cons x rest =>
    have h0 := phase0_reaches sep2 (x :: rest) suffix hblock (by simp) hsuffix
    have hloop := copy_loop_reaches sep2 (x :: rest) suffix hblock hsuffix
    have h23 := phase23_reaches sep2 hsep2 (x :: rest) suffix hblock
    rw [← RevBlock.mk₂_nil_eq_mk₁] at h0
    have goal_eq : copyWithSep sep2 (x :: rest) ++ default :: suffix =
        (x :: rest) ++ sep2 :: (x :: rest) ++ default :: suffix := by
      simp [copyWithSep]
    rw [goal_eq]
    exact h0.trans (hloop.trans h23)

end CopyBlock

/-! ### Realizability Theorems -/

/-- The general copy-with-sep operation is block-sep-realizable for the
default boundary separator.

The machine `CopyBlock.M sep2` copies everything before the first `default`,
inserting `sep2` between the original and the copy. -/
theorem tm0_copyWithSep_blockSep {Γ : Type} [Inhabited Γ] [DecidableEq Γ] [Fintype Γ]
    {sep2 : Γ} (hsep2 : sep2 ≠ default) :
    TM0RealizesBlockSep Γ default (copyWithSep sep2) := by
  refine ⟨CopyBlock.CSt Γ, inferInstance, inferInstance, CopyBlock.M sep2, ?_⟩
  intro block suffix hblock _hblock_sep hsuffix _hfblock _hfblock_sep
  have h_reaches := CopyBlock.full_reaches sep2 hsep2 block suffix hblock hsuffix
  have h_mem : ⟨Sum.inr (Sum.inr CopyBlock.NPhase.done),
       Tape.mk₁ (copyWithSep sep2 block ++ default :: suffix)⟩ ∈
      Turing.eval (TM0.step (CopyBlock.M sep2))
        (TM0.init (block ++ default :: suffix)) :=
    Turing.mem_eval.mpr ⟨h_reaches, CopyBlock.step_done sep2 _⟩
  exact ⟨Part.dom_iff_mem.mpr ⟨_, h_mem⟩, fun h =>
    (Part.mem_unique (Part.get_mem h) h_mem).symm ▸ rfl⟩

/-- The general copy-with-separator operation before an arbitrary outer
separator.

The underlying copy machine still uses `default` as its internal boundary
marker. We expose an arbitrary outer separator by first replacing that boundary
with `default`, running the existing copy machine, then restoring the boundary
separator. -/
theorem tm0_copyWithSep_blockSep_outer
    {Γ : Type} [Inhabited Γ] [DecidableEq Γ] [Fintype Γ]
    {sep2 outerSep : Γ}
    (hsep2 : sep2 ≠ default) :
    TM0RealizesBlockSep Γ outerSep (copyWithSep sep2) := by
  let Mpre := boundaryReplaceMachine outerSep (default : Γ)
  let Mcopy := CopyBlock.M sep2
  let Mpost := boundaryReplaceMachine (default : Γ) outerSep
  let h12i : Inhabited (BoundaryReplaceSt ⊕ CopyBlock.CSt Γ) :=
    ⟨Sum.inl (@default _ inferInstance)⟩
  let M12 : TM0.Machine Γ (BoundaryReplaceSt ⊕ CopyBlock.CSt Γ) :=
    @TM0Seq.compose Γ BoundaryReplaceSt inferInstance (CopyBlock.CSt Γ)
      inferInstance Mpre Mcopy
  let h123i : Inhabited ((BoundaryReplaceSt ⊕ CopyBlock.CSt Γ) ⊕ BoundaryReplaceSt) :=
    ⟨Sum.inl (@default _ h12i)⟩
  let M123 : TM0.Machine Γ ((BoundaryReplaceSt ⊕ CopyBlock.CSt Γ) ⊕ BoundaryReplaceSt) :=
    @TM0Seq.compose Γ (BoundaryReplaceSt ⊕ CopyBlock.CSt Γ) h12i
      BoundaryReplaceSt inferInstance M12 Mpost
  refine ⟨(BoundaryReplaceSt ⊕ CopyBlock.CSt Γ) ⊕ BoundaryReplaceSt, h123i,
    inferInstance, M123, ?_⟩
  intro block suffix hblock_nd hblock_nouter hsuffix_nd hf_nd _hf_nouter
  have hpre := tm0_boundaryReplace outerSep (default : Γ)
    block suffix hblock_nd hblock_nouter
  have hcopy_reaches :=
    CopyBlock.full_reaches sep2 hsep2 block suffix hblock_nd hsuffix_nd
  have hcopy_mem :
      ⟨Sum.inr (Sum.inr CopyBlock.NPhase.done),
        Tape.mk₁ (copyWithSep sep2 block ++ default :: suffix)⟩ ∈
        Turing.eval (TM0.step Mcopy)
          (TM0.init (block ++ default :: suffix)) :=
    Turing.mem_eval.mpr ⟨hcopy_reaches, CopyBlock.step_done sep2 _⟩
  have hcopy_dom :
      (TM0Seq.evalCfg Mcopy (block ++ default :: suffix)).Dom :=
    Part.dom_iff_mem.mpr ⟨_, hcopy_mem⟩
  have hcopy_tape :
      ∀ h,
        ((TM0Seq.evalCfg Mcopy (block ++ default :: suffix)).get h).Tape =
          Tape.mk₁ (copyWithSep sep2 block ++ default :: suffix) := by
    intro h
    exact (Part.mem_unique (Part.get_mem h) hcopy_mem).symm ▸ rfl
  have hcopy_from_cfg :
      (TM0Seq.evalFromCfg Mcopy
        ⟨default, ((TM0Seq.evalCfg Mpre
          (block ++ outerSep :: suffix)).get hpre.1).Tape⟩).Dom := by
    rw [hpre.2 hpre.1]
    show (TM0Seq.evalFromCfg Mcopy (TM0.init (block ++ default :: suffix))).Dom
    rw [TM0Seq.evalFromCfg_init]
    exact hcopy_dom
  have hM12_dom :
      (TM0Seq.evalCfg M12 (block ++ outerSep :: suffix)).Dom := by
    exact (TM0Seq.evalCfg_dom_iff M12 (block ++ outerSep :: suffix)).mpr
      (TM0Seq.compose_dom_of_parts Mpre Mcopy
        (block ++ outerSep :: suffix) hpre.1 hcopy_from_cfg)
  have hM12_tape :
      ((TM0Seq.evalCfg M12 (block ++ outerSep :: suffix)).get hM12_dom).Tape =
        Tape.mk₁ (copyWithSep sep2 block ++ default :: suffix) := by
    have ht := TM0Seq.compose_evalCfg_tape Mpre Mcopy
      (block ++ outerSep :: suffix) (block ++ default :: suffix)
      hpre.1 (hpre.2 hpre.1) hcopy_dom hM12_dom
    rw [ht]
    exact hcopy_tape hcopy_dom
  have hpost := tm0_boundaryReplace (default : Γ) outerSep
    (copyWithSep sep2 block) suffix hf_nd hf_nd
  have hpost_from_cfg :
      (TM0Seq.evalFromCfg Mpost
        ⟨default, ((TM0Seq.evalCfg M12
          (block ++ outerSep :: suffix)).get hM12_dom).Tape⟩).Dom := by
    rw [hM12_tape]
    show (TM0Seq.evalFromCfg Mpost
      (TM0.init (copyWithSep sep2 block ++ default :: suffix))).Dom
    rw [TM0Seq.evalFromCfg_init]
    exact hpost.1
  have hM123_dom :
      (TM0Seq.evalCfg M123 (block ++ outerSep :: suffix)).Dom := by
    exact (TM0Seq.evalCfg_dom_iff M123 (block ++ outerSep :: suffix)).mpr
      (TM0Seq.compose_dom_of_parts M12 Mpost
        (block ++ outerSep :: suffix) hM12_dom hpost_from_cfg)
  refine ⟨hM123_dom, ?_⟩
  intro h
  have ht := TM0Seq.compose_evalCfg_tape M12 Mpost
    (block ++ outerSep :: suffix)
    (copyWithSep sep2 block ++ default :: suffix)
    hM12_dom hM12_tape hpost.1 h
  rw [ht]
  exact hpost.2 hpost.1

/-- `copyWithSep` preserves freshness for a separator distinct from the
inserted copy separator. -/
theorem copyWithSep_ne_sep {Γ : Type} {sep2 sep : Γ}
    (hsep2_sep : sep2 ≠ sep) (block : List Γ)
    (hblock : ∀ g ∈ block, g ≠ sep) :
    ∀ g ∈ copyWithSep sep2 block, g ≠ sep := by
  unfold copyWithSep
  intro g hg
  rw [List.mem_append] at hg
  rcases hg with hg | hg
  · rw [List.mem_append] at hg
    rcases hg with hg | hg
    · exact hblock g hg
    · have hg_eq : g = sep2 := by simpa using hg
      simpa [hg_eq] using hsep2_sep
  · exact hblock g hg

/-- Appending just the copy separator is realizable before an opaque outer
separator. This is the first phase needed by a left-origin copy construction;
unlike `CopyBlock.M`, it does not shift the suffix by scanning through it. -/
theorem tm0_appendCopySep_blockSepAnySuffix
    {Γ : Type} [Inhabited Γ] [DecidableEq Γ] [Fintype Γ]
    {sep2 outerSep : Γ}
    (hsep2 : sep2 ≠ default) (hsep2_outer : sep2 ≠ outerSep) :
    TM0RealizesBlockSepAnySuffix Γ outerSep (fun block => block ++ [sep2]) := by
  exact tm0_appendList_blockSep_anySuffix [sep2]
    (by
      intro g hg
      simp at hg
      exact hg ▸ hsep2)
    (by
      intro g hg
      simp at hg
      exact hg ▸ hsep2_outer)

namespace CopyBlockLeft

variable {Γ : Type} [Inhabited Γ] [DecidableEq Γ] [Fintype Γ]

/-- States for the left-origin copy machine.

Unlike `CopyBlock.M`, this machine should not shift the suffix after the outer
separator. It copies source symbols into blank cells to the left of the current
origin, then finishes with the head on the new left origin.

The intended layout for a non-empty block is:

* original input, physical cells `0..n`: `block ++ [outerSep]`;
* output keeps `outerSep` in the same physical cell;
* the new origin is shifted left by `n + 1`, so the finite tape reads
  `block ++ [sep2] ++ block ++ [outerSep] ++ suffix`.
-/
inductive LPhase where
  | start
  | emptyWrite
  | initWrite
  | initReturn
  | scanEnd
  | sourceCheck
  | toBoundary
  | toCopyBlank
  | returnBoundary
  | returnMarker
  | afterRestore
  | doneSeekLeft
  | doneSeekOrigin
  | done
  deriving DecidableEq, Repr

instance : Fintype LPhase where
  elems := {.start, .emptyWrite, .initWrite, .initReturn, .scanEnd,
    .sourceCheck, .toBoundary, .toCopyBlank, .returnBoundary, .returnMarker,
    .afterRestore, .doneSeekLeft, .doneSeekOrigin, .done}
  complete q := by cases q <;> simp

abbrev LSt (Γ : Type) := (Γ × LPhase) ⊕ LPhase

instance : Inhabited (LSt Γ) := ⟨Sum.inr .start⟩

/-- Copy before `outerSep` by growing into the blank cells left of the current
origin, preserving the entire suffix after `outerSep` opaquely.

`default` is used only as the left boundary/source marker. Since active blocks
are default-free, the marker is unambiguous. -/
noncomputable def M (sep2 outerSep : Γ) :
    @TM0.Machine Γ (LSt Γ) ⟨Sum.inr .start⟩ := fun q a =>
  match q with
  | .inr .start =>
      if a = outerSep then
        some (.inr .emptyWrite, TM0.Stmt.move Dir.left)
      else
        some (.inr .initWrite, TM0.Stmt.move Dir.left)
  | .inr .emptyWrite =>
      some (.inr .done, TM0.Stmt.write sep2)
  | .inr .initWrite =>
      some (.inr .initReturn, TM0.Stmt.write outerSep)
  | .inr .initReturn =>
      some (.inr .scanEnd, TM0.Stmt.move Dir.right)
  | .inr .scanEnd =>
      if a = outerSep then
        some (.inr .sourceCheck, TM0.Stmt.move Dir.left)
      else
        some (.inr .scanEnd, TM0.Stmt.move Dir.right)
  | .inr .sourceCheck =>
      if a = outerSep then
        some (.inr .doneSeekLeft, TM0.Stmt.write sep2)
      else
        some (.inl (a, .toBoundary), TM0.Stmt.write default)
  | .inl (c, .toBoundary) =>
      if a = outerSep then
        some (.inl (c, .toCopyBlank), TM0.Stmt.move Dir.left)
      else
        some (.inl (c, .toBoundary), TM0.Stmt.move Dir.left)
  | .inl (c, .toCopyBlank) =>
      if a = default then
        some (.inl (c, .returnBoundary), TM0.Stmt.write c)
      else
        some (.inl (c, .toCopyBlank), TM0.Stmt.move Dir.left)
  | .inl (c, .returnBoundary) =>
      if a = outerSep then
        some (.inl (c, .returnMarker), TM0.Stmt.move Dir.right)
      else
        some (.inl (c, .returnBoundary), TM0.Stmt.move Dir.right)
  | .inl (c, .returnMarker) =>
      if a = default then
        some (.inr .afterRestore, TM0.Stmt.write c)
      else
        some (.inl (c, .returnMarker), TM0.Stmt.move Dir.right)
  | .inr .afterRestore =>
      some (.inr .sourceCheck, TM0.Stmt.move Dir.left)
  | .inr .doneSeekLeft =>
      if a = default then
        some (.inr .doneSeekOrigin, TM0.Stmt.move Dir.right)
      else
        some (.inr .doneSeekLeft, TM0.Stmt.move Dir.left)
  | .inr .doneSeekOrigin =>
      some (.inr .done, TM0.Stmt.move Dir.right)
  | .inr .done => none
  | .inr .toBoundary
  | .inr .toCopyBlank
  | .inr .returnBoundary
  | .inr .returnMarker => none
  | .inl (_, .start)
  | .inl (_, .emptyWrite)
  | .inl (_, .initWrite)
  | .inl (_, .initReturn)
  | .inl (_, .scanEnd)
  | .inl (_, .sourceCheck)
  | .inl (_, .afterRestore)
  | .inl (_, .doneSeekLeft)
  | .inl (_, .doneSeekOrigin)
  | .inl (_, .done) => none

theorem step_done (sep2 outerSep : Γ) (t : Tape Γ) :
    TM0.step (M sep2 outerSep)
      ⟨Sum.inr LPhase.done, t⟩ = none := by
  simp [TM0.step, M]

/-- Empty-block path for the left-origin copy machine. No suffix invariant is
needed: the machine only moves left of the outer separator and writes `sep2`. -/
theorem empty_block_reaches (sep2 outerSep : Γ) (suffix : List Γ) :
    Reaches (TM0.step (M sep2 outerSep))
      ⟨Sum.inr LPhase.start, Tape.mk₁ (outerSep :: suffix)⟩
      ⟨Sum.inr LPhase.done, Tape.mk₁ (sep2 :: outerSep :: suffix)⟩ := by
  refine Relation.ReflTransGen.head (b :=
      ⟨Sum.inr LPhase.emptyWrite,
        Tape.mk₂ ([] : List Γ) (default :: outerSep :: suffix)⟩) ?_ ?_
  · simp +decide [TM0.step, M, Tape.mk₁, Tape.mk₂]
  · refine Relation.ReflTransGen.single ?_
    simp +decide [TM0.step, M, Tape.mk₁, Tape.mk₂]

/-- Generic scan-left lemma for states whose transition is "move left while
the current symbol is not `stop`". -/
theorem generic_scan_left
    (sep2 outerSep stop : Γ) (q : LSt Γ)
    (h : Γ) (elems L R : List Γ)
    (hh : h ≠ stop)
    (hstep : ∀ a, a ≠ stop →
      M sep2 outerSep q a = some (q, TM0.Stmt.move Dir.left))
    (helems : ∀ a ∈ elems, a ≠ stop) :
    Reaches (TM0.step (M sep2 outerSep))
      ⟨q, Tape.mk₂ (elems ++ L) (h :: R)⟩
      ⟨q, Tape.mk₂ L (elems.reverse ++ h :: R)⟩ := by
  induction' elems with a elems ih generalizing h R
  · exact Relation.ReflTransGen.refl
  · have ha : a ≠ stop := helems a List.mem_cons_self
    have helems' : ∀ x ∈ elems, x ≠ stop := by
      intro x hx
      exact helems x (List.mem_cons_of_mem a hx)
    have h_step :
        TM0.step (M sep2 outerSep)
          ⟨q, Tape.mk₂ (a :: elems ++ L) (h :: R)⟩ =
        some ⟨q, Tape.mk₂ (elems ++ L) (a :: h :: R)⟩ := by
      unfold TM0.step
      simp +decide [Tape.mk₂, hstep h hh]
    refine Relation.ReflTransGen.head (by exact Option.mem_def.mpr h_step) ?_
    simpa [List.reverse_cons, List.append_assoc] using
      ih a (h :: R) ha helems'

/-- Generic scan-right lemma for states whose transition is "move right while
the current symbol is not `stop`". -/
theorem generic_scan_right
    (sep2 outerSep stop : Γ) (q : LSt Γ)
    (elems L R : List Γ)
    (hstep : ∀ a, a ≠ stop →
      M sep2 outerSep q a = some (q, TM0.Stmt.move Dir.right))
    (helems : ∀ a ∈ elems, a ≠ stop) :
    Reaches (TM0.step (M sep2 outerSep))
      ⟨q, Tape.mk₂ L (elems ++ R)⟩
      ⟨q, Tape.mk₂ (elems.reverse ++ L) R⟩ := by
  induction' elems with a elems ih generalizing L
  · exact Relation.ReflTransGen.refl
  · have ha : a ≠ stop := helems a List.mem_cons_self
    have helems' : ∀ x ∈ elems, x ≠ stop := by
      intro x hx
      exact helems x (List.mem_cons_of_mem a hx)
    have h_step :
        TM0.step (M sep2 outerSep)
          ⟨q, Tape.mk₂ L (a :: elems ++ R)⟩ =
        some ⟨q, Tape.mk₂ (a :: L) (elems ++ R)⟩ := by
      unfold TM0.step
      simp +decide [Tape.mk₂, hstep a ha]
    refine Relation.ReflTransGen.head (by exact Option.mem_def.mpr h_step) ?_
    simpa [List.reverse_cons, List.append_assoc] using ih (a :: L) helems'

/-- Scan left across `elems` and then one more step onto an explicit stop
symbol stored immediately to their left. -/
theorem generic_scan_left_to_stop
    (sep2 outerSep stop : Γ) (q : LSt Γ)
    (h : Γ) (elems L R : List Γ)
    (hh : h ≠ stop)
    (hstep : ∀ a, a ≠ stop →
      M sep2 outerSep q a = some (q, TM0.Stmt.move Dir.left))
    (helems : ∀ a ∈ elems, a ≠ stop) :
    Reaches (TM0.step (M sep2 outerSep))
      ⟨q, Tape.mk₂ (elems ++ stop :: L) (h :: R)⟩
      ⟨q, Tape.mk₂ L (stop :: elems.reverse ++ h :: R)⟩ := by
  induction' elems with a elems ih generalizing h R
  · have h_step :
        TM0.step (M sep2 outerSep)
          ⟨q, Tape.mk₂ (stop :: L) (h :: R)⟩ =
        some ⟨q, Tape.mk₂ L (stop :: h :: R)⟩ := by
      unfold TM0.step
      simp +decide [Tape.mk₂, hstep h hh]
    exact Relation.ReflTransGen.single (Option.mem_def.mpr h_step)
  · have ha : a ≠ stop := helems a List.mem_cons_self
    have helems' : ∀ x ∈ elems, x ≠ stop := by
      intro x hx
      exact helems x (List.mem_cons_of_mem a hx)
    have h_step :
        TM0.step (M sep2 outerSep)
          ⟨q, Tape.mk₂ (a :: elems ++ stop :: L) (h :: R)⟩ =
        some ⟨q, Tape.mk₂ (elems ++ stop :: L) (a :: h :: R)⟩ := by
      unfold TM0.step
      simp +decide [Tape.mk₂, hstep h hh]
    refine Relation.ReflTransGen.head (Option.mem_def.mpr h_step) ?_
    simpa [List.reverse_cons, List.append_assoc] using
      ih a (h :: R) ha helems'

/-- Scan left across the represented cells until the implicit blank just past
the left end of the finite tape. -/
theorem generic_scan_left_to_blank
    (sep2 outerSep : Γ) (q : LSt Γ)
    (h : Γ) (elems R : List Γ)
    (hh : h ≠ default)
    (hstep : ∀ a, a ≠ default →
      M sep2 outerSep q a = some (q, TM0.Stmt.move Dir.left))
    (helems : ∀ a ∈ elems, a ≠ default) :
    Reaches (TM0.step (M sep2 outerSep))
      ⟨q, Tape.mk₂ elems (h :: R)⟩
      ⟨q, Tape.mk₂ [] (default :: elems.reverse ++ h :: R)⟩ := by
  induction' elems with a elems ih generalizing h R
  · have h_step :
        TM0.step (M sep2 outerSep)
          ⟨q, Tape.mk₂ [] (h :: R)⟩ =
        some ⟨q, Tape.mk₂ [] (default :: h :: R)⟩ := by
      unfold TM0.step
      simp +decide [Tape.mk₂, hstep h hh]
    exact Relation.ReflTransGen.single (Option.mem_def.mpr h_step)
  · have ha : a ≠ default := helems a List.mem_cons_self
    have helems' : ∀ x ∈ elems, x ≠ default := by
      intro x hx
      exact helems x (List.mem_cons_of_mem a hx)
    have h_step :
        TM0.step (M sep2 outerSep)
          ⟨q, Tape.mk₂ (a :: elems) (h :: R)⟩ =
        some ⟨q, Tape.mk₂ elems (a :: h :: R)⟩ := by
      unfold TM0.step
      simp +decide [Tape.mk₂, hstep h hh]
    refine Relation.ReflTransGen.head (Option.mem_def.mpr h_step) ?_
    simpa [List.reverse_cons, List.append_assoc] using
      ih a (h :: R) ha helems'

/-- Non-empty correctness for `CopyBlockLeft.M`.

This is the remaining loop invariant for the left-origin copy machine. The
machine first installs a temporary `outerSep` marker immediately to the left of
the source block, copies source symbols right-to-left into the blank workspace
left of that marker, overwrites the temporary marker with `sep2`, and halts on
the new left origin. -/
theorem nonempty_block_reaches
    (sep2 outerSep : Γ) (x : Γ) (xs suffix : List Γ)
    (hblock_nd : ∀ g ∈ x :: xs, g ≠ default)
    (hblock_nouter : ∀ g ∈ x :: xs, g ≠ outerSep) :
    Reaches (TM0.step (M sep2 outerSep))
      (TM0.init ((x :: xs) ++ outerSep :: suffix))
      ⟨Sum.inr LPhase.done,
        Tape.mk₁ (copyWithSep sep2 (x :: xs) ++ outerSep :: suffix)⟩ := by
  sorry

end CopyBlockLeft

/-- Separator-bounded copy, with no assumptions about the suffix after the
outer separator.

The existing `CopyBlock.M` proof above is default-boundary based and shifts
the post-boundary region, so it requires that region to be default-free.  The
machine intended for this theorem is `CopyBlockLeft.M`: it leaves the physical
outer separator and suffix fixed, grows the represented finite tape to the
left, and therefore can preserve an arbitrary suffix opaquely. -/
theorem tm0_copyWithSep_blockSepAnySuffix_outer
    {Γ : Type} [Inhabited Γ] [DecidableEq Γ] [Fintype Γ]
    {sep2 outerSep : Γ}
    (hsep2 : sep2 ≠ default) :
    TM0RealizesBlockSepAnySuffix Γ outerSep (copyWithSep sep2) := by
  refine ⟨CopyBlockLeft.LSt Γ, inferInstance, inferInstance,
    CopyBlockLeft.M sep2 outerSep, ?_⟩
  intro block suffix hblock_nd hblock_nouter hf_nd hf_nouter
  cases block with
  | nil =>
      have h_reaches := CopyBlockLeft.empty_block_reaches sep2 outerSep suffix
      have h_reaches' :
          Reaches (TM0.step (CopyBlockLeft.M sep2 outerSep))
            (TM0.init ([] ++ outerSep :: suffix))
            ⟨Sum.inr CopyBlockLeft.LPhase.done,
              Tape.mk₁ (copyWithSep sep2 [] ++ outerSep :: suffix)⟩ := by
        simpa [TM0.init, copyWithSep] using h_reaches
      have h_mem :
          ⟨Sum.inr CopyBlockLeft.LPhase.done,
            Tape.mk₁ (copyWithSep sep2 [] ++ outerSep :: suffix)⟩ ∈
          Turing.eval (TM0.step (CopyBlockLeft.M sep2 outerSep))
            (TM0.init ([] ++ outerSep :: suffix)) :=
        Turing.mem_eval.mpr
          ⟨h_reaches',
            CopyBlockLeft.step_done sep2 outerSep
              (Tape.mk₁ (copyWithSep sep2 [] ++ outerSep :: suffix))⟩
      exact ⟨Part.dom_iff_mem.mpr ⟨_, h_mem⟩, fun h =>
        (Part.mem_unique (Part.get_mem h) h_mem).symm ▸ rfl⟩
  | cons x xs =>
      have h_reaches :=
        CopyBlockLeft.nonempty_block_reaches sep2 outerSep x xs suffix
          hblock_nd hblock_nouter
      have h_mem :
          ⟨Sum.inr CopyBlockLeft.LPhase.done,
            Tape.mk₁ (copyWithSep sep2 (x :: xs) ++ outerSep :: suffix)⟩ ∈
          Turing.eval (TM0.step (CopyBlockLeft.M sep2 outerSep))
            (TM0.init ((x :: xs) ++ outerSep :: suffix)) :=
        Turing.mem_eval.mpr
          ⟨h_reaches,
            CopyBlockLeft.step_done sep2 outerSep
              (Tape.mk₁ (copyWithSep sep2 (x :: xs) ++ outerSep :: suffix))⟩
      exact ⟨Part.dom_iff_mem.mpr ⟨_, h_mem⟩, fun h =>
        (Part.mem_unique (Part.get_mem h) h_mem).symm ▸ rfl⟩

/-- The general copy-with-sep operation is block-realizable.

This is the blank-delimited specialization of `tm0_copyWithSep_blockSep`. -/
theorem tm0_copyWithSep_block {Γ : Type} [Inhabited Γ] [DecidableEq Γ] [Fintype Γ]
    {sep2 : Γ} (hsep2 : sep2 ≠ default) :
    TM0RealizesBlock Γ (copyWithSep sep2) :=
  tm0RealizesBlock_of_sep_default (tm0_copyWithSep_blockSep hsep2)

theorem tm0_copyBinaryWithSep_block :
    TM0RealizesBlock ChainΓ copyBinaryWithSep := by
  exact tm0_copyWithSep_block chainConsBottom_ne_default
