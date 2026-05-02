import Mathlib
import Langlib.Automata.Turing.DSL.SplitAtSep

/-! # Decrement-After-Separator Machine

A TM0 machine that decrements the sub-block AFTER the first
`chainConsBottom` separator, preserving the prefix.
Identity when no separator is present.
-/

open Turing PartrecToTM2 TM2to1

inductive DecAfterSepSt where
  | skip | borrow | borrowMv | absorbed | rewind | done
  deriving DecidableEq

noncomputable instance : Inhabited DecAfterSepSt := ⟨.skip⟩

instance : Fintype DecAfterSepSt where
  elems := {.skip, .borrow, .borrowMv, .absorbed, .rewind, .done}
  complete := by intro x; cases x <;> simp

noncomputable def decAfterSepMachine : @TM0.Machine ChainΓ DecAfterSepSt ⟨.skip⟩ :=
  fun q a =>
    match q with
    | .skip =>
      if a = chainConsBottom then some (.borrow, .move Dir.right)
      else if a = default then some (.rewind, .move Dir.left)
      else some (.skip, .move Dir.right)
    | .borrow =>
      if a = γ'ToChainΓ Γ'.bit1 then some (.absorbed, .write (γ'ToChainΓ Γ'.bit0))
      else if a = γ'ToChainΓ Γ'.bit0 then some (.borrowMv, .write (γ'ToChainΓ Γ'.bit1))
      else some (.absorbed, .write a)
    | .borrowMv => some (.borrow, .move Dir.right)
    | .absorbed => some (.rewind, .move Dir.left)
    | .rewind =>
      if a = default then some (.done, .move Dir.right)
      else some (.rewind, .move Dir.left)
    | .done => none

/-! ### Rewind -/

theorem decAfterSep_rewind_collect (revLeft : List ChainΓ)
    (hrevLeft : ∀ g ∈ revLeft, g ≠ default) (acc : List ChainΓ) :
    Reaches (TM0.step decAfterSepMachine)
      ⟨.rewind, ⟨revLeft.headI, ListBlank.mk revLeft.tail, ListBlank.mk acc⟩⟩
      ⟨.rewind, ⟨default, ListBlank.mk [], ListBlank.mk (revLeft.reverse ++ acc)⟩⟩ := by
  induction' revLeft with a revLeft ih generalizing acc
  · exact .refl
  · convert (ih (fun g hg => hrevLeft g (List.mem_cons_of_mem _ hg)) (a :: acc)).head _ using 1
    · simp [List.reverse_cons]
    · unfold TM0.step decAfterSepMachine; aesop

theorem decAfterSep_rewind_final (rightList : List ChainΓ) :
    Reaches (TM0.step decAfterSepMachine)
      ⟨.rewind, ⟨default, ListBlank.mk [], ListBlank.mk rightList⟩⟩
      ⟨.done, Tape.mk₁ rightList⟩ := by
  -- Apply the definition of `Reaches` to show that the machine reaches the done state.
  apply Relation.ReflTransGen.single
  simp [TM0.step, decAfterSepMachine];
  -- By definition of `ListBlank.mk`, we know that `ListBlank.mk rightList` is equivalent to `rightList`.
  simp [Tape.move, Tape.mk₁, Tape.mk₂, Tape.mk'];
  -- By definition of `ListBlank.mk`, we know that `ListBlank.mk [default]` is equal to `ListBlank.mk []`.
  apply ListBlank.ext; simp [ListBlank.mk];
  intro i; induction i <;> simp +decide [ *, ListBlank.nth ] ;

theorem decAfterSep_rewind_loop (revLeft : List ChainΓ)
    (hrevLeft : ∀ g ∈ revLeft, g ≠ default) (rightList : List ChainΓ) :
    Reaches (TM0.step decAfterSepMachine)
      ⟨.rewind, ⟨revLeft.headI, ListBlank.mk revLeft.tail, ListBlank.mk rightList⟩⟩
      ⟨.done, Tape.mk₁ (revLeft.reverse ++ rightList)⟩ :=
  (decAfterSep_rewind_collect revLeft hrevLeft rightList).trans (decAfterSep_rewind_final _)

/-! ### Skip phase -/

theorem decAfterSep_skip_loop (prefix_ : List ChainΓ) (rest : List ChainΓ)
    (hprefix : ∀ c ∈ prefix_, c ≠ chainConsBottom)
    (hprefix_nd : ∀ c ∈ prefix_, c ≠ default)
    (revL : List ChainΓ) :
    Reaches (TM0.step decAfterSepMachine)
      ⟨.skip, ⟨(prefix_ ++ rest).headI, ListBlank.mk revL,
              ListBlank.mk (prefix_ ++ rest).tail⟩⟩
      ⟨.skip, ⟨rest.headI, ListBlank.mk (prefix_.reverse ++ revL),
              ListBlank.mk rest.tail⟩⟩ := by
  have hind : ∀ (c : ChainΓ) (l r : List ChainΓ) (revL : List ChainΓ),
      c ≠ chainConsBottom →
      c ≠ default →
      Reaches (TM0.step decAfterSepMachine)
        ⟨DecAfterSepSt.skip, ⟨(c :: l ++ r).headI, ListBlank.mk revL, ListBlank.mk (c :: l ++ r).tail⟩⟩
        ⟨DecAfterSepSt.skip, ⟨(l ++ r).headI, ListBlank.mk (c :: revL), ListBlank.mk (l ++ r).tail⟩⟩ := by
          intros c l r revL hc hc'; exact (by
          refine' Relation.ReflTransGen.single _;
          simp +decide [ TM0.step, decAfterSepMachine ];
          exact ⟨ _, by rw [ if_neg hc, if_neg hc' ], by cases l <;> rfl ⟩);
  induction' prefix_ with c l ih generalizing revL <;> simp +decide [ * ];
  · constructor;
  · specialize hind c l rest revL ; simp_all +decide [ List.mem_cons ];
    exact hind.trans ( ih _ )

/-! ### Borrow step lemmas -/

theorem decAfterSep_borrow_bit1 (rest suffix revLeft : List ChainΓ)
    (hrevLeft : ∀ g ∈ revLeft, g ≠ default) :
    Reaches (TM0.step decAfterSepMachine)
      ⟨.borrow, ⟨γ'ToChainΓ Γ'.bit1, ListBlank.mk revLeft,
                  ListBlank.mk (rest ++ default :: suffix)⟩⟩
      ⟨.done, Tape.mk₁ (revLeft.reverse ++ γ'ToChainΓ Γ'.bit0 :: rest ++ default :: suffix)⟩ := by
  have := @binPredRaw_borrow_bit1;
  convert this rest suffix revLeft hrevLeft using 1;
  constructor <;> intro h;
  · exact this rest suffix revLeft hrevLeft;
  · convert Relation.ReflTransGen.trans _ _;
    exact ⟨ DecAfterSepSt.rewind, ⟨ revLeft.headI, ListBlank.mk revLeft.tail, ListBlank.mk ( γ'ToChainΓ Γ'.bit0 :: rest ++ default :: suffix ) ⟩ ⟩;
    · convert Relation.ReflTransGen.head _ _;
      exact ⟨ DecAfterSepSt.absorbed, ⟨ γ'ToChainΓ Γ'.bit0, ListBlank.mk revLeft, ListBlank.mk ( rest ++ default :: suffix ) ⟩ ⟩;
      · cases revLeft <;> aesop;
      · convert Relation.ReflTransGen.single _;
        cases revLeft <;> aesop;
    · convert decAfterSep_rewind_loop revLeft hrevLeft ( γ'ToChainΓ Γ'.bit0 :: rest ++ default :: suffix ) using 1;
      simp +decide [ List.append_assoc ]

theorem decAfterSep_borrow_bit0_step (rest suffix revLeft : List ChainΓ) :
    Reaches (TM0.step decAfterSepMachine)
      ⟨.borrow, ⟨γ'ToChainΓ Γ'.bit0, ListBlank.mk revLeft,
                  ListBlank.mk (rest ++ default :: suffix)⟩⟩
      ⟨.borrow, ⟨(rest ++ default :: suffix).headI,
                  ListBlank.mk (γ'ToChainΓ Γ'.bit1 :: revLeft),
                  ListBlank.mk (rest ++ default :: suffix).tail⟩⟩ := by
  convert Relation.ReflTransGen.head _ _ using 1;
  exact ⟨ DecAfterSepSt.borrowMv, ⟨ γ'ToChainΓ Γ'.bit1, ListBlank.mk revLeft, ListBlank.mk ( rest ++ default :: suffix ) ⟩ ⟩;
  · unfold decAfterSepMachine; aesop;
  · apply_rules [ Relation.ReflTransGen.single ]

/-! ### Borrow phase -/

theorem decAfterSep_borrow_aux (block suffix : List ChainΓ) (revLeft : List ChainΓ)
    (hblock : ∀ g ∈ block, g ≠ default)
    (hsuffix : ∀ g ∈ suffix, g ≠ default)
    (hrevLeft : ∀ g ∈ revLeft, g ≠ default) :
    Reaches (TM0.step decAfterSepMachine)
      ⟨.borrow, ⟨(block ++ default :: suffix).headI,
                  ListBlank.mk revLeft,
                  ListBlank.mk (block ++ default :: suffix).tail⟩⟩
      ⟨.done, Tape.mk₁ (revLeft.reverse ++ binPredRaw block ++ default :: suffix)⟩ := by
  induction' block with c block ih generalizing revLeft suffix
  · -- base case: block = []
    simp only [binPredRaw, List.nil_append, List.append_nil]
    have : (default :: suffix).headI = (default : ChainΓ) := rfl
    have : (default :: suffix).tail = suffix := rfl
    simp only [‹(default :: suffix).headI = default›, ‹(default :: suffix).tail = suffix›]
    have h1 : TM0.step decAfterSepMachine ⟨DecAfterSepSt.borrow, ⟨default, ListBlank.mk revLeft, ListBlank.mk suffix⟩⟩ = some ⟨DecAfterSepSt.absorbed, ⟨default, ListBlank.mk revLeft, ListBlank.mk suffix⟩⟩ := by
      simp +decide [TM0.step, decAfterSepMachine, γ'ToChainΓ]
    have h2 : TM0.step decAfterSepMachine ⟨DecAfterSepSt.absorbed, ⟨default, ListBlank.mk revLeft, ListBlank.mk suffix⟩⟩ = some ⟨DecAfterSepSt.rewind, ⟨revLeft.headI, ListBlank.mk revLeft.tail, ListBlank.mk (default :: suffix)⟩⟩ := by
      cases revLeft <;> rfl
    exact Relation.ReflTransGen.head h1 (Relation.ReflTransGen.head h2 (decAfterSep_rewind_loop revLeft hrevLeft (default :: suffix)))
  · -- inductive case: block = c :: block
    have hc_nd := hblock c List.mem_cons_self
    have hblock' : ∀ g ∈ block, g ≠ default := fun g hg => hblock g (List.mem_cons_of_mem _ hg)
    simp only [List.cons_append, List.headI_cons, List.tail_cons]
    by_cases hc : c = γ'ToChainΓ Γ'.bit1
    · subst hc; simp [binPredRaw]
      convert decAfterSep_borrow_bit1 block suffix revLeft hrevLeft using 2
      simp [List.append_assoc]
    · by_cases hc' : c = γ'ToChainΓ Γ'.bit0
      · subst hc'; simp +decide [binPredRaw, hc]
        have h_step := decAfterSep_borrow_bit0_step block suffix revLeft
        have h_ih := ih suffix (γ'ToChainΓ Γ'.bit1 :: revLeft) hblock' hsuffix
            (by intro g hg; rcases List.mem_cons.mp hg with rfl | hg
                · simp +decide [γ'ToChainΓ]
                · exact hrevLeft g hg)
        convert h_step.trans h_ih using 1
        simp [List.reverse_cons]
      · -- non-bit cell: no-op
        simp [binPredRaw, hc, hc']
        have h1 : TM0.step decAfterSepMachine ⟨DecAfterSepSt.borrow, ⟨c, ListBlank.mk revLeft, ListBlank.mk (block ++ default :: suffix)⟩⟩ = some ⟨DecAfterSepSt.absorbed, ⟨c, ListBlank.mk revLeft, ListBlank.mk (block ++ default :: suffix)⟩⟩ := by
          simp +decide [TM0.step, decAfterSepMachine, hc, hc']
        have h2 : TM0.step decAfterSepMachine ⟨DecAfterSepSt.absorbed, ⟨c, ListBlank.mk revLeft, ListBlank.mk (block ++ default :: suffix)⟩⟩ = some ⟨DecAfterSepSt.rewind, ⟨revLeft.headI, ListBlank.mk revLeft.tail, ListBlank.mk (c :: block ++ default :: suffix)⟩⟩ := by
          cases revLeft <;> rfl
        exact Relation.ReflTransGen.head h1 (Relation.ReflTransGen.head h2 (decAfterSep_rewind_loop revLeft hrevLeft (c :: block ++ default :: suffix)))

/-! ### Full correctness -/

theorem decAfterSep_full_reaches (block suffix : List ChainΓ)
    (hblock : ∀ g ∈ block, g ≠ default)
    (hsuffix : ∀ g ∈ suffix, g ≠ default)
    (hresult : ∀ g ∈ decAfterSep block, g ≠ default) :
    Reaches (TM0.step decAfterSepMachine)
      (TM0.init (block ++ default :: suffix))
      ⟨DecAfterSepSt.done,
       Tape.mk₁ (decAfterSep block ++ default :: suffix)⟩ := by
  by_cases h : chainConsBottom ∈ block;
  · obtain ⟨l, r, hl⟩ : ∃ l r, block = l ++ [chainConsBottom] ++ r ∧ (∀ g ∈ l, g ≠ chainConsBottom) := by
      obtain ⟨l, r, hl⟩ : ∃ l r, block = l ++ chainConsBottom :: r ∧ (∀ g ∈ l, g ≠ chainConsBottom) := by
        exact ⟨ List.takeWhile ( fun g => g ≠ chainConsBottom ) block, List.dropWhile ( fun g => g ≠ chainConsBottom ) block |> List.tail!, by
          have h_split : ∀ {l : List ChainΓ}, chainConsBottom ∈ l → l = List.takeWhile (fun g => g ≠ chainConsBottom) l ++ chainConsBottom :: (List.dropWhile (fun g => g ≠ chainConsBottom) l).tail! := by
            intros l hl; induction' l with hd tl ih <;> simp +decide [ List.takeWhile, List.dropWhile ] at *;
            by_cases h : hd = chainConsBottom <;> simp +decide [ h ] at hl ⊢;
            exact ih <| hl.resolve_left <| Ne.symm h;
          exact h_split h, by
          intro g hg; have := List.mem_takeWhile_imp hg; aesop; ⟩;
      exact ⟨ l, r, by simpa using hl.1, hl.2 ⟩;
    -- Apply the skip loop lemma to process the prefix `l`.
    have h_skip : Reaches (TM0.step decAfterSepMachine)
      ⟨.skip, ⟨(l ++ [chainConsBottom] ++ r ++ default :: suffix).headI,
               ListBlank.mk [],
               ListBlank.mk (l ++ [chainConsBottom] ++ r ++ default :: suffix).tail⟩⟩
      ⟨.skip, ⟨(chainConsBottom :: r ++ default :: suffix).headI,
               ListBlank.mk l.reverse,
               ListBlank.mk (chainConsBottom :: r ++ default :: suffix).tail⟩⟩ := by
                 have := decAfterSep_skip_loop l ( chainConsBottom :: r ++ default :: suffix ) hl.2 ( by
                   exact fun g hg => hblock g <| hl.1.symm ▸ List.mem_append_left _ ( List.mem_append_left _ hg ) ) []
                 generalize_proofs at *;
                 simpa using this;
    -- Apply the borrow lemma to process the rest of the block.
    have h_borrow : Reaches (TM0.step decAfterSepMachine)
      ⟨.borrow, ⟨(r ++ default :: suffix).headI,
                 ListBlank.mk (chainConsBottom :: l.reverse),
                 ListBlank.mk (r ++ default :: suffix).tail⟩⟩
      ⟨.done, Tape.mk₁ (l.reverse.reverse ++ [chainConsBottom] ++ binPredRaw r ++ default :: suffix)⟩ := by
        convert decAfterSep_borrow_aux r suffix ( chainConsBottom :: l.reverse ) _ _ _ using 1;
        · simp +decide [ List.reverse_cons ];
        · grind;
        · assumption;
        · grind;
    convert h_skip.trans _ using 1;
    · cases l <;> aesop;
    · convert h_borrow.head _ using 1;
      · unfold decAfterSep; simp +decide [ hl ] ;
        rw [ show splitAtConsBottom ( l ++ chainConsBottom :: r ) = ( l, r ) from ?_ ];
        convert splitAtConsBottom_general l r _ using 1;
        · simp +decide [ List.append_assoc ];
        · exact hl.2;
      · simp +decide [ decAfterSepMachine ];
        cases r <;> simp +decide [ TM0.step ];
        · exact ⟨ _, rfl, by rfl ⟩;
        · exact ⟨ _, rfl, rfl ⟩;
  · unfold decAfterSep; simp_all +decide ;
    have h_skip : Reaches (TM0.step decAfterSepMachine) ⟨.skip, ⟨(block ++ default :: suffix).headI, ListBlank.mk [], ListBlank.mk (block ++ default :: suffix).tail⟩⟩ ⟨.skip, ⟨default, ListBlank.mk block.reverse, ListBlank.mk suffix⟩⟩ := by
      convert decAfterSep_skip_loop block ( default :: suffix ) _ _ _ using 1 <;> norm_num [ hblock, hsuffix ];
      · exact fun c hc => fun hc' => h <| hc'.symm ▸ hc;
      · assumption;
    have h_rewind : Reaches (TM0.step decAfterSepMachine) ⟨.skip, ⟨default, ListBlank.mk block.reverse, ListBlank.mk suffix⟩⟩ ⟨.rewind, ⟨block.reverse.headI, ListBlank.mk block.reverse.tail, ListBlank.mk (default :: suffix)⟩⟩ := by
      constructor;
      constructor;
      cases block.reverse <;> aesop;
    convert h_skip.trans h_rewind |> Relation.ReflTransGen.trans <| decAfterSep_rewind_loop _ _ _ using 1;
    · rw [ List.reverse_reverse ];
    · exact fun g hg => hblock g <| List.mem_reverse.mp hg

theorem decAfterSep_step_done (T : Tape ChainΓ) :
    TM0.step decAfterSepMachine ⟨DecAfterSepSt.done, T⟩ = none := by
  simp [TM0.step, decAfterSepMachine]

theorem tm0_decAfterSep_block : TM0RealizesBlock ChainΓ decAfterSep := by
  refine ⟨DecAfterSepSt, inferInstance, inferInstance, decAfterSepMachine, ?_⟩
  intro block suffix hblock hsuffix hresult
  have h_reaches := decAfterSep_full_reaches block suffix hblock hsuffix hresult
  constructor
  · exact Part.dom_iff_mem.mpr ⟨_, Turing.mem_eval.mpr ⟨h_reaches, decAfterSep_step_done _⟩⟩
  · intro h
    exact (Part.mem_unique (Part.get_mem h)
      (Turing.mem_eval.mpr ⟨h_reaches, decAfterSep_step_done _⟩)).symm ▸ rfl