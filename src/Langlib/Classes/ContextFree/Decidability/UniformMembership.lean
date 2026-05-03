import Mathlib
import Langlib.Grammars.ContextFree.Definition
import Langlib.Grammars.ContextFree.Toolbox
import Langlib.Classes.ContextFree.Basics.EncodedCFG
import Langlib.Classes.ContextFree.Basics.Splitting
import Langlib.Classes.ContextFree.Closure.PrefixBonus
import Langlib.Classes.ContextFree.Decidability.Helper
import Langlib.Utilities.PrimrecHelpers

/-! # Uniform Membership Check for Encoded Context-Free Grammars -/

open List

variable {T : Type} [DecidableEq T]

/-! ## Saturation Algorithm Definitions -/

/-- Match a rule's RHS against a substring of word `w`, starting from position `startPos`.
    Returns all possible end positions after matching the full RHS. -/
def matchRHS (w : List T) (nc : ℕ) (S : List (ℕ × ℕ × ℕ))
    (rhs : List (ℕ ⊕ T)) (startPos : ℕ) : List ℕ :=
  rhs.foldl (fun positions sym =>
    positions.flatMap fun pos =>
      match sym with
      | .inr t =>
        match w[pos]? with
        | some c => if c == t then [pos + 1] else []
        | none => []
      | .inl k =>
        (S.filter fun (n, s, _) => decide (n = k % nc ∧ s = pos)).map fun (_, _, e) => e
  ) [startPos]

/-- One step of the saturation. -/
def satStep (nc : ℕ) (rules : List (ℕ × List (ℕ ⊕ T))) (w : List T)
    (S : List (ℕ × ℕ × ℕ)) : List (ℕ × ℕ × ℕ) :=
  rules.foldl (fun S' (rule : ℕ × List (ℕ ⊕ T)) =>
    (range (w.length + 1)).foldl (fun S'' (startPos : ℕ) =>
      (matchRHS w nc S rule.2 startPos).foldl (fun S''' endPos =>
        let triple := (rule.1 % nc, startPos, endPos)
        if decide (triple ∈ S''') then S''' else S''' ++ [triple]
      ) S''
    ) S'
  ) S

/-- Iterate the saturation step. -/
def satFixpoint (nc : ℕ) (rules : List (ℕ × List (ℕ ⊕ T))) (w : List T)
    (steps : ℕ) : List (ℕ × ℕ × ℕ) :=
  (satStep nc rules w)^[steps] []

/-- Check membership of word `w` in the language of encoded CFG `G`. -/
def checkMembershipEncoded [Fintype T] (p : EncodedCFG T × List T) : Bool :=
  let G := p.1
  let w := p.2
  let nc := G.ntCount
  let rules := G.rawRules
  let bound := nc * (w.length + 1) * (w.length + 1) + 1
  let S := satFixpoint nc rules w bound
  decide ((G.initialIdx % nc, 0, w.length) ∈ S)

/-! ## Monotonicity -/

private lemma foldl_append_mono {α β : Type*} [DecidableEq β]
    (f : List β → α → List β) (hf : ∀ S a, ∀ t ∈ S, t ∈ f S a)
    (l : List α) (S : List β) :
    ∀ t ∈ S, t ∈ l.foldl f S := by
  induction l generalizing S with
  | nil => simp
  | cons h tl ih => intro t ht; simp [List.foldl]; exact ih _ _ (hf S h t ht)

lemma satStep_mono (nc : ℕ) (rules : List (ℕ × List (ℕ ⊕ T))) (w : List T)
    (S : List (ℕ × ℕ × ℕ)) :
    ∀ t ∈ S, t ∈ satStep nc rules w S := by
  unfold satStep; simp +decide
  induction' rules using List.reverseRecOn with rules rule ih <;> simp_all +decide [ List.foldl ]
  intro a a_1 b hab; exact foldl_append_mono _ (fun S startPos => by
    induction' ( matchRHS w nc _ rule.2 startPos ) using List.reverseRecOn with endPos endPos ih <;> simp_all +decide [ List.foldl ]
    grind +ring) _ _ _ (ih a a_1 b hab)

lemma satFixpoint_mono (nc : ℕ) (rules : List (ℕ × List (ℕ ⊕ T))) (w : List T)
    (n m : ℕ) (h : n ≤ m) :
    ∀ t ∈ satFixpoint nc rules w n, t ∈ satFixpoint nc rules w m := by
  induction' h with m hm ih
  · exact fun t ht => ht
  · unfold satFixpoint at *
    exact fun t ht => by simpa only [Function.iterate_succ_apply'] using satStep_mono nc rules w _ _ (ih _ ht)

/-! ## Soundness Lemmas -/

/-- Property that a triple represents a valid derivation. -/
def TripleDerives (G : EncodedCFG T) (w : List T) (nt i j : ℕ) : Prop :=
  ∃ (hnt : nt < G.ntCount),
    i ≤ j ∧ j ≤ w.length ∧
    CF_derives G.toCFGrammar [symbol.nonterminal ⟨nt, hnt⟩]
      ((w.drop i |>.take (j - i)).map symbol.terminal)

/-- Property that all triples in a set represent valid derivations. -/
def AllSound (G : EncodedCFG T) (w : List T) (S : List (ℕ × ℕ × ℕ)) : Prop :=
  ∀ nt i j, (nt, i, j) ∈ S → TripleDerives G w nt i j

/-
Key soundness lemma for matchRHS: if matchRHS returns endPos, then the RHS
    derives the corresponding substring.
-/
lemma matchRHS_sound (G : EncodedCFG T) (w : List T)
    (S : List (ℕ × ℕ × ℕ)) (hS : AllSound G w S)
    (rhs : List (ℕ ⊕ T)) (startPos endPos : ℕ)
    (hstart : startPos ≤ w.length)
    (hmatch : endPos ∈ matchRHS w G.ntCount S rhs startPos) :
    startPos ≤ endPos ∧ endPos ≤ w.length ∧
    CF_derives G.toCFGrammar (rhs.map (EncodedCFG.toSymbol G))
      ((w.drop startPos |>.take (endPos - startPos)).map symbol.terminal) := by
  revert hmatch;
  induction' rhs using List.reverseRecOn with rhs ih generalizing startPos endPos;
  · simp +decide [ matchRHS ];
    rintro rfl; simp +decide [ hstart ];
    constructor;
  · cases ih <;> simp +decide [ matchRHS ] at *;
    · intro x hx hxS;
      rename_i k hk;
      obtain ⟨ h₁, h₂, h₃ ⟩ := hk startPos x hstart hx;
      obtain ⟨ h₄, h₅, h₆ ⟩ := hS _ _ _ hxS;
      refine' ⟨ by linarith, h₆.1, _ ⟩;
      convert CF_deri_with_postfix _ h₃ |> CF_deri_of_deri_deri <| CF_deri_with_prefix _ h₆.2 using 1;
      rw [ show endPos - startPos = ( x - startPos ) + ( endPos - x ) by omega, List.take_add ];
      simp +decide [ List.drop_drop, h₁ ];
    · rename_i h;
      intro x hx hx';
      rcases hstart' : w[x]? with ( _ | c ) <;> simp +decide [ hstart' ] at hx' ⊢;
      rcases h startPos x hstart hx with ⟨ hx₁, hx₂, hx₃ ⟩ ; simp +decide [ hx', hx₁, hx₂, hx₃ ];
      refine' ⟨ Nat.le_succ_of_le hx₁, lt_of_le_of_ne hx₂ _, _ ⟩;
      · rintro rfl; simp +decide at hstart';
      · convert CF_deri_with_postfix _ hx₃ using 1;
        rw [ Nat.sub_add_comm hx₁ ];
        rw [ List.take_add_one ];
        simp +decide [ List.getElem?_eq_getElem, hx₁, hx₂, hstart' ];
        exact hx'.1.symm ▸ rfl

/-
Characterization of elements in satStep: either in S or newly derived.
-/
lemma mem_satStep_iff (nc : ℕ) (rules : List (ℕ × List (ℕ ⊕ T))) (w : List T)
    (S : List (ℕ × ℕ × ℕ)) (nt i j : ℕ) :
    (nt, i, j) ∈ satStep nc rules w S →
    (nt, i, j) ∈ S ∨
    ∃ rule ∈ rules, ∃ startPos ≤ w.length,
      nt = rule.1 % nc ∧ i = startPos ∧
      j ∈ matchRHS w nc S rule.2 startPos := by
  unfold satStep;
  induction' rules using List.reverseRecOn with rules rule ih;
  · grind;
  · simp +zetaDelta at *;
    intro h;
    by_cases h' : (nt, i, j) ∈ foldl (fun S' rule => foldl (fun S'' startPos => foldl (fun S''' endPos => if (rule.1 % nc, startPos, endPos) ∈ S''' then S''' else S''' ++ [(rule.1 % nc, startPos, endPos)]) S'' (matchRHS w nc S rule.2 startPos)) S' (range (w.length + 1))) S rules;
    · grind;
    · contrapose! h;
      intro H;
      have h_foldl : ∀ (S' : List (ℕ × ℕ × ℕ)) (startPos : ℕ), startPos ≤ w.length → (nt, i, j) ∈ foldl (fun S''' endPos => if (rule.1 % nc, startPos, endPos) ∈ S''' then S''' else S''' ++ [(rule.1 % nc, startPos, endPos)]) S' (matchRHS w nc S rule.2 startPos) → (nt, i, j) ∈ S' ∨ (nt = rule.1 % nc ∧ i = startPos ∧ j ∈ matchRHS w nc S rule.2 startPos) := by
        intros S' startPos hstartPos hfoldl;
        have h_foldl : ∀ (S' : List (ℕ × ℕ × ℕ)) (endPos : ℕ), (nt, i, j) ∈ foldl (fun S''' endPos => if (rule.1 % nc, startPos, endPos) ∈ S''' then S''' else S''' ++ [(rule.1 % nc, startPos, endPos)]) S' [endPos] → (nt, i, j) ∈ S' ∨ (nt = rule.1 % nc ∧ i = startPos ∧ j = endPos) := by
          grind;
        have h_foldl : ∀ (S' : List (ℕ × ℕ × ℕ)) (endPos : List ℕ), (nt, i, j) ∈ foldl (fun S''' endPos => if (rule.1 % nc, startPos, endPos) ∈ S''' then S''' else S''' ++ [(rule.1 % nc, startPos, endPos)]) S' endPos → (nt, i, j) ∈ S' ∨ (nt = rule.1 % nc ∧ i = startPos ∧ j ∈ endPos) := by
          intros S' endPos hfoldl;
          induction' endPos using List.reverseRecOn with endPos endPos ih;
          · exact Or.inl hfoldl;
          · grind;
        exact h_foldl S' _ hfoldl;
      have h_foldl : ∀ (S' : List (ℕ × ℕ × ℕ)) (startPos : ℕ), startPos ≤ w.length → (nt, i, j) ∈ foldl (fun S'' startPos => foldl (fun S''' endPos => if (rule.1 % nc, startPos, endPos) ∈ S''' then S''' else S''' ++ [(rule.1 % nc, startPos, endPos)]) S'' (matchRHS w nc S rule.2 startPos)) S' (range (startPos + 1)) → (nt, i, j) ∈ S' ∨ ∃ startPos' ≤ startPos, (nt = rule.1 % nc ∧ i = startPos' ∧ j ∈ matchRHS w nc S rule.2 startPos') := by
        intros S' startPos hstartPos hfoldl;
        induction' startPos with startPos ih generalizing S';
        · grind +extAll;
        · rw [ List.range_succ ] at hfoldl;
          grind;
      grind

/-
satStep preserves soundness and newly added triples are also sound.
-/
lemma satStep_sound (G : EncodedCFG T) (w : List T) (S : List (ℕ × ℕ × ℕ))
    (hS : AllSound G w S) :
    AllSound G w (satStep G.ntCount G.rawRules w S) := by
  intro nt i j hij;
  cases mem_satStep_iff G.ntCount G.rawRules w S nt i j hij <;> simp_all +decide [ AllSound ];
  obtain ⟨ a, b, h₁, h₂, rfl, h₃ ⟩ := ‹_›;
  have := matchRHS_sound G w S hS b i j h₂ h₃;
  refine' ⟨ _, _, _, _ ⟩;
  exact Nat.mod_lt _ ( EncodedCFG.ntCount_pos _ );
  · linarith;
  · linarith;
  · have h_rule : (G.toNT a, b.map G.toSymbol) ∈ G.toCFGrammar.rules := by
      unfold EncodedCFG.toCFGrammar; aesop;
    have h_rule : CF_transforms G.toCFGrammar [symbol.nonterminal (G.toNT a)] (b.map G.toSymbol) := by
      use (G.toNT a, b.map G.toSymbol), [], [] ; aesop;
    exact CF_deri_of_tran_deri h_rule this.2.2

/-
satFixpoint produces only sound triples.
-/
lemma satFixpoint_sound (G : EncodedCFG T) (w : List T) (steps : ℕ) :
    AllSound G w (satFixpoint G.ntCount G.rawRules w steps) := by
  induction' steps with n ih <;> simp_all +decide [ satFixpoint ];
  · exact fun _ _ _ _ => by contradiction;
  · convert satStep_sound G w _ ih using 1;
    exact Function.iterate_succ_apply' _ _ _

/-! ## matchRHS structural lemmas -/

/-- The single-symbol matching step. -/
def matchOneSym (w : List T) (nc : ℕ) (S : List (ℕ × ℕ × ℕ))
    (sym : ℕ ⊕ T) (pos : ℕ) : List ℕ :=
  match sym with
  | .inr t =>
    match w[pos]? with
    | some c => if c == t then [pos + 1] else []
    | none => []
  | .inl k =>
    (S.filter fun (n, s, _) => decide (n = k % nc ∧ s = pos)).map fun (_, _, e) => e

/-
matchRHS foldl distributes over append of positions.
-/
lemma matchRHS_foldl_append (w : List T) (nc : ℕ) (S : List (ℕ × ℕ × ℕ))
    (rhs : List (ℕ ⊕ T)) (p1 p2 : List ℕ) :
    rhs.foldl (fun positions sym => positions.flatMap (matchOneSym w nc S sym))
      (p1 ++ p2) =
    rhs.foldl (fun positions sym => positions.flatMap (matchOneSym w nc S sym)) p1 ++
    rhs.foldl (fun positions sym => positions.flatMap (matchOneSym w nc S sym)) p2 := by
  induction' rhs using List.reverseRecOn with rhs ih;
  · rfl;
  · grind

/-
matchRHS on cons unfolds to single-symbol match followed by matchRHS on tail.
-/
lemma matchRHS_cons (w : List T) (nc : ℕ) (S : List (ℕ × ℕ × ℕ))
    (sym : ℕ ⊕ T) (rest : List (ℕ ⊕ T)) (startPos : ℕ) :
    matchRHS w nc S (sym :: rest) startPos =
    (matchOneSym w nc S sym startPos).flatMap (matchRHS w nc S rest) := by
  -- By definition of `matchRHS`, we can unfold it to show that it applies the step function to each element in the list.
  have h_matchRHS_step : ∀ (l : List (ℕ ⊕ T)) (startPos : ℕ), matchRHS w nc S l startPos = l.foldl (fun positions sym => positions.flatMap (fun pos => matchOneSym w nc S sym pos)) [startPos] := by
    congr! 3;
  induction' rest using List.reverseRecOn with rest ih generalizing startPos <;> simp_all +decide [ matchRHS_foldl_append ];
  · unfold matchRHS; aesop;
  · induction' ( matchOneSym w nc S sym startPos ) using List.reverseRecOn with l ih <;> simp_all +decide [ List.flatMap ]

/-! ## Completeness Lemmas -/

/-
If the RHS of a rule derives a substring, then matchRHS returns the end position.
-/
set_option maxHeartbeats 800000 in
lemma matchRHS_complete (G : EncodedCFG T) (w : List T)
    (S : List (ℕ × ℕ × ℕ))
    (rhs : List (ℕ ⊕ T)) (startPos endPos : ℕ)
    (hstart : startPos ≤ endPos) (hend : endPos ≤ w.length)
    (hder : CF_derives G.toCFGrammar (rhs.map (EncodedCFG.toSymbol G))
      ((w.drop startPos |>.take (endPos - startPos)).map symbol.terminal))
    -- For each nonterminal in rhs, the sub-derivation is captured in S
    (hS_complete : ∀ (k : ℕ), .inl k ∈ rhs →
      ∀ (i j : ℕ), i ≤ j → j ≤ w.length →
        CF_derives G.toCFGrammar [symbol.nonterminal (G.toNT k)]
          ((w.drop i |>.take (j - i)).map symbol.terminal) →
        (k % G.ntCount, i, j) ∈ S) :
    endPos ∈ matchRHS w G.ntCount S rhs startPos := by
  revert hder endPos;
  induction' rhs with sym rhs ih generalizing startPos;
  · intro endPos hstart hend hder
    have h_empty : (List.take (endPos - startPos) (List.drop startPos w)) = [] := by
      have h_empty : ∀ (l : List (symbol T G.toCFGrammar.nt)), CF_derives G.toCFGrammar [] l → l = [] := by
        intro l hl
        induction' hl with l' hl' ih;
        · rfl;
        · cases ‹CF_transforms G.toCFGrammar _ _› ; aesop;
      specialize h_empty _ hder; aesop;
    simp_all +decide [ Nat.sub_eq_iff_eq_add' hstart ];
    grind +locals;
  · intro endPos hstart hend hder;
    -- By definition of `CF_derives`, we can split the derivation into two parts: the derivation of the first symbol and the derivation of the rest.
    obtain ⟨midPos, hmidPos⟩ : ∃ midPos, startPos ≤ midPos ∧ midPos ≤ endPos ∧ CF_derives G.toCFGrammar [G.toSymbol sym] (map symbol.terminal (take (midPos - startPos) (drop startPos w))) ∧ CF_derives G.toCFGrammar (map G.toSymbol rhs) (map symbol.terminal (take (endPos - midPos) (drop midPos w))) := by
      obtain ⟨ u, v, hu, hv, huv ⟩ := head_tail_split _ _ _ hder;
      refine' ⟨ startPos + u.length, _, _, _, _ ⟩;
      · exact Nat.le_add_right _ _;
      · replace huv := congr_arg List.length huv ; simp_all +decide;
        omega;
      · convert hu using 1;
        have h_take : u = map symbol.terminal (take u.length (drop startPos w)) := by
          have h_take_eq : u ++ v = map symbol.terminal (take (endPos - startPos) (drop startPos w)) := huv
          have h_take_len : u.length ≤ endPos - startPos := by
            replace h_take_eq := congr_arg List.length h_take_eq ; simp_all +decide;
            replace huv := congr_arg List.length huv ; simp_all +decide;
            exact le_trans ( Nat.le_add_right _ _ ) ( huv.le.trans ( min_le_left _ _ ) )
          have h_take_eq : u = take u.length (map symbol.terminal (take (endPos - startPos) (drop startPos w))) := by
            rw [ ← h_take_eq, List.take_append_of_le_length ] <;> norm_num;
          convert h_take_eq using 1;
          rw [ ← List.map_take ];
          grind;
        simpa using h_take.symm;
      · convert hv using 1;
        rw [ show endPos - ( startPos + u.length ) = ( endPos - startPos ) - u.length by rw [ Nat.sub_sub ] ];
        replace huv := congr_arg ( fun x => x.drop u.length ) huv ; simp_all +decide [ List.drop_append ];
        rw [ List.drop_take ];
        rw [ List.drop_drop ];
    -- By definition of `matchOneSym`, we know that `midPos ∈ matchOneSym w G.ntCount S sym startPos`.
    have hmidPos_in_matchOneSym : midPos ∈ matchOneSym w G.ntCount S sym startPos := by
      cases sym <;> simp_all +decide [ matchOneSym ];
      · exact hS_complete.1 _ _ hmidPos.1 ( by linarith ) hmidPos.2.2.1;
      · cases h : w[startPos]? <;> simp_all +decide [ CF_derives ];
        · cases h.eq_or_lt <;> first | linarith | simp_all +decide [ List.drop_eq_nil_of_le ] ;
          have := hmidPos.2.2.1;
          have := this.cases_head; simp_all +decide [ CF_transforms ] ;
          rcases this with ⟨ a, b, x, y, h, h' ⟩ ; rcases x with ( _ | ⟨ _, _ ⟩ ) <;> simp_all +decide [ List.append_assoc ] ;
          cases h.2.1;
        · rcases k : midPos - startPos with ( _ | _ | k ) <;> simp_all +decide [ List.take ];
          · have := hmidPos.2.2.1; simp_all +decide [ CF_transforms ] ;
            contrapose! this;
            intro h;
            have := h.cases_head; simp_all +decide [ CF_transforms ] ;
            rcases this with ⟨ a, b, x, y, h, h' ⟩ ; rcases x with ( _ | ⟨ _, _ ⟩ ) <;> simp_all +decide [ List.append_assoc ] ;
            cases h.2.1;
          · rw [ Nat.sub_eq_iff_eq_add ] at k <;> try linarith;
            have := hmidPos.2.2.1;
            have := this.cases_head; simp_all +decide [ CF_transforms ] ;
            cases this <;> simp_all +decide [ add_comm, List.take_add_one ];
            · cases ‹_› ; aesop;
            · rename_i h; rcases h with ⟨ a, b, x, y, h₁, h₂ ⟩ ; rcases x with ( _ | ⟨ x, x ⟩ ) <;> rcases y with ( _ | ⟨ y, y ⟩ ) <;> simp_all +decide [ List.append_assoc ] ;
              cases h₁.2;
          · have := hmidPos.2.2.1.cases_head; simp_all +decide [ CF_transforms ] ;
            rcases this with ( h | ⟨ a, b, x, y, h, h' ⟩ ) <;> simp_all +decide [ List.take ];
            · replace h := congr_arg List.length h ; simp_all +arith +decide;
              omega;
            · cases x <;> cases y <;> simp_all +decide [ List.append_assoc ];
              cases h.2;
    rw [ matchRHS_cons ];
    simp +zetaDelta at *;
    exact ⟨ midPos, hmidPos_in_matchOneSym, ih midPos ( fun k hk i j hij hj => hS_complete k ( Or.inr hk ) i j hij hj ) endPos ( by linarith ) ( by linarith ) hmidPos.2.2.2 ⟩

/-
Helper: if x ∈ l, then after foldl with conditional append, the result contains (f x).
-/
private lemma mem_foldl_cond_append {α : Type*} [DecidableEq α]
    (f : β → α) (l : List β) (init : List α) (x : β) (hx : x ∈ l) :
    f x ∈ l.foldl (fun acc y =>
      if f y ∈ acc then acc else acc ++ [f y]) init := by
  induction l using List.reverseRecOn <;> aesop

/-
If endPos ∈ matchRHS and (lhs, rhs) ∈ rules, then (lhs % nc, startPos, endPos) is
    in satStep nc rules w S, provided startPos ≤ w.length.
-/
lemma mem_satStep_of_matchRHS (nc : ℕ) (rules : List (ℕ × List (ℕ ⊕ T))) (w : List T)
    (S : List (ℕ × ℕ × ℕ)) (lhs : ℕ) (rhs : List (ℕ ⊕ T))
    (hrule : (lhs, rhs) ∈ rules) (startPos endPos : ℕ)
    (hstart : startPos ≤ w.length)
    (hmatch : endPos ∈ matchRHS w nc S rhs startPos) :
    (lhs % nc, startPos, endPos) ∈ satStep nc rules w S := by
  revert hrule;
  induction' rules using List.reverseRecOn with rules' rule ih <;> simp_all +decide [ satStep ];
  intro h;
  cases h <;> simp_all +decide [ List.foldl_append ];
  · apply foldl_append_mono;
    · intro S_1 a t ht; induction' ( matchRHS w nc S rule.2 a ) using List.reverseRecOn with endPos endPos' ih <;> aesop;
    · assumption;
  · have h_foldl_append : ∀ (l : List ℕ) (init : List (ℕ × ℕ × ℕ)), startPos ∈ l → (lhs % nc, startPos, endPos) ∈ List.foldl (fun S'' startPos => List.foldl (fun S''' endPos => if (lhs % nc, startPos, endPos) ∈ S''' then S''' else S''' ++ [(lhs % nc, startPos, endPos)]) S'' (matchRHS w nc S rhs startPos)) init l := by
      intros l init hstartPos
      induction' l using List.reverseRecOn with l' startPos ih generalizing init <;> simp_all +decide [ List.foldl_append ];
      cases hstartPos <;> simp_all +decide [ List.foldl_append ];
      · induction' ( matchRHS w nc S rhs startPos ) using List.reverseRecOn with endPos endPos ih <;> simp_all +decide [ List.foldl_append ];
        grind;
      · have h_foldl_append : ∀ (l : List ℕ) (init : List (ℕ × ℕ × ℕ)), endPos ∈ l → (lhs % nc, startPos, endPos) ∈ List.foldl (fun S''' endPos => if (lhs % nc, startPos, endPos) ∈ S''' then S''' else S''' ++ [(lhs % nc, startPos, endPos)]) init l := by
          intros l init hendPos; induction' l using List.reverseRecOn with l' endPos ih generalizing init <;> simp_all +decide [ List.foldl_append ] ;
          grind;
        exact h_foldl_append _ _ hmatch;
    convert h_foldl_append ( range ( w.length + 1 ) ) _ _ using 1;
    congr! 1;
    · aesop;
    · exact List.mem_range.mpr ( Nat.lt_succ_of_le hstart )

/-! ## Monotonicity of matchRHS in S -/

lemma matchOneSym_mono (w : List T) (nc : ℕ) (S₁ S₂ : List (ℕ × ℕ × ℕ))
    (hS : ∀ t ∈ S₁, t ∈ S₂) (sym : ℕ ⊕ T) (pos : ℕ) :
    ∀ e ∈ matchOneSym w nc S₁ sym pos, e ∈ matchOneSym w nc S₂ sym pos := by
  unfold matchOneSym; aesop;

lemma matchRHS_mono (w : List T) (nc : ℕ) (S₁ S₂ : List (ℕ × ℕ × ℕ))
    (hS : ∀ t ∈ S₁, t ∈ S₂) (rhs : List (ℕ ⊕ T)) (startPos : ℕ) :
    ∀ e ∈ matchRHS w nc S₁ rhs startPos, e ∈ matchRHS w nc S₂ rhs startPos := by
  induction' rhs with sym rhs ih generalizing startPos;
  · unfold matchRHS; aesop;
  · grind +suggestions

/-! ## Additional splitting lemmas -/

lemma terminal_concat_split {N : Type} {u v : List (symbol T N)} {w : List T}
    (h : u ++ v = List.map symbol.terminal w) :
    ∃ w₁ w₂, w = w₁ ++ w₂ ∧ u = List.map symbol.terminal w₁ ∧ v = List.map symbol.terminal w₂ := by
  induction' u with u u_ih generalizing w;
  · exact ⟨ [ ], w, rfl, rfl, h ⟩;
  · cases w <;> simp_all +decide [ List.map ];
    grind

lemma terminal_derives_in_self (g : CF_grammar T) (t : T) (n : ℕ) (w : List T)
    (h : CF_derives_in g n [symbol.terminal t] (List.map symbol.terminal w)) :
    n = 0 ∧ w = [t] := by
  induction' n with n ih generalizing w <;> simp_all +decide [ CF_derives_in ];
  · rcases w with ( _ | ⟨ _, _ | w ⟩ ) <;> aesop;
  · obtain ⟨ w₂, hw₂₁, hw₂₂ ⟩ := h;
    obtain ⟨ u, v, h₁, h₂ ⟩ := hw₂₁;
    cases v <;> cases h₁ <;> aesop

/-
A single nonterminal cannot derive empty list in 0 steps.
-/
omit [DecidableEq T] in
lemma no_terminal_eq_nonterminal (g : CF_grammar T) (nt : g.nt) (w' : List T) :
    [symbol.nonterminal nt] ≠ w'.map symbol.terminal := by
  cases w' <;> aesop

/-
From CF_transforms [nonterminal nt] mid, extract the rule.
-/
omit [DecidableEq T] in
lemma transforms_single_nonterminal (g : CF_grammar T) (nt : g.nt)
    (mid : List (symbol T g.nt))
    (h : CF_transforms g [symbol.nonterminal nt] mid) :
    ∃ rhs, (nt, rhs) ∈ g.rules ∧ mid = rhs := by
  obtain ⟨ r, hr, u, v, hu, hv ⟩ := h;
  cases hr <;> cases u <;> simp_all +decide

/-
Extract raw rule from G.toCFGrammar rule.
-/
omit [DecidableEq T] in
lemma rawRule_of_toCFGrammar_rule (G : EncodedCFG T)
    (nt : Fin G.ntCount) (rhs : List (symbol T (Fin G.ntCount)))
    (hrule : (nt, rhs) ∈ G.toCFGrammar.rules) :
    ∃ (lhs_raw : ℕ) (rhs_raw : List (ℕ ⊕ T)),
      (lhs_raw, rhs_raw) ∈ G.rawRules ∧
      G.toNT lhs_raw = nt ∧
      rhs = rhs_raw.map G.toSymbol := by
  unfold EncodedCFG.toCFGrammar at hrule; aesop;

/-
Key helper: if each nonterminal sub-derivation with < n+1 steps has a bound,
    then the matchRHS result is in some satFixpoint.
-/
lemma matchRHS_in_satFixpoint (G : EncodedCFG T) (w : List T) (n : ℕ)
    (ih_outer : ∀ m < n + 1, ∀ (nt : Fin G.ntCount) (i j : ℕ),
      i ≤ j → j ≤ w.length →
      CF_derives_in G.toCFGrammar m [symbol.nonterminal nt]
        ((w.drop i |>.take (j - i)).map symbol.terminal) →
      ∃ bound, (nt.val, i, j) ∈ satFixpoint G.ntCount G.rawRules w bound)
    (rhs : List (ℕ ⊕ T)) (startPos endPos : ℕ)
    (hstart : startPos ≤ endPos) (hend : endPos ≤ w.length)
    (nder : ℕ) (hnder : nder ≤ n)
    (hder : CF_derives_in G.toCFGrammar nder (rhs.map (EncodedCFG.toSymbol G))
      ((w.drop startPos |>.take (endPos - startPos)).map symbol.terminal)) :
    ∃ bound, endPos ∈ matchRHS w G.ntCount (satFixpoint G.ntCount G.rawRules w bound) rhs startPos := by
  induction' rhs with sym rhs ih generalizing startPos endPos nder;
  · unfold matchRHS; simp +decide [ hstart, hend ] ;
    cases nder <;> simp_all +decide [ CF_derives_in ];
    · omega;
    · obtain ⟨ w₂, hw₂₁, hw₂₂ ⟩ := hder; have := hw₂₁; simp_all +decide [ CF_transforms ] ;
  · obtain ⟨n₁, n₂, hn₁₂, u, v, hu, hv, huv⟩ : ∃ n₁ n₂, n₁ + n₂ ≤ nder ∧ ∃ u v, CF_derives_in G.toCFGrammar n₁ [G.toSymbol sym] u ∧ CF_derives_in G.toCFGrammar n₂ (rhs.map G.toSymbol) v ∧ u ++ v = List.map symbol.terminal (List.take (endPos - startPos) (List.drop startPos w)) := by
      convert head_tail_split_in _ _ _ _ hder using 1;
    obtain ⟨w₁, w₂, hw₁₂, hw₁, hw₂⟩ : ∃ w₁ w₂, (take (endPos - startPos) (drop startPos w)) = w₁ ++ w₂ ∧ u = w₁.map symbol.terminal ∧ v = w₂.map symbol.terminal := by
      exact?;
    rcases sym with ( k | t ) <;> simp_all +decide [ matchRHS_cons ];
    · obtain ⟨bound₁, hbound₁⟩ : ∃ bound₁, (k % G.ntCount, startPos, startPos + w₁.length) ∈ satFixpoint G.ntCount G.rawRules w bound₁ := by
        convert ih_outer n₁ ( by linarith ) ( G.toNT k ) startPos ( startPos + w₁.length ) _ _ _ using 1;
        · exact Nat.le_add_right _ _;
        · replace hw₁₂ := congr_arg List.length hw₁₂ ; simp_all +decide [ List.length_append ];
          omega;
        · convert hu using 1;
          convert congr_arg ( map symbol.terminal ) ( congr_arg ( take w₁.length ) hw₁₂ ) using 1;
          · simp +decide [ List.take_take, List.drop_take ];
            replace hw₁₂ := congr_arg List.length hw₁₂ ; simp_all +decide [ List.length_take, List.length_drop ];
            exact le_trans ( Nat.le_add_right _ _ ) ( hw₁₂ ▸ min_le_right _ _ );
          · simp +decide [ List.take_append ];
      obtain ⟨bound₂, hbound₂⟩ : ∃ bound₂, endPos ∈ matchRHS w G.ntCount (satFixpoint G.ntCount G.rawRules w bound₂) rhs (startPos + w₁.length) := by
        apply ih (startPos + w₁.length) endPos (by
        replace hw₁₂ := congr_arg List.length hw₁₂ ; simp_all +decide [ List.length_append ] ; omega;) (by
        linarith) n₂ (by
        linarith) (by
        convert hv using 1;
        convert congr_arg ( map symbol.terminal ) ( show take ( endPos - ( startPos + w₁.length ) ) ( drop ( startPos + w₁.length ) w ) = w₂ from ?_ ) using 1;
        · simp +decide [ List.map_take, List.map_drop ];
        · convert congr_arg ( fun x => drop w₁.length x ) hw₁₂ using 1;
          · rw [ List.drop_take ];
            rw [ Nat.sub_sub, List.drop_drop ];
          · simp +decide [ List.drop_append ]);
      use max bound₁ bound₂;
      refine' ⟨ startPos + w₁.length, _, _ ⟩;
      · unfold matchOneSym; simp +decide [ hbound₁ ] ;
        exact satFixpoint_mono _ _ _ _ _ ( Nat.le_max_left _ _ ) _ hbound₁;
      · exact matchRHS_mono _ _ _ _ ( fun t ht => satFixpoint_mono _ _ _ _ _ ( le_max_right _ _ ) _ ht ) _ _ _ hbound₂;
    · have := terminal_derives_in_self G.toCFGrammar t n₁ w₁ hu; simp_all +decide [ matchOneSym ] ;
      have h_substring : w[startPos]? = some t := by
        replace hw₁₂ := congr_arg List.head? hw₁₂; simp_all +decide [ List.getElem?_eq_getElem ] ;
        rw [ List.head?_take ] at hw₁₂ ; aesop;
      obtain ⟨ bound, hbound ⟩ := ih ( startPos + 1 ) endPos ( by
        cases hstart.eq_or_lt <;> simp_all +decide [ List.getElem?_eq_none ] ) ( by
        linarith ) n₂ ( by linarith ) ( by
        convert hv using 1;
        convert congr_arg ( fun x => x.tail.map symbol.terminal ) hw₁₂ using 1;
        grind +extAll );
      exact ⟨ bound, startPos + 1, by aesop ⟩

/-
Completeness of saturation.
-/
lemma satFixpoint_complete (G : EncodedCFG T) (w : List T)
    (nt : Fin G.ntCount) (i j : ℕ) (hij : i ≤ j) (hj : j ≤ w.length)
    (hder : CF_derives G.toCFGrammar [symbol.nonterminal nt]
        ((w.drop i |>.take (j - i)).map symbol.terminal)) :
    ∃ bound, (nt.val, i, j) ∈ satFixpoint G.ntCount G.rawRules w bound := by
  -- By induction on the number of steps, we can show that the fixespoint contains all derivable triples.
  have h_ind : ∀ n, ∀ nt : Fin G.ntCount, ∀ i j, i ≤ j → j ≤ w.length →
    CF_derives_in G.toCFGrammar n [symbol.nonterminal nt] ((w.drop i |>.take (j - i)).map symbol.terminal) →
    ∃ bound, (nt.val, i, j) ∈ satFixpoint G.ntCount G.rawRules w bound := by
      intro n
      induction' n using Nat.strong_induction_on with n ih;
      intro nt i j hij hj hder;
      rcases n with ( _ | n );
      · exact False.elim <| no_terminal_eq_nonterminal G.toCFGrammar nt ( take ( j - i ) ( drop i w ) ) hder;
      · obtain ⟨ mid, hmid₁, hmid₂ ⟩ := hder;
        obtain ⟨ rhs, hrhs₁, hrhs₂ ⟩ := transforms_single_nonterminal G.toCFGrammar nt mid hmid₁;
        obtain ⟨ lhs_raw, rhs_raw, hrhs₃, hrhs₄, hrhs₅ ⟩ := rawRule_of_toCFGrammar_rule G nt rhs hrhs₁;
        obtain ⟨ bound, hbound ⟩ := matchRHS_in_satFixpoint G w n ( fun m mn nt i j hij hj hder => ih m mn nt i j hij hj hder ) rhs_raw i j hij hj n le_rfl ( by aesop );
        use bound + 1;
        convert mem_satStep_of_matchRHS G.ntCount G.rawRules w ( satFixpoint G.ntCount G.rawRules w bound ) lhs_raw rhs_raw hrhs₃ i j _ hbound using 1;
        · exact Function.iterate_succ_apply' _ _ _;
        · exact hrhs₄ ▸ rfl;
        · linarith;
  obtain ⟨ n, hn ⟩ := derives_in_of_derives hder; exact h_ind n nt i j hij hj hn;

/-! ## Saturation Stabilization -/

/-
satStep preserves the prefix: S is a prefix of satStep nc rules w S.
-/
lemma satStep_prefix (nc : ℕ) (rules : List (ℕ × List (ℕ ⊕ T))) (w : List T)
    (S : List (ℕ × ℕ × ℕ)) :
    S <+: satStep nc rules w S := by
  induction' rules using List.reverseRecOn with rules ih generalizing S <;> simp_all +decide [ satStep ];
  rename_i h;
  specialize h S;
  obtain ⟨ k, hk ⟩ := h;
  rw [ ← hk ];
  induction' ( range ( w.length + 1 ) ) using List.reverseRecOn with startPos ih <;> simp_all +decide [ List.range_succ ];
  · exact hk ▸ List.prefix_append _ _;
  · induction' ( matchRHS w nc S ‹ℕ × List ( ℕ ⊕ T ) ›.2 ih ) using List.reverseRecOn with endPos ih <;> simp_all +decide [ List.range_succ ];
    grind

/-
All triples added by satStep have their first component < nc (when nc > 0).
-/
lemma satStep_fst_bound (nc : ℕ) (rules : List (ℕ × List (ℕ ⊕ T))) (w : List T)
    (S : List (ℕ × ℕ × ℕ)) (nt i j : ℕ)
    (hnc : 0 < nc)
    (hS : ∀ nt' i' j', (nt', i', j') ∈ S → nt' < nc)
    (h : (nt, i, j) ∈ satStep nc rules w S) : nt < nc := by
  have := mem_satStep_iff nc rules w S nt i j; simp_all +arith +decide [ Nat.mod_lt ] ;
  rcases this with ( h | ⟨ a, b, h₁, h₂, rfl, h₃ ⟩ ) <;> [ exact hS _ _ _ h; exact Nat.mod_lt _ hnc ]

/-
matchRHS returns positions ≤ w.length, given that S entries have endpoints ≤ w.length.
-/
lemma matchRHS_endPos_bound (w : List T) (nc : ℕ) (S : List (ℕ × ℕ × ℕ))
    (hS : ∀ nt i j, (nt, i, j) ∈ S → j ≤ w.length)
    (rhs : List (ℕ ⊕ T)) (startPos endPos : ℕ)
    (hstart : startPos ≤ w.length)
    (hmatch : endPos ∈ matchRHS w nc S rhs startPos) :
    endPos ≤ w.length := by
  contrapose! hmatch;
  induction' rhs with sym rhs ih generalizing startPos endPos;
  · grind +locals;
  · have h_nonempty : ∀ startPos, startPos ≤ w.length → ∀ endPos, endPos ∈ matchOneSym w nc S sym startPos → endPos ≤ w.length := by
      unfold matchOneSym;
      grind +splitIndPred;
    rw [ matchRHS_cons ];
    grind

/-
All triples in satStep have position components ≤ w.length.
-/
lemma satStep_pos_bound (nc : ℕ) (rules : List (ℕ × List (ℕ ⊕ T))) (w : List T)
    (S : List (ℕ × ℕ × ℕ))
    (hS : ∀ nt i j, (nt, i, j) ∈ S → i ≤ w.length ∧ j ≤ w.length)
    (nt i j : ℕ) (h : (nt, i, j) ∈ satStep nc rules w S) :
    i ≤ w.length ∧ j ≤ w.length := by
  -- By definition of `satStep`, we know that if `(nt, i, j)` is in `satStep nc rules w S`, then either `(nt, i, j)` is in `S` or it is added by processing a rule.
  obtain h_in_S | h_rule := mem_satStep_iff nc rules w S nt i j h;
  · exact hS _ _ _ h_in_S;
  · obtain ⟨ rule, hrule, startPos, hstartPos, rfl, rfl, hj ⟩ := h_rule;
    exact ⟨ hstartPos, matchRHS_endPos_bound w nc S ( fun nt i j hij => hS nt i j hij |>.2 ) rule.2 i j hstartPos hj ⟩

/-
satStep preserves Nodup.
-/
lemma satStep_nodup (nc : ℕ) (rules : List (ℕ × List (ℕ ⊕ T))) (w : List T)
    (S : List (ℕ × ℕ × ℕ)) (hS : S.Nodup) :
    (satStep nc rules w S).Nodup := by
  -- By definition of `satStep`, we know that if `S` is nodup, then `satStep nc rules w S` is also nodup.
  have h_satStep_nodup : ∀ (l : List (ℕ × ℕ × ℕ)) (t : ℕ × ℕ × ℕ), l.Nodup → (if t ∈ l then l else l ++ [t]).Nodup := by
    grind;
  -- By induction on the number of rules, we can show that each step of the fold preserves the nodup property.
  have h_ind : ∀ (rules : List (ℕ × ℕ × ℕ)) (l : List (ℕ × ℕ × ℕ)), l.Nodup → (rules.foldl (fun acc x => if x ∈ acc then acc else acc ++ [x]) l).Nodup := by
    intro rules l hl; induction' rules using List.reverseRecOn with rules ih <;> aesop;
  convert h_ind _ _ hS using 1;
  swap;
  exact List.flatMap ( fun rule => List.flatMap ( fun startPos => List.flatMap ( fun endPos => [ ( rule.1 % nc, startPos, endPos ) ] ) ( matchRHS w nc S rule.2 startPos ) ) ( List.range ( w.length + 1 ) ) ) rules;
  unfold satStep; simp +decide [ List.foldl_flatMap ] ;

/-
satFixpoint has no duplicates.
-/
lemma satFixpoint_nodup (nc : ℕ) (rules : List (ℕ × List (ℕ ⊕ T))) (w : List T)
    (n : ℕ) : (satFixpoint nc rules w n).Nodup := by
  induction' n with n ih;
  · exact List.nodup_nil;
  · convert satStep_nodup nc rules w _ ih using 1;
    exact Function.iterate_succ_apply' _ _ _

/-
All entries in satFixpoint are bounded (when nc > 0).
-/
lemma satFixpoint_entries_bounded (nc : ℕ) (rules : List (ℕ × List (ℕ ⊕ T))) (w : List T)
    (hnc : 0 < nc)
    (n : ℕ) (nt i j : ℕ) (h : (nt, i, j) ∈ satFixpoint nc rules w n) :
    nt < nc ∧ i ≤ w.length ∧ j ≤ w.length := by
  revert h;
  induction' n with n ih generalizing nt i j;
  · unfold satFixpoint; aesop;
  · unfold satFixpoint;
    rw [ Function.iterate_succ_apply' ];
    exact fun h => ⟨ satStep_fst_bound nc rules w _ _ _ _ hnc ( fun nt' i' j' h => ih _ _ _ h |>.1 ) h, satStep_pos_bound nc rules w _ ( fun nt' i' j' h => ih _ _ _ h |>.2 ) _ _ _ h ⟩

/-
satFixpoint length is bounded by the universe size (when nc > 0).
-/
lemma satFixpoint_length_bounded (nc : ℕ) (rules : List (ℕ × List (ℕ ⊕ T))) (w : List T)
    (hnc : 0 < nc)
    (n : ℕ) :
    (satFixpoint nc rules w n).length ≤ nc * (w.length + 1) * (w.length + 1) := by
  have h_card : (satFixpoint nc rules w n).toFinset.card ≤ nc * (w.length + 1) * (w.length + 1) := by
    refine' le_trans ( Finset.card_le_card _ ) _;
    exact Finset.Iio nc ×ˢ Finset.Iic w.length ×ˢ Finset.Iic w.length;
    · intro x hx; specialize hx; have := satFixpoint_entries_bounded nc rules w hnc n x.1 x.2.1 x.2.2; aesop;
    · norm_num [ mul_assoc ];
  rwa [ List.toFinset_card_of_nodup ( satFixpoint_nodup nc rules w n ) ] at h_card

/-
If satFixpoint stabilizes at step k, it stays the same forever.
-/
lemma satFixpoint_stable_after (nc : ℕ) (rules : List (ℕ × List (ℕ ⊕ T))) (w : List T)
    (k : ℕ) (hk : satFixpoint nc rules w k = satFixpoint nc rules w (k + 1)) :
    ∀ m ≥ k, satFixpoint nc rules w m = satFixpoint nc rules w k := by
  intro m hm;
  induction' hm with m hm ih;
  · rfl;
  · have h_iter : ∀ m, satFixpoint nc rules w (m + 1) = satStep nc rules w (satFixpoint nc rules w m) := by
      exact fun m => Function.iterate_succ_apply' ( satStep nc rules w ) m [];
    grind

/-
Key convergence: any triple in any satFixpoint is in the bounded satFixpoint (when nc > 0).
-/
lemma satFixpoint_converges (nc : ℕ) (rules : List (ℕ × List (ℕ ⊕ T))) (w : List T)
    (hnc : 0 < nc)
    (t : ℕ × ℕ × ℕ) :
    (∃ n, t ∈ satFixpoint nc rules w n) →
    t ∈ satFixpoint nc rules w (nc * (w.length + 1) * (w.length + 1) + 1) := by
  intro ht
  obtain ⟨n, hn⟩ := ht
  by_cases h : n ≤ nc * (w.length + 1) * (w.length + 1) + 1;
  · exact?;
  · -- By the stabilization argument, there exists some $k \leq B$ such that $satFixpoint k = satFixpoint (k + 1)$.
    obtain ⟨k, hk⟩ : ∃ k ≤ nc * (w.length + 1) * (w.length + 1), satFixpoint nc rules w k = satFixpoint nc rules w (k + 1) := by
      by_contra h_contra; push_neg at h_contra; (
      -- By the properties of the sequence, if it is strictly increasing and bounded above, it must stabilize.
      have h_strict_mono : ∀ k ≤ nc * (w.length + 1) * (w.length + 1), (satFixpoint nc rules w k).length < (satFixpoint nc rules w (k + 1)).length := by
        intros k hk
        have h_mono : satFixpoint nc rules w k <+: satFixpoint nc rules w (k + 1) := by
          have h_mono : ∀ k, satFixpoint nc rules w k <+: satFixpoint nc rules w (k + 1) := by
            intros k; exact (by
            convert satStep_prefix nc rules w ( satFixpoint nc rules w k ) using 1;
            exact Function.iterate_succ_apply' _ _ _);
          exact h_mono k
        have h_neq : satFixpoint nc rules w k ≠ satFixpoint nc rules w (k + 1) := by
          exact h_contra k hk
        have h_len : (satFixpoint nc rules w k).length < (satFixpoint nc rules w (k + 1)).length := by
          exact lt_of_le_of_ne ( by simpa using h_mono.length_le ) fun h => h_neq <| by simpa [ h ] using h_mono.eq_of_length_le <| by simp +decide [ h ] ;
        exact h_len;
      have h_strict_mono : (satFixpoint nc rules w (nc * (w.length + 1) * (w.length + 1) + 1)).length ≥ (nc * (w.length + 1) * (w.length + 1) + 1) := by
        have h_strict_mono : ∀ k ≤ nc * (w.length + 1) * (w.length + 1), (satFixpoint nc rules w k).length ≥ k := by
          intro k hk; induction' k with k ih <;> norm_num at *;
          linarith [ ih ( Nat.le_of_lt hk ), h_strict_mono k ( Nat.le_of_lt hk ) ];
        grind;
      exact not_lt_of_ge h_strict_mono ( Nat.lt_succ_of_le ( satFixpoint_length_bounded nc rules w hnc _ ) ));
    -- By the stabilization argument, since $n > B + 1$, we have $satFixpoint n = satFixpoint k$.
    have h_satFixpoint_eq : satFixpoint nc rules w n = satFixpoint nc rules w k := by
      exact satFixpoint_stable_after nc rules w k hk.2 n ( by linarith );
    exact satFixpoint_mono _ _ _ _ _ ( by linarith ) _ ( h_satFixpoint_eq ▸ hn )

/-! ## Main Correctness -/

theorem checkMembershipEncoded_correct [Fintype T] (G : EncodedCFG T) (w : List T) :
    checkMembershipEncoded (G, w) = true ↔ w ∈ CF_language G.toCFGrammar := by
  constructor;
  · intro h_true
    have h_triple : (G.initialIdx % G.ntCount, 0, w.length) ∈ satFixpoint G.ntCount G.rawRules w (G.ntCount * (w.length + 1) * (w.length + 1) + 1) := by
      unfold checkMembershipEncoded at h_true; aesop;
    have := satFixpoint_sound G w ( G.ntCount * ( w.length + 1 ) * ( w.length + 1 ) + 1 );
    obtain ⟨ hnt, h0, h1, h2 ⟩ := this _ _ _ h_triple;
    unfold CF_language; aesop;
  · intro hw
    obtain ⟨hnt, hstart, hend, hder⟩ : ∃ hnt : G.initialIdx % G.ntCount < G.ntCount, 0 ≤ w.length ∧ w.length ≤ w.length ∧ CF_derives G.toCFGrammar [symbol.nonterminal ⟨G.initialIdx % G.ntCount, hnt⟩] ((w.drop 0 |>.take (w.length - 0)).map symbol.terminal) := by
      exact ⟨ Nat.mod_lt _ G.ntCount_pos, Nat.zero_le _, le_rfl, by simpa using hw ⟩;
    have := satFixpoint_complete G w ⟨ G.initialIdx % G.ntCount, hnt ⟩ 0 w.length ( by linarith ) ( by linarith ) hder;
    exact decide_eq_true ( satFixpoint_converges _ _ _ ( G.ntCount_pos ) _ this )

/-! ## Computability -/

/- The proof of this theorem is in PrimrecSatStep.lean (as checkMembershipEncoded_computable').
   It cannot be imported here due to circular dependencies, so we leave it as a forward
   declaration. The main theorem contextFree_computableMembership uses
   checkMembershipEncoded_computable' directly.
theorem checkMembershipEncoded_computable [Fintype T] [Primcodable T] :
    Computable (checkMembershipEncoded : EncodedCFG T × List T → Bool) := by
  sorry
-/