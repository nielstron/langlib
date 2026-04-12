import Mathlib
import Langlib.Grammars.Indexed.Definition
import Langlib.Classes.Indexed.Definition
import Langlib.Utilities.ClosurePredicates

/-! # Indexed Languages Are Closed Under Union

Given indexed grammars `g₁` and `g₂`, we construct an indexed grammar whose language
is `g₁.Language ∪ g₂.Language`.

The construction introduces a fresh start symbol with two rules that jump to the
respective initial symbols of `g₁` and `g₂`.

## Main declarations

- `Indexed_of_Indexed_u_Indexed`
-/

open List

variable {T : Type}

/-- The combined nonterminal type for the union grammar. -/
inductive UnionNT (N₁ N₂ : Type) where
  | start : UnionNT N₁ N₂
  | inl : N₁ → UnionNT N₁ N₂
  | inr : N₂ → UnionNT N₁ N₂

/-- The combined flag type for the union grammar. -/
inductive UnionFlag (F₁ F₂ : Type) where
  | inl : F₁ → UnionFlag F₁ F₂
  | inr : F₂ → UnionFlag F₁ F₂

private def liftRhs1 {N₁ N₂ F₁ F₂ : Type} :
    IRhsSymbol T N₁ F₁ → IRhsSymbol T (UnionNT N₁ N₂) (UnionFlag F₁ F₂)
  | IRhsSymbol.terminal t => IRhsSymbol.terminal t
  | IRhsSymbol.nonterminal n none => IRhsSymbol.nonterminal (UnionNT.inl n) none
  | IRhsSymbol.nonterminal n (some f) =>
      IRhsSymbol.nonterminal (UnionNT.inl n) (some (UnionFlag.inl f))

private def liftRhs2 {N₁ N₂ F₁ F₂ : Type} :
    IRhsSymbol T N₂ F₂ → IRhsSymbol T (UnionNT N₁ N₂) (UnionFlag F₁ F₂)
  | IRhsSymbol.terminal t => IRhsSymbol.terminal t
  | IRhsSymbol.nonterminal n none => IRhsSymbol.nonterminal (UnionNT.inr n) none
  | IRhsSymbol.nonterminal n (some f) =>
      IRhsSymbol.nonterminal (UnionNT.inr n) (some (UnionFlag.inr f))

private def liftRule1 {N₁ N₂ F₁ F₂ : Type} (r : IRule T N₁ F₁) :
    IRule T (UnionNT N₁ N₂) (UnionFlag F₁ F₂) :=
  { lhs := UnionNT.inl r.lhs
    consume := r.consume.map UnionFlag.inl
    rhs := r.rhs.map liftRhs1 }

private def liftRule2 {N₁ N₂ F₁ F₂ : Type} (r : IRule T N₂ F₂) :
    IRule T (UnionNT N₁ N₂) (UnionFlag F₁ F₂) :=
  { lhs := UnionNT.inr r.lhs
    consume := r.consume.map UnionFlag.inr
    rhs := r.rhs.map liftRhs2 }

/-- Indexed grammar for the union of two indexed languages. -/
def indexed_union (g₁ g₂ : IndexedGrammar T) : IndexedGrammar T where
  nt := UnionNT g₁.nt g₂.nt
  flag := UnionFlag g₁.flag g₂.flag
  initial := UnionNT.start
  rules :=
    [ { lhs := UnionNT.start, consume := none,
        rhs := [IRhsSymbol.nonterminal (UnionNT.inl g₁.initial) none] },
      { lhs := UnionNT.start, consume := none,
        rhs := [IRhsSymbol.nonterminal (UnionNT.inr g₂.initial) none] } ] ++
    g₁.rules.map liftRule1 ++
    g₂.rules.map liftRule2

private def liftISym1 (g₁ g₂ : IndexedGrammar T) :
    g₁.ISym → (indexed_union g₁ g₂).ISym
  | IndexedGrammar.ISym.terminal t => IndexedGrammar.ISym.terminal t
  | IndexedGrammar.ISym.indexed n σ =>
      IndexedGrammar.ISym.indexed (UnionNT.inl n) (σ.map UnionFlag.inl)

private def liftISym2 (g₁ g₂ : IndexedGrammar T) :
    g₂.ISym → (indexed_union g₁ g₂).ISym
  | IndexedGrammar.ISym.terminal t => IndexedGrammar.ISym.terminal t
  | IndexedGrammar.ISym.indexed n σ =>
      IndexedGrammar.ISym.indexed (UnionNT.inr n) (σ.map UnionFlag.inr)

private lemma lift1_expandRhs (g₁ g₂ : IndexedGrammar T)
    (rhs : List (IRhsSymbol T g₁.nt g₁.flag)) (σ : List g₁.flag) :
    (g₁.expandRhs rhs σ).map (liftISym1 g₁ g₂) =
    (indexed_union g₁ g₂).expandRhs (rhs.map liftRhs1) (σ.map UnionFlag.inl) := by
      unfold IndexedGrammar.expandRhs; induction rhs <;> aesop;

private lemma lift2_expandRhs (g₁ g₂ : IndexedGrammar T)
    (rhs : List (IRhsSymbol T g₂.nt g₂.flag)) (σ : List g₂.flag) :
    (g₂.expandRhs rhs σ).map (liftISym2 g₁ g₂) =
    (indexed_union g₁ g₂).expandRhs (rhs.map liftRhs2) (σ.map UnionFlag.inr) := by
      unfold IndexedGrammar.expandRhs;
      rw [ List.map_map, List.map_map ];
      congr! 2;
      funext s; cases s <;> simp +decide [ liftRhs2, liftISym2 ] ;
      cases ‹Option g₂.flag› <;> rfl

private lemma lift1_tran (g₁ g₂ : IndexedGrammar T) {w₁ w₂ : List g₁.ISym}
    (h : g₁.Transforms w₁ w₂) :
    (indexed_union g₁ g₂).Transforms
      (w₁.map (liftISym1 g₁ g₂)) (w₂.map (liftISym1 g₁ g₂)) := by
        obtain ⟨ r, u, v, σ, hr, hw₁, hw₂ ⟩ := h;
        refine' ⟨ liftRule1 r, _, _, _, List.mem_append.mpr _, _, _ ⟩;
        exact u.map ( liftISym1 g₁ g₂ );
        exact v.map ( liftISym1 g₁ g₂ );
        exact σ.map UnionFlag.inl;
        · aesop;
        · unfold liftRule1; aesop;
        · simp +decide [ hw₂, lift1_expandRhs ];
          rfl

private lemma lift2_tran (g₁ g₂ : IndexedGrammar T) {w₁ w₂ : List g₂.ISym}
    (h : g₂.Transforms w₁ w₂) :
    (indexed_union g₁ g₂).Transforms
      (w₁.map (liftISym2 g₁ g₂)) (w₂.map (liftISym2 g₁ g₂)) := by
        obtain ⟨ r, u, v, σ, hr, hw₁, hw₂ ⟩ := h;
        refine' ⟨ _, _, _, _, List.mem_append_right _ ( List.mem_map.mpr ⟨ r, hr, rfl ⟩ ), _, _ ⟩;
        exact u.map ( liftISym2 g₁ g₂ );
        exact v.map ( liftISym2 g₁ g₂ );
        exact σ.map UnionFlag.inr;
        · unfold liftRule2; aesop;
        · simp +decide [ hw₂, lift2_expandRhs ];
          rfl

private lemma lift1_deri (g₁ g₂ : IndexedGrammar T) {w₁ w₂ : List g₁.ISym}
    (h : g₁.Derives w₁ w₂) :
    (indexed_union g₁ g₂).Derives
      (w₁.map (liftISym1 g₁ g₂)) (w₂.map (liftISym1 g₁ g₂)) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ ht ih => exact ih.tail (lift1_tran g₁ g₂ ht)

private lemma lift2_deri (g₁ g₂ : IndexedGrammar T) {w₁ w₂ : List g₂.ISym}
    (h : g₂.Derives w₁ w₂) :
    (indexed_union g₁ g₂).Derives
      (w₁.map (liftISym2 g₁ g₂)) (w₂.map (liftISym2 g₁ g₂)) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ ht ih => exact ih.tail (lift2_tran g₁ g₂ ht)

private lemma union_generates_left (g₁ g₂ : IndexedGrammar T) (w : List T)
    (h : g₁.Generates w) : (indexed_union g₁ g₂).Generates w := by
  unfold IndexedGrammar.Generates at *
  have hstart : (indexed_union g₁ g₂).Transforms
      [IndexedGrammar.ISym.indexed UnionNT.start []]
      [IndexedGrammar.ISym.indexed (UnionNT.inl g₁.initial) []] := by
    refine ⟨⟨UnionNT.start, none, [IRhsSymbol.nonterminal (UnionNT.inl g₁.initial) none]⟩,
            [], [], [], ?_, ?_, ?_⟩
    · simp [indexed_union]
    · simp
    · simp [IndexedGrammar.expandRhs]
  have hlift := lift1_deri g₁ g₂ h
  simp [liftISym1, List.map_map] at hlift
  exact (Relation.ReflTransGen.single hstart).trans hlift

private lemma union_generates_right (g₁ g₂ : IndexedGrammar T) (w : List T)
    (h : g₂.Generates w) : (indexed_union g₁ g₂).Generates w := by
  unfold IndexedGrammar.Generates at *
  have hstart : (indexed_union g₁ g₂).Transforms
      [IndexedGrammar.ISym.indexed UnionNT.start []]
      [IndexedGrammar.ISym.indexed (UnionNT.inr g₂.initial) []] := by
    refine ⟨⟨UnionNT.start, none, [IRhsSymbol.nonterminal (UnionNT.inr g₂.initial) none]⟩,
            [], [], [], ?_, ?_, ?_⟩
    · simp [indexed_union]
    · simp
    · simp [IndexedGrammar.expandRhs]
  have hlift := lift2_deri g₁ g₂ h
  simp [liftISym2, List.map_map] at hlift
  exact (Relation.ReflTransGen.single hstart).trans hlift

/-
---------------------------------------------------------------------------
Backward direction helpers
---------------------------------------------------------------------------

In the union grammar, the first step from Start must choose a side.
-/
private lemma union_first_step (g₁ g₂ : IndexedGrammar T)
    {b : List (indexed_union g₁ g₂).ISym}
    (h : (indexed_union g₁ g₂).Transforms
      [IndexedGrammar.ISym.indexed UnionNT.start []] b) :
    b = [IndexedGrammar.ISym.indexed (UnionNT.inl g₁.initial) []] ∨
    b = [IndexedGrammar.ISym.indexed (UnionNT.inr g₂.initial) []] := by
      obtain ⟨ r, u, v, σ, hr, hu, hv ⟩ := h;
      rcases r with ⟨ lhs, consume, rhs ⟩;
      rcases consume with ( _ | f ) <;> simp_all +decide [ List.append_assoc ];
      · rcases u with ( _ | ⟨ _, _ ⟩ ) <;> rcases v with ( _ | ⟨ _, _ ⟩ ) <;> simp_all +decide;
        unfold indexed_union at hr; simp_all +decide [ List.mem_append, List.mem_map ] ;
        unfold liftRule1 liftRule2 at hr; aesop;
      · cases u <;> cases v <;> aesop

/-
If a union-grammar step acts on a sentential form that is a lifted g₁ form,
    then the result is also a lifted g₁ form and corresponds to a g₁ step.
-/
private lemma unlift1_tran (g₁ g₂ : IndexedGrammar T)
    {w₁ : List g₁.ISym}
    {w₂ : List (indexed_union g₁ g₂).ISym}
    (ht : (indexed_union g₁ g₂).Transforms (w₁.map (liftISym1 g₁ g₂)) w₂) :
    ∃ w₂g : List g₁.ISym,
      w₂ = w₂g.map (liftISym1 g₁ g₂) ∧ g₁.Transforms w₁ w₂g := by
        obtain ⟨ r, u, v, σ, hr, hw₁, hw₂ ⟩ := ht;
        by_cases hr₁ : r ∈ List.map (liftRule1 : IRule T g₁.nt g₁.flag → IRule T (UnionNT g₁.nt g₂.nt) (UnionFlag g₁.flag g₂.flag)) g₁.rules;
        · obtain ⟨ r₁, hr₁, rfl ⟩ := List.mem_map.mp hr₁;
          -- Since $σ$ is a list of flags, we can decompose it into $σ'$ and $σ''$ such that $σ = σ'.map UnionFlag.inl$.
          obtain ⟨σ', hσ'⟩ : ∃ σ' : List g₁.flag, σ = σ'.map UnionFlag.inl := by
            have hσ : ∀ f ∈ σ, ∃ f' : g₁.flag, f = UnionFlag.inl f' := by
              intro f hf;
              rcases f with ( _ | _ ) <;> simp_all +decide [ liftRule1 ];
              rcases r₁consume : r₁.consume with ( _ | _ ) <;> simp_all +decide [ List.map_eq_append_iff ];
              · obtain ⟨ l₁, l₂, rfl, rfl, hl₂ ⟩ := hw₁;
                cases l₂ <;> simp_all +decide [ liftISym1 ];
                cases ‹g₁.ISym› <;> simp_all +decide [ liftISym1 ];
                aesop;
              · obtain ⟨ l₁, l₂, rfl, rfl, hl₂ ⟩ := hw₁;
                cases l₂ <;> simp_all +decide [ liftISym1 ];
                cases ‹g₁.ISym› <;> simp_all +decide [ liftISym1 ];
                grind +splitImp;
            have hσ' : ∀ {l : List (UnionFlag g₁.flag g₂.flag)}, (∀ f ∈ l, ∃ f' : g₁.flag, f = UnionFlag.inl f') → ∃ l' : List g₁.flag, l = l'.map UnionFlag.inl := by
              intros l hl; induction' l with f l ih <;> simp_all +decide [ List.map ] ;
              rcases hl.1 with ⟨ f', rfl ⟩ ; obtain ⟨ l', rfl ⟩ := ih; exact ⟨ f' :: l', by simp +decide ⟩ ;
            exact hσ' hσ;
          -- Since $u$ and $v$ are lists of symbols, we can decompose them into $u'$ and $v'$ such that $u = u'.map liftISym1$ and $v = v'.map liftISym1$.
          obtain ⟨u', hu'⟩ : ∃ u' : List g₁.ISym, u = u'.map (liftISym1 g₁ g₂) := by
            have hu' : ∀ {l : List (indexed_union g₁ g₂).ISym}, (∀ s ∈ l, ∃ s' : g₁.ISym, s = liftISym1 g₁ g₂ s') → ∃ l' : List g₁.ISym, l = l'.map (liftISym1 g₁ g₂) := by
              intros l hl; induction' l with s l ih;
              · exact ⟨ [ ], rfl ⟩;
              · obtain ⟨ s', hs' ⟩ := hl s ( by simp +decide ) ; obtain ⟨ l', hl' ⟩ := ih fun x hx => hl x ( by simp +decide [ hx ] ) ; use s' :: l'; simp +decide [ hs', hl' ] ;
            apply hu';
            intro s hs;
            have hs' : s ∈ map (liftISym1 g₁ g₂) w₁ := by
              grind +splitIndPred;
            rw [ List.mem_map ] at hs'; obtain ⟨ s', hs', rfl ⟩ := hs'; exact ⟨ s', rfl ⟩ ;
          obtain ⟨v', hv'⟩ : ∃ v' : List g₁.ISym, v = v'.map (liftISym1 g₁ g₂) := by
            have hv' : ∀ x ∈ v, ∃ y : g₁.ISym, x = liftISym1 g₁ g₂ y := by
              have hv' : ∀ x ∈ map (liftISym1 g₁ g₂) w₁, ∃ y : g₁.ISym, x = liftISym1 g₁ g₂ y := by
                simp +decide [ eq_comm ];
                exact fun x y hy hx => ⟨ y, hx ⟩;
              cases h : ( liftRule1 r₁ ).consume <;> simp_all +decide;
              all_goals rw [ h ] at hw₁; simp_all +decide [ List.mem_append, List.mem_cons ] ;
            have hv' : ∃ v' : List g₁.ISym, v = v'.map (liftISym1 g₁ g₂) := by
              have hv'_list : ∀ {l : List (indexed_union g₁ g₂).ISym}, (∀ x ∈ l, ∃ y : g₁.ISym, x = liftISym1 g₁ g₂ y) → ∃ l' : List g₁.ISym, l = l'.map (liftISym1 g₁ g₂) := by
                intros l hl; induction' l with x l ih;
                · exact ⟨ [ ], rfl ⟩;
                · obtain ⟨ y, rfl ⟩ := hl x ( by simp +decide ) ; obtain ⟨ l', hl' ⟩ := ih fun x hx => hl x ( by simp +decide [ hx ] ) ; exact ⟨ y :: l', by simp +decide [ hl' ] ⟩ ;
              exact hv'_list hv';
            exact hv';
          use u' ++ g₁.expandRhs r₁.rhs σ' ++ v';
          constructor;
          · simp_all +decide [ lift1_expandRhs ];
            rfl;
          · use r₁, u', v', σ';
            cases h : r₁.consume <;> simp_all +decide [ liftRule1 ];
            · exact List.map_injective_iff.mpr ( show Function.Injective ( liftISym1 g₁ g₂ ) from by
                                                  intro x y; cases x <;> cases y <;> simp +decide [ liftISym1 ] ;
                                                  exact fun h₁ h₂ => ⟨ by injection h₁, by simpa using List.map_injective_iff.mpr ( show Function.Injective UnionFlag.inl from by rintro x y; aesop ) h₂ ⟩ ) <| by simpa using hw₁;
            · exact List.map_injective_iff.mpr ( show Function.Injective ( liftISym1 g₁ g₂ ) from by
                                                  intro x y; cases x <;> cases y <;> simp +decide [ liftISym1 ] ;
                                                  exact fun h₁ h₂ => ⟨ by injection h₁, by simpa using List.map_injective_iff.mpr ( show Function.Injective ( UnionFlag.inl ) from by rintro x y; aesop ) h₂ ⟩ ) <| by simpa [ List.map_append ] using hw₁;
        · by_cases hr₂ : r ∈ List.map (liftRule2 : IRule T g₂.nt g₂.flag → IRule T (UnionNT g₁.nt g₂.nt) (UnionFlag g₁.flag g₂.flag)) g₂.rules;
          · obtain ⟨ r', hr', rfl ⟩ := List.mem_map.mp hr₂;
            rcases r' with ⟨ lhs, consume, rhs ⟩ ; simp_all +decide [ liftRule2 ] ;
            rcases consume with ( _ | f ) <;> simp_all +decide [ List.map_eq_append_iff ];
            · rcases hw₁ with ⟨ l₁, l₂, rfl, rfl, hl₂ ⟩ ; rcases l₂ with ( _ | ⟨ x, l₂ ⟩ ) <;> simp_all +decide [ List.map ] ;
              cases x <;> cases hl₂.1;
            · obtain ⟨ l₁, l₂, rfl, rfl, hl₂ ⟩ := hw₁; rcases l₂ with ( _ | ⟨ x, l₂ ⟩ ) <;> simp_all +decide [ List.map_eq_cons_iff ] ;
              cases x <;> cases hl₂.1;
          · unfold indexed_union at hr; simp_all +decide [ List.mem_append ] ;
            rcases hr with ( rfl | rfl ) <;> simp_all +decide [ List.map_eq_append_iff ];
            · rcases hw₁ with ⟨ l₁, l₂, rfl, rfl, hl₂ ⟩ ; rcases l₂ with ( _ | ⟨ x, l₂ ⟩ ) <;> simp_all +decide [ List.map ] ;
              cases x <;> simp_all +decide [ liftISym1 ];
            · rcases hw₁ with ⟨ l₁, l₂, rfl, rfl, hl₂ ⟩ ; rcases l₂ with ( _ | ⟨ x, l₂ ⟩ ) <;> simp_all +decide [ List.map ] ;
              cases x <;> cases hl₂.1

set_option maxHeartbeats 800000 in
private lemma unlift2_tran (g₁ g₂ : IndexedGrammar T)
    {w₁ : List g₂.ISym}
    {w₂ : List (indexed_union g₁ g₂).ISym}
    (ht : (indexed_union g₁ g₂).Transforms (w₁.map (liftISym2 g₁ g₂)) w₂) :
    ∃ w₂g : List g₂.ISym,
      w₂ = w₂g.map (liftISym2 g₁ g₂) ∧ g₂.Transforms w₁ w₂g := by
        obtain ⟨ r, u, v, σ, hr, hw₁, hw₂ ⟩ := ht;
        by_cases hr₂ : r ∈ g₂.rules.map liftRule2;
        · obtain ⟨ r₂, hr₂ ⟩ := List.mem_map.mp hr₂;
          -- Since `r` is in `g₂.rules.map liftRule2`, we can decompose `σ` into `σ'.map UnionFlag.inr` for some `σ'`.
          obtain ⟨ σ', hσ' ⟩ : ∃ σ' : List g₂.flag, σ = σ'.map UnionFlag.inr := by
            have hσ' : ∀ f ∈ σ, ∃ f' : g₂.flag, f = UnionFlag.inr f' := by
              intro f hf
              have h_f_in_lift : f ∈ (w₁.map (liftISym2 g₁ g₂)).flatMap (fun x => match x with | IndexedGrammar.ISym.terminal _ => [] | IndexedGrammar.ISym.indexed _ σ' => σ') := by
                cases h : r.consume <;> simp_all +decide;
              rw [ List.mem_flatMap ] at h_f_in_lift;
              obtain ⟨ a, ha, hf ⟩ := h_f_in_lift;
              rw [ List.mem_map ] at ha;
              rcases ha with ⟨ a, ha, rfl ⟩ ; rcases a with ( _ | ⟨ n, σ ⟩ ) <;> simp +decide [ liftISym2 ] at hf ⊢;
              tauto;
            have hσ' : ∀ {l : List (indexed_union g₁ g₂).flag}, (∀ f ∈ l, ∃ f' : g₂.flag, f = UnionFlag.inr f') → ∃ l' : List g₂.flag, l = l'.map UnionFlag.inr := by
              intros l hl; induction' l with f l ih <;> simp_all +decide ;
              rcases hl.1 with ⟨ f', rfl ⟩ ; rcases ih with ⟨ l', rfl ⟩ ; exact ⟨ f' :: l', by simp +decide ⟩ ;
            exact hσ' ‹_›;
          -- Since `r` is in `g₂.rules.map liftRule2`, we can decompose `u` and `v` into images of `liftISym2`.
          obtain ⟨ u', hu' ⟩ : ∃ u' : List g₂.ISym, u = u'.map (liftISym2 g₁ g₂) := by
            have hu' : u = (w₁.map (liftISym2 g₁ g₂)).take u.length := by
              cases h : r.consume <;> simp_all +decide;
            rw [ hu' ];
            use w₁.take u.length;
            rw [ List.map_take ]
          obtain ⟨ v', hv' ⟩ : ∃ v' : List g₂.ISym, v = v'.map (liftISym2 g₁ g₂) := by
            have hv' : ∀ x ∈ v, ∃ x' : g₂.ISym, x = liftISym2 g₁ g₂ x' := by
              intro x hx
              have hx' : x ∈ map (liftISym2 g₁ g₂) w₁ := by
                cases h : r.consume <;> aesop;
              rw [ List.mem_map ] at hx'; obtain ⟨ x', hx', rfl ⟩ := hx'; exact ⟨ x', rfl ⟩ ;
            have hv' : ∀ {l : List (indexed_union g₁ g₂).ISym}, (∀ x ∈ l, ∃ x' : g₂.ISym, x = liftISym2 g₁ g₂ x') → ∃ l' : List g₂.ISym, l = l'.map (liftISym2 g₁ g₂) := by
              intros l hl; induction' l with x l ih;
              · exact ⟨ [ ], rfl ⟩;
              · simp +zetaDelta at *;
                rcases hl with ⟨ ⟨ x', rfl ⟩, hl ⟩ ; obtain ⟨ l', rfl ⟩ := ih hl; exact ⟨ x' :: l', by simp +decide ⟩ ;
            exact hv' ‹_›;
          refine' ⟨ u' ++ g₂.expandRhs r₂.rhs σ' ++ v', _, _ ⟩ <;> simp_all +decide [ List.map_append ];
          · rw [ ← hr₂.2, lift2_expandRhs ];
            rfl;
          · rcases h : r.consume with ( _ | f ) <;> simp_all +decide [ liftRule2 ];
            · use r₂, u', v', σ';
              rcases r₂consume : r₂.consume with ( _ | f ) <;> simp_all +decide [ liftISym2 ];
              · have h_inj : Function.Injective (liftISym2 g₁ g₂) := by
                  intro x y hxy; cases x <;> cases y <;> simp_all +decide [ liftISym2 ] ;
                  exact ⟨ by injection hxy.1, by simpa using List.map_injective_iff.mpr ( show Function.Injective ( UnionFlag.inr : g₂.flag → ( indexed_union g₁ g₂ ).flag ) from by rintro x y; aesop ) hxy.2 ⟩;
                exact List.map_injective_iff.mpr h_inj <| by aesop;
              · lia;
            · cases h' : r₂.consume <;> simp_all +decide [ liftRule2 ];
              · grind;
              · use r₂, u', v', σ';
                simp_all +decide [ List.append_assoc ];
                exact List.map_injective_iff.mpr ( show Function.Injective ( liftISym2 g₁ g₂ ) from by
                                                    intro x y; cases x <;> cases y <;> simp +decide [ liftISym2 ] ;
                                                    exact fun h₁ h₂ => ⟨ by injection h₁, by simpa using List.map_injective_iff.mpr ( show Function.Injective UnionFlag.inr from by intros a b; aesop ) h₂ ⟩ ) <| by aesop;
        · by_cases hr₁ : r ∈ g₁.rules.map liftRule1;
          · -- Since $r$ is in $g₁.rules.map liftRule1$, its $lhs$ is of the form $UnionNT.inl n$.
            obtain ⟨n, hn⟩ : ∃ n : g₁.nt, r.lhs = UnionNT.inl n := by
              unfold liftRule1 at hr₁; aesop;
            cases r_consume : r.consume <;> simp_all +decide [ List.map_eq_append_iff ];
            · rcases hw₁ with ⟨ l₁, l₂, rfl, rfl, hl₂ ⟩ ; rcases l₂ with ( _ | ⟨ x, l₂ ⟩ ) <;> simp_all +decide [ List.map ] ;
              cases x <;> cases hl₂.1;
            · obtain ⟨ l₁, l₂, rfl, rfl, hl₂ ⟩ := hw₁;
              cases l₂ <;> simp_all +decide [ List.map ];
              cases ‹g₂.ISym› <;> simp_all +decide [ liftISym2 ];
          · unfold indexed_union at hr; simp_all +decide [ List.mem_append ] ;
            rcases hr with ( rfl | rfl ) <;> simp_all +decide [ List.map_eq_append_iff ];
            · obtain ⟨ l₁, l₂, rfl, rfl, hl₂ ⟩ := hw₁; simp_all +decide [ List.map_eq_cons_iff ] ;
              rcases hl₂ with ⟨ a, l₁, rfl, ha, rfl ⟩ ; rcases a with ( _ | ⟨ n, σ ⟩ ) <;> simp_all +decide [ liftISym2 ] ;
            · rcases hw₁ with ⟨ l₁, l₂, rfl, rfl, hl₂ ⟩ ; rcases l₂ with ( _ | ⟨ x, l₂ ⟩ ) <;> simp_all +decide [ List.map ] ;
              cases x <;> cases hl₂.1

private lemma unlift1_deri (g₁ g₂ : IndexedGrammar T)
    {w₁ : List g₁.ISym}
    {w₂ : List (indexed_union g₁ g₂).ISym}
    (h : (indexed_union g₁ g₂).Derives (w₁.map (liftISym1 g₁ g₂)) w₂) :
    ∃ w₂g : List g₁.ISym,
      w₂ = w₂g.map (liftISym1 g₁ g₂) ∧ g₁.Derives w₁ w₂g := by
  induction h with
  | refl => exact ⟨w₁, rfl, Relation.ReflTransGen.refl⟩
  | tail _ ht ih =>
    obtain ⟨b_g, hb_eq, hb_deri⟩ := ih
    rw [hb_eq] at ht
    obtain ⟨c_g, hc_eq, hc_tran⟩ := unlift1_tran g₁ g₂ ht
    exact ⟨c_g, hc_eq, hb_deri.tail hc_tran⟩

private lemma unlift2_deri (g₁ g₂ : IndexedGrammar T)
    {w₁ : List g₂.ISym}
    {w₂ : List (indexed_union g₁ g₂).ISym}
    (h : (indexed_union g₁ g₂).Derives (w₁.map (liftISym2 g₁ g₂)) w₂) :
    ∃ w₂g : List g₂.ISym,
      w₂ = w₂g.map (liftISym2 g₁ g₂) ∧ g₂.Derives w₁ w₂g := by
  induction h with
  | refl => exact ⟨w₁, rfl, Relation.ReflTransGen.refl⟩
  | tail _ ht ih =>
    obtain ⟨b_g, hb_eq, hb_deri⟩ := ih
    rw [hb_eq] at ht
    obtain ⟨c_g, hc_eq, hc_tran⟩ := unlift2_tran g₁ g₂ ht
    exact ⟨c_g, hc_eq, hb_deri.tail hc_tran⟩

/-
If liftISym1 maps a list to a list of terminals, the original was a list of terminals.
-/
private lemma liftISym1_terminal_inv (g₁ g₂ : IndexedGrammar T)
    {wg : List g₁.ISym} {w : List T}
    (h : wg.map (liftISym1 g₁ g₂) = w.map IndexedGrammar.ISym.terminal) :
    wg = w.map IndexedGrammar.ISym.terminal := by
      induction wg generalizing w <;> cases w <;> simp_all +decide [ liftISym1 ];
      cases ‹g₁.ISym› <;> aesop

private lemma liftISym2_terminal_inv (g₁ g₂ : IndexedGrammar T)
    {wg : List g₂.ISym} {w : List T}
    (h : wg.map (liftISym2 g₁ g₂) = w.map IndexedGrammar.ISym.terminal) :
    wg = w.map IndexedGrammar.ISym.terminal := by
      -- By induction on the list `wg`, we can show that if the map of `liftISym2` over `wg` equals the map of `IndexedGrammar.ISym.terminal` over `w`, then `wg` must be equal to the map of `IndexedGrammar.ISym.terminal` over `w`.
      induction' wg with wg_head wg_tail ih generalizing w;
      · cases w <;> aesop;
      · rcases w with ( _ | ⟨ t, w ⟩ ) <;> simp_all +decide [ List.map ];
        cases wg_head <;> simp_all +decide [ liftISym2 ];
        grind

private lemma union_backward (g₁ g₂ : IndexedGrammar T) (w : List T)
    (h : (indexed_union g₁ g₂).Generates w) :
    g₁.Generates w ∨ g₂.Generates w := by
  unfold IndexedGrammar.Generates at h
  rcases h.cases_head with h_refl | ⟨b, hfirst, hrest⟩
  · cases w with
    | nil => simp at h_refl
    | cons hd tl => simp at h_refl
  · rcases union_first_step g₁ g₂ hfirst with rfl | rfl
    · have hlift : (indexed_union g₁ g₂).Derives
          ([IndexedGrammar.ISym.indexed g₁.initial []].map (liftISym1 g₁ g₂))
          (w.map IndexedGrammar.ISym.terminal) := by
        simpa [liftISym1] using hrest
      obtain ⟨wg, hwg_eq, hwg_deri⟩ := unlift1_deri g₁ g₂ hlift
      left; unfold IndexedGrammar.Generates
      rwa [liftISym1_terminal_inv g₁ g₂ hwg_eq.symm] at hwg_deri
    · have hlift : (indexed_union g₁ g₂).Derives
          ([IndexedGrammar.ISym.indexed g₂.initial []].map (liftISym2 g₁ g₂))
          (w.map IndexedGrammar.ISym.terminal) := by
        simpa [liftISym2] using hrest
      obtain ⟨wg, hwg_eq, hwg_deri⟩ := unlift2_deri g₁ g₂ hlift
      right; unfold IndexedGrammar.Generates
      rwa [liftISym2_terminal_inv g₁ g₂ hwg_eq.symm] at hwg_deri

/-- The class of indexed languages is closed under union. -/
theorem Indexed_of_Indexed_u_Indexed (L₁ : Language T) (L₂ : Language T) :
    is_Indexed L₁ ∧ is_Indexed L₂ → is_Indexed (L₁ + L₂) := by
  rintro ⟨⟨g₁, rfl⟩, ⟨g₂, rfl⟩⟩
  refine ⟨indexed_union g₁ g₂, ?_⟩
  ext w
  change (indexed_union g₁ g₂).Generates w ↔ g₁.Generates w ∨ g₂.Generates w
  constructor
  · exact union_backward g₁ g₂ w
  · rintro (h | h)
    · exact union_generates_left g₁ g₂ w h
    · exact union_generates_right g₁ g₂ w h
/-- The class of indexed languages is closed under union. -/
theorem Indexed_closedUnderUnion : ClosedUnderUnion (α := T) is_Indexed :=
  fun L₁ L₂ h₁ h₂ => Indexed_of_Indexed_u_Indexed L₁ L₂ ⟨h₁, h₂⟩
