module

public import Langlib.Classes.Indexed.Closure.Union
public import Langlib.Utilities.ClosurePredicates
import Mathlib.Tactic

/-! # Indexed Languages Are Closed Under Concatenation

Given indexed grammars `g₁` and `g₂`, we construct a grammar with a fresh start
symbol and one start rule expanding to the two lifted initial symbols in sequence.
-/

open List

variable {T : Type}

private def concatStartRule (g₁ g₂ : IndexedGrammar T) :
    IRule T (UnionNT g₁.nt g₂.nt) (UnionFlag g₁.flag g₂.flag) :=
  { lhs := UnionNT.start
    consume := none
    rhs :=
      [ IRhsSymbol.nonterminal (UnionNT.inl g₁.initial) none
      , IRhsSymbol.nonterminal (UnionNT.inr g₂.initial) none ] }

private def indexedConcat (g₁ g₂ : IndexedGrammar T) : IndexedGrammar T where
  nt := UnionNT g₁.nt g₂.nt
  flag := UnionFlag g₁.flag g₂.flag
  initial := UnionNT.start
  rules := [concatStartRule g₁ g₂] ++ g₁.rules.map liftRule1 ++ g₂.rules.map liftRule2

private def concatLiftISym1 (g₁ g₂ : IndexedGrammar T) :
    g₁.ISym → (indexedConcat g₁ g₂).ISym
  | .terminal t => .terminal t
  | .indexed n σ => .indexed (UnionNT.inl n) (σ.map UnionFlag.inl)

private def concatLiftISym2 (g₁ g₂ : IndexedGrammar T) :
    g₂.ISym → (indexedConcat g₁ g₂).ISym
  | .terminal t => .terminal t
  | .indexed n σ => .indexed (UnionNT.inr n) (σ.map UnionFlag.inr)

private lemma concat_lift1_expandRhs (g₁ g₂ : IndexedGrammar T)
    (rhs : List (IRhsSymbol T g₁.nt g₁.flag)) (σ : List g₁.flag) :
    (g₁.expandRhs rhs σ).map (concatLiftISym1 g₁ g₂) =
      (indexedConcat g₁ g₂).expandRhs (rhs.map liftRhs1) (σ.map UnionFlag.inl) := by
  unfold IndexedGrammar.expandRhs
  induction rhs <;> aesop

private lemma concat_lift2_expandRhs (g₁ g₂ : IndexedGrammar T)
    (rhs : List (IRhsSymbol T g₂.nt g₂.flag)) (σ : List g₂.flag) :
    (g₂.expandRhs rhs σ).map (concatLiftISym2 g₁ g₂) =
      (indexedConcat g₁ g₂).expandRhs (rhs.map liftRhs2) (σ.map UnionFlag.inr) := by
  unfold IndexedGrammar.expandRhs
  rw [List.map_map, List.map_map]
  congr! 2
  funext s
  cases s <;> simp +decide [liftRhs2, concatLiftISym2]
  cases ‹Option g₂.flag› <;> rfl

private lemma concat_lift1_tran (g₁ g₂ : IndexedGrammar T) {w₁ w₂ : List g₁.ISym}
    (h : g₁.Transforms w₁ w₂) :
    (indexedConcat g₁ g₂).Transforms
      (w₁.map (concatLiftISym1 g₁ g₂)) (w₂.map (concatLiftISym1 g₁ g₂)) := by
  obtain ⟨r, u, v, σ, hr, hw₁, hw₂⟩ := h
  refine ⟨liftRule1 r, u.map (concatLiftISym1 g₁ g₂),
    v.map (concatLiftISym1 g₁ g₂), σ.map UnionFlag.inl, ?_, ?_, ?_⟩
  · simp [indexedConcat]
    exact Or.inr (Or.inl ⟨r, hr, rfl⟩)
  · cases hc : r.consume with
    | none =>
        rw [hc] at hw₁
        rw [hw₁]
        simp [liftRule1, concatLiftISym1, hc]
    | some f =>
        rw [hc] at hw₁
        rw [hw₁]
        simp [liftRule1, concatLiftISym1, hc]
  · rw [hw₂]
    simp [liftRule1, concat_lift1_expandRhs]

private lemma concat_lift2_tran (g₁ g₂ : IndexedGrammar T) {w₁ w₂ : List g₂.ISym}
    (h : g₂.Transforms w₁ w₂) :
    (indexedConcat g₁ g₂).Transforms
      (w₁.map (concatLiftISym2 g₁ g₂)) (w₂.map (concatLiftISym2 g₁ g₂)) := by
  obtain ⟨r, u, v, σ, hr, hw₁, hw₂⟩ := h
  refine ⟨liftRule2 r, u.map (concatLiftISym2 g₁ g₂),
    v.map (concatLiftISym2 g₁ g₂), σ.map UnionFlag.inr, ?_, ?_, ?_⟩
  · simp [indexedConcat]
    exact Or.inr (show
      (∃ a ∈ g₁.rules, liftRule1 a = liftRule2 r) ∨
        ∃ a ∈ g₂.rules, liftRule2 a = liftRule2 r from
      Or.inr ⟨r, hr, rfl⟩)
  · cases hc : r.consume with
    | none =>
        rw [hc] at hw₁
        rw [hw₁]
        simp [liftRule2, concatLiftISym2, hc]
    | some f =>
        rw [hc] at hw₁
        rw [hw₁]
        simp [liftRule2, concatLiftISym2, hc]
  · rw [hw₂]
    simp [liftRule2, concat_lift2_expandRhs]

private lemma concat_lift1_deri (g₁ g₂ : IndexedGrammar T) {w₁ w₂ : List g₁.ISym}
    (h : g₁.Derives w₁ w₂) :
    (indexedConcat g₁ g₂).Derives
      (w₁.map (concatLiftISym1 g₁ g₂)) (w₂.map (concatLiftISym1 g₁ g₂)) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ ht ih => exact ih.tail (concat_lift1_tran g₁ g₂ ht)

private lemma concat_lift2_deri (g₁ g₂ : IndexedGrammar T) {w₁ w₂ : List g₂.ISym}
    (h : g₂.Derives w₁ w₂) :
    (indexedConcat g₁ g₂).Derives
      (w₁.map (concatLiftISym2 g₁ g₂)) (w₂.map (concatLiftISym2 g₁ g₂)) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ ht ih => exact ih.tail (concat_lift2_tran g₁ g₂ ht)

private lemma concat_start_tran (g₁ g₂ : IndexedGrammar T) :
    (indexedConcat g₁ g₂).Transforms
      [IndexedGrammar.ISym.indexed UnionNT.start []]
      [ IndexedGrammar.ISym.indexed (UnionNT.inl g₁.initial) []
      , IndexedGrammar.ISym.indexed (UnionNT.inr g₂.initial) [] ] := by
  refine ⟨concatStartRule g₁ g₂, [], [], [], ?_, ?_, ?_⟩
  · simp [indexedConcat]
  · simp [concatStartRule]
  · simp [concatStartRule, IndexedGrammar.expandRhs]

private theorem indexedConcat_generates_append (g₁ g₂ : IndexedGrammar T)
    {w₁ w₂ : List T} (h₁ : g₁.Generates w₁) (h₂ : g₂.Generates w₂) :
    (indexedConcat g₁ g₂).Generates (w₁ ++ w₂) := by
  unfold IndexedGrammar.Generates at h₁ h₂ ⊢
  have hstart := IndexedGrammar.deri_of_tran (concat_start_tran g₁ g₂)
  have hleft := IndexedGrammar.deri_with_suffix
    ([IndexedGrammar.ISym.indexed (UnionNT.inr g₂.initial) []] :
      List (indexedConcat g₁ g₂).ISym)
    (concat_lift1_deri g₁ g₂ h₁)
  have hright := IndexedGrammar.deri_with_prefix
    ((w₁.map IndexedGrammar.ISym.terminal).map (concatLiftISym1 g₁ g₂))
    (concat_lift2_deri g₁ g₂ h₂)
  refine hstart.trans (hleft.trans ?_)
  simpa [concatLiftISym1, concatLiftISym2, List.map_append, List.map_map] using hright

private theorem indexedConcat_language_subset_product (g₁ g₂ : IndexedGrammar T) :
    Set.Subset (g₁.Language * g₂.Language) (indexedConcat g₁ g₂).Language := by
  intro w hw
  rw [Language.mul_def] at hw
  obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := hw
  exact indexedConcat_generates_append g₁ g₂ hw₁ hw₂

private lemma map_eq_append_singleton_of_injective {α β : Type} {f : α → β}
    (hf : Function.Injective f) {xs : List α} {x : α} {u v : List β}
    (h : xs.map f = u ++ [f x] ++ v) :
    ∃ xs₁ xs₂ : List α,
      xs = xs₁ ++ [x] ++ xs₂ ∧ u = xs₁.map f ∧ v = xs₂.map f := by
  have h' : xs.map f = u ++ f x :: v := by
    simpa using h
  obtain ⟨xs₁, rest, hxs, hu, hrest⟩ := List.map_eq_append_iff.mp h'
  cases rest with
  | nil =>
      simp at hrest
  | cons y xs₂ =>
      simp only [List.map_cons, List.cons.injEq] at hrest
      obtain ⟨hy, hv⟩ := hrest
      subst hxs
      have hyx : y = x := hf hy
      subst y
      exact ⟨xs₁, xs₂, by simp, hu.symm, hv.symm⟩

private lemma append_eq_append_cons_of_not_mem {γ : Type} {x : γ}
    {block rest u v : List γ} (hno : x ∉ block) :
    block ++ rest = u ++ x :: v →
      ∃ u', u = block ++ u' ∧ rest = u' ++ x :: v := by
  induction block generalizing u with
  | nil =>
      intro h
      exact ⟨u, by simp, h⟩
  | cons b block ih =>
      intro h
      cases u with
      | nil =>
          simp at h
          exact False.elim (hno (by simp [h.1]))
      | cons c u =>
          simp only [List.cons_append, List.cons.injEq] at h
          obtain ⟨rfl, htail⟩ := h
          have hno_tail : x ∉ block := by
            intro hx
            exact hno (by simp [hx])
          obtain ⟨u', hu, hrest⟩ := ih hno_tail htail
          exact ⟨u', by simp [hu], hrest⟩

private lemma append_eq_append_cons_of_not_mem_right {γ : Type} {x : γ}
    {left right u v : List γ} (hno : x ∉ right) :
    left ++ right = u ++ x :: v →
      ∃ pre post : List γ, left = pre ++ x :: post ∧ u = pre ∧ v = post ++ right := by
  induction left generalizing u with
  | nil =>
      intro h
      have hx : x ∈ right := by
        simp at h
        rw [h]
        simp
      exact False.elim (hno hx)
  | cons a left ih =>
      intro h
      cases u with
      | nil =>
          simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
          obtain ⟨rfl, hv⟩ := h
          exact ⟨[], left, by simp, rfl, by simpa using hv.symm⟩
      | cons b u =>
          simp only [List.cons_append, List.cons.injEq] at h
          obtain ⟨rfl, htail⟩ := h
          obtain ⟨pre, post, hleft, hu, hv⟩ := ih htail
          exact ⟨a :: pre, post, by simp [hleft], by simp [hu], hv⟩

private lemma append_eq_append_cons_of_not_mem_left {γ : Type} {x : γ}
    {left right u v : List γ} (hno : x ∉ left) :
    left ++ right = u ++ x :: v →
      ∃ pre post : List γ,
        right = pre ++ x :: post ∧ u = left ++ pre ∧ v = post := by
  intro h
  obtain ⟨pre, hpre, hright⟩ :=
    append_eq_append_cons_of_not_mem
      (γ := γ) (x := x) (block := left) (rest := right) (u := u) (v := v) hno h
  exact ⟨pre, v, hright, hpre, rfl⟩

private lemma concatLiftISym1_injective (g₁ g₂ : IndexedGrammar T) :
    Function.Injective (concatLiftISym1 g₁ g₂) := by
  intro x y h
  cases x <;> cases y <;> simp [concatLiftISym1] at h ⊢
  · exact h
  · exact ⟨by cases h.1; rfl, by
      exact List.map_injective_iff.mpr (by intro a b hab; cases hab; rfl) h.2⟩

private lemma concatLiftISym2_injective (g₁ g₂ : IndexedGrammar T) :
    Function.Injective (concatLiftISym2 g₁ g₂) := by
  intro x y h
  cases x <;> cases y <;> simp [concatLiftISym2] at h ⊢
  · exact h
  · exact ⟨by cases h.1; rfl, by
      exact List.map_injective_iff.mpr (by intro a b hab; cases hab; rfl) h.2⟩

private lemma inl_indexed_not_mem_lift2 (g₁ g₂ : IndexedGrammar T)
    (n : g₁.nt) (σ : List (UnionFlag g₁.flag g₂.flag)) (ys : List g₂.ISym) :
    (IndexedGrammar.ISym.indexed (UnionNT.inl n) σ :
      (indexedConcat g₁ g₂).ISym) ∉ ys.map (concatLiftISym2 g₁ g₂) := by
  intro h
  obtain ⟨y, _hy, hy⟩ := List.mem_map.mp h
  cases y <;> simp [concatLiftISym2] at hy

private lemma inr_indexed_not_mem_lift1 (g₁ g₂ : IndexedGrammar T)
    (n : g₂.nt) (σ : List (UnionFlag g₁.flag g₂.flag)) (xs : List g₁.ISym) :
    (IndexedGrammar.ISym.indexed (UnionNT.inr n) σ :
      (indexedConcat g₁ g₂).ISym) ∉ xs.map (concatLiftISym1 g₁ g₂) := by
  intro h
  obtain ⟨x, _hx, hx⟩ := List.mem_map.mp h
  cases x <;> simp [concatLiftISym1] at hx

private lemma concat_first_step (g₁ g₂ : IndexedGrammar T)
    {b : List (indexedConcat g₁ g₂).ISym}
    (h : (indexedConcat g₁ g₂).Transforms
      [IndexedGrammar.ISym.indexed UnionNT.start []] b) :
    b =
      [ IndexedGrammar.ISym.indexed (UnionNT.inl g₁.initial) []
      , IndexedGrammar.ISym.indexed (UnionNT.inr g₂.initial) [] ] := by
  obtain ⟨r, u, v, σ, hr, hu, hv⟩ := h
  rcases r with ⟨lhs, consume, rhs⟩
  cases consume with
  | none =>
      rcases u with (_ | ⟨uh, ut⟩) <;>
        rcases v with (_ | ⟨vh, vt⟩) <;>
        simp_all +decide [indexedConcat, concatStartRule, liftRule1, liftRule2,
          IndexedGrammar.expandRhs, List.append_assoc]
      obtain ⟨hlhs, hσ⟩ := hu
      subst lhs
      subst σ
      rcases hr with hr | hleft | hright
      · rw [hr]
        simp
      · obtain ⟨a, _ha, hstart, _hc, _hrhs⟩ := hleft
        cases hstart
      · obtain ⟨a, _ha, hstart, _hc, _hrhs⟩ := hright
        cases hstart
      | some f =>
          rcases u with (_ | ⟨uh, ut⟩) <;>
            rcases v with (_ | ⟨vh, vt⟩) <;>
          simp_all +decide [indexedConcat, concatStartRule, liftRule1, liftRule2,
          List.append_assoc]

private lemma split_mixed_at_lift1_indexed (g₁ g₂ : IndexedGrammar T)
    {xs : List g₁.ISym} {ys : List g₂.ISym}
    {u v : List (indexedConcat g₁ g₂).ISym}
    {n : g₁.nt} {σ : List (UnionFlag g₁.flag g₂.flag)}
    (h : xs.map (concatLiftISym1 g₁ g₂) ++ ys.map (concatLiftISym2 g₁ g₂) =
      u ++ [IndexedGrammar.ISym.indexed (UnionNT.inl n) σ] ++ v) :
    ∃ xs₁ xs₂ : List g₁.ISym, ∃ τ : List g₁.flag,
      xs = xs₁ ++ [IndexedGrammar.ISym.indexed n τ] ++ xs₂ ∧
      σ = τ.map UnionFlag.inl ∧
      u = xs₁.map (concatLiftISym1 g₁ g₂) ∧
      v = xs₂.map (concatLiftISym1 g₁ g₂) ++ ys.map (concatLiftISym2 g₁ g₂) := by
  obtain ⟨pre, post, hleft, hu, hv⟩ :=
    append_eq_append_cons_of_not_mem_right
      (x := (IndexedGrammar.ISym.indexed (UnionNT.inl n) σ :
        (indexedConcat g₁ g₂).ISym))
      (left := xs.map (concatLiftISym1 g₁ g₂))
      (right := ys.map (concatLiftISym2 g₁ g₂))
      (u := u) (v := v)
      (inl_indexed_not_mem_lift2 g₁ g₂ n σ ys)
      (by simpa [List.append_assoc] using h)
  have hmem : (IndexedGrammar.ISym.indexed (UnionNT.inl n) σ :
      (indexedConcat g₁ g₂).ISym) ∈ xs.map (concatLiftISym1 g₁ g₂) := by
    rw [hleft]
    simp
  obtain ⟨s, _hs, hs⟩ := List.mem_map.mp hmem
  cases s with
  | terminal t => simp [concatLiftISym1] at hs
  | indexed m τ =>
      simp [concatLiftISym1] at hs
      obtain ⟨hm, hσ⟩ := hs
      cases hm
      subst σ
      obtain ⟨xs₁, xs₂, hxs, hpre, hpost⟩ :=
        map_eq_append_singleton_of_injective (concatLiftISym1_injective g₁ g₂)
          (xs := xs) (x := IndexedGrammar.ISym.indexed n τ)
          (u := pre) (v := post)
          (by simpa [concatLiftISym1] using hleft)
      exact ⟨xs₁, xs₂, τ, hxs, rfl, by simp [hu, hpre], by simp [hv, hpost]⟩

private lemma split_mixed_at_lift2_indexed (g₁ g₂ : IndexedGrammar T)
    {xs : List g₁.ISym} {ys : List g₂.ISym}
    {u v : List (indexedConcat g₁ g₂).ISym}
    {n : g₂.nt} {σ : List (UnionFlag g₁.flag g₂.flag)}
    (h : xs.map (concatLiftISym1 g₁ g₂) ++ ys.map (concatLiftISym2 g₁ g₂) =
      u ++ [IndexedGrammar.ISym.indexed (UnionNT.inr n) σ] ++ v) :
    ∃ ys₁ ys₂ : List g₂.ISym, ∃ τ : List g₂.flag,
      ys = ys₁ ++ [IndexedGrammar.ISym.indexed n τ] ++ ys₂ ∧
      σ = τ.map UnionFlag.inr ∧
      u = xs.map (concatLiftISym1 g₁ g₂) ++ ys₁.map (concatLiftISym2 g₁ g₂) ∧
      v = ys₂.map (concatLiftISym2 g₁ g₂) := by
  obtain ⟨pre, post, hright, hu, hv⟩ :=
    append_eq_append_cons_of_not_mem_left
      (x := (IndexedGrammar.ISym.indexed (UnionNT.inr n) σ :
        (indexedConcat g₁ g₂).ISym))
      (left := xs.map (concatLiftISym1 g₁ g₂))
      (right := ys.map (concatLiftISym2 g₁ g₂))
      (u := u) (v := v)
      (inr_indexed_not_mem_lift1 g₁ g₂ n σ xs)
      (by simpa [List.append_assoc] using h)
  have hmem : (IndexedGrammar.ISym.indexed (UnionNT.inr n) σ :
      (indexedConcat g₁ g₂).ISym) ∈ ys.map (concatLiftISym2 g₁ g₂) := by
    rw [hright]
    simp
  obtain ⟨s, _hs, hs⟩ := List.mem_map.mp hmem
  cases s with
  | terminal t => simp [concatLiftISym2] at hs
  | indexed m τ =>
      simp [concatLiftISym2] at hs
      obtain ⟨hm, hσ⟩ := hs
      cases hm
      subst σ
      obtain ⟨ys₁, ys₂, hys, hpre, hpost⟩ :=
        map_eq_append_singleton_of_injective (concatLiftISym2_injective g₁ g₂)
          (xs := ys) (x := IndexedGrammar.ISym.indexed n τ)
          (u := pre) (v := post)
          (by simpa [concatLiftISym2] using hright)
      exact ⟨ys₁, ys₂, τ, hys, rfl, by simp [hu, hpre], by simp [hv, hpost]⟩

private lemma concat_mixed_step (g₁ g₂ : IndexedGrammar T)
    {xs : List g₁.ISym} {ys : List g₂.ISym}
    {z : List (indexedConcat g₁ g₂).ISym}
    (h : (indexedConcat g₁ g₂).Transforms
      (xs.map (concatLiftISym1 g₁ g₂) ++ ys.map (concatLiftISym2 g₁ g₂)) z) :
    (∃ xs' : List g₁.ISym,
      z = xs'.map (concatLiftISym1 g₁ g₂) ++ ys.map (concatLiftISym2 g₁ g₂) ∧
      g₁.Transforms xs xs') ∨
    (∃ ys' : List g₂.ISym,
      z = xs.map (concatLiftISym1 g₁ g₂) ++ ys'.map (concatLiftISym2 g₁ g₂) ∧
      g₂.Transforms ys ys') := by
  obtain ⟨r, u, v, σ, hr, hw, hz⟩ := h
  simp [indexedConcat] at hr
  rcases hr with hstart | hleft | hright
  · subst r
    have hmem : (IndexedGrammar.ISym.indexed UnionNT.start σ :
        (indexedConcat g₁ g₂).ISym) ∈
        xs.map (concatLiftISym1 g₁ g₂) ++ ys.map (concatLiftISym2 g₁ g₂) := by
      rw [hw]
      simp [concatStartRule]
    rw [List.mem_append] at hmem
    rcases hmem with hmem | hmem
    · obtain ⟨x, _hx, hx⟩ := List.mem_map.mp hmem
      cases x <;> simp [concatLiftISym1] at hx
    · obtain ⟨y, _hy, hy⟩ := List.mem_map.mp hmem
      cases y <;> simp [concatLiftISym2] at hy
  · obtain ⟨r₁, hr₁, hrule⟩ := hleft
    subst r
    cases hc : r₁.consume with
    | none =>
        simp [liftRule1, hc] at hw hz
        obtain ⟨xs₁, xs₂, τ, hxs, hσ, hu, hv⟩ :=
          split_mixed_at_lift1_indexed g₁ g₂ (by simpa [List.singleton_append] using hw)
        subst σ
        subst xs
        left
        refine ⟨xs₁ ++ g₁.expandRhs r₁.rhs τ ++ xs₂, ?_, ?_⟩
        · rw [hz, hu, hv]
          simp [concat_lift1_expandRhs, List.map_append, List.append_assoc]
        · refine ⟨r₁, xs₁, xs₂, τ, hr₁, ?_, rfl⟩
          simp [hc]
    | some f =>
        simp [liftRule1, hc] at hw hz
        obtain ⟨xs₁, xs₂, τ, hxs, hσ, hu, hv⟩ :=
          split_mixed_at_lift1_indexed g₁ g₂ (by simpa [List.singleton_append] using hw)
        cases τ with
        | nil =>
            simp at hσ
        | cons f' τ' =>
            simp at hσ
            obtain ⟨hf, hτ⟩ := hσ
            cases hf
            subst xs
            left
            refine ⟨xs₁ ++ g₁.expandRhs r₁.rhs τ' ++ xs₂, ?_, ?_⟩
            · rw [hz, hu, hv]
              simp [concat_lift1_expandRhs, hτ, List.map_append, List.append_assoc]
            · refine ⟨r₁, xs₁, xs₂, τ', hr₁, ?_, rfl⟩
              simp [hc]
  · obtain ⟨r₂, hr₂, hrule⟩ := hright
    subst r
    cases hc : r₂.consume with
    | none =>
        simp [liftRule2, hc] at hw hz
        obtain ⟨ys₁, ys₂, τ, hys, hσ, hu, hv⟩ :=
          split_mixed_at_lift2_indexed g₁ g₂ (by simpa [List.singleton_append] using hw)
        subst σ
        subst ys
        right
        refine ⟨ys₁ ++ g₂.expandRhs r₂.rhs τ ++ ys₂, ?_, ?_⟩
        · rw [hz, hu, hv]
          simp [concat_lift2_expandRhs, List.map_append, List.append_assoc]
        · refine ⟨r₂, ys₁, ys₂, τ, hr₂, ?_, rfl⟩
          simp [hc]
    | some f =>
        simp [liftRule2, hc] at hw hz
        obtain ⟨ys₁, ys₂, τ, hys, hσ, hu, hv⟩ :=
          split_mixed_at_lift2_indexed g₁ g₂ (by simpa [List.singleton_append] using hw)
        cases τ with
        | nil =>
            simp at hσ
        | cons f' τ' =>
            simp at hσ
            obtain ⟨hf, hτ⟩ := hσ
            cases hf
            subst ys
            right
            refine ⟨ys₁ ++ g₂.expandRhs r₂.rhs τ' ++ ys₂, ?_, ?_⟩
            · rw [hz, hu, hv]
              simp [concat_lift2_expandRhs, hτ, List.map_append, List.append_assoc]
            · refine ⟨r₂, ys₁, ys₂, τ', hr₂, ?_, rfl⟩
              simp [hc]

private lemma concat_mixed_derives (g₁ g₂ : IndexedGrammar T)
    {xs₀ xs : List g₁.ISym} {ys₀ ys : List g₂.ISym}
    {z : List (indexedConcat g₁ g₂).ISym}
    (hd₁ : g₁.Derives xs₀ xs) (hd₂ : g₂.Derives ys₀ ys)
    (h : (indexedConcat g₁ g₂).Derives
      (xs.map (concatLiftISym1 g₁ g₂) ++ ys.map (concatLiftISym2 g₁ g₂)) z) :
    ∃ xs' ys',
      z = xs'.map (concatLiftISym1 g₁ g₂) ++ ys'.map (concatLiftISym2 g₁ g₂) ∧
      g₁.Derives xs₀ xs' ∧ g₂.Derives ys₀ ys' := by
  induction h with
  | refl => exact ⟨xs, ys, rfl, hd₁, hd₂⟩
  | tail hprev ht ih =>
      obtain ⟨xs₁, ys₁, hz₁, hdxs₁, hdys₁⟩ := ih
      rw [hz₁] at ht
      rcases concat_mixed_step g₁ g₂ ht with hleft | hright
      · obtain ⟨xs₂, hz₂, hstep⟩ := hleft
        exact ⟨xs₂, ys₁, hz₂, hdxs₁.tail hstep, hdys₁⟩
      · obtain ⟨ys₂, hz₂, hstep⟩ := hright
        exact ⟨xs₁, ys₂, hz₂, hdxs₁, hdys₁.tail hstep⟩

private lemma concatLiftISym1_terminal_inv (g₁ g₂ : IndexedGrammar T)
    {xs : List g₁.ISym} {w : List T}
    (h : xs.map (concatLiftISym1 g₁ g₂) = w.map IndexedGrammar.ISym.terminal) :
    xs = w.map IndexedGrammar.ISym.terminal := by
  induction xs generalizing w with
  | nil => cases w <;> simp_all
  | cons x xs ih =>
      cases w with
      | nil => simp at h
      | cons a w =>
          cases x <;> simp [concatLiftISym1] at h ⊢
          exact ⟨h.1, ih h.2⟩

private lemma concatLiftISym2_terminal_inv (g₁ g₂ : IndexedGrammar T)
    {ys : List g₂.ISym} {w : List T}
    (h : ys.map (concatLiftISym2 g₁ g₂) = w.map IndexedGrammar.ISym.terminal) :
    ys = w.map IndexedGrammar.ISym.terminal := by
  induction ys generalizing w with
  | nil => cases w <;> simp_all
  | cons y ys ih =>
      cases w with
      | nil => simp at h
      | cons a w =>
          cases y <;> simp [concatLiftISym2] at h ⊢
          exact ⟨h.1, ih h.2⟩

private lemma concat_terminal_split (g₁ g₂ : IndexedGrammar T)
    {xs : List g₁.ISym} {ys : List g₂.ISym} {w : List T}
    (h : xs.map (concatLiftISym1 g₁ g₂) ++ ys.map (concatLiftISym2 g₁ g₂) =
      w.map IndexedGrammar.ISym.terminal) :
    ∃ w₁ w₂ : List T,
      w = w₁ ++ w₂ ∧
      xs = w₁.map IndexedGrammar.ISym.terminal ∧
      ys = w₂.map IndexedGrammar.ISym.terminal := by
  let w₁ := w.take xs.length
  let w₂ := w.drop xs.length
  have hw : w = w₁ ++ w₂ := by
    simp [w₁, w₂]
  have hleft :
      xs.map (concatLiftISym1 g₁ g₂) = w₁.map IndexedGrammar.ISym.terminal := by
    have ht := congrArg (List.take xs.length) h
    simpa [w₁, List.length_map] using ht
  have hright :
      ys.map (concatLiftISym2 g₁ g₂) = w₂.map IndexedGrammar.ISym.terminal := by
    have hd := congrArg (List.drop xs.length) h
    simpa [w₂, List.length_map] using hd
  exact ⟨w₁, w₂, hw, concatLiftISym1_terminal_inv g₁ g₂ hleft,
    concatLiftISym2_terminal_inv g₁ g₂ hright⟩

private theorem indexedConcat_language_product_subset (g₁ g₂ : IndexedGrammar T) :
    Set.Subset (indexedConcat g₁ g₂).Language (g₁.Language * g₂.Language) := by
  intro w hw
  change (indexedConcat g₁ g₂).Generates w at hw
  unfold IndexedGrammar.Generates at hw
  rcases hw.cases_head with hrefl | ⟨b, hfirst, hrest⟩
  · cases w <;> simp [indexedConcat] at hrefl
  · have hb := concat_first_step g₁ g₂ hfirst
    subst b
    have hmixed : (indexedConcat g₁ g₂).Derives
        (([IndexedGrammar.ISym.indexed g₁.initial []] : List g₁.ISym).map
            (concatLiftISym1 g₁ g₂) ++
          ([IndexedGrammar.ISym.indexed g₂.initial []] : List g₂.ISym).map
            (concatLiftISym2 g₁ g₂))
        (w.map IndexedGrammar.ISym.terminal) := by
      simpa [concatLiftISym1, concatLiftISym2] using hrest
    obtain ⟨xs, ys, hterm, hdxs, hdys⟩ :=
      concat_mixed_derives g₁ g₂
        (IndexedGrammar.deri_self g₁ [IndexedGrammar.ISym.indexed g₁.initial []])
        (IndexedGrammar.deri_self g₂ [IndexedGrammar.ISym.indexed g₂.initial []])
        hmixed
    obtain ⟨w₁, w₂, hw, hxs, hys⟩ := concat_terminal_split g₁ g₂ hterm.symm
    rw [Language.mul_def]
    refine ⟨w₁, ?_, w₂, ?_, hw.symm⟩
    · change g₁.Generates w₁
      unfold IndexedGrammar.Generates
      simpa [hxs] using hdxs
    · change g₂.Generates w₂
      unfold IndexedGrammar.Generates
      simpa [hys] using hdys

private theorem indexedConcat_language (g₁ g₂ : IndexedGrammar T) :
    (indexedConcat g₁ g₂).Language = g₁.Language * g₂.Language := by
  apply Set.Subset.antisymm
  · exact indexedConcat_language_product_subset g₁ g₂
  · exact indexedConcat_language_subset_product g₁ g₂

/-- Indexed languages are closed under concatenation. -/
public theorem Indexed_closedUnderConcatenation :
    ClosedUnderConcatenation (α := T) is_Indexed := by
  intro L₁ L₂ h₁ h₂
  obtain ⟨g₁, hg₁⟩ := h₁
  obtain ⟨g₂, hg₂⟩ := h₂
  refine ⟨indexedConcat g₁ g₂, ?_⟩
  rw [indexedConcat_language, hg₁, hg₂]
