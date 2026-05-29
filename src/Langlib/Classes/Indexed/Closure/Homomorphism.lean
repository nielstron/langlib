module

public import Langlib.Classes.Indexed.Definition
public import Langlib.Utilities.ClosurePredicates

/-! # Indexed Languages Are Closed Under String Homomorphism

This file maps terminal symbols in indexed grammar right-hand sides to strings of
terminals while preserving nonterminals and their stacks.

Proof idea: replace each terminal occurrence in every rule by the corresponding
output string and leave indexed nonterminals unchanged. The derivation
translation maps each sentential form by the same terminal expansion, giving
exactly the homomorphic image of the generated language.
-/

variable {α β : Type}

private def homIRhsSymbol {N F : Type} (h : α → List β) :
    IRhsSymbol α N F → List (IRhsSymbol β N F)
  | .terminal a => (h a).map IRhsSymbol.terminal
  | .nonterminal n push => [IRhsSymbol.nonterminal n push]

private def homIRule {N F : Type} (h : α → List β) (r : IRule α N F) :
    IRule β N F :=
  { lhs := r.lhs
    consume := r.consume
    rhs := r.rhs.flatMap (homIRhsSymbol h) }

private def homIndexedGrammar (g : IndexedGrammar α) (h : α → List β) :
    IndexedGrammar β where
  nt := g.nt
  flag := g.flag
  initial := g.initial
  rules := g.rules.map (homIRule h)

private def homISym (g : IndexedGrammar α) (h : α → List β) :
    g.ISym → List (homIndexedGrammar g h).ISym
  | .terminal a => (h a).map IndexedGrammar.ISym.terminal
  | .indexed n σ => [IndexedGrammar.ISym.indexed n σ]

private lemma homISym_terminals (g : IndexedGrammar α) (h : α → List β) (w : List α) :
    (w.map IndexedGrammar.ISym.terminal).flatMap (homISym g h) =
      (w.flatMap h).map IndexedGrammar.ISym.terminal := by
  induction w with
  | nil => rfl
  | cons a w ih => simp [homISym, ih, List.map_append]

private lemma hom_expandRhs (g : IndexedGrammar α) (h : α → List β)
    (rhs : List (IRhsSymbol α g.nt g.flag)) (σ : List g.flag) :
    (homIndexedGrammar g h).expandRhs (rhs.flatMap (homIRhsSymbol h)) σ =
      (g.expandRhs rhs σ).flatMap (homISym g h) := by
  induction rhs with
  | nil => rfl
  | cons s rhs ih =>
      cases s with
      | terminal a =>
          change (homIndexedGrammar g h).expandRhs
              ((h a).map IRhsSymbol.terminal ++ rhs.flatMap (homIRhsSymbol h)) σ =
            (h a).map IndexedGrammar.ISym.terminal ++
              (g.expandRhs rhs σ).flatMap (homISym g h)
          rw [show (homIndexedGrammar g h).expandRhs
              ((h a).map IRhsSymbol.terminal ++ rhs.flatMap (homIRhsSymbol h)) σ =
            (h a).map IndexedGrammar.ISym.terminal ++
              (homIndexedGrammar g h).expandRhs (rhs.flatMap (homIRhsSymbol h)) σ by
              simp [IndexedGrammar.expandRhs, List.map_append]]
          rw [ih]
      | nonterminal n push =>
          cases push <;> simpa [IndexedGrammar.expandRhs, homIRhsSymbol, homISym] using ih

private lemma hom_transforms (g : IndexedGrammar α) (h : α → List β)
    {w₁ w₂ : List g.ISym} (ht : g.Transforms w₁ w₂) :
    (homIndexedGrammar g h).Transforms
      (w₁.flatMap (homISym g h)) (w₂.flatMap (homISym g h)) := by
  obtain ⟨r, u, v, σ, hr, hw₁, hw₂⟩ := ht
  refine ⟨homIRule h r, u.flatMap (homISym g h), v.flatMap (homISym g h), σ,
    ?_, ?_, ?_⟩
  · exact List.mem_map.mpr ⟨r, hr, rfl⟩
  · cases hc : r.consume with
    | none =>
        rw [hc] at hw₁
        rw [hw₁]
        simp [homIRule, homISym, hc, List.flatMap_append]
    | some f =>
        rw [hc] at hw₁
        rw [hw₁]
        simp [homIRule, homISym, hc, List.flatMap_append]
  · rw [hw₂]
    simp [homIRule, List.flatMap_append, hom_expandRhs]

private lemma hom_derives (g : IndexedGrammar α) (h : α → List β)
    {w₁ w₂ : List g.ISym} (hd : g.Derives w₁ w₂) :
    (homIndexedGrammar g h).Derives
      (w₁.flatMap (homISym g h)) (w₂.flatMap (homISym g h)) := by
  induction hd with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ ht ih => exact ih.tail (hom_transforms g h ht)

private lemma mem_prod_singletons_flatMap (w : List α) (h : α → List β) (u : List β) :
    u ∈ (w.map fun a => ({h a} : Language β)).prod ↔ u = w.flatMap h := by
  induction w generalizing u with
  | nil => simp
  | cons a w ih =>
      simp only [List.map_cons, List.prod_cons, Language.mul_def]
      constructor
      · rintro ⟨u₁, hu₁, u₂, hu₂, rfl⟩
        rw [Set.mem_singleton_iff] at hu₁
        rw [hu₁, List.flatMap_cons]
        exact congrArg (h a ++ ·) ((ih u₂).mp hu₂)
      · intro hu
        refine ⟨h a, Set.mem_singleton _, w.flatMap h, (ih _).mpr rfl, ?_⟩
        simpa [List.flatMap_cons] using hu.symm

private theorem homIndexedGrammar_generates (g : IndexedGrammar α) (h : α → List β)
    (w : List α) :
    w ∈ g.Language → w.flatMap h ∈ (homIndexedGrammar g h).Language := by
  intro hw
  change (homIndexedGrammar g h).Generates (w.flatMap h)
  change g.Generates w at hw
  unfold IndexedGrammar.Generates at hw ⊢
  simpa [homISym, homISym_terminals] using hom_derives g h hw

private theorem homIndexedGrammar_language_subset (g : IndexedGrammar α) (h : α → List β) :
    Set.Subset ((g.Language).homomorphicImage h) (homIndexedGrammar g h).Language := by
  intro w hw
  simp only [Language.homomorphicImage, Language.subst] at hw
  obtain ⟨x, hx, hprod⟩ := hw
  rw [(mem_prod_singletons_flatMap x h w).mp hprod]
  exact homIndexedGrammar_generates g h x hx

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

private lemma indexed_not_mem_terminal_image (g : IndexedGrammar α) (h : α → List β)
    (a : α) (n : g.nt) (σ : List g.flag) :
    (IndexedGrammar.ISym.indexed n σ : (homIndexedGrammar g h).ISym) ∉
      (h a).map IndexedGrammar.ISym.terminal := by
  intro hm
  obtain ⟨b, _hb, hb⟩ := List.mem_map.mp hm
  cases hb

private lemma homISym_split_at_indexed (g : IndexedGrammar α) (h : α → List β)
    (s : List g.ISym) {u v : List (homIndexedGrammar g h).ISym}
    {n : g.nt} {σ : List g.flag} :
    s.flatMap (homISym g h) =
      u ++ ([IndexedGrammar.ISym.indexed n σ] : List (homIndexedGrammar g h).ISym) ++ v →
    ∃ s₁ s₂ : List g.ISym,
      s = s₁ ++ ([IndexedGrammar.ISym.indexed n σ] : List g.ISym) ++ s₂ ∧
      s₁.flatMap (homISym g h) = u ∧
      s₂.flatMap (homISym g h) = v := by
  induction s generalizing u with
  | nil =>
      intro hsplit
      have hlen := congrArg List.length hsplit
      simp at hlen
      omega
  | cons s₀ rest ih =>
      cases s₀ with
      | terminal a =>
          intro hsplit
          have hno := indexed_not_mem_terminal_image g h a n σ
          obtain ⟨u', hu, hrest⟩ :=
            append_eq_append_cons_of_not_mem
              (γ := (homIndexedGrammar g h).ISym)
              (x := IndexedGrammar.ISym.indexed n σ)
              (block := (h a).map IndexedGrammar.ISym.terminal)
              (rest := rest.flatMap (homISym g h)) (u := u) (v := v) hno
              (by simpa [homISym, List.flatMap_cons, List.append_assoc] using hsplit)
          obtain ⟨s₁, s₂, hs, hs₁, hs₂⟩ := ih (by simpa using hrest)
          refine ⟨IndexedGrammar.ISym.terminal a :: s₁, s₂, ?_, ?_, hs₂⟩
          · simp [hs]
          · simp [homISym, hs₁, hu]
      | indexed m τ =>
          intro hsplit
          by_cases heq :
              (IndexedGrammar.ISym.indexed m τ : (homIndexedGrammar g h).ISym) =
                (IndexedGrammar.ISym.indexed n σ : (homIndexedGrammar g h).ISym)
          · cases heq
            cases u with
            | nil =>
                simp only [homISym, List.flatMap_cons, List.singleton_append,
                  List.nil_append, List.cons.injEq] at hsplit
                refine ⟨[], rest, by simp, rfl, ?_⟩
                exact hsplit.2
            | cons uhd utl =>
                simp only [homISym, List.flatMap_cons,
                  List.cons_append, List.cons.injEq] at hsplit
                obtain ⟨_hhead, htail⟩ := hsplit
                obtain ⟨s₁, s₂, hs, hs₁, hs₂⟩ := ih htail
                refine ⟨IndexedGrammar.ISym.indexed n σ :: s₁, s₂, ?_, ?_, hs₂⟩
                · simp [hs]
                · simp [homISym, hs₁, _hhead]
          · have hno :
                (IndexedGrammar.ISym.indexed n σ : (homIndexedGrammar g h).ISym) ∉
                  ([IndexedGrammar.ISym.indexed m τ] :
                    List (homIndexedGrammar g h).ISym) := by
              intro hm
              simp at hm
              obtain ⟨hσ, hn⟩ := hm
              cases hn
              cases hσ
              exact heq rfl
            obtain ⟨u', hu, hrest⟩ :=
              append_eq_append_cons_of_not_mem
                (γ := (homIndexedGrammar g h).ISym)
                (x := IndexedGrammar.ISym.indexed n σ)
                (block := ([IndexedGrammar.ISym.indexed m τ] :
                  List (homIndexedGrammar g h).ISym))
                (rest := rest.flatMap (homISym g h)) (u := u) (v := v) hno
                (by simpa [homISym, List.flatMap_cons, List.append_assoc] using hsplit)
            obtain ⟨s₁, s₂, hs, hs₁, hs₂⟩ := ih (by simpa using hrest)
            refine ⟨IndexedGrammar.ISym.indexed m τ :: s₁, s₂, ?_, ?_, hs₂⟩
            · simp [hs]
            · simp [homISym, hs₁, hu]

private lemma hom_valid_step (g : IndexedGrammar α) (h : α → List β)
    {t₁ t₂ : List (homIndexedGrammar g h).ISym}
    {s₁ : List g.ISym}
    (ht₁ : t₁ = s₁.flatMap (homISym g h))
    (hs₁ : g.Derives [IndexedGrammar.ISym.indexed g.initial []] s₁)
    (ht : (homIndexedGrammar g h).Transforms t₁ t₂) :
    ∃ s₂ : List g.ISym,
      t₂ = s₂.flatMap (homISym g h) ∧
      g.Derives [IndexedGrammar.ISym.indexed g.initial []] s₂ := by
  obtain ⟨r, u, v, σ, hr, ht₁_rule, ht₂_rule⟩ := ht
  obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.mp hr
  cases hc : r₀.consume with
  | none =>
      simp [homIRule, hc] at ht₁_rule ht₂_rule
      have hsplit_eq : s₁.flatMap (homISym g h) =
          u ++ ([IndexedGrammar.ISym.indexed r₀.lhs σ] :
            List (homIndexedGrammar g h).ISym) ++ v := by
        simpa using ht₁.symm.trans ht₁_rule
      obtain ⟨pre, post, hs_split, hpre, hpost⟩ :=
        homISym_split_at_indexed g h s₁ hsplit_eq
      let s₂ := pre ++ g.expandRhs r₀.rhs σ ++ post
      refine ⟨s₂, ?_, ?_⟩
      · rw [ht₂_rule]
        calc
          u ++ ((homIndexedGrammar g h).expandRhs (r₀.rhs.flatMap (homIRhsSymbol h)) σ ++ v) =
              pre.flatMap (homISym g h) ++
                ((g.expandRhs r₀.rhs σ).flatMap (homISym g h) ++
                  post.flatMap (homISym g h)) := by
            rw [hpre, hpost, hom_expandRhs]
          _ = s₂.flatMap (homISym g h) := by
            simp [s₂, List.flatMap_append, List.append_assoc]
      · exact hs₁.tail
          ⟨r₀, pre, post, σ, hr₀, by simpa [hc] using hs_split, rfl⟩
  | some f =>
      simp [homIRule, hc] at ht₁_rule ht₂_rule
      have hsplit_eq : s₁.flatMap (homISym g h) =
          u ++ ([IndexedGrammar.ISym.indexed r₀.lhs (f :: σ)] :
            List (homIndexedGrammar g h).ISym) ++ v := by
        simpa using ht₁.symm.trans ht₁_rule
      obtain ⟨pre, post, hs_split, hpre, hpost⟩ :=
        homISym_split_at_indexed g h s₁ hsplit_eq
      let s₂ := pre ++ g.expandRhs r₀.rhs σ ++ post
      refine ⟨s₂, ?_, ?_⟩
      · rw [ht₂_rule]
        calc
          u ++ ((homIndexedGrammar g h).expandRhs (r₀.rhs.flatMap (homIRhsSymbol h)) σ ++ v) =
              pre.flatMap (homISym g h) ++
                ((g.expandRhs r₀.rhs σ).flatMap (homISym g h) ++
                  post.flatMap (homISym g h)) := by
            rw [hpre, hpost, hom_expandRhs]
          _ = s₂.flatMap (homISym g h) := by
            simp [s₂, List.flatMap_append, List.append_assoc]
      · exact hs₁.tail
          ⟨r₀, pre, post, σ, hr₀, by simpa [hc] using hs_split, rfl⟩

private lemma hom_valid_of_derives (g : IndexedGrammar α) (h : α → List β)
    {t : List (homIndexedGrammar g h).ISym}
    (hd : (homIndexedGrammar g h).Derives
      [IndexedGrammar.ISym.indexed (homIndexedGrammar g h).initial []] t) :
    ∃ s : List g.ISym,
      t = s.flatMap (homISym g h) ∧
      g.Derives [IndexedGrammar.ISym.indexed g.initial []] s := by
  induction hd with
  | refl =>
      exact ⟨[IndexedGrammar.ISym.indexed g.initial []], by simp [homIndexedGrammar, homISym],
        Relation.ReflTransGen.refl⟩
  | tail _ ht ih =>
      obtain ⟨s₁, ht₁, hs₁⟩ := ih
      exact hom_valid_step g h ht₁ hs₁ ht

private lemma all_source_symbols_terminal_of_hom_terminal (g : IndexedGrammar α) (h : α → List β)
    {s : List g.ISym} {w : List β}
    (heq : s.flatMap (homISym g h) = w.map IndexedGrammar.ISym.terminal) :
    ∀ x ∈ s, ∃ a, x = IndexedGrammar.ISym.terminal a := by
  intro x hx
  cases x with
  | terminal a => exact ⟨a, rfl⟩
  | indexed n σ =>
      have hmem : (IndexedGrammar.ISym.indexed n σ : (homIndexedGrammar g h).ISym) ∈
          s.flatMap (homISym g h) := by
        exact List.mem_flatMap.mpr ⟨IndexedGrammar.ISym.indexed n σ, hx, by simp [homISym]⟩
      rw [heq] at hmem
      obtain ⟨b, _hb, hb⟩ := List.mem_map.mp hmem
      cases hb

private lemma source_form_eq_terminal_map (g : IndexedGrammar α)
    {s : List g.ISym} (hterm : ∀ x ∈ s, ∃ a, x = IndexedGrammar.ISym.terminal a) :
    ∃ w : List α, s = w.map IndexedGrammar.ISym.terminal := by
  induction s with
  | nil => exact ⟨[], rfl⟩
  | cons x xs ih =>
      obtain ⟨a, rfl⟩ := hterm x (by simp)
      obtain ⟨w, hw⟩ := ih (fun y hy => hterm y (by simp [hy]))
      exact ⟨a :: w, by simp [hw]⟩

private theorem homIndexedGrammar_language_superset (g : IndexedGrammar α) (h : α → List β) :
    Set.Subset (homIndexedGrammar g h).Language ((g.Language).homomorphicImage h) := by
  intro w hw
  change (homIndexedGrammar g h).Generates w at hw
  unfold IndexedGrammar.Generates at hw
  obtain ⟨s, ht, hs⟩ := hom_valid_of_derives g h hw
  have hterm := all_source_symbols_terminal_of_hom_terminal g h ht.symm
  obtain ⟨x, rfl⟩ := source_form_eq_terminal_map g hterm
  rw [homISym_terminals] at ht
  have hinj : Function.Injective
      (IndexedGrammar.ISym.terminal : β → (homIndexedGrammar g h).ISym) := by
    intro a b hab
    cases hab
    rfl
  have hword : x.flatMap h = w := List.map_injective_iff.mpr hinj ht.symm
  simp only [Language.homomorphicImage, Language.subst]
  refine ⟨x, ?_, ?_⟩
  · change g.Generates x
    simpa [IndexedGrammar.Generates] using hs
  · exact (mem_prod_singletons_flatMap x h w).mpr hword.symm

/-- Indexed languages are closed under string homomorphism. -/
public theorem Indexed_closedUnderHomomorphism : ClosedUnderHomomorphism is_Indexed := by
  intro α β _ _ L h hL
  obtain ⟨g, hg⟩ := hL
  refine ⟨homIndexedGrammar g h, ?_⟩
  apply Set.Subset.antisymm
  · rw [← hg]
    exact homIndexedGrammar_language_superset g h
  ·
    rw [← hg]
    exact homIndexedGrammar_language_subset g h

/-- Indexed languages are closed under ε-free string homomorphism. -/
public theorem Indexed_closedUnderEpsFreeHomomorphism :
    ClosedUnderEpsFreeHomomorphism is_Indexed := by
  intro α β _ _ L h _heps hL
  exact Indexed_closedUnderHomomorphism L h hL
