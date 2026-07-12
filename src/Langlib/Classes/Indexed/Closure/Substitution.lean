module

public import Langlib.Classes.Indexed.Definition
public import Langlib.Grammars.Indexed.NormalForm.Derivation
public import Langlib.Utilities.ClosurePredicates
import Langlib.Classes.ContextFree.Closure.Substitution.Support
import Mathlib.Tactic

@[expose]
public section

/-!
# Indexed Languages Are Closed Under Substitution

The construction combines an outer indexed grammar with one tagged inner grammar for every
source letter. An outer terminal production launches the initial nonterminal of the corresponding
inner grammar. Outer and inner flags use disjoint tags, so the independent derivations can be
separated again.
-/

open List

variable {α β : Type}

private inductive SubstNT (g : IndexedGrammar α) (gs : α → IndexedGrammar β) where
  | outer : g.nt → SubstNT g gs
  | inner (a : α) : (gs a).nt → SubstNT g gs

private inductive SubstFlag (g : IndexedGrammar α) (gs : α → IndexedGrammar β) where
  | outer : g.flag → SubstFlag g gs
  | inner (a : α) : (gs a).flag → SubstFlag g gs

private def substLiftOuterRhs (g : IndexedGrammar α) (gs : α → IndexedGrammar β) :
    IRhsSymbol α g.nt g.flag → IRhsSymbol β (SubstNT g gs) (SubstFlag g gs)
  | .terminal a => .nonterminal (.inner a (gs a).initial) none
  | .nonterminal n none => .nonterminal (.outer n) none
  | .nonterminal n (some f) => .nonterminal (.outer n) (some (.outer f))

private def substLiftOuterRule (g : IndexedGrammar α) (gs : α → IndexedGrammar β)
    (r : IRule α g.nt g.flag) : IRule β (SubstNT g gs) (SubstFlag g gs) :=
  { lhs := .outer r.lhs
    consume := r.consume.map SubstFlag.outer
    rhs := r.rhs.map (substLiftOuterRhs g gs) }

private def substLiftInnerRhs (g : IndexedGrammar α) (gs : α → IndexedGrammar β)
    (a : α) :
    IRhsSymbol β (gs a).nt (gs a).flag →
      IRhsSymbol β (SubstNT g gs) (SubstFlag g gs)
  | .terminal b => .terminal b
  | .nonterminal n none => .nonterminal (.inner a n) none
  | .nonterminal n (some f) => .nonterminal (.inner a n) (some (.inner a f))

private def substLiftInnerRule (g : IndexedGrammar α) (gs : α → IndexedGrammar β)
    (a : α) (r : IRule β (gs a).nt (gs a).flag) :
    IRule β (SubstNT g gs) (SubstFlag g gs) :=
  { lhs := .inner a r.lhs
    consume := r.consume.map (SubstFlag.inner a)
    rhs := r.rhs.map (substLiftInnerRhs g gs a) }

private noncomputable def substInnerRules [Fintype α]
    (g : IndexedGrammar α) (gs : α → IndexedGrammar β) :
    List (IRule β (SubstNT g gs) (SubstFlag g gs)) :=
  Finset.univ.toList.flatMap fun a => (gs a).rules.map (substLiftInnerRule g gs a)

private noncomputable def indexedSubst [Fintype α]
    (g : IndexedGrammar α) (gs : α → IndexedGrammar β) : IndexedGrammar β where
  nt := SubstNT g gs
  flag := SubstFlag g gs
  initial := .outer g.initial
  rules := g.rules.map (substLiftOuterRule g gs) ++ substInnerRules g gs

private def ruleSourceSym (G : IndexedGrammar β)
    (r : IRule β G.nt G.flag) (σ : List G.flag) : G.ISym :=
  match r.consume with
  | none => .indexed r.lhs σ
  | some f => .indexed r.lhs (f :: σ)

private def RuleApplies (G : IndexedGrammar β)
    (r : IRule β G.nt G.flag) (w₁ w₂ : List G.ISym) : Prop :=
  ∃ (u v : List G.ISym) (σ : List G.flag),
    w₁ = u ++ [ruleSourceSym G r σ] ++ v ∧
    w₂ = u ++ G.expandRhs r.rhs σ ++ v

private theorem transforms_iff_ruleApplies {G : IndexedGrammar β}
    {w₁ w₂ : List G.ISym} :
    G.Transforms w₁ w₂ ↔ ∃ r ∈ G.rules, RuleApplies G r w₁ w₂ := by
  constructor
  · rintro ⟨r, u, v, σ, hr, hsource, htarget⟩
    refine ⟨r, hr, u, v, σ, ?_, htarget⟩
    cases hc : r.consume with
    | none =>
        rw [hc] at hsource
        simpa [ruleSourceSym, hc] using hsource
    | some f =>
        rw [hc] at hsource
        simpa [ruleSourceSym, hc] using hsource
  · rintro ⟨r, hr, u, v, σ, hsource, htarget⟩
    refine ⟨r, u, v, σ, hr, ?_, htarget⟩
    cases hc : r.consume with
    | none =>
        simpa [ruleSourceSym, hc] using hsource
    | some f =>
        simpa [ruleSourceSym, hc] using hsource

private def OuterStep [Fintype α] (g : IndexedGrammar α)
    (gs : α → IndexedGrammar β) (w₁ w₂ : List (indexedSubst g gs).ISym) : Prop :=
  ∃ r ∈ g.rules, RuleApplies (indexedSubst g gs) (substLiftOuterRule g gs r) w₁ w₂

private def InnerStep [Fintype α] (g : IndexedGrammar α)
    (gs : α → IndexedGrammar β) (w₁ w₂ : List (indexedSubst g gs).ISym) : Prop :=
  ∃ a, ∃ r ∈ (gs a).rules,
    RuleApplies (indexedSubst g gs) (substLiftInnerRule g gs a r) w₁ w₂

private theorem mem_substInnerRules [Fintype α] (g : IndexedGrammar α)
    (gs : α → IndexedGrammar β) (r : IRule β (SubstNT g gs) (SubstFlag g gs)) :
    r ∈ substInnerRules g gs ↔
      ∃ a, ∃ s ∈ (gs a).rules, substLiftInnerRule g gs a s = r := by
  classical
  simp [substInnerRules]

private theorem indexedSubst_step_iff [Fintype α] (g : IndexedGrammar α)
    (gs : α → IndexedGrammar β) {w₁ w₂ : List (indexedSubst g gs).ISym} :
    (indexedSubst g gs).Transforms w₁ w₂ ↔
      OuterStep g gs w₁ w₂ ∨ InnerStep g gs w₁ w₂ := by
  rw [transforms_iff_ruleApplies]
  constructor
  · rintro ⟨r, hr, happ⟩
    rw [show (indexedSubst g gs).rules =
        g.rules.map (substLiftOuterRule g gs) ++ substInnerRules g gs from rfl,
      List.mem_append] at hr
    rcases hr with hr | hr
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
      exact Or.inl ⟨s, hs, happ⟩
    · obtain ⟨a, s, hs, rfl⟩ := (mem_substInnerRules g gs r).mp hr
      exact Or.inr ⟨a, s, hs, happ⟩
  · rintro (⟨r, hr, happ⟩ | ⟨a, r, hr, happ⟩)
    · exact ⟨substLiftOuterRule g gs r, by
        simp only [indexedSubst, List.mem_append]
        exact Or.inl (List.mem_map.mpr ⟨r, hr, rfl⟩), happ⟩
    · exact ⟨substLiftInnerRule g gs a r, by
        simp only [indexedSubst, List.mem_append]
        exact Or.inr ((mem_substInnerRules g gs _).mpr ⟨a, r, hr, rfl⟩), happ⟩

private lemma ruleApplies_commute
    (G : IndexedGrammar β) (r₁ r₂ : IRule β G.nt G.flag)
    {u v w : List G.ISym}
    (h₁ : RuleApplies G r₁ u v) (h₂ : RuleApplies G r₂ v w)
    (hnot : ∀ (σ τ : List G.flag),
      (IndexedGrammar.ISym.indexed r₂.lhs τ : G.ISym) ∉ G.expandRhs r₁.rhs σ) :
    ∃ v', RuleApplies G r₂ u v' ∧ RuleApplies G r₁ v' w := by
  obtain ⟨p₁, q₁, σ₁, hu, hv⟩ := h₁
  obtain ⟨p₂, q₂, σ₂, hv', hw⟩ := h₂
  let t₁ : G.ISym := ruleSourceSym G r₁ σ₁
  let t₂ : G.ISym := ruleSourceSym G r₂ σ₂
  have hu' : u = p₁ ++ t₁ :: q₁ := by
    simpa [t₁, List.singleton_append] using hu
  have hv₂ : v = p₂ ++ t₂ :: q₂ := by
    simpa [t₂, List.singleton_append] using hv'
  have hmid : p₁ ++ G.expandRhs r₁.rhs σ₁ ++ q₁ = p₂ ++ t₂ :: q₂ := by
    rw [← hv₂, hv]
  have ht₂ : t₂ ∉ G.expandRhs r₁.rhs σ₁ := by
    cases hc : r₂.consume with
    | none => simpa [t₂, ruleSourceSym, hc] using hnot σ₁ σ₂
    | some f => simpa [t₂, ruleSourceSym, hc] using hnot σ₁ (f :: σ₂)
  rcases List.split_commute_of_not_mem p₁ q₁ p₂ q₂
      (G.expandRhs r₁.rhs σ₁) t₂ hmid ht₂ with
    ⟨z, hp₂, hq₁⟩ | ⟨z, hp₁, hq₂⟩
  · let v' := p₁ ++ t₁ :: z ++ G.expandRhs r₂.rhs σ₂ ++ q₂
    refine ⟨v', ?_, ?_⟩
    · refine ⟨p₁ ++ [t₁] ++ z, q₂, σ₂, ?_, ?_⟩
      · change u = (p₁ ++ [t₁] ++ z) ++ [t₂] ++ q₂
        rw [hu', hq₁]
        simp [List.append_assoc]
      · simp [v', List.append_assoc]
    · refine ⟨p₁, z ++ G.expandRhs r₂.rhs σ₂ ++ q₂, σ₁, ?_, ?_⟩
      · change v' = p₁ ++ [t₁] ++
            (z ++ G.expandRhs r₂.rhs σ₂ ++ q₂)
        simp [v', List.append_assoc]
      · rw [hw, hp₂]
        simp [List.append_assoc]
  · let v' := p₂ ++ G.expandRhs r₂.rhs σ₂ ++ z ++ t₁ :: q₁
    refine ⟨v', ?_, ?_⟩
    · refine ⟨p₂, z ++ [t₁] ++ q₁, σ₂, ?_, ?_⟩
      · change u = p₂ ++ [t₂] ++ (z ++ [t₁] ++ q₁)
        rw [hu', hp₁]
        simp [List.append_assoc]
      · simp [v', List.append_assoc]
    · refine ⟨p₂ ++ G.expandRhs r₂.rhs σ₂ ++ z, q₁, σ₁, ?_, ?_⟩
      · change v' = (p₂ ++ G.expandRhs r₂.rhs σ₂ ++ z) ++ [t₁] ++ q₁
        simp [v', List.append_assoc]
      · rw [hw, hq₂]
        simp [List.append_assoc]

private lemma outer_not_mem_inner_expand [Fintype α]
    (g : IndexedGrammar α) (gs : α → IndexedGrammar β)
    (a : α) (r : IRule β (gs a).nt (gs a).flag)
    (σ τ : List (SubstFlag g gs)) (n : g.nt) :
    (IndexedGrammar.ISym.indexed (SubstNT.outer n) τ : (indexedSubst g gs).ISym) ∉
      (indexedSubst g gs).expandRhs (substLiftInnerRule g gs a r).rhs σ := by
  intro h
  simp only [IndexedGrammar.expandRhs, substLiftInnerRule, List.mem_map] at h
  obtain ⟨s, hs, _heq⟩ := h
  obtain ⟨s', _hs', hs'⟩ := hs
  subst s
  cases s' with
  | terminal b => simp [substLiftInnerRhs] at _heq
  | nonterminal m push => cases push <;> simp [substLiftInnerRhs] at _heq

private lemma inner_outer_commute [Fintype α]
    (g : IndexedGrammar α) (gs : α → IndexedGrammar β)
    {u v w : List (indexedSubst g gs).ISym}
    (hi : InnerStep g gs u v) (ho : OuterStep g gs v w) :
    ∃ v', OuterStep g gs u v' ∧ InnerStep g gs v' w := by
  obtain ⟨a, ri, hri, happi⟩ := hi
  obtain ⟨ro, hro, happo⟩ := ho
  obtain ⟨v', houter, hinner⟩ := ruleApplies_commute
    (indexedSubst g gs) (substLiftInnerRule g gs a ri)
      (substLiftOuterRule g gs ro) happi happo (by
        intro σ τ
        exact outer_not_mem_inner_expand g gs a ri σ τ ro.lhs)
  exact ⟨v', ⟨ro, hro, houter⟩, ⟨a, ri, hri, hinner⟩⟩

private lemma inner_derives_outer_commute [Fintype α]
    (g : IndexedGrammar α) (gs : α → IndexedGrammar β)
    {u v w : List (indexedSubst g gs).ISym}
    (hi : Relation.ReflTransGen (InnerStep g gs) u v)
    (ho : OuterStep g gs v w) :
    ∃ v', OuterStep g gs u v' ∧ Relation.ReflTransGen (InnerStep g gs) v' w := by
  induction hi generalizing w with
  | refl => exact ⟨w, ho, Relation.ReflTransGen.refl⟩
  | tail hprev hlast ih =>
      obtain ⟨y, houter, hinner⟩ := inner_outer_commute g gs hlast ho
      obtain ⟨z, houter', hinners⟩ := ih houter
      exact ⟨z, houter', hinners.tail hinner⟩

private lemma derives_outer_then_inner [Fintype α]
    (g : IndexedGrammar α) (gs : α → IndexedGrammar β)
    {u v : List (indexedSubst g gs).ISym}
    (h : (indexedSubst g gs).Derives u v) :
    ∃ mid,
      Relation.ReflTransGen (OuterStep g gs) u mid ∧
      Relation.ReflTransGen (InnerStep g gs) mid v := by
  induction h with
  | refl => exact ⟨u, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
  | tail _ hstep ih =>
      obtain ⟨mid, houter, hinner⟩ := ih
      rcases (indexedSubst_step_iff g gs).mp hstep with hstep | hstep
      · obtain ⟨mid', hmove, hinner'⟩ :=
          inner_derives_outer_commute g gs hinner hstep
        exact ⟨mid', houter.tail hmove, hinner'⟩
      · exact ⟨mid, houter, hinner.tail hstep⟩

private inductive OuterDecoratedSym (g : IndexedGrammar α) where
  | terminal : α → List g.flag → OuterDecoratedSym g
  | indexed : g.nt → List g.flag → OuterDecoratedSym g

private def outerErase (g : IndexedGrammar α) : OuterDecoratedSym g → g.ISym
  | .terminal a _ => .terminal a
  | .indexed n σ => .indexed n σ

private def outerEncode [Fintype α] (g : IndexedGrammar α)
    (gs : α → IndexedGrammar β) : OuterDecoratedSym g → (indexedSubst g gs).ISym
  | .terminal a σ => .indexed (.inner a (gs a).initial) (σ.map SubstFlag.outer)
  | .indexed n σ => .indexed (.outer n) (σ.map SubstFlag.outer)

private def decorateOuterRhs (g : IndexedGrammar α) (σ : List g.flag) :
    IRhsSymbol α g.nt g.flag → OuterDecoratedSym g
  | .terminal a => .terminal a σ
  | .nonterminal n none => .indexed n σ
  | .nonterminal n (some f) => .indexed n (f :: σ)

private lemma outerErase_decorate_expand (g : IndexedGrammar α)
    (rhs : List (IRhsSymbol α g.nt g.flag)) (σ : List g.flag) :
    (rhs.map (decorateOuterRhs g σ)).map (outerErase g) = g.expandRhs rhs σ := by
  simp only [IndexedGrammar.expandRhs, List.map_map]
  apply List.map_congr_left
  intro s _hs
  cases s with
  | terminal a => rfl
  | nonterminal n push => cases push <;> rfl

private lemma outerEncode_decorate_expand [Fintype α]
    (g : IndexedGrammar α) (gs : α → IndexedGrammar β)
    (rhs : List (IRhsSymbol α g.nt g.flag)) (σ : List g.flag) :
    (rhs.map (decorateOuterRhs g σ)).map (outerEncode g gs) =
      (indexedSubst g gs).expandRhs
        (rhs.map (substLiftOuterRhs g gs)) (σ.map SubstFlag.outer) := by
  unfold IndexedGrammar.expandRhs
  rw [List.map_map, List.map_map]
  congr! 2
  funext s
  cases s with
  | terminal a => rfl
  | nonterminal n push => cases push <;> rfl

private lemma outerEncode_injective [Fintype α]
    (g : IndexedGrammar α) (gs : α → IndexedGrammar β) :
    Function.Injective (outerEncode g gs) := by
  intro x y h
  cases x with
  | terminal a σ =>
      cases y with
      | terminal b τ =>
          simp [outerEncode] at h ⊢
          obtain ⟨hab, hσ⟩ := h
          cases hab
          exact ⟨rfl, List.map_injective_iff.mpr (by intro x y h; cases h; rfl) hσ⟩
      | indexed n τ => simp [outerEncode] at h
  | indexed n σ =>
      cases y with
      | terminal a τ => simp [outerEncode] at h
      | indexed m τ =>
          simp [outerEncode] at h ⊢
          exact ⟨by cases h.1; rfl,
            List.map_injective_iff.mpr (by intro x y h; cases h; rfl) h.2⟩

private lemma map_eq_append_singleton_of_injective {γ δ : Type} {f : γ → δ}
    (hf : Function.Injective f) {xs : List γ} {x : γ} {u v : List δ}
    (h : xs.map f = u ++ [f x] ++ v) :
    ∃ xs₁ xs₂ : List γ,
      xs = xs₁ ++ [x] ++ xs₂ ∧ u = xs₁.map f ∧ v = xs₂.map f := by
  have h' : xs.map f = u ++ f x :: v := by simpa using h
  obtain ⟨xs₁, rest, hxs, hu, hrest⟩ := List.map_eq_append_iff.mp h'
  cases rest with
  | nil => simp at hrest
  | cons y xs₂ =>
      simp only [List.map_cons, List.cons.injEq] at hrest
      obtain ⟨hy, hv⟩ := hrest
      have hyx : y = x := hf hy
      subst y
      exact ⟨xs₁, xs₂, by simpa [List.singleton_append] using hxs, hu.symm, hv.symm⟩

private lemma outer_unlift_step [Fintype α]
    (g : IndexedGrammar α) (gs : α → IndexedGrammar β)
    (d : List (OuterDecoratedSym g)) {z : List (indexedSubst g gs).ISym}
    (h : OuterStep g gs (d.map (outerEncode g gs)) z) :
    ∃ d' : List (OuterDecoratedSym g),
      z = d'.map (outerEncode g gs) ∧
      g.Transforms (d.map (outerErase g)) (d'.map (outerErase g)) := by
  obtain ⟨r, hr, u, v, σ, hsource, htarget⟩ := h
  cases hc : r.consume with
  | none =>
      have hsource' : d.map (outerEncode g gs) =
          u ++ [IndexedGrammar.ISym.indexed (SubstNT.outer r.lhs) σ] ++ v := by
        simpa [ruleSourceSym, substLiftOuterRule, hc] using hsource
      have hmem :
          (IndexedGrammar.ISym.indexed (SubstNT.outer r.lhs) σ :
            (indexedSubst g gs).ISym) ∈ d.map (outerEncode g gs) := by
        rw [hsource']
        simp
      obtain ⟨s, _hs, hs⟩ := List.mem_map.mp hmem
      cases s with
      | terminal a τ => simp [outerEncode] at hs
      | indexed n τ =>
          simp [outerEncode] at hs
          obtain ⟨hn, hτ⟩ := hs
          cases hn
          have hsource'' : d.map (outerEncode g gs) =
              u ++ [(outerEncode g gs) (OuterDecoratedSym.indexed r.lhs τ)] ++ v := by
            rw [hsource']
            simp [outerEncode, hτ]
          obtain ⟨d₁, d₂, hd, hu, hv⟩ :=
            map_eq_append_singleton_of_injective (outerEncode_injective g gs) hsource''
          let d' := d₁ ++ r.rhs.map (decorateOuterRhs g τ) ++ d₂
          refine ⟨d', ?_, ?_⟩
          · rw [htarget, hu, hv, ← hτ]
            simp only [substLiftOuterRule]
            rw [← outerEncode_decorate_expand g gs r.rhs τ]
            simp [d', List.map_append, List.append_assoc]
          · refine ⟨r, d₁.map (outerErase g), d₂.map (outerErase g), τ, hr, ?_, ?_⟩
            · simp [hc, hd, outerErase, List.map_append]
            · simp only [d', List.map_append]
              rw [outerErase_decorate_expand]
  | some f =>
      have hsource' : d.map (outerEncode g gs) =
          u ++ [IndexedGrammar.ISym.indexed (SubstNT.outer r.lhs)
            (SubstFlag.outer f :: σ)] ++ v := by
        simpa [ruleSourceSym, substLiftOuterRule, hc] using hsource
      have hmem :
          (IndexedGrammar.ISym.indexed (SubstNT.outer r.lhs)
            (SubstFlag.outer f :: σ) : (indexedSubst g gs).ISym) ∈
              d.map (outerEncode g gs) := by
        rw [hsource']
        simp
      obtain ⟨s, _hs, hs⟩ := List.mem_map.mp hmem
      cases s with
      | terminal a τ => simp [outerEncode] at hs
      | indexed n τ =>
          simp [outerEncode] at hs
          obtain ⟨hn, hτ⟩ := hs
          cases hn
          cases τ with
          | nil => simp at hτ
          | cons f' τ =>
              simp at hτ
              obtain ⟨hf, hτ⟩ := hτ
              cases hf
              have hsource'' : d.map (outerEncode g gs) =
                  u ++ [(outerEncode g gs)
                    (OuterDecoratedSym.indexed r.lhs (f :: τ))] ++ v := by
                rw [hsource']
                simp [outerEncode, hτ]
              obtain ⟨d₁, d₂, hd, hu, hv⟩ :=
                map_eq_append_singleton_of_injective (outerEncode_injective g gs) hsource''
              let d' := d₁ ++ r.rhs.map (decorateOuterRhs g τ) ++ d₂
              refine ⟨d', ?_, ?_⟩
              · rw [htarget, hu, hv, ← hτ]
                simp only [substLiftOuterRule]
                rw [← outerEncode_decorate_expand g gs r.rhs τ]
                simp [d', List.map_append, List.append_assoc]
              · refine ⟨r, d₁.map (outerErase g), d₂.map (outerErase g), τ, hr, ?_, ?_⟩
                · simp [hc, hd, outerErase, List.map_append]
                · simp only [d', List.map_append]
                  rw [outerErase_decorate_expand]

private lemma outer_unlift_derives [Fintype α]
    (g : IndexedGrammar α) (gs : α → IndexedGrammar β)
    {mid : List (indexedSubst g gs).ISym}
    (h : Relation.ReflTransGen (OuterStep g gs)
      [(outerEncode g gs) (OuterDecoratedSym.indexed g.initial [])] mid) :
    ∃ d : List (OuterDecoratedSym g),
      mid = d.map (outerEncode g gs) ∧
      g.Derives [.indexed g.initial []] (d.map (outerErase g)) := by
  induction h with
  | refl =>
      exact ⟨[.indexed g.initial []], rfl, Relation.ReflTransGen.refl⟩
  | tail _ hstep ih =>
      obtain ⟨d, rfl, hd⟩ := ih
      obtain ⟨d', rfl, hstep'⟩ := outer_unlift_step g gs d hstep
      exact ⟨d', rfl, hd.tail hstep'⟩

private lemma innerStep_outer_mem [Fintype α]
    (g : IndexedGrammar α) (gs : α → IndexedGrammar β)
    {u v : List (indexedSubst g gs).ISym}
    (h : InnerStep g gs u v) (n : g.nt) (τ : List (SubstFlag g gs))
    (hmem : (IndexedGrammar.ISym.indexed (SubstNT.outer n) τ :
      (indexedSubst g gs).ISym) ∈ u) :
    (IndexedGrammar.ISym.indexed (SubstNT.outer n) τ :
      (indexedSubst g gs).ISym) ∈ v := by
  obtain ⟨a, r, _hr, p, q, σ, hsource, htarget⟩ := h
  have hne :
      (IndexedGrammar.ISym.indexed (SubstNT.outer n) τ :
        (indexedSubst g gs).ISym) ≠
        ruleSourceSym (indexedSubst g gs) (substLiftInnerRule g gs a r) σ := by
    cases hc : r.consume <;>
      simp [ruleSourceSym, substLiftInnerRule, hc]
  rw [hsource] at hmem
  simp only [List.mem_append, List.mem_singleton] at hmem
  rcases hmem with (hp | heq) | hq
  · rw [htarget]
    simp [hp]
  · exact False.elim (hne heq)
  · rw [htarget]
    simp [hq]

private lemma innerDerives_outer_mem [Fintype α]
    (g : IndexedGrammar α) (gs : α → IndexedGrammar β)
    {u v : List (indexedSubst g gs).ISym}
    (h : Relation.ReflTransGen (InnerStep g gs) u v)
    (n : g.nt) (τ : List (SubstFlag g gs))
    (hmem : (IndexedGrammar.ISym.indexed (SubstNT.outer n) τ :
      (indexedSubst g gs).ISym) ∈ u) :
    (IndexedGrammar.ISym.indexed (SubstNT.outer n) τ :
      (indexedSubst g gs).ISym) ∈ v := by
  induction h with
  | refl => exact hmem
  | tail _ hstep ih => exact innerStep_outer_mem g gs hstep n τ ih

private lemma innerDerives_to_derives [Fintype α]
    (g : IndexedGrammar α) (gs : α → IndexedGrammar β)
    {u v : List (indexedSubst g gs).ISym}
    (h : Relation.ReflTransGen (InnerStep g gs) u v) :
    (indexedSubst g gs).Derives u v := by
  exact Relation.ReflTransGen.mono
    (fun _ _ hs => (indexedSubst_step_iff g gs).mpr (Or.inr hs)) h

private lemma decorated_all_terminal_of_inner_derives [Fintype α]
    (g : IndexedGrammar α) (gs : α → IndexedGrammar β)
    (d : List (OuterDecoratedSym g)) (w : List β)
    (h : Relation.ReflTransGen (InnerStep g gs)
      (d.map (outerEncode g gs))
      (w.map (IndexedGrammar.ISym.terminal (g := indexedSubst g gs)))) :
    ∀ s ∈ d, ∃ a σ, s = OuterDecoratedSym.terminal a σ := by
  intro s hs
  cases s with
  | terminal a σ => exact ⟨a, σ, rfl⟩
  | indexed n σ =>
      have hmem :
          (IndexedGrammar.ISym.indexed (SubstNT.outer n) (σ.map SubstFlag.outer) :
            (indexedSubst g gs).ISym) ∈ d.map (outerEncode g gs) :=
        List.mem_map.mpr ⟨OuterDecoratedSym.indexed n σ, hs, rfl⟩
      have hfinal := innerDerives_outer_mem g gs h n (σ.map SubstFlag.outer) hmem
      obtain ⟨b, _hb, heq⟩ := List.mem_map.mp hfinal
      simp at heq

private def innerEncode [Fintype α]
    (g : IndexedGrammar α) (gs : α → IndexedGrammar β)
    (a : α) (suffix : List g.flag) :
    (gs a).ISym → (indexedSubst g gs).ISym
  | .terminal b => .terminal b
  | .indexed n τ => .indexed (.inner a n)
      (τ.map (SubstFlag.inner a) ++ suffix.map SubstFlag.outer)

private lemma innerEncode_injective [Fintype α]
    (g : IndexedGrammar α) (gs : α → IndexedGrammar β)
    (a : α) (suffix : List g.flag) :
    Function.Injective (innerEncode g gs a suffix) := by
  intro x y h
  cases x with
  | terminal x =>
      cases y with
      | terminal y => simpa [innerEncode] using h
      | indexed n τ => simp [innerEncode] at h
  | indexed n σ =>
      cases y with
      | terminal y => simp [innerEncode] at h
      | indexed m τ =>
          simp [innerEncode] at h ⊢
          obtain ⟨hn, hstack⟩ := h
          cases hn
          exact ⟨rfl, List.map_injective_iff.mpr (by intro x y h; cases h; rfl) hstack⟩

private lemma innerEncode_expand [Fintype α]
    (g : IndexedGrammar α) (gs : α → IndexedGrammar β)
    (a : α) (suffix : List g.flag)
    (rhs : List (IRhsSymbol β (gs a).nt (gs a).flag)) (τ : List (gs a).flag) :
    ((gs a).expandRhs rhs τ).map (innerEncode g gs a suffix) =
      (indexedSubst g gs).expandRhs (rhs.map (substLiftInnerRhs g gs a))
        (τ.map (SubstFlag.inner a) ++ suffix.map SubstFlag.outer) := by
  unfold IndexedGrammar.expandRhs
  rw [List.map_map, List.map_map]
  congr! 2
  funext s
  cases s with
  | terminal b => rfl
  | nonterminal n push => cases push <;> simp [innerEncode, substLiftInnerRhs]

private lemma inner_lift_step [Fintype α]
    (g : IndexedGrammar α) (gs : α → IndexedGrammar β)
    (a : α) (suffix : List g.flag) {u v : List (gs a).ISym}
    (h : (gs a).Transforms u v) :
    InnerStep g gs
      (u.map (innerEncode g gs a suffix))
      (v.map (innerEncode g gs a suffix)) := by
  obtain ⟨r, p, q, τ, hr, hsource, htarget⟩ := h
  refine ⟨a, r, hr, p.map (innerEncode g gs a suffix),
    q.map (innerEncode g gs a suffix),
    τ.map (SubstFlag.inner a) ++ suffix.map SubstFlag.outer, ?_, ?_⟩
  · cases hc : r.consume with
    | none =>
        rw [hc] at hsource
        simpa [ruleSourceSym, substLiftInnerRule, hc, innerEncode, List.map_append]
          using congrArg (List.map (innerEncode g gs a suffix)) hsource
    | some f =>
        rw [hc] at hsource
        simpa [ruleSourceSym, substLiftInnerRule, hc, innerEncode, List.map_append]
          using congrArg (List.map (innerEncode g gs a suffix)) hsource
  · rw [htarget]
    simp [substLiftInnerRule, innerEncode_expand, List.map_append]

private lemma inner_lift_derives [Fintype α]
    (g : IndexedGrammar α) (gs : α → IndexedGrammar β)
    (a : α) (suffix : List g.flag) {u v : List (gs a).ISym}
    (h : (gs a).Derives u v) :
    Relation.ReflTransGen (InnerStep g gs)
      (u.map (innerEncode g gs a suffix))
      (v.map (innerEncode g gs a suffix)) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail (inner_lift_step g gs a suffix hstep)

private lemma inner_unlift_step [Fintype α]
    (g : IndexedGrammar α) (gs : α → IndexedGrammar β)
    (a : α) (suffix : List g.flag) (d : List (gs a).ISym)
    {z : List (indexedSubst g gs).ISym}
    (h : InnerStep g gs (d.map (innerEncode g gs a suffix)) z) :
    ∃ d' : List (gs a).ISym,
      z = d'.map (innerEncode g gs a suffix) ∧ (gs a).Transforms d d' := by
  obtain ⟨b, r, hr, p, q, σ, hsource, htarget⟩ := h
  cases hc : r.consume with
  | none =>
      have hsource' : d.map (innerEncode g gs a suffix) =
          p ++ [IndexedGrammar.ISym.indexed (SubstNT.inner b r.lhs) σ] ++ q := by
        simpa [ruleSourceSym, substLiftInnerRule, hc] using hsource
      have hmem :
          (IndexedGrammar.ISym.indexed (SubstNT.inner b r.lhs) σ :
            (indexedSubst g gs).ISym) ∈ d.map (innerEncode g gs a suffix) := by
        rw [hsource']
        simp
      obtain ⟨s, _hs, hs⟩ := List.mem_map.mp hmem
      cases s with
      | terminal c => simp [innerEncode] at hs
      | indexed n τ =>
          simp [innerEncode] at hs
          obtain ⟨hnt, hstack⟩ := hs
          cases hnt
          have hsource'' : d.map (innerEncode g gs a suffix) =
              p ++ [(innerEncode g gs a suffix)
                (IndexedGrammar.ISym.indexed r.lhs τ)] ++ q := by
            rw [hsource']
            simp [innerEncode, hstack]
          obtain ⟨d₁, d₂, hd, hp, hq⟩ :=
            map_eq_append_singleton_of_injective
              (innerEncode_injective g gs a suffix) hsource''
          let d' := d₁ ++ (gs a).expandRhs r.rhs τ ++ d₂
          refine ⟨d', ?_, ?_⟩
          · rw [htarget, hp, hq, ← hstack]
            simp only [substLiftInnerRule]
            rw [← innerEncode_expand g gs a suffix r.rhs τ]
            simp [d', List.map_append, List.append_assoc]
          · refine ⟨r, d₁, d₂, τ, hr, ?_, rfl⟩
            simp [hc, hd]
  | some f =>
      have hsource' : d.map (innerEncode g gs a suffix) =
          p ++ [IndexedGrammar.ISym.indexed (SubstNT.inner b r.lhs)
            (SubstFlag.inner b f :: σ)] ++ q := by
        simpa [ruleSourceSym, substLiftInnerRule, hc] using hsource
      have hmem :
          (IndexedGrammar.ISym.indexed (SubstNT.inner b r.lhs)
            (SubstFlag.inner b f :: σ) : (indexedSubst g gs).ISym) ∈
              d.map (innerEncode g gs a suffix) := by
        rw [hsource']
        simp
      obtain ⟨s, _hs, hs⟩ := List.mem_map.mp hmem
      cases s with
      | terminal c => simp [innerEncode] at hs
      | indexed n τ =>
          simp [innerEncode] at hs
          obtain ⟨hnt, hstack⟩ := hs
          cases hnt
          cases τ with
          | nil =>
              cases suffix with
              | nil => simp at hstack
              | cons x xs => simp at hstack
          | cons f' τ =>
              simp at hstack
              obtain ⟨hf, hstack⟩ := hstack
              cases hf
              have hsource'' : d.map (innerEncode g gs a suffix) =
                  p ++ [(innerEncode g gs a suffix)
                    (IndexedGrammar.ISym.indexed r.lhs (f :: τ))] ++ q := by
                rw [hsource']
                simp [innerEncode, hstack]
              obtain ⟨d₁, d₂, hd, hp, hq⟩ :=
                map_eq_append_singleton_of_injective
                  (innerEncode_injective g gs a suffix) hsource''
              let d' := d₁ ++ (gs a).expandRhs r.rhs τ ++ d₂
              refine ⟨d', ?_, ?_⟩
              · rw [htarget, hp, hq, ← hstack]
                simp only [substLiftInnerRule]
                rw [← innerEncode_expand g gs a suffix r.rhs τ]
                simp [d', List.map_append, List.append_assoc]
              · refine ⟨r, d₁, d₂, τ, hr, ?_, rfl⟩
                simp [hc, hd]

private lemma inner_unlift_derives [Fintype α]
    (g : IndexedGrammar α) (gs : α → IndexedGrammar β)
    (a : α) (suffix : List g.flag) {d : List (gs a).ISym}
    {z : List (indexedSubst g gs).ISym}
    (h : Relation.ReflTransGen (InnerStep g gs)
      (d.map (innerEncode g gs a suffix)) z) :
    ∃ d' : List (gs a).ISym,
      z = d'.map (innerEncode g gs a suffix) ∧ (gs a).Derives d d' := by
  induction h with
  | refl => exact ⟨d, rfl, Relation.ReflTransGen.refl⟩
  | tail _ hstep ih =>
      obtain ⟨mid, rfl, hmid⟩ := ih
      obtain ⟨d', rfl, hstep'⟩ := inner_unlift_step g gs a suffix mid hstep
      exact ⟨d', rfl, hmid.tail hstep'⟩

private lemma outerStep_impossible_from_inner_encoded [Fintype α]
    (g : IndexedGrammar α) (gs : α → IndexedGrammar β)
    (a : α) (suffix : List g.flag) (d : List (gs a).ISym)
    {z : List (indexedSubst g gs).ISym}
    (h : OuterStep g gs (d.map (innerEncode g gs a suffix)) z) : False := by
  obtain ⟨r, _hr, p, q, σ, hsource, _htarget⟩ := h
  have hmem : ruleSourceSym (indexedSubst g gs) (substLiftOuterRule g gs r) σ ∈
      d.map (innerEncode g gs a suffix) := by
    rw [hsource]
    simp
  obtain ⟨s, _hs, hs⟩ := List.mem_map.mp hmem
  cases hc : r.consume <;> cases s <;>
    simp [ruleSourceSym, substLiftOuterRule, hc, innerEncode] at hs

private lemma inner_unlift_combined_derives [Fintype α]
    (g : IndexedGrammar α) (gs : α → IndexedGrammar β)
    (a : α) (suffix : List g.flag) {d : List (gs a).ISym}
    {z : List (indexedSubst g gs).ISym}
    (h : (indexedSubst g gs).Derives (d.map (innerEncode g gs a suffix)) z) :
    ∃ d' : List (gs a).ISym,
      z = d'.map (innerEncode g gs a suffix) ∧ (gs a).Derives d d' := by
  induction h with
  | refl => exact ⟨d, rfl, Relation.ReflTransGen.refl⟩
  | tail _ hstep ih =>
      obtain ⟨mid, rfl, hmid⟩ := ih
      rcases (indexedSubst_step_iff g gs).mp hstep with houter | hinner
      · exact False.elim (outerStep_impossible_from_inner_encoded g gs a suffix mid houter)
      · obtain ⟨d', rfl, hstep'⟩ := inner_unlift_step g gs a suffix mid hinner
        exact ⟨d', rfl, hmid.tail hstep'⟩

private lemma innerEncode_terminal_inv [Fintype α]
    (g : IndexedGrammar α) (gs : α → IndexedGrammar β)
    (a : α) (suffix : List g.flag) {d : List (gs a).ISym} {w : List β}
    (h : d.map (innerEncode g gs a suffix) =
      w.map (IndexedGrammar.ISym.terminal (g := indexedSubst g gs))) :
    d = w.map (IndexedGrammar.ISym.terminal (g := gs a)) := by
  induction d generalizing w with
  | nil => cases w <;> simp_all
  | cons s d ih =>
      cases w with
      | nil => simp at h
      | cons b w =>
          cases s <;> simp [innerEncode] at h ⊢
          exact ⟨h.1, ih h.2⟩

private lemma extract_substitution_blocks [Fintype α]
    (g : IndexedGrammar α) (gs : α → IndexedGrammar β)
    (d : List (OuterDecoratedSym g)) (w : List β)
    (hall : ∀ s ∈ d, ∃ a σ, s = OuterDecoratedSym.terminal a σ)
    (hder : (indexedSubst g gs).Derives
      (d.map (outerEncode g gs))
      (w.map (IndexedGrammar.ISym.terminal (g := indexedSubst g gs)))) :
    ∃ xs : List α, ∃ W : List (List β),
      d.map (outerErase g) = xs.map (IndexedGrammar.ISym.terminal (g := g)) ∧
      w = W.flatten ∧
      List.Forall₂ (fun u a => u ∈ (gs a).Language) W xs := by
  induction d generalizing w with
  | nil =>
      have hcount := IndexedGrammar.exists_derivesIn_of_derives hder
      obtain ⟨n, hn⟩ := hcount
      obtain ⟨_, hnil⟩ := IndexedGrammar.derivesIn_nil_left_eq (g := indexedSubst g gs) hn
      have hw : w = [] := by simpa using hnil
      subst w
      exact ⟨[], [], rfl, rfl, List.Forall₂.nil⟩
  | cons s d ih =>
      obtain ⟨a, suffix, rfl⟩ := hall s (by simp)
      have hall' : ∀ x ∈ d, ∃ a σ, x = OuterDecoratedSym.terminal a σ := by
        intro x hx
        exact hall x (by simp [hx])
      have hder' : (indexedSubst g gs).Derives
          ([IndexedGrammar.ISym.indexed (SubstNT.inner a (gs a).initial)
              (suffix.map SubstFlag.outer)] ++ d.map (outerEncode g gs))
          (w.map (IndexedGrammar.ISym.terminal (g := indexedSubst g gs))) := by
        simpa [outerEncode] using hder
      obtain ⟨w₁, w₂, hw, hleft, hright⟩ :=
        IndexedGrammar.derives_append_to_terminals_split hder'
      have hleft' : (indexedSubst g gs).Derives
          (([IndexedGrammar.ISym.indexed (gs a).initial []] : List (gs a).ISym).map
            (innerEncode g gs a suffix))
          (w₁.map (IndexedGrammar.ISym.terminal (g := indexedSubst g gs))) := by
        simpa [innerEncode] using hleft
      obtain ⟨endg, hend, hinner⟩ :=
        inner_unlift_combined_derives g gs a suffix hleft'
      have hend' : endg =
          w₁.map (IndexedGrammar.ISym.terminal (g := gs a)) :=
        innerEncode_terminal_inv g gs a suffix hend.symm
      have hw₁ : w₁ ∈ (gs a).Language := by
        change (gs a).Generates w₁
        unfold IndexedGrammar.Generates
        simpa [hend'] using hinner
      obtain ⟨xs, W, hd, hw₂, hW⟩ := ih w₂ hall' hright
      refine ⟨a :: xs, w₁ :: W, ?_, ?_, ?_⟩
      · simp [outerErase, hd]
      · simp [hw, hw₂]
      · exact List.Forall₂.cons hw₁ hW

private lemma forall₂_languages_map {gs : α → IndexedGrammar β}
    {W : List (List β)} {xs : List α}
    (h : List.Forall₂ (fun u a => u ∈ (gs a).Language) W xs) :
    List.Forall₂ (fun u L => u ∈ L) W (xs.map fun a => (gs a).Language) := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hmem _ ih => exact List.Forall₂.cons hmem ih

private theorem indexedSubst_language_subset [Fintype α]
    (g : IndexedGrammar α) (gs : α → IndexedGrammar β) :
    Set.Subset (indexedSubst g gs).Language
      (g.Language.subst fun a => (gs a).Language) := by
  intro w hw
  change (indexedSubst g gs).Generates w at hw
  unfold IndexedGrammar.Generates at hw
  obtain ⟨mid, houter, hinner⟩ := derives_outer_then_inner g gs hw
  have houter' : Relation.ReflTransGen (OuterStep g gs)
      [(outerEncode g gs) (OuterDecoratedSym.indexed g.initial [])] mid := by
    simpa [indexedSubst, outerEncode] using houter
  obtain ⟨d, rfl, hdouter⟩ := outer_unlift_derives g gs houter'
  have hall := decorated_all_terminal_of_inner_derives g gs d w hinner
  have hinner' := innerDerives_to_derives g gs hinner
  obtain ⟨xs, W, hd, hw, hW⟩ :=
    extract_substitution_blocks g gs d w hall hinner'
  refine ⟨xs, ?_, ?_⟩
  · change g.Generates xs
    unfold IndexedGrammar.Generates
    simpa [hd] using hdouter
  · exact (Language.mem_list_prod_iff_forall2
      (xs.map fun a => (gs a).Language) w).mpr
      ⟨W, hw, forall₂_languages_map hW⟩

private lemma outerErase_split_indexed (g : IndexedGrammar α)
    {d : List (OuterDecoratedSym g)} {n : g.nt} {σ : List g.flag}
    {p q : List g.ISym}
    (h : d.map (outerErase g) = p ++ [.indexed n σ] ++ q) :
    ∃ d₁ d₂,
      d = d₁ ++ [OuterDecoratedSym.indexed n σ] ++ d₂ ∧
      p = d₁.map (outerErase g) ∧ q = d₂.map (outerErase g) := by
  have h' : d.map (outerErase g) = p ++ IndexedGrammar.ISym.indexed n σ :: q := by
    simpa using h
  obtain ⟨d₁, rest, hd, hp, hrest⟩ := List.map_eq_append_iff.mp h'
  cases rest with
  | nil => simp at hrest
  | cons s d₂ =>
      simp only [List.map_cons, List.cons.injEq] at hrest
      obtain ⟨hs, hq⟩ := hrest
      cases s with
      | terminal a τ => simp [outerErase] at hs
      | indexed m τ =>
          simp [outerErase] at hs
          obtain ⟨rfl, rfl⟩ := hs
          exact ⟨d₁, d₂, by simpa [List.singleton_append] using hd, hp.symm, hq.symm⟩

private lemma outer_lift_step [Fintype α]
    (g : IndexedGrammar α) (gs : α → IndexedGrammar β)
    (d : List (OuterDecoratedSym g)) {x : List g.ISym}
    (h : g.Transforms (d.map (outerErase g)) x) :
    ∃ d' : List (OuterDecoratedSym g),
      x = d'.map (outerErase g) ∧
      OuterStep g gs (d.map (outerEncode g gs)) (d'.map (outerEncode g gs)) := by
  obtain ⟨r, p, q, σ, hr, hsource, htarget⟩ := h
  cases hc : r.consume with
  | none =>
      rw [hc] at hsource
      obtain ⟨d₁, d₂, hd, hp, hq⟩ := outerErase_split_indexed g hsource
      let d' := d₁ ++ r.rhs.map (decorateOuterRhs g σ) ++ d₂
      refine ⟨d', ?_, ⟨r, hr, d₁.map (outerEncode g gs),
        d₂.map (outerEncode g gs), σ.map SubstFlag.outer, ?_, ?_⟩⟩
      · rw [htarget, hp, hq]
        simp only [d', List.map_append]
        rw [outerErase_decorate_expand]
      · simp [ruleSourceSym, substLiftOuterRule, hc, hd, outerEncode, List.map_append]
      · simp only [d', List.map_append, substLiftOuterRule]
        rw [← outerEncode_decorate_expand]
  | some f =>
      rw [hc] at hsource
      obtain ⟨d₁, d₂, hd, hp, hq⟩ := outerErase_split_indexed g hsource
      let d' := d₁ ++ r.rhs.map (decorateOuterRhs g σ) ++ d₂
      refine ⟨d', ?_, ⟨r, hr, d₁.map (outerEncode g gs),
        d₂.map (outerEncode g gs), σ.map SubstFlag.outer, ?_, ?_⟩⟩
      · rw [htarget, hp, hq]
        simp only [d', List.map_append]
        rw [outerErase_decorate_expand]
      · simp [ruleSourceSym, substLiftOuterRule, hc, hd, outerEncode, List.map_append]
      · simp only [d', List.map_append, substLiftOuterRule]
        rw [← outerEncode_decorate_expand]

private lemma outer_lift_derives [Fintype α]
    (g : IndexedGrammar α) (gs : α → IndexedGrammar β)
    {x : List g.ISym} (h : g.Derives [.indexed g.initial []] x) :
    ∃ d : List (OuterDecoratedSym g),
      x = d.map (outerErase g) ∧
      Relation.ReflTransGen (OuterStep g gs)
        [(outerEncode g gs) (OuterDecoratedSym.indexed g.initial [])]
        (d.map (outerEncode g gs)) := by
  induction h with
  | refl => exact ⟨[.indexed g.initial []], rfl, Relation.ReflTransGen.refl⟩
  | tail _ hstep ih =>
      obtain ⟨d, rfl, hd⟩ := ih
      obtain ⟨d', hx, hstep'⟩ := outer_lift_step g gs d hstep
      exact ⟨d', hx, hd.tail hstep'⟩

private lemma decorated_terminal_form (g : IndexedGrammar α)
    {d : List (OuterDecoratedSym g)} {xs : List α}
    (h : xs.map (IndexedGrammar.ISym.terminal (g := g)) = d.map (outerErase g)) :
    List.Forall₂ (fun s a => ∃ σ, s = OuterDecoratedSym.terminal a σ) d xs := by
  induction xs generalizing d with
  | nil =>
      have hd : d = [] := by
        cases d <;> simp_all
      subst d
      exact List.Forall₂.nil
  | cons a xs ih =>
      cases d with
      | nil => simp at h
      | cons s d =>
          cases s with
          | indexed n σ => simp [outerErase] at h
          | terminal b σ =>
              simp [outerErase] at h
              obtain ⟨rfl, htail⟩ := h
              exact List.Forall₂.cons ⟨σ, rfl⟩ (ih htail)

private lemma forall₂_languages_unmap {gs : α → IndexedGrammar β}
    {W : List (List β)} {xs : List α}
    (h : List.Forall₂ (fun u L => u ∈ L) W
      (xs.map fun a => (gs a).Language)) :
    List.Forall₂ (fun u a => u ∈ (gs a).Language) W xs := by
  induction xs generalizing W with
  | nil =>
      cases W <;> simp_all
  | cons a xs ih =>
      cases W with
      | nil => simp at h
      | cons w W =>
          have h' : List.Forall₂ (fun u L => u ∈ L) (w :: W)
              ((gs a).Language :: (xs.map fun a => (gs a).Language)) := by
            simpa only [List.map_cons] using h
          rw [List.forall₂_cons] at h'
          exact List.Forall₂.cons h'.1 (ih h'.2)

private lemma outerDerives_to_derives [Fintype α]
    (g : IndexedGrammar α) (gs : α → IndexedGrammar β)
    {u v : List (indexedSubst g gs).ISym}
    (h : Relation.ReflTransGen (OuterStep g gs) u v) :
    (indexedSubst g gs).Derives u v :=
  Relation.ReflTransGen.mono
    (fun _ _ hs => (indexedSubst_step_iff g gs).mpr (Or.inl hs)) h

private lemma inner_generate_blocks [Fintype α]
    (g : IndexedGrammar α) (gs : α → IndexedGrammar β)
    {d : List (OuterDecoratedSym g)} {xs : List α} {W : List (List β)}
    (hdecor : List.Forall₂
      (fun s a => ∃ σ, s = OuterDecoratedSym.terminal a σ) d xs)
    (hW : List.Forall₂ (fun u a => u ∈ (gs a).Language) W xs) :
    (indexedSubst g gs).Derives
      (d.map (outerEncode g gs))
      (W.flatten.map (IndexedGrammar.ISym.terminal (g := indexedSubst g gs))) := by
  induction hdecor generalizing W with
  | nil =>
      cases W with
      | nil => exact Relation.ReflTransGen.refl
      | cons w W => simp at hW
  | @cons s a d xs hs _ ih =>
      cases W with
      | nil => simp at hW
      | cons w W =>
          rw [List.forall₂_cons] at hW
          obtain ⟨suffix, rfl⟩ := hs
          have hw : (gs a).Generates w := hW.1
          unfold IndexedGrammar.Generates at hw
          have hheadInner := inner_lift_derives g gs a suffix hw
          have hhead : (indexedSubst g gs).Derives
              [(outerEncode g gs) (OuterDecoratedSym.terminal a suffix)]
              (w.map (IndexedGrammar.ISym.terminal (g := indexedSubst g gs))) := by
            have := innerDerives_to_derives g gs hheadInner
            simpa [outerEncode, innerEncode] using this
          have htail := ih hW.2
          have hleft := IndexedGrammar.deri_with_suffix
            (d.map (outerEncode g gs)) hhead
          have hright := IndexedGrammar.deri_with_prefix
            (w.map (IndexedGrammar.ISym.terminal (g := indexedSubst g gs))) htail
          exact hleft.trans (by
            simpa [List.map_append, List.append_assoc] using hright)

private theorem indexedSubst_language_superset [Fintype α]
    (g : IndexedGrammar α) (gs : α → IndexedGrammar β) :
    Set.Subset (g.Language.subst fun a => (gs a).Language)
      (indexedSubst g gs).Language := by
  intro w hw
  obtain ⟨xs, hxs, hprod⟩ := hw
  obtain ⟨W, hw, hWlanguages⟩ :=
    (Language.mem_list_prod_iff_forall2
      (xs.map fun a => (gs a).Language) w).mp hprod
  have hW : List.Forall₂ (fun u a => u ∈ (gs a).Language) W xs :=
    forall₂_languages_unmap hWlanguages
  change g.Generates xs at hxs
  unfold IndexedGrammar.Generates at hxs
  obtain ⟨d, hd, houter⟩ := outer_lift_derives g gs hxs
  have hdecor : List.Forall₂
      (fun s a => ∃ σ, s = OuterDecoratedSym.terminal a σ) d xs :=
    decorated_terminal_form g hd
  have hinner := inner_generate_blocks g gs hdecor hW
  have houter' := outerDerives_to_derives g gs houter
  change (indexedSubst g gs).Generates w
  unfold IndexedGrammar.Generates
  have hfull := houter'.trans hinner
  simpa [indexedSubst, hw] using hfull

private theorem indexedSubst_language [Fintype α]
    (g : IndexedGrammar α) (gs : α → IndexedGrammar β) :
    (indexedSubst g gs).Language =
      g.Language.subst (fun a => (gs a).Language) := by
  apply Set.Subset.antisymm
  · exact indexedSubst_language_subset g gs
  · exact indexedSubst_language_superset g gs

/-- Indexed languages are closed under substitution. -/
public theorem Indexed_closedUnderSubstitution :
    ClosedUnderSubstitution is_Indexed := by
  intro α β _ _ L f hL hf
  classical
  obtain ⟨g, hg⟩ := hL
  let gs : α → IndexedGrammar β := fun a => Classical.choose (hf a)
  have hgs (a : α) : (gs a).Language = f a := Classical.choose_spec (hf a)
  refine ⟨indexedSubst g gs, ?_⟩
  rw [indexedSubst_language, hg]
  congr 1
  funext a
  exact hgs a

end
