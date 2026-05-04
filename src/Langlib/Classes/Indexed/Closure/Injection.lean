import Langlib.Classes.Indexed.Definition
import Langlib.Utilities.LanguageOperations

/-! # Indexed Languages Under Injective Terminal Maps

This file proves that indexed languages are preserved by injective terminal maps.
-/

variable {T₁ T₂ : Type}

namespace IndexedGrammar

def mapIRhsSymbol (f : T₁ → T₂) {N F : Type} : IRhsSymbol T₁ N F → IRhsSymbol T₂ N F
  | .terminal t => .terminal (f t)
  | .nonterminal n push => .nonterminal n push

def mapTerminals (f : T₁ → T₂) (g : IndexedGrammar T₁) : IndexedGrammar T₂ where
  nt := g.nt
  flag := g.flag
  initial := g.initial
  rules := g.rules.map fun r =>
    { lhs := r.lhs
      consume := r.consume
      rhs := r.rhs.map (mapIRhsSymbol f) }

def mapISym (f : T₁ → T₂) (g : IndexedGrammar T₁) :
    g.ISym → (g.mapTerminals f).ISym
  | .terminal t => .terminal (f t)
  | .indexed n σ => .indexed n σ

private noncomputable def invOfInjective [Nonempty T₁] (f : T₁ → T₂) (y : T₂) : T₁ := by
  classical
  exact if h : ∃ x, f x = y then Classical.choose h else Classical.ofNonempty

private lemma invOfInjective_apply [Nonempty T₁] {f : T₁ → T₂}
    (hf : Function.Injective f) (x : T₁) :
    invOfInjective f (f x) = x := by
  classical
  let h : ∃ y, f y = f x := ⟨x, rfl⟩
  rw [invOfInjective]
  simp only [dif_pos h]
  exact hf (Classical.choose_spec h)

private noncomputable def invISym [Nonempty T₁] (f : T₁ → T₂) (g : IndexedGrammar T₁) :
    (g.mapTerminals f).ISym → g.ISym
  | .terminal t => .terminal (invOfInjective f t)
  | .indexed n σ => .indexed n σ

private lemma invISym_mapISym [Nonempty T₁] {f : T₁ → T₂} (hf : Function.Injective f)
    (g : IndexedGrammar T₁) (s : g.ISym) :
    invISym f g (mapISym f g s) = s := by
  cases s with
  | terminal t => simp [mapISym, invISym, invOfInjective_apply hf]
  | indexed n σ => rfl

private lemma expandRhs_mapTerminals (f : T₁ → T₂) (g : IndexedGrammar T₁)
    (rhs : List (IRhsSymbol T₁ g.nt g.flag)) (σ : List g.flag) :
    (g.mapTerminals f).expandRhs (rhs.map (mapIRhsSymbol f)) σ =
      (g.expandRhs rhs σ).map (mapISym f g) := by
  simp [mapTerminals, expandRhs, mapISym, mapIRhsSymbol]
  intro s _
  cases s with
  | terminal t => rfl
  | nonterminal n push =>
      cases push <;> rfl

private lemma inv_expandRhs_mapTerminals [Nonempty T₁] {f : T₁ → T₂}
    (hf : Function.Injective f) (g : IndexedGrammar T₁)
    (rhs : List (IRhsSymbol T₁ g.nt g.flag)) (σ : List g.flag) :
    ((g.mapTerminals f).expandRhs (rhs.map (mapIRhsSymbol f)) σ).map (invISym f g) =
      g.expandRhs rhs σ := by
  rw [expandRhs_mapTerminals]
  rw [List.map_map]
  let xs := g.expandRhs rhs σ
  change List.map (invISym f g ∘ mapISym f g) xs = xs
  induction xs with
  | nil => rfl
  | cons s rest ih =>
      simp [invISym_mapISym hf g s, ih]

private lemma transforms_mapTerminals (f : T₁ → T₂) (g : IndexedGrammar T₁)
    {w₁ w₂ : List g.ISym} (h : g.Transforms w₁ w₂) :
    (g.mapTerminals f).Transforms (w₁.map (mapISym f g)) (w₂.map (mapISym f g)) := by
  obtain ⟨r, u, v, σ, hr, hw₁, hw₂⟩ := h
  refine ⟨⟨r.lhs, r.consume, r.rhs.map (mapIRhsSymbol f)⟩,
    u.map (mapISym f g), v.map (mapISym f g), σ, ?_, ?_, ?_⟩
  · simp [mapTerminals]
    exact ⟨r, hr, rfl, rfl, rfl⟩
  · cases hc : r.consume with
    | none =>
        simp [hc] at hw₁
        rw [hw₁]
        simp [mapISym, List.map_append]
    | some flag =>
        simp [hc] at hw₁
        rw [hw₁]
        simp [mapISym, List.map_append]
  · rw [hw₂, List.map_append, List.map_append, expandRhs_mapTerminals]

private lemma derives_mapTerminals (f : T₁ → T₂) (g : IndexedGrammar T₁)
    {w₁ w₂ : List g.ISym} (h : g.Derives w₁ w₂) :
    (g.mapTerminals f).Derives (w₁.map (mapISym f g)) (w₂.map (mapISym f g)) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ ht ih => exact ih.tail (transforms_mapTerminals f g ht)

private lemma transforms_inv_mapTerminals [Nonempty T₁] {f : T₁ → T₂}
    (hf : Function.Injective f) (g : IndexedGrammar T₁)
    {w₁ w₂ : List (g.mapTerminals f).ISym} (h : (g.mapTerminals f).Transforms w₁ w₂) :
    g.Transforms (w₁.map (invISym f g)) (w₂.map (invISym f g)) := by
  obtain ⟨r, u, v, σ, hr, hw₁, hw₂⟩ := h
  obtain ⟨r₀, hr₀, hEq⟩ : ∃ r₀ ∈ g.rules,
      { lhs := r₀.lhs, consume := r₀.consume, rhs := r₀.rhs.map (mapIRhsSymbol f) } = r := by
    simpa [mapTerminals] using hr
  subst r
  refine ⟨r₀, u.map (invISym f g), v.map (invISym f g), σ, hr₀, ?_, ?_⟩
  · cases hc : r₀.consume with
    | none =>
        simp [hc] at hw₁
        rw [hw₁]
        simp [invISym, List.map_append]
    | some flag =>
        simp [hc] at hw₁
        rw [hw₁]
        simp [invISym, List.map_append]
  · rw [hw₂, List.map_append, List.map_append, inv_expandRhs_mapTerminals hf]

private lemma terminal_mem_expandRhs_mapTerminals (f : T₁ → T₂) (g : IndexedGrammar T₁)
    (rhs : List (IRhsSymbol T₁ g.nt g.flag)) (σ : List g.flag) {t : T₂}
    (h : (IndexedGrammar.ISym.terminal t : (g.mapTerminals f).ISym) ∈
      (g.mapTerminals f).expandRhs (rhs.map (mapIRhsSymbol f)) σ) :
    ∃ x, f x = t := by
  rw [expandRhs_mapTerminals] at h
  simp only [List.mem_map] at h
  obtain ⟨s, _hs, hs⟩ := h
  cases s with
  | terminal x => exact ⟨x, by simpa [mapISym] using hs⟩
  | indexed n stack => cases hs

private lemma terminal_mem_range_of_derives_mapTerminals [Nonempty T₁] (f : T₁ → T₂)
    (g : IndexedGrammar T₁) {w : List (g.mapTerminals f).ISym}
    (h : (g.mapTerminals f).Derives [.indexed g.initial []] w) :
    ∀ t, (IndexedGrammar.ISym.terminal t : (g.mapTerminals f).ISym) ∈ w →
      ∃ x, f x = t := by
  induction h with
  | refl =>
      intro t ht
      simp at ht
  | tail hd ht ih =>
      intro t htmem
      obtain ⟨r, u, v, σ, hr, hw₁, hw₂⟩ := ht
      rw [hw₂] at htmem
      simp only [List.mem_append] at htmem
      rcases htmem with hleftOrMid | hright
      · rcases hleftOrMid with hleft | hmid
        · exact ih t (by
            cases hc : r.consume with
            | none =>
                simp [hc] at hw₁
                rw [hw₁]
                simp [hleft]
            | some flag =>
                simp [hc] at hw₁
                rw [hw₁]
                simp [hleft])
        · obtain ⟨r₀, _hr₀, hEq⟩ : ∃ r₀ ∈ g.rules,
              { lhs := r₀.lhs, consume := r₀.consume, rhs := r₀.rhs.map (mapIRhsSymbol f) } = r := by
            simpa [mapTerminals] using hr
          subst r
          exact terminal_mem_expandRhs_mapTerminals f g r₀.rhs σ hmid
      · exact ih t (by
          cases hc : r.consume with
          | none =>
              simp [hc] at hw₁
              rw [hw₁]
              simp [hright]
          | some flag =>
              simp [hc] at hw₁
              rw [hw₁]
              simp [hright])

private lemma map_invOfInjective_of_derives [Nonempty T₁] (f : T₁ → T₂)
    (g : IndexedGrammar T₁) {w : List T₂}
    (h : (g.mapTerminals f).Derives [.indexed g.initial []] (w.map .terminal)) :
    (w.map (invOfInjective f)).map f = w := by
  apply List.ext_getElem
  · simp
  · intro n hn₁ hn₂
    have hmem : (IndexedGrammar.ISym.terminal w[n] : (g.mapTerminals f).ISym) ∈
        w.map IndexedGrammar.ISym.terminal :=
      List.mem_map_of_mem
        (f := fun x => (IndexedGrammar.ISym.terminal x : (g.mapTerminals f).ISym))
        (show w[n] ∈ w from List.getElem_mem _)
    obtain ⟨x, hx⟩ := terminal_mem_range_of_derives_mapTerminals f g h w[n] hmem
    let hx' : ∃ y, f y = w[n] := ⟨x, hx⟩
    simp [invOfInjective, hx', Classical.choose_spec hx']

private lemma derives_inv_mapTerminals [Nonempty T₁] {f : T₁ → T₂}
    (hf : Function.Injective f) (g : IndexedGrammar T₁)
    {w₁ w₂ : List (g.mapTerminals f).ISym} (h : (g.mapTerminals f).Derives w₁ w₂) :
    g.Derives (w₁.map (invISym f g)) (w₂.map (invISym f g)) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ ht ih => exact ih.tail (transforms_inv_mapTerminals hf g ht)

theorem language_mapTerminals [Nonempty T₁] {f : T₁ → T₂} (hf : Function.Injective f)
    (g : IndexedGrammar T₁) :
    (g.mapTerminals f).Language = Language.map f g.Language := by
  ext w
  constructor
  · intro h
    refine ⟨w.map (invOfInjective f), ?_, ?_⟩
    · simpa [Language, Generates, invISym, List.map_map] using derives_inv_mapTerminals hf g h
    · exact map_invOfInjective_of_derives f g h
  · rintro ⟨u, hu, rfl⟩
    change (g.mapTerminals f).Derives [IndexedGrammar.ISym.indexed g.initial []]
      ((u.map f).map IndexedGrammar.ISym.terminal)
    convert derives_mapTerminals f g hu using 1
    simp [mapISym, List.map_map]

end IndexedGrammar

theorem Indexed_of_map_injective_Indexed [Nonempty T₁] {f : T₁ → T₂}
    (hf : Function.Injective f) (L : Language T₁) :
    is_Indexed L → is_Indexed (Language.map f L) := by
  intro hL
  obtain ⟨g, hg⟩ := hL
  exact ⟨g.mapTerminals f, by rw [IndexedGrammar.language_mapTerminals hf, hg]⟩
