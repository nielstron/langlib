module

public import Langlib.Classes.Indexed.Definition
public import Langlib.Utilities.ClosurePredicates

/-! # Indexed Languages Are Closed Under Reverse

This file reverses every right-hand side of an indexed grammar rule and proves that the
resulting grammar generates the reversal of the original language.

Proof idea: map every derivation step to a derivation step in the grammar with
reversed right-hand sides, while reversing the surrounding sentential form. This
turns terminal yield `w` into `w.reverse`; the converse follows by applying the
same construction again because reversing the grammar twice gives the original.
-/

variable {T : Type}

private def reverseIRule {N F : Type} (r : IRule T N F) : IRule T N F :=
  { lhs := r.lhs, consume := r.consume, rhs := r.rhs.reverse }

private def reverseIndexedGrammar (g : IndexedGrammar T) : IndexedGrammar T where
  nt := g.nt
  flag := g.flag
  initial := g.initial
  rules := g.rules.map reverseIRule

private def reverseISym (g : IndexedGrammar T) :
    g.ISym → (reverseIndexedGrammar g).ISym
  | .terminal t => .terminal t
  | .indexed n σ => .indexed n σ

private lemma reverseIndexedGrammar_reverse (g : IndexedGrammar T) :
    reverseIndexedGrammar (reverseIndexedGrammar g) = g := by
  cases g
  simp [reverseIndexedGrammar, reverseIRule, List.map_map, Function.comp_def]

private lemma reverseISym_initial (g : IndexedGrammar T) :
    [IndexedGrammar.ISym.indexed g.initial []].reverse.map (reverseISym g) =
      [IndexedGrammar.ISym.indexed (reverseIndexedGrammar g).initial []] := by
  rfl

private lemma reverseISym_terminals (g : IndexedGrammar T) (w : List T) :
    (w.map IndexedGrammar.ISym.terminal).reverse.map (reverseISym g) =
      w.reverse.map IndexedGrammar.ISym.terminal := by
  induction w <;> simp [reverseISym, *]

private lemma reverse_expandRhs (g : IndexedGrammar T)
    (rhs : List (IRhsSymbol T g.nt g.flag)) (σ : List g.flag) :
    (reverseIndexedGrammar g).expandRhs rhs.reverse σ =
      (g.expandRhs rhs σ).reverse.map (reverseISym g) := by
  simp [IndexedGrammar.expandRhs, reverseISym, List.map_reverse, List.map_map,
    Function.comp_def]
  intro s _hs
  cases s with
  | terminal t => rfl
  | nonterminal n push => cases push <;> rfl

private lemma reverse_transforms (g : IndexedGrammar T)
    {w₁ w₂ : List g.ISym} (h : g.Transforms w₁ w₂) :
    (reverseIndexedGrammar g).Transforms
      (w₁.reverse.map (reverseISym g)) (w₂.reverse.map (reverseISym g)) := by
  obtain ⟨r, u, v, σ, hr, hw₁, hw₂⟩ := h
  refine ⟨reverseIRule r, v.reverse.map (reverseISym g), u.reverse.map (reverseISym g),
    σ, ?_, ?_, ?_⟩
  · exact List.mem_map.mpr ⟨r, hr, rfl⟩
  · cases hc : r.consume with
    | none =>
        rw [hc] at hw₁
        rw [hw₁]
        simp [reverseIRule, reverseISym, hc, List.reverse_append, List.map_append]
    | some f =>
        rw [hc] at hw₁
        rw [hw₁]
        simp [reverseIRule, reverseISym, hc, List.reverse_append, List.map_append]
  · simp [reverseIRule, hw₂, List.reverse_append, List.map_append, reverse_expandRhs]

private lemma reverse_derives (g : IndexedGrammar T)
    {w₁ w₂ : List g.ISym} (h : g.Derives w₁ w₂) :
    (reverseIndexedGrammar g).Derives
      (w₁.reverse.map (reverseISym g)) (w₂.reverse.map (reverseISym g)) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ ht ih => exact ih.tail (reverse_transforms g ht)

private theorem reverseIndexedGrammar_generates (g : IndexedGrammar T) (w : List T) :
    w ∈ g.Language → w.reverse ∈ (reverseIndexedGrammar g).Language := by
  intro hw
  exact by
    change (reverseIndexedGrammar g).Generates w.reverse
    change g.Generates w at hw
    unfold IndexedGrammar.Generates at hw ⊢
    simpa [reverseISym_initial, reverseISym_terminals] using reverse_derives g hw

private theorem reverseIndexedGrammar_language (g : IndexedGrammar T) :
    (reverseIndexedGrammar g).Language = g.Language.reverse := by
  ext w
  constructor
  · intro hw
    have hrev := reverseIndexedGrammar_generates (reverseIndexedGrammar g) w hw
    rw [reverseIndexedGrammar_reverse] at hrev
    change w.reverse ∈ g.Language at hrev
    simpa using hrev
  · intro hw
    change w.reverse ∈ g.Language at hw
    simpa using reverseIndexedGrammar_generates g w.reverse hw

/-- Indexed languages are closed under reverse. -/
public theorem Indexed_closedUnderReverse : ClosedUnderReverse (α := T) is_Indexed :=
  fun L hL => by
    obtain ⟨g, hg⟩ := hL
    exact ⟨reverseIndexedGrammar g, by rw [reverseIndexedGrammar_language, hg]⟩
