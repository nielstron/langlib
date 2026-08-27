module

/-
Copyright (c) 2026 Niels Mündler. All rights reserved.
Released under Apache 2.0 license; see licenses/Apache-2.0.txt.
-/
public import Langlib.Classes.Linear.Definition
public import Langlib.Classes.RecursivelyEnumerable.Closure.Union
public import Langlib.Utilities.ClosurePredicates
@[expose]
public section

/-! # Linear languages are closed under union

The ordinary union grammar adds a fresh start symbol whose two rules select one
of the input grammars. Those rules, and the lifted rules from both grammars,
remain linear.
-/

variable {T : Type}

private theorem linear_output_lift {N₁ N₂ : Type} (f : N₁ → N₂)
    {s : List (symbol T N₁)} (hs : linear_output s) :
    linear_output (lift_string_ f s) := by
  rcases hs with hs | ⟨u, B, v, rfl⟩
  · left
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    obtain ⟨t, rfl⟩ := hs y hy
    exact ⟨t, rfl⟩
  · right
    refine ⟨u, f B, v, ?_⟩
    simp only [lift_string_, List.map_append, List.map_cons, List.map_nil,
      List.map_map, lift_symbol_]
    rw [show (lift_symbol_ f ∘ (symbol.terminal : T → symbol T N₁)) =
      (symbol.terminal : T → symbol T N₂) by funext t; rfl]

/-- The standard union grammar preserves linearity. -/
public theorem union_grammar_linear {g₁ g₂ : grammar T}
    (h₁ : grammar_linear g₁) (h₂ : grammar_linear g₂) :
    grammar_linear (union_grammar g₁ g₂) := by
  intro r hr
  change r ∈
    (⟨[], none, [], [symbol.nonterminal (some (Sum.inl g₁.initial))]⟩ ::
      ⟨[], none, [], [symbol.nonterminal (some (Sum.inr g₂.initial))]⟩ ::
      List.map (lift_rule_ (some ∘ Sum.inl)) g₁.rules ++
        List.map (lift_rule_ (some ∘ Sum.inr)) g₂.rules) at hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact ⟨rfl, rfl, Or.inr ⟨[], _, [], rfl⟩⟩
  rcases List.mem_cons.mp hr with rfl | hr
  · exact ⟨rfl, rfl, Or.inr ⟨[], _, [], rfl⟩⟩
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨r₁, hr₁, rfl⟩ := List.mem_map.mp hr
    obtain ⟨hL, hR, hout⟩ := h₁ r₁ hr₁
    exact ⟨by change lift_string_ _ r₁.input_L = []; rw [hL]; rfl,
      by change lift_string_ _ r₁.input_R = []; rw [hR]; rfl,
      linear_output_lift _ hout⟩
  · obtain ⟨r₂, hr₂, rfl⟩ := List.mem_map.mp hr
    obtain ⟨hL, hR, hout⟩ := h₂ r₂ hr₂
    exact ⟨by change lift_string_ _ r₂.input_L = []; rw [hL]; rfl,
      by change lift_string_ _ r₂.input_R = []; rw [hR]; rfl,
      linear_output_lift _ hout⟩

/-- The standard union grammar generates exactly the union of its component
languages. -/
public theorem grammar_language_union_grammar (g₁ g₂ : grammar T) :
    grammar_language (union_grammar g₁ g₂) =
      grammar_language g₁ + grammar_language g₂ := by
  ext w
  constructor
  · exact in_L₁_or_L₂_of_in_union
  · intro hw
    rcases hw with hw | hw
    · exact in_union_of_in_L₁ hw
    · exact in_union_of_in_L₂ hw

/-- Linear languages are closed under union. -/
public theorem Linear_closedUnderUnion : ClosedUnderUnion (@is_Linear T) := by
  rintro L₁ L₂ ⟨g₁, hg₁, rfl⟩ ⟨g₂, hg₂, rfl⟩
  exact ⟨union_grammar g₁ g₂, union_grammar_linear hg₁ hg₂,
    grammar_language_union_grammar g₁ g₂⟩

end
