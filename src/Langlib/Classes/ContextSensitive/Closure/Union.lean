import Langlib.Classes.ContextSensitive.Definition
import Langlib.Classes.RecursivelyEnumerable.Closure.Union

/-! # Context-Sensitive Closure Under Union

This file proves that the class of context-sensitive languages is closed under union.

The proof reuses the union grammar construction from the RE closure proof and additionally
shows that the construction preserves the context-sensitive (non-contracting) property.

## Main results

- `union_grammar_context_sensitive` — the union grammar is context-sensitive when both
  inputs are context-sensitive.
- `CS_of_CS_u_CS` — the class of context-sensitive languages is closed under union.
-/

variable {T : Type}

/-
The union grammar preserves the context-sensitive (non-contracting) property.
-/
lemma union_grammar_context_sensitive {g₁ g₂ : grammar T}
    (h₁ : grammar_context_sensitive g₁) (h₂ : grammar_context_sensitive g₂) :
    grammar_context_sensitive (union_grammar g₁ g₂) := by
  intro r hr;
  unfold union_grammar at hr; simp_all +decide [ List.mem_cons ] ;
  rcases hr with ( rfl | rfl | ⟨ a, ha, rfl ⟩ | ⟨ a, ha, rfl ⟩ ) <;> simp_all +decide [ lift_rule_ ];
  · obtain ⟨ γ, hγ₁, hγ₂ ⟩ := h₁ a ha;
    unfold lift_string_ at *; aesop;
  · obtain ⟨ γ, hγ₁, hγ₂ ⟩ := h₂ a ha;
    simp_all +decide [ lift_string_ ]

/-- The class of context-sensitive languages is closed under union. -/
theorem CS_of_CS_u_CS (L₁ : Language T) (L₂ : Language T) :
    is_CS L₁ ∧ is_CS L₂ → is_CS (L₁ + L₂) := by
  rintro ⟨⟨g₁, hcs₁, hL₁⟩, ⟨g₂, hcs₂, hL₂⟩⟩
  refine ⟨union_grammar g₁ g₂, union_grammar_context_sensitive hcs₁ hcs₂, ?_⟩
  ext w
  constructor
  · intro hw
    rw [Language.mem_add, ← hL₁, ← hL₂]
    exact in_L₁_or_L₂_of_in_union hw
  · intro hw
    cases hw with
    | inl h₁ => exact in_union_of_in_L₁ (hL₁ ▸ h₁)
    | inr h₂ => exact in_union_of_in_L₂ (hL₂ ▸ h₂)