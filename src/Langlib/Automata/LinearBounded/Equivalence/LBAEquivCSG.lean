import Mathlib
import Langlib.Automata.NondeterministicLinearBounded.Definition
import Langlib.Classes.ContextSensitive.Definition
import Langlib.Grammars.ContextSensitive.Toolbox

/-!
Initial lemmas for LBA -> CSG constructions
-/

open Relation List

variable {T : Type}

/-- A single CS derivation step never decreases word length. -/
theorem CS_transforms_length_le {g : CS_grammar T}
    {w₁ w₂ : List (symbol T g.nt)}
    (h : CS_transforms g w₁ w₂) :
    w₁.length ≤ w₂.length := by
  obtain ⟨r, u, v, hr, hw₁, hw₂⟩ := h
  have hne := g.output_nonempty r hr
  subst hw₁
  subst hw₂
  simp only [List.length_append, List.length_cons, List.length_nil]
  have : r.output_string.length ≥ 1 := List.length_pos_of_ne_nil hne
  omega

/-- CS derivations are non-contracting: multi-step version. -/
theorem CS_derives_length_le {g : CS_grammar T}
    {w₁ w₂ : List (symbol T g.nt)}
    (h : CS_derives g w₁ w₂) :
    w₁.length ≤ w₂.length := by
  induction h with
  | refl => exact le_refl _
  | tail _ step ih => exact le_trans ih (CS_transforms_length_le step)

/-- The empty word is never in a CS language. -/
theorem empty_not_in_CS_language (g : CS_grammar T) :
    [] ∉ CS_language g := by
  intro h
  have hlen := CS_derives_length_le h
  simp at hlen

/-- If `L` is context-sensitive, then `[] ∉ L`. -/
theorem is_CS_no_empty {L : Language T} (hL : is_CS L) :
    [] ∉ L := by
  obtain ⟨g, rfl⟩ := hL
  exact empty_not_in_CS_language g

/-- The empty word is never accepted by an NLBA. -/
theorem empty_not_in_NLBA_language {Γ Λ : Type*}
    (M : NLBA.Machine Γ Λ) (embed : T → Γ) :
    [] ∉ NLBA.LanguageViaEmbed M embed := by
  intro ⟨hw, _⟩
  exact hw (by simp)

/-- If `L` is NLBA-recognizable, then `[] ∉ L`. -/
theorem is_NLBA_no_empty {L : Language T} (hL : is_NLBA L) :
    [] ∉ L := by
  obtain ⟨Γ, Λ, _, _, _, _, embed, M, rfl⟩ := hL
  exact empty_not_in_NLBA_language M embed
