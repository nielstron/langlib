import Mathlib
import Langlib.Grammars.ContextSensitive.Definition
import Langlib.Grammars.Unrestricted.Definition

/-! # Context-Sensitive Languages

This file defines the class of context-sensitive languages via unrestricted grammars
satisfying the context-sensitive rule-shape property.
-/

variable {T : Type}

/-- An unrestricted grammar is context-sensitive if every rule preserves its
surrounding context and rewrites the distinguished nonterminal to a non-empty string. -/
def grammar_context_sensitive (g : grammar T) : Prop :=
  ∀ r ∈ g.rules, ∃ γ : List (symbol T g.nt), γ ≠ [] ∧
    r.output_string = r.input_L ++ γ ++ r.input_R

/-- Predicate that a language is context-sensitive. -/
def is_CS (L : Language T) : Prop :=
  ∃ g : grammar T, grammar_context_sensitive g ∧ grammar_language g = L

/-- Legacy characterization of context-sensitive languages via `CS_grammar`. -/
def is_CS_via_csg (L : Language T) : Prop :=
  ∃ g : CS_grammar T, CS_language g = L

/-- The class of context-sensitive languages. -/
def CS : Set (Language T) :=
  setOf is_CS

/-- Remove the empty word from a language. -/
def withoutEpsilon (L : Language T) : Language T :=
  fun w => w ∈ L ∧ w ≠ []

@[simp] theorem mem_withoutEpsilon {L : Language T} {w : List T} :
    w ∈ withoutEpsilon L ↔ w ∈ L ∧ w ≠ [] :=
  Iff.rfl

/--
The epsilon-aware context-sensitive language predicate.  This matches the common
CSL convention that `[]` is allowed as an exceptional word: only the nonempty
part of the language must satisfy the strictly noncontracting `is_CS` predicate.
-/
def is_CSL (L : Language T) : Prop :=
  is_CS (withoutEpsilon L)

/-- The epsilon-aware class of context-sensitive languages. -/
def CSL : Set (Language T) :=
  setOf is_CSL

lemma grammar_context_sensitive_transforms_length_le (g : grammar T)
    (hg : grammar_context_sensitive g)
    {w₁ w₂ : List (symbol T g.nt)}
    (h : grammar_transforms g w₁ w₂) : w₁.length ≤ w₂.length := by
  rcases h with ⟨r, hr, u, v, hw₁, hw₂⟩
  rcases hg r hr with ⟨γ, hγ, hout⟩
  subst w₁
  subst w₂
  rw [hout]
  simp [List.length_append]
  have hγlen : 1 ≤ γ.length := Nat.succ_le_of_lt (List.length_pos_of_ne_nil hγ)
  omega

lemma grammar_context_sensitive_derives_length_le (g : grammar T)
    (hg : grammar_context_sensitive g)
    {w₁ w₂ : List (symbol T g.nt)}
    (h : grammar_derives g w₁ w₂) : w₁.length ≤ w₂.length := by
  induction h with
  | refl => exact le_rfl
  | tail _ hstep ih =>
      exact le_trans ih (grammar_context_sensitive_transforms_length_le g hg hstep)

theorem nil_not_mem_of_is_CS {L : Language T} (h : is_CS L) : [] ∉ L := by
  intro hnil
  rcases h with ⟨g, hg, hL⟩
  have hgen : grammar_language g [] := by
    simpa [hL] using hnil
  have hder : grammar_derives g [symbol.nonterminal g.initial]
      (([] : List T).map symbol.terminal) := by
    simpa [grammar_language, grammar_generates] using hgen
  have hlen := grammar_context_sensitive_derives_length_le g hg hder
  simp at hlen

theorem is_CSL_of_is_CS {L : Language T} (h : is_CS L) : is_CSL L := by
  unfold is_CSL
  have hwithout : withoutEpsilon L = L := by
    ext w
    constructor
    · intro hw
      exact hw.1
    · intro hw
      exact ⟨hw, fun hnil => by
        subst w
        exact nil_not_mem_of_is_CS h hw⟩
  rwa [hwithout]

theorem CS_subclass_CSL : (CS : Set (Language T)) ⊆ CSL := by
  intro L hL
  exact is_CSL_of_is_CS hL
