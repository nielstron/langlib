import Mathlib
import Langlib.Grammars.Unrestricted.Definition
import Langlib.Grammars.Unrestricted.Toolbox

/-! # Grammar Projection

Given a grammar `g` over terminal alphabet `T ⊕ Γ`, we construct a grammar
`GrammarProjection.projectGrammar g` over terminal alphabet `T` such that:

  `w ∈ grammar_language (projectGrammar g) ↔ w.map Sum.inl ∈ grammar_language g`

This is used to convert a TM over `Option (T ⊕ Γ)` (with auxiliary tape symbols)
to a grammar over `T` (with only the original terminal alphabet).
-/

namespace GrammarProjection

variable {T Γ NT : Type}

/-- Map symbols from `Symbol (T ⊕ Γ) NT` to `Symbol T (NT ⊕ Γ)`. -/
def projSym : symbol (T ⊕ Γ) NT → symbol T (NT ⊕ Γ)
  | .terminal (Sum.inl t) => .terminal t
  | .terminal (Sum.inr γ) => .nonterminal (Sum.inr γ)
  | .nonterminal n => .nonterminal (Sum.inl n)

/-- Inverse map: `Symbol T (NT ⊕ Γ) → Symbol (T ⊕ Γ) NT`. -/
def liftSym : symbol T (NT ⊕ Γ) → symbol (T ⊕ Γ) NT
  | .terminal t => .terminal (Sum.inl t)
  | .nonterminal (Sum.inl n) => .nonterminal n
  | .nonterminal (Sum.inr γ) => .terminal (Sum.inr γ)

theorem projSym_liftSym (s : symbol T (NT ⊕ Γ)) :
    projSym (liftSym s) = s := by
  cases s with
  | terminal t => simp [liftSym, projSym]
  | nonterminal n => cases n <;> simp [liftSym, projSym]

theorem liftSym_projSym (s : symbol (T ⊕ Γ) NT) :
    liftSym (projSym s) = s := by
  cases s with
  | terminal t => cases t <;> simp [liftSym, projSym]
  | nonterminal n => simp [liftSym, projSym]

theorem projSym_injective :
    Function.Injective (projSym (T := T) (Γ := Γ) (NT := NT)) :=
  Function.LeftInverse.injective liftSym_projSym

theorem map_projSym_map_liftSym (l : List (symbol T (NT ⊕ Γ))) :
    (l.map liftSym).map projSym = l := by
  rw [List.map_map]; conv_rhs => rw [← List.map_id l]
  congr 1; ext s; exact projSym_liftSym s

theorem map_liftSym_map_projSym (l : List (symbol (T ⊕ Γ) NT)) :
    (l.map projSym).map liftSym = l := by
  rw [List.map_map]; conv_rhs => rw [← List.map_id l]
  congr 1; ext s; exact liftSym_projSym s

/-- Project a grammar rule from `T ⊕ Γ` terminals to `T` terminals. -/
def projRule (r : grule (T ⊕ Γ) NT) : grule T (NT ⊕ Γ) where
  input_L := r.input_L.map projSym
  input_N := Sum.inl r.input_N
  input_R := r.input_R.map projSym
  output_string := r.output_string.map projSym

/-- Project a grammar from `T ⊕ Γ` terminals to `T` terminals. -/
def projectGrammar (g : grammar (T ⊕ Γ)) : grammar T where
  nt := g.nt ⊕ Γ
  initial := Sum.inl g.initial
  rules := g.rules.map projRule

/-! ### Derivation correspondence -/

/-
A single grammar transformation step in `g` corresponds to a step in `projectGrammar g`.
-/
theorem projectGrammar_transforms_of_transforms (g : grammar (T ⊕ Γ))
    (sf₁ sf₂ : List (symbol (T ⊕ Γ) g.nt))
    (h : grammar_transforms g sf₁ sf₂) :
    grammar_transforms (projectGrammar g)
      (sf₁.map projSym) (sf₂.map projSym) := by
        obtain ⟨r, hr_mem, u, v, hf₁, hf₂⟩ := h;
        use projRule r;
        unfold projectGrammar; aesop;

/-
A single grammar transformation step in `projectGrammar g` on projected forms
corresponds to a step in `g`.
-/
theorem transforms_of_projectGrammar_transforms (g : grammar (T ⊕ Γ))
    (sf₁ sf₂ : List (symbol (T ⊕ Γ) g.nt))
    (h : grammar_transforms (projectGrammar g)
      (sf₁.map projSym) (sf₂.map projSym)) :
    grammar_transforms g sf₁ sf₂ := by
      obtain ⟨ r', hr'_mem, u', v', h1, h2 ⟩ := h;
      obtain ⟨ r, hr_mem, rfl ⟩ := List.mem_map.mp hr'_mem;
      use r, hr_mem, u'.map liftSym, v'.map liftSym;
      have h_map_liftSym : List.map liftSym (List.map projSym sf₁) = sf₁ ∧ List.map liftSym (List.map projSym sf₂) = sf₂ := by
        exact ⟨ map_liftSym_map_projSym sf₁, map_liftSym_map_projSym sf₂ ⟩;
      have h_map_liftSym : List.map liftSym (projRule r).input_L = r.input_L ∧ List.map liftSym (projRule r).input_R = r.input_R ∧ List.map liftSym (projRule r).output_string = r.output_string := by
        exact ⟨ map_liftSym_map_projSym _, map_liftSym_map_projSym _, map_liftSym_map_projSym _ ⟩;
      aesop

/-- Derivations in `g` correspond to derivations in `projectGrammar g`. -/
theorem projectGrammar_derives_of_derives (g : grammar (T ⊕ Γ))
    (sf₁ sf₂ : List (symbol (T ⊕ Γ) g.nt))
    (h : grammar_derives g sf₁ sf₂) :
    grammar_derives (projectGrammar g)
      (sf₁.map projSym) (sf₂.map projSym) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ htrans ih =>
    exact ih.tail (projectGrammar_transforms_of_transforms g _ _ htrans)

/-
Derivations in `projectGrammar g` on projected forms correspond to derivations in `g`.
-/
theorem derives_of_projectGrammar_derives (g : grammar (T ⊕ Γ))
    (sf₁ sf₂ : List (symbol (T ⊕ Γ) g.nt))
    (h : grammar_derives (projectGrammar g)
      (sf₁.map projSym) (sf₂.map projSym)) :
    grammar_derives g sf₁ sf₂ := by
      contrapose! h;
      intro H;
      have h_ind : ∀ {u v : List (symbol T (g.nt ⊕ Γ))}, Relation.ReflTransGen (grammar_transforms (projectGrammar g)) u v → Relation.ReflTransGen (grammar_transforms g) (u.map liftSym) (v.map liftSym) := by
        intros u v huv; induction huv; aesop;
        exact Relation.ReflTransGen.trans ‹_› ( Relation.ReflTransGen.single <| by
          apply transforms_of_projectGrammar_transforms;
          convert ‹grammar_transforms ( projectGrammar g ) _ _› using 1;
          · exact map_projSym_map_liftSym _;
          · exact map_projSym_map_liftSym _ );
      convert h_ind H;
      simp +decide [ Function.comp, map_projSym_map_liftSym ];
      rw [ show liftSym ∘ projSym = id from funext fun x => liftSym_projSym x ] ; aesop

/-
**Main theorem**: The projected grammar generates `w` iff the original
grammar generates `w.map Sum.inl`.
-/
theorem projectGrammar_language (g : grammar (T ⊕ Γ)) (w : List T) :
    w ∈ grammar_language (projectGrammar g) ↔
    w.map Sum.inl ∈ grammar_language g := by
      constructor <;> intro h;
      · convert derives_of_projectGrammar_derives g [ symbol.nonterminal g.initial ] ( List.map symbol.terminal ( List.map Sum.inl w ) ) _;
        unfold grammar_language at h
        generalize_proofs at *;
        convert h using 1;
        unfold grammar_generates; aesop;
      · convert projectGrammar_derives_of_derives g _ _ h using 1;
        unfold grammar_language; aesop;

end GrammarProjection