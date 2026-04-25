import Mathlib
import Langlib.Grammars.Unrestricted.Definition
import Langlib.Grammars.Unrestricted.Toolbox

/-! # Grammar Pullback (Inverse Homomorphism)

Given a grammar `g` over terminal alphabet `Γ` and a map `encode : T → Γ`
(with `[Fintype T]`), we construct a grammar
`GrammarPullback.pullbackGrammar g encode` over terminal alphabet `T` such that:

  `w ∈ grammar_language (pullbackGrammar g encode) ↔ w.map encode ∈ grammar_language g`

This generalizes `GrammarProjection.projectGrammar` to arbitrary encoding functions.
-/

namespace GrammarPullback

variable {T Γ NT : Type}

/-! ### Symbol maps -/

/-- Lift symbols from `g` (over `Γ`) to the pullback grammar (over `T`).
Terminals become decoding nonterminals; nonterminals are tagged. -/
def liftSym : symbol Γ NT → symbol T (NT ⊕ Γ)
  | .terminal γ => .nonterminal (Sum.inr γ)
  | .nonterminal n => .nonterminal (Sum.inl n)

/-- Project symbols from the pullback grammar back to `g`.
Terminals in `T` are mapped via `encode`; nonterminals are untagged. -/
def projSym (encode : T → Γ) : symbol T (NT ⊕ Γ) → symbol Γ NT
  | .terminal t => .terminal (encode t)
  | .nonterminal (Sum.inl n) => .nonterminal n
  | .nonterminal (Sum.inr γ) => .terminal γ

theorem projSym_liftSym (encode : T → Γ) (s : symbol Γ NT) :
    projSym encode (liftSym s) = s := by
  cases s <;> simp [liftSym, projSym]

theorem map_projSym_map_liftSym (encode : T → Γ) (l : List (symbol Γ NT)) :
    (l.map liftSym).map (projSym encode) = l := by
  rw [List.map_map]; conv_rhs => rw [← List.map_id l]
  congr 1; ext s; exact projSym_liftSym encode s

/-! ### Pullback grammar construction -/

/-- Lift a grammar rule from `g` to the pullback grammar. -/
def liftRule (r : grule Γ NT) : grule T (NT ⊕ Γ) where
  input_L := r.input_L.map liftSym
  input_N := Sum.inl r.input_N
  input_R := r.input_R.map liftSym
  output_string := r.output_string.map liftSym

/-- A decode rule: `(Sum.inr (encode t)) → [terminal t]`. -/
def decodeRule (encode : T → Γ) (t : T) : grule T (NT ⊕ Γ) where
  input_L := []
  input_N := Sum.inr (encode t)
  input_R := []
  output_string := [symbol.terminal t]

/-- The pullback grammar: given grammar `g` over `Γ` and `encode : T → Γ`,
produces a grammar over `T` that generates `w` iff `g` generates `w.map encode`. -/
noncomputable def pullbackGrammar (g : grammar Γ) (encode : T → Γ) [Fintype T] : grammar T where
  nt := g.nt ⊕ Γ
  initial := Sum.inl g.initial
  rules :=
    (g.rules.map (liftRule (NT := g.nt))) ++
    (Fintype.elems.toList.map (decodeRule (NT := g.nt) encode))

/-! ### Forward direction: pullback generates ⟹ g generates encoded -/

/-
Any transformation step in the pullback grammar projects (via `projSym`)
to either a step in `g` or a no-op (for decode rules).
-/
theorem transforms_proj (g : grammar Γ) (encode : T → Γ) [Fintype T]
    (sf₁ sf₂ : List (symbol T (g.nt ⊕ Γ)))
    (h : grammar_transforms (pullbackGrammar g encode) sf₁ sf₂) :
    grammar_derives g (sf₁.map (projSym encode)) (sf₂.map (projSym encode)) := by
  obtain ⟨ r, hr, u, v, rfl, rfl ⟩ := h;
  unfold pullbackGrammar at hr; simp_all +decide [ List.mem_append ] ;
  rcases hr with ( ⟨ a, ha, rfl ⟩ | ⟨ a, ha, rfl ⟩ );
  · -- Apply the definition of `liftRule` and `projSym` to simplify the goal.
    have h_simp : List.map (projSym encode) (liftRule a).input_L = a.input_L ∧ List.map (projSym encode) (liftRule a).input_R = a.input_R ∧ List.map (projSym encode) (liftRule a).output_string = a.output_string := by
      exact ⟨ map_projSym_map_liftSym encode a.input_L, map_projSym_map_liftSym encode a.input_R, map_projSym_map_liftSym encode a.output_string ⟩;
    exact .single ⟨ a, ha, List.map ( projSym encode ) u, List.map ( projSym encode ) v, by aesop ⟩;
  · convert Relation.ReflTransGen.refl using 1

/-
Derivations in the pullback grammar project to derivations in `g`.
-/
theorem derives_proj (g : grammar Γ) (encode : T → Γ) [Fintype T]
    (sf₁ sf₂ : List (symbol T (g.nt ⊕ Γ)))
    (h : grammar_derives (pullbackGrammar g encode) sf₁ sf₂) :
    grammar_derives g (sf₁.map (projSym encode)) (sf₂.map (projSym encode)) := by
  induction h;
  · exact Relation.ReflTransGen.refl;
  · exact grammar_deri_of_deri_deri ‹_› ( transforms_proj _ _ _ _ ‹_› )

/-
Forward direction: if the pullback grammar generates `w`, then `g` generates `w.map encode`.
-/
theorem pullback_generates_implies_original (g : grammar Γ) (encode : T → Γ) [Fintype T]
    (w : List T)
    (h : w ∈ grammar_language (pullbackGrammar g encode)) :
    w.map encode ∈ grammar_language g := by
  contrapose! h;
  intro hw;
  obtain ⟨l₁, l₂, hl₁, hl₂, h⟩ : ∃ l₁ l₂, l₁ = [symbol.nonterminal (Sum.inl g.initial)] ∧ l₂ = w.map symbol.terminal ∧ grammar_derives (pullbackGrammar g encode) l₁ l₂ := by
    exact ⟨ _, _, rfl, rfl, hw ⟩;
  have h_proj : grammar_derives g (l₁.map (projSym encode)) (l₂.map (projSym encode)) := by
    exact derives_proj g encode l₁ l₂ h;
  simp_all +decide [ grammar_language ];
  exact ‹List.map encode w ∉ setOf ( grammar_generates g ) › ( by simpa [ grammar_generates ] using h_proj )

/-! ### Backward direction: g generates encoded ⟹ pullback generates -/

/-
Core rule steps in `g` lift to core rule steps in the pullback grammar.
-/
theorem pullback_transforms_of_transforms (g : grammar Γ) (encode : T → Γ) [Fintype T]
    (sf₁ sf₂ : List (symbol Γ g.nt))
    (h : grammar_transforms g sf₁ sf₂) :
    grammar_transforms (pullbackGrammar g encode)
      (sf₁.map liftSym) (sf₂.map liftSym) := by
  obtain ⟨ r, hr, u, v, rfl, rfl ⟩ := h;
  use liftRule r;
  unfold liftRule pullbackGrammar; aesop;

/-
Derivations in `g` lift to derivations in the pullback grammar.
-/
theorem pullback_derives_of_derives (g : grammar Γ) (encode : T → Γ) [Fintype T]
    (sf₁ sf₂ : List (symbol Γ g.nt))
    (h : grammar_derives g sf₁ sf₂) :
    grammar_derives (pullbackGrammar g encode)
      (sf₁.map liftSym) (sf₂.map liftSym) := by
  induction h;
  · constructor;
  · exact Relation.ReflTransGen.trans ‹_› ( Relation.ReflTransGen.single ( pullback_transforms_of_transforms g encode _ _ ‹_› ) )

/-
Decode all positions: given a list of `nonterminal (Sum.inr (encode tᵢ))`,
derive the corresponding `terminal tᵢ` list.
-/
theorem decode_all (g : grammar Γ) (encode : T → Γ) [Fintype T]
    (w : List T) :
    grammar_derives (pullbackGrammar g encode)
      (w.map (fun t => symbol.nonterminal (Sum.inr (encode t))))
      (w.map symbol.terminal) := by
  induction' w with t w ih;
  · constructor;
  · -- Apply the decode rule to the first element of the list.
    have h_decode : grammar_transforms (pullbackGrammar g encode) (List.map (fun t => symbol.nonterminal (Sum.inr (encode t))) (t :: w)) (symbol.terminal t :: List.map (fun t => symbol.nonterminal (Sum.inr (encode t))) w) := by
      apply Exists.intro (decodeRule encode t);
      simp +decide [ pullbackGrammar ];
      exact ⟨ Or.inr ⟨ t, Fintype.complete t, rfl ⟩, [ ], List.map ( fun t => symbol.nonterminal ( Sum.inr ( encode t ) ) ) w, rfl, rfl ⟩;
    apply grammar_deri_of_deri_deri;
    exact .single h_decode;
    simpa using grammar_deri_with_prefix [ symbol.terminal t ] ih

/-
Backward direction: if `g` generates `w.map encode`, then the pullback
grammar generates `w`.
-/
theorem original_generates_implies_pullback (g : grammar Γ) (encode : T → Γ) [Fintype T]
    (w : List T)
    (h : w.map encode ∈ grammar_language g) :
    w ∈ grammar_language (pullbackGrammar g encode) := by
  have := h;
  convert this using 1;
  constructor <;> intro h';
  · exact this;
  · convert Relation.ReflTransGen.trans _ _;
    exact List.map ( fun t => symbol.nonterminal ( Sum.inr ( encode t ) ) ) w;
    · convert pullback_derives_of_derives g encode _ _ h' using 1;
      aesop;
    · convert decode_all g encode w using 1

/-! ### Main theorem -/

/-- **Pullback grammar language**: The pullback grammar generates `w` iff
`g` generates `w.map encode`. -/
theorem pullbackGrammar_language (g : grammar Γ) (encode : T → Γ) [Fintype T]
    (w : List T) :
    w ∈ grammar_language (pullbackGrammar g encode) ↔
    w.map encode ∈ grammar_language g :=
  ⟨pullback_generates_implies_original g encode w,
   original_generates_implies_pullback g encode w⟩

end GrammarPullback