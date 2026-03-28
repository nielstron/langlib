import Grammars.Classes.Unrestricted.Basics.Toolbox
import Grammars.Utilities.LanguageOperations

/-! # RE Closure Under Bijection

This file proves closure of recursively enumerable languages under bijective
renaming of terminals.

The key construction `terminal_map_grammar` applies a terminal bijection to every
rule of an unrestricted grammar.  The central result
`grammar_language_terminal_map_grammar` shows that the language of the mapped
grammar equals the image of the original language under the bijection.  This fact
is then reused by the context-free bijection proof, avoiding duplicated derivation
arguments.

## Main declarations

- `terminal_map_symbol`   — map a single symbol along a terminal bijection
- `terminal_map_grule`    — map a single unrestricted rule
- `terminal_map_grammar`  — map every rule of an unrestricted grammar
- `grammar_language_terminal_map_grammar` — language of mapped grammar = mapped language
- `RE_of_bijemap_RE`
-/

variable {T₁ T₂ : Type}

section terminal_map_defs

/-- Map a single symbol along a terminal bijection, leaving nonterminals unchanged. -/
def terminal_map_symbol {N : Type} (π : T₁ ≃ T₂) : symbol T₁ N → symbol T₂ N
  | symbol.terminal t => symbol.terminal (π t)
  | symbol.nonterminal n => symbol.nonterminal n

/-- Map a list of symbols along a terminal bijection. -/
def terminal_map_symbols {N : Type} (π : T₁ ≃ T₂) : List (symbol T₁ N) → List (symbol T₂ N) :=
  List.map (terminal_map_symbol π)

@[simp] lemma terminal_map_symbol_inv {N : Type} (π : T₁ ≃ T₂) (s : symbol T₁ N) :
    terminal_map_symbol π.symm (terminal_map_symbol π s) = s := by
  cases s <;> simp [terminal_map_symbol]

@[simp] lemma terminal_map_symbol_inv' {N : Type} (π : T₁ ≃ T₂) (s : symbol T₂ N) :
    terminal_map_symbol π (terminal_map_symbol π.symm s) = s := by
  cases s <;> simp [terminal_map_symbol]

lemma terminal_map_symbol_comp {N : Type} (π : T₁ ≃ T₂) :
    @terminal_map_symbol T₂ T₁ N π.symm ∘ @terminal_map_symbol T₁ T₂ N π = id := by
  ext s; exact terminal_map_symbol_inv π s

lemma terminal_map_symbol_comp' {N : Type} (π : T₁ ≃ T₂) :
    @terminal_map_symbol T₁ T₂ N π ∘ @terminal_map_symbol T₂ T₁ N π.symm = id := by
  ext s; exact terminal_map_symbol_inv' π s

@[simp] lemma terminal_map_symbols_inv {N : Type} (π : T₁ ≃ T₂)
    (l : List (symbol T₁ N)) :
    terminal_map_symbols π.symm (terminal_map_symbols π l) = l := by
  simp [terminal_map_symbols, List.map_map, terminal_map_symbol_comp]

@[simp] lemma terminal_map_symbols_inv' {N : Type} (π : T₁ ≃ T₂)
    (l : List (symbol T₂ N)) :
    terminal_map_symbols π (terminal_map_symbols π.symm l) = l := by
  simp [terminal_map_symbols, List.map_map, terminal_map_symbol_comp']

/-- Map a single unrestricted rule along a terminal bijection. -/
def terminal_map_grule {N : Type} (π : T₁ ≃ T₂) (r : grule T₁ N) : grule T₂ N :=
  grule.mk (terminal_map_symbols π r.input_L) r.input_N
           (terminal_map_symbols π r.input_R) (terminal_map_symbols π r.output_string)

lemma dual_of_terminal_map_grule {N : Type} (π : T₁ ≃ T₂) (r : grule T₁ N) :
    terminal_map_grule π.symm (terminal_map_grule π r) = r := by
  cases r
  simp [terminal_map_grule]

lemma terminal_map_grule_comp {N : Type} (π : T₁ ≃ T₂) :
    @terminal_map_grule T₂ T₁ N π.symm ∘ @terminal_map_grule T₁ T₂ N π = id := by
  ext; apply dual_of_terminal_map_grule

/-- Map every rule of an unrestricted grammar along a terminal bijection. -/
def terminal_map_grammar (π : T₁ ≃ T₂) (g : grammar T₁) : grammar T₂ :=
  grammar.mk g.nt g.initial (List.map (terminal_map_grule π) g.rules)

lemma dual_of_terminal_map_grammar (π : T₁ ≃ T₂) (g : grammar T₁) :
    terminal_map_grammar π.symm (terminal_map_grammar π g) = g := by
  cases g
  unfold terminal_map_grammar
  dsimp only
  rw [List.map_map, terminal_map_grule_comp, List.map_id]

end terminal_map_defs

section terminal_map_language

/-
PROBLEM
A derivation in the terminal-mapped grammar can be translated back to a derivation
in the original grammar by applying the inverse map to every sentential form.

PROVIDED SOLUTION
Induction on the derivation. In the `refl` case, trivial. In the `tail` case, we have a derivation from u to some b, followed by a single step from b to c. By the IH, we have the transformed derivation from π⁻¹(u) to π⁻¹(b). For the last step b→c: unpack the rule r from the mapped grammar, find the original rule r₀ with terminal_map_grule π r₀ = r. Then show that applying π⁻¹ to the step b→c gives a valid step using r₀ in the original grammar. The key is that terminal_map_symbols π.symm distributes over append and that terminal_map_symbol π.symm (symbol.nonterminal n) = symbol.nonterminal n.
-/
private lemma terminal_map_derives (π : T₁ ≃ T₂) (g : grammar T₁)
    {u v : List (symbol T₂ g.nt)}
    (huv : grammar_derives (terminal_map_grammar π g) u v) :
    grammar_derives g (terminal_map_symbols π.symm u) (terminal_map_symbols π.symm v) := by
  induction huv;
  · exact Relation.ReflTransGen.refl;
  · rename_i h₁ h₂ h₃;
    refine' h₃.trans _;
    obtain ⟨ r, hr, u, v, hu, hv ⟩ := h₂;
    -- By definition of `terminal_map_grammar`, we know that `r` is of the form `terminal_map_grule π r₀` for some `r₀` in `g.rules`.
    obtain ⟨ r₀, hr₀, rfl ⟩ : ∃ r₀ ∈ g.rules, r = terminal_map_grule π r₀ := by
      unfold terminal_map_grammar at hr; aesop;
    simp_all +decide [ terminal_map_grule, terminal_map_symbols ];
    convert Relation.ReflTransGen.single ( show grammar_transforms g _ _ from ⟨ r₀, hr₀, List.map ( terminal_map_symbol π.symm ) u, List.map ( terminal_map_symbol π.symm ) v, ?_, ?_ ⟩ ) using 1 <;> simp +decide [ *, Function.comp ];
    · congr! 1;
      · exact List.ext_get ( by simp +decide ) ( by simp +decide [ Function.comp ] );
      · congr! 1;
        congr! 1;
        exact List.ext_get ( by simp +decide ) ( by simp +decide [ Function.comp ] );
    · exact List.ext_get ( by simp +decide [ Function.comp ] ) ( by simp +decide [ Function.comp ] )

/-
PROBLEM
A derivation in the original grammar can be translated to a derivation in the
terminal-mapped grammar by applying the forward map.

PROVIDED SOLUTION
Induction on the derivation. In the `refl` case, trivial. In the `tail` case, we have a derivation from u to some b, followed by a single step from b to c using rule r. By the IH, we have the transformed derivation from π(u) to π(b). For the last step b→c: show that terminal_map_grule π r is in the mapped grammar's rules (since r ∈ g.rules implies terminal_map_grule π r ∈ List.map (terminal_map_grule π) g.rules). Then show that applying π to the step b→c gives a valid step using terminal_map_grule π r. The key is that terminal_map_symbols π distributes over append and terminal_map_symbol π (symbol.nonterminal n) = symbol.nonterminal n.
-/
private lemma terminal_map_derives_forward (π : T₁ ≃ T₂) (g : grammar T₁)
    {u v : List (symbol T₁ g.nt)}
    (huv : grammar_derives g u v) :
    grammar_derives (terminal_map_grammar π g)
      (terminal_map_symbols π u) (terminal_map_symbols π v) := by
  -- By definition of `terminal_map_deriv`, we know that if $u \implies v$, then $\pi(u) \implies \pi(v)$.
  have h_terminal_map_deriv : ∀ (u v : List (symbol T₁ g.nt)), grammar_transforms g u v → grammar_transforms (terminal_map_grammar π g) (terminal_map_symbols π u) (terminal_map_symbols π v) := by
    rintro u v ⟨ r, hr, u', v', rfl, rfl ⟩;
    use terminal_map_grule π r;
    unfold terminal_map_grammar terminal_map_grule terminal_map_symbols; aesop;
  induction huv;
  · constructor;
  · exact Relation.ReflTransGen.tail ‹_› ( h_terminal_map_deriv _ _ ‹_› )

/-
PROBLEM
The language of the terminal-mapped grammar is exactly the image of the original
language under the bijection.

This is the key lemma reused by the context-free bijection proof.

PROVIDED SOLUTION
Use terminal_map_derives and terminal_map_derives_forward. Forward direction: given w in the mapped grammar language, apply terminal_map_derives to get a derivation with π⁻¹ applied, showing π⁻¹(w) is in the original language. Backward direction: given π⁻¹(w) in the original language, apply terminal_map_derives_forward to get a derivation with π applied, then simplify π(π⁻¹(w)) = w. bijemapLang L π is defined as fun w => List.map π.symm w ∈ L.
-/
theorem grammar_language_terminal_map_grammar (π : T₁ ≃ T₂) (g : grammar T₁) :
    grammar_language (terminal_map_grammar π g) = Language.bijemapLang (grammar_language g) π := by
  -- To prove equality of sets, we show each set is a subset of the other.
  apply Set.ext
  intro w
  simp [grammar_language, Language.bijemapLang];
  constructor <;> intro h' <;> unfold grammar_generates at *;
  · -- Apply the inverse map to the derivation in the terminal-mapped grammar.
    have h_inv : grammar_derives g [symbol.nonterminal g.initial] (List.map symbol.terminal (List.map π.symm w)) := by
      convert terminal_map_derives π g h' using 1;
      unfold terminal_map_symbols; aesop;
    exact Set.mem_preimage.mp h_inv;
  · convert terminal_map_derives_forward π g h' using 1;
    -- By definition of `terminal_map_symbols`, applying it twice with the inverse permutation gives back the original list.
    simp [terminal_map_symbols];
    exact fun a ha => by simp +decide [ terminal_map_symbol ] ;

end terminal_map_language

/-- The class of RE languages is closed under bijective terminal renaming. -/
theorem RE_of_bijemap_RE (π : T₁ ≃ T₂) (L : Language T₁) :
    is_RE L → is_RE (Language.bijemapLang L π) := by
  rintro ⟨g, hgL⟩
  exact ⟨terminal_map_grammar π g, by rw [grammar_language_terminal_map_grammar, hgL]⟩

/-- The converse: if the image is RE, so is the original. -/
theorem RE_of_bijemap_RE_rev (π : T₁ ≃ T₂) (L : Language T₁) :
    is_RE (Language.bijemapLang L π) → is_RE L := by
  intro h
  have h' := RE_of_bijemap_RE π.symm _ h
  simpa using h'
