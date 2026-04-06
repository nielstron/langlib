import Langlib.Grammars.Unrestricted.Toolbox
import Langlib.Classes.RecursivelyEnumerable.Definition
import Langlib.Utilities.LanguageOperations

/-! # RE Closure Under Terminal Bijection

This file proves closure of recursively enumerable languages under bijective
renaming of terminals.

The key construction is `bijection_grammar`, which maps terminals in all rule
components via an equivalence `π : T₁ ≃ T₂`. The main result
`bijection_grammar_language` shows that this grammar generates exactly the
π-image of the original language. This is then used by the context-free and
context-sensitive bijection proofs via commutativity with their respective
embeddings.

## Main declarations

- `map_symbol`
- `map_symbol_fn`
- `bijection_grule`
- `bijection_grammar`
- `map_grammar`
- `bijection_grammar_language`
- `map_grammar_language_of_leftInverse`
- `RE_of_map_injective_RE`
- `RE_of_bijemap_RE`
-/

variable {T₁ T₂ : Type}

/-- Map a symbol along a terminal equivalence, leaving nonterminals unchanged. -/
def map_symbol {N : Type} (π : T₁ ≃ T₂) : symbol T₁ N → symbol T₂ N
  | symbol.terminal t => symbol.terminal (π t)
  | symbol.nonterminal n => symbol.nonterminal n

/-- Map a symbol back along the inverse equivalence. -/
def map_symbol_inv {N : Type} (π : T₁ ≃ T₂) : symbol T₂ N → symbol T₁ N
  | symbol.terminal t => symbol.terminal (π.symm t)
  | symbol.nonterminal n => symbol.nonterminal n

/-- Map terminals along an arbitrary function, leaving nonterminals unchanged. -/
def map_symbol_fn {N : Type} (f : T₁ → T₂) : symbol T₁ N → symbol T₂ N
  | symbol.terminal t => symbol.terminal (f t)
  | symbol.nonterminal n => symbol.nonterminal n

@[simp]
lemma map_symbol_fn_comp {N : Type} (f : T₁ → T₂) (g : T₂ → T₁) (s : symbol T₁ N) :
    map_symbol_fn g (map_symbol_fn f s) = map_symbol_fn (g ∘ f) s := by
  cases s <;> rfl

@[simp]
lemma map_symbol_fn_leftInverse {N : Type} {f : T₁ → T₂} {g : T₂ → T₁}
    (hfg : Function.LeftInverse g f) (s : symbol T₁ N) :
    map_symbol_fn g (map_symbol_fn f s) = s := by
  cases s <;> simp [map_symbol_fn, hfg _]

@[simp]
lemma map_symbol_inv_map_symbol {N : Type} (π : T₁ ≃ T₂) (s : symbol T₁ N) :
    map_symbol_inv π (map_symbol π s) = s := by
  cases s <;> simp [map_symbol, map_symbol_inv]

@[simp]
lemma map_symbol_map_symbol_inv {N : Type} (π : T₁ ≃ T₂) (s : symbol T₂ N) :
    map_symbol π (map_symbol_inv π s) = s := by
  cases s <;> simp [map_symbol, map_symbol_inv]

/-- Map an unrestricted grammar rule along a terminal equivalence. -/
def bijection_grule {N : Type} (π : T₁ ≃ T₂) (r : grule T₁ N) : grule T₂ N :=
  grule.mk (r.input_L.map (map_symbol π)) r.input_N
    (r.input_R.map (map_symbol π)) (r.output_string.map (map_symbol π))

/-- Map an unrestricted grammar along a terminal equivalence. -/
def bijection_grammar (g : grammar T₁) (π : T₁ ≃ T₂) : grammar T₂ :=
  grammar.mk g.nt g.initial (g.rules.map (bijection_grule π))

/-- Map an unrestricted grammar along an arbitrary terminal map. -/
def map_grammar (g : grammar T₁) (f : T₁ → T₂) : grammar T₂ :=
  grammar.mk g.nt g.initial <|
    g.rules.map fun r =>
      grule.mk (r.input_L.map (map_symbol_fn f)) r.input_N
        (r.input_R.map (map_symbol_fn f)) (r.output_string.map (map_symbol_fn f))

private def symbol_in_image (f : T₁ → T₂) {N : Type} : symbol T₂ N → Prop
  | symbol.terminal t => ∃ a, f a = t
  | symbol.nonterminal _ => True

private lemma symbol_in_image_map_symbol_fn (f : T₁ → T₂) {N : Type} (s : symbol T₁ N) :
    symbol_in_image f (map_symbol_fn f s) := by
  cases s <;> simp [symbol_in_image, map_symbol_fn]

private lemma derives_symbols_in_image (g : grammar T₁) (f : T₁ → T₂) :
    ∀ {u v : List (symbol T₂ g.nt)},
      grammar_derives (map_grammar g f) u v →
      (∀ s ∈ u, symbol_in_image f s) →
      (∀ s ∈ v, symbol_in_image f s) := by
  intro u v h
  induction h with
  | refl =>
      intro hu
      exact hu
  | tail _ step ih =>
      intro hu s hs
      rcases step with ⟨r, hr, u', v', hsrc, htgt⟩
      obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
      rw [htgt] at hs
      simp only [List.mem_append, List.mem_map, exists_or, or_assoc] at hs
      rcases hs with hs | hs | hs
      · exact ih hu _ (by rw [hsrc]; simp [hs])
      · rcases hs with ⟨s', hs', rfl⟩
        exact symbol_in_image_map_symbol_fn f s'
      · exact ih hu _ (by rw [hsrc]; simp [hs])

/-- The bijection grammar generates exactly the π-image of the original language.
    This is the core result from which all class-specific bijection closure theorems
    are derived. -/
theorem bijection_grammar_language (g : grammar T₁) (π : T₁ ≃ T₂) :
    grammar_language (bijection_grammar g π) = Language.bijemapLang (grammar_language g) π := by
  ext w;
  constructor;
  · -- By definition of `bijection_grule`, we know that if `w` is derived from `g` using `π`, then `w` is in the language generated by `g` under `π`.
    have h_derives : ∀ (u v : List (symbol T₂ g.nt)), grammar_derives (bijection_grammar g π) u v → grammar_derives g (List.map (map_symbol_inv π) u) (List.map (map_symbol_inv π) v) := by
      intro u v h;
      induction h;
      · constructor;
      · rename_i h₁ h₂ h₃;
        obtain ⟨ r, hr, u', v', hu, hv ⟩ := h₂;
        obtain ⟨ r', hr', rfl ⟩ := List.mem_map.mp hr;
        convert h₃.tail _ using 1;
        use r';
        simp_all +decide [ bijection_grule ];
        use List.map (map_symbol_inv π) u', List.map (map_symbol_inv π) v';
        simp +decide [ Function.comp, map_symbol_inv_map_symbol ];
        exact ⟨ by congr <;> ext <;> aesop, by ext; aesop ⟩;
    -- Apply the hypothesis `h_derives` to the derivation from the initial symbol to `w` in the bijection grammar.
    intro h_deriv
    have h_deriv_g : grammar_derives g (List.map (map_symbol_inv π) [symbol.nonterminal g.initial]) (List.map (map_symbol_inv π) (List.map (symbol.terminal) w)) := by
      exact h_derives _ _ h_deriv;
    have h_deriv_g : grammar_derives g [symbol.nonterminal g.initial] (List.map (symbol.terminal) (List.map (π.symm) w)) := by
      convert h_deriv_g using 1 ; aesop;
    exact h_deriv_g;
  · intro hw;
    -- By definition of `bijection_grule`, we know that if `w` is in the language of `g`, then `map_symbol π w` is in the language of `bijection_grammar g π`.
    have h_bijection : ∀ (w : List (symbol T₁ g.nt)), grammar_derives g [symbol.nonterminal g.initial] w → grammar_derives (bijection_grammar g π) [symbol.nonterminal g.initial] (List.map (map_symbol π) w) := by
      intro w hw;
      induction hw;
      · constructor;
      · rename_i b c hb hc ih;
        obtain ⟨ r, hr, u, v, rfl, rfl ⟩ := hc;
        convert ih.tail _ using 1;
        use bijection_grule π r;
        unfold bijection_grammar bijection_grule; aesop;
    convert h_bijection _ hw using 1;
    simp +decide [ map_symbol, List.map_map ];
    rw [ show ( map_symbol π ∘ symbol.terminal ∘ ⇑π.symm ) = symbol.terminal from funext fun x => by simp +decide [ map_symbol ] ] ; aesop

/-- If `g` is a left inverse of `f`, mapping an unrestricted grammar along `f`
    generates exactly the `Language.map f` image of the original language. -/
theorem map_grammar_language_of_leftInverse (g : grammar T₁) {f : T₁ → T₂} {g' : T₂ → T₁}
    (hfg : Function.LeftInverse g' f) :
    grammar_language (map_grammar g f) = Language.map f (grammar_language g) := by
  ext w
  constructor
  · intro hw
    change grammar_derives (map_grammar g f) [symbol.nonterminal g.initial] (List.map symbol.terminal w) at hw
    have h_derives :
        ∀ u v : List (symbol T₂ g.nt),
          grammar_derives (map_grammar g f) u v →
            grammar_derives g (u.map (map_symbol_fn g')) (v.map (map_symbol_fn g')) := by
      intro u v h
      induction h with
      | refl =>
          simpa using grammar_deri_self (g := g) (w := u.map (map_symbol_fn g'))
      | tail _ step ih =>
          apply grammar_deri_of_deri_tran ih
          rcases step with ⟨r, hr, u', v', hu, hv⟩
          obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
          have hu' := congrArg (List.map (map_symbol_fn g')) hu
          have hv' := congrArg (List.map (map_symbol_fn g')) hv
          have hleft : map_symbol_fn g' ∘ map_symbol_fn f = @id (symbol T₁ g.nt) := by
            funext s
            exact map_symbol_fn_leftInverse hfg s
          refine ⟨r', hr', u'.map (map_symbol_fn g'), v'.map (map_symbol_fn g'), ?_, ?_⟩
          · simpa [List.map_map, hleft, List.append_assoc]
              using hu'
          · simpa [List.map_map, hleft, List.append_assoc]
              using hv'
    have hpre := h_derives _ _ hw
    have hpre' : grammar_derives g [symbol.nonterminal g.initial]
        (List.map symbol.terminal (List.map g' w)) := by
      simpa [List.map_map, map_symbol_fn] using hpre
    have himage : ∀ a ∈ w, ∃ b, f b = a := by
      have hsymbols := derives_symbols_in_image g f hw (by
        intro s hs
        simp at hs
        subst hs
        trivial)
      intro a ha
      have hs : symbol_in_image f (symbol.terminal a) := hsymbols _ (by
        change symbol.terminal a ∈ List.map symbol.terminal w
        exact List.mem_map.mpr ⟨a, ha, rfl⟩)
      simpa [symbol_in_image] using hs
    have hw_eq : List.map f (List.map g' w) = w := by
      have hpoint : ∀ a ∈ w, f (g' a) = a := by
        intro a ha
        rcases himage a ha with ⟨b, hb⟩
        calc
          f (g' a) = f (g' (f b)) := by simpa [hb]
          _ = f b := by simp [hfg b]
          _ = a := hb
      have aux : ∀ w : List T₂, (∀ a ∈ w, f (g' a) = a) → List.map f (List.map g' w) = w := by
        intro w
        induction w with
        | nil =>
            intro _
            rfl
        | cons a w ih =>
            intro h
            have ha : f (g' a) = a := h a (by simp)
            have hw' : ∀ b ∈ w, f (g' b) = b := by
              intro b hb
              exact h b (by simp [hb])
            simpa [ha] using ih hw'
      exact aux w hpoint
    exact ⟨List.map g' w, hpre', hw_eq⟩
  · rintro ⟨w', hw', rfl⟩
    change grammar_derives (map_grammar g f) [symbol.nonterminal g.initial]
      (List.map symbol.terminal (List.map f w'))
    have h_map :
        ∀ v : List (symbol T₁ g.nt),
          grammar_derives g [symbol.nonterminal g.initial] v →
            grammar_derives (map_grammar g f) [symbol.nonterminal g.initial] (v.map (map_symbol_fn f)) := by
      intro v hv
      induction hv with
      | refl =>
          simpa using grammar_deri_self (g := map_grammar g f)
            (w := [symbol.nonterminal g.initial])
      | tail _ step ih =>
          apply grammar_deri_of_deri_tran ih
          rcases step with ⟨r, hr, u, v, hu, hv⟩
          have hu' := congrArg (List.map (map_symbol_fn f)) hu
          have hv' := congrArg (List.map (map_symbol_fn f)) hv
          refine ⟨_, List.mem_map.mpr ⟨r, hr, rfl⟩, u.map (map_symbol_fn f), v.map (map_symbol_fn f), ?_, ?_⟩
          · simpa [map_grammar, List.map_map, map_symbol_fn, List.append_assoc] using hu'
          · simpa [map_grammar, List.map_map, map_symbol_fn, List.append_assoc] using hv'
    simpa [List.map_map, map_symbol_fn] using h_map _ hw'

/-- RE languages are closed under injective terminal maps. -/
theorem RE_of_map_injective_RE [Nonempty T₁] {f : T₁ → T₂} (hf : Function.Injective f)
    (L : Language T₁) :
    is_RE L → is_RE (Language.map f L) := by
  rintro ⟨g, hgL⟩
  refine ⟨map_grammar g f, ?_⟩
  rw [map_grammar_language_of_leftInverse g (Function.leftInverse_invFun hf), hgL]

/-- The class of RE languages is closed under bijective terminal renaming. -/
theorem RE_of_bijemap_RE (π : T₁ ≃ T₂) (L : Language T₁) :
    is_RE L → is_RE (Language.bijemapLang L π) := by
  rintro ⟨g, hgL⟩
  exact ⟨bijection_grammar g π, by rw [bijection_grammar_language, hgL]⟩

/-- The converse direction. -/
theorem RE_of_bijemap_RE_rev (π : T₁ ≃ T₂) (L : Language T₁) :
    is_RE (Language.bijemapLang L π) → is_RE L := by
  intro h
  have h' := RE_of_bijemap_RE π.symm _ h
  simpa using h'

/-- A language is RE iff its image under a bijection of terminal alphabets is RE. -/
@[simp] theorem RE_bijemap_iff_RE (π : T₁ ≃ T₂) (L : Language T₁) :
    is_RE (Language.bijemapLang L π) ↔ is_RE L := by
  constructor
  · exact RE_of_bijemap_RE_rev π L
  · exact RE_of_bijemap_RE π L
