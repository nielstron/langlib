module

public import Langlib.Classes.ContextFree.Decidability.EncodedOperations
public import Langlib.Classes.RecursivelyEnumerable.Closure.Homomorphism

@[expose]
public section

/-!
# Effective homomorphic images of encoded context-free grammars

This module implements the terminal-to-word operation needed by effective
alphabet codings.  The construction is deliberately the same two-phase
construction as `hom_grammar`: terminals in the source grammar first become
placeholder nonterminals, and one expansion rule for every used terminal emits
its image word.

The construction is exact for epsilon-free homomorphisms.  It is primitive
recursive uniformly in the encoded source grammar, and it preserves the
raw-code invariant `NoEmptyRHS` when the homomorphism is epsilon-free.
-/

namespace ContextFree.EncodedCFG

variable {A B : Type}

open EncodedCFG

/-! ## Semantic grammar construction -/

/-- Context-free version of the two-phase epsilon-free homomorphic-image
grammar `hom_grammar`. -/
def homomorphicImageGrammar (g : CF_grammar A) (h : A → List B) :
    CF_grammar B where
  nt := g.nt ⊕ A
  initial := Sum.inl g.initial
  rules :=
    g.rules.map (fun r ↦
      (Sum.inl r.1, r.2.map homLiftSym)) ++
    (all_used_terminals (grammar_of_cfg g)).map (fun a ↦
      (Sum.inr a, (h a).map symbol.terminal))

private theorem grammar_of_cfg_homomorphicImageGrammar
    (g : CF_grammar A) (h : A → List B) :
    grammar_of_cfg (homomorphicImageGrammar g h) =
      hom_grammar (grammar_of_cfg g) h := by
  simp only [homomorphicImageGrammar, grammar_of_cfg, hom_grammar,
    homLiftRule, homLiftStr, all_used_terminals, List.map_append,
    List.map_map, Function.comp_def]
  congr 1

/-- The semantic two-phase CFG denotes the homomorphic image for every
epsilon-free terminal-to-word map. -/
theorem language_homomorphicImageGrammar (g : CF_grammar A)
    (h : A → List B) (heps : IsEpsFreeHomomorphism h) :
    CF_language (homomorphicImageGrammar g h) =
      (CF_language g).homomorphicImage h := by
  rw [CF_language_eq_grammar_language,
    grammar_of_cfg_homomorphicImageGrammar,
    hom_grammar_language_epsfree _ _ heps,
    CF_language_eq_grammar_language]

/-! ## Numeric encoding -/

/-- Numeric layout consisting of the old nonterminal block followed by one
placeholder for every source terminal. -/
noncomputable def homomorphicImageNTEq [Fintype A] (G : EncodedCFG A) :
    Fin G.ntCount ⊕ A ≃
      Fin (G.numNT + Fintype.card A + 1) :=
  ((Equiv.refl (Fin G.ntCount)).sumCongr (Fintype.equivFin A)).trans
    finSumFinEquiv |>.trans
      (finCongr (by
        simp [EncodedCFG.ntCount, EncodedCFG.numNT]
        omega))

/-- Encode the two-phase homomorphic-image grammar. -/
noncomputable def homomorphicImage [Fintype A]
    (h : A → List B) (G : EncodedCFG A) : EncodedCFG B :=
  ContextFree.EncodedCFG.encodeCFG
    (homomorphicImageGrammar G.toCFGrammar h)
    (homomorphicImageNTEq G)

/-! ## Explicit raw form -/

variable [Fintype A]

private def rawTerminal? : ℕ ⊕ A → Option A
  | .inl _ => none
  | .inr a => some a

private def usedRawTerminals (G : EncodedCFG A) : List A :=
  G.rawRules.flatMap fun r ↦ r.2.filterMap rawTerminal?

private def homLiftRawSymbol (count : ℕ)
    (e : A → Fin (Fintype.card A)) : ℕ ⊕ A → ℕ ⊕ B
  | .inl N => .inl (N % count)
  | .inr a => .inl (count + (e a).val)

private def homLiftRawRule (count : ℕ)
    (e : A → Fin (Fintype.card A))
    (r : ℕ × List (ℕ ⊕ A)) : ℕ × List (ℕ ⊕ B) :=
  (r.1 % count, r.2.map (homLiftRawSymbol count e))

private def homExpandRawRule (count : ℕ)
    (e : A → Fin (Fintype.card A)) (h : A → List B)
    (a : A) : ℕ × List (ℕ ⊕ B) :=
  (count + (e a).val, (h a).map Sum.inr)

private def homomorphicImageRaw [Fintype A]
    (e : A → Fin (Fintype.card A)) (h : A → List B)
    (G : EncodedCFG A) : EncodedCFG B :=
  (G.numNT + Fintype.card A,
    G.initialIdx % G.ntCount,
    G.rawRules.map (homLiftRawRule G.ntCount e) ++
      (usedRawTerminals G).map
        (homExpandRawRule G.ntCount e h))

private theorem homomorphicImage_eq_raw (h : A → List B)
    (G : EncodedCFG A) :
    homomorphicImage h G =
      homomorphicImageRaw (Fintype.equivFin A) h G := by
  rcases G with ⟨n, initial, rules⟩
  simp [homomorphicImage, homomorphicImageRaw,
    homomorphicImageGrammar, homomorphicImageNTEq,
    usedRawTerminals,
    ContextFree.EncodedCFG.encodeCFG,
    ContextFree.EncodedCFG.encodeSymbol,
    EncodedCFG.toCFGrammar, EncodedCFG.toNT,
    EncodedCFG.toSymbol, EncodedCFG.ntCount, EncodedCFG.numNT,
    EncodedCFG.initialIdx, EncodedCFG.rawRules,
    all_used_terminals, grammar_of_cfg, homLiftSym,
    List.map_map, Function.comp_def,
    finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]
  congr 2
  congr 1
  · apply List.map_congr_left
    rintro ⟨lhs, rhs⟩ _
    unfold homLiftRawRule
    apply Prod.ext
    · rfl
    · apply List.map_congr_left
      intro s _
      cases s <;>
        simp [homLiftRawSymbol,
          finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]
  · change List.flatMap _ rules = _
    rw [List.map_flatMap]
    apply List.flatMap_congr
    rintro ⟨lhs, rhs⟩ hr
    clear hr
    induction rhs with
    | nil => simp
    | cons s rhs ih =>
        cases s <;>
          simpa [rawTerminal?, homExpandRawRule, as_terminal] using ih

/-! ## Correctness and syntactic preservation -/

/-- The encoded construction denotes the epsilon-free homomorphic image of
the source language. -/
theorem contextFreeLanguageOf_homomorphicImage (h : A → List B)
    (G : EncodedCFG A) (heps : IsEpsFreeHomomorphism h) :
    contextFreeLanguageOf (homomorphicImage h G) =
      (contextFreeLanguageOf G).homomorphicImage h := by
  unfold contextFreeLanguageOf homomorphicImage
  rw [cf_language_encodeCFG,
    language_homomorphicImageGrammar _ _ heps]

/-- Epsilon-free terminal expansions preserve the invariant that every raw
production has a nonempty right-hand side. -/
theorem noEmptyRHS_homomorphicImage {h : A → List B}
    {G : EncodedCFG A} (hG : NoEmptyRHS G)
    (heps : IsEpsFreeHomomorphism h) :
    NoEmptyRHS (homomorphicImage h G) := by
  rw [homomorphicImage_eq_raw]
  intro r hr
  simp only [homomorphicImageRaw, EncodedCFG.rawRules,
    List.mem_append, List.mem_map] at hr
  rcases hr with ⟨r₀, hr₀, rfl⟩ | ⟨a, ha, rfl⟩
  · intro hnil
    exact hG r₀ hr₀ (List.map_eq_nil_iff.mp hnil)
  · intro hnil
    exact heps a (List.map_eq_nil_iff.mp hnil)

/-! ## Effectivity -/

omit [Fintype A] in
private theorem rawTerminal?_primrec [Primcodable A] :
    Primrec (rawTerminal? : ℕ ⊕ A → Option A) := by
  refine (Primrec.sumCasesOn
    (f := fun s : ℕ ⊕ A ↦ s)
    (g := fun _ _ ↦ none)
    (h := fun _ a ↦ some a)
    Primrec.id ?_ ?_).of_eq ?_
  · exact Primrec₂.mk (Primrec.const none)
  · exact Primrec₂.mk (Primrec.option_some.comp Primrec.snd)
  · intro s
    cases s <;> rfl

omit [Fintype A] in
private theorem usedRawTerminals_primrec [Primcodable A] :
    Primrec (usedRawTerminals : EncodedCFG A → List A) := by
  unfold usedRawTerminals
  apply Primrec.list_flatMap rawRules_primrec
  apply Primrec₂.mk
  exact Primrec.listFilterMap
    (Primrec.snd.comp Primrec.snd)
    (Primrec₂.mk (rawTerminal?_primrec.comp Primrec.snd))

private theorem homLiftRawSymbol_primrec [Primcodable A] [Primcodable B]
    {e : A → Fin (Fintype.card A)} (he : Primrec e) :
    Primrec (fun p : ℕ × (ℕ ⊕ A) ↦
      (homLiftRawSymbol p.1 e p.2 : ℕ ⊕ B)) := by
  refine (Primrec.sumCasesOn
    (f := fun p : ℕ × (ℕ ⊕ A) ↦ p.2)
    (g := fun p N ↦ (Sum.inl (N % p.1) : ℕ ⊕ B))
    (h := fun p a ↦
      (Sum.inl (p.1 + (e a).val) : ℕ ⊕ B))
    Primrec.snd ?_ ?_).of_eq ?_
  · apply Primrec₂.mk
    exact Primrec.sumInl.comp
      (Primrec.nat_mod.comp Primrec.snd
        (Primrec.fst.comp Primrec.fst))
  · apply Primrec₂.mk
    exact Primrec.sumInl.comp
      (Primrec.nat_add.comp
        (Primrec.fst.comp Primrec.fst)
        (Primrec.fin_val.comp (he.comp Primrec.snd)))
  · intro p
    cases p.2 <;> rfl

private theorem homLiftRawRule_primrec [Primcodable A] [Primcodable B]
    {e : A → Fin (Fintype.card A)} (he : Primrec e) :
    Primrec (fun p : ℕ × (ℕ × List (ℕ ⊕ A)) ↦
      (homLiftRawRule p.1 e p.2 : ℕ × List (ℕ ⊕ B))) := by
  have hlhs : Primrec (fun p : ℕ × (ℕ × List (ℕ ⊕ A)) ↦
      p.2.1 % p.1) :=
    Primrec.nat_mod.comp
      (Primrec.fst.comp Primrec.snd) Primrec.fst
  have hrhs : Primrec (fun p : ℕ × (ℕ × List (ℕ ⊕ A)) ↦
      (p.2.2.map (homLiftRawSymbol p.1 e) : List (ℕ ⊕ B))) := by
    apply Primrec.list_map (Primrec.snd.comp Primrec.snd)
    apply Primrec₂.mk
    exact (homLiftRawSymbol_primrec he).comp
      (Primrec.pair
        (Primrec.fst.comp Primrec.fst) Primrec.snd)
  exact Primrec.pair hlhs hrhs

private theorem homExpandRawRule_primrec [Primcodable A] [Primcodable B]
    {e : A → Fin (Fintype.card A)} (he : Primrec e)
    {h : A → List B} (hh : Primrec h) :
    Primrec (fun p : ℕ × A ↦
      homExpandRawRule p.1 e h p.2) := by
  have hlhs : Primrec (fun p : ℕ × A ↦
      p.1 + (e p.2).val) :=
    Primrec.nat_add.comp Primrec.fst
      (Primrec.fin_val.comp (he.comp Primrec.snd))
  have hrhs : Primrec (fun p : ℕ × A ↦
      (h p.2).map (Sum.inr : B → ℕ ⊕ B)) := by
    apply Primrec.list_map (hh.comp Primrec.snd)
    exact Primrec₂.mk (Primrec.sumInr.comp Primrec.snd)
  exact Primrec.pair hlhs hrhs

private theorem homomorphicImageRaw_primrec
    [Primcodable A] [Primcodable B]
    {e : A → Fin (Fintype.card A)} (he : Primrec e)
    {h : A → List B} (hh : Primrec h) :
    Primrec (homomorphicImageRaw e h : EncodedCFG A → EncodedCFG B) := by
  have hcount : Primrec (fun G : EncodedCFG A ↦ G.ntCount) :=
    ntCount_primrec
  have hnum : Primrec (fun G : EncodedCFG A ↦
      G.numNT + Fintype.card A) :=
    Primrec.nat_add.comp Primrec.fst
      (Primrec.const (Fintype.card A))
  have hinitial : Primrec (fun G : EncodedCFG A ↦
      G.initialIdx % G.ntCount) :=
    Primrec.nat_mod.comp initialIdx_primrec hcount
  have hlifted : Primrec (fun G : EncodedCFG A ↦
      (G.rawRules.map (homLiftRawRule G.ntCount e) :
        List (ℕ × List (ℕ ⊕ B)))) := by
    apply Primrec.list_map rawRules_primrec
    apply Primrec₂.mk
    exact (homLiftRawRule_primrec he).comp
      (Primrec.pair
        (hcount.comp Primrec.fst) Primrec.snd)
  have hexpanded : Primrec (fun G : EncodedCFG A ↦
      (usedRawTerminals G).map
        (homExpandRawRule G.ntCount e h)) := by
    apply Primrec.list_map usedRawTerminals_primrec
    apply Primrec₂.mk
    exact (homExpandRawRule_primrec he hh).comp
      (Primrec.pair
        (hcount.comp Primrec.fst) Primrec.snd)
  have hrules : Primrec (fun G : EncodedCFG A ↦
      G.rawRules.map (homLiftRawRule G.ntCount e) ++
        (usedRawTerminals G).map
          (homExpandRawRule G.ntCount e h)) :=
    Primrec.list_append.comp hlifted hexpanded
  exact Primrec.pair hnum (Primrec.pair hinitial hrules)

/-- The encoded homomorphic-image compiler is primitive recursive uniformly
in the source grammar.  Since the source alphabet is finite, every fixed
terminal-to-word map has a primitive-recursive table. -/
theorem homomorphicImage_primrec [Primcodable A] [Primcodable B]
    (h : A → List B) :
    Primrec (homomorphicImage h : EncodedCFG A → EncodedCFG B) := by
  have he : Primrec (Fintype.equivFin A :
      A → Fin (Fintype.card A)) :=
    Primrec.dom_finite _
  have hh : Primrec h := Primrec.dom_finite _
  exact (homomorphicImageRaw_primrec he hh).of_eq fun G ↦
    (homomorphicImage_eq_raw h G).symm

theorem homomorphicImage_computable [Primcodable A] [Primcodable B]
    (h : A → List B) :
    Computable (homomorphicImage h : EncodedCFG A → EncodedCFG B) :=
  (homomorphicImage_primrec h).to_comp

end ContextFree.EncodedCFG
