module

public import Langlib.Automata.LinearBounded.Equivalence.ContextSensitive
public import Langlib.Classes.ContextSensitive.Basics.FiniteAlphabet
public import Langlib.Grammars.NonContracting.Equivalence.ContextSensitive
import Mathlib.Tactic

@[expose]
public section

/-!
# Non-contracting grammars and context-preserving grammars

This file completes the hard direction of the classical equivalence between
non-contracting unrestricted grammars and non-erasing context-preserving grammars.

The terminal alphabet of a grammar is always finitely supported, even when its ambient
terminal type is arbitrary.  We therefore first restrict a non-contracting language to
that finite support, use the Kuroda--Myhill `CS = LBA` development to obtain a
context-preserving grammar there, and finally embed that grammar back into the ambient
terminal type.

The last operation is proved below without a finiteness assumption on the target type.
Original terminals are kept as private nonterminals while the source grammar runs and are
converted to ambient terminals only by final one-symbol rules.  Projecting such a derivation
back either gives a source-grammar step or a stuttering step, which proves soundness even
when the final conversions are interleaved with simulation steps.
-/

open scoped Classical

namespace CSGTerminalEmbedding

variable {A T : Type}

/-- Nonterminals used when embedding a context-preserving grammar's terminal alphabet. -/
inductive NT (N : Type) where
  | source : N → NT N
  | terminal : A → NT N

/-- Lift every source symbol to a nonterminal over the target terminal alphabet. -/
def liftSymbol {N : Type} : symbol A N → symbol T (NT (A := A) N)
  | .terminal a => .nonterminal (.terminal a)
  | .nonterminal n => .nonterminal (.source n)

/-- Lift a source context-preserving rule. -/
def liftRule {N : Type} (r : csrule A N) : csrule T (NT (A := A) N) where
  context_left := r.context_left.map liftSymbol
  input_nonterminal := .source r.input_nonterminal
  context_right := r.context_right.map liftSymbol
  output_string := r.output_string.map liftSymbol

/-- Convert one private source-terminal nonterminal to its ambient terminal. -/
def terminalRule {N : Type} (f : A → T) (a : A) : csrule T (NT (A := A) N) where
  context_left := []
  input_nonterminal := .terminal a
  context_right := []
  output_string := [.terminal (f a)]

/-- Embed a context-preserving grammar along an injective terminal map. -/
noncomputable def grammar [Fintype A] [DecidableEq A] (g : CS_grammar A) (f : A ↪ T) :
    CS_grammar T where
  nt := NT (A := A) g.nt
  initial := .source g.initial
  rules := g.rules.map liftRule ++
    (Finset.univ.toList : List A).map (terminalRule (N := g.nt) f)
  output_nonempty := by
    intro r hr
    simp only [List.mem_append, List.mem_map] at hr
    rcases hr with ⟨r, hr, rfl⟩ | ⟨a, _ha, rfl⟩
    · simpa [liftRule] using g.output_nonempty r hr
    · simp [terminalRule]

private lemma map_liftSymbol_injective {N : Type} :
    Function.Injective (List.map (@liftSymbol A T N)) := by
  apply List.map_injective_iff.mpr
  intro x y h
  cases x <;> cases y <;> simp [liftSymbol] at h ⊢
  all_goals assumption

/-- A source context-sensitive step is simulated by one embedded step. -/
private lemma sim_transform [Fintype A] [DecidableEq A]
    (g : CS_grammar A) (f : A ↪ T)
    {s₁ s₂ : List (symbol A g.nt)} (h : CS_transforms g s₁ s₂) :
    CS_transforms (grammar g f) (s₁.map liftSymbol) (s₂.map liftSymbol) := by
  obtain ⟨r, u, v, hr, rfl, rfl⟩ := h
  refine ⟨liftRule r, u.map liftSymbol, v.map liftSymbol, ?_, ?_, ?_⟩
  · exact List.mem_append_left _ (List.mem_map.mpr ⟨r, hr, rfl⟩)
  · simp [liftRule, List.map_append, liftSymbol, List.append_assoc]
  · simp [liftRule, List.map_append, List.append_assoc]

/-- A source derivation is simulated by the embedded grammar. -/
private lemma sim_derives [Fintype A] [DecidableEq A]
    (g : CS_grammar A) (f : A ↪ T)
    {s₁ s₂ : List (symbol A g.nt)} (h : CS_derives g s₁ s₂) :
    CS_derives (grammar g f) (s₁.map liftSymbol) (s₂.map liftSymbol) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail (sim_transform g f hstep)

/-- One private terminal can be exposed in arbitrary sentential context. -/
private lemma unlift_one [Fintype A] [DecidableEq A]
    (g : CS_grammar A) (f : A ↪ T) (a : A)
    (u v : List (symbol T (NT (A := A) g.nt))) :
    CS_transforms (grammar g f)
      (u ++ [.nonterminal (.terminal a)] ++ v)
      (u ++ [.terminal (f a)] ++ v) := by
  refine ⟨terminalRule (N := g.nt) f a, u, v, ?_, ?_, ?_⟩
  · apply List.mem_append_right
    exact List.mem_map.mpr ⟨a, by simp, rfl⟩
  · simp [terminalRule, List.append_assoc]
  · simp [terminalRule, List.append_assoc]

/-- Expose every private terminal in a word. -/
private lemma unlift_all [Fintype A] [DecidableEq A]
    (g : CS_grammar A) (f : A ↪ T) (w : List A) :
    CS_derives (grammar g f)
      (w.map fun a => symbol.nonterminal (NT.terminal a))
      ((w.map f).map symbol.terminal) := by
  induction w with
  | nil => exact Relation.ReflTransGen.refl
  | cons a w ih =>
      have hhead := unlift_one g f a []
        (w.map fun a => symbol.nonterminal (NT.terminal a))
      have htail := CS_deri_with_context [symbol.terminal (f a)] [] ih
      exact (Relation.ReflTransGen.single (by simpa using hhead)).trans (by simpa using htail)

/-- Forward language inclusion for terminal embeddings. -/
private lemma map_language_subset [Fintype A] [DecidableEq A]
    (g : CS_grammar A) (f : A ↪ T) :
    ∀ w, w ∈ Language.map f (CS_language g) → w ∈ CS_language (grammar g f) := by
  rintro w ⟨u, hu, rfl⟩
  have hsim := sim_derives g f hu
  have hunlift := unlift_all g f u
  have hunlift' : CS_derives (grammar g f)
      ((u.map symbol.terminal).map (@liftSymbol A T g.nt))
      ((u.map f).map symbol.terminal) := by
    simpa [liftSymbol, List.map_map] using hunlift
  change CS_derives (grammar g f)
    [symbol.nonterminal (grammar g f).initial]
    ((u.map f).map symbol.terminal)
  simpa [grammar, liftSymbol, List.map_map] using hsim.trans hunlift'

section Projection

variable [Nonempty A]

/-- Project an embedded sentential symbol to the source grammar.  Ambient terminals not in
the embedding's range may be sent to the arbitrary `invFun` default; the support invariant
below proves that no such terminal is reachable. -/
noncomputable def projectSymbol {N : Type} (f : A ↪ T) :
    symbol T (NT (A := A) N) → symbol A N
  | .terminal t => .terminal (Function.invFun f t)
  | .nonterminal (.source n) => .nonterminal n
  | .nonterminal (.terminal a) => .terminal a

private lemma project_liftSymbol {N : Type} (f : A ↪ T) (s : symbol A N) :
    projectSymbol f (liftSymbol (T := T) s) = s := by
  cases s <;> rfl

private lemma project_terminal_image {N : Type} (f : A ↪ T) (a : A) :
    projectSymbol (N := N) f (.terminal (f a)) = .terminal a := by
  simp [projectSymbol, Function.leftInverse_invFun f.injective a]

private lemma project_map_liftSymbol {N : Type} (f : A ↪ T)
    (s : List (symbol A N)) :
    (s.map (@liftSymbol A T N)).map (projectSymbol f) = s := by
  simp [List.map_map, Function.comp_def, project_liftSymbol]

/-- Every embedded step projects either to a source step or to equality. -/
private lemma project_transform [Fintype A] [DecidableEq A]
    (g : CS_grammar A) (f : A ↪ T)
    {s₁ s₂ : List (symbol T (grammar g f).nt)}
    (h : CS_transforms (grammar g f) s₁ s₂) :
    CS_derives g
      (s₁.map (projectSymbol f)) (s₂.map (projectSymbol f)) := by
  obtain ⟨r, u, v, hr, hs₁, hs₂⟩ := h
  simp only [grammar, List.mem_append, List.mem_map] at hr
  rcases hr with ⟨r₀, hr₀, rfl⟩ | ⟨a, _ha, rfl⟩
  · apply CS_deri_of_tran
    refine ⟨r₀, u.map (projectSymbol f), v.map (projectSymbol f), hr₀, ?_, ?_⟩
    · rw [hs₁]
      simp only [liftRule, List.map_append, List.map_cons, List.map_nil]
      rw [project_map_liftSymbol f r₀.context_left,
        project_map_liftSymbol f r₀.context_right]
      simp [projectSymbol, List.append_assoc]
    · rw [hs₂]
      simp only [liftRule, List.map_append]
      rw [project_map_liftSymbol f r₀.context_left,
        project_map_liftSymbol f r₀.output_string,
        project_map_liftSymbol f r₀.context_right]
  · rw [hs₁, hs₂]
    simp [terminalRule, List.map_append, projectSymbol,
      Function.leftInverse_invFun f.injective a, List.append_assoc]
    exact CS_deri_self

/-- Embedded derivations project to unrestricted derivations of the source grammar. -/
private lemma project_derives [Fintype A] [DecidableEq A]
    (g : CS_grammar A) (f : A ↪ T)
    {s₁ s₂ : List (symbol T (grammar g f).nt)}
    (h : CS_derives (grammar g f) s₁ s₂) :
    CS_derives g
      (s₁.map (projectSymbol f)) (s₂.map (projectSymbol f)) := by
  induction h with
  | refl => exact CS_deri_self
  | tail _ hstep ih =>
      exact CS_deri_of_deri_deri ih (project_transform g f hstep)

/-- All ambient terminals in a sentential form lie in the embedding's range. -/
def Supported {N : Type} (f : A ↪ T)
    (s : List (symbol T (NT (A := A) N))) : Prop :=
  ∀ t, symbol.terminal t ∈ s → ∃ a, f a = t

omit [Nonempty A] in
private lemma supported_initial [Fintype A] [DecidableEq A]
    (g : CS_grammar A) (f : A ↪ T) :
    Supported f [symbol.nonterminal (grammar g f).initial] := by
  intro t ht
  simp [grammar] at ht

omit [Nonempty A] in
private lemma supported_transform [Fintype A] [DecidableEq A]
    (g : CS_grammar A) (f : A ↪ T)
    {s₁ s₂ : List (symbol T (grammar g f).nt)}
    (hs : Supported f s₁) (h : CS_transforms (grammar g f) s₁ s₂) :
    Supported f s₂ := by
  obtain ⟨r, u, v, hr, hs₁, hs₂⟩ := h
  simp only [grammar, List.mem_append, List.mem_map] at hr
  rcases hr with ⟨r₀, _hr₀, rfl⟩ | ⟨a, _ha, rfl⟩
  · intro t ht
    have hnot : ∀ l : List (symbol A g.nt),
        symbol.terminal t ∉ l.map (@liftSymbol A T g.nt) := by
      intro l hmem
      rw [List.mem_map] at hmem
      obtain ⟨s, _hs, heq⟩ := hmem
      cases s <;> simp [liftSymbol] at heq
    rw [hs₂] at ht
    simp only [liftRule, List.mem_append] at ht
    have htuv : symbol.terminal t ∈ u ∨ symbol.terminal t ∈ v := by
      rcases ht with (((hu | hcl) | hout) | hcr) | hv
      · exact Or.inl hu
      · exact (hnot r₀.context_left hcl).elim
      · exact (hnot r₀.output_string hout).elim
      · exact (hnot r₀.context_right hcr).elim
      · exact Or.inr hv
    apply hs t
    rw [hs₁]
    rcases htuv with hu | hv
    · simp [liftRule, List.mem_append, hu]
    · simp [liftRule, List.mem_append, hv]
  · intro t ht
    rw [hs₂] at ht
    simp [terminalRule, List.mem_append] at ht
    rcases ht with ht | rfl | ht
    · apply hs t
      rw [hs₁]
      simp [terminalRule, List.mem_append, ht]
    · exact ⟨a, rfl⟩
    · apply hs t
      rw [hs₁]
      simp [terminalRule, List.mem_append, ht]

omit [Nonempty A] in
private lemma supported_derives [Fintype A] [DecidableEq A]
    (g : CS_grammar A) (f : A ↪ T)
    {s : List (symbol T (grammar g f).nt)}
    (h : CS_derives (grammar g f)
      [symbol.nonterminal (grammar g f).initial] s) :
    Supported f s := by
  induction h with
  | refl => exact supported_initial g f
  | tail _ hstep ih => exact supported_transform g f ih hstep

/-- Reverse language inclusion for terminal embeddings. -/
private lemma language_subset_map [Fintype A] [DecidableEq A]
    (g : CS_grammar A) (f : A ↪ T) :
    ∀ w, w ∈ CS_language (grammar g f) → w ∈ Language.map f (CS_language g) := by
  intro w hw
  let u := w.map (Function.invFun f)
  have hsupp := supported_derives g f hw
  have hleft : u.map f = w := by
    simp only [u, List.map_map]
    calc
      w.map (f ∘ Function.invFun f) = w.map id :=
        List.map_congr_left (by
          intro t ht
          obtain ⟨a, rfl⟩ := hsupp t (List.mem_map.mpr ⟨t, ht, rfl⟩)
          exact congrArg f (Function.leftInverse_invFun f.injective a))
      _ = w := List.map_id w
  refine ⟨u, ?_, hleft⟩
  have hproj := project_derives g f hw
  change CS_derives g [symbol.nonterminal g.initial] (u.map symbol.terminal)
  simpa [grammar, u, projectSymbol, List.map_map] using hproj

end Projection

/-- Embedding a finite source terminal alphabet along an injection produces exactly the
language image, while the target terminal type remains completely arbitrary. -/
theorem language_eq_map [Fintype A] [DecidableEq A] [Nonempty A]
    (g : CS_grammar A) (f : A ↪ T) :
    CS_language (grammar g f) = Language.map f (CS_language g) := by
  funext w
  apply propext
  constructor
  · exact language_subset_map g f w
  · exact map_language_subset g f w

end CSGTerminalEmbedding

variable {T : Type}

/-- A non-contracting grammar cannot generate the empty word. -/
private lemma nil_not_mem_of_noncontracting_language {L : Language T}
    (hL : is_noncontracting L) : [] ∉ L := by
  obtain ⟨g, hnc, hlang⟩ := hL
  intro hnil
  have hder : grammar_derives g [symbol.nonterminal g.initial] [] := by
    simpa [← hlang, grammar_language, grammar_generates] using hnil
  have hlen :
      ([symbol.nonterminal g.initial] : List (symbol T g.nt)).length ≤
        ([] : List (symbol T g.nt)).length := by
    have hmono : ∀ {x y : List (symbol T g.nt)}, grammar_derives g x y →
        x.length ≤ y.length := by
      intro x y hxy
      induction hxy with
      | refl => exact le_rfl
      | tail _ hstep ih =>
          exact le_trans ih (noncontracting_transforms_length_le g hnc hstep)
    exact hmono hder
  simp at hlen

/-- Over a finite terminal type, Kuroda--Myhill supplies an equivalent non-erasing
context-preserving grammar for every non-contracting grammar language. -/
private theorem is_CS_via_csg_of_is_noncontracting_finite
    {A : Type} [Fintype A] [DecidableEq A] {L : Language A}
    (hL : is_noncontracting L) : is_CS_via_csg L := by
  have hpos : is_LBA_pos L :=
    is_LBA_pos_of_isCS_not_nil (is_CS_of_is_noncontracting hL)
      (nil_not_mem_of_noncontracting_language hL)
  obtain ⟨Γ, Λ, hΓ, hΛ, hdΓ, hdΛ, M, hM⟩ := hpos
  letI := hΓ
  letI := hΛ
  letI := hdΓ
  letI := hdΛ
  let emb : A ↪ Option (A ⊕ Γ) :=
    ⟨fun a => some (Sum.inl a), fun _ _ h => by simpa using h⟩
  refine ⟨MyhillConstruction.myhillGrammar M emb, ?_⟩
  exact (myhill_language_eq M emb).trans hM

/-- **Non-contracting implies non-erasing context-preserving**, for an arbitrary terminal
type.  No finiteness hypothesis is imposed on the ambient alphabet; only the finite support
actually occurring in the source grammar is used internally. -/
public theorem is_CS_via_csg_of_is_noncontracting {L : Language T}
    (hL : is_noncontracting L) : is_CS_via_csg L := by
  classical
  obtain ⟨S, L', hCS', hmap⟩ :=
    is_CS_exists_finiteAlphabet_CS_image (is_CS_of_is_noncontracting hL)
  have hnil' : [] ∉ L' := by
    intro hnil
    have : [] ∈ Language.map (fun t : {t : T // t ∈ S} => t.1) L' :=
      ⟨[], hnil, rfl⟩
    rw [hmap] at this
    exact nil_not_mem_of_noncontracting_language hL this
  have hnc' : is_noncontracting L' := by
    obtain ⟨g, hg, hlang⟩ := hCS'
    obtain ⟨g₀, _hfin, hnc, hcore⟩ := exists_noncontracting_offEmpty_of_CS g hg
    refine ⟨g₀, hnc, ?_⟩
    rw [hcore, hlang]
    exact Set.diff_singleton_eq_self hnil'
  let f : {t : T // t ∈ S} ↪ T :=
    ⟨Subtype.val, Subtype.val_injective⟩
  cases isEmpty_or_nonempty {t : T // t ∈ S} with
  | inl hempty =>
      letI := hempty
      let g : CS_grammar T :=
        { nt := Unit
          initial := ()
          rules := []
          output_nonempty := by simp }
      refine ⟨g, ?_⟩
      ext w
      constructor
      · intro hw
        change CS_derives g [symbol.nonterminal ()] (w.map symbol.terminal) at hw
        rcases CS_tran_or_id_of_deri hw with heq | ⟨s, hstep, _⟩
        · cases w <;> simp at heq
        · obtain ⟨r, u, v, hr, _hs, _ht⟩ := hstep
          simp [g] at hr
      · intro hw
        rw [← hmap] at hw
        obtain ⟨u, hu, _humap⟩ := hw
        have hu_nil : u = [] := by
          cases u with
          | nil => rfl
          | cons a _ => exact isEmptyElim a
        subst u
        exact (hnil' hu).elim
  | inr hnonempty =>
      letI := hnonempty
      obtain ⟨g, hg⟩ := is_CS_via_csg_of_is_noncontracting_finite hnc'
      refine ⟨CSGTerminalEmbedding.grammar g f, ?_⟩
      calc
        CS_language (CSGTerminalEmbedding.grammar g f) =
            Language.map f (CS_language g) :=
          CSGTerminalEmbedding.language_eq_map g f
        _ = Language.map f L' := congrArg (Language.map f) hg
        _ = L := by simpa [f] using hmap

/-- The classical equivalence between non-contracting unrestricted grammars and non-erasing
context-preserving grammars, uniformly over every terminal type. -/
public theorem is_noncontracting_iff_is_CS_via_csg {L : Language T} :
    is_noncontracting L ↔ is_CS_via_csg L := by
  constructor
  · exact is_CS_via_csg_of_is_noncontracting
  · rintro ⟨g, rfl⟩
    exact ⟨grammar_of_csg g, CS_is_noncontracting g,
      (CS_language_eq_grammar_language g).symm⟩

end
