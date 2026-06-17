module

public import Langlib.Classes.Indexed.Definition
public import Langlib.Classes.Indexed.Closure.Homomorphism
public import Mathlib.Data.Finset.Basic
@[expose]
public section

/-! # Finite terminal support for indexed languages

Every indexed grammar has finitely many rules, and every rule has a finite right-hand side.
Therefore each generated word uses only terminals from a finite set syntactically present in
the grammar. This file packages that fact as a finite-alphabet restriction theorem.
-/

namespace IndexedGrammarFiniteAlphabet

variable {T : Type}

/-- The terminals appearing in a right-hand-side symbol. -/
def rhsSymbolTerminals {N F : Type} : IRhsSymbol T N F → List T
  | IRhsSymbol.terminal t => [t]
  | IRhsSymbol.nonterminal _ _ => []

/-- The terminals appearing in an indexed production rule. -/
def ruleTerminals {N F : Type} (r : IRule T N F) : List T :=
  r.rhs.flatMap rhsSymbolTerminals

/-- The finite terminal support syntactically mentioned by an indexed grammar. -/
def grammarTerminalSet [DecidableEq T] (g : IndexedGrammar T) : Finset T :=
  (g.rules.flatMap ruleTerminals).toFinset

def rhsSymbolSupported {N F : Type} (S : Finset T) : IRhsSymbol T N F → Prop
  | IRhsSymbol.terminal t => t ∈ S
  | IRhsSymbol.nonterminal _ _ => True

def rhsSupported {N F : Type} (S : Finset T) (rhs : List (IRhsSymbol T N F)) : Prop :=
  ∀ s ∈ rhs, rhsSymbolSupported S s

def isymSupported {g : IndexedGrammar T} (S : Finset T) : g.ISym → Prop
  | IndexedGrammar.ISym.terminal t => t ∈ S
  | IndexedGrammar.ISym.indexed _ _ => True

def sententialSupported {g : IndexedGrammar T} (S : Finset T) (w : List g.ISym) : Prop :=
  ∀ s ∈ w, isymSupported S s

def restrictRhsSymbolOfSupported {N F : Type} (S : Finset T)
    (s : IRhsSymbol T N F) (h : rhsSymbolSupported S s) :
    IRhsSymbol {t : T // t ∈ S} N F :=
  match s with
  | IRhsSymbol.terminal t => IRhsSymbol.terminal ⟨t, h⟩
  | IRhsSymbol.nonterminal n push => IRhsSymbol.nonterminal n push

def restrictRhsOfSupported {N F : Type} (S : Finset T)
    (rhs : List (IRhsSymbol T N F)) (h : rhsSupported S rhs) :
    List (IRhsSymbol {t : T // t ∈ S} N F) :=
  rhs.attach.map fun s => restrictRhsSymbolOfSupported S s.1 (h s.1 s.2)

def unrestrictRhsSymbol {S : Finset T} {N F : Type} :
    IRhsSymbol {t : T // t ∈ S} N F → IRhsSymbol T N F
  | IRhsSymbol.terminal t => IRhsSymbol.terminal t.1
  | IRhsSymbol.nonterminal n push => IRhsSymbol.nonterminal n push

private lemma unrestrict_restrictRhsSymbol {N F : Type} (S : Finset T)
    (s : IRhsSymbol T N F) (h : rhsSymbolSupported S s) :
    unrestrictRhsSymbol (restrictRhsSymbolOfSupported S s h) = s := by
  cases s <;> rfl

private lemma unrestrictRhsSymbol_injective {S : Finset T} {N F : Type} :
    Function.Injective (@unrestrictRhsSymbol T S N F) := by
  intro a b h
  cases a <;> cases b <;> simp [unrestrictRhsSymbol] at h ⊢
  all_goals assumption

private lemma unrestrict_restrictRhsOfSupported {N F : Type} (S : Finset T)
    (rhs : List (IRhsSymbol T N F)) (h : rhsSupported S rhs) :
    (restrictRhsOfSupported S rhs h).map unrestrictRhsSymbol = rhs := by
  unfold restrictRhsOfSupported
  rw [List.map_map]
  simp [Function.comp_def, unrestrict_restrictRhsSymbol]

private lemma terminal_mem_ruleTerminals {N F : Type}
    {r : IRule T N F} {t : T} (ht : IRhsSymbol.terminal t ∈ r.rhs) :
    t ∈ ruleTerminals r := by
  unfold ruleTerminals
  exact List.mem_flatMap.mpr ⟨IRhsSymbol.terminal t, ht, by simp [rhsSymbolTerminals]⟩

private lemma terminal_mem_grammarTerminalSet [DecidableEq T] {g : IndexedGrammar T}
    {r : IRule T g.nt g.flag} (hr : r ∈ g.rules) {t : T}
    (ht : IRhsSymbol.terminal t ∈ r.rhs) :
    t ∈ grammarTerminalSet g := by
  unfold grammarTerminalSet
  rw [List.mem_toFinset]
  exact List.mem_flatMap.mpr ⟨r, hr, terminal_mem_ruleTerminals ht⟩

lemma rule_rhs_supported [DecidableEq T] {g : IndexedGrammar T}
    {r : IRule T g.nt g.flag} (hr : r ∈ g.rules) :
    rhsSupported (grammarTerminalSet g) r.rhs := by
  intro s hs
  cases s with
  | terminal t => exact terminal_mem_grammarTerminalSet hr hs
  | nonterminal n push => trivial

def restrictRule [DecidableEq T] (g : IndexedGrammar T)
    (r : IRule T g.nt g.flag) (hr : r ∈ g.rules) :
    IRule {t : T // t ∈ grammarTerminalSet g} g.nt g.flag where
  lhs := r.lhs
  consume := r.consume
  rhs := restrictRhsOfSupported (grammarTerminalSet g) r.rhs (rule_rhs_supported hr)

private lemma restrictRhsOfSupported_ne_nil {N F : Type} (S : Finset T)
    {rhs : List (IRhsSymbol T N F)} (h : rhsSupported S rhs) (hne : rhs ≠ []) :
    restrictRhsOfSupported S rhs h ≠ [] := by
  intro hnil
  have hmap := congrArg (List.map (@unrestrictRhsSymbol T S N F)) hnil
  rw [unrestrict_restrictRhsOfSupported] at hmap
  exact hne hmap

/-- The same indexed grammar, with terminals restricted to the finite set appearing in rules. -/
def finiteAlphabetGrammar [DecidableEq T] (g : IndexedGrammar T) :
    IndexedGrammar {t : T // t ∈ grammarTerminalSet g} where
  nt := g.nt
  flag := g.flag
  initial := g.initial
  rules := g.rules.attach.map fun r => restrictRule g r.1 r.2

theorem finiteAlphabetGrammar_noEpsilon [DecidableEq T] (g : IndexedGrammar T)
    (hne : g.NoEpsilon') :
    (finiteAlphabetGrammar g).NoEpsilon' := by
  intro r hr
  unfold finiteAlphabetGrammar at hr
  obtain ⟨r₀, _hr₀, rfl⟩ := List.mem_map.mp hr
  exact restrictRhsOfSupported_ne_nil (grammarTerminalSet g) (rule_rhs_supported r₀.2)
    (hne r₀.1 r₀.2)

theorem restrictRule_isNF [DecidableEq T] {g : IndexedGrammar T} [DecidableEq g.nt]
    {r : IRule T g.nt g.flag} (hr : r ∈ g.rules)
    (hNF : IndexedGrammar.IRule.IsNF r g.initial) :
    IndexedGrammar.IRule.IsNF (restrictRule g r hr) g.initial := by
  rcases hNF with hbin | hpop | hpush | hterm
  · rcases hbin with ⟨hc, B, C, hrhs, hB, hC⟩
    left
    refine ⟨by simp [restrictRule, hc], B, C, ?_, hB, hC⟩
    apply List.map_injective_iff.mpr unrestrictRhsSymbol_injective
    simp [restrictRule, unrestrict_restrictRhsOfSupported, unrestrictRhsSymbol, hrhs]
  · rcases hpop with ⟨f, hc, B, hrhs, hB⟩
    right
    left
    refine ⟨f, by simp [restrictRule, hc], B, ?_, hB⟩
    apply List.map_injective_iff.mpr unrestrictRhsSymbol_injective
    simp [restrictRule, unrestrict_restrictRhsOfSupported, unrestrictRhsSymbol, hrhs]
  · rcases hpush with ⟨hc, B, f, hrhs, hB⟩
    right
    right
    left
    refine ⟨by simp [restrictRule, hc], B, f, ?_, hB⟩
    apply List.map_injective_iff.mpr unrestrictRhsSymbol_injective
    simp [restrictRule, unrestrict_restrictRhsOfSupported, unrestrictRhsSymbol, hrhs]
  · rcases hterm with ⟨hc, a, hrhs⟩
    right
    right
    right
    refine ⟨by simp [restrictRule, hc], ⟨a, ?_⟩, ?_⟩
    · exact terminal_mem_grammarTerminalSet hr (by
        rw [hrhs]
        simp)
    · apply List.map_injective_iff.mpr unrestrictRhsSymbol_injective
      simp [restrictRule, unrestrict_restrictRhsOfSupported, unrestrictRhsSymbol, hrhs]

theorem finiteAlphabetGrammar_isNormalForm [DecidableEq T] (g : IndexedGrammar T)
    [DecidableEq g.nt] (hNF : g.IsNormalForm) :
    (finiteAlphabetGrammar g).IsNormalForm := by
  intro r hr
  unfold finiteAlphabetGrammar at hr
  obtain ⟨r₀, _hr₀, rfl⟩ := List.mem_map.mp hr
  exact restrictRule_isNF r₀.2 (hNF r₀.1 r₀.2)

def unrestrictISym [DecidableEq T] (g : IndexedGrammar T) :
    (finiteAlphabetGrammar g).ISym → g.ISym
  | IndexedGrammar.ISym.terminal t => IndexedGrammar.ISym.terminal t.1
  | IndexedGrammar.ISym.indexed n σ => IndexedGrammar.ISym.indexed n σ

private lemma unrestrictISym_injective [DecidableEq T] (g : IndexedGrammar T) :
    Function.Injective (unrestrictISym g) := by
  intro a b h
  cases a <;> cases b <;> simp [unrestrictISym] at h ⊢
  all_goals assumption

def restrictISymOfSupported [DecidableEq T] (g : IndexedGrammar T)
    (s : g.ISym) (h : isymSupported (grammarTerminalSet g) s) :
    (finiteAlphabetGrammar g).ISym :=
  match s with
  | IndexedGrammar.ISym.terminal t => IndexedGrammar.ISym.terminal ⟨t, h⟩
  | IndexedGrammar.ISym.indexed n σ => IndexedGrammar.ISym.indexed n σ

def restrictStringOfSupported [DecidableEq T] (g : IndexedGrammar T)
    (w : List g.ISym) (h : sententialSupported (grammarTerminalSet g) w) :
    List (finiteAlphabetGrammar g).ISym :=
  w.attach.map fun s => restrictISymOfSupported g s.1 (h s.1 s.2)

private lemma unrestrict_restrictISym [DecidableEq T] (g : IndexedGrammar T)
    (s : g.ISym) (h : isymSupported (grammarTerminalSet g) s) :
    unrestrictISym g (restrictISymOfSupported g s h) = s := by
  cases s <;> rfl

private lemma unrestrict_restrictStringOfSupported [DecidableEq T] (g : IndexedGrammar T)
    (w : List g.ISym) (h : sententialSupported (grammarTerminalSet g) w) :
    (restrictStringOfSupported g w h).map (unrestrictISym g) = w := by
  unfold restrictStringOfSupported
  rw [List.map_map]
  simp [Function.comp_def, unrestrict_restrictISym]

private lemma restrictStringOfSupported_terminal_values [DecidableEq T] (g : IndexedGrammar T)
    (w : List {t : T // t ∈ grammarTerminalSet g})
    (h : sententialSupported (grammarTerminalSet g)
      ((w.map (fun t => t.1)).map
        (fun t => (IndexedGrammar.ISym.terminal t : g.ISym)))) :
    restrictStringOfSupported g
        ((w.map (fun t => t.1)).map
          (fun t => (IndexedGrammar.ISym.terminal t : g.ISym))) h =
      w.map (fun t => (IndexedGrammar.ISym.terminal t : (finiteAlphabetGrammar g).ISym)) := by
  apply List.map_injective_iff.mpr (unrestrictISym_injective g)
  simp [unrestrict_restrictStringOfSupported, unrestrictISym, List.map_map]

private lemma terminal_mem_expandRhs {g : IndexedGrammar T}
    {rhs : List (IRhsSymbol T g.nt g.flag)} {σ : List g.flag} {t : T}
    (h : (IndexedGrammar.ISym.terminal t : g.ISym) ∈ g.expandRhs rhs σ) :
    IRhsSymbol.terminal t ∈ rhs := by
  unfold IndexedGrammar.expandRhs at h
  rw [List.mem_map] at h
  obtain ⟨s, hs, hs_eq⟩ := h
  cases s with
  | terminal t₀ =>
      simp at hs_eq
      subst t₀
      exact hs
  | nonterminal n push =>
      cases push <;> simp at hs_eq

private lemma transforms_supported [DecidableEq T] (g : IndexedGrammar T)
    {w₁ w₂ : List g.ISym}
    (h₁ : sententialSupported (grammarTerminalSet g) w₁)
    (h : g.Transforms w₁ w₂) :
    sententialSupported (grammarTerminalSet g) w₂ := by
  rcases h with ⟨r, u, v, σ, hr, hw₁, hw₂⟩
  subst w₂
  intro s hs
  rcases List.mem_append.mp hs with hleft | hv
  · rcases List.mem_append.mp hleft with hu | hmid
    · cases hc : r.consume with
      | none =>
          rw [hc] at hw₁
          exact h₁ s (by rw [hw₁]; simp [hu])
      | some f =>
          rw [hc] at hw₁
          exact h₁ s (by rw [hw₁]; simp [hu])
    · cases s with
      | indexed n stack => trivial
      | terminal t =>
          exact terminal_mem_grammarTerminalSet hr (terminal_mem_expandRhs hmid)
  · cases hc : r.consume with
    | none =>
        rw [hc] at hw₁
        exact h₁ s (by rw [hw₁]; simp [hv])
    | some f =>
        rw [hc] at hw₁
        exact h₁ s (by rw [hw₁]; simp [hv])

theorem derives_supported_of_supported [DecidableEq T] (g : IndexedGrammar T)
    {w₁ w₂ : List g.ISym}
    (h₁ : sententialSupported (grammarTerminalSet g) w₁)
    (h : g.Derives w₁ w₂) :
    sententialSupported (grammarTerminalSet g) w₂ := by
  induction h with
  | refl => exact h₁
  | tail _ hstep ih => exact transforms_supported g ih hstep

/-- A derivation from the start symbol mentions only terminals syntactically present in
the indexed grammar's rules. -/
theorem derives_supported [DecidableEq T] (g : IndexedGrammar T)
    {w : List g.ISym} (h : g.Derives [IndexedGrammar.ISym.indexed g.initial []] w) :
    sententialSupported (grammarTerminalSet g) w :=
  derives_supported_of_supported g (by
    intro s hs
    simp at hs
    subst s
    trivial) h

/-- Every word generated by an indexed grammar is supported by the finite terminal set
occurring in its rules. -/
theorem language_supported [DecidableEq T] (g : IndexedGrammar T)
    {w : List T} (hw : w ∈ g.Language) :
    ∀ t ∈ w, t ∈ grammarTerminalSet g := by
  intro t ht
  have hder : g.Derives [IndexedGrammar.ISym.indexed g.initial []]
      (w.map IndexedGrammar.ISym.terminal) := by
    simpa [IndexedGrammar.Language, IndexedGrammar.Generates] using hw
  have hsupp := derives_supported g hder
  exact hsupp (IndexedGrammar.ISym.terminal t) (List.mem_map.mpr ⟨t, ht, rfl⟩)

private lemma expandRhs_unrestrictRhsSymbol [DecidableEq T] (g : IndexedGrammar T)
    (rhs : List (IRhsSymbol {t : T // t ∈ grammarTerminalSet g} g.nt g.flag))
    (σ : List g.flag) :
    ((finiteAlphabetGrammar g).expandRhs rhs σ).map (unrestrictISym g) =
      g.expandRhs (rhs.map unrestrictRhsSymbol) σ := by
  unfold IndexedGrammar.expandRhs
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro s _hs
  cases s with
  | terminal t => rfl
  | nonterminal n push =>
      cases push <;> rfl

private lemma unrestrict_expandRhs_restrictRule [DecidableEq T] (g : IndexedGrammar T)
    (r : IRule T g.nt g.flag) (hr : r ∈ g.rules) (σ : List g.flag) :
    ((finiteAlphabetGrammar g).expandRhs (restrictRule g r hr).rhs σ).map (unrestrictISym g) =
      g.expandRhs r.rhs σ := by
  rw [expandRhs_unrestrictRhsSymbol]
  simp [restrictRule, unrestrict_restrictRhsOfSupported]

private theorem finiteAlphabetGrammar_transforms_unrestrict [DecidableEq T]
    (g : IndexedGrammar T)
    {w₁ w₂ : List (finiteAlphabetGrammar g).ISym}
    (h : (finiteAlphabetGrammar g).Transforms w₁ w₂) :
    g.Transforms (w₁.map (unrestrictISym g)) (w₂.map (unrestrictISym g)) := by
  rcases h with ⟨r, u, v, σ, hr, hw₁, hw₂⟩
  obtain ⟨r₀, _hr₀, rfl⟩ := List.mem_map.mp hr
  simp [restrictRule] at hw₁
  refine ⟨r₀.1, u.map (unrestrictISym g), v.map (unrestrictISym g), σ, r₀.2, ?_, ?_⟩
  · cases hc : r₀.1.consume with
    | none =>
        rw [hc] at hw₁
        have hw₁' := congrArg (List.map (unrestrictISym g)) hw₁
        simpa [List.map_append, restrictRule, unrestrictISym, hc] using hw₁'
    | some f =>
        rw [hc] at hw₁
        have hw₁' := congrArg (List.map (unrestrictISym g)) hw₁
        simpa [List.map_append, restrictRule, unrestrictISym, hc] using hw₁'
  · have hw₂' := congrArg (List.map (unrestrictISym g)) hw₂
    simpa [List.map_append, List.append_assoc, unrestrict_expandRhs_restrictRule] using hw₂'

private theorem finiteAlphabetGrammar_derives_unrestrict [DecidableEq T]
    (g : IndexedGrammar T)
    {w₁ w₂ : List (finiteAlphabetGrammar g).ISym}
    (h : (finiteAlphabetGrammar g).Derives w₁ w₂) :
    g.Derives (w₁.map (unrestrictISym g)) (w₂.map (unrestrictISym g)) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail (finiteAlphabetGrammar_transforms_unrestrict g hstep)

private theorem grammar_transforms_restrict [DecidableEq T] (g : IndexedGrammar T)
    {w₁ w₂ : List g.ISym}
    (h₁ : sententialSupported (grammarTerminalSet g) w₁)
    (h : g.Transforms w₁ w₂) :
    (finiteAlphabetGrammar g).Transforms
      (restrictStringOfSupported g w₁ h₁)
      (restrictStringOfSupported g w₂ (transforms_supported g h₁ h)) := by
  rcases h with ⟨r, u, v, σ, hr, hw₁, hw₂⟩
  subst w₂
  let hu : sententialSupported (grammarTerminalSet g) u := by
    intro s hs
    cases hc : r.consume with
    | none =>
        rw [hc] at hw₁
        exact h₁ s (by rw [hw₁]; simp [hs])
    | some f =>
        rw [hc] at hw₁
        exact h₁ s (by rw [hw₁]; simp [hs])
  let hv : sententialSupported (grammarTerminalSet g) v := by
    intro s hs
    cases hc : r.consume with
    | none =>
        rw [hc] at hw₁
        exact h₁ s (by rw [hw₁]; simp [hs])
    | some f =>
        rw [hc] at hw₁
        exact h₁ s (by rw [hw₁]; simp [hs])
  refine ⟨restrictRule g r hr, restrictStringOfSupported g u hu,
    restrictStringOfSupported g v hv, σ, ?_, ?_, ?_⟩
  · unfold finiteAlphabetGrammar
    exact List.mem_map.mpr ⟨⟨r, hr⟩, by simp, rfl⟩
  · cases hc : r.consume with
    | none =>
        simp only [restrictRule, hc]
        apply List.map_injective_iff.mpr (unrestrictISym_injective g)
        rw [hc] at hw₁
        simp [List.map_append, unrestrict_restrictStringOfSupported, unrestrictISym, hw₁]
    | some f =>
        simp only [restrictRule, hc]
        apply List.map_injective_iff.mpr (unrestrictISym_injective g)
        rw [hc] at hw₁
        simp [List.map_append, unrestrict_restrictStringOfSupported, unrestrictISym, hw₁]
  · apply List.map_injective_iff.mpr (unrestrictISym_injective g)
    simp [List.map_append, unrestrict_restrictStringOfSupported,
      unrestrict_expandRhs_restrictRule, List.append_assoc]

private theorem grammar_derives_restrict [DecidableEq T] (g : IndexedGrammar T)
    {w₁ w₂ : List g.ISym}
    (h₁ : sententialSupported (grammarTerminalSet g) w₁)
    (h : g.Derives w₁ w₂) :
    (finiteAlphabetGrammar g).Derives
      (restrictStringOfSupported g w₁ h₁)
      (restrictStringOfSupported g w₂ (derives_supported_of_supported g h₁ h)) := by
  induction h with
  | refl =>
      convert (Relation.ReflTransGen.refl :
        (finiteAlphabetGrammar g).Derives
          (restrictStringOfSupported g w₁ h₁)
          (restrictStringOfSupported g w₁ h₁)) using 1
  | tail hprev hstep ih =>
      let hmid := derives_supported_of_supported g h₁ hprev
      have hstep' := grammar_transforms_restrict g hmid hstep
      convert ih.tail hstep' using 1

/-- Restrict a language to words over a finite terminal set. -/
def finiteAlphabetRestriction (S : Finset T) (L : Language T) :
    Language {t : T // t ∈ S} :=
  fun w => w.map (fun t => t.1) ∈ L

/-- The restricted indexed grammar generates exactly the finite-alphabet restriction. -/
theorem grammar_language_finiteAlphabetGrammar [DecidableEq T] (g : IndexedGrammar T) :
    (finiteAlphabetGrammar g).Language =
      finiteAlphabetRestriction (grammarTerminalSet g) g.Language := by
  ext w
  constructor
  · intro hw
    change (finiteAlphabetGrammar g).Derives
      [IndexedGrammar.ISym.indexed g.initial []] (w.map IndexedGrammar.ISym.terminal) at hw
    have hder := finiteAlphabetGrammar_derives_unrestrict g hw
    change (w.map (fun t => t.1)) ∈ g.Language
    simpa [IndexedGrammar.Language, IndexedGrammar.Generates, finiteAlphabetGrammar,
      unrestrictISym, List.map_map] using hder
  · intro hw
    change (w.map (fun t => t.1)) ∈ g.Language at hw
    have hstart :
        sententialSupported (grammarTerminalSet g) [IndexedGrammar.ISym.indexed g.initial []] := by
      intro s hs
      simp at hs
      subst s
      trivial
    have hder : g.Derives [IndexedGrammar.ISym.indexed g.initial []]
        ((w.map (fun t => t.1)).map IndexedGrammar.ISym.terminal) := by
      simpa [IndexedGrammar.Language, IndexedGrammar.Generates] using hw
    have hlift := grammar_derives_restrict g hstart hder
    change (finiteAlphabetGrammar g).Derives [IndexedGrammar.ISym.indexed g.initial []]
      (w.map IndexedGrammar.ISym.terminal)
    convert hlift using 1
    exact (restrictStringOfSupported_terminal_values g w _).symm

theorem finiteAlphabetRestriction_is_Indexed [DecidableEq T] (g : IndexedGrammar T) :
    is_Indexed (finiteAlphabetRestriction (grammarTerminalSet g) g.Language) :=
  ⟨finiteAlphabetGrammar g, grammar_language_finiteAlphabetGrammar g⟩

theorem finiteAlphabetRestriction_is_Indexed_noEpsilon [DecidableEq T]
    (g : IndexedGrammar T) (hne : g.NoEpsilon') :
    is_Indexed_noEpsilon (finiteAlphabetRestriction (grammarTerminalSet g) g.Language) :=
  ⟨finiteAlphabetGrammar g, finiteAlphabetGrammar_noEpsilon g hne,
    grammar_language_finiteAlphabetGrammar g⟩

/-- Any indexed grammar language is an image of an indexed language over a finite subtype
of its terminal alphabet. -/
theorem indexed_language_finiteAlphabet_Indexed_image [DecidableEq T] (g : IndexedGrammar T) :
    ∃ (S : Finset T) (L' : Language {t : T // t ∈ S}),
      is_Indexed L' ∧ Language.map (fun t : {t : T // t ∈ S} => t.1) L' = g.Language := by
  refine ⟨grammarTerminalSet g, finiteAlphabetRestriction (grammarTerminalSet g) g.Language,
    finiteAlphabetRestriction_is_Indexed g, ?_⟩
  ext w
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact hu
  · intro hw
    let u : List {t : T // t ∈ grammarTerminalSet g} :=
      w.attach.map fun t => ⟨t.1, language_supported g hw t.1 t.2⟩
    have hmap : u.map (fun t : {t : T // t ∈ grammarTerminalSet g} => t.1) = w := by
      simp [u]
    refine ⟨u, ?_, hmap⟩
    change u.map (fun t : {t : T // t ∈ grammarTerminalSet g} => t.1) ∈ g.Language
    rw [hmap]
    exact hw

/-- Any ε-free indexed grammar language is an image of an ε-free indexed language over a
finite subtype of its terminal alphabet. -/
theorem indexed_language_finiteAlphabet_Indexed_noEpsilon_image [DecidableEq T]
    (g : IndexedGrammar T) (hne : g.NoEpsilon') :
    ∃ (S : Finset T) (L' : Language {t : T // t ∈ S}),
      is_Indexed_noEpsilon L' ∧
        Language.map (fun t : {t : T // t ∈ S} => t.1) L' = g.Language := by
  refine ⟨grammarTerminalSet g, finiteAlphabetRestriction (grammarTerminalSet g) g.Language,
    finiteAlphabetRestriction_is_Indexed_noEpsilon g hne, ?_⟩
  ext w
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact hu
  · intro hw
    let u : List {t : T // t ∈ grammarTerminalSet g} :=
      w.attach.map fun t => ⟨t.1, language_supported g hw t.1 t.2⟩
    have hmap : u.map (fun t : {t : T // t ∈ grammarTerminalSet g} => t.1) = w := by
      simp [u]
    refine ⟨u, ?_, hmap⟩
    change u.map (fun t : {t : T // t ∈ grammarTerminalSet g} => t.1) ∈ g.Language
    rw [hmap]
    exact hw

end IndexedGrammarFiniteAlphabet

open IndexedGrammarFiniteAlphabet

variable {T : Type}

/-- Every indexed language is equivalent to an indexed language over a finite terminal subtype. -/
public theorem is_Indexed_exists_finiteAlphabet_Indexed_image {L : Language T}
    (hL : is_Indexed L) :
    ∃ (S : Finset T) (L' : Language {t : T // t ∈ S}),
      is_Indexed L' ∧ Language.map (fun t : {t : T // t ∈ S} => t.1) L' = L := by
  classical
  obtain ⟨g, hlang⟩ := hL
  obtain ⟨S, L', hIndexed, hS⟩ := indexed_language_finiteAlphabet_Indexed_image g
  exact ⟨S, L', hIndexed, hS.trans hlang⟩

/-- Every indexed language is equivalent to an indexed language over some finite terminal
alphabet. The finite alphabet is represented as a type carrying `Fintype` and `DecidableEq`,
together with a terminal map into the original alphabet. -/
public theorem is_Indexed_exists_fintype_alphabet_Indexed_image {L : Language T}
    (hL : is_Indexed L) :
    ∃ (A : Type) (_ : Fintype A) (_ : DecidableEq A) (L' : Language A) (f : A → T),
      is_Indexed L' ∧ Language.map f L' = L := by
  classical
  obtain ⟨S, L', hIndexed, hmap⟩ :=
    is_Indexed_exists_finiteAlphabet_Indexed_image (L := L) hL
  refine ⟨{t : T // t ∈ S}, ?_, ?_, L', (fun t => t.1), hIndexed, hmap⟩
  · infer_instance
  · infer_instance

/-- Every ε-free indexed language is equivalent to an ε-free indexed language over a finite
terminal subtype. -/
public theorem is_Indexed_noEpsilon_exists_finiteAlphabet_Indexed_noEpsilon_image
    {L : Language T} (hL : is_Indexed_noEpsilon L) :
    ∃ (S : Finset T) (L' : Language {t : T // t ∈ S}),
      is_Indexed_noEpsilon L' ∧
        Language.map (fun t : {t : T // t ∈ S} => t.1) L' = L := by
  classical
  obtain ⟨g, hne, hlang⟩ := hL
  obtain ⟨S, L', hIndexed, hS⟩ :=
    indexed_language_finiteAlphabet_Indexed_noEpsilon_image g hne
  exact ⟨S, L', hIndexed, hS.trans hlang⟩

/-- Every ε-free indexed language is equivalent to an ε-free indexed language over some finite
terminal alphabet. -/
public theorem is_Indexed_noEpsilon_exists_fintype_alphabet_Indexed_noEpsilon_image
    {L : Language T} (hL : is_Indexed_noEpsilon L) :
    ∃ (A : Type) (_ : Fintype A) (_ : DecidableEq A) (L' : Language A) (f : A → T),
      is_Indexed_noEpsilon L' ∧ Language.map f L' = L := by
  classical
  obtain ⟨S, L', hIndexed, hmap⟩ :=
    is_Indexed_noEpsilon_exists_finiteAlphabet_Indexed_noEpsilon_image (L := L) hL
  refine ⟨{t : T // t ∈ S}, ?_, ?_, L', (fun t => t.1), hIndexed, hmap⟩
  · infer_instance
  · infer_instance

/-- The inclusion image of an indexed language over a finite subtype is indexed over the
ambient alphabet. -/
public theorem is_Indexed_of_finiteAlphabet_Indexed_image {S : Finset T}
    {L' : Language {t : T // t ∈ S}} (hL' : is_Indexed L') :
    is_Indexed (Language.map (fun t : {t : T // t ∈ S} => t.1) L') := by
  have hIndexed : is_Indexed
      (L'.homomorphicImage (fun t : {t : T // t ∈ S} => [t.1])) :=
    is_Indexed_homomorphicImage L' (fun t : {t : T // t ∈ S} => [t.1]) hL'
  rwa [Language.homomorphicImage, Language.subst_singletons_eq_map] at hIndexed

/-- A language is indexed iff it is the inclusion image of an indexed language over a finite
terminal subtype. -/
public theorem is_Indexed_iff_exists_finiteAlphabet_Indexed_image {L : Language T} :
    is_Indexed L ↔
      ∃ (S : Finset T) (L' : Language {t : T // t ∈ S}),
        is_Indexed L' ∧ Language.map (fun t : {t : T // t ∈ S} => t.1) L' = L := by
  constructor
  · exact is_Indexed_exists_finiteAlphabet_Indexed_image
  · rintro ⟨S, L', hIndexed, hmap⟩
    rw [← hmap]
    exact is_Indexed_of_finiteAlphabet_Indexed_image hIndexed

/-- A language is indexed iff it is the image of an indexed language over some finite
terminal alphabet. -/
public theorem is_Indexed_iff_exists_fintype_alphabet_Indexed_image {L : Language T} :
    is_Indexed L ↔
      ∃ (A : Type) (_ : Fintype A) (_ : DecidableEq A) (L' : Language A) (f : A → T),
        is_Indexed L' ∧ Language.map f L' = L := by
  constructor
  · exact is_Indexed_exists_fintype_alphabet_Indexed_image
  · rintro ⟨A, _, _, L', f, hIndexed, hmap⟩
    rw [← hmap]
    have hImage : is_Indexed (L'.homomorphicImage fun a => [f a]) :=
      is_Indexed_homomorphicImage L' (fun a => [f a]) hIndexed
    rwa [Language.homomorphicImage, Language.subst_singletons_eq_map] at hImage

/-- Every indexed language has finite terminal support. -/
public theorem is_Indexed_finite_terminal_support {L : Language T} (hL : is_Indexed L) :
    ∃ S : Finset T, ∀ w ∈ L, ∀ t ∈ w, t ∈ S := by
  classical
  obtain ⟨g, hlang⟩ := hL
  refine ⟨grammarTerminalSet g, ?_⟩
  intro w hw
  exact language_supported g (by simpa [hlang] using hw)
