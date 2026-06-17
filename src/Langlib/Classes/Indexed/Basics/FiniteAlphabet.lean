module

public import Langlib.Classes.Indexed.Definition
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

/-- The same indexed grammar, with terminals restricted to the finite set appearing in rules. -/
def finiteAlphabetGrammar [DecidableEq T] (g : IndexedGrammar T) :
    IndexedGrammar {t : T // t ∈ grammarTerminalSet g} where
  nt := g.nt
  flag := g.flag
  initial := g.initial
  rules := g.rules.attach.map fun r => restrictRule g r.1 r.2

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

/-- Every indexed language has finite terminal support. -/
public theorem is_Indexed_finite_terminal_support {L : Language T} (hL : is_Indexed L) :
    ∃ S : Finset T, ∀ w ∈ L, ∀ t ∈ w, t ∈ S := by
  classical
  obtain ⟨g, hlang⟩ := hL
  refine ⟨grammarTerminalSet g, ?_⟩
  intro w hw
  exact language_supported g (by simpa [hlang] using hw)
