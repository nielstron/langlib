module

public import Langlib.Classes.ContextSensitive.Definition
public import Langlib.Classes.ContextSensitive.Closure.EpsFreeHomomorphism
public import Mathlib.Data.Finset.Basic
@[expose]
public section

/-! # Finite terminal support for context-sensitive languages

Every grammar in this repository has finitely many rules, and every rule is a finite list of
symbols. Hence every grammar-generated language uses only finitely many terminal symbols. This
file packages that observation for context-sensitive languages as a finite-alphabet image theorem.
-/

open scoped Classical

namespace GrammarFiniteAlphabet

variable {T : Type}

/-- The terminals appearing in a grammar symbol. -/
def symbolTerminals {N : Type} : symbol T N → List T
  | symbol.terminal t => [t]
  | symbol.nonterminal _ => []

/-- The terminals appearing in a sentential form. -/
def stringTerminals {N : Type} (w : List (symbol T N)) : List T :=
  w.flatMap symbolTerminals

/-- The terminals appearing anywhere in a grammar rule. -/
def ruleTerminals {N : Type} (r : grule T N) : List T :=
  stringTerminals r.input_L ++ stringTerminals r.input_R ++ stringTerminals r.output_string

/-- The finite terminal support syntactically mentioned by a grammar. -/
def grammarTerminalSet [DecidableEq T] (g : grammar T) : Finset T :=
  (g.rules.flatMap ruleTerminals).toFinset

def symbolSupported {N : Type} (S : Finset T) : symbol T N → Prop
  | symbol.terminal t => t ∈ S
  | symbol.nonterminal _ => True

def sententialSupported {N : Type} (S : Finset T) (w : List (symbol T N)) : Prop :=
  ∀ s ∈ w, symbolSupported S s

def restrictSymbolOfSupported {N : Type} (S : Finset T)
    (s : symbol T N) (h : symbolSupported S s) :
    symbol {t : T // t ∈ S} N :=
  match s with
  | symbol.terminal t => symbol.terminal ⟨t, h⟩
  | symbol.nonterminal n => symbol.nonterminal n

def restrictStringOfSupported {N : Type} (S : Finset T)
    (w : List (symbol T N)) (h : sententialSupported S w) :
    List (symbol {t : T // t ∈ S} N) :=
  w.attach.map fun s => restrictSymbolOfSupported S s.1 (h s.1 s.2)

def unrestrictSymbol {S : Finset T} {N : Type} :
    symbol {t : T // t ∈ S} N → symbol T N
  | symbol.terminal t => symbol.terminal t.1
  | symbol.nonterminal n => symbol.nonterminal n

private lemma unrestrictSymbol_injective {S : Finset T} {N : Type} :
    Function.Injective (@unrestrictSymbol T S N) := by
  intro a b h
  cases a <;> cases b <;> simp [unrestrictSymbol] at h ⊢
  all_goals assumption

private lemma unrestrict_restrictSymbol {N : Type} (S : Finset T)
    (s : symbol T N) (h : symbolSupported S s) :
    unrestrictSymbol (restrictSymbolOfSupported S s h) = s := by
  cases s <;> rfl

private lemma unrestrict_restrictStringOfSupported {N : Type} (S : Finset T)
    (w : List (symbol T N)) (h : sententialSupported S w) :
    (restrictStringOfSupported S w h).map unrestrictSymbol = w := by
  unfold restrictStringOfSupported
  rw [List.map_map]
  simp [Function.comp_def, unrestrict_restrictSymbol]

private lemma restrictStringOfSupported_eq {N : Type} (S : Finset T)
    {w : List (symbol T N)} (h₁ h₂ : sententialSupported S w) :
    restrictStringOfSupported S w h₁ = restrictStringOfSupported S w h₂ := by
  apply List.map_injective_iff.mpr unrestrictSymbol_injective
  simp [unrestrict_restrictStringOfSupported]

private lemma restrictStringOfSupported_length {N : Type} (S : Finset T)
    (w : List (symbol T N)) (h : sententialSupported S w) :
    (restrictStringOfSupported S w h).length = w.length := by
  have hmap := congrArg List.length (unrestrict_restrictStringOfSupported S w h)
  simpa using hmap

private lemma restrictStringOfSupported_initial {N : Type} (S : Finset T) (n : N)
    (h : sententialSupported S [symbol.nonterminal n]) :
    restrictStringOfSupported S [symbol.nonterminal n] h = [symbol.nonterminal n] := by
  apply List.map_injective_iff.mpr unrestrictSymbol_injective
  simp [unrestrict_restrictStringOfSupported, unrestrictSymbol]

private lemma restrictStringOfSupported_terminal_values {N : Type} (S : Finset T)
    (w : List {t : T // t ∈ S})
    (h : sententialSupported S
      ((w.map (fun t => t.1)).map (fun t => (symbol.terminal t : symbol T N)))) :
    restrictStringOfSupported S
        ((w.map (fun t => t.1)).map (fun t => (symbol.terminal t : symbol T N))) h =
      w.map (fun t => (symbol.terminal t : symbol {t : T // t ∈ S} N)) := by
  apply List.map_injective_iff.mpr unrestrictSymbol_injective
  simp [unrestrict_restrictStringOfSupported, unrestrictSymbol, List.map_map]

private lemma terminal_mem_stringTerminals {N : Type} {w : List (symbol T N)} {t : T}
    (ht : symbol.terminal t ∈ w) : t ∈ stringTerminals w := by
  unfold stringTerminals
  exact List.mem_flatMap.mpr ⟨symbol.terminal t, ht, by simp [symbolTerminals]⟩

private lemma terminal_mem_ruleTerminals_input_L {N : Type} {r : grule T N} {t : T}
    (ht : symbol.terminal t ∈ r.input_L) : t ∈ ruleTerminals r := by
  unfold ruleTerminals
  exact List.mem_append.mpr <|
    Or.inl (List.mem_append.mpr (Or.inl (terminal_mem_stringTerminals ht)))

private lemma terminal_mem_ruleTerminals_input_R {N : Type} {r : grule T N} {t : T}
    (ht : symbol.terminal t ∈ r.input_R) : t ∈ ruleTerminals r := by
  unfold ruleTerminals
  exact List.mem_append.mpr <|
    Or.inl (List.mem_append.mpr (Or.inr (terminal_mem_stringTerminals ht)))

private lemma terminal_mem_ruleTerminals_output {N : Type} {r : grule T N} {t : T}
    (ht : symbol.terminal t ∈ r.output_string) : t ∈ ruleTerminals r := by
  unfold ruleTerminals
  exact List.mem_append.mpr <|
    Or.inr (terminal_mem_stringTerminals ht)

private lemma terminal_mem_grammarTerminalSet_of_ruleTerminals [DecidableEq T]
    {g : grammar T} {r : grule T g.nt} (hr : r ∈ g.rules) {t : T}
    (ht : t ∈ ruleTerminals r) :
    t ∈ grammarTerminalSet g := by
  unfold grammarTerminalSet
  rw [List.mem_toFinset]
  exact List.mem_flatMap.mpr ⟨r, hr, ht⟩

private lemma terminal_mem_grammarTerminalSet_input_L [DecidableEq T] {g : grammar T}
    {r : grule T g.nt} (hr : r ∈ g.rules) {t : T}
    (ht : symbol.terminal t ∈ r.input_L) :
    t ∈ grammarTerminalSet g :=
  terminal_mem_grammarTerminalSet_of_ruleTerminals hr
    (terminal_mem_ruleTerminals_input_L ht)

private lemma terminal_mem_grammarTerminalSet_input_R [DecidableEq T] {g : grammar T}
    {r : grule T g.nt} (hr : r ∈ g.rules) {t : T}
    (ht : symbol.terminal t ∈ r.input_R) :
    t ∈ grammarTerminalSet g :=
  terminal_mem_grammarTerminalSet_of_ruleTerminals hr
    (terminal_mem_ruleTerminals_input_R ht)

private lemma terminal_mem_grammarTerminalSet_output [DecidableEq T] {g : grammar T}
    {r : grule T g.nt} (hr : r ∈ g.rules) {t : T}
    (ht : symbol.terminal t ∈ r.output_string) :
    t ∈ grammarTerminalSet g :=
  terminal_mem_grammarTerminalSet_of_ruleTerminals hr
    (terminal_mem_ruleTerminals_output ht)

lemma rule_input_L_supported [DecidableEq T] {g : grammar T}
    {r : grule T g.nt} (hr : r ∈ g.rules) :
    sententialSupported (grammarTerminalSet g) r.input_L := by
  intro s hs
  cases s with
  | nonterminal n => trivial
  | terminal t => exact terminal_mem_grammarTerminalSet_input_L hr hs

lemma rule_input_R_supported [DecidableEq T] {g : grammar T}
    {r : grule T g.nt} (hr : r ∈ g.rules) :
    sententialSupported (grammarTerminalSet g) r.input_R := by
  intro s hs
  cases s with
  | nonterminal n => trivial
  | terminal t => exact terminal_mem_grammarTerminalSet_input_R hr hs

lemma rule_output_supported [DecidableEq T] {g : grammar T}
    {r : grule T g.nt} (hr : r ∈ g.rules) :
    sententialSupported (grammarTerminalSet g) r.output_string := by
  intro s hs
  cases s with
  | nonterminal n => trivial
  | terminal t => exact terminal_mem_grammarTerminalSet_output hr hs

private lemma sententialSupported_of_append_left {N : Type} {S : Finset T}
    {u v : List (symbol T N)} (h : sententialSupported S (u ++ v)) :
    sententialSupported S u := by
  intro s hs
  exact h s (List.mem_append.mpr (Or.inl hs))

private lemma sententialSupported_of_append_right {N : Type} {S : Finset T}
    {u v : List (symbol T N)} (h : sententialSupported S (u ++ v)) :
    sententialSupported S v := by
  intro s hs
  exact h s (List.mem_append.mpr (Or.inr hs))

private lemma grammar_transforms_supported [DecidableEq T] (g : grammar T)
    {w₁ w₂ : List (symbol T g.nt)}
    (h₁ : sententialSupported (grammarTerminalSet g) w₁)
    (h : grammar_transforms g w₁ w₂) :
    sententialSupported (grammarTerminalSet g) w₂ := by
  rcases h with ⟨r, hr, u, v, hw₁, hw₂⟩
  subst w₁
  subst w₂
  intro s hs
  rcases List.mem_append.mp hs with hleft | hv
  rcases List.mem_append.mp hleft with hu | hout
  · exact h₁ s (by simp [hu])
  · cases s with
  | nonterminal n => trivial
  | terminal t =>
        exact terminal_mem_grammarTerminalSet_output hr hout
  · exact h₁ s (by simp [hv])

private theorem grammar_derives_supported_of_supported [DecidableEq T] (g : grammar T)
    {w₁ w₂ : List (symbol T g.nt)}
    (h₁ : sententialSupported (grammarTerminalSet g) w₁)
    (h : grammar_derives g w₁ w₂) :
    sententialSupported (grammarTerminalSet g) w₂ := by
  induction h with
  | refl => exact h₁
  | tail _ hstep ih =>
      exact grammar_transforms_supported g ih hstep

/-- A derivation from the start symbol mentions only terminals syntactically present in
the grammar's rules. -/
theorem grammar_derives_supported [DecidableEq T] (g : grammar T)
    {w : List (symbol T g.nt)}
    (h : grammar_derives g [symbol.nonterminal g.initial] w) :
    sententialSupported (grammarTerminalSet g) w := by
  exact grammar_derives_supported_of_supported g (by
    intro s hs
    simp at hs
    subst s
    trivial) h

def restrictRule [DecidableEq T] (g : grammar T)
    (r : grule T g.nt) (hr : r ∈ g.rules) :
    grule {t : T // t ∈ grammarTerminalSet g} g.nt where
  input_L := restrictStringOfSupported (grammarTerminalSet g) r.input_L
    (rule_input_L_supported hr)
  input_N := r.input_N
  input_R := restrictStringOfSupported (grammarTerminalSet g) r.input_R
    (rule_input_R_supported hr)
  output_string := restrictStringOfSupported (grammarTerminalSet g) r.output_string
    (rule_output_supported hr)

/-- The same grammar, with terminals restricted to the finite set syntactically appearing
in its rules. -/
def finiteAlphabetGrammar [DecidableEq T] (g : grammar T) :
    grammar {t : T // t ∈ grammarTerminalSet g} where
  nt := g.nt
  initial := g.initial
  rules := g.rules.attach.map fun r => restrictRule g r.1 r.2

private lemma restrictRule_initial_epsilon [DecidableEq T] {g : grammar T}
    {r : grule T g.nt} {hr : r ∈ g.rules}
    (hε : initial_epsilon_rule g r) :
    initial_epsilon_rule (finiteAlphabetGrammar g) (restrictRule g r hr) := by
  rcases hε with ⟨hL, hN, hR, hO⟩
  simp [initial_epsilon_rule, finiteAlphabetGrammar, restrictRule, hL, hN, hR, hO,
    restrictStringOfSupported]

private lemma initial_epsilon_of_restrictRule [DecidableEq T] {g : grammar T}
    {r : grule T g.nt} {hr : r ∈ g.rules}
    (hε : initial_epsilon_rule (finiteAlphabetGrammar g) (restrictRule g r hr)) :
    initial_epsilon_rule g r := by
  rcases hε with ⟨hL, hN, hR, hO⟩
  refine ⟨?_, hN, ?_, ?_⟩
  · have hlen := congrArg List.length hL
    simp [restrictRule, restrictStringOfSupported_length] at hlen
    exact hlen
  · have hlen := congrArg List.length hR
    simp [restrictRule, restrictStringOfSupported_length] at hlen
    exact hlen
  · have hlen := congrArg List.length hO
    simp [restrictRule, restrictStringOfSupported_length] at hlen
    exact hlen

private theorem finiteAlphabetGrammar_context_sensitive [DecidableEq T] (g : grammar T)
    (hg : grammar_context_sensitive g) :
    grammar_context_sensitive (finiteAlphabetGrammar g) := by
  refine ⟨?_, ?_⟩
  · intro r hr
    obtain ⟨r₀, _hr₀, rfl⟩ := List.mem_map.mp hr
    rcases hg.1 r₀.1 r₀.2 with hε | hnc
    · exact Or.inl (restrictRule_initial_epsilon hε)
    · exact Or.inr (by
        simpa [grule_noncontracting, restrictRule, restrictStringOfSupported_length]
          using hnc)
  · rintro ⟨r, hr, hε⟩
    obtain ⟨r₀, _hr₀, rfl⟩ := List.mem_map.mp hr
    have hε₀ := initial_epsilon_of_restrictRule hε
    have hnot := hg.2 ⟨r₀.1, r₀.2, hε₀⟩
    intro r' hr'
    obtain ⟨r₁, _hr₁, rfl⟩ := List.mem_map.mp hr'
    intro hmem
    have hmap :
        symbol.nonterminal g.initial ∈
          ((restrictRule g r₁.1 r₁.2).output_string.map unrestrictSymbol) :=
      List.mem_map.mpr ⟨symbol.nonterminal g.initial, hmem, rfl⟩
    have hmap' : symbol.nonterminal g.initial ∈ r₁.1.output_string := by
      simpa [restrictRule, unrestrict_restrictStringOfSupported] using hmap
    exact hnot r₁.1 r₁.2 hmap'

private theorem finiteAlphabetGrammar_transforms_unrestrict [DecidableEq T] (g : grammar T)
    {w₁ w₂ : List (symbol {t : T // t ∈ grammarTerminalSet g} (finiteAlphabetGrammar g).nt)}
    (h : grammar_transforms (finiteAlphabetGrammar g) w₁ w₂) :
    grammar_transforms g (w₁.map unrestrictSymbol) (w₂.map unrestrictSymbol) := by
  rcases h with ⟨r, hr, u, v, hw₁, hw₂⟩
  obtain ⟨r₀, _hr₀, rfl⟩ := List.mem_map.mp hr
  refine ⟨r₀.1, r₀.2, u.map unrestrictSymbol, v.map unrestrictSymbol, ?_, ?_⟩
  · have hw₁' := congrArg (List.map unrestrictSymbol) hw₁
    simpa [List.map_append, restrictRule, unrestrict_restrictStringOfSupported,
      unrestrictSymbol, List.append_assoc] using hw₁'
  · have hw₂' := congrArg (List.map unrestrictSymbol) hw₂
    simpa [List.map_append, restrictRule, unrestrict_restrictStringOfSupported,
      unrestrictSymbol, List.append_assoc] using hw₂'

private theorem finiteAlphabetGrammar_derives_unrestrict [DecidableEq T] (g : grammar T)
    {w₁ w₂ : List (symbol {t : T // t ∈ grammarTerminalSet g} (finiteAlphabetGrammar g).nt)}
    (h : grammar_derives (finiteAlphabetGrammar g) w₁ w₂) :
    grammar_derives g (w₁.map unrestrictSymbol) (w₂.map unrestrictSymbol) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact ih.tail (finiteAlphabetGrammar_transforms_unrestrict g hstep)

private theorem grammar_transforms_restrict [DecidableEq T] (g : grammar T)
    {w₁ w₂ : List (symbol T g.nt)}
    (h₁ : sententialSupported (grammarTerminalSet g) w₁)
    (h : grammar_transforms g w₁ w₂) :
    grammar_transforms (finiteAlphabetGrammar g)
      (restrictStringOfSupported (grammarTerminalSet g) w₁ h₁)
      (restrictStringOfSupported (grammarTerminalSet g) w₂
        (grammar_transforms_supported g h₁ h)) := by
  rcases h with ⟨r, hr, u, v, hw₁, hw₂⟩
  subst w₁
  subst w₂
  let S := grammarTerminalSet g
  let hu : sententialSupported S u := by
    intro s hs
    exact h₁ s (by simp [hs])
  let hv : sententialSupported S v := by
    intro s hs
    exact h₁ s (by simp [hs])
  refine ⟨restrictRule g r hr, ?_, restrictStringOfSupported S u hu,
    restrictStringOfSupported S v hv, ?_, ?_⟩
  · unfold finiteAlphabetGrammar
    exact List.mem_map.mpr ⟨⟨r, hr⟩, by simp, rfl⟩
  · apply List.map_injective_iff.mpr unrestrictSymbol_injective
    simp [S, List.map_append, restrictRule, unrestrict_restrictStringOfSupported,
      unrestrictSymbol, List.append_assoc]
  · apply List.map_injective_iff.mpr unrestrictSymbol_injective
    simp [S, List.map_append, restrictRule, unrestrict_restrictStringOfSupported,
      List.append_assoc]

private theorem grammar_derives_restrict [DecidableEq T] (g : grammar T)
    {w₁ w₂ : List (symbol T g.nt)}
    (h₁ : sententialSupported (grammarTerminalSet g) w₁)
    (h : grammar_derives g w₁ w₂) :
    grammar_derives (finiteAlphabetGrammar g)
      (restrictStringOfSupported (grammarTerminalSet g) w₁ h₁)
      (restrictStringOfSupported (grammarTerminalSet g) w₂
        (grammar_derives_supported_of_supported g h₁ h)) := by
  induction h with
  | refl =>
      convert (Relation.ReflTransGen.refl :
        grammar_derives (finiteAlphabetGrammar g)
          (restrictStringOfSupported (grammarTerminalSet g) w₁ h₁)
          (restrictStringOfSupported (grammarTerminalSet g) w₁ h₁)) using 1
  | tail hprev hstep ih =>
      let hmid := grammar_derives_supported_of_supported g h₁ hprev
      have hstep' := grammar_transforms_restrict g hmid hstep
      convert ih.tail hstep' using 1

/-- Restrict a language to words over a finite terminal set. -/
def finiteAlphabetRestriction (S : Finset T) (L : Language T) :
    Language {t : T // t ∈ S} :=
  fun w => w.map (fun t => t.1) ∈ L

theorem grammar_language_finiteAlphabetGrammar [DecidableEq T] (g : grammar T) :
    grammar_language (finiteAlphabetGrammar g) =
      finiteAlphabetRestriction (grammarTerminalSet g) (grammar_language g) := by
  ext w
  constructor
  · intro hw
    change grammar_derives (finiteAlphabetGrammar g) [symbol.nonterminal g.initial]
      (w.map symbol.terminal) at hw
    have hder := finiteAlphabetGrammar_derives_unrestrict g hw
    change (w.map (fun t => t.1)) ∈ grammar_language g
    simpa [grammar_language, grammar_generates, finiteAlphabetGrammar, unrestrictSymbol,
      List.map_map] using hder
  · intro hw
    change (w.map (fun t => t.1)) ∈ grammar_language g at hw
    let S := grammarTerminalSet g
    have hstart : sententialSupported S [symbol.nonterminal g.initial] := by
      intro s hs
      simp at hs
      subst s
      trivial
    have hder :
        grammar_derives g [symbol.nonterminal g.initial]
          ((w.map (fun t => t.1)).map symbol.terminal) := by
      simpa [grammar_language, grammar_generates] using hw
    have hlift := grammar_derives_restrict g hstart hder
    change grammar_derives (finiteAlphabetGrammar g) [symbol.nonterminal g.initial]
      (w.map symbol.terminal)
    convert hlift using 1
    exact (restrictStringOfSupported_terminal_values (N := g.nt) S w _).symm

theorem finiteAlphabetRestriction_is_CS [DecidableEq T] (g : grammar T)
    (hg : grammar_context_sensitive g) :
    is_CS (finiteAlphabetRestriction (grammarTerminalSet g) (grammar_language g)) :=
  ⟨finiteAlphabetGrammar g, finiteAlphabetGrammar_context_sensitive g hg,
    grammar_language_finiteAlphabetGrammar g⟩

/-- Every word generated by a grammar is supported by the finite terminal set occurring in
the grammar's rules. -/
theorem grammar_language_supported [DecidableEq T] (g : grammar T)
    {w : List T} (hw : w ∈ grammar_language g) :
    ∀ t ∈ w, t ∈ grammarTerminalSet g := by
  intro t ht
  have hder :
      grammar_derives g [symbol.nonterminal g.initial] (w.map symbol.terminal) := by
    simpa [grammar_language, grammar_generates] using hw
  have hsupp := grammar_derives_supported g hder
  exact hsupp (symbol.terminal t) (List.mem_map.mpr ⟨t, ht, rfl⟩)

/-- If `S` supports `L`, then `L` is the image of its restriction to the finite subtype `S`. -/
theorem map_finiteAlphabetRestriction_eq_of_supported (S : Finset T) (L : Language T)
    (hS : ∀ w ∈ L, ∀ t ∈ w, t ∈ S) :
    Language.map (fun t : {t : T // t ∈ S} => t.1)
        (finiteAlphabetRestriction S L) = L := by
  ext w
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact hu
  · intro hw
    let u : List {t : T // t ∈ S} :=
      w.attach.map fun t => ⟨t.1, hS w hw t.1 t.2⟩
    have hmap : u.map (fun t : {t : T // t ∈ S} => t.1) = w := by
      simp [u]
    refine ⟨u, ?_, hmap⟩
    change u.map (fun t : {t : T // t ∈ S} => t.1) ∈ L
    rw [hmap]
    exact hw

/-- Any grammar language is an image of a language over a finite subtype of the terminal
alphabet. -/
theorem grammar_language_finiteAlphabet_image [DecidableEq T] (g : grammar T) :
    ∃ (S : Finset T) (L' : Language {t : T // t ∈ S}),
      Language.map (fun t : {t : T // t ∈ S} => t.1) L' = grammar_language g := by
  refine ⟨grammarTerminalSet g,
    finiteAlphabetRestriction (grammarTerminalSet g) (grammar_language g), ?_⟩
  exact map_finiteAlphabetRestriction_eq_of_supported _ _ (fun w hw => grammar_language_supported g hw)

/-- A context-sensitive grammar language is the image of a context-sensitive language over
the finite subtype of terminals appearing in the grammar. -/
theorem grammar_language_finiteAlphabet_CS_image [DecidableEq T] (g : grammar T)
    (hg : grammar_context_sensitive g) :
    ∃ (S : Finset T) (L' : Language {t : T // t ∈ S}),
      is_CS L' ∧
        Language.map (fun t : {t : T // t ∈ S} => t.1) L' = grammar_language g := by
  refine ⟨grammarTerminalSet g,
    finiteAlphabetRestriction (grammarTerminalSet g) (grammar_language g),
    finiteAlphabetRestriction_is_CS g hg, ?_⟩
  exact map_finiteAlphabetRestriction_eq_of_supported _ _ (fun w hw => grammar_language_supported g hw)

end GrammarFiniteAlphabet

open GrammarFiniteAlphabet

variable {T : Type}

/-- Every context-sensitive language is the image of a language over a finite subtype of
its terminal alphabet. -/
public theorem is_CS_exists_finiteAlphabet_image {L : Language T} (hL : is_CS L) :
    ∃ (S : Finset T) (L' : Language {t : T // t ∈ S}),
      Language.map (fun t : {t : T // t ∈ S} => t.1) L' = L := by
  classical
  obtain ⟨g, _, hlang⟩ := hL
  obtain ⟨S, L', hS⟩ := grammar_language_finiteAlphabet_image g
  exact ⟨S, L', hS.trans hlang⟩

/-- Every context-sensitive language is equivalent to a context-sensitive language over a
finite terminal subtype. -/
public theorem is_CS_exists_finiteAlphabet_CS_image {L : Language T} (hL : is_CS L) :
    ∃ (S : Finset T) (L' : Language {t : T // t ∈ S}),
      is_CS L' ∧ Language.map (fun t : {t : T // t ∈ S} => t.1) L' = L := by
  classical
  obtain ⟨g, hg, hlang⟩ := hL
  obtain ⟨S, L', hCS, hS⟩ := grammar_language_finiteAlphabet_CS_image g hg
  exact ⟨S, L', hCS, hS.trans hlang⟩

/-- Every context-sensitive language is equivalent to a context-sensitive language over
some finite terminal alphabet. The finite alphabet is represented as a type carrying
`Fintype` and `DecidableEq`, together with a terminal map into the original alphabet. -/
public theorem is_CS_exists_fintype_alphabet_CS_image {L : Language T} (hL : is_CS L) :
    ∃ (A : Type) (_ : Fintype A) (_ : DecidableEq A) (L' : Language A) (f : A → T),
      is_CS L' ∧ Language.map f L' = L := by
  classical
  obtain ⟨S, L', hCS, hmap⟩ := is_CS_exists_finiteAlphabet_CS_image (L := L) hL
  refine ⟨{t : T // t ∈ S}, ?_, ?_, L', (fun t => t.1), hCS, hmap⟩
  · infer_instance
  · infer_instance

/-- The inclusion image of a context-sensitive language over a finite subtype is
context-sensitive over the ambient alphabet. -/
public theorem is_CS_of_finiteAlphabet_CS_image {S : Finset T}
    {L' : Language {t : T // t ∈ S}} (hL' : is_CS L') :
    is_CS (Language.map (fun t : {t : T // t ∈ S} => t.1) L') := by
  have hCS : is_CS
      (L'.homomorphicImage (fun t : {t : T // t ∈ S} => [t.1])) :=
    is_CS_homomorphicImage_epsfree L' (fun t : {t : T // t ∈ S} => [t.1])
      (fun _ => by simp) hL'
  rwa [Language.homomorphicImage, Language.subst_singletons_eq_map] at hCS

/-- A language is context-sensitive iff it is the inclusion image of a context-sensitive
language over a finite terminal subtype. -/
public theorem is_CS_iff_exists_finiteAlphabet_CS_image {L : Language T} :
    is_CS L ↔
      ∃ (S : Finset T) (L' : Language {t : T // t ∈ S}),
        is_CS L' ∧ Language.map (fun t : {t : T // t ∈ S} => t.1) L' = L := by
  constructor
  · exact is_CS_exists_finiteAlphabet_CS_image
  · rintro ⟨S, L', hCS, hmap⟩
    rw [← hmap]
    exact is_CS_of_finiteAlphabet_CS_image hCS

/-- A language is context-sensitive iff it is the image of a context-sensitive language over
some finite terminal alphabet. -/
public theorem is_CS_iff_exists_fintype_alphabet_CS_image {L : Language T} :
    is_CS L ↔
      ∃ (A : Type) (_ : Fintype A) (_ : DecidableEq A) (L' : Language A) (f : A → T),
        is_CS L' ∧ Language.map f L' = L := by
  constructor
  · exact is_CS_exists_fintype_alphabet_CS_image
  · rintro ⟨A, _, _, L', f, hCS, hmap⟩
    rw [← hmap]
    have hImage : is_CS (L'.homomorphicImage fun a => [f a]) :=
      is_CS_homomorphicImage_epsfree L' (fun a => [f a]) (fun _ => by simp) hCS
    rwa [Language.homomorphicImage, Language.subst_singletons_eq_map] at hImage

/-- Every context-sensitive language has finite terminal support. -/
public theorem is_CS_finite_terminal_support {L : Language T} (hL : is_CS L) :
    ∃ S : Finset T, ∀ w ∈ L, ∀ t ∈ w, t ∈ S := by
  classical
  obtain ⟨g, _, hlang⟩ := hL
  refine ⟨grammarTerminalSet g, ?_⟩
  intro w hw
  exact grammar_language_supported g (by simpa [hlang] using hw)
