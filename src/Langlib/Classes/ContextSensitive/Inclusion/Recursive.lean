module

public import Langlib.Classes.ContextSensitive.Decidability.Computability
public import Langlib.Classes.ContextSensitive.Inclusion.RecursivelyEnumerable
public import Langlib.Classes.RecursivelyEnumerable.Closure.Intersection
public import Langlib.Classes.RecursivelyEnumerable.Closure.Union
public import Langlib.Classes.Regular.Inclusion.RecursivelyEnumerable
public import Langlib.Classes.Regular.Closure.Homomorphism
public import Langlib.Classes.Regular.Closure.Complement
public import Langlib.Grammars.Unrestricted.FiniteNonterminals
public import Langlib.Grammars.NonContracting.Equivalence.ContextSensitive
public import Langlib.Grammars.NonContracting.EpsilonElimination
import Mathlib.Tactic
@[expose]
public section



/-! # Context-Sensitive Languages are Recursive

This file proves the bridge theorem that every context-sensitive language (in the
broad `S → ε`-optional `grammar_context_sensitive` sense) is recursive, and the
corresponding class-level inclusion `(CS : Set (Language T)) ⊆ Recursive`.

## Strategy

Given `is_CS L` we get an unrestricted grammar `g` with `grammar_context_sensitive g`
and `grammar_language g = L`. Then:

* `is_RE L` is immediate via `is_RE_of_CS`.
* `is_RE Lᶜ` is the work. We produce a **non-contracting** grammar `g₀` with finitely
  many nonterminals generating `L \ {[]}` (this is ε-elimination of the optional start
  rule `S → ε`, isolated as `exists_noncontracting_offEmpty_of_CS`). Its complement is
  RE by `is_RE_compl_of_noncontracting`. Then `Lᶜ` differs from `(grammar_language g₀)ᶜ`
  only at the single word `[]`, and RE-ness is preserved under intersection with the
  regular language `{[]}ᶜ`, giving `is_RE Lᶜ`.
* Post's theorem `is_Recursive_of_isRE_of_isRE_compl` concludes.

## Main declarations

* `is_Recursive_of_is_CS`
* `CS_subset_Recursive_class`
-/

open Relation

variable {T : Type}

/-! ## Non-contracting preservation under `restrictGrammar`

`restrictGrammar` rewrites every rule by mapping each of its symbol lists through
`restrictSym`. Since `List.map` preserves length, the non-contracting inequality is
preserved verbatim. -/

/-- Restricting a non-contracting grammar to its used nonterminals keeps it
non-contracting. -/
public theorem restrictGrammar_noncontracting (g : grammar T)
    (hg : grammar_noncontracting g) :
    grammar_noncontracting (restrictGrammar g) := by
  intro r' hr'
  obtain ⟨r, hr, hL, hN, hR, hout⟩ := restrictGrammar_rule_mem hr'
  have := hg r hr
  rw [hL, hR, hout]
  simpa [List.length_map] using this

/-! ## ε-elimination of the optional start rule (isolated hard step)

The only contracting rule allowed by `grammar_context_sensitive` is the optional
`S → ε` rule (`initial_epsilon_rule`). The classical context-sensitive normal-form
result is that such a grammar can be converted into an ε-free non-contracting grammar
generating the same language **minus the empty word**. (Naively deleting the `S → ε`
rule is *not* correct, because that rule can help derive non-empty words by spawning
and later deleting copies of the start symbol; a genuine nullable-`S` elimination that
adds rule variants is required, and it must be arranged to stay non-contracting.)

We isolate this as a single statement. Everything downstream depends only on it. -/

/-- **Isolated ε-elimination lemma.** Every broadly-context-sensitive grammar admits an
equivalent (off the empty word) ε-free **non-contracting** grammar with finitely many
nonterminals. -/
public theorem exists_noncontracting_offEmpty_of_CS (g : grammar T)
    (hg : grammar_context_sensitive g) :
    ∃ g₀ : grammar T, Finite g₀.nt ∧ grammar_noncontracting g₀ ∧
      grammar_language g₀ = grammar_language g \ {[]} := by
  -- `EpsElim.g_elim g` is a non-contracting grammar (possibly infinite nt) generating
  -- `L(g) \ {[]}`.  Finitize its nonterminals with `restrictGrammar`, which preserves both
  -- the language (`grammar_language_eq_restrictGrammar`) and non-contraction
  -- (`restrictGrammar_noncontracting`).
  refine ⟨restrictGrammar (EpsElim.g_elim g), Finite.of_fintype _,
    restrictGrammar_noncontracting _ (EpsElim.g_elim_noncontracting g), ?_⟩
  rw [← grammar_language_eq_restrictGrammar]
  exact EpsElim.g_elim_language g hg

/-! ## RE-ness of the complement

The complement of a non-contracting language is RE (`is_RE_compl_of_noncontracting`).
We package the finite-nonterminal instance plumbing, then adjust at the single word
`[]`. -/

/-- The complement of a finite-nonterminal non-contracting language is RE. -/
public theorem is_RE_compl_of_noncontracting_finite
    [Fintype T] [DecidableEq T] [Primcodable T]
    (g₀ : grammar T) (hfin : Finite g₀.nt) (hnc : grammar_noncontracting g₀) :
    is_RE (grammar_language g₀)ᶜ := by
  haveI : Fintype g₀.nt := Fintype.ofFinite _
  haveI : DecidableEq g₀.nt := Classical.decEq _
  haveI : Primcodable g₀.nt :=
    Primcodable.ofEquiv (Fin (Fintype.card g₀.nt)) (Fintype.truncEquivFin g₀.nt).out
  exact is_RE_compl_of_noncontracting g₀ hnc

/-- The complement of the singleton empty-word language is RE (it is regular). -/
public theorem is_RE_compl_singleton_empty [Fintype T] :
    is_RE (({[]} : Language T)ᶜ) :=
  is_RE_of_isRegular (Language.IsRegular.compl Language.isRegular_epsilon)

/-- The empty language is RE (it is regular as the complement of the universal regular
language; here we get it directly as `{[]} ⊓ {[]}ᶜ`). -/
public theorem is_RE_empty [Fintype T] [DecidableEq T] [Primcodable T] :
    is_RE (⊥ : Language T) := by
  have : (⊥ : Language T) = ({[]} : Language T) ⊓ ({[]} : Language T)ᶜ := by
    simp
  rw [this]
  exact RE_of_RE_i_RE _ _ ⟨is_RE_of_isRegular Language.isRegular_epsilon, is_RE_compl_singleton_empty⟩

/-- The singleton empty-word language is RE. -/
public theorem is_RE_singleton_empty [Fintype T] : is_RE ({[]} : Language T) :=
  is_RE_of_isRegular Language.isRegular_epsilon

/-- If `M` agrees with `L` off the empty word (`M = L \ {[]}`), and `Mᶜ` is RE, then
`Lᶜ` is RE.

`Lᶜ` decomposes as `(Mᶜ ⊓ {[]}ᶜ) + (Lᶜ ⊓ {[]})`: off the empty word `L` and `M` agree,
and the single word `[]` is added back exactly when `[] ∉ L`. The first part is an
intersection of RE languages; the second is either `{[]}` or `∅`, both RE; RE is closed
under union. -/
public theorem is_RE_compl_of_compl_offEmpty
    [Fintype T] [DecidableEq T] [Primcodable T]
    {L M : Language T} (hM : M = L \ {[]}) (hcompl : is_RE Mᶜ) :
    is_RE Lᶜ := by
  -- The "off-empty" part.
  have hoff : is_RE (Mᶜ ⊓ ({[]} : Language T)ᶜ) :=
    RE_of_RE_i_RE Mᶜ (({[]} : Language T)ᶜ) ⟨hcompl, is_RE_compl_singleton_empty⟩
  -- The "at-empty" part: either `{[]}` or `∅`.
  have hat : is_RE (Lᶜ ⊓ ({[]} : Language T)) := by
    by_cases h0 : [] ∈ L
    · have : Lᶜ ⊓ ({[]} : Language T) = (⊥ : Language T) := by
        ext w
        constructor
        · rintro ⟨hwL, (rfl : w = [])⟩; exact (hwL h0).elim
        · intro hw
          rw [Set.bot_eq_empty, Set.mem_empty_iff_false] at hw
          exact hw.elim
      rw [this]; exact is_RE_empty
    · have : Lᶜ ⊓ ({[]} : Language T) = ({[]} : Language T) := by
        ext w; constructor
        · rintro ⟨_, hw⟩; exact hw
        · rintro (rfl : w = []); exact ⟨h0, rfl⟩
      rw [this]; exact is_RE_singleton_empty
  -- Assemble: `Lᶜ = (Mᶜ ⊓ {[]}ᶜ) + (Lᶜ ⊓ {[]})`.
  have heq : Lᶜ = (Mᶜ ⊓ ({[]} : Language T)ᶜ) + (Lᶜ ⊓ ({[]} : Language T)) := by
    subst hM
    ext w
    rw [Language.mem_add]
    constructor
    · intro hwL
      -- `hwL : w ∉ L`
      by_cases hw0 : w = []
      · exact Or.inr ⟨hwL, hw0⟩
      · refine Or.inl ⟨?_, ?_⟩
        · -- `w ∉ L \ {[]}`
          rintro ⟨hwL', _⟩; exact hwL hwL'
        · -- `w ∉ {[]}`
          exact hw0
    · rintro (⟨h1, h2⟩ | ⟨h1, _⟩)
      · -- `h1 : w ∉ L \ {[]}`, `h2 : w ∉ {[]}` ⊢ `w ∉ L`
        intro hwL'
        exact h1 ⟨hwL', fun (hw0 : w = []) => h2 hw0⟩
      · -- `h1 : w ∉ L`
        exact h1
  rw [heq]
  exact RE_of_RE_u_RE _ _ ⟨hoff, hat⟩

/-! ## Main bridge theorems -/

/-- **Every context-sensitive language is recursive.** -/
public theorem is_Recursive_of_is_CS
    [Fintype T] [DecidableEq T] [Primcodable T]
    {L : Language T} (h : is_CS L) : is_Recursive L := by
  obtain ⟨g, hgcs, hgL⟩ := h
  -- `L` is RE.
  have hRE : is_RE L := is_RE_of_CS ⟨g, hgcs, hgL⟩
  -- `Lᶜ` is RE via the ε-eliminated non-contracting grammar.
  obtain ⟨g₀, hfin, hnc, hg₀⟩ := exists_noncontracting_offEmpty_of_CS g hgcs
  have hMcompl : is_RE (grammar_language g₀)ᶜ :=
    is_RE_compl_of_noncontracting_finite g₀ hfin hnc
  have hg₀L : grammar_language g₀ = L \ {[]} := by rw [hg₀, hgL]
  have hREc : is_RE Lᶜ := is_RE_compl_of_compl_offEmpty hg₀L hMcompl
  exact is_Recursive_of_isRE_of_isRE_compl hRE hREc

/-- **The class of context-sensitive languages is a subset of the recursive languages.** -/
public theorem CS_subset_Recursive_class
    [Fintype T] [DecidableEq T] [Primcodable T] :
    (CS : Set (Language T)) ⊆ (Recursive : Set (Language T)) := by
  intro L hL
  exact is_Recursive_of_is_CS hL
