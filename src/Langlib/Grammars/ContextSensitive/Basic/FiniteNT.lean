module
public import Langlib.Grammars.Unrestricted.FiniteNonterminals
public import Langlib.Grammars.NonContracting.Definition
@[expose]
public section

/-!
# Finite-nonterminal equivalence for non-contracting grammars

`restrictGrammar` finitizes the nonterminal type of any unrestricted grammar while
preserving its language. Here we record that it also preserves non-contractingness,
and package the resulting equivalence: every non-contracting grammar is equivalent to
one with finitely many nonterminals that is still non-contracting.

## Main results

- `restrictGrammar_noncontracting` — `restrictGrammar` preserves non-contractingness.
- `noncontracting_equivalent_finiteNT` — every non-contracting grammar has an equivalent
  one with `Finite` nonterminals that is again non-contracting.
-/

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

/-- **Finite-nonterminal equivalence.** Every non-contracting grammar is equivalent to a
non-contracting grammar with finitely many nonterminals. We take `restrictGrammar g`,
which finitizes the nonterminals, preserves the language, and stays non-contracting. -/
public theorem noncontracting_equivalent_finiteNT (g : grammar T)
    (hg : grammar_noncontracting g) :
    ∃ g' : grammar T, Finite g'.nt ∧ grammar_noncontracting g' ∧
      grammar_language g' = grammar_language g :=
  ⟨restrictGrammar g, Finite.of_fintype _, restrictGrammar_noncontracting g hg,
    (grammar_language_eq_restrictGrammar g).symm⟩

end
