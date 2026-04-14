import Mathlib
import Langlib.Automata.Turing.DSL.SearchProc
import Langlib.Automata.Turing.DSL.Compile
import Langlib.Automata.Turing.DSL.InternalTM
import Langlib.Automata.Turing.Equivalence.GrammarToTM.Decidability
import Langlib.Automata.Turing.Equivalence.GrammarToTM.Computability

/-! # Grammar Membership as a Search Procedure

This file connects grammars to the DSL by expressing grammar membership
as a `SearchProc`. This is the key step in the Grammar → TM proof.

## The Search Procedure

Given a grammar `g`, we build a `SearchProc` where:
- **Witness type**: `List (ℕ × ℕ)` — a sequence of (rule_index, position) pairs
  representing a derivation
- **Enumeration**: all finite lists of pairs of naturals (using `Encodable`)
- **Test**: `grammarTest g` — does this derivation sequence, applied from the
  start symbol, produce the input word?

## Main results

- `grammarSearchProc` — the search procedure for grammar membership
- `grammarSearchProc_language` — its language equals `grammar_language g`
- `grammar_language_is_TM_internal` — grammar languages are internally
  TM-recognizable (with a `Fintype` tape alphabet from the Partrec chain)
-/

open Enum SearchProc

variable {T : Type} [DecidableEq T]

/-! ### The Grammar Search Procedure -/

/-- The search procedure for grammar membership.

Given grammar `g`, this searches over all possible derivation sequences
`seq : List (ℕ × ℕ)` and checks whether applying `seq` to the start
symbol produces the input word. -/
noncomputable def grammarSearchProc (g : grammar T) [DecidableEq g.nt] :
    SearchProc T where
  WitTy := List (ℕ × ℕ)
  enum := Enum.ofEncodable
  test := grammarTest g

/-- The search procedure recognizes exactly the grammar's language.

**Proof sketch**: Immediate from soundness and completeness of `grammarTest`.
- (⊆) If the search accepts `w`, then some `seq` passes `grammarTest`,
  so by `grammarTest_sound`, `w ∈ grammar_language g`.
- (⊇) If `w ∈ grammar_language g`, then by `grammarTest_complete`,
  some `seq` passes `grammarTest`. Since `Enum.ofEncodable` enumerates
  all `List (ℕ × ℕ)`, this `seq` will be found.
-/
theorem grammarSearchProc_language (g : grammar T) [DecidableEq g.nt] :
    (grammarSearchProc g).language = grammar_language g := by
  ext w
  simp only [SearchProc.language, Set.mem_setOf_eq, SearchProc.accepts,
    grammarSearchProc, Enum.range, Enum.ofEncodable, grammar_language,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨seq, ⟨n, hn⟩, ht⟩
    exact grammarTest_sound g seq w ht
  · intro hw
    obtain ⟨seq, hseq⟩ := grammarTest_complete g w hw
    exact ⟨seq, ⟨Encodable.encode seq, Encodable.encodek seq⟩, hseq⟩

/-! ### Grammar → TM via the DSL -/

/-- Grammar languages are internally TM-recognizable.

**Proof**: Express grammar membership as a `SearchProc`, then compile
to TM0 using the compilation theorem.

The search procedure enumerates all `List (ℕ × ℕ)` (derivation sequences)
and for each, tests whether applying it from the start symbol produces
the input word. This test is decidable (pattern matching + list comparison),
so the search is step-computable.

Note: This requires `Fintype g.nt` to derive `Primcodable` instances
needed for the computability proof. The result produces a TM0 over the
Partrec chain's internal `Fintype` alphabet; converting to `Option T`
alphabet requires the alphabet simulation theorem. -/
theorem grammar_language_is_TM_internal {T : Type} [DecidableEq T] [Fintype T]
    (g : grammar T) [DecidableEq g.nt] [Fintype g.nt] :
    ∃ (Γ : Type) (_ : Inhabited Γ) (_ : Fintype Γ)
      (Λ : Type) (_ : Inhabited Λ)
      (M : Turing.TM0.Machine Γ Λ)
      (enc : List T → List Γ),
      ∀ w : List T,
        w ∈ grammar_language g ↔ (Turing.TM0.eval M (enc w)).Dom := by
  haveI : Primcodable T :=
    Primcodable.ofEquiv (Fin (Fintype.card T)) (Fintype.truncEquivFin T).out
  haveI : Primcodable g.nt :=
    Primcodable.ofEquiv (Fin (Fintype.card g.nt)) (Fintype.truncEquivFin g.nt).out
  have key := is_TM_of_searchable (α := List (ℕ × ℕ)) (grammarTest g)
    (grammarTest_computable₂ g)
    (grammar_language g)
    (by
      ext w
      simp only [SearchProc.language, Set.mem_setOf_eq, SearchProc.accepts,
        grammarSearchProc, Enum.range, Enum.ofEncodable, grammar_language,
        Set.mem_setOf_eq]
      constructor
      · intro hw
        obtain ⟨seq, hseq⟩ := grammarTest_complete g w hw
        exact ⟨seq, hseq⟩
      · rintro ⟨seq, ht⟩
        exact grammarTest_sound g seq w ht)
  exact key

/-- Strengthened version: grammar languages are internally TM-recognizable
with **finite states**.

This uses `is_TM_of_searchable_fintype` which produces a TM0 with
`Fintype` state type via support restriction. -/
theorem grammar_language_is_TM_internal_fintype {T : Type} [DecidableEq T] [Fintype T]
    (g : grammar T) [DecidableEq g.nt] [Fintype g.nt] :
    is_TM_internal (grammar_language g) := by
  haveI : Primcodable T :=
    Primcodable.ofEquiv (Fin (Fintype.card T)) (Fintype.truncEquivFin T).out
  haveI : Primcodable g.nt :=
    Primcodable.ofEquiv (Fin (Fintype.card g.nt)) (Fintype.truncEquivFin g.nt).out
  have key := is_TM_of_searchable_fintype (α := List (ℕ × ℕ)) (grammarTest g)
    (grammarTest_computable₂ g)
    (grammar_language g)
    (by
      ext w
      simp only [SearchProc.language, Set.mem_setOf_eq, SearchProc.accepts,
        grammarSearchProc, Enum.range, Enum.ofEncodable, grammar_language,
        Set.mem_setOf_eq]
      constructor
      · intro hw
        obtain ⟨seq, hseq⟩ := grammarTest_complete g w hw
        exact ⟨seq, hseq⟩
      · rintro ⟨seq, ht⟩
        exact grammarTest_sound g seq w ht)
  obtain ⟨Γ, hΓ, hΓf, Λ, hΛ, hΛf, M, enc, hM⟩ := key
  exact ⟨Γ, Λ, hΓ, hΛ, hΓf, hΛf, M, enc, hM⟩
