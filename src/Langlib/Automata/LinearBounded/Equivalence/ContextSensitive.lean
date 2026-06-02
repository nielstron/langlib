module

public import Langlib.Automata.LinearBounded.Equivalence.LBAToCSG
public import Langlib.Automata.LinearBounded.Equivalence.LBAToCSG.Completeness
public import Langlib.Automata.LinearBounded.Equivalence.LBAToCSG.Soundness
public import Langlib.Automata.LinearBounded.Equivalence.CSGToLBA
public import Langlib.Automata.LinearBounded.Positive
public import Langlib.Automata.LinearBounded.Equivalence.EndmarkerTape
public import Langlib.Automata.LinearBounded.Equivalence.EndmarkerToFlag
public import Langlib.Classes.ContextSensitive.Definition
public import Langlib.Classes.ContextSensitive.Inclusion.RecursivelyEnumerable
public import Langlib.Classes.ContextSensitive.Inclusion.Recursive
public import Langlib.Classes.ContextSensitive.Closure.EmptyWord
import Mathlib.Tactic
@[expose]
public section



/-!
# Context-Sensitive Languages = LBA Languages (`CS = LBA`)

This file states the Myhill–Landweber–Kuroda theorem in its set-level form,

  `CS = LBA`  (`CS_eq_LBA`),

for the canonical **endmarker** LBA (`is_LBA`/`LBA`, `Automata/LinearBounded/Definition.lean`).

It is assembled in two layers:

* The genuinely space-bounded core, `is_LBA_pos_iff : is_LBA_pos L ↔ is_CS L ∧ [] ∉ L`: the
  marker-free `|w|`-cell model (`Automata/LinearBounded/Positive.lean`) recognizes exactly the
  **ε-free** context-sensitive languages. This is `myhill_language_eq` (Myhill's bisimulation, `→`,
  `Equivalence/LBAToCSG.lean`) together with the Kuroda construction restricted to the
  non-contracting core (`←`, `Equivalence/CSGToLBA.lean`).
* The empty word, carried by the **endmarker** model on the genuine two-cell tape `⊢⊣` — so the
  machine itself decides `ε`, no external flag. `CS_subset_LBA` runs the Kuroda LBA on `⊢ w ⊣` via
  `simMachine` (`Equivalence/EndmarkerTape.lean`); `LBA_subset_CS` folds an endmarker LBA onto
  `|w|` cells via `flagMachine` (`Equivalence/EndmarkerToFlag.lean`) and adjoins `ε` when accepted.

This makes the two classes *equal* (the endmarker's `⊢⊣` cell is exactly what upgrades "ε-free CSL"
to all of `CS`), rather than merely "equal up to `ε`".

## References

* Kuroda, S.-Y. (1964), "Classes of languages and linear-bounded automata".
* Myhill, J. (1960), "Linear bounded automata".
* Hopcroft, Motwani, Ullman, *Introduction to Automata Theory, Languages, and Computation*,
  Chapter 9.
-/

open MyhillConstruction

variable {T : Type}

/-! ## LBA ⊆ CS (Myhill) -/

/-- **Myhill's construction (core).** The context-sensitive grammar built from an LBA in
`LBAToCSG.lean` generates exactly the non-empty language recognised by the automaton.

This is the genuine content of the LBA → CS direction: the bisimulation between
cell-sentential-forms and LBA configurations (the grammar and its rule membership lemmas are
established in `LBAToCSG.lean`):

* **completeness** (`⊇`): an accepting LBA run on `w` is mirrored by a derivation
  `start ⇒* map terminal w` — the start rules lay down one `cell` per input symbol, the
  simulation rules track each LBA step (interior moves use the 3-step `cellPending`
  protocol), and the cleanup rules recover the terminals once an accepting state appears;
* **soundness** (`⊆`): conversely every terminal string derivable from `start` arises this
  way, by an invariant stating that every reachable sentential form of `cell`s decodes to a
  configuration reachable by `M` from the initial configuration on `w`. -/
theorem myhill_language_eq
    {Γ Λ : Type} [Fintype T] [Fintype Γ] [Fintype Λ]
    [DecidableEq T] [DecidableEq Γ] [DecidableEq Λ]
    (M : LBA.Machine Γ Λ) (embed : T ↪ Γ) :
    CS_language (myhillGrammar M embed) = LBA.LanguageViaEmbed M embed := by
  funext w
  apply propext
  constructor
  · -- soundness (⊆): every derived terminal word is accepted
    exact MyhillConstruction.myhill_sound M embed w
  · -- completeness (⊇): every accepted word is derived
    exact MyhillConstruction.myhill_complete M embed w

variable [Fintype T] [DecidableEq T]

/-! ## `LBA_pos` ⊆ ε-free CS (Myhill) -/

/-- Every bounded-tape LBA language is context-sensitive (Myhill's direction). -/
theorem is_LBA_pos_imp_isCS {L : Language T} (h : is_LBA_pos L) : is_CS L := by
  obtain ⟨Γ, Λ, hΓ, hΛ, hdΓ, hdΛ, M, rfl⟩ := h
  haveI := hΓ; haveI := hΛ; haveI := hdΓ; haveI := hdΛ
  let emb : T ↪ Option (T ⊕ Γ) := ⟨fun t => some (Sum.inl t), fun _ _ h => by simpa using h⟩
  rw [show LBA.LanguageViaEmbed M (fun t => some (Sum.inl t))
        = CS_language (myhillGrammar M emb) from (myhill_language_eq M emb).symm]
  exact is_CS_via_csg_implies_is_CS ⟨_, rfl⟩

/-- A bounded-tape LBA never runs on the empty input, so its language is ε-free. -/
theorem not_nil_mem_of_is_LBA_pos {L : Language T} (h : is_LBA_pos L) : [] ∉ L := by
  obtain ⟨Γ, Λ, hΓ, hΛ, hdΓ, hdΛ, M, rfl⟩ := h
  rintro ⟨hne, -⟩
  simp at hne

/-! ## ε-free CS ⊆ `LBA_pos` (Kuroda)

Given a context-sensitive `L` with `[] ∉ L`, restrict to the non-contracting core
(`Grammars/NonContracting`) with finitely many nonterminals
(`Grammars/ContextSensitive/Basic/FiniteNT.lean`), whose language is `L \ {[]} = L`. On input `w`
of length `n` the Kuroda LBA carries the frozen input and a working sentential form over the finite
grammar-symbol alphabet, nondeterministically runs the grammar backwards, and accepts once the form
reduces to `[S]`. Non-contraction bounds every form of a derivation of `w` by `n`, so the `|w|`-cell
tape suffices. -/
theorem is_LBA_pos_of_isCS_not_nil {L : Language T} (hCS : is_CS L) (hne : [] ∉ L) :
    is_LBA_pos L := by
  classical
  obtain ⟨g, hg, rfl⟩ := hCS
  obtain ⟨g₀, hfin, hnc, hlang⟩ := exists_noncontracting_offEmpty_of_CS g hg
  obtain ⟨Γ, Λ, hΓ, hΛ, hdΓ, hdΛ, M, hM⟩ :=
    KurodaConstruction.noncontracting_finite_to_LBA g₀ hfin hnc
  -- `LanguageViaEmbed M = grammar_language g₀ = grammar_language g \ {[]} = grammar_language g`.
  rw [hlang] at hM
  exact ⟨Γ, Λ, hΓ, hΛ, hdΓ, hdΛ, M, by rw [hM, Set.diff_singleton_eq_self hne]⟩

/-! ## The characterization -/

/-- **The bounded-tape LBA languages are exactly the ε-free context-sensitive languages.** -/
theorem is_LBA_pos_iff {L : Language T} : is_LBA_pos L ↔ (is_CS L ∧ [] ∉ L) :=
  ⟨fun h => ⟨is_LBA_pos_imp_isCS h, not_nil_mem_of_is_LBA_pos h⟩,
   fun h => is_LBA_pos_of_isCS_not_nil h.1 h.2⟩

/-! ## CS = LBA (the canonical endmarker model)

Promoting the ε-free core to the full theorem: the empty word is carried by the endmarker model,
which runs on the genuine two-cell tape `⊢⊣`. The two simulations live in
`Equivalence/EndmarkerTape.lean` (`simMachine`/`language_simMachine_eq`) and
`Equivalence/EndmarkerToFlag.lean` (`flagMachine`/`language_flagMachine_eq`). -/

/-- **CS ⊆ LBA.** Every context-sensitive language is recognized by an endmarker LBA: the Kuroda
LBA for the ε-free core is run on `⊢ w ⊣` via `simMachine`, and `ε` is decided on `⊢⊣` by the bit
`decide (ε ∈ L)`. -/
theorem CS_subset_LBA : (CS : Set (Language T)) ⊆ LBA := by
  classical
  rintro L ⟨g, hg, rfl⟩
  obtain ⟨g₀, hfin, hnc, hlang⟩ := exists_noncontracting_offEmpty_of_CS g hg
  obtain ⟨Γ, Λ, hΓ, hΛ, hdΓ, hdΛ, M, hM⟩ :=
    KurodaConstruction.noncontracting_finite_to_LBA g₀ hfin hnc
  rw [hlang] at hM
  haveI := hΓ; haveI := hΛ; haveI := hdΓ; haveI := hdΛ
  refine ⟨Γ, LBA.SimState Λ, inferInstance, inferInstance, inferInstance, inferInstance,
    LBA.simMachine M (decide ([] ∈ grammar_language g)), ?_⟩
  rw [LBA.language_simMachine_eq]
  funext w
  apply propext
  simp only [LBA.LanguageRecognized]
  rcases eq_or_ne w [] with rfl | hw
  · constructor
    · rintro (⟨hb, _⟩ | hv)
      · exact of_decide_eq_true hb
      · obtain ⟨hne, -⟩ := hv; simp at hne
    · intro hmem; exact Or.inl ⟨by simpa using hmem, rfl⟩
  · constructor
    · rintro (⟨_, h0⟩ | hv)
      · exact absurd h0 hw
      · exact ((congrFun hM w) ▸ hv).1
    · intro hmem
      exact Or.inr (by rw [congrFun hM w]; exact ⟨hmem, by simpa using hw⟩)

/-- **LBA ⊆ CS.** Every endmarker-LBA language is context-sensitive: its non-empty part is the
bounded-tape language `LanguageViaEmbed (flagMachine M')` (context-sensitive via Myhill), and `ε`
(if accepted on `⊢⊣`) is adjoined by `is_CS_insert_empty_of_CS_grammar`. -/
theorem LBA_subset_CS : (LBA : Set (Language T)) ⊆ CS := by
  classical
  rintro L ⟨Γ, Λ, hΓ, hΛ, hdΓ, hdΛ, M', rfl⟩
  haveI := hΓ; haveI := hΛ; haveI := hdΓ; haveI := hdΛ
  let emb : T ↪ Option (T ⊕ LBA.FoldCell T Γ) :=
    ⟨fun t => some (Sum.inl t), fun _ _ h => by simpa using h⟩
  have hcore : LBA.LanguageViaEmbed (LBA.flagMachine M') ⇑emb
      = CS_language (myhillGrammar (LBA.flagMachine M') emb) :=
    (myhill_language_eq (LBA.flagMachine M') emb).symm
  rw [show LBA.LanguageEnd M'
        = LBA.LanguageRecognized (LBA.flagMachine M') ⇑emb
            (decide (LBA.Accepts M' (LBA.initCfgEnd M' [])))
      from (LBA.language_flagMachine_eq M' _ (by simp)).symm]
  by_cases hb : (decide (LBA.Accepts M' (LBA.initCfgEnd M' []))) = true
  · -- `ε` accepted: adjoin `ε` to the Myhill language
    rw [hb]
    have : LBA.LanguageRecognized (LBA.flagMachine M') ⇑emb true
        = (fun w => w = [] ∨ CS_language (myhillGrammar (LBA.flagMachine M') emb) w) := by
      funext w
      simp only [LBA.LanguageRecognized]
      rw [show LBA.LanguageViaEmbed (LBA.flagMachine M') ⇑emb w
            = CS_language (myhillGrammar (LBA.flagMachine M') emb) w from congrFun hcore w]
      apply propext
      constructor
      · rintro (⟨_, h⟩ | h)
        · exact Or.inl h
        · exact Or.inr h
      · rintro (h | h)
        · exact Or.inl ⟨trivial, h⟩
        · exact Or.inr h
    rw [this]
    exact is_CS_insert_empty_of_CS_grammar _
  · -- `ε` not accepted: exactly the Myhill language
    rw [Bool.not_eq_true] at hb
    rw [hb]
    have : LBA.LanguageRecognized (LBA.flagMachine M') ⇑emb false
        = CS_language (myhillGrammar (LBA.flagMachine M') emb) := by
      funext w
      simp only [LBA.LanguageRecognized, Bool.false_eq_true, false_and, false_or, hcore]
    rw [this]
    exact is_CS_via_csg_implies_is_CS ⟨_, rfl⟩

/-! ## The theorem -/

/-- **Context-sensitive languages are exactly the LBA languages: `CS = LBA`.** The headline form of
the Myhill–Landweber–Kuroda theorem, for the canonical endmarker LBA model (`is_LBA`/`LBA`,
`Automata/LinearBounded/Definition.lean`). -/
theorem CS_eq_LBA : (CS : Set (Language T)) = LBA :=
  Set.Subset.antisymm CS_subset_LBA LBA_subset_CS
