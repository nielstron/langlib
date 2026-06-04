module

public import Langlib.Classes.ContextSensitive.Inclusion.RecursivelyEnumerable
public import Langlib.Grammars.ContextFree.UnrestrictedCharacterization
public import Langlib.Grammars.ContextFree.EquivMathlibCFG
import Langlib.Grammars.ContextFree.Toolbox
import Langlib.Grammars.ContextSensitive.Toolbox
import Langlib.Classes.ContextFree.Pumping.EpsilonElimination
import Langlib.Classes.ContextSensitive.Closure.EmptyWord
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Height.Basic
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
@[expose]
public section



/-! # Context-Free Inclusions

This file relates the project's context-free grammars to context-sensitive, unrestricted, and mathlib formulations.

## Main declarations

- `is_CS_of_is_CF` / `CF_subclass_CS`
- `is_CF_iff_isContextFree`
-/

variable {T : Type}


/-- A context-free grammar has no ε-productions (every rule has a non-empty right-hand side). -/
def CF_no_epsilon' (g : CF_grammar T) : Prop :=
  ∀ r ∈ g.rules, r.snd ≠ []

/-- Convert a context-free grammar without ε-productions to a context-sensitive grammar.
    The CS rules have empty context (α = β = []) and γ = rule output. -/
def csg_of_cfg (g : CF_grammar T) (hne : CF_no_epsilon' g) : CS_grammar T where
  nt := g.nt
  initial := g.initial
  rules := List.map (fun r : g.nt × (List (symbol T g.nt)) =>
    csrule.mk [] r.fst [] r.snd) g.rules
  output_nonempty := by
    intro r hr
    rw [List.mem_map] at hr
    obtain ⟨r₀, hr₀, rfl⟩ := hr
    exact hne r₀ hr₀

private lemma grammar_of_cfg_well_defined (g : CF_grammar T) (hne : CF_no_epsilon' g) :
  grammar_of_csg (csg_of_cfg g hne) = grammar_of_cfg g :=
by
  cases g with
  | mk nt initial rules =>
    simp [grammar_of_csg, csg_of_cfg, grammar_of_cfg, List.map_map, List.append_nil]

lemma CF_language_eq_CS_language (g : CF_grammar T) (hne : CF_no_epsilon' g) :
  CF_language g = CS_language (csg_of_cfg g hne) :=
by
  unfold CF_language
  unfold CS_language
  ext1 w
  change
    CF_derives g [symbol.nonterminal g.initial] (List.map symbol.terminal w) ↔
    CS_derives (csg_of_cfg g hne) [symbol.nonterminal (csg_of_cfg g hne).initial]
      (List.map symbol.terminal w)
  constructor
  ·
    have indu :
      ∀ v : List (symbol T g.nt),
        CF_derives g [symbol.nonterminal g.initial] v →
          CS_derives (csg_of_cfg g hne) [symbol.nonterminal (csg_of_cfg g hne).initial] v :=
    by
      intro v h
      induction h with
      | refl =>
        apply CS_deri_self
      | tail _ hyp ih =>
        apply CS_deri_of_deri_tran ih
        unfold CF_transforms at hyp
        unfold CS_transforms
        rcases hyp with ⟨r, u, w, rin, bef, aft⟩
        refine ⟨csrule.mk [] r.fst [] r.snd, u, w, ?_, ?_, ?_⟩
        ·
          show _ ∈ (csg_of_cfg g hne).rules
          change _ ∈ List.map _ g.rules
          exact List.mem_map.mpr ⟨r, rin, rfl⟩
        ·
          simpa [List.append_nil] using bef
        ·
          simpa [List.append_nil] using aft
    exact indu (List.map symbol.terminal w)
  ·
    have indu :
      ∀ v : List (symbol T g.nt),
        CS_derives (csg_of_cfg g hne) [symbol.nonterminal g.initial] v →
          CF_derives g [symbol.nonterminal (csg_of_cfg g hne).initial] v :=
    by
      intro v h
      induction h with
      | refl =>
        apply CF_deri_self
      | tail _ hyp ih =>
        apply CF_deri_of_deri_tran ih
        unfold CS_transforms at hyp
        unfold CF_transforms
        rcases hyp with ⟨r, u, w, rin, bef, aft⟩
        change r ∈ List.map _ g.rules at rin
        obtain ⟨r₀, r₀_in, r_eq⟩ := List.mem_map.mp rin
        rw [← r_eq] at bef aft
        simp at bef aft
        refine ⟨r₀, u, w, r₀_in, ?_, ?_⟩
        · simpa [List.singleton_append] using bef
        · simpa [List.append_assoc] using aft
    exact indu (List.map symbol.terminal w)

/-- Context-free languages are context-sensitive.

Context-sensitive grammars require non-empty rule outputs, so the ε-productions of the
context-free grammar are first removed (`ContextFreeGrammar.eliminateEmpty`), yielding a
non-contracting grammar for `L \ {ε}`. The empty word is re-adjoined when `ε ∈ L` using
`is_CS_insert_empty_of_CS_grammar`. -/
theorem is_CS_of_is_CF {L : Language T} (h : is_CF L) : is_CS L := by
  classical
  rw [is_CF_iff_isContextFree] at h
  obtain ⟨g, rfl⟩ := h
  -- An ε-free context-free grammar for `g.language \ {[]}`, as a Langlib `CF_grammar`.
  have heps : CF_no_epsilon' (cfg_of_mathlib_cfg g.eliminateEmpty) := by
    intro r hr
    simp only [cfg_of_mathlib_cfg, ContextFreeGrammar.eliminateEmpty, List.mem_map,
      Finset.mem_toList] at hr
    obtain ⟨r', hr', rfl⟩ := hr
    have hne : r'.output ≠ [] := ContextFreeGrammar.output_mem_removeNullables hr'
    simpa [lssymbol_of_lsSymbol] using hne
  set csg := csg_of_cfg (cfg_of_mathlib_cfg g.eliminateEmpty) heps with hcsg
  have hcsg_lang : CS_language csg = g.language \ {[]} := by
    rw [hcsg, ← CF_language_eq_CS_language, ← mathlib_language_eq_CF_language,
      ContextFreeGrammar.eliminateEmpty_correct]
  have hmem : ∀ w, CS_language csg w ↔ (g.language w ∧ w ≠ []) := by
    intro w
    have hw := Set.ext_iff.mp hcsg_lang w
    simpa [Set.mem_diff, Set.mem_singleton_iff] using hw
  by_cases hε : ([] : List T) ∈ g.language
  · -- `g.language = (g.language \ {[]}) ∪ {ε}`
    have hins := is_CS_insert_empty_of_CS_grammar csg
    have hEq : (fun w => w = [] ∨ CS_language csg w) = g.language := by
      funext w
      apply propext
      rw [hmem w]
      constructor
      · rintro (rfl | ⟨hw, _⟩)
        · exact hε
        · exact hw
      · intro hw
        by_cases hwe : w = []
        · exact Or.inl hwe
        · exact Or.inr ⟨hw, hwe⟩
    rwa [hEq] at hins
  · -- `ε ∉ L`, so `g.language = g.language \ {[]}` is presented directly by the CS grammar.
    refine is_CS_via_csg_implies_is_CS ⟨csg, ?_⟩
    funext w
    apply propext
    rw [hmem w]
    exact ⟨fun hw => hw.1, fun hw => ⟨hw, fun hwe => hε (hwe ▸ hw)⟩⟩

/-- Context-free languages form a subclass of the context-sensitive languages. -/
theorem CF_subclass_CS : (CF : Set (Language T)) ⊆ (CS : Set (Language T)) :=
  fun _ h => is_CS_of_is_CF h
