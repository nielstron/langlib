module

public import Langlib.Classes.ContextFree.Decidability.Characterization
public import Langlib.Classes.Regular.Decidability.Characterization
public import Langlib.Classes.ContextSensitive.Decidability.Characterization
public import Langlib.Classes.RecursivelyEnumerable.Closure.Union
public import Langlib.Classes.ContextFree.Pumping.EpsilonElimination
public import Langlib.Classes.ContextFree.Closure.ConcatenationBonus
public import Mathlib.Computability.Primrec.List
public import Mathlib.Logic.Equiv.Fin.Basic
import Langlib.Classes.ContextSensitive.Closure.EmptyWord
import Langlib.Classes.RecursivelyEnumerable.Closure.Bijection
import Langlib.Utilities.PrimrecHelpers
import Langlib.Utilities.Tactics

@[expose]
public section

/-!
# Computable operations on encoded context-free grammars

This file provides the raw-code operations used by uniform reductions to
context-free grammar problems.  The constructions keep nonterminals in finite
numeric blocks and record the syntactic facts needed to reuse an epsilon-free
CFG as a noncontracting grammar.
-/

namespace ContextFree.EncodedCFG

variable {T : Type}

open EncodedCFG

/-! ## Disjoint union -/

/-- The ordinary fresh-start union of two context-free grammars. -/
def unionGrammar (g₁ g₂ : CF_grammar T) : CF_grammar T :=
  { nt := Option (g₁.nt ⊕ g₂.nt)
    initial := none
    rules :=
      (none, [.nonterminal (some (.inl g₁.initial))]) ::
      (none, [.nonterminal (some (.inr g₂.initial))]) ::
      g₁.rules.map (lift_rule (some ∘ Sum.inl)) ++
      g₂.rules.map (lift_rule (some ∘ Sum.inr)) }

private theorem lift_string_eq_lift_string_ {N₀ N : Type} (f : N₀ → N)
    (rhs : List (symbol T N₀)) :
    lift_string f rhs = lift_string_ f rhs := by
  have hsym : lift_symbol (T := T) f = lift_symbol_ f := by
    funext a
    cases a <;> rfl
  simp [lift_string, lift_string_, hsym]

private theorem grammarRule_lift_rule {N₀ N : Type} (f : N₀ → N)
    (r : N₀ × List (symbol T N₀)) :
    (fun r : N × List (symbol T N) => grule.mk [] r.1 [] r.2) (lift_rule f r) =
      lift_rule_ f ((fun r : N₀ × List (symbol T N₀) =>
        grule.mk [] r.1 [] r.2) r) := by
  rcases r with ⟨A, rhs⟩
  simp [lift_rule, lift_rule_, lift_string_, lift_string_eq_lift_string_]

private theorem grammar_of_cfg_unionGrammar (g₁ g₂ : CF_grammar T) :
    grammar_of_cfg (unionGrammar g₁ g₂) =
      union_grammar (grammar_of_cfg g₁) (grammar_of_cfg g₂) := by
  simp only [unionGrammar, grammar_of_cfg, union_grammar, List.map_append,
    List.map_cons, List.map_map]
  congr 1 <;>
    apply List.map_congr_left <;>
    intro r _ <;>
    exact grammarRule_lift_rule _ r

/-- The fresh-start grammar generates exactly the union. -/
theorem language_unionGrammar (g₁ g₂ : CF_grammar T) :
    CF_language (unionGrammar g₁ g₂) = CF_language g₁ + CF_language g₂ := by
  rw [CF_language_eq_grammar_language, grammar_of_cfg_unionGrammar]
  ext w
  rw [Language.mem_add, CF_language_eq_grammar_language,
    CF_language_eq_grammar_language]
  constructor
  · exact in_L₁_or_L₂_of_in_union
  · rintro (h | h)
    · exact in_union_of_in_L₁ h
    · exact in_union_of_in_L₂ h

/-- Canonical numeric layout for the fresh start followed by the two disjoint
nonterminal blocks. -/
def unionNTEq (G₁ G₂ : EncodedCFG T) :
    Option (Fin G₁.ntCount ⊕ Fin G₂.ntCount) ≃
      Fin (G₁.ntCount + G₂.ntCount + 1) :=
  (Equiv.optionCongr finSumFinEquiv).trans
    (finSuccEquiv (G₁.ntCount + G₂.ntCount)).symm

/-- Normalize and shift one raw nonterminal occurrence into a disjoint block. -/
def shiftRawSymbol (count offset : ℕ) : ℕ ⊕ T → ℕ ⊕ T
  | .inl A => .inl (offset + A % count + 1)
  | .inr a => .inr a

/-- Normalize and shift one raw CFG rule into a disjoint block. -/
def shiftRawRule (count offset : ℕ)
    (r : ℕ × List (ℕ ⊕ T)) : ℕ × List (ℕ ⊕ T) :=
  (offset + r.1 % count + 1, r.2.map (shiftRawSymbol count offset))

/-- The fully explicit raw representation of disjoint union. -/
def unionRaw (G₁ G₂ : EncodedCFG T) : EncodedCFG T :=
  (G₁.ntCount + G₂.ntCount, 0,
    (0, [.inl (G₁.initialIdx % G₁.ntCount + 1)]) ::
    (0, [.inl (G₁.ntCount + G₂.initialIdx % G₂.ntCount + 1)]) ::
    G₁.rawRules.map (shiftRawRule G₁.ntCount 0) ++
    G₂.rawRules.map (shiftRawRule G₂.ntCount G₁.ntCount))

theorem ntCount_primrec [Primcodable T] :
    Primrec (EncodedCFG.ntCount : EncodedCFG T → ℕ) := by
  exact Primrec.nat_add.comp Primrec.fst (Primrec.const 1)

theorem initialIdx_primrec [Primcodable T] :
    Primrec (EncodedCFG.initialIdx : EncodedCFG T → ℕ) := by
  exact Primrec.fst.comp Primrec.snd

theorem rawRules_primrec [Primcodable T] :
    Primrec (EncodedCFG.rawRules : EncodedCFG T → List (ℕ × List (ℕ ⊕ T))) := by
  exact Primrec.snd.comp Primrec.snd

theorem shiftRawSymbol_primrec [Primcodable T] :
    Primrec (fun p : (ℕ × ℕ) × (ℕ ⊕ T) =>
      shiftRawSymbol p.1.1 p.1.2 p.2) := by
  refine (Primrec.sumCasesOn
    (f := fun p : (ℕ × ℕ) × (ℕ ⊕ T) => p.2)
    (g := fun p A => Sum.inl (p.1.2 + A % p.1.1 + 1))
    (h := fun _ a => Sum.inr a)
    Primrec.snd ?_ ?_).of_eq ?_
  · apply Primrec₂.mk
    have hoff : Primrec
        (fun q : (((ℕ × ℕ) × (ℕ ⊕ T)) × ℕ) => q.1.1.2) :=
      Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
    have hmod : Primrec
        (fun q : (((ℕ × ℕ) × (ℕ ⊕ T)) × ℕ) =>
          q.2 % q.1.1.1) :=
      Primrec.nat_mod.comp Primrec.snd
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
    exact Primrec.sumInl.comp
      (Primrec.nat_add.comp (Primrec.nat_add.comp hoff hmod) (Primrec.const 1))
  · apply Primrec₂.mk
    exact Primrec.sumInr.comp Primrec.snd
  · intro p
    cases p.2 <;> rfl

theorem shiftRawRule_primrec [Primcodable T] :
    Primrec (fun p : (ℕ × ℕ) × (ℕ × List (ℕ ⊕ T)) =>
      shiftRawRule p.1.1 p.1.2 p.2) := by
  have hoff : Primrec
      (fun p : (ℕ × ℕ) × (ℕ × List (ℕ ⊕ T)) => p.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hmod : Primrec
      (fun p : (ℕ × ℕ) × (ℕ × List (ℕ ⊕ T)) =>
        p.2.1 % p.1.1) :=
    Primrec.nat_mod.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.fst.comp Primrec.fst)
  have hlhs : Primrec
      (fun p : (ℕ × ℕ) × (ℕ × List (ℕ ⊕ T)) =>
        p.1.2 + p.2.1 % p.1.1 + 1) :=
    Primrec.nat_add.comp (Primrec.nat_add.comp hoff hmod) (Primrec.const 1)
  have hmap : Primrec
      (fun p : (ℕ × ℕ) × List (ℕ ⊕ T) =>
        p.2.map (shiftRawSymbol p.1.1 p.1.2)) := by
    apply Primrec.list_map Primrec.snd
    apply Primrec₂.mk
    exact shiftRawSymbol_primrec.comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)
  have hrhs : Primrec
      (fun p : (ℕ × ℕ) × (ℕ × List (ℕ ⊕ T)) =>
        p.2.2.map (shiftRawSymbol p.1.1 p.1.2)) := by
    exact hmap.comp (Primrec.pair Primrec.fst (Primrec.snd.comp Primrec.snd))
  exact Primrec.pair hlhs hrhs

theorem mapShiftedRules_primrec [Primcodable T] :
    Primrec (fun p : (ℕ × ℕ) × List (ℕ × List (ℕ ⊕ T)) =>
      p.2.map (shiftRawRule p.1.1 p.1.2)) := by
  apply Primrec.list_map Primrec.snd
  apply Primrec₂.mk
  exact shiftRawRule_primrec.comp
    (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)

theorem unionRaw_primrec [Primcodable T] :
    Primrec (fun p : EncodedCFG T × EncodedCFG T => unionRaw p.1 p.2) := by
  have hc₁ : Primrec (fun p : EncodedCFG T × EncodedCFG T => p.1.ntCount) :=
    ntCount_primrec.comp Primrec.fst
  have hc₂ : Primrec (fun p : EncodedCFG T × EncodedCFG T => p.2.ntCount) :=
    ntCount_primrec.comp Primrec.snd
  have hi₁ : Primrec (fun p : EncodedCFG T × EncodedCFG T => p.1.initialIdx) :=
    initialIdx_primrec.comp Primrec.fst
  have hi₂ : Primrec (fun p : EncodedCFG T × EncodedCFG T => p.2.initialIdx) :=
    initialIdx_primrec.comp Primrec.snd
  have hfirstIdx : Primrec (fun p : EncodedCFG T × EncodedCFG T =>
      p.1.initialIdx % p.1.ntCount + 1) :=
    Primrec.nat_add.comp (Primrec.nat_mod.comp hi₁ hc₁) (Primrec.const 1)
  have hsecondIdx : Primrec (fun p : EncodedCFG T × EncodedCFG T =>
      p.1.ntCount + p.2.initialIdx % p.2.ntCount + 1) :=
    Primrec.nat_add.comp
      (Primrec.nat_add.comp hc₁ (Primrec.nat_mod.comp hi₂ hc₂))
      (Primrec.const 1)
  have hfirstRule : Primrec (fun p : EncodedCFG T × EncodedCFG T =>
      ((0, [Sum.inl (p.1.initialIdx % p.1.ntCount + 1)]) :
        ℕ × List (ℕ ⊕ T))) :=
    Primrec.pair (Primrec.const 0)
      (Primrec.list_cons.comp (Primrec.sumInl.comp hfirstIdx) (Primrec.const []))
  have hsecondRule : Primrec (fun p : EncodedCFG T × EncodedCFG T =>
      ((0, [Sum.inl (p.1.ntCount + p.2.initialIdx % p.2.ntCount + 1)]) :
        ℕ × List (ℕ ⊕ T))) :=
    Primrec.pair (Primrec.const 0)
      (Primrec.list_cons.comp (Primrec.sumInl.comp hsecondIdx) (Primrec.const []))
  have hleft : Primrec (fun p : EncodedCFG T × EncodedCFG T =>
      p.1.rawRules.map (shiftRawRule p.1.ntCount 0)) := by
    exact mapShiftedRules_primrec.comp
      (Primrec.pair (Primrec.pair hc₁ (Primrec.const 0))
        (rawRules_primrec.comp Primrec.fst))
  have hright : Primrec (fun p : EncodedCFG T × EncodedCFG T =>
      p.2.rawRules.map (shiftRawRule p.2.ntCount p.1.ntCount)) := by
    exact mapShiftedRules_primrec.comp
      (Primrec.pair (Primrec.pair hc₂ hc₁)
        (rawRules_primrec.comp Primrec.snd))
  have htail : Primrec (fun p : EncodedCFG T × EncodedCFG T =>
      p.1.rawRules.map (shiftRawRule p.1.ntCount 0) ++
        p.2.rawRules.map (shiftRawRule p.2.ntCount p.1.ntCount)) :=
    Primrec.list_append.comp hleft hright
  have hrules : Primrec (fun p : EncodedCFG T × EncodedCFG T =>
      (0, [Sum.inl (p.1.initialIdx % p.1.ntCount + 1)]) ::
      (0, [Sum.inl (p.1.ntCount + p.2.initialIdx % p.2.ntCount + 1)]) ::
      p.1.rawRules.map (shiftRawRule p.1.ntCount 0) ++
        p.2.rawRules.map (shiftRawRule p.2.ntCount p.1.ntCount)) :=
    Primrec.list_cons.comp hfirstRule (Primrec.list_cons.comp hsecondRule htail)
  exact Primrec.pair (Primrec.nat_add.comp hc₁ hc₂)
    (Primrec.pair (Primrec.const 0) hrules)

/-- Computable disjoint union at the encoded-grammar level.  `encodeCFG`
normalizes every source index modulo its declared nonterminal count before
placing it in its numeric block. -/
def union (G₁ G₂ : EncodedCFG T) : EncodedCFG T :=
  ContextFree.EncodedCFG.encodeCFG
    (unionGrammar G₁.toCFGrammar G₂.toCFGrammar) (unionNTEq G₁ G₂)

private theorem union_eq_unionRaw (G₁ G₂ : EncodedCFG T) :
    union G₁ G₂ = unionRaw G₁ G₂ := by
  rcases G₁ with ⟨n₁, i₁, r₁⟩
  rcases G₂ with ⟨n₂, i₂, r₂⟩
  simp [union, unionRaw, unionGrammar, unionNTEq, shiftRawRule, shiftRawSymbol,
    ContextFree.EncodedCFG.encodeCFG, EncodedCFG.toCFGrammar, EncodedCFG.toNT,
    EncodedCFG.toSymbol, EncodedCFG.ntCount, EncodedCFG.numNT,
    EncodedCFG.initialIdx, EncodedCFG.rawRules, ContextFree.EncodedCFG.encodeSymbol,
    lift_rule, lift_string, lift_symbol, List.map_map, Function.comp_def,
    finSuccEquiv_symm_some, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]
  congr 3
  congr 2
  all_goals
    apply List.map_congr_left
    rintro ⟨A, rhs⟩ _
    unfold shiftRawRule
    apply Prod.ext
    · simp [EncodedCFG.ntCount, EncodedCFG.numNT]
    · apply List.map_congr_left
      intro s _
      cases s <;>
        simp [shiftRawSymbol, EncodedCFG.toSymbol, EncodedCFG.toNT,
          EncodedCFG.ntCount, EncodedCFG.numNT,
        finSuccEquiv_symm_some, finSumFinEquiv_apply_left,
        finSumFinEquiv_apply_right]

/-- Disjoint union is primitive recursive uniformly in both raw grammar codes. -/
theorem union_primrec [Primcodable T] :
    Primrec (fun p : EncodedCFG T × EncodedCFG T => union p.1 p.2) :=
  unionRaw_primrec.of_eq fun p => (union_eq_unionRaw p.1 p.2).symm

theorem union_primrec₂ [Primcodable T] : Primrec₂ (union : EncodedCFG T → EncodedCFG T → EncodedCFG T) :=
  Primrec₂.mk union_primrec

theorem union_computable₂ [Primcodable T] :
    Computable₂ (union : EncodedCFG T → EncodedCFG T → EncodedCFG T) :=
  union_primrec₂.to_comp

/-- Encoded union denotes exactly language union. -/
theorem contextFreeLanguageOf_union (G₁ G₂ : EncodedCFG T) :
    contextFreeLanguageOf (union G₁ G₂) =
      contextFreeLanguageOf G₁ + contextFreeLanguageOf G₂ := by
  unfold contextFreeLanguageOf union
  rw [cf_language_encodeCFG, language_unionGrammar]

/-! ## Concatenation -/

/-- Fresh-start concatenation of two context-free grammars. -/
def concatGrammar (g₁ g₂ : CF_grammar T) : CF_grammar T :=
  { nt := Option (g₁.nt ⊕ g₂.nt)
    initial := none
    rules :=
      (none, [.nonterminal (some (.inl g₁.initial)),
        .nonterminal (some (.inr g₂.initial))]) ::
      g₁.rules.map (lift_rule (some ∘ Sum.inl)) ++
      g₂.rules.map (lift_rule (some ∘ Sum.inr)) }

private theorem concatGrammar_eq_combined (g₁ g₂ : CF_grammar T) :
    concatGrammar g₁ g₂ = combined_grammar g₁ g₂ := by
  have hleft :
      g₁.rules.map (lift_rule (some ∘ Sum.inl)) =
        g₁.rules.map (rule_of_rule₁ (g₂ := g₂)) := by
    apply List.map_congr_left
    rintro ⟨A, rhs⟩ _
    simp [rule_of_rule₁, lift_rule, lsTN_of_lsTN₁_eq_lift_string]
  have hright :
      g₂.rules.map (lift_rule (some ∘ Sum.inr)) =
        g₂.rules.map (rule_of_rule₂ (g₁ := g₁)) := by
    apply List.map_congr_left
    rintro ⟨A, rhs⟩ _
    simp [rule_of_rule₂, lift_rule, lsTN_of_lsTN₂_eq_lift_string]
  simp only [concatGrammar, combined_grammar]
  rw [hleft, hright]
  rfl

theorem language_concatGrammar (g₁ g₂ : CF_grammar T) :
    CF_language (concatGrammar g₁ g₂) =
      CF_language g₁ * CF_language g₂ := by
  rw [concatGrammar_eq_combined, CF_language_combined_grammar]

/-- Fully explicit raw concatenation code. -/
def concatRaw (G₁ G₂ : EncodedCFG T) : EncodedCFG T :=
  (G₁.ntCount + G₂.ntCount, 0,
    (0, [.inl (G₁.initialIdx % G₁.ntCount + 1),
      .inl (G₁.ntCount + G₂.initialIdx % G₂.ntCount + 1)]) ::
    G₁.rawRules.map (shiftRawRule G₁.ntCount 0) ++
    G₂.rawRules.map (shiftRawRule G₂.ntCount G₁.ntCount))

/-- Encoded concatenation obtained by normalizing both nonterminal blocks. -/
def concat (G₁ G₂ : EncodedCFG T) : EncodedCFG T :=
  ContextFree.EncodedCFG.encodeCFG
    (concatGrammar G₁.toCFGrammar G₂.toCFGrammar) (unionNTEq G₁ G₂)

private theorem concat_eq_concatRaw (G₁ G₂ : EncodedCFG T) :
    concat G₁ G₂ = concatRaw G₁ G₂ := by
  rcases G₁ with ⟨n₁, i₁, r₁⟩
  rcases G₂ with ⟨n₂, i₂, r₂⟩
  simp [concat, concatRaw, concatGrammar, unionNTEq, shiftRawRule,
    shiftRawSymbol, ContextFree.EncodedCFG.encodeCFG,
    EncodedCFG.toCFGrammar, EncodedCFG.toNT, EncodedCFG.toSymbol,
    EncodedCFG.ntCount, EncodedCFG.numNT, EncodedCFG.initialIdx,
    EncodedCFG.rawRules, ContextFree.EncodedCFG.encodeSymbol,
    lift_rule, lift_string, lift_symbol, List.map_map, Function.comp_def,
    finSuccEquiv_symm_some, finSumFinEquiv_apply_left,
    finSumFinEquiv_apply_right]
  congr 3
  congr 2 <;> funext x
  all_goals
    rcases x with ⟨A, rhs⟩
    unfold shiftRawRule
    apply Prod.ext
    · simp [EncodedCFG.ntCount, EncodedCFG.numNT]
    · apply List.map_congr_left
      intro s _
      cases s <;>
        simp [shiftRawSymbol, EncodedCFG.toSymbol, EncodedCFG.toNT,
          EncodedCFG.ntCount, EncodedCFG.numNT,
          finSuccEquiv_symm_some, finSumFinEquiv_apply_left,
          finSumFinEquiv_apply_right]

theorem concatRaw_primrec [Primcodable T] :
    Primrec (fun p : EncodedCFG T × EncodedCFG T =>
      concatRaw p.1 p.2) := by
  have hc₁ : Primrec (fun p : EncodedCFG T × EncodedCFG T =>
      p.1.ntCount) := ntCount_primrec.comp Primrec.fst
  have hc₂ : Primrec (fun p : EncodedCFG T × EncodedCFG T =>
      p.2.ntCount) := ntCount_primrec.comp Primrec.snd
  have hi₁ : Primrec (fun p : EncodedCFG T × EncodedCFG T =>
      p.1.initialIdx) := initialIdx_primrec.comp Primrec.fst
  have hi₂ : Primrec (fun p : EncodedCFG T × EncodedCFG T =>
      p.2.initialIdx) := initialIdx_primrec.comp Primrec.snd
  have hfirstIdx : Primrec (fun p : EncodedCFG T × EncodedCFG T =>
      p.1.initialIdx % p.1.ntCount + 1) :=
    Primrec.nat_add.comp (Primrec.nat_mod.comp hi₁ hc₁)
      (Primrec.const 1)
  have hsecondIdx : Primrec (fun p : EncodedCFG T × EncodedCFG T =>
      p.1.ntCount + p.2.initialIdx % p.2.ntCount + 1) :=
    Primrec.nat_add.comp
      (Primrec.nat_add.comp hc₁ (Primrec.nat_mod.comp hi₂ hc₂))
      (Primrec.const 1)
  have hstartRule : Primrec (fun p : EncodedCFG T × EncodedCFG T =>
      ((0, [.inl (p.1.initialIdx % p.1.ntCount + 1),
        .inl (p.1.ntCount + p.2.initialIdx % p.2.ntCount + 1)]) :
        ℕ × List (ℕ ⊕ T))) :=
    Primrec.pair (Primrec.const 0)
      (Primrec.list_cons.comp (Primrec.sumInl.comp hfirstIdx)
        (Primrec.list_cons.comp (Primrec.sumInl.comp hsecondIdx)
          (Primrec.const [])))
  have hleft : Primrec (fun p : EncodedCFG T × EncodedCFG T =>
      p.1.rawRules.map (shiftRawRule p.1.ntCount 0)) :=
    mapShiftedRules_primrec.comp
      (Primrec.pair (Primrec.pair hc₁ (Primrec.const 0))
        (rawRules_primrec.comp Primrec.fst))
  have hright : Primrec (fun p : EncodedCFG T × EncodedCFG T =>
      p.2.rawRules.map
        (shiftRawRule p.2.ntCount p.1.ntCount)) :=
    mapShiftedRules_primrec.comp
      (Primrec.pair (Primrec.pair hc₂ hc₁)
        (rawRules_primrec.comp Primrec.snd))
  have htail : Primrec (fun p : EncodedCFG T × EncodedCFG T =>
      p.1.rawRules.map (shiftRawRule p.1.ntCount 0) ++
        p.2.rawRules.map
          (shiftRawRule p.2.ntCount p.1.ntCount)) :=
    Primrec.list_append.comp hleft hright
  have hrules : Primrec (fun p : EncodedCFG T × EncodedCFG T =>
      (0, [.inl (p.1.initialIdx % p.1.ntCount + 1),
        .inl (p.1.ntCount + p.2.initialIdx % p.2.ntCount + 1)]) ::
      p.1.rawRules.map (shiftRawRule p.1.ntCount 0) ++
        p.2.rawRules.map
          (shiftRawRule p.2.ntCount p.1.ntCount)) :=
    Primrec.list_cons.comp hstartRule htail
  exact Primrec.pair (Primrec.nat_add.comp hc₁ hc₂)
    (Primrec.pair (Primrec.const 0) hrules)

theorem concat_primrec [Primcodable T] :
    Primrec (fun p : EncodedCFG T × EncodedCFG T =>
      concat p.1 p.2) :=
  concatRaw_primrec.of_eq fun p =>
    (concat_eq_concatRaw p.1 p.2).symm

theorem concat_primrec₂ [Primcodable T] :
    Primrec₂ (concat : EncodedCFG T → EncodedCFG T → EncodedCFG T) :=
  Primrec₂.mk concat_primrec

theorem concat_computable₂ [Primcodable T] :
    Computable₂ (concat : EncodedCFG T → EncodedCFG T → EncodedCFG T) :=
  concat_primrec₂.to_comp

theorem contextFreeLanguageOf_concat (G₁ G₂ : EncodedCFG T) :
    contextFreeLanguageOf (concat G₁ G₂) =
      contextFreeLanguageOf G₁ * contextFreeLanguageOf G₂ := by
  unfold contextFreeLanguageOf concat
  rw [cf_language_encodeCFG, language_concatGrammar]

/-! ## A single isolated epsilon start rule -/

/-- Add a fresh start nonterminal with the two rules `S₀ → ε` and
`S₀ → S`. -/
def addEpsilonStartGrammar (g : CF_grammar T) : CF_grammar T :=
  { nt := Option g.nt
    initial := none
    rules :=
      (none, []) ::
      (none, [.nonterminal (some g.initial)]) ::
      g.rules.map (lift_rule some) }

private theorem grammar_of_cfg_addEpsilonStartGrammar (g : CF_grammar T) :
    grammar_of_cfg (addEpsilonStartGrammar g) =
      ContextSensitiveEmptyWord.addEmpty_grammar (grammar_of_cfg g) := by
  simp only [addEpsilonStartGrammar, grammar_of_cfg,
    ContextSensitiveEmptyWord.addEmpty_grammar, List.map_cons, List.map_map]
  congr 1

theorem language_addEpsilonStartGrammar (g : CF_grammar T) :
    CF_language (addEpsilonStartGrammar g) = {[]} + CF_language g := by
  rw [CF_language_eq_grammar_language, grammar_of_cfg_addEpsilonStartGrammar,
    ContextSensitiveEmptyWord.grammar_language_addEmpty]
  ext w
  rw [Language.mem_add, CF_language_eq_grammar_language]
  change (w = [] ∨ grammar_language (grammar_of_cfg g) w) ↔
    (w = [] ∨ grammar_language (grammar_of_cfg g) w)
  rfl

def addEpsilonStartNTEq (G : EncodedCFG T) :
    Option (Fin G.ntCount) ≃ Fin (G.ntCount + 1) :=
  (finSuccEquiv G.ntCount).symm

/-- Raw form of `addEpsilonStart`: exactly one empty right-hand side, followed
by a nonempty routing rule and normalized, shifted source rules. -/
def addEpsilonStartRaw (G : EncodedCFG T) : EncodedCFG T :=
  (G.ntCount, 0,
    (0, []) ::
    (0, [.inl (G.initialIdx % G.ntCount + 1)]) ::
    G.rawRules.map (shiftRawRule G.ntCount 0))

def addEpsilonStart (G : EncodedCFG T) : EncodedCFG T :=
  ContextFree.EncodedCFG.encodeCFG
    (addEpsilonStartGrammar G.toCFGrammar) (addEpsilonStartNTEq G)

private theorem addEpsilonStart_eq_raw (G : EncodedCFG T) :
    addEpsilonStart G = addEpsilonStartRaw G := by
  rcases G with ⟨n, i, rules⟩
  simp [addEpsilonStart, addEpsilonStartRaw, addEpsilonStartGrammar,
    addEpsilonStartNTEq, shiftRawRule, shiftRawSymbol,
    ContextFree.EncodedCFG.encodeCFG, ContextFree.EncodedCFG.encodeSymbol,
    EncodedCFG.toCFGrammar, EncodedCFG.toNT, EncodedCFG.toSymbol,
    EncodedCFG.ntCount, EncodedCFG.numNT, EncodedCFG.initialIdx,
    EncodedCFG.rawRules, lift_rule, lift_string, lift_symbol,
    List.map_map, Function.comp_def, finSuccEquiv_symm_some]
  congr 3
  congr 2
  funext r
  rcases r with ⟨A, rhs⟩
  unfold shiftRawRule
  apply Prod.ext
  · simp
  · apply List.map_congr_left
    intro s _
    cases s <;> simp [shiftRawSymbol]

theorem addEpsilonStartRaw_primrec [Primcodable T] :
    Primrec (addEpsilonStartRaw : EncodedCFG T → EncodedCFG T) := by
  have hc : Primrec (fun G : EncodedCFG T => G.ntCount) := ntCount_primrec
  have hi : Primrec (fun G : EncodedCFG T => G.initialIdx) := initialIdx_primrec
  have hidx : Primrec (fun G : EncodedCFG T => G.initialIdx % G.ntCount + 1) :=
    Primrec.nat_add.comp (Primrec.nat_mod.comp hi hc) (Primrec.const 1)
  have hroute : Primrec (fun G : EncodedCFG T =>
      ((0, [Sum.inl (G.initialIdx % G.ntCount + 1)]) : ℕ × List (ℕ ⊕ T))) :=
    Primrec.pair (Primrec.const 0)
      (Primrec.list_cons.comp (Primrec.sumInl.comp hidx) (Primrec.const []))
  have hshifted : Primrec (fun G : EncodedCFG T =>
      G.rawRules.map (shiftRawRule G.ntCount 0)) :=
    mapShiftedRules_primrec.comp
      (Primrec.pair (Primrec.pair hc (Primrec.const 0)) rawRules_primrec)
  have hrules : Primrec (fun G : EncodedCFG T =>
      (0, []) :: (0, [.inl (G.initialIdx % G.ntCount + 1)]) ::
        G.rawRules.map (shiftRawRule G.ntCount 0)) :=
    Primrec.list_cons.comp (Primrec.const (0, []))
      (Primrec.list_cons.comp hroute hshifted)
  exact Primrec.pair hc (Primrec.pair (Primrec.const 0) hrules)

theorem addEpsilonStart_primrec [Primcodable T] :
    Primrec (addEpsilonStart : EncodedCFG T → EncodedCFG T) :=
  addEpsilonStartRaw_primrec.of_eq fun G => (addEpsilonStart_eq_raw G).symm

theorem addEpsilonStart_computable [Primcodable T] :
    Computable (addEpsilonStart : EncodedCFG T → EncodedCFG T) :=
  addEpsilonStart_primrec.to_comp

theorem contextFreeLanguageOf_addEpsilonStart (G : EncodedCFG T) :
    contextFreeLanguageOf (addEpsilonStart G) = {[]} + contextFreeLanguageOf G := by
  unfold contextFreeLanguageOf addEpsilonStart
  rw [cf_language_encodeCFG, language_addEpsilonStartGrammar]

/-! ## Syntactic invariants -/

/-- Every encoded production has a nonempty right-hand side. -/
def NoEmptyRHS (G : EncodedCFG T) : Prop :=
  ∀ r ∈ G.rawRules, r.2 ≠ []

/-- The (raw) initial nonterminal does not occur on any right-hand side. -/
def InitialNotOnRawRHS (G : EncodedCFG T) : Prop :=
  ∀ r ∈ G.rawRules, Sum.inl G.initialIdx ∉ r.2

/-- Encoding a finite-nonterminal grammar with no epsilon productions preserves
that syntactic invariant at the raw-code level. -/
theorem noEmptyRHS_encodeCFG {k : ℕ} (g : CF_grammar T)
    (e : g.nt ≃ Fin (k + 1)) (hfree : CF_no_epsilon g) :
    NoEmptyRHS (ContextFree.EncodedCFG.encodeCFG g e) := by
  intro r hr
  change r ∈ g.rules.map
    (fun r => ((e r.1).val,
      r.2.map (ContextFree.EncodedCFG.encodeSymbol (⇑e)))) at hr
  obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.mp hr
  cases hright : r₀.2 with
  | nil => exact ((hfree r₀ hr₀) hright).elim
  | cons a rhs => simp

/-- Every context-free language has an encoded epsilon-free presentation of
its positive-length part.  This existential form is useful for choosing the
fixed grammar components in computable reductions: once chosen, each code is
a genuine computable constant. -/
theorem exists_noEmptyRHS_code [DecidableEq T] {L : Language T}
    (hL : is_CF L) :
    ∃ G : EncodedCFG T, NoEmptyRHS G ∧
      contextFreeLanguageOf G = L \ ({[]} : Set (List T)) := by
  classical
  rw [is_CF_iff_isContextFree] at hL
  obtain ⟨g₀, hfinite, hlanguage⟩ :=
    ContextFreeGrammar.exists_fintype_nt L hL
  letI : Fintype g₀.NT := hfinite
  let g := cfg_of_mathlib_cfg g₀.eliminateEmpty
  letI : Fintype g.nt := hfinite
  have hfree : CF_no_epsilon g := by
    intro r hr
    simp only [g, cfg_of_mathlib_cfg, ContextFreeGrammar.eliminateEmpty,
      List.mem_map, Finset.mem_toList] at hr
    obtain ⟨r₀, hr₀, rfl⟩ := hr
    have hne : r₀.output ≠ [] :=
      ContextFreeGrammar.output_mem_removeNullables hr₀
    simpa [lssymbol_of_lsSymbol] using hne
  have hpositive : 0 < Fintype.card g.nt :=
    Fintype.card_pos_iff.mpr ⟨g.initial⟩
  let e : g.nt ≃ Fin (Fintype.card g.nt - 1 + 1) :=
    (Fintype.equivFin g.nt).trans
      (finCongr (Nat.succ_pred_eq_of_pos hpositive).symm)
  let G := ContextFree.EncodedCFG.encodeCFG g e
  refine ⟨G, noEmptyRHS_encodeCFG g e hfree, ?_⟩
  unfold contextFreeLanguageOf G
  rw [ContextFree.EncodedCFG.cf_language_encodeCFG,
    ← mathlib_language_eq_CF_language,
    ← ContextFreeGrammar.eliminateEmpty_correct, hlanguage]

theorem shiftRawRule_rhs_ne_nil {count offset : ℕ}
    {r : ℕ × List (ℕ ⊕ T)} (hr : r.2 ≠ []) :
    (shiftRawRule count offset r).2 ≠ [] := by
  simp [shiftRawRule, hr]

theorem noEmptyRHS_concat {G₁ G₂ : EncodedCFG T}
    (h₁ : NoEmptyRHS G₁) (h₂ : NoEmptyRHS G₂) :
    NoEmptyRHS (concat G₁ G₂) := by
  rw [concat_eq_concatRaw]
  intro r hr
  simp only [concatRaw, EncodedCFG.rawRules, List.mem_cons,
    List.mem_append, List.mem_map] at hr
  rcases hr with (hstart | hleft) | hright
  · subst r
    simp
  · obtain ⟨r₀, hr₀, rfl⟩ := hleft
    exact shiftRawRule_rhs_ne_nil (h₁ r₀ hr₀)
  · obtain ⟨r₀, hr₀, rfl⟩ := hright
    exact shiftRawRule_rhs_ne_nil (h₂ r₀ hr₀)

theorem noEmptyRHS_union {G₁ G₂ : EncodedCFG T}
    (h₁ : NoEmptyRHS G₁) (h₂ : NoEmptyRHS G₂) :
    NoEmptyRHS (union G₁ G₂) := by
  rw [union_eq_unionRaw]
  intro r hr
  simp only [unionRaw, EncodedCFG.rawRules, List.mem_cons,
    List.mem_append, List.mem_map] at hr
  rcases hr with (rfl | rfl | ⟨r₀, hr₀, rfl⟩) | ⟨r₀, hr₀, rfl⟩
  · simp
  · simp
  · exact shiftRawRule_rhs_ne_nil (h₁ r₀ hr₀)
  · exact shiftRawRule_rhs_ne_nil (h₂ r₀ hr₀)

/-! ## Injective changes of terminal alphabet -/

section TerminalMap

variable {A B : Type}

/-- Map the terminal occurrences in one raw CFG symbol, retaining numeric
nonterminal names literally. -/
def mapRawTerminalSymbol (f : A → B) : ℕ ⊕ A → ℕ ⊕ B
  | .inl N => .inl N
  | .inr a => .inr (f a)

/-- Map the terminal occurrences in one raw CFG rule. -/
def mapRawTerminalRule (f : A → B)
    (r : ℕ × List (ℕ ⊕ A)) : ℕ × List (ℕ ⊕ B) :=
  (r.1, r.2.map (mapRawTerminalSymbol f))

/-- Literal terminal relabelling of an encoded context-free grammar.  Numeric
nonterminal names, the initial name, and the declared nonterminal count are
unchanged. -/
def mapTerminals (f : A → B) (G : EncodedCFG A) : EncodedCFG B :=
  (G.numNT, G.initialIdx, G.rawRules.map (mapRawTerminalRule f))

/-- Semantic terminal relabelling of a decoded context-free grammar. -/
private def mapCFGrammar (f : A → B) (g : CF_grammar A) : CF_grammar B where
  nt := g.nt
  initial := g.initial
  rules := g.rules.map fun r =>
    (r.1, r.2.map (map_symbol_fn f))

private theorem grammar_of_cfg_mapCFGrammar (f : A → B)
    (g : CF_grammar A) :
    grammar_of_cfg (mapCFGrammar f g) =
      map_grammar (grammar_of_cfg g) f := by
  simp [mapCFGrammar, grammar_of_cfg, map_grammar, List.map_map,
    Function.comp_def]

private theorem toCFGrammar_mapTerminals (f : A → B)
    (G : EncodedCFG A) :
    (mapTerminals f G).toCFGrammar = mapCFGrammar f G.toCFGrammar := by
  rcases G with ⟨numNT, initial, rules⟩
  simp [mapTerminals, mapRawTerminalRule, mapRawTerminalSymbol,
    mapCFGrammar, EncodedCFG.toCFGrammar, EncodedCFG.toSymbol,
    EncodedCFG.toNT, EncodedCFG.ntCount, EncodedCFG.numNT,
    EncodedCFG.initialIdx, EncodedCFG.rawRules, List.map_map,
    Function.comp_def, map_symbol_fn]

/-- An injective literal terminal relabelling denotes exactly the
letter-to-letter image of the source language.  A left inverse is accepted as
the useful data form of injectivity. -/
theorem contextFreeLanguageOf_mapTerminals_of_leftInverse
    (G : EncodedCFG A) {f : A → B} {g : B → A}
    (hgf : Function.LeftInverse g f) :
    contextFreeLanguageOf (mapTerminals f G) =
      Language.map f (contextFreeLanguageOf G) := by
  unfold contextFreeLanguageOf
  rw [toCFGrammar_mapTerminals, CF_language_eq_grammar_language,
    grammar_of_cfg_mapCFGrammar,
    map_grammar_language_of_leftInverse (grammar_of_cfg G.toCFGrammar) hgf,
    ← CF_language_eq_grammar_language]

/-- Injective form of `contextFreeLanguageOf_mapTerminals_of_leftInverse`. -/
theorem contextFreeLanguageOf_mapTerminals [Nonempty A] (G : EncodedCFG A)
    {f : A → B} (hf : Function.Injective f) :
    contextFreeLanguageOf (mapTerminals f G) =
      Language.map f (contextFreeLanguageOf G) :=
  contextFreeLanguageOf_mapTerminals_of_leftInverse G
    (Function.leftInverse_invFun hf)

theorem mapRawTerminalSymbol_primrec [Primcodable A] [Primcodable B]
    {f : A → B} (hf : Primrec f) :
    Primrec (mapRawTerminalSymbol f : ℕ ⊕ A → ℕ ⊕ B) := by
  refine (Primrec.sumCasesOn
    (f := fun s : ℕ ⊕ A => s)
    (g := fun _ N => Sum.inl N)
    (h := fun _ a => Sum.inr (f a))
    Primrec.id ?_ ?_).of_eq ?_
  · exact Primrec₂.mk (Primrec.sumInl.comp Primrec.snd)
  · exact Primrec₂.mk
      (Primrec.sumInr.comp (hf.comp Primrec.snd))
  · intro s
    cases s <;> rfl

theorem mapRawTerminalRule_primrec [Primcodable A] [Primcodable B]
    {f : A → B} (hf : Primrec f) :
    Primrec (mapRawTerminalRule f :
      (ℕ × List (ℕ ⊕ A)) → ℕ × List (ℕ ⊕ B)) := by
  have hrhs : Primrec (fun r : ℕ × List (ℕ ⊕ A) =>
      r.2.map (mapRawTerminalSymbol f)) := by
    apply Primrec.list_map Primrec.snd
    exact Primrec₂.mk
      ((mapRawTerminalSymbol_primrec hf).comp Primrec.snd)
  exact Primrec.pair Primrec.fst hrhs

/-- Terminal relabelling is primitive recursive for every fixed primitive
recursive letter map. -/
theorem mapTerminals_primrec [Primcodable A] [Primcodable B]
    {f : A → B} (hf : Primrec f) :
    Primrec (mapTerminals f : EncodedCFG A → EncodedCFG B) := by
  have hrules : Primrec (fun G : EncodedCFG A =>
      G.rawRules.map (mapRawTerminalRule f)) := by
    apply Primrec.list_map rawRules_primrec
    exact Primrec₂.mk
      ((mapRawTerminalRule_primrec hf).comp Primrec.snd)
  exact Primrec.pair
    (Primrec.fst)
    (Primrec.pair initialIdx_primrec hrules)

theorem mapTerminals_computable [Primcodable A] [Primcodable B]
    {f : A → B} (hf : Primrec f) :
    Computable (mapTerminals f : EncodedCFG A → EncodedCFG B) :=
  (mapTerminals_primrec hf).to_comp

/-- Literal terminal relabelling neither creates nor removes empty
right-hand sides. -/
theorem noEmptyRHS_mapTerminals {f : A → B} {G : EncodedCFG A}
    (hG : NoEmptyRHS G) : NoEmptyRHS (mapTerminals f G) := by
  intro r hr
  change r ∈ G.rawRules.map (mapRawTerminalRule f) at hr
  obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.mp hr
  intro hnil
  exact hG r₀ hr₀ (List.map_eq_nil_iff.mp hnil)

end TerminalMap

theorem addEpsilonStart_initialIdx (G : EncodedCFG T) :
    (addEpsilonStart G).initialIdx = 0 := by
  rw [addEpsilonStart_eq_raw]
  rfl

theorem addEpsilonStart_rawRules (G : EncodedCFG T) :
    (addEpsilonStart G).rawRules =
      (0, []) ::
      (0, [.inl (G.initialIdx % G.ntCount + 1)]) ::
      G.rawRules.map (shiftRawRule G.ntCount 0) := by
  rw [addEpsilonStart_eq_raw]
  rfl

/-- The fresh start is absent from every right-hand side, independently of
whether the source grammar has epsilon rules. -/
theorem addEpsilonStart_initialNotOnRawRHS (G : EncodedCFG T) :
    InitialNotOnRawRHS (addEpsilonStart G) := by
  intro r hr
  rw [addEpsilonStart_initialIdx]
  rw [addEpsilonStart_rawRules] at hr
  simp only [List.mem_cons, List.mem_map] at hr
  rcases hr with rfl | rfl | ⟨r₀, hr₀, rfl⟩
  · simp
  · simp
  · intro hmem
    simp only [shiftRawRule, Prod.snd, List.mem_map] at hmem
    obtain ⟨s, _, hs⟩ := hmem
    cases s <;> simp [shiftRawSymbol] at hs

/-- If the source is epsilon-free, the wrapper's distinguished rule is its
only empty-output production. -/
theorem addEpsilonStart_empty_rhs_iff {G : EncodedCFG T} (hG : NoEmptyRHS G)
    {r : ℕ × List (ℕ ⊕ T)} (hr : r ∈ (addEpsilonStart G).rawRules) :
    r.2 = [] ↔ r = (0, []) := by
  rw [addEpsilonStart_rawRules] at hr
  simp only [List.mem_cons, List.mem_map] at hr
  rcases hr with rfl | rfl | ⟨r₀, hr₀, rfl⟩
  · simp
  · simp
  · have hne := shiftRawRule_rhs_ne_nil
      (count := G.ntCount) (offset := 0) (hG r₀ hr₀)
    constructor
    · exact fun h => (hne h).elim
    · intro h
      have : (shiftRawRule G.ntCount 0 r₀).2 = [] := congrArg Prod.snd h
      exact (hne this).elim

/-! ## Reusing an epsilon-free CFG code as a context-sensitive code -/

/-- Read a raw CFG symbol as an unrestricted-grammar symbol, without changing
its numeric nonterminal name. -/
def rawSymbolToGrammarSymbol : ℕ ⊕ T → symbol T ℕ
  | .inl A => .nonterminal A
  | .inr a => .terminal a

/-- Read a raw CFG production `A → rhs` as the unrestricted rule with empty
left and right contexts and the same numeric nonterminal names. -/
def rawRuleToGrule (r : ℕ × List (ℕ ⊕ T)) : grule T ℕ :=
  { input_L := []
    input_N := r.1
    input_R := []
    output_string := r.2.map rawSymbolToGrammarSymbol }

/-- The literal unrestricted-grammar code carried by an encoded CFG.  In
particular, this does not hide a semantic translation: it maps each raw rule
independently and retains the raw initial index. -/
def toContextSensitiveCode (G : EncodedCFG T) : Code T :=
  (G.rawRules.map rawRuleToGrule, G.initialIdx)

/-- Canonically lift the decoded finite nonterminals into `ℕ`.  This
semantic comparison code is used only to prove the language bridge; the
effective compiler itself remains the literal raw-rule map above. -/
def finiteLiftCode (G : EncodedCFG T) : Code T :=
  ((grammar_of_cfg G.toCFGrammar).rules.map (lift_rule_ Fin.val),
    G.toCFGrammar.initial.val)

/-- Relabeling the decoded finite grammar by `Fin.val` preserves its language. -/
theorem grammar_language_finiteLiftCode (G : EncodedCFG T) :
    grammar_language (ofCode (finiteLiftCode G)) =
      grammar_language (grammar_of_cfg G.toCFGrammar) := by
  let g₀ := grammar_of_cfg G.toCFGrammar
  let liftNT : g₀.nt → ℕ := fun A => A.val
  let sinkNT : ℕ → Option g₀.nt := fun A =>
    if h : A < G.ntCount then some ⟨A, h⟩ else none
  have hliftSink : ∀ A : g₀.nt, sinkNT (liftNT A) = some A := by
    intro A
    simp only [sinkNT, liftNT, dif_pos A.isLt]
    congr 1
  let lg : lifted_grammar_ T :=
    { g₀ := g₀
      g := ofCode (finiteLiftCode G)
      lift_nt := liftNT
      sink_nt := sinkNT
      lift_inj := fun A B h => Fin.ext h
      sink_inj := by
        intro A B hAB
        by_cases hA : A < G.ntCount
        · by_cases hB : B < G.ntCount
          · left
            simp only [sinkNT, dif_pos hA, dif_pos hB,
              Option.some.injEq] at hAB
            exact congrArg Fin.val hAB
          · simp only [sinkNT, dif_pos hA, dif_neg hB] at hAB
            exact (Option.some_ne_none _ hAB).elim
        · right
          simp only [sinkNT, dif_neg hA]
      lift_nt_sink := hliftSink
      corresponding_rules := by
        intro r hr
        exact List.mem_map_of_mem hr
      preimage_of_rules := by
        rintro r ⟨hr, -⟩
        rcases List.mem_map.mp hr with ⟨r₀, hr₀, rfl⟩
        exact ⟨r₀, hr₀, rfl⟩ }
  apply Set.eq_of_subset_of_subset
  · intro w hw
    have hgood : good_string_ (lg := lg)
        [symbol.nonterminal (liftNT g₀.initial)] := by
      intro a ha
      rw [List.mem_singleton] at ha
      subst a
      exact ⟨g₀.initial, hliftSink g₀.initial⟩
    have hsink := sink_deri_ lg
      (w₁ := [symbol.nonterminal (liftNT g₀.initial)])
      (w₂ := w.map symbol.terminal) hw hgood
    rw [sink_string_map_terminal_ sinkNT w] at hsink
    have hstart :
        sink_string_ sinkNT
          ([symbol.nonterminal (liftNT g₀.initial)] : List (symbol T ℕ)) =
            [symbol.nonterminal g₀.initial] := by
      simp [sink_string_, sink_symbol_, hliftSink]
    rw [hstart] at hsink
    exact hsink
  · intro w hw
    have hlift := lift_deri_ lg
      (w₁ := [symbol.nonterminal g₀.initial])
      (w₂ := w.map symbol.terminal) hw
    rw [lift_string_map_terminal_ liftNT w] at hlift
    exact hlift

private theorem toContextSensitiveCode_addEpsilonStart_eq_finiteLiftCode
    (G : EncodedCFG T) :
    toContextSensitiveCode (addEpsilonStart G) =
      finiteLiftCode (addEpsilonStart G) := by
  rw [addEpsilonStart_eq_raw]
  rcases G with ⟨n, i, rules⟩
  simp [toContextSensitiveCode, finiteLiftCode, addEpsilonStartRaw,
    rawRuleToGrule, rawSymbolToGrammarSymbol, grammar_of_cfg,
    EncodedCFG.toCFGrammar, EncodedCFG.toNT, EncodedCFG.toSymbol,
    EncodedCFG.ntCount, EncodedCFG.numNT, EncodedCFG.initialIdx,
    EncodedCFG.rawRules, shiftRawRule, shiftRawSymbol, lift_rule_,
    lift_string_, lift_symbol_, List.map_map, Function.comp_def]
  constructor
  · have hi : i % (n + 1) < n + 1 := Nat.mod_lt _ (by omega)
    symm
    exact Nat.mod_eq_of_lt (by omega)
  · rintro a b _
    constructor
    · have ha : a % (n + 1) < n + 1 := Nat.mod_lt _ (by omega)
      symm
      exact Nat.mod_eq_of_lt (by omega)
    · intro a _
      have ha : a % (n + 1) < n + 1 := Nat.mod_lt _ (by omega)
      symm
      exact Nat.mod_eq_of_lt (by omega)

/-- The literal numeric code of the fresh-start grammar denotes exactly its
decoded context-free language. -/
theorem grammar_language_toContextSensitiveCode_addEpsilonStart
    (G : EncodedCFG T) :
    grammar_language
        (ofCode (toContextSensitiveCode (addEpsilonStart G))) =
      contextFreeLanguageOf (addEpsilonStart G) := by
  rw [toContextSensitiveCode_addEpsilonStart_eq_finiteLiftCode,
    grammar_language_finiteLiftCode]
  exact (CF_language_eq_grammar_language _).symm

theorem rawSymbolToGrammarSymbol_primrec [Primcodable T] :
    Primrec (rawSymbolToGrammarSymbol : ℕ ⊕ T → symbol T ℕ) := by
  refine (Primrec.sumCasesOn
    (f := fun s : ℕ ⊕ T => s)
    (g := fun _ A => symbol.nonterminal A)
    (h := fun _ a => symbol.terminal a)
    Primrec.id ?_ ?_).of_eq ?_
  · exact Primrec₂.mk (primrec_symbol_nonterminal.comp Primrec.snd)
  · exact Primrec₂.mk (primrec_symbol_terminal.comp Primrec.snd)
  · intro s
    cases s <;> rfl

theorem rawRuleToGrule_primrec [Primcodable T] :
    Primrec (rawRuleToGrule : ℕ × List (ℕ ⊕ T) → grule T ℕ) := by
  have hout : Primrec (fun r : ℕ × List (ℕ ⊕ T) =>
      r.2.map rawSymbolToGrammarSymbol) := by
    apply Primrec.list_map Primrec.snd
    exact Primrec₂.mk (rawSymbolToGrammarSymbol_primrec.comp Primrec.snd)
  have htuple : Primrec (fun r : ℕ × List (ℕ ⊕ T) =>
      (([], r.1, [], r.2.map rawSymbolToGrammarSymbol) :
        List (symbol T ℕ) × ℕ × List (symbol T ℕ) ×
          List (symbol T ℕ))) :=
    Primrec.pair (Primrec.const [])
      (Primrec.pair Primrec.fst (Primrec.pair (Primrec.const []) hout))
  have hdecode : Primrec ((gruleEquiv T ℕ).symm) := Primrec.of_equiv_symm
  exact (hdecode.comp htuple).of_eq fun r => by cases r; rfl

/-- Literal conversion from raw CFG codes to unrestricted grammar codes is
primitive recursive. -/
theorem toContextSensitiveCode_primrec [Primcodable T] :
    Primrec (toContextSensitiveCode : EncodedCFG T → Code T) := by
  have hrules : Primrec (fun G : EncodedCFG T =>
      G.rawRules.map rawRuleToGrule) := by
    apply Primrec.list_map rawRules_primrec
    exact Primrec₂.mk (rawRuleToGrule_primrec.comp Primrec.snd)
  exact Primrec.pair hrules initialIdx_primrec

theorem rawRuleToGrule_noncontracting {r : ℕ × List (ℕ ⊕ T)}
    (hr : r.2 ≠ []) : grule_noncontracting (rawRuleToGrule r) := by
  simp only [rawRuleToGrule, grule_noncontracting, List.length_map,
    List.length_nil, zero_add, add_zero]
  exact List.length_pos_of_ne_nil hr

/-- An epsilon-free encoded CFG is literally a noncontracting unrestricted
grammar when its raw productions are read as grammar rules. -/
theorem toContextSensitiveCode_noncontracting {G : EncodedCFG T}
    (hG : NoEmptyRHS G) :
    grammar_noncontracting
      (ofCode (toContextSensitiveCode G)) := by
  intro r hr
  change r ∈ G.rawRules.map rawRuleToGrule at hr
  obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.mp hr
  exact rawRuleToGrule_noncontracting (hG r₀ hr₀)

/-- If the source is epsilon-free, the fresh-start wrapper is a valid
context-sensitive grammar code.  Its sole contracting rule is the isolated
fresh-initial rule `0 → ε`. -/
theorem addEpsilonStart_contextSensitive {G : EncodedCFG T}
    (hG : NoEmptyRHS G) :
    grammar_context_sensitive
      (ofCode
        (toContextSensitiveCode (addEpsilonStart G))) := by
  constructor
  · intro r hr
    change r ∈ (addEpsilonStart G).rawRules.map rawRuleToGrule at hr
    obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.mp hr
    by_cases he : r₀.2 = []
    · left
      have hrule := (addEpsilonStart_empty_rhs_iff hG hr₀).mp he
      subst r₀
      simp [rawRuleToGrule, initial_epsilon_rule,
        toContextSensitiveCode, addEpsilonStart_initialIdx]
    · exact Or.inr (rawRuleToGrule_noncontracting he)
  · intro _
    intro r hr
    change r ∈ (addEpsilonStart G).rawRules.map rawRuleToGrule at hr
    obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.mp hr
    have hnot := addEpsilonStart_initialNotOnRawRHS G r₀ hr₀
    change symbol.nonterminal (addEpsilonStart G).initialIdx ∉
      r₀.2.map rawSymbolToGrammarSymbol
    simpa [rawSymbolToGrammarSymbol] using hnot

section CSCode

variable [DecidableEq T] [Primcodable T]

/-- Package the literal fresh-start rule list as an effective CS code. -/
def addEpsilonStartCSCode (G : EncodedCFG T) (hG : NoEmptyRHS G) :
    ContextSensitive.CSCode T :=
  ⟨toContextSensitiveCode (addEpsilonStart G),
    addEpsilonStart_contextSensitive hG⟩

/-- The bundled context-sensitive compiler preserves the fresh-start CFG
language exactly. -/
theorem contextSensitiveLanguageOf_addEpsilonStartCSCode
    (G : EncodedCFG T) (hG : NoEmptyRHS G) :
    ContextSensitive.contextSensitiveLanguageOf'
        (addEpsilonStartCSCode G hG) =
      contextFreeLanguageOf (addEpsilonStart G) := by
  change contextSensitiveLanguageOf
      (toContextSensitiveCode (addEpsilonStart G)) = _
  rw [ContextSensitive.csLang_eq (addEpsilonStart_contextSensitive hG)]
  exact grammar_language_toContextSensitiveCode_addEpsilonStart G

/-- Uniform compiler form of `addEpsilonStartCSCode`: any primitive-recursive
family of epsilon-free CFG codes gives a primitive-recursive family of bundled
CS codes. -/
theorem addEpsilonStartCSCode_primrec {A : Type} [Primcodable A]
    (f : A → EncodedCFG T) (hf : Primrec f) (hfree : ∀ a, NoEmptyRHS (f a)) :
    Primrec (fun a => addEpsilonStartCSCode (f a) (hfree a)) := by
  exact Primrec.subtype_mk
    (hp := ContextSensitive.primrecPred_isCS)
    (toContextSensitiveCode_primrec.comp (addEpsilonStart_primrec.comp hf))

end CSCode

end ContextFree.EncodedCFG

namespace Regular.EncodedRG

variable {T N : Type}

/-! ## Removing the empty word from a right-regular grammar -/

/-- Expand one right-regular rule during epsilon elimination.  Epsilon rules
are dropped.  A rule `A → a B` additionally yields `A → a` exactly when
`B → ε` is present. -/
def positiveRule [DecidableEq T] [DecidableEq N]
    (rules : List (RG_rule T N)) : RG_rule T N → List (RG_rule T N)
  | .cons A a B =>
      if RG_rule.epsilon B ∈ rules then
        [.cons A a B, .single A a]
      else
        [.cons A a B]
  | .single A a => [.single A a]
  | .epsilon _ => []

/-- A right-regular grammar for the positive-length part of `g`.
The construction preserves every consuming transition, removes all epsilon
rules, and shortcuts a final consuming transition into an accepting state. -/
def positiveGrammar [DecidableEq T] (g : RG_grammar T) [DecidableEq g.nt] :
    RG_grammar T :=
  { nt := g.nt
    initial := g.initial
    rules := g.rules.flatMap (positiveRule g.rules) }

@[simp] theorem cons_mem_positiveGrammar [DecidableEq T]
    (g : RG_grammar T) [DecidableEq g.nt] (A B : g.nt) (a : T) :
    RG_rule.cons A a B ∈ (positiveGrammar g).rules ↔
      RG_rule.cons A a B ∈ g.rules := by
  simp only [positiveGrammar, List.mem_flatMap]
  constructor
  · rintro ⟨r, hr, hmem⟩
    cases r with
    | cons C b D =>
        by_cases he : RG_rule.epsilon D ∈ g.rules
        · have heq : RG_rule.cons A a B = RG_rule.cons C b D := by
            simpa [positiveRule, he] using hmem
          cases heq
          exact hr
        · have heq : RG_rule.cons A a B = RG_rule.cons C b D := by
            simpa [positiveRule, he] using hmem
          cases heq
          exact hr
    | single C b => simp [positiveRule] at hmem
    | epsilon C => simp [positiveRule] at hmem
  · intro hr
    refine ⟨RG_rule.cons A a B, hr, ?_⟩
    by_cases he : RG_rule.epsilon B ∈ g.rules <;> simp [positiveRule, he]

@[simp] theorem epsilon_not_mem_positiveGrammar [DecidableEq T]
    (g : RG_grammar T) [DecidableEq g.nt] (A : g.nt) :
    RG_rule.epsilon A ∉ (positiveGrammar g).rules := by
  simp only [positiveGrammar, List.mem_flatMap, not_exists, not_and]
  intro r _
  cases r with
  | cons C b D =>
      by_cases he : RG_rule.epsilon D ∈ g.rules <;> simp [positiveRule, he]
  | single C b => simp [positiveRule]
  | epsilon C => simp [positiveRule]

@[simp] theorem single_mem_positiveGrammar [DecidableEq T]
    (g : RG_grammar T) [DecidableEq g.nt] (A : g.nt) (a : T) :
    RG_rule.single A a ∈ (positiveGrammar g).rules ↔
      RG_rule.single A a ∈ g.rules ∨
        ∃ B, RG_rule.cons A a B ∈ g.rules ∧ RG_rule.epsilon B ∈ g.rules := by
  simp only [positiveGrammar, List.mem_flatMap]
  constructor
  · rintro ⟨r, hr, hmem⟩
    cases r with
    | cons C b D =>
        by_cases he : RG_rule.epsilon D ∈ g.rules
        · have heq : RG_rule.single A a = RG_rule.single C b := by
            simpa [positiveRule, he] using hmem
          cases heq
          exact Or.inr ⟨D, hr, he⟩
        · simp [positiveRule, he] at hmem
    | single C b =>
        have heq : RG_rule.single A a = RG_rule.single C b := by
          simpa [positiveRule] using hmem
        cases heq
        exact Or.inl hr
    | epsilon C => simp [positiveRule] at hmem
  · rintro (hr | ⟨B, hcons, heps⟩)
    · exact ⟨RG_rule.single A a, hr, by simp [positiveRule]⟩
    · exact ⟨RG_rule.cons A a B, hcons, by simp [positiveRule, heps]⟩

private theorem positiveGrammar_transform_simulates [DecidableEq T]
    (g : RG_grammar T) [DecidableEq g.nt]
    {u v : List (symbol T g.nt)}
    (h : RG_transforms (positiveGrammar g) u v) : RG_derives g u v := by
  unfold RG_transforms at h
  simp only [positiveGrammar] at h
  rcases h with ⟨r, hr, x, y, hu, hv⟩
  cases r with
  | cons A a B =>
      apply RG_deri_of_tran
      exact ⟨RG_rule.cons A a B, (cons_mem_positiveGrammar g A B a).mp hr,
        x, y, hu, hv⟩
  | single A a =>
      rcases (single_mem_positiveGrammar g A a).mp hr with hsingle | ⟨B, hcons, heps⟩
      · apply RG_deri_of_tran
        exact ⟨RG_rule.single A a, hsingle, x, y, hu, hv⟩
      · apply RG_deri_of_deri_tran
          (v := x ++ [symbol.terminal a, symbol.nonterminal B] ++ y)
        · apply RG_deri_of_tran
          exact ⟨RG_rule.cons A a B, hcons, x, y, hu, rfl⟩
        · refine ⟨RG_rule.epsilon B, heps,
            x ++ [symbol.terminal a], y, ?_, ?_⟩
          · simp [RG_rule.lhs, List.append_assoc]
          · simpa [List.append_assoc] using hv
  | epsilon A => exact (epsilon_not_mem_positiveGrammar g A hr).elim

private theorem positiveGrammar_derives_simulates [DecidableEq T]
    (g : RG_grammar T) [DecidableEq g.nt]
    {u v : List (symbol T g.nt)}
    (h : RG_derives (positiveGrammar g) u v) : RG_derives g u v := by
  induction h with
  | refl => exact RG_deri_self g
  | tail _ hstep ih =>
      exact RG_deri_of_deri_deri ih (positiveGrammar_transform_simulates g hstep)

private theorem derives_to_trailing_nonterminal_positive_aux [DecidableEq T]
    (g : RG_grammar T) [DecidableEq g.nt] {A : g.nt}
    {s : List (symbol T g.nt)}
    (h : RG_derives g [symbol.nonterminal A] s) :
    ∀ {w : List T} {B : g.nt},
      s = w.map symbol.terminal ++ [symbol.nonterminal B] →
      RG_derives (positiveGrammar g) [symbol.nonterminal A] s := by
  induction h with
  | refl =>
      intro _ _ _
      exact RG_deri_self (positiveGrammar g)
  | @tail s₁ s₂ hpre hstep ih =>
      intro w B hs
      subst s₂
      rcases RG_derives_form hpre with ⟨p, C, hs₁⟩ | ⟨p, hs₁⟩
      · subst s₁
        have ih' := ih (w := p) (B := C) rfl
        rcases RG_transforms_of_terminal_nt hstep with
          ⟨a, D, hrule, hs₂⟩ | ⟨a, hrule, hs₂⟩ | ⟨hrule, hs₂⟩
        · rw [hs₂]
          apply RG_deri_of_deri_tran ih'
          exact ⟨RG_rule.cons C a D,
            (cons_mem_positiveGrammar g C D a).mpr hrule,
            p.map symbol.terminal, [],
            by simp [RG_rule.lhs], by simp [RG_rule.output]⟩
        · no_nonterminal (symbol.nonterminal B) at hs₂
        · no_nonterminal (symbol.nonterminal B) at hs₂
      · subst s₁
        rcases hstep with ⟨r, _, x, y, hxy, _⟩
        no_nonterminal (symbol.nonterminal r.lhs) at hxy

private theorem derives_to_trailing_nonterminal_positive [DecidableEq T]
    (g : RG_grammar T) [DecidableEq g.nt] {A B : g.nt} {w : List T}
    (h : RG_derives g [symbol.nonterminal A]
      (w.map symbol.terminal ++ [symbol.nonterminal B])) :
    RG_derives (positiveGrammar g) [symbol.nonterminal A]
      (w.map symbol.terminal ++ [symbol.nonterminal B]) :=
  derives_to_trailing_nonterminal_positive_aux g h rfl

/-- Epsilon elimination on a right-regular grammar removes exactly the empty
word. -/
theorem RG_language_positiveGrammar [DecidableEq T]
    (g : RG_grammar T) [DecidableEq g.nt] :
    RG_language (positiveGrammar g) = RG_language g \ ({[]} : Set (List T)) := by
  ext w
  constructor
  · intro hw
    refine ⟨positiveGrammar_derives_simulates g hw, ?_⟩
    simp only [Set.mem_singleton_iff]
    intro hwNil
    have hlast := RG_generates_last_step hw
    rcases hlast with ⟨C, p, _, heps, hwp⟩ | ⟨C, p, a, _, _, hwp⟩
    · exact epsilon_not_mem_positiveGrammar g C heps
    · rw [hwp] at hwNil
      simp at hwNil
  · rintro ⟨hw, hwne⟩
    have hlast := RG_generates_last_step hw
    rcases hlast with ⟨C, p, hp, heps, hwp⟩ | ⟨C, p, a, hp, hsingle, hwp⟩
    · have hpne : p ≠ [] := by
        intro hpNil
        apply hwne
        simp [hwp, hpNil]
      obtain ⟨D, hprefix, hcons⟩ := RG_derives_snoc hpne hp
      have hprefix' := derives_to_trailing_nonterminal_positive g hprefix
      rw [hwp]
      apply RG_deri_of_deri_tran hprefix'
      refine ⟨RG_rule.single D (p.getLast hpne), ?_,
        p.dropLast.map symbol.terminal, [], by simp [RG_rule.lhs], ?_⟩
      · exact (single_mem_positiveGrammar g D (p.getLast hpne)).mpr
          (Or.inr ⟨C, hcons, heps⟩)
      · simp only [RG_rule.output, List.append_nil]
        simpa using congrArg (List.map symbol.terminal)
          (List.dropLast_append_getLast hpne).symm
    · have hp' := derives_to_trailing_nonterminal_positive g hp
      rw [hwp]
      apply RG_deri_of_deri_tran hp'
      exact ⟨RG_rule.single C a,
        (single_mem_positiveGrammar g C a).mpr (Or.inl hsingle),
        p.map symbol.terminal, [], by simp [RG_rule.lhs], by simp [RG_rule.output]⟩

/-! ### The raw encoded compiler -/

/-- Test whether the decoded nonterminal named by `B` has an epsilon rule.
Raw nonterminal names are compared modulo the declared positive count, exactly
as `EncodedRG.toRG` decodes them. -/
def rawHasEpsilon (count : ℕ)
    (rules : List (ℕ × Option (T × Option ℕ))) (B : ℕ) : Bool :=
  rules.any fun r =>
    match r.2 with
    | none => decide (r.1 % count = B % count)
    | some _ => false

/-- Raw rule expansion implementing `positiveRule`. -/
def positiveRawRule (count : ℕ)
    (rules : List (ℕ × Option (T × Option ℕ)))
    (r : ℕ × Option (T × Option ℕ)) :
    List (ℕ × Option (T × Option ℕ)) :=
  match r.2 with
  | none => []
  | some (a, none) => [r]
  | some (a, some B) =>
      bif rawHasEpsilon count rules B then
        [r, (r.1, some (a, none))]
      else
        [r]

/-- Effective right-regular code for the positive-length part. -/
def positivePartRG (c : EncodedRG T) : EncodedRG T :=
  (c.1, c.2.1,
    c.2.2.flatMap (positiveRawRule (c.1 + 1) c.2.2))

/-- The epsilon-free CFG code used by later context-sensitive compilers. -/
def positivePart (c : EncodedRG T) : EncodedCFG T :=
  toCFG (positivePartRG c)

local instance (c : EncodedRG T) : DecidableEq (toRG c).nt := by
  change DecidableEq (Fin (toCFG c).ntCount)
  infer_instance

theorem rawHasEpsilon_eq_true_iff [DecidableEq T] (c : EncodedRG T) (B : ℕ) :
    rawHasEpsilon (c.1 + 1) c.2.2 B = true ↔
      RG_rule.epsilon ((toCFG c).toNT B) ∈ (toRG c).rules := by
  simp only [rawHasEpsilon, List.any_eq_true, Bool.decide_eq_true,
    toRG, List.mem_map]
  constructor
  · rintro ⟨⟨C, body⟩, hr, hbody⟩
    rcases body with _ | ⟨a, next⟩
    · simp only at hbody
      refine ⟨(C, none), hr, ?_⟩
      simp only [rgRuleOf]
      apply congrArg RG_rule.epsilon
      apply Fin.ext
      simpa [EncodedCFG.toNT] using hbody
    · simp at hbody
  · rintro ⟨⟨C, body⟩, hr, heq⟩
    rcases body with _ | ⟨a, next⟩
    · refine ⟨(C, none), hr, ?_⟩
      simp only
      have hnt : (toCFG c).toNT C = (toCFG c).toNT B := by
        simpa [rgRuleOf] using heq
      simpa [EncodedCFG.toNT] using congrArg Fin.val hnt
    · rcases next with _ | D <;> simp [rgRuleOf] at heq

private theorem toRG_positivePartRG [DecidableEq T] (c : EncodedRG T) :
    toRG (positivePartRG c) = positiveGrammar (toRG c) := by
  have htoNT (A : ℕ) :
      (toCFG (positivePartRG c)).toNT A = (toCFG c).toNT A := by
    apply Fin.ext
    rfl
  unfold toRG positivePartRG positiveGrammar
  congr 1
  simp only [List.map_flatMap, List.flatMap_map, Function.comp_def]
  apply List.flatMap_congr
  intro r hr
  rcases r with ⟨A, body⟩
  rcases body with _ | ⟨a, _ | B⟩
  · simp [positiveRawRule, positiveRule, rgRuleOf]
  · simpa [positiveRawRule, positiveRule, rgRuleOf] using htoNT A
  · have hA :
        (toCFG (c.1, c.2.1,
          c.2.2.flatMap (positiveRawRule (c.1 + 1) c.2.2))).toNT A =
          (toCFG c).toNT A := by
        simpa only [positivePartRG] using htoNT A
    have hB :
        (toCFG (c.1, c.2.1,
          c.2.2.flatMap (positiveRawRule (c.1 + 1) c.2.2))).toNT B =
          (toCFG c).toNT B := by
        simpa only [positivePartRG] using htoNT B
    by_cases hraw : rawHasEpsilon (c.1 + 1) c.2.2 B = true
    · have he := (rawHasEpsilon_eq_true_iff c B).mp hraw
      have he' : RG_rule.epsilon ((toCFG c).toNT B) ∈
          List.map (rgRuleOf c) c.2.2 := by
        simpa only [toRG] using he
      simp [positiveRawRule, positiveRule, rgRuleOf, hraw, he', hA, hB]
    · have he : RG_rule.epsilon ((toCFG c).toNT B) ∉ (toRG c).rules :=
        fun h => hraw ((rawHasEpsilon_eq_true_iff c B).mpr h)
      have he' : RG_rule.epsilon ((toCFG c).toNT B) ∉
          List.map (rgRuleOf c) c.2.2 := by
        simpa only [toRG] using he
      simp [positiveRawRule, positiveRule, rgRuleOf, hraw, he', hA, hB]

/-- The encoded compiler denotes exactly the positive-length part of the
source regular language. -/
theorem contextFreeLanguageOf_positivePart [DecidableEq T] (c : EncodedRG T) :
    contextFreeLanguageOf (positivePart c) =
      regularLanguageOf c \ ({[]} : Set (List T)) := by
  change regularLanguageOf (positivePartRG c) =
    regularLanguageOf c \ ({[]} : Set (List T))
  rw [← rgLanguage_toRG, toRG_positivePartRG,
    RG_language_positiveGrammar, rgLanguage_toRG]

/-- Every production emitted by `positivePart` has a nonempty right-hand
side. -/
theorem positivePart_noEmptyRHS (c : EncodedRG T) :
    ContextFree.EncodedCFG.NoEmptyRHS (positivePart c) := by
  intro r hr
  change r ∈ (positivePartRG c).2.2.map
    (fun r => (r.1, bodyToRHS r.2)) at hr
  obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.mp hr
  change r₀ ∈ c.2.2.flatMap (positiveRawRule (c.1 + 1) c.2.2) at hr₀
  obtain ⟨source, _, hsource⟩ := List.mem_flatMap.mp hr₀
  rcases source with ⟨A, body⟩
  rcases body with _ | ⟨a, _ | B⟩
  · simp [positiveRawRule] at hsource
  · simp [positiveRawRule] at hsource
    subst r₀
    simp [bodyToRHS]
  · by_cases he : rawHasEpsilon (c.1 + 1) c.2.2 B = true <;>
      simp [positiveRawRule, he] at hsource
    · rcases hsource with h | h <;> subst r₀ <;> simp [bodyToRHS]
    · subst r₀
      simp [bodyToRHS]

/-! ### Primitive recursiveness -/

theorem rawHasEpsilon_primrec [Primcodable T] :
    Primrec (fun p :
      (ℕ × List (ℕ × Option (T × Option ℕ))) × ℕ =>
        rawHasEpsilon p.1.1 p.1.2 p.2) := by
  apply primrec_list_any (hf := Primrec.snd.comp Primrec.fst)
  apply Primrec₂.mk
  have hcount : Primrec (fun q :
      ((ℕ × List (ℕ × Option (T × Option ℕ))) × ℕ) ×
        (ℕ × Option (T × Option ℕ)) => q.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hlhs : Primrec (fun q :
      ((ℕ × List (ℕ × Option (T × Option ℕ))) × ℕ) ×
        (ℕ × Option (T × Option ℕ)) => q.2.1) :=
    Primrec.fst.comp Primrec.snd
  have htarget : Primrec (fun q :
      ((ℕ × List (ℕ × Option (T × Option ℕ))) × ℕ) ×
        (ℕ × Option (T × Option ℕ)) => q.1.2) :=
    Primrec.snd.comp Primrec.fst
  have heq : Primrec (fun q :
      ((ℕ × List (ℕ × Option (T × Option ℕ))) × ℕ) ×
        (ℕ × Option (T × Option ℕ)) =>
      decide (q.2.1 % q.1.1.1 = q.1.2 % q.1.1.1)) :=
    Primrec.beq.comp (Primrec.nat_mod.comp hlhs hcount)
      (Primrec.nat_mod.comp htarget hcount)
  refine (Primrec.option_casesOn
    (o := fun q :
      ((ℕ × List (ℕ × Option (T × Option ℕ))) × ℕ) ×
        (ℕ × Option (T × Option ℕ)) => q.2.2)
    (f := fun q => decide (q.2.1 % q.1.1.1 = q.1.2 % q.1.1.1))
    (g := fun _ _ => false)
    (Primrec.snd.comp Primrec.snd) heq
    (Primrec₂.mk (Primrec.const false))).of_eq ?_
  intro q
  rcases q.2.2 with _ | body <;> rfl

abbrev RawRGRule (T : Type) := ℕ × Option (T × Option ℕ)
abbrev RawRGMeta (T : Type) := ℕ × List (RawRGRule T)

/-- The consuming-rule branch of `positiveRawRule`, separated so its
primitive-recursive proof does not carry a redundant nested option. -/
def positiveConsRaw (m : RawRGMeta T) (data : ℕ × T × ℕ) :
    List (RawRGRule T) :=
  bif rawHasEpsilon m.1 m.2 data.2.2 then
    [(data.1, some (data.2.1, some data.2.2)),
      (data.1, some (data.2.1, none))]
  else
    [(data.1, some (data.2.1, some data.2.2))]

theorem positiveConsRaw_primrec [Primcodable T] :
    Primrec (fun p : RawRGMeta T × (ℕ × T × ℕ) =>
      positiveConsRaw p.1 p.2) := by
  have hhas : Primrec (fun p : RawRGMeta T × (ℕ × T × ℕ) =>
      rawHasEpsilon p.1.1 p.1.2 p.2.2.2) :=
    rawHasEpsilon_primrec.comp
      (Primrec.pair Primrec.fst (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hA : Primrec (fun p : RawRGMeta T × (ℕ × T × ℕ) => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have ha : Primrec (fun p : RawRGMeta T × (ℕ × T × ℕ) => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hB : Primrec (fun p : RawRGMeta T × (ℕ × T × ℕ) => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have horiginal : Primrec (fun p : RawRGMeta T × (ℕ × T × ℕ) =>
      ((p.2.1, some (p.2.2.1, some p.2.2.2)) : RawRGRule T)) :=
    Primrec.pair hA
      (Primrec.option_some.comp
        (Primrec.pair ha (Primrec.option_some.comp hB)))
  have hshortcut : Primrec (fun p : RawRGMeta T × (ℕ × T × ℕ) =>
      ((p.2.1, some (p.2.2.1, none)) : RawRGRule T)) :=
    Primrec.pair hA
      (Primrec.option_some.comp (Primrec.pair ha (Primrec.const none)))
  have hone : Primrec (fun p : RawRGMeta T × (ℕ × T × ℕ) =>
      [((p.2.1, some (p.2.2.1, some p.2.2.2)) : RawRGRule T)]) :=
    Primrec.list_cons.comp horiginal (Primrec.const [])
  have htwo : Primrec (fun p : RawRGMeta T × (ℕ × T × ℕ) =>
      [((p.2.1, some (p.2.2.1, some p.2.2.2)) : RawRGRule T),
        (p.2.1, some (p.2.2.1, none))]) :=
    Primrec.list_cons.comp horiginal
      (Primrec.list_cons.comp hshortcut (Primrec.const []))
  exact (Primrec.cond hhas htwo hone).of_eq fun p => by
    unfold positiveConsRaw
    rfl

theorem positiveRawRule_primrec [Primcodable T] :
    Primrec (fun p : RawRGMeta T × RawRGRule T =>
      positiveRawRule p.1.1 p.1.2 p.2) := by
  have hsome : Primrec (fun z :
      (RawRGMeta T × RawRGRule T) × (T × Option ℕ) =>
      match z.2.2 with
      | none => [z.1.2]
      | some B => positiveConsRaw z.1.1 (z.1.2.1, z.2.1, B)) := by
    have hnone : Primrec (fun z :
        (RawRGMeta T × RawRGRule T) × (T × Option ℕ) => [z.1.2]) :=
      Primrec.list_cons.comp (Primrec.snd.comp Primrec.fst) (Primrec.const [])
    have hbranch : Primrec (fun q :
        ((RawRGMeta T × RawRGRule T) × (T × Option ℕ)) × ℕ =>
        positiveConsRaw q.1.1.1 (q.1.1.2.1, q.1.2.1, q.2)) :=
      positiveConsRaw_primrec.comp
        (Primrec.pair
          (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.pair
            (Primrec.fst.comp
              (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
            (Primrec.pair
              (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd)))
    refine (Primrec.option_casesOn
      (o := fun z : (RawRGMeta T × RawRGRule T) × (T × Option ℕ) => z.2.2)
      (f := fun z => [z.1.2])
      (g := fun z B => positiveConsRaw z.1.1 (z.1.2.1, z.2.1, B))
      (Primrec.snd.comp Primrec.snd) hnone (Primrec₂.mk hbranch)).of_eq ?_
    intro z
    rcases z.2.2 with _ | B <;> rfl
  refine (Primrec.option_casesOn
    (o := fun p : RawRGMeta T × RawRGRule T => p.2.2)
    (f := fun _ => ([] : List (RawRGRule T)))
    (g := fun p body =>
      match body.2 with
      | none => [p.2]
      | some B => positiveConsRaw p.1 (p.2.1, body.1, B))
    (Primrec.snd.comp Primrec.snd) (Primrec.const [])
    (Primrec₂.mk hsome)).of_eq ?_
  rintro ⟨⟨count, rules⟩, A, body⟩
  rcases body with _ | ⟨a, next⟩
  · rfl
  · rcases next with _ | B
    · rfl
    · simp only [positiveRawRule, positiveConsRaw]

theorem positivePartRG_primrec [Primcodable T] :
    Primrec (positivePartRG : EncodedRG T → EncodedRG T) := by
  have hrules : Primrec (fun c : EncodedRG T => c.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hflat : Primrec (fun c : EncodedRG T =>
      c.2.2.flatMap (positiveRawRule (c.1 + 1) c.2.2)) := by
    apply Primrec.list_flatMap hrules
    apply Primrec₂.mk
    exact positiveRawRule_primrec.comp
      (Primrec.pair
        (Primrec.pair
          (Primrec.succ.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
        Primrec.snd)
  exact Primrec.pair Primrec.fst
    (Primrec.pair (Primrec.fst.comp Primrec.snd) hflat)

theorem positivePart_primrec [Primcodable T] :
    Primrec (positivePart : EncodedRG T → EncodedCFG T) :=
  toCFG_primrec.comp positivePartRG_primrec

theorem positivePart_computable [Primcodable T] :
    Computable (positivePart : EncodedRG T → EncodedCFG T) :=
  positivePart_primrec.to_comp

end Regular.EncodedRG

namespace ContextFree.EncodedCFG

/-! ## Completing an embedded alphabet -/

section AlphabetCompletion

variable {A B : Type}

/-- Words that contain at least one letter outside the image of `f`. -/
def outsideImageLanguage (f : A → B) : Language B :=
  {w | ∃ b ∈ w, b ∉ Set.range f}

/-- The two-state automaton which remembers whether a letter outside the image
of `f` has occurred. -/
def outsideImageDFA [Fintype A] [DecidableEq B] (f : A → B) :
    DFA B Bool :=
  { step := fun seen b => seen || decide (b ∉ Set.range f)
    start := false
    accept := {true} }

theorem outsideImageDFA_evalFrom [Fintype A] [DecidableEq B]
    (f : A → B) (seen : Bool) (w : List B) :
    (outsideImageDFA f).evalFrom seen w = true ↔
      seen = true ∨ ∃ b ∈ w, b ∉ Set.range f := by
  induction w generalizing seen with
  | nil => simp
  | cons b w ih =>
      rw [DFA.evalFrom_cons, ih]
      simp only [outsideImageDFA, Bool.or_eq_true, List.mem_cons,
        exists_eq_or_imp, decide_eq_true_eq]
      tauto

theorem outsideImageDFA_accepts [Fintype A] [DecidableEq B]
    (f : A → B) :
    (outsideImageDFA f).accepts = outsideImageLanguage f := by
  ext w
  change (outsideImageDFA f).eval w ∈ ({true} : Set Bool) ↔ _
  rw [Set.mem_singleton_iff]
  simpa [DFA.eval, outsideImageDFA, outsideImageLanguage] using
    outsideImageDFA_evalFrom f false w

theorem outsideImageLanguage_isRegular [Fintype A] [DecidableEq B]
    (f : A → B) : (outsideImageLanguage f).IsRegular :=
  ⟨Bool, inferInstance, outsideImageDFA f, outsideImageDFA_accepts f⟩

/-- A fixed encoded right-regular presentation of the outside-image language.
It is chosen once for the fixed embedding and is therefore a genuine constant
in every compiler below. -/
noncomputable def outsideImageRG [Fintype A] [Fintype B] [DecidableEq B]
    (f : A → B) : Regular.EncodedRG B :=
  Classical.choose
    (Regular.EncodedRG.regularLanguageOf_complete
      (outsideImageLanguage f) (outsideImageLanguage_isRegular f))

theorem regularLanguageOf_outsideImageRG [Fintype A] [Fintype B]
    [DecidableEq B] (f : A → B) :
    Regular.EncodedRG.regularLanguageOf (outsideImageRG f) =
      outsideImageLanguage f :=
  Classical.choose_spec
    (Regular.EncodedRG.regularLanguageOf_complete
      (outsideImageLanguage f) (outsideImageLanguage_isRegular f))

/-- Epsilon-free encoded CFG for the outside-image language.  The existing
positive-part compiler is exact here because an outside-image word is always
nonempty. -/
noncomputable def outsideImageCFG [Fintype A] [Fintype B] [DecidableEq B]
    (f : A → B) : EncodedCFG B :=
  Regular.EncodedRG.positivePart (outsideImageRG f)

theorem contextFreeLanguageOf_outsideImageCFG [Fintype A] [Fintype B]
    [DecidableEq B] (f : A → B) :
    contextFreeLanguageOf (outsideImageCFG f) = outsideImageLanguage f := by
  rw [outsideImageCFG,
    Regular.EncodedRG.contextFreeLanguageOf_positivePart,
    regularLanguageOf_outsideImageRG]
  ext w
  constructor
  · exact And.left
  · intro hw
    refine ⟨hw, ?_⟩
    intro hwNil
    subst w
    change ∃ b ∈ ([] : List B), b ∉ Set.range f at hw
    simpa using hw

theorem outsideImageCFG_noEmptyRHS [Fintype A] [Fintype B]
    [DecidableEq B] (f : A → B) : NoEmptyRHS (outsideImageCFG f) :=
  Regular.EncodedRG.positivePart_noEmptyRHS _

/-- Relabel a grammar into an ambient finite alphabet and accept every word
which visibly leaves the embedded subalphabet. -/
noncomputable def completeAlphabet [Fintype A] [Fintype B] [DecidableEq B]
    (f : A → B) (G : EncodedCFG A) : EncodedCFG B :=
  union (mapTerminals f G) (outsideImageCFG f)

/-- Exact language semantics of alphabet completion. -/
theorem contextFreeLanguageOf_completeAlphabet_of_leftInverse
    [Fintype A] [Fintype B] [DecidableEq B]
    (G : EncodedCFG A) {f : A → B} {g : B → A}
    (hgf : Function.LeftInverse g f) :
    contextFreeLanguageOf (completeAlphabet f G) =
      Language.map f (contextFreeLanguageOf G) + outsideImageLanguage f := by
  rw [completeAlphabet, contextFreeLanguageOf_union,
    contextFreeLanguageOf_mapTerminals_of_leftInverse G hgf,
    contextFreeLanguageOf_outsideImageCFG]

theorem contextFreeLanguageOf_completeAlphabet
    [Fintype A] [Fintype B] [DecidableEq B] [Nonempty A]
    (G : EncodedCFG A) {f : A → B} (hf : Function.Injective f) :
    contextFreeLanguageOf (completeAlphabet f G) =
      Language.map f (contextFreeLanguageOf G) + outsideImageLanguage f :=
  contextFreeLanguageOf_completeAlphabet_of_leftInverse G
    (Function.leftInverse_invFun hf)

/-- Alphabet completion is primitive recursive for each fixed primitive
recursive embedding.  The regular outside-image grammar is a fixed code, not
part of the runtime input. -/
theorem completeAlphabet_primrec [Fintype A] [Fintype B]
    [DecidableEq B] [Primcodable A] [Primcodable B]
    {f : A → B} (hf : Primrec f) :
    Primrec (completeAlphabet f : EncodedCFG A → EncodedCFG B) := by
  exact union_primrec.comp
    (Primrec.pair (mapTerminals_primrec hf)
      (Primrec.const (outsideImageCFG f)))

theorem completeAlphabet_computable [Fintype A] [Fintype B]
    [DecidableEq B] [Primcodable A] [Primcodable B]
    {f : A → B} (hf : Primrec f) :
    Computable (completeAlphabet f : EncodedCFG A → EncodedCFG B) :=
  (completeAlphabet_primrec hf).to_comp

theorem completeAlphabet_noEmptyRHS [Fintype A] [Fintype B]
    [DecidableEq B] {f : A → B} {G : EncodedCFG A}
    (hG : NoEmptyRHS G) : NoEmptyRHS (completeAlphabet f G) :=
  noEmptyRHS_union (noEmptyRHS_mapTerminals hG)
    (outsideImageCFG_noEmptyRHS f)

/-- The semantic core of alphabet completion: adding all words which leave an
embedded alphabet makes the target language universal exactly when the source
language was universal. -/
theorem map_add_outsideImage_eq_univ_iff
    {f : A → B} {g : B → A} (hgf : Function.LeftInverse g f)
    (L : Language A) :
    Language.map f L + outsideImageLanguage f = Set.univ ↔
      L = Set.univ := by
  have hf : Function.Injective f := hgf.injective
  constructor
  · intro hall
    apply Set.eq_univ_of_forall
    intro w
    have hw : List.map f w ∈
        Language.map f L + outsideImageLanguage f := by
      rw [hall]
      exact Set.mem_univ _
    rw [Language.mem_add] at hw
    rcases hw with hmap | hout
    · change List.map f w ∈ Set.image (List.map f) L at hmap
      obtain ⟨u, hu, heq⟩ := hmap
      exact (hf.list_map heq).symm ▸ hu
    · rcases hout with ⟨b, hb, hbout⟩
      obtain ⟨a, _, rfl⟩ := List.mem_map.mp hb
      exact (hbout ⟨a, rfl⟩).elim
  · intro hL
    apply Set.eq_univ_of_forall
    intro w
    rw [Language.mem_add]
    by_cases hout : ∃ b ∈ w, b ∉ Set.range f
    · exact Or.inr hout
    · left
      have hallrange : ∀ b ∈ w, b ∈ Set.range f := by
        intro b hb
        by_contra hbnot
        exact hout ⟨b, hb, hbnot⟩
      have hfgOn : ∀ b ∈ w, f (g b) = b := by
        intro b hb
        obtain ⟨a, rfl⟩ := hallrange b hb
        simp [hgf a]
      have hwmap : List.map f (List.map g w) = w := by
        rw [List.map_map]
        simpa only [List.map_id] using
          (List.map_congr_left (l := w) (f := f ∘ g) (g := id)
            (fun b hb => hfgOn b hb))
      change w ∈ Set.image (List.map f) L
      exact ⟨List.map g w, by rw [hL]; exact Set.mem_univ _, hwmap⟩

/-- The compiled grammar is universal exactly when its source grammar is. -/
theorem contextFreeLanguageOf_completeAlphabet_eq_univ_iff
    [Fintype A] [Fintype B] [DecidableEq B]
    (G : EncodedCFG A) {f : A → B} {g : B → A}
    (hgf : Function.LeftInverse g f) :
    contextFreeLanguageOf (completeAlphabet f G) = Set.univ ↔
      contextFreeLanguageOf G = Set.univ := by
  rw [contextFreeLanguageOf_completeAlphabet_of_leftInverse G hgf]
  exact map_add_outsideImage_eq_univ_iff hgf _

end AlphabetCompletion

end ContextFree.EncodedCFG
