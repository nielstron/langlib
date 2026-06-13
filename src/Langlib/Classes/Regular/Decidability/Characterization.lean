module

/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import Langlib.Classes.Regular.Decidability.Helper
public import Langlib.Classes.Regular.Inclusion.ContextFree
public import Langlib.Classes.Regular.Definition
public import Langlib.Automata.FiniteState.Equivalence.Regular
public import Langlib.Grammars.RightRegular.Definition
public import Langlib.Grammars.RightRegular.UnrestrictedCharacterization
@[expose]
public section



/-! # `EncodedRG` characterizes the regular languages

This file proves that the right-regular-grammar encoding `EncodedRG` denotes exactly
the regular languages:

`∀ L, L.IsRegular ↔ ∃ c : EncodedRG T, regularLanguageOf c = L`

**Soundness** (every code denotes a regular language): an `EncodedRG` decodes — by
construction — to a right-regular grammar `toRG c` whose `RG_language` equals
`regularLanguageOf c` (both are the context-free language of the same underlying
context-free grammar, via `CF_grammar_of_RG`). Hence the language is `is_RG`, so
`IsRegular`.
-/

namespace Regular.EncodedRG

variable {T : Type}

open EncodedCFG

/-- The right-regular grammar denoted by an encoded right-regular grammar: it reads
each rule body back as a right-regular rule over the nonterminals `Fin (toCFG c).ntCount`. -/
public def rgRuleOf (c : EncodedRG T) (r : ℕ × Option (T × Option ℕ)) :
    RG_rule T (Fin (toCFG c).ntCount) :=
  match r.2 with
  | none => RG_rule.epsilon ((toCFG c).toNT r.1)
  | some (a, none) => RG_rule.single ((toCFG c).toNT r.1) a
  | some (a, some B) => RG_rule.cons ((toCFG c).toNT r.1) a ((toCFG c).toNT B)

/-- Decode an encoded right-regular grammar to a `RG_grammar`. -/
public def toRG (c : EncodedRG T) : RG_grammar T where
  nt := Fin (toCFG c).ntCount
  initial := (toCFG c).toNT (toCFG c).initialIdx
  rules := c.2.2.map (rgRuleOf c)

/-- The context-free grammar of `toRG c` is exactly the context-free grammar that
`regularLanguageOf` already uses, namely `(toCFG c).toCFGrammar`. -/
public theorem cfGrammarOf_toRG (c : EncodedRG T) :
    CF_grammar_of_RG (toRG c) = (toCFG c).toCFGrammar := by
  have hrules :
      (c.2.2.map (rgRuleOf c)).map (fun r => (r.lhs, r.output))
        = (toCFG c).rawRules.map
            (fun p => ((toCFG c).toNT p.1, p.2.map (toCFG c).toSymbol)) := by
    unfold toCFG EncodedCFG.rawRules
    simp only [List.map_map]
    apply List.map_congr_left
    intro r _
    obtain ⟨lhs, body⟩ := r
    simp only [Function.comp_apply]
    rcases body with _ | ⟨a, _ | B⟩ <;> rfl
  unfold CF_grammar_of_RG toRG EncodedCFG.toCFGrammar
  exact congrArg
    (CF_grammar.mk (Fin (toCFG c).ntCount) ((toCFG c).toNT (toCFG c).initialIdx)) hrules

/-- `RG_language` of `toRG c` is the language denoted by the code. -/
public theorem rgLanguage_toRG (c : EncodedRG T) :
    RG_language (toRG c) = regularLanguageOf c := by
  have h : RG_language (toRG c) = CF_language (CF_grammar_of_RG (toRG c)) := by
    ext w
    simp only [CF_language, RG_language]
    exact RG_derives_iff_CF_derives (toRG c) _ _
  rw [h, cfGrammarOf_toRG]
  rfl

/-- **Soundness:** every code denotes a regular language. -/
public theorem regularLanguageOf_isRegular [Fintype T] (c : EncodedRG T) :
    (regularLanguageOf c).IsRegular := by
  apply isRegular_of_is_RG
  apply is_RG_via_rg_implies_is_RG
  exact ⟨toRG c, rgLanguage_toRG c⟩

/-! ## Completeness: every regular language is encoded -/

/-- Encode a right-regular rule (over `Fin (k+1)`) back into the `EncodedRG` body format. -/
public def rgRuleToBody {k : ℕ} : RG_rule T (Fin (k + 1)) → ℕ × Option (T × Option ℕ)
  | .cons A a B => (A.val, some (a, some B.val))
  | .single A a => (A.val, some (a, none))
  | .epsilon A => (A.val, none)

/-- `toNT` is the identity on indices already in range. -/
theorem toNT_self (c : EncodedRG T) (A : Fin (toCFG c).ntCount) :
    (toCFG c).toNT A.val = A := by
  apply Fin.ext
  simp [EncodedCFG.toNT, Nat.mod_eq_of_lt A.isLt]

theorem rgRuleOf_rgRuleToBody (c : EncodedRG T)
    (r : RG_rule T (Fin (toCFG c).ntCount)) :
    rgRuleOf c (rgRuleToBody (k := (toCFG c).numNT) r) = r := by
  cases r <;> simp [rgRuleToBody, rgRuleOf, toNT_self]

/-- Encode a DFA over `Fin (k+1)` as a right-regular code. -/
public noncomputable def encodeDFA [Fintype T] {k : ℕ} (M : DFA T (Fin (k + 1)))
    [DecidablePred (· ∈ M.accept)] : EncodedRG T :=
  (k, (M.start).val, (RG_of_DFA M).rules.map rgRuleToBody)

/-- Decoding the encoding of a DFA recovers `RG_of_DFA`. -/
theorem toRG_encodeDFA [Fintype T] {k : ℕ} (M : DFA T (Fin (k + 1)))
    [DecidablePred (· ∈ M.accept)] :
    toRG (encodeDFA M) = RG_of_DFA M := by
  have hinit : (toCFG (encodeDFA M)).toNT (toCFG (encodeDFA M)).initialIdx = M.start :=
    toNT_self (encodeDFA M) M.start
  have h22 : (encodeDFA M).2.2 = (RG_of_DFA M).rules.map rgRuleToBody := rfl
  have hrules : (encodeDFA M).2.2.map (rgRuleOf (encodeDFA M)) = (RG_of_DFA M).rules := by
    rw [h22, List.map_map]
    conv_rhs => rw [← List.map_id (RG_of_DFA M).rules]
    apply List.map_congr_left
    intro r _
    simp only [Function.comp_apply, id_eq]
    exact rgRuleOf_rgRuleToBody (encodeDFA M) r
  unfold toRG
  rw [hrules, hinit]
  rfl

/-- **Completeness:** every regular language is denoted by some code. -/
public theorem regularLanguageOf_complete [Fintype T] (L : Language T)
    (hL : L.IsRegular) : ∃ c : EncodedRG T, regularLanguageOf c = L := by
  classical
  obtain ⟨σ, hσ, M, rfl⟩ := hL
  have hpos : 0 < Fintype.card σ := Fintype.card_pos_iff.mpr ⟨M.start⟩
  let e : σ ≃ Fin (Fintype.card σ - 1 + 1) :=
    (Fintype.equivFin σ).trans (finCongr (Nat.succ_pred_eq_of_pos hpos).symm)
  let M' : DFA T (Fin (Fintype.card σ - 1 + 1)) := M.reindex e
  refine ⟨encodeDFA M', ?_⟩
  rw [← rgLanguage_toRG, toRG_encodeDFA, RG_of_DFA_language, DFA.accepts_reindex]

/-- **`EncodedRG` characterizes the regular languages** (the library's class `RG`). -/
public theorem regularLanguageOf_characterizes [Fintype T] :
    Characterizes RG (regularLanguageOf : EncodedRG T → Language T) := by
  intro L
  rw [show (L ∈ RG) = is_RG L from rfl, is_RG_iff_isRegular]
  exact ⟨fun hL => regularLanguageOf_complete L hL,
    fun ⟨c, hc⟩ => hc ▸ regularLanguageOf_isRegular c⟩

end Regular.EncodedRG
