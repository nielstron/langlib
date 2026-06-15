module

/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import Langlib.Classes.ContextSensitive.Decidability.Membership
public import Langlib.Utilities.ComputabilityPredicates
public import Langlib.Automata.Turing.Equivalence.GrammarToTM.MembershipComputability
@[expose]
public section



/-! # `Code`-with-CS-shape characterizes the context-sensitive languages

The bounded-search language `contextSensitiveLanguageOf : Code T → Language T` agrees
with the actual grammar language only on *context-sensitive* codes. So the adequate,
effective presentation of the CS class uses the subtype of codes whose decoded grammar
is context-sensitive:

`CSCode T := {c : Code T // grammar_context_sensitive (ofCode c)}`.

This file:
- proves the shape predicate `grammar_context_sensitive ∘ ofCode` is a `PrimrecPred`
  (so the subtype is `Primcodable`);
- packages `ComputableMembership CS contextSensitiveLanguageOf'`, where
  `contextSensitiveLanguageOf'` is the restriction to `CSCode`.
-/

namespace ContextSensitive

variable {T : Type}

/-! ## Boolean folds with clean specifications -/

/-- `boolAll p l` is `true` iff every element satisfies `p`. -/
def boolAll {β : Type} (p : β → Bool) (l : List β) : Bool :=
  l.foldr (fun b acc => p b && acc) true

/-- `boolAny p l` is `true` iff some element satisfies `p`. -/
def boolAny {β : Type} (p : β → Bool) (l : List β) : Bool :=
  l.foldr (fun b acc => p b || acc) false

theorem boolAll_eq_true {β : Type} (p : β → Bool) (l : List β) :
    boolAll p l = true ↔ ∀ b ∈ l, p b = true := by
  unfold boolAll
  induction l with
  | nil => simp
  | cons a t ih => simp [List.foldr_cons, ih, Bool.and_eq_true]

theorem boolAny_eq_true {β : Type} (p : β → Bool) (l : List β) :
    boolAny p l = true ↔ ∃ b ∈ l, p b = true := by
  unfold boolAny
  induction l with
  | nil => simp
  | cons a t ih => simp [List.foldr_cons, ih, Bool.or_eq_true]

theorem primrec_boolAll {β : Type} [Primcodable β] {p : ℕ → β → Bool}
    (hp : Primrec₂ p) :
    Primrec (fun x : ℕ × List β => boolAll (p x.1) x.2) := by
  have hh : Primrec₂ (fun (a : ℕ × List β) (bs : β × Bool) => p a.1 bs.1 && bs.2) :=
    Primrec.and.comp
      (hp.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
  exact Primrec.list_foldr Primrec.snd (Primrec.const true) hh

theorem primrec_boolAny {β : Type} [Primcodable β] {p : ℕ → β → Bool}
    (hp : Primrec₂ p) :
    Primrec (fun x : ℕ × List β => boolAny (p x.1) x.2) := by
  have hh : Primrec₂ (fun (a : ℕ × List β) (bs : β × Bool) => p a.1 bs.1 || bs.2) :=
    Primrec.or.comp
      (hp.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
  exact Primrec.list_foldr Primrec.snd (Primrec.const false) hh

/-! ## The CS-shape decision procedure -/

/-- The single-rule "epsilon or noncontracting" check, relative to an initial index. -/
def epsOrNc (init : ℕ) (r : grule T ℕ) : Bool :=
  ((decide (r.input_L.length = 0) && decide (r.input_N = init)) &&
    (decide (r.input_R.length = 0) && decide (r.output_string.length = 0))) ||
  decide (r.input_L.length + 1 + r.input_R.length ≤ r.output_string.length)

/-- The single-rule "is an initial epsilon rule" check. -/
def isEps (init : ℕ) (r : grule T ℕ) : Bool :=
  (decide (r.input_L.length = 0) && decide (r.input_N = init)) &&
    (decide (r.input_R.length = 0) && decide (r.output_string.length = 0))

/-- The single-rule "initial nonterminal not on this rule's RHS" check. -/
def notOnRhs [DecidableEq T] (init : ℕ) (r : grule T ℕ) : Bool :=
  boolAll (fun s => ! decide (s = symbol.nonterminal init)) r.output_string

/-- Boolean decision of `grammar_context_sensitive (ofCode c)`. -/
def isCSCode [DecidableEq T] (c : Code T) : Bool :=
  boolAll (epsOrNc c.2) c.1 &&
    (! boolAny (isEps c.2) c.1 || boolAll (notOnRhs c.2) c.1)

/-! ## Correctness of the decision procedure -/

theorem isEps_iff [DecidableEq T] (c : Code T) (r : grule T ℕ) :
    isEps c.2 r = true ↔ initial_epsilon_rule (ofCode c) r := by
  unfold isEps initial_epsilon_rule ofCode
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.length_eq_zero_iff]
  tauto

theorem epsOrNc_iff [DecidableEq T] (c : Code T) (r : grule T ℕ) :
    epsOrNc c.2 r = true ↔
      initial_epsilon_rule (ofCode c) r ∨ grule_noncontracting r := by
  have he := isEps_iff c r
  unfold epsOrNc isEps at *
  unfold grule_noncontracting
  rw [Bool.or_eq_true, he, decide_eq_true_eq, ge_iff_le]

theorem notOnRhs_iff [DecidableEq T] (init : ℕ) (r : grule T ℕ) :
    notOnRhs init r = true ↔ symbol.nonterminal init ∉ r.output_string := by
  unfold notOnRhs
  rw [boolAll_eq_true]
  refine ⟨fun h hmem => ?_, fun h s hs => ?_⟩
  · have hb := h _ hmem
    simp at hb
  · rcases eq_or_ne s (symbol.nonterminal init) with rfl | h'
    · exact absurd hs h
    · simp [h']

theorem isCSCode_iff [DecidableEq T] (c : Code T) :
    isCSCode c = true ↔ grammar_context_sensitive (ofCode c) := by
  have h1 : boolAll (epsOrNc c.2) c.1 = true ↔
      ∀ r ∈ c.1, initial_epsilon_rule (ofCode c) r ∨ grule_noncontracting r := by
    rw [boolAll_eq_true]; exact forall₂_congr fun r _ => epsOrNc_iff c r
  have h2 : boolAny (isEps c.2) c.1 = true ↔
      ∃ r ∈ c.1, initial_epsilon_rule (ofCode c) r := by
    rw [boolAny_eq_true]
    exact ⟨fun ⟨r, hr, h⟩ => ⟨r, hr, (isEps_iff c r).mp h⟩,
      fun ⟨r, hr, h⟩ => ⟨r, hr, (isEps_iff c r).mpr h⟩⟩
  have h3 : boolAll (notOnRhs c.2) c.1 = true ↔ initial_not_on_rhs (ofCode c) := by
    rw [boolAll_eq_true]
    unfold initial_not_on_rhs ofCode
    exact forall₂_congr fun r _ => notOnRhs_iff c.2 r
  unfold isCSCode grammar_context_sensitive
  rw [Bool.and_eq_true, h1]
  refine and_congr_right fun _ => ?_
  rw [Bool.or_eq_true, h3]
  by_cases hb : boolAny (isEps c.2) c.1 = true
  · have hex := h2.mp hb
    rw [hb]
    simp only [Bool.not_true, Bool.false_eq_true, false_or]
    exact ⟨fun h _ => h, fun h => h hex⟩
  · have hbf : boolAny (isEps c.2) c.1 = false := by
      cases hbb : boolAny (isEps c.2) c.1 with
      | true => exact absurd hbb hb
      | false => rfl
    have hnex : ¬ (∃ r ∈ c.1, initial_epsilon_rule (ofCode c) r) := fun h => hb (h2.mpr h)
    rw [hbf]
    simp only [Bool.not_false, true_or, true_iff]
    exact fun hex => absurd hex hnex

/-! ## Primitive recursiveness of the decision procedure -/

section Primrec
variable [DecidableEq T] [Primcodable T]

omit [DecidableEq T] in
private theorem primrec_isEps : Primrec₂ (isEps : ℕ → grule T ℕ → Bool) := by
  have lenL : Primrec (fun x : ℕ × grule T ℕ => x.2.input_L.length) :=
    Primrec.list_length.comp (primrec_grule_inputL.comp Primrec.snd)
  have lenR : Primrec (fun x : ℕ × grule T ℕ => x.2.input_R.length) :=
    Primrec.list_length.comp (primrec_grule_inputR.comp Primrec.snd)
  have lenO : Primrec (fun x : ℕ × grule T ℕ => x.2.output_string.length) :=
    Primrec.list_length.comp (primrec_grule_outputString.comp Primrec.snd)
  have inN : Primrec (fun x : ℕ × grule T ℕ => x.2.input_N) :=
    primrec_grule_inputN.comp Primrec.snd
  exact Primrec.and.comp
    (Primrec.and.comp (Primrec.eq.comp lenL (Primrec.const 0)).decide
      (Primrec.eq.comp inN Primrec.fst).decide)
    (Primrec.and.comp (Primrec.eq.comp lenR (Primrec.const 0)).decide
      (Primrec.eq.comp lenO (Primrec.const 0)).decide)

omit [DecidableEq T] in
private theorem primrec_epsOrNc : Primrec₂ (epsOrNc : ℕ → grule T ℕ → Bool) := by
  have lenL : Primrec (fun x : ℕ × grule T ℕ => x.2.input_L.length) :=
    Primrec.list_length.comp (primrec_grule_inputL.comp Primrec.snd)
  have lenR : Primrec (fun x : ℕ × grule T ℕ => x.2.input_R.length) :=
    Primrec.list_length.comp (primrec_grule_inputR.comp Primrec.snd)
  have lenO : Primrec (fun x : ℕ × grule T ℕ => x.2.output_string.length) :=
    Primrec.list_length.comp (primrec_grule_outputString.comp Primrec.snd)
  have hnc : Primrec (fun x : ℕ × grule T ℕ =>
      decide (x.2.input_L.length + 1 + x.2.input_R.length ≤ x.2.output_string.length)) :=
    (Primrec.nat_le.comp
      (Primrec.nat_add.comp (Primrec.nat_add.comp lenL (Primrec.const 1)) lenR) lenO).decide
  exact Primrec.or.comp primrec_isEps hnc

private theorem primrec_notOnRhs : Primrec₂ (notOnRhs : ℕ → grule T ℕ → Bool) := by
  have hinner : Primrec₂ (fun (init : ℕ) (s : symbol T ℕ) =>
      ! decide (s = symbol.nonterminal init)) :=
    Primrec.not.comp
      (Primrec.eq.comp Primrec.snd (primrec_symbol_nonterminal.comp Primrec.fst)).decide
  have hbA := primrec_boolAll (β := symbol T ℕ) hinner
  exact hbA.comp (Primrec.pair Primrec.fst (primrec_grule_outputString.comp Primrec.snd))

theorem primrec_isCSCode : Primrec (isCSCode : Code T → Bool) := by
  have hAll : Primrec (fun c : Code T => boolAll (epsOrNc c.2) c.1) :=
    (primrec_boolAll primrec_epsOrNc).comp (Primrec.pair Primrec.snd Primrec.fst)
  have hAny : Primrec (fun c : Code T => boolAny (isEps c.2) c.1) :=
    (primrec_boolAny primrec_isEps).comp (Primrec.pair Primrec.snd Primrec.fst)
  have hNot : Primrec (fun c : Code T => boolAll (notOnRhs c.2) c.1) :=
    (primrec_boolAll primrec_notOnRhs).comp (Primrec.pair Primrec.snd Primrec.fst)
  exact Primrec.and.comp hAll (Primrec.or.comp (Primrec.not.comp hAny) hNot)

theorem primrecPred_isCS :
    PrimrecPred (fun c : Code T => grammar_context_sensitive (ofCode c)) := by
  refine ⟨fun c => decidable_of_iff _ (isCSCode_iff c), ?_⟩
  refine primrec_isCSCode.of_eq fun c => ?_
  have hiff : (isCSCode c = true) = grammar_context_sensitive (ofCode c) :=
    propext (isCSCode_iff c)
  simp only [← hiff]
  cases isCSCode c <;> rfl

end Primrec

/-! ## The adequate, effective CS presentation -/

section Bundle
variable [DecidableEq T] [Primcodable T]

instance : DecidablePred (fun c : Code T => grammar_context_sensitive (ofCode c)) :=
  fun c => decidable_of_iff _ (isCSCode_iff c)

/-- The subtype of codes whose decoded grammar is context-sensitive. It is `Primcodable`
because the CS-shape predicate is primitive recursive (`primrecPred_isCS`). -/
public abbrev CSCode (T : Type) [DecidableEq T] [Primcodable T] : Type :=
  {c : Code T // grammar_context_sensitive (ofCode c)}

noncomputable instance : Primcodable (CSCode T) := Primcodable.subtype primrecPred_isCS

/-- The language presented by a context-sensitive code. -/
public def contextSensitiveLanguageOf' (sc : CSCode T) : Language T :=
  contextSensitiveLanguageOf sc.val

omit [Primcodable T] in
/-- On a context-sensitive code, the bounded-search language is the grammar language. -/
theorem csLang_eq {c : Code T} (hcs : grammar_context_sensitive (ofCode c)) :
    contextSensitiveLanguageOf c = grammar_language (ofCode c) := by
  ext v
  exact ⟨fun hv => memCode_sound c v hv, fun hv => memCode_complete c v hcs hv⟩

/-- The CS code presentation is adequate: it denotes exactly the context-sensitive
languages (the library's class `CS`). -/
theorem characterizes_CS :
    Characterizes CS (contextSensitiveLanguageOf' : CSCode T → Language T) := by
  intro L
  rw [show (L ∈ CS) = is_CS L from rfl]
  constructor
  · intro hL
    obtain ⟨c, hcs, hlang⟩ := code_of_CS hL
    exact ⟨⟨c, hcs⟩, by rw [contextSensitiveLanguageOf', csLang_eq hcs, hlang]⟩
  · rintro ⟨sc, rfl⟩
    exact ⟨ofCode sc.val, sc.2, (csLang_eq sc.2).symm⟩

/-- Uniform membership for the CS presentation is computable. -/
theorem contextSensitive_membership_computablePred' :
    ComputablePred (fun p : CSCode T × List T => p.2 ∈ contextSensitiveLanguageOf' p.1) := by
  obtain ⟨f, hf, hfeq⟩ :=
    ComputablePred.computable_iff.mp (contextSensitive_membership_computablePred (T := T))
  refine ComputablePred.computable_iff.mpr ⟨fun p => f (p.1.val, p.2), ?_, ?_⟩
  · exact hf.comp (Computable.pair (Primrec.subtype_val.to_comp.comp Computable.fst) Computable.snd)
  · funext p
    exact congrFun hfeq (p.1.val, p.2)

/-- **Context-sensitive membership is uniformly computable** as a statement about the
class `CS`: the context-sensitive codes form an adequate, effective presentation with
uniformly decidable membership. -/
public theorem contextSensitive_computableMembership :
    ComputableMembership CS (contextSensitiveLanguageOf' : CSCode T → Language T) :=
  ⟨characterizes_CS, contextSensitive_membership_computablePred'.to_re,
    contextSensitive_membership_computablePred'⟩

end Bundle

end ContextSensitive
