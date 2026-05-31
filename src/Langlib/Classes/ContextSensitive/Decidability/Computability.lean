module

public import Langlib.Classes.ContextSensitive.Decidability.Membership
public import Langlib.Classes.ContextSensitive.Inclusion.RecursivelyEnumerable
public import Langlib.Classes.Recursive.Definition
public import Langlib.Classes.Recursive.Inclusion.ByTapeFromComputable
public import Langlib.Classes.Recursive.Basics.Post
public import Mathlib.Computability.Halting
import Langlib.Automata.Turing.Equivalence.GrammarToTM.MembershipComputability
import Langlib.Classes.ContextSensitive.Decidability.CertComputable
import Langlib.Grammars.Unrestricted.FiniteNonterminals
import Langlib.Grammars.NonContracting.Equivalence.ContextSensitive
import Langlib.Automata.Turing.DSL.SearchProcToTM0
import Langlib.Automata.Turing.DSL.CodeToTMDirect
import Langlib.Automata.Turing.Equivalence.TMEqualsRE
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
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



/-! # Computability of Membership in Context-Sensitive Languages

This file strengthens the membership result for context-sensitive languages from
the (classically trivial) `Decidable` statement to genuine **computability** in the
theory-of-computation sense: membership is a `ComputablePred`.

The argument is Post's theorem: a predicate whose positive instances and negative
instances are both recursively enumerable is computable.

- Membership `w ∈ L` is `REPred` by the usual grammar-derivation search
  (`grammarTest`).
- Non-membership `w ∉ L` is `REPred` because, for a non-contracting grammar, a
  failed bounded reachability search has a finite certificate: a list `S` of
  sentential forms of length `≤ |w|` that contains the start form, excludes the
  target, and is closed under all bounded one-step successors
  (`grammarClosedComplementCert`).

Combining the two via `ComputablePred.computable_iff_re_compl_re'` yields
`ComputablePred (fun w => w ∈ L)`.
-/

open Relation

variable {T : Type}

/-! ## Non-membership is recursively enumerable (co-RE certificate)

For a non-contracting grammar, derivations are length non-decreasing, so a word `w` is
in the language iff the terminal form `w.map terminal` is reachable from the start form
among sentential forms of length `≤ |w| + 1`. We take the bound to be `|w| + 1` rather
than `|w|` so that the start form (of length `1`) always fits, even when `w = []`.

Non-membership therefore has a finite certificate: a list `S` of forms of length `≤ |w|+1`
containing the start form, excluding the target, and closed under bounded successors. -/

section CoRE

variable [DecidableEq T]

/-- **Certificate soundness.** If a valid closed-complement certificate exists for a
non-contracting grammar at a bound that accommodates both the start and the target forms,
then the target form is not derivable from the start form. -/
public theorem not_derives_of_grammarClosedComplementCert
    (gr : grammar T) [DecidableEq gr.nt] (hnc : grammar_noncontracting gr)
    {bound : ℕ} {target : List (symbol T gr.nt)} {S : List (List (symbol T gr.nt))}
    (htarget : target.length ≤ bound)
    (hstart : ([symbol.nonterminal gr.initial] : List (symbol T gr.nt)).length ≤ bound)
    (hcert : grammarClosedComplementCert gr bound target S = true) :
    ¬ grammar_derives gr [symbol.nonterminal gr.initial] target := by
  -- Every reachable form of length ≤ bound lies in `S`.
  have key : ∀ v : List (symbol T gr.nt),
      grammar_derives gr [symbol.nonterminal gr.initial] v → v.length ≤ bound → v ∈ S := by
    intro v hv
    induction hv with
    | refl => intro _; exact grammarClosedComplementCert_start_mem gr hcert
    | @tail u v hd hstep ih =>
        intro hvlen
        have hulen : u.length ≤ bound :=
          le_trans (noncontracting_transforms_length_le gr hnc hstep) hvlen
        have huS : u ∈ S := ih hulen
        have hsucc : v ∈ grammarStepSuccessors gr.rules bound u :=
          grammarStepSuccessors_complete_of_transform gr hstep hulen hvlen
        exact grammarClosedComplementCert_closed gr hcert huS hsucc
  intro hderiv
  exact grammarClosedComplementCert_target_not_mem gr hcert (key target hderiv htarget)

/-- **Certificate completeness.** For a non-contracting grammar over finite alphabets, if
`w` is not in the language then the set of forms reachable (within the length bound) forms a
valid closed-complement certificate. -/
public theorem exists_grammarClosedComplementCert_of_not_mem
    (gr : grammar T) [Fintype T] [Fintype gr.nt] [DecidableEq gr.nt]
    (hnc : grammar_noncontracting gr)
    (w : List T) (hw : w ∉ grammar_language gr) :
    ∃ S : List (List (symbol T gr.nt)),
      grammarClosedComplementCert gr (w.length + 1) (w.map symbol.terminal) S = true := by
  classical
  set bound := w.length + 1 with hbound
  set start : List (symbol T gr.nt) := [symbol.nonterminal gr.initial] with hstart_def
  set target : List (symbol T gr.nt) := w.map symbol.terminal with htarget_def
  -- The bounded-length sentential forms.
  haveI : Fintype (symbol T gr.nt) := symbol.fintype T gr.nt
  letI α := {l : List (symbol T gr.nt) // l.length ≤ bound}
  haveI : Fintype α := fintypeBoundedList (symbol T gr.nt) bound
  -- One bounded step, given by membership in the successor list (decidable for free).
  let R : α → α → Prop := fun a b => b.val ∈ grammarStepSuccessors gr.rules bound a.val
  haveI : DecidableRel R := fun a b => inferInstanceAs (Decidable (_ ∈ _))
  have hstart_len : start.length ≤ bound := by simp [hstart_def, hbound]
  have htarget_len : target.length ≤ bound := by simp [htarget_def, hbound]
  let start' : α := ⟨start, hstart_len⟩
  let RS : Finset α := reachSet R start' (Fintype.card α)
  let S : List (List (symbol T gr.nt)) := RS.toList.map Subtype.val
  -- Membership in `S` reflects membership in the reachable Finset.
  have memS : ∀ sf : List (symbol T gr.nt), sf ∈ S ↔ ∃ a : α, a ∈ RS ∧ a.val = sf := by
    intro sf
    constructor
    · intro h
      rw [List.mem_map] at h
      obtain ⟨a, ha, rfl⟩ := h
      exact ⟨a, Finset.mem_toList.mp ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      rw [List.mem_map]
      exact ⟨a, Finset.mem_toList.mpr ha, rfl⟩
  -- A reachable bounded form yields a genuine derivation.
  have RtoD : ∀ {x y : α}, Relation.ReflTransGen R x y →
      grammar_derives gr x.val y.val := by
    intro x y h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hstep ih =>
        rename_i b c hstep
        obtain ⟨⟨r, hr, pos, happly⟩, _⟩ := grammarStepSuccessors_sound gr.rules hstep
        obtain ⟨u, v, hbef, haft⟩ := applyRuleAt_correct r b.val c.val pos happly
        exact ih.tail ⟨r, hr, u, v, hbef, haft⟩
  -- The reachable set is closed under one bounded step.
  have RSclosed : ∀ {a b : α}, a ∈ RS → R a b → b ∈ RS := by
    intro a b ha hab
    have hb : b ∈ stepClosure R RS := by
      rw [stepClosure]
      exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, a, ha, hab⟩)
    have hstab : RS = reachSet R start' (Fintype.card α + 1) := reachSet_stabilizes R start'
    rw [hstab]
    exact hb
  refine ⟨S, ?_⟩
  -- Establish the three certificate conjuncts.
  have hstart_mem : start ∈ S := by
    rw [memS]
    exact ⟨start', start_mem_reachSet R start' _, rfl⟩
  have htarget_not_mem : target ∉ S := by
    rw [memS]
    rintro ⟨a, haRS, haval⟩
    have hreach : Relation.ReflTransGen R start' a :=
      ReflTransGen_of_mem_reachSet R start' (Fintype.card α) haRS
    have hderiv : grammar_derives gr start a.val := RtoD hreach
    rw [haval] at hderiv
    exact hw hderiv
  have hclosed : ∀ sf ∈ S, sf.length ≤ bound ∧
      ∀ sf' ∈ grammarStepSuccessors gr.rules bound sf, sf' ∈ S := by
    intro sf hsf
    rw [memS] at hsf
    obtain ⟨a, haRS, haval⟩ := hsf
    have hsflen : sf.length ≤ bound := haval ▸ a.2
    refine ⟨hsflen, ?_⟩
    intro sf' hsf'
    obtain ⟨_, hsf'len⟩ := grammarStepSuccessors_sound gr.rules hsf'
    have hR : R a ⟨sf', hsf'len⟩ := by
      show (⟨sf', hsf'len⟩ : α).val ∈ grammarStepSuccessors gr.rules bound a.val
      simpa [haval] using hsf'
    have hmem : (⟨sf', hsf'len⟩ : α) ∈ RS := RSclosed haRS hR
    rw [memS]
    exact ⟨⟨sf', hsf'len⟩, hmem, rfl⟩
  -- Assemble.
  unfold grammarClosedComplementCert
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not,
    List.all_eq_true]
  exact ⟨⟨hstart_mem, htarget_not_mem⟩, hclosed⟩

/-- For a non-contracting grammar over finite alphabets, non-membership is recursively
enumerable: the search is over closed-complement certificates. -/
public theorem REPred_not_mem_of_noncontracting
    [Fintype T] [Primcodable T]
    (gr : grammar T) [Fintype gr.nt] [DecidableEq gr.nt] [Primcodable gr.nt]
    (hnc : grammar_noncontracting gr) :
    REPred (fun w : List T => w ∉ grammar_language gr) := by
  have hcert : Computable₂ (fun (w : List T) (S : List (List (symbol T gr.nt))) =>
      grammarClosedComplementCert gr (w.length + 1) (w.map symbol.terminal) S) :=
    grammarClosedComplementCert_computable₂ gr
  have hpart : REPred (fun w : List T =>
      ∃ S : List (List (symbol T gr.nt)),
        grammarClosedComplementCert gr (w.length + 1) (w.map symbol.terminal) S = true) := by
    have hdom : Partrec (fun w : List T =>
        Nat.rfind (fun k =>
          Part.some (((Encodable.decode (α := List (List (symbol T gr.nt))) k).map
            (fun S => grammarClosedComplementCert gr (w.length + 1)
              (w.map symbol.terminal) S)).getD false))) := by
      have hgEnc : Computable₂ (fun (w : List T) (k : ℕ) =>
          ((Encodable.decode (α := List (List (symbol T gr.nt))) k).map
            (fun S => grammarClosedComplementCert gr (w.length + 1)
              (w.map symbol.terminal) S)).getD false) := by
        exact Computable.option_getD
          (Computable.option_map
            (Computable.decode.comp Computable.snd)
            (hcert.comp
              (g := fun x : (List T × ℕ) × List (List (symbol T gr.nt)) => x.1.1)
              (h := fun x : (List T × ℕ) × List (List (symbol T gr.nt)) => x.2)
              (Computable.fst.comp Computable.fst)
              Computable.snd))
          (Computable.const false)
      exact Partrec.rfind hgEnc.partrec₂
    exact hdom.dom_re.of_eq fun w => by
      simp only [Nat.rfind_dom, Part.mem_some_iff, Part.some_dom, and_true]
      constructor
      · rintro ⟨n, hn⟩
        rcases hdec : Encodable.decode (α := List (List (symbol T gr.nt))) n with _ | S
        · simp [hdec] at hn
        · exact ⟨S, by simpa [hdec] using hn⟩
      · rintro ⟨S, hS⟩
        exact ⟨Encodable.encode S, by simp [Encodable.encodek, hS]⟩
  refine hpart.of_eq fun w => ?_
  constructor
  · rintro ⟨S, hS⟩ hmem
    exact not_derives_of_grammarClosedComplementCert gr hnc
      (by simp only [List.length_map]; omega)
      (by simp only [List.length_cons, List.length_nil]; omega) hS hmem
  · intro hnotmem
    exact exists_grammarClosedComplementCert_of_not_mem gr hnc w hnotmem

end CoRE

/-! ## Genuine computability of membership -/

/-- **Membership in a non-contracting language is computable.** Combining the
recursively-enumerable membership search with the recursively-enumerable non-membership
certificate search, Post's theorem yields genuine computability. -/
public theorem computablePred_mem_of_noncontracting
    [Fintype T] [DecidableEq T] [Primcodable T]
    (gr : grammar T) [Fintype gr.nt] [DecidableEq gr.nt] [Primcodable gr.nt]
    (hnc : grammar_noncontracting gr) :
    ComputablePred (fun w : List T => w ∈ grammar_language gr) := by
  rw [ComputablePred.computable_iff_re_compl_re']
  exact ⟨REPred_mem_of_is_RE ⟨gr, rfl⟩, REPred_not_mem_of_noncontracting gr hnc⟩

/-- **Membership in a context-sensitive language is computable.** This is the genuine
theory-of-computation statement that membership is decidable, strengthening the
classically-trivial `Decidable` instance `CS_membership_decidable`. -/
public theorem CS_membership_computable
    [Fintype T] [DecidableEq T] [Primcodable T]
    (g : CS_grammar T) [Fintype g.nt] [DecidableEq g.nt] [Primcodable g.nt] :
    ComputablePred (fun w : List T => w ∈ CS_language g) := by
  haveI : Fintype (grammar_of_csg g).nt := (inferInstance : Fintype g.nt)
  haveI : DecidableEq (grammar_of_csg g).nt := (inferInstance : DecidableEq g.nt)
  haveI : Primcodable (grammar_of_csg g).nt := (inferInstance : Primcodable g.nt)
  rw [CS_language_eq_grammar_language g]
  exact computablePred_mem_of_noncontracting (grammar_of_csg g) (CS_is_noncontracting g)

/-! ## Recognizability of the language and its complement

The textbook characterization of a recursive (decidable) language is that both the
language and its complement are recursively enumerable. For context-sensitive languages
the complement is RE because non-membership is a computable certificate search. -/

/-- The complement of a non-contracting language is recursively enumerable. -/
public theorem is_RE_compl_of_noncontracting
    [Fintype T] [DecidableEq T] [Primcodable T]
    (gr : grammar T) [Fintype gr.nt] [DecidableEq gr.nt] [Primcodable gr.nt]
    (hnc : grammar_noncontracting gr) :
    is_RE (grammar_language gr)ᶜ := by
  have htest : Computable₂ (fun (S : List (List (symbol T gr.nt))) (w : List T) =>
      grammarClosedComplementCert gr (w.length + 1) (w.map symbol.terminal) S) := by
    apply Computable₂.mk
    exact (grammarClosedComplementCert_computable₂ gr).comp
      (g := fun p : List (List (symbol T gr.nt)) × List T => p.2)
      (h := fun p : List (List (symbol T gr.nt)) × List T => p.1)
      Computable.snd Computable.fst
  obtain ⟨c, hc⟩ := search_is_partrec _ htest
  have htm : is_TM (grammar_language gr)ᶜ := by
    apply code_implies_isTM_direct _ c
    intro w
    rw [← hc w, Set.mem_compl_iff]
    constructor
    · intro hmem
      exact exists_grammarClosedComplementCert_of_not_mem gr hnc w hmem
    · rintro ⟨S, hS⟩ hmemL
      exact not_derives_of_grammarClosedComplementCert gr hnc
        (by simp only [List.length_map]; omega)
        (by simp only [List.length_cons, List.length_nil]; omega) hS hmemL
  exact (is_TM_iff_is_RE _).1 htm

/-- **A context-sensitive language and its complement are both recursively enumerable.**
This is the recognizability characterization underlying recursiveness/decidability:
membership is verified by a derivation search, non-membership by a bounded-reachability
certificate search. -/
public theorem CS_isRE_and_compl_isRE
    [Fintype T] [DecidableEq T] [Primcodable T]
    (g : CS_grammar T) [Fintype g.nt] [DecidableEq g.nt] [Primcodable g.nt] :
    is_RE (CS_language g) ∧ is_RE (CS_language g)ᶜ := by
  haveI : Fintype (grammar_of_csg g).nt := (inferInstance : Fintype g.nt)
  haveI : DecidableEq (grammar_of_csg g).nt := (inferInstance : DecidableEq g.nt)
  haveI : Primcodable (grammar_of_csg g).nt := (inferInstance : Primcodable g.nt)
  rw [CS_language_eq_grammar_language g]
  exact ⟨⟨grammar_of_csg g, rfl⟩,
    is_RE_compl_of_noncontracting (grammar_of_csg g) (CS_is_noncontracting g)⟩

/-! ## Context-sensitive languages are recursive

Putting it all together (Post's theorem + the TM0 decider construction): a
recursively-enumerable language whose complement is recursively enumerable is recursive,
and context-sensitive languages have this property. -/

/-- **Every context-sensitive grammar generates a recursive language.** This is the
formal statement that context-sensitive languages are a subset of the recursive
(decidable) languages. -/
public theorem is_Recursive_of_CS_grammar
    [Fintype T] [DecidableEq T] [Primcodable T]
    (g : CS_grammar T) [Fintype g.nt] [DecidableEq g.nt] [Primcodable g.nt] :
    is_Recursive (CS_language g) := by
  obtain ⟨hRE, hREc⟩ := CS_isRE_and_compl_isRE g
  exact is_Recursive_of_isRE_of_isRE_compl hRE hREc

/-- **Context-sensitive languages (presented by a finite-nonterminal context-sensitive
grammar) are a subset of the recursive languages**, stated with the language-class sets. -/
public theorem CS_subset_Recursive [Fintype T] [DecidableEq T] [Primcodable T] :
    {L : Language T | ∃ g : CS_grammar T, Finite g.nt ∧ CS_language g = L} ⊆
      (Recursive : Set (Language T)) := by
  rintro L ⟨g, hfin, rfl⟩
  haveI : Fintype g.nt := Fintype.ofFinite _
  haveI : DecidableEq g.nt := Classical.decEq _
  haveI : Primcodable g.nt :=
    Primcodable.ofEquiv (Fin (Fintype.card g.nt)) (Fintype.truncEquivFin g.nt).out
  exact is_Recursive_of_CS_grammar g
