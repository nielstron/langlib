module

/-
Copyright (c) 2026 Harmonic, Niels Mündler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import Langlib.Classes.ContextFree.Decidability.Membership
public import Langlib.Classes.ContextFree.Decidability.PrimrecSatStep
public import Langlib.Classes.DeterministicContextFree.Inclusion.ContextFree
public import Langlib.Utilities.PromiseComputability
@[expose]
public section


/-! # Computability of Membership for Deterministic Context-Free Languages

Membership here is the joint problem specified by a grammar code and a word.  Since
the repository does not yet have an `EncodedDPDA`, we use raw `EncodedCFG` codes and
the semantic promise that the grammar's language is deterministic context-free.  The
existing CYK algorithm is total on every encoded CFG, and therefore uniformly decides
membership on the promised DCFL codes in particular.

## Main results

- `DCFEncodedCFG.eval_decidesMembership` – the encoded grammar and word are joint
  inputs to one uniform membership procedure, correct under `DCFEncodedCFG.Valid`.
- `DCFEncodedCFG.exists_valid_iff_is_DCF` – the valid encoded grammars present
  exactly the deterministic context-free languages.
- `DCFEncodedCFG.dcf_computableMembership` – the complete result packaged by the
  promise-aware `ComputableMembership` predicate.
- `dcf_membership_computable` – membership in a fixed deterministic context-free
  language is a `ComputablePred`.
-/

variable {T : Type} [Fintype T]

namespace DCFEncodedCFG

/-- The semantic promise that a raw encoded context-free grammar presents a
deterministic context-free language. -/
@[expose]
public def Valid (G : EncodedCFG T) : Prop :=
  is_DCF (contextFreeLanguageOf G)

/-- The valid raw encoded grammars present exactly the deterministic context-free
languages.  Validity is a semantic promise; it is not asserted to be decidable. -/
public theorem exists_valid_iff_is_DCF (L : Language T) :
    (∃ G : EncodedCFG T, Valid G ∧ contextFreeLanguageOf G = L) ↔ is_DCF L := by
  constructor
  · rintro ⟨G, hG, rfl⟩
    exact hG
  · intro hL
    obtain ⟨G, hG⟩ := ContextFree.EncodedCFG.contextFreeLanguageOf_complete L
      (is_CF_of_is_DCF hL)
    refine ⟨G, ?_, hG⟩
    unfold Valid
    rw [hG]
    exact hL

section Effective

variable [DecidableEq T] [Primcodable T]

/-- Run the existing encoded-CFG membership checker as a partial Boolean evaluator.
It is in fact total even when the DCFL promise does not hold. -/
@[expose]
public def evalMembership (G : EncodedCFG T) (w : List T) : Part Bool :=
  Part.some (checkMembershipEncoded (G, w))

/-- The encoded-CFG membership evaluator is partial recursive jointly in the raw
grammar code and the input word. -/
public theorem evalMembership_partrec₂ :
    Partrec₂ (evalMembership : EncodedCFG T → List T →. Bool) := by
  simpa [evalMembership] using
    (checkMembershipEncoded_computable' (T := T)).to₂.partrec₂

/-- A single evaluator decides membership from an encoded grammar and a word, under
the promise that the encoded grammar presents a deterministic context-free language.

The evaluator is actually total and correct for every raw `EncodedCFG`; the promise
is used to restrict the presented language class to exactly the DCFLs. -/
public theorem eval_decidesMembership :
    DecidesOnPromise (Valid : EncodedCFG T → Prop)
      (evalMembership : EncodedCFG T → List T →. Bool)
      (fun G w => w ∈ contextFreeLanguageOf G) := by
  refine ⟨⟨evalMembership_partrec₂, ?_⟩, ?_⟩
  · intro G _ w
    exact Part.some_dom _
  · intro G _ w
    simpa only [evalMembership, Part.mem_some_iff, contextFreeLanguageOf, eq_comm] using
      (checkMembershipEncoded_correct G w).symm

/-- **DCFL membership is uniformly computable from an encoded grammar and a
word.**  Valid encoded CFGs present exactly the deterministic context-free
languages, raw CFG membership is effective, and the joint CYK evaluator is total
and correct (in fact on every raw CFG code). -/
public theorem dcf_computableMembership :
    ComputableMembership DCF (contextFreeLanguageOf : EncodedCFG T → Language T)
      (valid := Valid) := by
  refine ⟨?_, contextFree_membership_computablePred.to_re, ?_⟩
  · intro L
    exact (exists_valid_iff_is_DCF L).symm
  · exact ComputablePredOnPromise.ofComputablePred
      contextFree_membership_computablePred

end Effective

end DCFEncodedCFG

/-- Membership in any fixed deterministic context-free language is a computable
predicate.  This is a corollary of the effective encoded-grammar membership
algorithm, via `DCF ⊆ CF`. -/
public theorem dcf_membership_computable
    [DecidableEq T] [Primcodable T]
    {L : Language T} (hL : is_DCF L) :
    ComputablePred (fun w : List T => w ∈ L) := by
  obtain ⟨G, hG⟩ := ContextFree.EncodedCFG.contextFreeLanguageOf_complete L
    (is_CF_of_is_DCF hL)
  rw [← hG]
  exact cf_membership_computable G.toCFGrammar
