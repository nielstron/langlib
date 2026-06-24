module

public import Langlib.Grammars.Indexed.NormalForm.ParseTree
public import Langlib.Grammars.Indexed.NormalForm.Shrinking
@[expose]
public section

/-! # Shrinking parse certificates

The suffix-shrinking lemmas in `Shrinking.lean` are stated for derivability. This file exposes the
same bounded-suffix information directly for the normal-form parse certificates from
`ParseTree.lean`.
-/

variable {T : Type}

open List

namespace IndexedGrammar

namespace NFYield

/-- Length-uniform bounded-prefix suffix shrinking for parse certificates. For a fixed target
length bound and a fixed live-prefix bound, every certificate whose yield is a sublist of the
target has an equivalent certificate using a bounded sub-suffix of the inherited stack. -/
public theorem exists_bound_prefixed_suffix_for_target_length_bounded_prefix_target_sublists
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (N L : ℕ) :
    ∃ K : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        ∀ pref : List g.flag,
          pref.length ≤ N →
          ∀ A : g.nt, ∀ w : List T,
            w <+ target →
            ∀ σ : List g.flag,
              NFYield g A (pref ++ σ) w →
              ∃ τ : List g.flag,
                NFYield g A (pref ++ τ) w ∧
                τ <+ σ ∧
                τ.length ≤ K ∧
                ∀ ρ : List g.flag,
                  NFYield g A (pref ++ ρ) w →
                  ρ <+ τ → ρ = τ := by
  obtain ⟨K, hK⟩ :=
    exists_bound_generating_prefixed_suffix_for_target_length_bounded_prefix_target_sublists
      (g := g) N L
  refine ⟨K, ?_⟩
  intro target htargetLen pref hpref A w hwt σ hcert
  obtain ⟨τ, hτder, hτsub, hτlen, hτmin⟩ :=
    hK target htargetLen pref hpref A w hwt σ
      (NFYield.derives (g := g) hcert)
  refine ⟨τ, ?_, hτsub, hτlen, ?_⟩
  · exact (NFYield.iff_derives_isNormalForm (g := g) hNF).mpr hτder
  · intro ρ hρcert hρsub
    exact hτmin ρ (NFYield.derives (g := g) hρcert) hρsub

/-- A sublist-minimal parse-certificate suffix under a bounded live prefix has uniformly bounded
length over all target words up to a fixed length. -/
public theorem exists_bound_minimal_suffix_length_for_target_length_bounded_prefix
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (N L : ℕ) :
    ∃ K : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        ∀ pref : List g.flag,
          pref.length ≤ N →
          ∀ A : g.nt, ∀ σ : List g.flag, ∀ w : List T,
            w <+ target →
            NFYield g A (pref ++ σ) w →
            (∀ ρ : List g.flag,
              NFYield g A (pref ++ ρ) w →
              ρ <+ σ → ρ = σ) →
            σ.length ≤ K := by
  obtain ⟨K, hK⟩ :=
    NFYield.exists_bound_prefixed_suffix_for_target_length_bounded_prefix_target_sublists
      (g := g) hNF N L
  refine ⟨K, ?_⟩
  intro target htargetLen pref hpref A σ w hwt hcert hmin
  obtain ⟨τ, hτcert, hτsub, hτlen, _hτmin⟩ :=
    hK target htargetLen pref hpref A w hwt σ hcert
  have hτσ : τ = σ := hmin τ hτcert hτsub
  simpa [← hτσ] using hτlen

/-- Every parse certificate can be replaced, for the same nonterminal and yield, by one whose
root stack has a bounded-length sublist of the original stack. The first `N` live flags are
preserved and only the deeper suffix is shrunk. -/
public theorem exists_bound_short_stack_certificate_for_target_length
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (N L : ℕ) :
    ∃ K : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        ∀ A : g.nt, ∀ w : List T,
          w <+ target →
          ∀ σ : List g.flag,
            NFYield g A σ w →
            ∃ σ' : List g.flag,
              NFYield g A σ' w ∧
              σ' <+ σ ∧
              σ'.length ≤ N + K := by
  obtain ⟨K, hK⟩ :=
    NFYield.exists_bound_prefixed_suffix_for_target_length_bounded_prefix_target_sublists
      (g := g) hNF N L
  refine ⟨K, ?_⟩
  intro target htargetLen A w hwt σ hcert
  let pref : List g.flag := σ.take N
  let rest : List g.flag := σ.drop N
  have hpref : pref.length ≤ N := by
    simp [pref]
  have hsplit : pref ++ rest = σ := by
    simp [pref, rest]
  have hcertSplit : NFYield g A (pref ++ rest) w := by
    simpa [hsplit] using hcert
  obtain ⟨τ, hτcert, hτsub, hτlen, _hτmin⟩ :=
    hK target htargetLen pref hpref A w hwt rest hcertSplit
  refine ⟨pref ++ τ, hτcert, ?_, ?_⟩
  · have hsub : (pref ++ τ).Sublist (pref ++ rest) :=
      List.Sublist.append (List.Sublist.refl pref) hτsub
    simpa [hsplit] using hsub
  · simp [List.length_append]
    omega

end NFYield

end IndexedGrammar
