module

public import Langlib.Grammars.Indexed.NormalForm.ParseTree
public import Langlib.Grammars.Indexed.NormalForm.Shrinking
import Mathlib.Data.Finite.Prod
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

/-- Certificate-level first-step decomposition with bounded shrinking for the stack-copying
branches. Binary branches use one bounded common inherited stack; push branches use a bounded
base stack below the pushed flag. Pop and terminal branches are exposed exactly. -/
public theorem exists_bound_first_step_binary_push_certificate_for_target_sublists
    {g : IndexedGrammar T} [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (target : List T) :
    ∃ K : ℕ,
      ∀ A : g.nt, ∀ σ : List g.flag, ∀ w : List T,
        w <+ target →
        NFYield g A σ w →
        (∃ B C : g.nt, ∃ u v : List T, ∃ r ∈ g.rules, ∃ τ : List g.flag,
          r.lhs = A ∧ r.consume = none ∧
          r.rhs = [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none] ∧
          w = u ++ v ∧
          0 < u.length ∧ 0 < v.length ∧
          u.length < w.length ∧ v.length < w.length ∧
          u <+ target ∧ v <+ target ∧
          τ <+ σ ∧ τ.length ≤ K ∧
          NFYield g B τ u ∧
          NFYield g C τ v ∧
          NFYield g A τ w ∧
          ∀ ρ : List g.flag,
            NFYield g B ρ u →
            NFYield g C ρ v →
            ρ <+ τ → ρ = τ) ∨
        (∃ f : g.flag, ∃ ρ : List g.flag, ∃ B : g.nt,
          ∃ r ∈ g.rules,
            σ = f :: ρ ∧
            r.lhs = A ∧ r.consume = some f ∧
            r.rhs = [IRhsSymbol.nonterminal B none] ∧
            NFYield g B ρ w) ∨
        (∃ B : g.nt, ∃ f : g.flag, ∃ r ∈ g.rules, ∃ τ : List g.flag,
          r.lhs = A ∧ r.consume = none ∧
          r.rhs = [IRhsSymbol.nonterminal B (some f)] ∧
          τ <+ σ ∧ τ.length ≤ K ∧
          NFYield g B (f :: τ) w ∧
          NFYield g A τ w ∧
          ∀ ρ : List g.flag,
            NFYield g B (f :: ρ) w →
            ρ <+ τ → ρ = τ) ∨
        (∃ a : T, ∃ r ∈ g.rules,
          r.lhs = A ∧ r.consume = none ∧ r.rhs = [IRhsSymbol.terminal a] ∧
            w = [a]) := by
  obtain ⟨K, hK⟩ :=
    exists_bound_rule_binary_push_substack_for_target_sublists (g := g) hNF target
  refine ⟨K, ?_⟩
  intro A σ w hwt hcert
  have hcases := hK A σ w hwt (NFYield.derives (g := g) hcert)
  rcases hcases with hbin | hpop | hpush | hterm
  · rcases hbin with
      ⟨B, C, u, v, r, hr, τ, hlhs, hc, hrhs, hw, hupos, hvpos, hult, hvlt,
        husub, hvsub, hτsub, hτlen, hleft, hright, hparent, hτmin⟩
    left
    exact ⟨B, C, u, v, r, hr, τ, hlhs, hc, hrhs, hw, hupos, hvpos, hult, hvlt,
      husub, hvsub, hτsub, hτlen,
      (NFYield.iff_derives_isNormalForm (g := g) hNF).mpr hleft,
      (NFYield.iff_derives_isNormalForm (g := g) hNF).mpr hright,
      (NFYield.iff_derives_isNormalForm (g := g) hNF).mpr hparent,
      fun ρ hρleft hρright hρsub =>
        hτmin ρ (NFYield.derives (g := g) hρleft)
          (NFYield.derives (g := g) hρright) hρsub⟩
  · rcases hpop with ⟨f, ρ, B, r, hr, hσ, hlhs, hc, hrhs, hchild⟩
    right
    left
    exact ⟨f, ρ, B, r, hr, hσ, hlhs, hc, hrhs,
      (NFYield.iff_derives_isNormalForm (g := g) hNF).mpr hchild⟩
  · rcases hpush with
      ⟨B, f, r, hr, τ, hlhs, hc, hrhs, hτsub, hτlen, hchild, hparent, hτmin⟩
    right
    right
    left
    exact ⟨B, f, r, hr, τ, hlhs, hc, hrhs, hτsub, hτlen,
      (NFYield.iff_derives_isNormalForm (g := g) hNF).mpr hchild,
      (NFYield.iff_derives_isNormalForm (g := g) hNF).mpr hparent,
      fun ρ hρchild hρsub =>
        hτmin ρ (NFYield.derives (g := g) hρchild) hρsub⟩
  · right
    right
    right
    exact hterm

/-- Length-uniform version of
`exists_bound_first_step_binary_push_certificate_for_target_sublists`. -/
public theorem exists_bound_first_step_binary_push_certificate_for_target_length
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (L : ℕ) :
    ∃ K : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        ∀ A : g.nt, ∀ σ : List g.flag, ∀ w : List T,
          w <+ target →
          NFYield g A σ w →
          (∃ B C : g.nt, ∃ u v : List T, ∃ r ∈ g.rules, ∃ τ : List g.flag,
            r.lhs = A ∧ r.consume = none ∧
            r.rhs = [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none] ∧
            w = u ++ v ∧
            0 < u.length ∧ 0 < v.length ∧
            u.length < w.length ∧ v.length < w.length ∧
            u <+ target ∧ v <+ target ∧
            τ <+ σ ∧ τ.length ≤ K ∧
            NFYield g B τ u ∧
            NFYield g C τ v ∧
            NFYield g A τ w ∧
            ∀ ρ : List g.flag,
              NFYield g B ρ u →
              NFYield g C ρ v →
              ρ <+ τ → ρ = τ) ∨
          (∃ f : g.flag, ∃ ρ : List g.flag, ∃ B : g.nt,
            ∃ r ∈ g.rules,
              σ = f :: ρ ∧
              r.lhs = A ∧ r.consume = some f ∧
              r.rhs = [IRhsSymbol.nonterminal B none] ∧
              NFYield g B ρ w) ∨
          (∃ B : g.nt, ∃ f : g.flag, ∃ r ∈ g.rules, ∃ τ : List g.flag,
            r.lhs = A ∧ r.consume = none ∧
            r.rhs = [IRhsSymbol.nonterminal B (some f)] ∧
            τ <+ σ ∧ τ.length ≤ K ∧
            NFYield g B (f :: τ) w ∧
            NFYield g A τ w ∧
            ∀ ρ : List g.flag,
              NFYield g B (f :: ρ) w →
              ρ <+ τ → ρ = τ) ∨
          (∃ a : T, ∃ r ∈ g.rules,
            r.lhs = A ∧ r.consume = none ∧ r.rhs = [IRhsSymbol.terminal a] ∧
              w = [a]) := by
  classical
  have htargets :
      ({target : List T | target.length ≤ L} : Set (List T)).Finite :=
    List.finite_length_le T L
  let targets : Finset (List T) := Set.Finite.toFinset htargets
  let targetBound : List T → ℕ := fun target =>
    Classical.choose
      (NFYield.exists_bound_first_step_binary_push_certificate_for_target_sublists
        (g := g) hNF target)
  refine ⟨targets.sup targetBound, ?_⟩
  intro target htargetLen A σ w hwt hcert
  have htargetMem : target ∈ targets := by
    rw [Set.Finite.mem_toFinset]
    exact htargetLen
  have hle : targetBound target ≤ targets.sup targetBound :=
    Finset.le_sup (s := targets) (f := targetBound) htargetMem
  have htarget :=
    Classical.choose_spec
      (NFYield.exists_bound_first_step_binary_push_certificate_for_target_sublists
        (g := g) hNF target)
  have hcases := htarget A σ w hwt hcert
  rcases hcases with hbin | hpop | hpush | hterm
  · rcases hbin with
      ⟨B, C, u, v, r, hr, τ, hlhs, hc, hrhs, hw, hupos, hvpos, hult, hvlt,
        husub, hvsub, hτsub, hτlen, hleft, hright, hparent, hτmin⟩
    left
    exact ⟨B, C, u, v, r, hr, τ, hlhs, hc, hrhs, hw, hupos, hvpos, hult, hvlt,
      husub, hvsub, hτsub, le_trans hτlen hle, hleft, hright, hparent, hτmin⟩
  · right
    left
    exact hpop
  · rcases hpush with
      ⟨B, f, r, hr, τ, hlhs, hc, hrhs, hτsub, hτlen, hchild, hparent, hτmin⟩
    right
    right
    left
    exact ⟨B, f, r, hr, τ, hlhs, hc, hrhs, hτsub, le_trans hτlen hle,
      hchild, hparent, hτmin⟩
  · right
    right
    right
    exact hterm

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

/-! ## Finite certificate frontiers -/

/-- For a fixed target word, there are only finitely many candidate certificate items with a
bounded stack and a yield that is a sublist of the target. -/
public theorem finite_bounded_target_items
    (g : IndexedGrammar T) [Fintype g.nt] [Fintype g.flag]
    (B : ℕ) (target : List T) :
    ({item : (g.nt × List g.flag) × List T |
      item.1.2.length ≤ B ∧ item.2 <+ target} : Set ((g.nt × List g.flag) × List T)).Finite := by
  have hnt : (Set.univ : Set g.nt).Finite := Set.finite_univ
  have hstacks : ({σ : List g.flag | σ.length ≤ B} : Set (List g.flag)).Finite :=
    List.finite_length_le g.flag B
  have hwords : ({w : List T | w <+ target} : Set (List T)).Finite :=
    (List.finite_toSet target.sublists).subset
      (by
        intro w hw
        exact (List.mem_sublists).2 hw)
  have hprod :
      ((((Set.univ : Set g.nt) ×ˢ
          ({σ : List g.flag | σ.length ≤ B} : Set (List g.flag))) ×ˢ
        ({w : List T | w <+ target} : Set (List T)))).Finite :=
    _root_.Set.Finite.prod (_root_.Set.Finite.prod hnt hstacks) hwords
  refine hprod.subset ?_
  rintro ⟨⟨A, σ⟩, w⟩ h
  simpa using h

/-- For a fixed length bound, there are only finitely many candidate certificate items with a
bounded stack and a yield of bounded length. -/
public theorem finite_bounded_length_items
    (g : IndexedGrammar T) [Fintype T] [Fintype g.nt] [Fintype g.flag]
    (B L : ℕ) :
    ({item : (g.nt × List g.flag) × List T |
      item.1.2.length ≤ B ∧ item.2.length ≤ L} :
        Set ((g.nt × List g.flag) × List T)).Finite := by
  have hnt : (Set.univ : Set g.nt).Finite := Set.finite_univ
  have hstacks : ({σ : List g.flag | σ.length ≤ B} : Set (List g.flag)).Finite :=
    List.finite_length_le g.flag B
  have hwords : ({w : List T | w.length ≤ L} : Set (List T)).Finite :=
    List.finite_length_le T L
  have hprod :
      ((((Set.univ : Set g.nt) ×ˢ
          ({σ : List g.flag | σ.length ≤ B} : Set (List g.flag))) ×ˢ
        ({w : List T | w.length ≤ L} : Set (List T)))).Finite :=
    _root_.Set.Finite.prod (_root_.Set.Finite.prod hnt hstacks) hwords
  refine hprod.subset ?_
  rintro ⟨⟨A, σ⟩, w⟩ h
  simpa using h

/-- Actual parse-certificate items form a finite subset of the bounded target frontier. -/
public theorem finite_bounded_target_certificate_items
    (g : IndexedGrammar T) [Fintype g.nt] [Fintype g.flag]
    (B : ℕ) (target : List T) :
    ({item : (g.nt × List g.flag) × List T |
      item.1.2.length ≤ B ∧ item.2 <+ target ∧
        NFYield g item.1.1 item.1.2 item.2} :
        Set ((g.nt × List g.flag) × List T)).Finite := by
  exact (NFYield.finite_bounded_target_items (g := g) B target).subset
    (by
      intro item h
      exact ⟨h.1, h.2.1⟩)

/-- Actual parse-certificate items form a finite subset of the bounded length frontier. -/
public theorem finite_bounded_length_certificate_items
    (g : IndexedGrammar T) [Fintype T] [Fintype g.nt] [Fintype g.flag]
    (B L : ℕ) :
    ({item : (g.nt × List g.flag) × List T |
      item.1.2.length ≤ B ∧ item.2.length ≤ L ∧
        NFYield g item.1.1 item.1.2 item.2} :
        Set ((g.nt × List g.flag) × List T)).Finite := by
  exact (NFYield.finite_bounded_length_items (g := g) B L).subset
    (by
      intro item h
      exact ⟨h.1, h.2.1⟩)

end NFYield

end IndexedGrammar
