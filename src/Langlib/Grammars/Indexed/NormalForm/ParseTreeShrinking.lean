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

/-- Length-uniform bounded-prefix first-step decomposition for parse certificates. Binary
branches shrink only the suffix below the preserved live prefix; push branches preserve the new
pushed flag and the live prefix, shrinking only below them. Pop and terminal branches are
exposed exactly. -/
public theorem exists_bound_first_step_bounded_prefix_certificate_for_target_length
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
            (∃ B C : g.nt, ∃ u v : List T, ∃ r ∈ g.rules, ∃ τ : List g.flag,
              r.lhs = A ∧ r.consume = none ∧
              r.rhs = [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none] ∧
              w = u ++ v ∧
              0 < u.length ∧ 0 < v.length ∧
              u.length < w.length ∧ v.length < w.length ∧
              u <+ target ∧ v <+ target ∧
              τ <+ σ ∧ τ.length ≤ K ∧
              NFYield g B (pref ++ τ) u ∧
              NFYield g C (pref ++ τ) v ∧
              NFYield g A (pref ++ τ) w ∧
              ∀ ρ : List g.flag,
                NFYield g B (pref ++ ρ) u →
                NFYield g C (pref ++ ρ) v →
                ρ <+ τ → ρ = τ) ∨
            (∃ f : g.flag, ∃ ρ : List g.flag, ∃ B : g.nt,
              ∃ r ∈ g.rules,
                pref ++ σ = f :: ρ ∧
                r.lhs = A ∧ r.consume = some f ∧
                r.rhs = [IRhsSymbol.nonterminal B none] ∧
                NFYield g B ρ w) ∨
            (∃ B : g.nt, ∃ f : g.flag, ∃ r ∈ g.rules, ∃ τ : List g.flag,
              r.lhs = A ∧ r.consume = none ∧
              r.rhs = [IRhsSymbol.nonterminal B (some f)] ∧
              τ <+ σ ∧ τ.length ≤ K ∧
              NFYield g B ((f :: pref) ++ τ) w ∧
              NFYield g A (pref ++ τ) w ∧
              ∀ ρ : List g.flag,
                NFYield g B ((f :: pref) ++ ρ) w →
                ρ <+ τ → ρ = τ) ∨
            (∃ a : T, ∃ r ∈ g.rules,
              r.lhs = A ∧ r.consume = none ∧ r.rhs = [IRhsSymbol.terminal a] ∧
                w = [a]) := by
  obtain ⟨K, hK⟩ :=
    exists_bound_rule_binary_push_bounded_prefix_suffix_for_target_length_sublists
      (g := g) hNF N L
  refine ⟨K, ?_⟩
  intro target htargetLen pref hpref A σ w hwt hcert
  have hcases :=
    hK target htargetLen pref hpref A σ w hwt (NFYield.derives (g := g) hcert)
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

/-- Canonical-prefix specialization of bounded-prefix first-step decomposition.

For stacks split as `η.take P ++ σ`, the first-step cases preserve the visible canonical
prefix in binary branches and expose whether a pop consumes from that prefix or from the
remaining suffix. -/
public theorem exists_bound_canonical_prefix_first_step_certificate_for_target_length
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (P L : ℕ) :
    ∃ K : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        ∀ A : g.nt, ∀ η σ : List g.flag, ∀ w : List T,
          w <+ target →
          NFYield g A (η.take P ++ σ) w →
          (∃ B C : g.nt, ∃ u v : List T, ∃ r ∈ g.rules, ∃ τ : List g.flag,
            r.lhs = A ∧ r.consume = none ∧
            r.rhs = [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none] ∧
            w = u ++ v ∧
            0 < u.length ∧ 0 < v.length ∧
            u.length < w.length ∧ v.length < w.length ∧
            u <+ target ∧ v <+ target ∧
            τ <+ σ ∧ τ.length ≤ K ∧
            NFYield g B (η.take P ++ τ) u ∧
            NFYield g C (η.take P ++ τ) v ∧
            NFYield g A (η.take P ++ τ) w ∧
            ∀ ρ : List g.flag,
              NFYield g B (η.take P ++ ρ) u →
              NFYield g C (η.take P ++ ρ) v →
              ρ <+ τ → ρ = τ) ∨
          (∃ f : g.flag, ∃ ρ : List g.flag, ∃ B : g.nt,
            ∃ r ∈ g.rules,
              η.take P ++ σ = f :: ρ ∧
              r.lhs = A ∧ r.consume = some f ∧
              r.rhs = [IRhsSymbol.nonterminal B none] ∧
              NFYield g B ρ w) ∨
          (∃ B : g.nt, ∃ f : g.flag, ∃ r ∈ g.rules, ∃ τ : List g.flag,
            r.lhs = A ∧ r.consume = none ∧
            r.rhs = [IRhsSymbol.nonterminal B (some f)] ∧
            τ <+ σ ∧ τ.length ≤ K ∧
            NFYield g B ((f :: η.take P) ++ τ) w ∧
            NFYield g A (η.take P ++ τ) w ∧
            ∀ ρ : List g.flag,
              NFYield g B ((f :: η.take P) ++ ρ) w →
              ρ <+ τ → ρ = τ) ∨
          (∃ a : T, ∃ r ∈ g.rules,
            r.lhs = A ∧ r.consume = none ∧ r.rhs = [IRhsSymbol.terminal a] ∧
              w = [a]) := by
  obtain ⟨K, hK⟩ :=
    NFYield.exists_bound_first_step_bounded_prefix_certificate_for_target_length
      (g := g) hNF P L
  refine ⟨K, ?_⟩
  intro target htargetLen A η σ w hwt hcert
  exact hK target htargetLen (η.take P) (List.length_take_le P η) A σ w hwt hcert

/-- Length-uniform bounded-prefix common-suffix shrinking for pairs of parse certificates.
This is the certificate-level form needed by binary branches: the two children keep one shared
bounded suffix below the preserved prefix, and that suffix is sublist-minimal for the pair. -/
public theorem exists_bound_pair_certificate_for_target_length_bounded_prefix
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (N L : ℕ) :
    ∃ K : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        ∀ pref : List g.flag,
          pref.length ≤ N →
          ∀ A C : g.nt, ∀ u v : List T,
            u <+ target →
            v <+ target →
            ∀ σ : List g.flag,
              NFYield g A (pref ++ σ) u →
              NFYield g C (pref ++ σ) v →
              ∃ τ : List g.flag,
                NFYield g A (pref ++ τ) u ∧
                NFYield g C (pref ++ τ) v ∧
                τ <+ σ ∧
                τ.length ≤ K ∧
                ∀ ρ : List g.flag,
                  NFYield g A (pref ++ ρ) u →
                  NFYield g C (pref ++ ρ) v →
                  ρ <+ τ → ρ = τ := by
  classical
  have htargets :
      ({target : List T | target.length ≤ L} : Set (List T)).Finite :=
    List.finite_length_le T L
  let targets : Finset (List T) := Set.Finite.toFinset htargets
  let targetBound : List T → ℕ := fun target =>
    Classical.choose
      (exists_bound_generating_prefixed_pair_suffix_for_bounded_prefix_target_sublists
        (g := g) N target)
  refine ⟨targets.sup targetBound, ?_⟩
  intro target htargetLen pref hpref A C u v hu hv σ hleft hright
  have htargetMem : target ∈ targets := by
    rw [Set.Finite.mem_toFinset]
    exact htargetLen
  have hle : targetBound target ≤ targets.sup targetBound :=
    Finset.le_sup (s := targets) (f := targetBound) htargetMem
  have hspec :=
    Classical.choose_spec
      (exists_bound_generating_prefixed_pair_suffix_for_bounded_prefix_target_sublists
        (g := g) N target)
  obtain ⟨τ, hτleft, hτright, hτsub, hτlen, hτmin⟩ :=
    hspec pref hpref A C u v hu hv σ
      (NFYield.derives (g := g) hleft)
      (NFYield.derives (g := g) hright)
  refine ⟨τ,
    (NFYield.iff_derives_isNormalForm (g := g) hNF).mpr hτleft,
    (NFYield.iff_derives_isNormalForm (g := g) hNF).mpr hτright,
    hτsub, le_trans hτlen hle, ?_⟩
  intro ρ hρleft hρright hρsub
  exact hτmin ρ (NFYield.derives (g := g) hρleft)
    (NFYield.derives (g := g) hρright) hρsub

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

/-- Length-uniform exact first-step decomposition for sublist-minimal parse certificates.

For a minimal stack item, the bounded first-step shrinker cannot replace the parent stack by
a proper substack. Thus binary and push branches keep the original stack exactly, while pop
branches pass minimality to the popped child. The single bound controls every minimal parent
stack and every pushed child stack. -/
public theorem exists_bound_minimal_certificate_first_step_for_target_length
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (L : ℕ) :
    ∃ K : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        ∀ A : g.nt, ∀ σ : List g.flag, ∀ w : List T,
          w <+ target →
          NFYield g A σ w →
          (∀ ρ : List g.flag,
            NFYield g A ρ w →
            ρ <+ σ → ρ = σ) →
          σ.length ≤ K ∧
          ((∃ B C : g.nt, ∃ u v : List T, ∃ r ∈ g.rules,
            r.lhs = A ∧ r.consume = none ∧
            r.rhs = [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none] ∧
            w = u ++ v ∧
            0 < u.length ∧ 0 < v.length ∧
            u.length < w.length ∧ v.length < w.length ∧
            u <+ target ∧ v <+ target ∧
            NFYield g B σ u ∧
            NFYield g C σ v ∧
            ∀ ρ : List g.flag,
              NFYield g B ρ u →
              NFYield g C ρ v →
              ρ <+ σ → ρ = σ) ∨
          (∃ f : g.flag, ∃ ρ : List g.flag, ∃ B : g.nt,
            ∃ r ∈ g.rules,
              σ = f :: ρ ∧
              ρ.length ≤ K ∧
              r.lhs = A ∧ r.consume = some f ∧
              r.rhs = [IRhsSymbol.nonterminal B none] ∧
              NFYield g B ρ w ∧
              ∀ μ : List g.flag,
                NFYield g B μ w →
                μ <+ ρ → μ = ρ) ∨
          (∃ B : g.nt, ∃ f : g.flag, ∃ r ∈ g.rules,
            r.lhs = A ∧ r.consume = none ∧
            r.rhs = [IRhsSymbol.nonterminal B (some f)] ∧
            (f :: σ).length ≤ K ∧
            NFYield g B (f :: σ) w ∧
            ∀ ρ : List g.flag,
              NFYield g B (f :: ρ) w →
              ρ <+ σ → ρ = σ) ∨
          (∃ a : T, ∃ r ∈ g.rules,
            r.lhs = A ∧ r.consume = none ∧ r.rhs = [IRhsSymbol.terminal a] ∧
              w = [a])) := by
  obtain ⟨Kstep, hStep⟩ :=
    NFYield.exists_bound_first_step_binary_push_certificate_for_target_length
      (g := g) hNF L
  obtain ⟨Kmin, hMinLen⟩ :=
    NFYield.exists_bound_minimal_suffix_length_for_target_length_bounded_prefix
      (g := g) hNF 0 L
  refine ⟨max Kstep (Kmin + 1), ?_⟩
  intro target htargetLen A σ w hwt hcert hmin
  have hσlenMin : σ.length ≤ Kmin := by
    exact hMinLen target htargetLen ([] : List g.flag) (by simp) A σ w hwt
      (by simpa using hcert)
      (by
        intro ρ hρcert hρsub
        exact hmin ρ (by simpa using hρcert) hρsub)
  have hσlen : σ.length ≤ max Kstep (Kmin + 1) := by
    omega
  refine ⟨hσlen, ?_⟩
  have hcases := hStep target htargetLen A σ w hwt hcert
  rcases hcases with hbin | hpop | hpush | hterm
  · rcases hbin with
      ⟨B, C, u, v, r, hr, τ, hlhs, hc, hrhs, hw, hupos, hvpos, hult, hvlt,
        husub, hvsub, hτsub, _hτlen, hleft, hright, hparent, hτmin⟩
    have hτσ : τ = σ := hmin τ hparent hτsub
    left
    exact ⟨B, C, u, v, r, hr, hlhs, hc, hrhs, hw, hupos, hvpos, hult, hvlt,
      husub, hvsub,
      (by simpa [hτσ] using hleft),
      (by simpa [hτσ] using hright),
      fun ρ hρleft hρright hρsub => by
        exact (hτmin ρ hρleft hρright (by simpa [hτσ] using hρsub)).trans hτσ⟩
  · rcases hpop with ⟨f, ρ, B, r, hr, hσ, hlhs, hc, hrhs, hchild⟩
    right
    left
    have hρlen : ρ.length ≤ max Kstep (Kmin + 1) := by
      have hρle : ρ.length ≤ σ.length := by
        rw [hσ]
        simp
      omega
    refine ⟨f, ρ, B, r, hr, hσ, hρlen, hlhs, hc, hrhs, hchild, ?_⟩
    intro μ hμ hμsub
    have hparent : NFYield g A (f :: μ) w :=
      NFYield.pop (g := g) hr hlhs hc hrhs hμ
    have hsub : (f :: μ) <+ σ := by
      simpa [hσ] using List.Sublist.cons_cons f hμsub
    have heq := hmin (f :: μ) hparent hsub
    have heq' : f :: μ = f :: ρ := by
      simpa [hσ] using heq
    exact (List.cons.inj heq').2
  · rcases hpush with
      ⟨B, f, r, hr, τ, hlhs, hc, hrhs, hτsub, _hτlen, hchild, hparent, hτmin⟩
    have hτσ : τ = σ := hmin τ hparent hτsub
    right
    right
    left
    have hchildLen : (f :: σ).length ≤ max Kstep (Kmin + 1) := by
      simp
      omega
    exact ⟨B, f, r, hr, hlhs, hc, hrhs, hchildLen,
      (by simpa [hτσ] using hchild),
      fun ρ hρchild hρsub => by
        exact (hτmin ρ hρchild (by simpa [hτσ] using hρsub)).trans hτσ⟩
  · right
    right
    right
    exact hterm

/-- Initial-stack specialization of
`exists_bound_minimal_certificate_first_step_for_target_length`. The root stack is `[]`, so
the pop case is impossible and the remaining binary/push/terminal cases expose exactly the
certificate obligations below the start symbol. -/
public theorem exists_bound_initial_certificate_first_step_for_target_length
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag] [DecidableEq g.nt]
    (hNF : g.IsNormalForm) (L : ℕ) :
    ∃ K : ℕ,
      ∀ target : List T,
        target.length ≤ L →
        ∀ w : List T,
          w <+ target →
          NFYield g g.initial [] w →
          ((∃ B C : g.nt, ∃ u v : List T, ∃ r ∈ g.rules,
            r.lhs = g.initial ∧ r.consume = none ∧
            r.rhs = [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none] ∧
            w = u ++ v ∧
            0 < u.length ∧ 0 < v.length ∧
            u.length < w.length ∧ v.length < w.length ∧
            u <+ target ∧ v <+ target ∧
            NFYield g B [] u ∧
            NFYield g C [] v ∧
            ∀ ρ : List g.flag,
              NFYield g B ρ u →
              NFYield g C ρ v →
              ρ <+ ([] : List g.flag) → ρ = []) ∨
          (∃ B : g.nt, ∃ f : g.flag, ∃ r ∈ g.rules,
            r.lhs = g.initial ∧ r.consume = none ∧
            r.rhs = [IRhsSymbol.nonterminal B (some f)] ∧
            ([f] : List g.flag).length ≤ K ∧
            NFYield g B [f] w ∧
            ∀ ρ : List g.flag,
              NFYield g B (f :: ρ) w →
              ρ <+ ([] : List g.flag) → ρ = []) ∨
          (∃ a : T, ∃ r ∈ g.rules,
            r.lhs = g.initial ∧ r.consume = none ∧ r.rhs = [IRhsSymbol.terminal a] ∧
              w = [a])) := by
  obtain ⟨K, hK⟩ :=
    NFYield.exists_bound_minimal_certificate_first_step_for_target_length
      (g := g) hNF L
  refine ⟨K, ?_⟩
  intro target htargetLen w hwt hcert
  have hmin :
      ∀ ρ : List g.flag,
        NFYield g g.initial ρ w →
        ρ <+ ([] : List g.flag) → ρ = [] := by
    intro ρ _hρ hρsub
    exact eq_nil_of_sublist_nil hρsub
  obtain ⟨_hemptyLen, hcases⟩ :=
    hK target htargetLen g.initial ([] : List g.flag) w hwt hcert hmin
  rcases hcases with hbin | hpop | hpush | hterm
  · rcases hbin with
      ⟨B, C, u, v, r, hr, hlhs, hc, hrhs, hw, hupos, hvpos, hult, hvlt,
        husub, hvsub, hleft, hright, hpairMin⟩
    left
    exact ⟨B, C, u, v, r, hr, hlhs, hc, hrhs, hw, hupos, hvpos, hult, hvlt,
      husub, hvsub, hleft, hright, hpairMin⟩
  · rcases hpop with ⟨f, ρ, B, r, hr, hnil, _hρlen, _hlhs, _hc, _hrhs, _hchild, _hmin⟩
    cases hnil
  · rcases hpush with ⟨B, f, r, hr, hlhs, hc, hrhs, hflen, hchild, hchildMin⟩
    right
    left
    exact ⟨B, f, r, hr, hlhs, hc, hrhs, by simpa using hflen, by simpa using hchild,
      hchildMin⟩
  · right
    right
    exact hterm

/-- Bounded-prefix exact first-step decomposition for suffix-minimal parse certificates.

The suffix below `pref` is minimal among certificates preserving that prefix. Binary and push
branches therefore keep that suffix exactly. A pop either consumes the first suffix flag
(`pref = []`) and passes global minimality to the child, or consumes the first prefix flag and
passes suffix-minimality to the child under the shortened prefix. -/
public theorem exists_bound_minimal_prefixed_certificate_first_step_for_target_length
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
            σ.length ≤ K ∧
            ((∃ B C : g.nt, ∃ u v : List T, ∃ r ∈ g.rules,
              r.lhs = A ∧ r.consume = none ∧
              r.rhs = [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none] ∧
              w = u ++ v ∧
              0 < u.length ∧ 0 < v.length ∧
              u.length < w.length ∧ v.length < w.length ∧
              u <+ target ∧ v <+ target ∧
              NFYield g B (pref ++ σ) u ∧
              NFYield g C (pref ++ σ) v ∧
              ∀ ρ : List g.flag,
                NFYield g B (pref ++ ρ) u →
                NFYield g C (pref ++ ρ) v →
                ρ <+ σ → ρ = σ) ∨
            (∃ f : g.flag, ∃ ρ : List g.flag, ∃ B : g.nt,
              ∃ r ∈ g.rules,
                pref = [] ∧
                σ = f :: ρ ∧
                ρ.length ≤ K ∧
                r.lhs = A ∧ r.consume = some f ∧
                r.rhs = [IRhsSymbol.nonterminal B none] ∧
                NFYield g B ρ w ∧
                ∀ μ : List g.flag,
                  NFYield g B μ w →
                  μ <+ ρ → μ = ρ) ∨
            (∃ f : g.flag, ∃ pref' : List g.flag, ∃ B : g.nt,
              ∃ r ∈ g.rules,
                pref = f :: pref' ∧
                pref'.length ≤ N ∧
                r.lhs = A ∧ r.consume = some f ∧
                r.rhs = [IRhsSymbol.nonterminal B none] ∧
                NFYield g B (pref' ++ σ) w ∧
                ∀ μ : List g.flag,
                  NFYield g B (pref' ++ μ) w →
                  μ <+ σ → μ = σ) ∨
            (∃ B : g.nt, ∃ f : g.flag, ∃ r ∈ g.rules,
              r.lhs = A ∧ r.consume = none ∧
              r.rhs = [IRhsSymbol.nonterminal B (some f)] ∧
              NFYield g B ((f :: pref) ++ σ) w ∧
              ∀ ρ : List g.flag,
                NFYield g B ((f :: pref) ++ ρ) w →
                ρ <+ σ → ρ = σ) ∨
            (∃ a : T, ∃ r ∈ g.rules,
              r.lhs = A ∧ r.consume = none ∧ r.rhs = [IRhsSymbol.terminal a] ∧
                w = [a])) := by
  obtain ⟨Kstep, hStep⟩ :=
    NFYield.exists_bound_first_step_bounded_prefix_certificate_for_target_length
      (g := g) hNF N L
  obtain ⟨Kmin, hMinLen⟩ :=
    NFYield.exists_bound_minimal_suffix_length_for_target_length_bounded_prefix
      (g := g) hNF N L
  refine ⟨max Kstep Kmin, ?_⟩
  intro target htargetLen pref hpref A σ w hwt hcert hmin
  have hσlenMin : σ.length ≤ Kmin :=
    hMinLen target htargetLen pref hpref A σ w hwt hcert hmin
  have hσlen : σ.length ≤ max Kstep Kmin := by
    omega
  refine ⟨hσlen, ?_⟩
  have hcases := hStep target htargetLen pref hpref A σ w hwt hcert
  rcases hcases with hbin | hpop | hpush | hterm
  · rcases hbin with
      ⟨B, C, u, v, r, hr, τ, hlhs, hc, hrhs, hw, hupos, hvpos, hult, hvlt,
        husub, hvsub, hτsub, _hτlen, hleft, hright, hparent, hτmin⟩
    have hτσ : τ = σ := hmin τ hparent hτsub
    left
    exact ⟨B, C, u, v, r, hr, hlhs, hc, hrhs, hw, hupos, hvpos, hult, hvlt,
      husub, hvsub,
      (by simpa [hτσ] using hleft),
      (by simpa [hτσ] using hright),
      fun ρ hρleft hρright hρsub => by
        exact (hτmin ρ hρleft hρright (by simpa [hτσ] using hρsub)).trans hτσ⟩
  · rcases hpop with ⟨f, ρ, B, r, hr, hstack, hlhs, hc, hrhs, hchild⟩
    rcases _root_.IndexedGrammar.append_eq_cons_cases
        (pref := pref) (σ := σ) (f := f) (ρ := ρ) hstack with hempty | hcons
    · rcases hempty with ⟨hpref, hσ⟩
      right
      left
      have hρlen : ρ.length ≤ max Kstep Kmin := by
        have hρle : ρ.length ≤ σ.length := by
          rw [hσ]
          simp
        omega
      refine ⟨f, ρ, B, r, hr, hpref, hσ, hρlen, hlhs, hc, hrhs, hchild, ?_⟩
      intro μ hμ hμsub
      have hparent : NFYield g A (pref ++ (f :: μ)) w := by
        have hpopCert : NFYield g A (f :: μ) w :=
          NFYield.pop (g := g) hr hlhs hc hrhs hμ
        simpa [hpref] using hpopCert
      have hsub : (f :: μ) <+ σ := by
        simpa [hσ] using List.Sublist.cons_cons f hμsub
      have heq := hmin (f :: μ) hparent hsub
      simpa [hσ] using heq
    · rcases hcons with ⟨pref', hpref, hρ⟩
      right
      right
      left
      have hpref'len : pref'.length ≤ N := by
        subst pref
        simp at hpref ⊢
        omega
      refine ⟨f, pref', B, r, hr, hpref, hpref'len, hlhs, hc, hrhs,
        (by simpa [hρ] using hchild), ?_⟩
      intro μ hμ hμsub
      have hparent : NFYield g A (pref ++ μ) w := by
        have hpopCert : NFYield g A (f :: (pref' ++ μ)) w :=
          NFYield.pop (g := g) hr hlhs hc hrhs hμ
        simpa [hpref] using hpopCert
      exact hmin μ hparent hμsub
  · rcases hpush with
      ⟨B, f, r, hr, τ, hlhs, hc, hrhs, hτsub, _hτlen, hchild, hparent, hτmin⟩
    have hτσ : τ = σ := hmin τ hparent hτsub
    right
    right
    right
    left
    exact ⟨B, f, r, hr, hlhs, hc, hrhs,
      (by simpa [hτσ] using hchild),
      fun ρ hρchild hρsub => by
        exact (hτmin ρ hρchild (by simpa [hτσ] using hρsub)).trans hτσ⟩
  · right
    right
    right
    right
    exact hterm

/-- Appending a sublist of the dropped suffix below `σ.take N` does not change the first `N`
visible stack flags. -/
theorem take_append_sublist_drop_eq_take {α : Type} {σ τ : List α} {N : ℕ}
    (hτ : τ <+ σ.drop N) :
    (σ.take N ++ τ).take N = σ.take N := by
  by_cases hN : N ≤ σ.length
  · have hlen : (σ.take N).length = N := List.length_take_of_le hN
    rw [List.take_append, hlen, Nat.sub_self]
    simp
  · have hσlen : σ.length ≤ N := Nat.le_of_not_ge hN
    have hdrop : σ.drop N = [] := List.drop_eq_nil_of_le hσlen
    have hτnil : τ = [] := by
      simpa [hdrop] using hτ
    simp [hτnil, (List.take_eq_self_iff σ).mpr hσlen]

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
              σ'.length ≤ N + K ∧
              σ'.take N = σ.take N := by
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
  refine ⟨pref ++ τ, hτcert, ?_, ?_, ?_⟩
  · have hsub : (pref ++ τ).Sublist (pref ++ rest) :=
      List.Sublist.append (List.Sublist.refl pref) hτsub
    simpa [hsplit] using hsub
  · simp [List.length_append]
    omega
  · simpa [pref, rest] using
      take_append_sublist_drop_eq_take (σ := σ) (τ := τ) (N := N) hτsub

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

/-- Stack-bounded parse-certificate items form a finite subset of the bounded target frontier. -/
public theorem finite_bounded_target_stackBounded_certificate_items
    (g : IndexedGrammar T) [Fintype g.nt] [Fintype g.flag]
    (B : ℕ) (target : List T) :
    ({item : (g.nt × List g.flag) × List T |
      item.1.2.length ≤ B ∧ item.2 <+ target ∧
        NFYield.StackBounded g B item.1.1 item.1.2 item.2} :
        Set ((g.nt × List g.flag) × List T)).Finite := by
  exact (NFYield.finite_bounded_target_items (g := g) B target).subset
    (by
      intro item h
      exact ⟨h.1, h.2.1⟩)

/-- Terminal words with some stack-bounded certificate over the bounded target frontier form a
finite set. -/
public theorem finite_bounded_target_stackBounded_certificate_words
    (g : IndexedGrammar T) [Fintype g.nt] [Fintype g.flag]
    (B : ℕ) (target : List T) :
    ({w : List T |
      w <+ target ∧
        ∃ A : g.nt, ∃ σ : List g.flag,
          σ.length ≤ B ∧ NFYield.StackBounded g B A σ w} :
        Set (List T)).Finite := by
  let items :
      Set ((g.nt × List g.flag) × List T) :=
    {item | item.1.2.length ≤ B ∧ item.2 <+ target ∧
      NFYield.StackBounded g B item.1.1 item.1.2 item.2}
  have hitems : items.Finite :=
    NFYield.finite_bounded_target_stackBounded_certificate_items (g := g) B target
  have himage : (items.image fun item => item.2).Finite := hitems.image _
  exact himage.subset
    (by
      intro w hw
      rcases hw with ⟨hwt, A, σ, hσ, hcert⟩
      exact ⟨((A, σ), w), ⟨hσ, hwt, hcert⟩, rfl⟩)

/-- Initial stack-bounded certificate words over a fixed target frontier form a finite set. -/
public theorem finite_bounded_target_initial_stackBounded_certificate_words
    (g : IndexedGrammar T) [Fintype g.nt] [Fintype g.flag]
    (B : ℕ) (target : List T) :
    ({w : List T |
      w <+ target ∧ NFYield.StackBounded g B g.initial [] w} :
        Set (List T)).Finite := by
  exact (NFYield.finite_bounded_target_stackBounded_certificate_words (g := g) B target).subset
    (by
      intro w hw
      exact ⟨hw.1, g.initial, [], by simp, hw.2⟩)

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

/-- A canonical-prefix replacement certificate is one of the finite target-frontier
certificate items once the replacement suffix is bounded. -/
public theorem canonical_prefix_certificate_mem_bounded_target_items
    {g : IndexedGrammar T} {P K : ℕ} {target w : List T}
    {A : g.nt} {η τ : List g.flag}
    (hwt : w <+ target)
    (hτ : τ.length ≤ K)
    (hcert : NFYield g A (η.take P ++ τ) w) :
    (((A, η.take P ++ τ), w) :
        (g.nt × List g.flag) × List T) ∈
      ({item : (g.nt × List g.flag) × List T |
        item.1.2.length ≤ P + K ∧ item.2 <+ target ∧
          NFYield g item.1.1 item.1.2 item.2} :
        Set ((g.nt × List g.flag) × List T)) := by
  refine ⟨?_, hwt, hcert⟩
  have htake : (η.take P).length ≤ P := List.length_take_le P η
  simp [List.length_append]
  omega

/-- A bounded-prefix replacement certificate is one of the finite target-frontier certificate
items once both the preserved prefix and replacement suffix are bounded. -/
public theorem bounded_prefix_certificate_mem_bounded_target_items
    {g : IndexedGrammar T} {N K : ℕ} {target w : List T}
    {A : g.nt} {pref τ : List g.flag}
    (hpref : pref.length ≤ N)
    (hwt : w <+ target)
    (hτ : τ.length ≤ K)
    (hcert : NFYield g A (pref ++ τ) w) :
    (((A, pref ++ τ), w) :
        (g.nt × List g.flag) × List T) ∈
      ({item : (g.nt × List g.flag) × List T |
        item.1.2.length ≤ N + K ∧ item.2 <+ target ∧
          NFYield g item.1.1 item.1.2 item.2} :
        Set ((g.nt × List g.flag) × List T)) := by
  exact ⟨by simpa [List.length_append] using Nat.add_le_add hpref hτ, hwt, hcert⟩

/-- Length-uniform version of
`canonical_prefix_certificate_mem_bounded_target_items`. -/
public theorem canonical_prefix_certificate_mem_bounded_length_items
    {g : IndexedGrammar T} {P K L : ℕ} {w : List T}
    {A : g.nt} {η τ : List g.flag}
    (hwlen : w.length ≤ L)
    (hτ : τ.length ≤ K)
    (hcert : NFYield g A (η.take P ++ τ) w) :
    (((A, η.take P ++ τ), w) :
        (g.nt × List g.flag) × List T) ∈
      ({item : (g.nt × List g.flag) × List T |
        item.1.2.length ≤ P + K ∧ item.2.length ≤ L ∧
          NFYield g item.1.1 item.1.2 item.2} :
        Set ((g.nt × List g.flag) × List T)) := by
  refine ⟨?_, hwlen, hcert⟩
  have htake : (η.take P).length ≤ P := List.length_take_le P η
  simp [List.length_append]
  omega

/-- Length-uniform version of
`bounded_prefix_certificate_mem_bounded_target_items`. -/
public theorem bounded_prefix_certificate_mem_bounded_length_items
    {g : IndexedGrammar T} {N K L : ℕ} {w : List T}
    {A : g.nt} {pref τ : List g.flag}
    (hpref : pref.length ≤ N)
    (hwlen : w.length ≤ L)
    (hτ : τ.length ≤ K)
    (hcert : NFYield g A (pref ++ τ) w) :
    (((A, pref ++ τ), w) :
        (g.nt × List g.flag) × List T) ∈
      ({item : (g.nt × List g.flag) × List T |
        item.1.2.length ≤ N + K ∧ item.2.length ≤ L ∧
          NFYield g item.1.1 item.1.2 item.2} :
        Set ((g.nt × List g.flag) × List T)) := by
  exact ⟨by simpa [List.length_append] using Nat.add_le_add hpref hτ, hwlen, hcert⟩

/-- Length-uniform finite frontier for stack-bounded parse-certificate items. -/
public theorem finite_bounded_length_stackBounded_certificate_items
    (g : IndexedGrammar T) [Fintype T] [Fintype g.nt] [Fintype g.flag]
    (B L : ℕ) :
    ({item : (g.nt × List g.flag) × List T |
      item.1.2.length ≤ B ∧ item.2.length ≤ L ∧
        NFYield.StackBounded g B item.1.1 item.1.2 item.2} :
        Set ((g.nt × List g.flag) × List T)).Finite := by
  exact (NFYield.finite_bounded_length_items (g := g) B L).subset
    (by
      intro item h
      exact ⟨h.1, h.2.1⟩)

/-- Terminal words of bounded length with some stack-bounded certificate form a finite set. -/
public theorem finite_bounded_length_stackBounded_certificate_words
    (g : IndexedGrammar T) [Fintype T] [Fintype g.nt] [Fintype g.flag]
    (B L : ℕ) :
    ({w : List T |
      w.length ≤ L ∧
        ∃ A : g.nt, ∃ σ : List g.flag,
          σ.length ≤ B ∧ NFYield.StackBounded g B A σ w} :
        Set (List T)).Finite := by
  let items :
      Set ((g.nt × List g.flag) × List T) :=
    {item | item.1.2.length ≤ B ∧ item.2.length ≤ L ∧
      NFYield.StackBounded g B item.1.1 item.1.2 item.2}
  have hitems : items.Finite :=
    NFYield.finite_bounded_length_stackBounded_certificate_items (g := g) B L
  have himage : (items.image fun item => item.2).Finite := hitems.image _
  exact himage.subset
    (by
      intro w hw
      rcases hw with ⟨hwlen, A, σ, hσ, hcert⟩
      exact ⟨((A, σ), w), ⟨hσ, hwlen, hcert⟩, rfl⟩)

/-- Initial stack-bounded certificate words of bounded length form a finite set. -/
public theorem finite_bounded_length_initial_stackBounded_certificate_words
    (g : IndexedGrammar T) [Fintype T] [Fintype g.nt] [Fintype g.flag]
    (B L : ℕ) :
    ({w : List T |
      w.length ≤ L ∧ NFYield.StackBounded g B g.initial [] w} :
        Set (List T)).Finite := by
  exact (NFYield.finite_bounded_length_stackBounded_certificate_words (g := g) B L).subset
    (by
      intro w hw
      exact ⟨hw.1, g.initial, [], by simp, hw.2⟩)

/-- For a fixed target word, binary pair-certificate items with one bounded shared stack and
two yields drawn from the target sublists form a finite frontier. -/
public theorem finite_bounded_target_pair_certificate_items
    (g : IndexedGrammar T) [Fintype g.nt] [Fintype g.flag]
    (B : ℕ) (target : List T) :
    ({item : ((g.nt × g.nt) × List g.flag) × (List T × List T) |
      item.1.2.length ≤ B ∧
        item.2.1 <+ target ∧
        item.2.2 <+ target ∧
        NFYield g item.1.1.1 item.1.2 item.2.1 ∧
        NFYield g item.1.1.2 item.1.2 item.2.2} :
        Set (((g.nt × g.nt) × List g.flag) × (List T × List T))).Finite := by
  have hnts : (Set.univ : Set (g.nt × g.nt)).Finite := Set.finite_univ
  have hstacks : ({σ : List g.flag | σ.length ≤ B} : Set (List g.flag)).Finite :=
    List.finite_length_le g.flag B
  have hwords : ({w : List T | w <+ target} : Set (List T)).Finite :=
    (List.finite_toSet target.sublists).subset
      (by
        intro w hw
        exact (List.mem_sublists).2 hw)
  have hprod :
      ((((Set.univ : Set (g.nt × g.nt)) ×ˢ
          ({σ : List g.flag | σ.length ≤ B} : Set (List g.flag))) ×ˢ
        (({w : List T | w <+ target} : Set (List T)) ×ˢ
          ({w : List T | w <+ target} : Set (List T))))).Finite :=
    _root_.Set.Finite.prod (_root_.Set.Finite.prod hnts hstacks)
      (_root_.Set.Finite.prod hwords hwords)
  refine hprod.subset ?_
  rintro ⟨⟨⟨A, C⟩, σ⟩, ⟨u, v⟩⟩ h
  exact ⟨⟨trivial, h.1⟩, h.2.1, h.2.2.1⟩

/-- Length-uniform finite frontier for binary pair-certificate items with one bounded shared
stack and two bounded-length yields. -/
public theorem finite_bounded_length_pair_certificate_items
    (g : IndexedGrammar T) [Fintype T] [Fintype g.nt] [Fintype g.flag]
    (B L : ℕ) :
    ({item : ((g.nt × g.nt) × List g.flag) × (List T × List T) |
      item.1.2.length ≤ B ∧
        item.2.1.length ≤ L ∧
        item.2.2.length ≤ L ∧
        NFYield g item.1.1.1 item.1.2 item.2.1 ∧
        NFYield g item.1.1.2 item.1.2 item.2.2} :
        Set (((g.nt × g.nt) × List g.flag) × (List T × List T))).Finite := by
  have hnts : (Set.univ : Set (g.nt × g.nt)).Finite := Set.finite_univ
  have hstacks : ({σ : List g.flag | σ.length ≤ B} : Set (List g.flag)).Finite :=
    List.finite_length_le g.flag B
  have hwords : ({w : List T | w.length ≤ L} : Set (List T)).Finite :=
    List.finite_length_le T L
  have hprod :
      ((((Set.univ : Set (g.nt × g.nt)) ×ˢ
          ({σ : List g.flag | σ.length ≤ B} : Set (List g.flag))) ×ˢ
        (({w : List T | w.length ≤ L} : Set (List T)) ×ˢ
          ({w : List T | w.length ≤ L} : Set (List T))))).Finite :=
    _root_.Set.Finite.prod (_root_.Set.Finite.prod hnts hstacks)
      (_root_.Set.Finite.prod hwords hwords)
  refine hprod.subset ?_
  rintro ⟨⟨⟨A, C⟩, σ⟩, ⟨u, v⟩⟩ h
  exact ⟨⟨trivial, h.1⟩, h.2.1, h.2.2.1⟩

/-- A canonical-prefix binary pair certificate is one of the finite target-frontier pair
items once its shared replacement suffix is bounded. -/
public theorem canonical_prefix_pair_certificate_mem_bounded_target_items
    {g : IndexedGrammar T} {P K : ℕ} {target u v : List T}
    {A C : g.nt} {η τ : List g.flag}
    (hut : u <+ target)
    (hvt : v <+ target)
    (hτ : τ.length ≤ K)
    (hleft : NFYield g A (η.take P ++ τ) u)
    (hright : NFYield g C (η.take P ++ τ) v) :
    ((((A, C), η.take P ++ τ), (u, v)) :
        ((g.nt × g.nt) × List g.flag) × (List T × List T)) ∈
      ({item : ((g.nt × g.nt) × List g.flag) × (List T × List T) |
        item.1.2.length ≤ P + K ∧
          item.2.1 <+ target ∧
          item.2.2 <+ target ∧
          NFYield g item.1.1.1 item.1.2 item.2.1 ∧
          NFYield g item.1.1.2 item.1.2 item.2.2} :
        Set (((g.nt × g.nt) × List g.flag) × (List T × List T))) := by
  refine ⟨?_, hut, hvt, hleft, hright⟩
  have htake : (η.take P).length ≤ P := List.length_take_le P η
  simp [List.length_append]
  omega

/-- A bounded-prefix binary pair certificate is one of the finite target-frontier pair items
once the shared preserved prefix and replacement suffix are bounded. -/
public theorem bounded_prefix_pair_certificate_mem_bounded_target_items
    {g : IndexedGrammar T} {N K : ℕ} {target u v : List T}
    {A C : g.nt} {pref τ : List g.flag}
    (hpref : pref.length ≤ N)
    (hut : u <+ target)
    (hvt : v <+ target)
    (hτ : τ.length ≤ K)
    (hleft : NFYield g A (pref ++ τ) u)
    (hright : NFYield g C (pref ++ τ) v) :
    ((((A, C), pref ++ τ), (u, v)) :
        ((g.nt × g.nt) × List g.flag) × (List T × List T)) ∈
      ({item : ((g.nt × g.nt) × List g.flag) × (List T × List T) |
        item.1.2.length ≤ N + K ∧
          item.2.1 <+ target ∧
          item.2.2 <+ target ∧
          NFYield g item.1.1.1 item.1.2 item.2.1 ∧
          NFYield g item.1.1.2 item.1.2 item.2.2} :
        Set (((g.nt × g.nt) × List g.flag) × (List T × List T))) := by
  exact ⟨by simpa [List.length_append] using Nat.add_le_add hpref hτ,
    hut, hvt, hleft, hright⟩

/-- Length-uniform version of
`canonical_prefix_pair_certificate_mem_bounded_target_items`. -/
public theorem canonical_prefix_pair_certificate_mem_bounded_length_items
    {g : IndexedGrammar T} {P K L : ℕ} {u v : List T}
    {A C : g.nt} {η τ : List g.flag}
    (hulen : u.length ≤ L)
    (hvlen : v.length ≤ L)
    (hτ : τ.length ≤ K)
    (hleft : NFYield g A (η.take P ++ τ) u)
    (hright : NFYield g C (η.take P ++ τ) v) :
    ((((A, C), η.take P ++ τ), (u, v)) :
        ((g.nt × g.nt) × List g.flag) × (List T × List T)) ∈
      ({item : ((g.nt × g.nt) × List g.flag) × (List T × List T) |
        item.1.2.length ≤ P + K ∧
          item.2.1.length ≤ L ∧
          item.2.2.length ≤ L ∧
          NFYield g item.1.1.1 item.1.2 item.2.1 ∧
          NFYield g item.1.1.2 item.1.2 item.2.2} :
        Set (((g.nt × g.nt) × List g.flag) × (List T × List T))) := by
  refine ⟨?_, hulen, hvlen, hleft, hright⟩
  have htake : (η.take P).length ≤ P := List.length_take_le P η
  simp [List.length_append]
  omega

/-- Length-uniform version of
`bounded_prefix_pair_certificate_mem_bounded_target_items`. -/
public theorem bounded_prefix_pair_certificate_mem_bounded_length_items
    {g : IndexedGrammar T} {N K L : ℕ} {u v : List T}
    {A C : g.nt} {pref τ : List g.flag}
    (hpref : pref.length ≤ N)
    (hulen : u.length ≤ L)
    (hvlen : v.length ≤ L)
    (hτ : τ.length ≤ K)
    (hleft : NFYield g A (pref ++ τ) u)
    (hright : NFYield g C (pref ++ τ) v) :
    ((((A, C), pref ++ τ), (u, v)) :
        ((g.nt × g.nt) × List g.flag) × (List T × List T)) ∈
      ({item : ((g.nt × g.nt) × List g.flag) × (List T × List T) |
        item.1.2.length ≤ N + K ∧
          item.2.1.length ≤ L ∧
          item.2.2.length ≤ L ∧
          NFYield g item.1.1.1 item.1.2 item.2.1 ∧
          NFYield g item.1.1.2 item.1.2 item.2.2} :
        Set (((g.nt × g.nt) × List g.flag) × (List T × List T))) := by
  exact ⟨by simpa [List.length_append] using Nat.add_le_add hpref hτ,
    hulen, hvlen, hleft, hright⟩

/-- Frontier memberships supplied by a bounded-prefix binary certificate branch. This bundles
the individual child certificates, the shrunken parent certificate, and the shared pair
certificate into both target-specific and length-uniform finite frontiers. -/
public theorem bounded_prefix_binary_branch_mem_frontiers
    {g : IndexedGrammar T} {N K L : ℕ} {target u v w : List T}
    {A B C : g.nt} {pref τ : List g.flag}
    (hpref : pref.length ≤ N)
    (htargetLen : target.length ≤ L)
    (hut : u <+ target)
    (hvt : v <+ target)
    (hwt : w <+ target)
    (hτ : τ.length ≤ K)
    (hleft : NFYield g B (pref ++ τ) u)
    (hright : NFYield g C (pref ++ τ) v)
    (hparent : NFYield g A (pref ++ τ) w) :
    (((B, pref ++ τ), u) :
        (g.nt × List g.flag) × List T) ∈
        ({item : (g.nt × List g.flag) × List T |
          item.1.2.length ≤ N + K ∧ item.2 <+ target ∧
            NFYield g item.1.1 item.1.2 item.2} :
          Set ((g.nt × List g.flag) × List T)) ∧
      (((C, pref ++ τ), v) :
        (g.nt × List g.flag) × List T) ∈
        ({item : (g.nt × List g.flag) × List T |
          item.1.2.length ≤ N + K ∧ item.2 <+ target ∧
            NFYield g item.1.1 item.1.2 item.2} :
          Set ((g.nt × List g.flag) × List T)) ∧
      (((A, pref ++ τ), w) :
        (g.nt × List g.flag) × List T) ∈
        ({item : (g.nt × List g.flag) × List T |
          item.1.2.length ≤ N + K ∧ item.2 <+ target ∧
            NFYield g item.1.1 item.1.2 item.2} :
          Set ((g.nt × List g.flag) × List T)) ∧
      ((((B, C), pref ++ τ), (u, v)) :
        ((g.nt × g.nt) × List g.flag) × (List T × List T)) ∈
        ({item : ((g.nt × g.nt) × List g.flag) × (List T × List T) |
          item.1.2.length ≤ N + K ∧
            item.2.1 <+ target ∧
            item.2.2 <+ target ∧
            NFYield g item.1.1.1 item.1.2 item.2.1 ∧
            NFYield g item.1.1.2 item.1.2 item.2.2} :
          Set (((g.nt × g.nt) × List g.flag) × (List T × List T))) ∧
      (((B, pref ++ τ), u) :
        (g.nt × List g.flag) × List T) ∈
        ({item : (g.nt × List g.flag) × List T |
          item.1.2.length ≤ N + K ∧ item.2.length ≤ L ∧
            NFYield g item.1.1 item.1.2 item.2} :
          Set ((g.nt × List g.flag) × List T)) ∧
      (((C, pref ++ τ), v) :
        (g.nt × List g.flag) × List T) ∈
        ({item : (g.nt × List g.flag) × List T |
          item.1.2.length ≤ N + K ∧ item.2.length ≤ L ∧
            NFYield g item.1.1 item.1.2 item.2} :
          Set ((g.nt × List g.flag) × List T)) ∧
      (((A, pref ++ τ), w) :
        (g.nt × List g.flag) × List T) ∈
        ({item : (g.nt × List g.flag) × List T |
          item.1.2.length ≤ N + K ∧ item.2.length ≤ L ∧
            NFYield g item.1.1 item.1.2 item.2} :
          Set ((g.nt × List g.flag) × List T)) ∧
      ((((B, C), pref ++ τ), (u, v)) :
        ((g.nt × g.nt) × List g.flag) × (List T × List T)) ∈
        ({item : ((g.nt × g.nt) × List g.flag) × (List T × List T) |
          item.1.2.length ≤ N + K ∧
            item.2.1.length ≤ L ∧
            item.2.2.length ≤ L ∧
            NFYield g item.1.1.1 item.1.2 item.2.1 ∧
            NFYield g item.1.1.2 item.1.2 item.2.2} :
          Set (((g.nt × g.nt) × List g.flag) × (List T × List T))) := by
  have hulen : u.length ≤ L := le_trans hut.length_le htargetLen
  have hvlen : v.length ≤ L := le_trans hvt.length_le htargetLen
  have hwlen : w.length ≤ L := le_trans hwt.length_le htargetLen
  exact ⟨
    bounded_prefix_certificate_mem_bounded_target_items
      (g := g) (N := N) (K := K) hpref hut hτ hleft,
    bounded_prefix_certificate_mem_bounded_target_items
      (g := g) (N := N) (K := K) hpref hvt hτ hright,
    bounded_prefix_certificate_mem_bounded_target_items
      (g := g) (N := N) (K := K) hpref hwt hτ hparent,
    bounded_prefix_pair_certificate_mem_bounded_target_items
      (g := g) (N := N) (K := K) hpref hut hvt hτ hleft hright,
    bounded_prefix_certificate_mem_bounded_length_items
      (g := g) (N := N) (K := K) (L := L) hpref hulen hτ hleft,
    bounded_prefix_certificate_mem_bounded_length_items
      (g := g) (N := N) (K := K) (L := L) hpref hvlen hτ hright,
    bounded_prefix_certificate_mem_bounded_length_items
      (g := g) (N := N) (K := K) (L := L) hpref hwlen hτ hparent,
    bounded_prefix_pair_certificate_mem_bounded_length_items
      (g := g) (N := N) (K := K) (L := L) hpref hulen hvlen hτ hleft hright⟩

/-- Frontier memberships supplied by a bounded-prefix push certificate branch. The pushed
child lives in the finite frontier with preserved prefix length `N + 1`; the shrunken parent
stays in the original `N`-prefix frontier. -/
public theorem bounded_prefix_push_branch_mem_frontiers
    {g : IndexedGrammar T} {N K L : ℕ} {target w : List T}
    {A B : g.nt} {pref τ : List g.flag} {f : g.flag}
    (hpref : pref.length ≤ N)
    (htargetLen : target.length ≤ L)
    (hwt : w <+ target)
    (hτ : τ.length ≤ K)
    (hchild : NFYield g B ((f :: pref) ++ τ) w)
    (hparent : NFYield g A (pref ++ τ) w) :
    (((B, (f :: pref) ++ τ), w) :
        (g.nt × List g.flag) × List T) ∈
        ({item : (g.nt × List g.flag) × List T |
          item.1.2.length ≤ (N + 1) + K ∧ item.2 <+ target ∧
            NFYield g item.1.1 item.1.2 item.2} :
          Set ((g.nt × List g.flag) × List T)) ∧
      (((A, pref ++ τ), w) :
        (g.nt × List g.flag) × List T) ∈
        ({item : (g.nt × List g.flag) × List T |
          item.1.2.length ≤ N + K ∧ item.2 <+ target ∧
            NFYield g item.1.1 item.1.2 item.2} :
          Set ((g.nt × List g.flag) × List T)) ∧
      (((B, (f :: pref) ++ τ), w) :
        (g.nt × List g.flag) × List T) ∈
        ({item : (g.nt × List g.flag) × List T |
          item.1.2.length ≤ (N + 1) + K ∧ item.2.length ≤ L ∧
            NFYield g item.1.1 item.1.2 item.2} :
          Set ((g.nt × List g.flag) × List T)) ∧
      (((A, pref ++ τ), w) :
        (g.nt × List g.flag) × List T) ∈
        ({item : (g.nt × List g.flag) × List T |
          item.1.2.length ≤ N + K ∧ item.2.length ≤ L ∧
            NFYield g item.1.1 item.1.2 item.2} :
          Set ((g.nt × List g.flag) × List T)) := by
  have hpushPref : (f :: pref).length ≤ N + 1 := by
    simp
    exact hpref
  have hwlen : w.length ≤ L := le_trans hwt.length_le htargetLen
  exact ⟨
    bounded_prefix_certificate_mem_bounded_target_items
      (g := g) (N := N + 1) (K := K) hpushPref hwt hτ hchild,
    bounded_prefix_certificate_mem_bounded_target_items
      (g := g) (N := N) (K := K) hpref hwt hτ hparent,
    bounded_prefix_certificate_mem_bounded_length_items
      (g := g) (N := N + 1) (K := K) (L := L) hpushPref hwlen hτ hchild,
    bounded_prefix_certificate_mem_bounded_length_items
      (g := g) (N := N) (K := K) (L := L) hpref hwlen hτ hparent⟩

/-- Frontier memberships supplied by a pop that consumes the first suffix flag below an empty
preserved prefix. -/
public theorem empty_prefix_pop_branch_mem_frontiers
    {g : IndexedGrammar T} {K L : ℕ} {target w : List T}
    {B : g.nt} {ρ : List g.flag}
    (htargetLen : target.length ≤ L)
    (hwt : w <+ target)
    (hρ : ρ.length ≤ K)
    (hchild : NFYield g B ρ w) :
    (((B, ρ), w) :
        (g.nt × List g.flag) × List T) ∈
        ({item : (g.nt × List g.flag) × List T |
          item.1.2.length ≤ K ∧ item.2 <+ target ∧
            NFYield g item.1.1 item.1.2 item.2} :
          Set ((g.nt × List g.flag) × List T)) ∧
      (((B, ρ), w) :
        (g.nt × List g.flag) × List T) ∈
        ({item : (g.nt × List g.flag) × List T |
          item.1.2.length ≤ K ∧ item.2.length ≤ L ∧
            NFYield g item.1.1 item.1.2 item.2} :
          Set ((g.nt × List g.flag) × List T)) := by
  have hnil : ([] : List g.flag).length ≤ 0 := by simp
  have hwlen : w.length ≤ L := le_trans hwt.length_le htargetLen
  exact ⟨
    by
      simpa using
        (bounded_prefix_certificate_mem_bounded_target_items
          (g := g) (N := 0) (K := K) hnil hwt hρ hchild),
    by
      simpa using
        (bounded_prefix_certificate_mem_bounded_length_items
          (g := g) (N := 0) (K := K) (L := L) hnil hwlen hρ hchild)⟩

/-- Frontier memberships supplied by a pop that consumes the first preserved prefix flag and
therefore continues under the shortened prefix. -/
public theorem shortened_prefix_pop_branch_mem_frontiers
    {g : IndexedGrammar T} {N K L : ℕ} {target w : List T}
    {B : g.nt} {pref' σ : List g.flag}
    (hpref' : pref'.length ≤ N)
    (htargetLen : target.length ≤ L)
    (hwt : w <+ target)
    (hσ : σ.length ≤ K)
    (hchild : NFYield g B (pref' ++ σ) w) :
    (((B, pref' ++ σ), w) :
        (g.nt × List g.flag) × List T) ∈
        ({item : (g.nt × List g.flag) × List T |
          item.1.2.length ≤ N + K ∧ item.2 <+ target ∧
            NFYield g item.1.1 item.1.2 item.2} :
          Set ((g.nt × List g.flag) × List T)) ∧
      (((B, pref' ++ σ), w) :
        (g.nt × List g.flag) × List T) ∈
        ({item : (g.nt × List g.flag) × List T |
          item.1.2.length ≤ N + K ∧ item.2.length ≤ L ∧
            NFYield g item.1.1 item.1.2 item.2} :
          Set ((g.nt × List g.flag) × List T)) := by
  have hwlen : w.length ≤ L := le_trans hwt.length_le htargetLen
  exact ⟨
    bounded_prefix_certificate_mem_bounded_target_items
      (g := g) (N := N) (K := K) hpref' hwt hσ hchild,
    bounded_prefix_certificate_mem_bounded_length_items
      (g := g) (N := N) (K := K) (L := L) hpref' hwlen hσ hchild⟩

/-- Bounded-prefix first-step decomposition for suffix-minimal certificates, with the finite
frontier memberships needed by the branch exposed in each case. -/
public theorem exists_bound_minimal_prefixed_certificate_first_step_mem_frontiers_for_target_length
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
            σ.length ≤ K ∧
            (((A, pref ++ σ), w) :
                (g.nt × List g.flag) × List T) ∈
              ({item : (g.nt × List g.flag) × List T |
                item.1.2.length ≤ N + K ∧ item.2 <+ target ∧
                  NFYield g item.1.1 item.1.2 item.2} :
                Set ((g.nt × List g.flag) × List T)) ∧
            (((A, pref ++ σ), w) :
                (g.nt × List g.flag) × List T) ∈
              ({item : (g.nt × List g.flag) × List T |
                item.1.2.length ≤ N + K ∧ item.2.length ≤ L ∧
                  NFYield g item.1.1 item.1.2 item.2} :
                Set ((g.nt × List g.flag) × List T)) ∧
            ((∃ B C : g.nt, ∃ u v : List T, ∃ r ∈ g.rules,
                r.lhs = A ∧ r.consume = none ∧
                r.rhs = [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none] ∧
                w = u ++ v ∧
                0 < u.length ∧ 0 < v.length ∧
                u.length < w.length ∧ v.length < w.length ∧
                u <+ target ∧ v <+ target ∧
                NFYield g B (pref ++ σ) u ∧
                NFYield g C (pref ++ σ) v ∧
                (∀ ρ : List g.flag,
                  NFYield g B (pref ++ ρ) u →
                  NFYield g C (pref ++ ρ) v →
                  ρ <+ σ → ρ = σ) ∧
                (((B, pref ++ σ), u) :
                    (g.nt × List g.flag) × List T) ∈
                  ({item : (g.nt × List g.flag) × List T |
                    item.1.2.length ≤ N + K ∧ item.2 <+ target ∧
                      NFYield g item.1.1 item.1.2 item.2} :
                    Set ((g.nt × List g.flag) × List T)) ∧
                (((C, pref ++ σ), v) :
                    (g.nt × List g.flag) × List T) ∈
                  ({item : (g.nt × List g.flag) × List T |
                    item.1.2.length ≤ N + K ∧ item.2 <+ target ∧
                      NFYield g item.1.1 item.1.2 item.2} :
                    Set ((g.nt × List g.flag) × List T)) ∧
                (((A, pref ++ σ), w) :
                    (g.nt × List g.flag) × List T) ∈
                  ({item : (g.nt × List g.flag) × List T |
                    item.1.2.length ≤ N + K ∧ item.2 <+ target ∧
                      NFYield g item.1.1 item.1.2 item.2} :
                    Set ((g.nt × List g.flag) × List T)) ∧
                ((((B, C), pref ++ σ), (u, v)) :
                    ((g.nt × g.nt) × List g.flag) × (List T × List T)) ∈
                  ({item : ((g.nt × g.nt) × List g.flag) × (List T × List T) |
                    item.1.2.length ≤ N + K ∧
                      item.2.1 <+ target ∧
                      item.2.2 <+ target ∧
                      NFYield g item.1.1.1 item.1.2 item.2.1 ∧
                      NFYield g item.1.1.2 item.1.2 item.2.2} :
                    Set (((g.nt × g.nt) × List g.flag) × (List T × List T))) ∧
                (((B, pref ++ σ), u) :
                    (g.nt × List g.flag) × List T) ∈
                  ({item : (g.nt × List g.flag) × List T |
                    item.1.2.length ≤ N + K ∧ item.2.length ≤ L ∧
                      NFYield g item.1.1 item.1.2 item.2} :
                    Set ((g.nt × List g.flag) × List T)) ∧
                (((C, pref ++ σ), v) :
                    (g.nt × List g.flag) × List T) ∈
                  ({item : (g.nt × List g.flag) × List T |
                    item.1.2.length ≤ N + K ∧ item.2.length ≤ L ∧
                      NFYield g item.1.1 item.1.2 item.2} :
                    Set ((g.nt × List g.flag) × List T)) ∧
                (((A, pref ++ σ), w) :
                    (g.nt × List g.flag) × List T) ∈
                  ({item : (g.nt × List g.flag) × List T |
                    item.1.2.length ≤ N + K ∧ item.2.length ≤ L ∧
                      NFYield g item.1.1 item.1.2 item.2} :
                    Set ((g.nt × List g.flag) × List T)) ∧
                ((((B, C), pref ++ σ), (u, v)) :
                    ((g.nt × g.nt) × List g.flag) × (List T × List T)) ∈
                  ({item : ((g.nt × g.nt) × List g.flag) × (List T × List T) |
                    item.1.2.length ≤ N + K ∧
                      item.2.1.length ≤ L ∧
                      item.2.2.length ≤ L ∧
                      NFYield g item.1.1.1 item.1.2 item.2.1 ∧
                      NFYield g item.1.1.2 item.1.2 item.2.2} :
                    Set (((g.nt × g.nt) × List g.flag) × (List T × List T)))) ∨
            (∃ f : g.flag, ∃ ρ : List g.flag, ∃ B : g.nt,
              ∃ r ∈ g.rules,
                pref = [] ∧
                σ = f :: ρ ∧
                ρ.length ≤ K ∧
                r.lhs = A ∧ r.consume = some f ∧
                r.rhs = [IRhsSymbol.nonterminal B none] ∧
                NFYield g B ρ w ∧
                (∀ μ : List g.flag,
                  NFYield g B μ w →
                  μ <+ ρ → μ = ρ) ∧
                (((B, ρ), w) :
                    (g.nt × List g.flag) × List T) ∈
                  ({item : (g.nt × List g.flag) × List T |
                    item.1.2.length ≤ K ∧ item.2 <+ target ∧
                      NFYield g item.1.1 item.1.2 item.2} :
                    Set ((g.nt × List g.flag) × List T)) ∧
                (((B, ρ), w) :
                    (g.nt × List g.flag) × List T) ∈
                  ({item : (g.nt × List g.flag) × List T |
                    item.1.2.length ≤ K ∧ item.2.length ≤ L ∧
                      NFYield g item.1.1 item.1.2 item.2} :
                    Set ((g.nt × List g.flag) × List T))) ∨
            (∃ f : g.flag, ∃ pref' : List g.flag, ∃ B : g.nt,
              ∃ r ∈ g.rules,
                pref = f :: pref' ∧
                pref'.length ≤ N ∧
                r.lhs = A ∧ r.consume = some f ∧
                r.rhs = [IRhsSymbol.nonterminal B none] ∧
                NFYield g B (pref' ++ σ) w ∧
                (∀ μ : List g.flag,
                  NFYield g B (pref' ++ μ) w →
                  μ <+ σ → μ = σ) ∧
                (((B, pref' ++ σ), w) :
                    (g.nt × List g.flag) × List T) ∈
                  ({item : (g.nt × List g.flag) × List T |
                    item.1.2.length ≤ N + K ∧ item.2 <+ target ∧
                      NFYield g item.1.1 item.1.2 item.2} :
                    Set ((g.nt × List g.flag) × List T)) ∧
                (((B, pref' ++ σ), w) :
                    (g.nt × List g.flag) × List T) ∈
                  ({item : (g.nt × List g.flag) × List T |
                    item.1.2.length ≤ N + K ∧ item.2.length ≤ L ∧
                      NFYield g item.1.1 item.1.2 item.2} :
                    Set ((g.nt × List g.flag) × List T))) ∨
            (∃ B : g.nt, ∃ f : g.flag, ∃ r ∈ g.rules,
                NFYield g B ((f :: pref) ++ σ) w ∧
                r.lhs = A ∧ r.consume = none ∧
                r.rhs = [IRhsSymbol.nonterminal B (some f)] ∧
                (∀ ρ : List g.flag,
                  NFYield g B ((f :: pref) ++ ρ) w →
                  ρ <+ σ → ρ = σ) ∧
                (((B, (f :: pref) ++ σ), w) :
                    (g.nt × List g.flag) × List T) ∈
                  ({item : (g.nt × List g.flag) × List T |
                    item.1.2.length ≤ (N + 1) + K ∧ item.2 <+ target ∧
                      NFYield g item.1.1 item.1.2 item.2} :
                    Set ((g.nt × List g.flag) × List T)) ∧
                (((A, pref ++ σ), w) :
                    (g.nt × List g.flag) × List T) ∈
                  ({item : (g.nt × List g.flag) × List T |
                    item.1.2.length ≤ N + K ∧ item.2 <+ target ∧
                      NFYield g item.1.1 item.1.2 item.2} :
                    Set ((g.nt × List g.flag) × List T)) ∧
                (((B, (f :: pref) ++ σ), w) :
                    (g.nt × List g.flag) × List T) ∈
                  ({item : (g.nt × List g.flag) × List T |
                    item.1.2.length ≤ (N + 1) + K ∧ item.2.length ≤ L ∧
                      NFYield g item.1.1 item.1.2 item.2} :
                    Set ((g.nt × List g.flag) × List T)) ∧
                (((A, pref ++ σ), w) :
                    (g.nt × List g.flag) × List T) ∈
                  ({item : (g.nt × List g.flag) × List T |
                    item.1.2.length ≤ N + K ∧ item.2.length ≤ L ∧
                      NFYield g item.1.1 item.1.2 item.2} :
                    Set ((g.nt × List g.flag) × List T))) ∨
            (∃ a : T, ∃ r ∈ g.rules,
              r.lhs = A ∧ r.consume = none ∧ r.rhs = [IRhsSymbol.terminal a] ∧
                w = [a])) := by
  obtain ⟨K, hK⟩ :=
    NFYield.exists_bound_minimal_prefixed_certificate_first_step_for_target_length
      (g := g) hNF N L
  refine ⟨K, ?_⟩
  intro target htargetLen pref hpref A σ w hwt hcert hmin
  obtain ⟨hσlen, hcases⟩ :=
    hK target htargetLen pref hpref A σ w hwt hcert hmin
  have hparentTarget :
      (((A, pref ++ σ), w) :
          (g.nt × List g.flag) × List T) ∈
        ({item : (g.nt × List g.flag) × List T |
          item.1.2.length ≤ N + K ∧ item.2 <+ target ∧
            NFYield g item.1.1 item.1.2 item.2} :
          Set ((g.nt × List g.flag) × List T)) :=
    bounded_prefix_certificate_mem_bounded_target_items
      (g := g) (N := N) (K := K) hpref hwt hσlen hcert
  have hparentLength :
      (((A, pref ++ σ), w) :
          (g.nt × List g.flag) × List T) ∈
        ({item : (g.nt × List g.flag) × List T |
          item.1.2.length ≤ N + K ∧ item.2.length ≤ L ∧
            NFYield g item.1.1 item.1.2 item.2} :
          Set ((g.nt × List g.flag) × List T)) := by
    have hwlen : w.length ≤ L := le_trans hwt.length_le htargetLen
    exact bounded_prefix_certificate_mem_bounded_length_items
      (g := g) (N := N) (K := K) (L := L) hpref hwlen hσlen hcert
  refine ⟨hσlen, hparentTarget, hparentLength, ?_⟩
  rcases hcases with hbin | hpopEmpty | hpopPrefix | hpush | hterm
  · rcases hbin with
      ⟨B, C, u, v, r, hr, hlhs, hc, hrhs, hw, hupos, hvpos, hult, hvlt,
        hut, hvt, hleft, hright, hpairMin⟩
    left
    refine ⟨B, C, u, v, r, hr, hlhs, hc, hrhs, hw,
      hupos, hvpos, hult, hvlt, hut, hvt, hleft, hright, hpairMin, ?_⟩
    exact bounded_prefix_binary_branch_mem_frontiers
      (g := g) (N := N) (K := K) (L := L)
      (target := target) (u := u) (v := v) (w := w)
      (A := A) (B := B) (C := C) (pref := pref) (τ := σ)
      hpref htargetLen hut hvt hwt hσlen hleft hright hcert
  · rcases hpopEmpty with
      ⟨f, ρ, B, r, hr, hprefEmpty, hσ, hρlen, hlhs, hc, hrhs, hchild, hchildMin⟩
    right
    left
    refine ⟨f, ρ, B, r, hr, hprefEmpty, hσ, hρlen,
      hlhs, hc, hrhs, hchild, hchildMin, ?_⟩
    exact empty_prefix_pop_branch_mem_frontiers
      (g := g) (K := K) (L := L) (target := target)
      (w := w) (B := B) (ρ := ρ) htargetLen hwt hρlen hchild
  · rcases hpopPrefix with
      ⟨f, pref', B, r, hr, hprefEq, hpref'len, hlhs, hc, hrhs, hchild, hchildMin⟩
    right
    right
    left
    refine ⟨f, pref', B, r, hr, hprefEq, hpref'len,
      hlhs, hc, hrhs, hchild, hchildMin, ?_⟩
    exact shortened_prefix_pop_branch_mem_frontiers
      (g := g) (N := N) (K := K) (L := L)
      (target := target) (w := w) (B := B)
      (pref' := pref') (σ := σ) hpref'len htargetLen hwt hσlen hchild
  · rcases hpush with
      ⟨B, f, r, hr, hlhs, hc, hrhs, hchild, hchildMin⟩
    right
    right
    right
    left
    refine ⟨B, f, r, hr, hchild, hlhs, hc, hrhs, hchildMin, ?_⟩
    exact bounded_prefix_push_branch_mem_frontiers
      (g := g) (N := N) (K := K) (L := L)
      (target := target) (w := w) (A := A) (B := B)
      (pref := pref) (τ := σ) (f := f)
      hpref htargetLen hwt hσlen hchild hcert
  · right
    right
    right
    right
    exact hterm

end NFYield

end IndexedGrammar
