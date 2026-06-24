module

public import Langlib.Grammars.Indexed.NormalForm.Bounds
@[expose]
public section

/-! # Parse certificates for indexed normal form

This file gives a depth-first certificate relation for singleton terminal derivations from a
normal-form indexed grammar. The constructors mirror the four normal-form rule shapes and are
proved equivalent to the existing counted derivation semantics.
-/

variable {T : Type}

namespace IndexedGrammar

/-- A structural certificate that one indexed nonterminal with a concrete stack yields a terminal
word using normal-form rule shapes. -/
public inductive NFYield (g : IndexedGrammar T) : g.nt → List g.flag → List T → Prop where
  | binary {A B C : g.nt} {σ : List g.flag} {u v : List T}
      {r : IRule T g.nt g.flag}
      (hr : r ∈ g.rules)
      (hlhs : r.lhs = A)
      (hc : r.consume = none)
      (hrhs : r.rhs =
        [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none])
      (hleft : NFYield g B σ u)
      (hright : NFYield g C σ v) :
      NFYield g A σ (u ++ v)
  | pop {A B : g.nt} {f : g.flag} {ρ : List g.flag} {w : List T}
      {r : IRule T g.nt g.flag}
      (hr : r ∈ g.rules)
      (hlhs : r.lhs = A)
      (hc : r.consume = some f)
      (hrhs : r.rhs = [IRhsSymbol.nonterminal B none])
      (hrest : NFYield g B ρ w) :
      NFYield g A (f :: ρ) w
  | push {A B : g.nt} {f : g.flag} {σ : List g.flag} {w : List T}
      {r : IRule T g.nt g.flag}
      (hr : r ∈ g.rules)
      (hlhs : r.lhs = A)
      (hc : r.consume = none)
      (hrhs : r.rhs = [IRhsSymbol.nonterminal B (some f)])
      (hrest : NFYield g B (f :: σ) w) :
      NFYield g A σ w
  | terminal {A : g.nt} {σ : List g.flag} {a : T}
      {r : IRule T g.nt g.flag}
      (hr : r ∈ g.rules)
      (hlhs : r.lhs = A)
      (hc : r.consume = none)
      (hrhs : r.rhs = [IRhsSymbol.terminal a]) :
      NFYield g A σ [a]

namespace NFYield

theorem transforms_binary_of_rule {g : IndexedGrammar T}
    {A B C : g.nt} {σ : List g.flag} {r : IRule T g.nt g.flag}
    (hr : r ∈ g.rules)
    (hlhs : r.lhs = A)
    (hc : r.consume = none)
    (hrhs : r.rhs = [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none]) :
    g.Transforms [ISym.indexed A σ] [ISym.indexed B σ, ISym.indexed C σ] := by
  refine ⟨r, [], [], σ, hr, ?_, ?_⟩
  · rw [hc, hlhs]
    rfl
  · rw [hrhs]
    simp [expandRhs]

theorem transforms_pop_of_rule {g : IndexedGrammar T}
    {A B : g.nt} {f : g.flag} {ρ : List g.flag} {r : IRule T g.nt g.flag}
    (hr : r ∈ g.rules)
    (hlhs : r.lhs = A)
    (hc : r.consume = some f)
    (hrhs : r.rhs = [IRhsSymbol.nonterminal B none]) :
    g.Transforms [ISym.indexed A (f :: ρ)] [ISym.indexed B ρ] := by
  refine ⟨r, [], [], ρ, hr, ?_, ?_⟩
  · rw [hc, hlhs]
    rfl
  · rw [hrhs]
    simp [expandRhs]

theorem transforms_push_of_rule {g : IndexedGrammar T}
    {A B : g.nt} {f : g.flag} {σ : List g.flag} {r : IRule T g.nt g.flag}
    (hr : r ∈ g.rules)
    (hlhs : r.lhs = A)
    (hc : r.consume = none)
    (hrhs : r.rhs = [IRhsSymbol.nonterminal B (some f)]) :
    g.Transforms [ISym.indexed A σ] [ISym.indexed B (f :: σ)] := by
  refine ⟨r, [], [], σ, hr, ?_, ?_⟩
  · rw [hc, hlhs]
    rfl
  · rw [hrhs]
    simp [expandRhs]

theorem transforms_terminal_of_rule {g : IndexedGrammar T}
    {A : g.nt} {σ : List g.flag} {a : T} {r : IRule T g.nt g.flag}
    (hr : r ∈ g.rules)
    (hlhs : r.lhs = A)
    (hc : r.consume = none)
    (hrhs : r.rhs = [IRhsSymbol.terminal a]) :
    g.Transforms [ISym.indexed A σ] [ISym.terminal a] := by
  refine ⟨r, [], [], σ, hr, ?_, ?_⟩
  · rw [hc, hlhs]
    rfl
  · rw [hrhs]
    simp [expandRhs]

/-- A parse certificate composes to a counted indexed-grammar derivation. -/
public theorem exists_derivesIn {g : IndexedGrammar T}
    {A : g.nt} {σ : List g.flag} {w : List T}
    (h : NFYield g A σ w) :
    ∃ n, g.DerivesIn n [ISym.indexed A σ]
      (w.map fun a => (ISym.terminal a : g.ISym)) := by
  induction h with
  | binary hr hlhs hc hrhs _ _ ihleft ihright =>
      rcases ihleft with ⟨m, hleft⟩
      rcases ihright with ⟨k, hright⟩
      have hpair := derivesIn_pair_to_terminals_of_derivesIn (g := g) hleft hright
      exact ⟨1 + (m + k),
        derivesIn_trans
          (derivesIn_one_of_transforms
            (transforms_binary_of_rule (g := g) hr hlhs hc hrhs))
          hpair⟩
  | pop hr hlhs hc hrhs _ ihrest =>
      rcases ihrest with ⟨n, hrest⟩
      exact ⟨1 + n,
        derivesIn_trans
          (derivesIn_one_of_transforms
            (transforms_pop_of_rule (g := g) hr hlhs hc hrhs))
          hrest⟩
  | push hr hlhs hc hrhs _ ihrest =>
      rcases ihrest with ⟨n, hrest⟩
      exact ⟨1 + n,
        derivesIn_trans
          (derivesIn_one_of_transforms
            (transforms_push_of_rule (g := g) hr hlhs hc hrhs))
          hrest⟩
  | terminal hr hlhs hc hrhs =>
      exact ⟨1,
        derivesIn_one_of_transforms
          (transforms_terminal_of_rule (g := g) hr hlhs hc hrhs)⟩

/-- A parse certificate composes to the uncounted indexed-grammar derivation semantics. -/
public theorem derives {g : IndexedGrammar T}
    {A : g.nt} {σ : List g.flag} {w : List T}
    (h : NFYield g A σ w) :
    g.Derives [ISym.indexed A σ]
      (w.map fun a => (ISym.terminal a : g.ISym)) := by
  rcases exists_derivesIn (g := g) h with ⟨n, hn⟩
  exact derives_of_derivesIn (g := g) hn

/-- Every counted singleton terminal derivation in normal form has a parse certificate. -/
public theorem of_derivesIn_isNormalForm {g : IndexedGrammar T}
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {n : ℕ} {A : g.nt} {σ : List g.flag} {w : List T}
    (hder : g.DerivesIn n [ISym.indexed A σ]
      (w.map fun a => (ISym.terminal a : g.ISym))) :
    NFYield g A σ w := by
  induction n using Nat.strong_induction_on generalizing A σ w with
  | h n ih =>
      cases n with
      | zero =>
          have heq : [ISym.indexed A σ] =
              w.map fun a => (ISym.terminal a : g.ISym) := by
            simpa using hder
          cases w with
          | nil => simp at heq
          | cons a w => simp at heq
      | succ n =>
          have hder' :
              g.DerivesIn (n + 1) [ISym.indexed A σ]
                (w.map fun a => (ISym.terminal a : g.ISym)) := by
            simpa [Nat.succ_eq_add_one] using hder
          have hcases :=
            derivesIn_singleton_to_terminals_rule_cases_with_target_bounds_of_isNormalForm
              (g := g) hNF (n := n) (A := A) (σ := σ) (w := w) (target := w)
              (List.Sublist.refl w) hder'
          rcases hcases with hbin | hpop | hpush | hterm
          · rcases hbin with
              ⟨B, C, m, k, u, v, r, hr, hlhs, hc, hrhs, _hmk, hm_lt, hk_lt,
                hw, _hu_pos, _hv_pos, _hu_lt, _hv_lt, _hu_sub, _hv_sub,
                hleft, hright⟩
            subst w
            exact NFYield.binary hr hlhs hc hrhs
              (ih m (by simpa [Nat.succ_eq_add_one] using hm_lt) hleft)
              (ih k (by simpa [Nat.succ_eq_add_one] using hk_lt) hright)
          · rcases hpop with
              ⟨f, ρ, B, r, hr, hσ, hlhs, hc, hrhs, hn_lt, hrest⟩
            have hcert : NFYield g A (f :: ρ) w :=
              NFYield.pop hr hlhs hc hrhs
                (ih n (Nat.lt_succ_self n) hrest)
            simpa [hσ] using hcert
          · rcases hpush with
              ⟨B, f, r, hr, hlhs, hc, hrhs, hn_lt, hrest⟩
            exact NFYield.push hr hlhs hc hrhs
              (ih n (Nat.lt_succ_self n) hrest)
          · rcases hterm with ⟨a, r, hr, hlhs, hc, hrhs, hw, _hn⟩
            simpa [hw] using (NFYield.terminal (g := g) (σ := σ) hr hlhs hc hrhs)

/-- Uncounted singleton terminal derivations in normal form are exactly parse certificates. -/
public theorem iff_derives_isNormalForm {g : IndexedGrammar T}
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {A : g.nt} {σ : List g.flag} {w : List T} :
    NFYield g A σ w ↔
      g.Derives [ISym.indexed A σ]
        (w.map fun a => (ISym.terminal a : g.ISym)) := by
  constructor
  · exact derives
  · intro hder
    rcases exists_derivesIn_of_derives (g := g) hder with ⟨n, hn⟩
    exact of_derivesIn_isNormalForm (g := g) hNF hn

/-- Counted singleton terminal derivability in normal form is equivalent to existence of a
parse certificate. -/
public theorem iff_exists_derivesIn_isNormalForm {g : IndexedGrammar T}
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {A : g.nt} {σ : List g.flag} {w : List T} :
    NFYield g A σ w ↔
      ∃ n, g.DerivesIn n [ISym.indexed A σ]
        (w.map fun a => (ISym.terminal a : g.ISym)) := by
  constructor
  · exact exists_derivesIn
  · rintro ⟨n, hn⟩
    exact of_derivesIn_isNormalForm (g := g) hNF hn

end NFYield

end IndexedGrammar
