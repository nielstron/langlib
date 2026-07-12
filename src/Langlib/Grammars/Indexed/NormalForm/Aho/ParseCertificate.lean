module

public import Langlib.Grammars.Indexed.NormalForm.ParseTree
@[expose]
public section

/-!
# Data-carrying normal-form indexed parse certificates

`IndexedGrammar.NFYield` is intentionally proposition-valued.  Aho's marked simulation must,
however, follow individual pushed flag occurrences through one chosen parse.  Proof irrelevance
means that this information cannot soundly be indexed by an `NFYield` proof itself, so this file
introduces the parallel Type-valued certificate `NFParse`.

Every `NFYield` proposition has a nonempty `NFParse` type, and every `NFParse` erases back to an
`NFYield` proof.  We then define whether one root-stack occurrence is consumed in that concrete
parse and prove that an occurrence which is not consumed can be erased throughout the tree.
-/

variable {T : Type}

namespace IndexedGrammar

/-- A data-carrying version of `NFYield`.  Its constructors have exactly the four normal-form
rule shapes, but the result lives in `Type` so later algorithms may inspect the chosen tree. -/
public inductive NFParse (g : IndexedGrammar T) :
    g.nt → List g.flag → List T → Type where
  | binary {A B C : g.nt} {σ : List g.flag} {u v : List T}
      {r : IRule T g.nt g.flag}
      (hr : r ∈ g.rules)
      (hlhs : r.lhs = A)
      (hc : r.consume = none)
      (hrhs : r.rhs =
        [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none])
      (left : NFParse g B σ u)
      (right : NFParse g C σ v) :
      NFParse g A σ (u ++ v)
  | pop {A B : g.nt} {f : g.flag} {ρ : List g.flag} {w : List T}
      {r : IRule T g.nt g.flag}
      (hr : r ∈ g.rules)
      (hlhs : r.lhs = A)
      (hc : r.consume = some f)
      (hrhs : r.rhs = [IRhsSymbol.nonterminal B none])
      (rest : NFParse g B ρ w) :
      NFParse g A (f :: ρ) w
  | push {A B : g.nt} {f : g.flag} {σ : List g.flag} {w : List T}
      {r : IRule T g.nt g.flag}
      (hr : r ∈ g.rules)
      (hlhs : r.lhs = A)
      (hc : r.consume = none)
      (hrhs : r.rhs = [IRhsSymbol.nonterminal B (some f)])
      (rest : NFParse g B (f :: σ) w) :
      NFParse g A σ w
  | terminal {A : g.nt} {σ : List g.flag} {a : T}
      {r : IRule T g.nt g.flag}
      (hr : r ∈ g.rules)
      (hlhs : r.lhs = A)
      (hc : r.consume = none)
      (hrhs : r.rhs = [IRhsSymbol.terminal a]) :
      NFParse g A σ [a]

namespace NFParse

/-- Forget the data-carrying tree and retain the proposition-valued certificate. -/
public def toNFYield {g : IndexedGrammar T} {A : g.nt} {σ : List g.flag} {w : List T} :
    NFParse g A σ w → NFYield g A σ w
  | .binary hr hlhs hc hrhs left right =>
      NFYield.binary hr hlhs hc hrhs left.toNFYield right.toNFYield
  | .pop hr hlhs hc hrhs rest =>
      NFYield.pop hr hlhs hc hrhs rest.toNFYield
  | .push hr hlhs hc hrhs rest =>
      NFYield.push hr hlhs hc hrhs rest.toNFYield
  | .terminal hr hlhs hc hrhs =>
      NFYield.terminal hr hlhs hc hrhs

/-- Every data-carrying normal-form parse has a nonempty terminal yield. -/
public theorem yield_length_pos
    {g : IndexedGrammar T} {A : g.nt} {σ : List g.flag} {w : List T}
    (p : NFParse g A σ w) : 0 < w.length :=
  NFYield.yield_length_pos p.toNFYield

/-- Every proposition-valued normal-form parse has a data-carrying representative. -/
public theorem nonempty_of_nfyield
    {g : IndexedGrammar T} {A : g.nt} {σ : List g.flag} {w : List T}
    (h : NFYield g A σ w) :
    Nonempty (NFParse g A σ w) := by
  induction h with
  | binary hr hlhs hc hrhs hleft hright ihleft ihright =>
      rcases ihleft with ⟨left⟩
      rcases ihright with ⟨right⟩
      exact ⟨NFParse.binary hr hlhs hc hrhs left right⟩
  | pop hr hlhs hc hrhs hrest ih =>
      rcases ih with ⟨rest⟩
      exact ⟨NFParse.pop hr hlhs hc hrhs rest⟩
  | push hr hlhs hc hrhs hrest ih =>
      rcases ih with ⟨rest⟩
      exact ⟨NFParse.push hr hlhs hc hrhs rest⟩
  | terminal hr hlhs hc hrhs =>
      exact ⟨NFParse.terminal hr hlhs hc hrhs⟩

/-- Choose a concrete data-carrying representative of an `NFYield` proof. -/
public noncomputable def ofNFYield
    {g : IndexedGrammar T} {A : g.nt} {σ : List g.flag} {w : List T}
    (h : NFYield g A σ w) : NFParse g A σ w :=
  Classical.choice (nonempty_of_nfyield h)

/-- The data-carrying and proposition-valued certificate presentations are equivalent. -/
public theorem nonempty_iff_nfyield
    {g : IndexedGrammar T} {A : g.nt} {σ : List g.flag} {w : List T} :
    Nonempty (NFParse g A σ w) ↔ NFYield g A σ w := by
  constructor
  · rintro ⟨p⟩
    exact p.toNFYield
  · exact nonempty_of_nfyield

/-- At the initial nonterminal, concrete parse trees characterize normal-form generation. -/
public theorem nonempty_initial_iff_generates
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {w : List T} :
    Nonempty (NFParse g g.initial [] w) ↔ g.Generates w := by
  rw [nonempty_iff_nfyield]
  exact (NFYield.generates_iff_isNormalForm (g := g) hNF).symm

/-- `ConsumesAt p k` says that some pop in the concrete parse `p` consumes the occurrence
initially at root-stack position `k` (positions start at zero). -/
public def ConsumesAt {g : IndexedGrammar T} {A : g.nt} {σ : List g.flag} {w : List T}
    (p : NFParse g A σ w) (k : ℕ) : Prop :=
  match p with
  | .binary _ _ _ _ left right => left.ConsumesAt k ∨ right.ConsumesAt k
  | .pop _ _ _ _ rest => k = 0 ∨ rest.ConsumesAt (k - 1)
  | .push _ _ _ _ rest => rest.ConsumesAt (k + 1)
  | .terminal _ _ _ _ => False

@[simp] public theorem consumesAt_binary_iff
    {g : IndexedGrammar T} {A B C : g.nt} {σ : List g.flag} {u v : List T}
    {r : IRule T g.nt g.flag}
    (hr : r ∈ g.rules) (hlhs : r.lhs = A) (hc : r.consume = none)
    (hrhs : r.rhs =
      [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none])
    (left : NFParse g B σ u) (right : NFParse g C σ v) (k : ℕ) :
    (NFParse.binary hr hlhs hc hrhs left right).ConsumesAt k ↔
      left.ConsumesAt k ∨ right.ConsumesAt k :=
  Iff.rfl

@[simp] public theorem consumesAt_pop_zero
    {g : IndexedGrammar T} {A B : g.nt} {f : g.flag} {ρ : List g.flag} {w : List T}
    {r : IRule T g.nt g.flag}
    (hr : r ∈ g.rules) (hlhs : r.lhs = A) (hc : r.consume = some f)
    (hrhs : r.rhs = [IRhsSymbol.nonterminal B none])
    (rest : NFParse g B ρ w) :
    (NFParse.pop hr hlhs hc hrhs rest).ConsumesAt 0 := by
  exact Or.inl rfl

@[simp] public theorem consumesAt_pop_succ_iff
    {g : IndexedGrammar T} {A B : g.nt} {f : g.flag} {ρ : List g.flag} {w : List T}
    {r : IRule T g.nt g.flag}
    (hr : r ∈ g.rules) (hlhs : r.lhs = A) (hc : r.consume = some f)
    (hrhs : r.rhs = [IRhsSymbol.nonterminal B none])
    (rest : NFParse g B ρ w) (k : ℕ) :
    (NFParse.pop hr hlhs hc hrhs rest).ConsumesAt (k + 1) ↔
      rest.ConsumesAt k := by
  simp [ConsumesAt]

@[simp] public theorem consumesAt_push_iff
    {g : IndexedGrammar T} {A B : g.nt} {f : g.flag} {σ : List g.flag} {w : List T}
    {r : IRule T g.nt g.flag}
    (hr : r ∈ g.rules) (hlhs : r.lhs = A) (hc : r.consume = none)
    (hrhs : r.rhs = [IRhsSymbol.nonterminal B (some f)])
    (rest : NFParse g B (f :: σ) w) (k : ℕ) :
    (NFParse.push hr hlhs hc hrhs rest).ConsumesAt k ↔
      rest.ConsumesAt (k + 1) :=
  Iff.rfl

@[simp] public theorem not_consumesAt_terminal
    {g : IndexedGrammar T} {A : g.nt} {σ : List g.flag} {a : T}
    {r : IRule T g.nt g.flag}
    (hr : r ∈ g.rules) (hlhs : r.lhs = A) (hc : r.consume = none)
    (hrhs : r.rhs = [IRhsSymbol.terminal a]) (k : ℕ) :
    ¬ (NFParse.terminal (σ := σ) hr hlhs hc hrhs).ConsumesAt k := by
  simp [ConsumesAt]

/-- Erase an inherited occurrence which is never consumed in a concrete parse. -/
public def eraseIdxOfNotConsumesAt
    {g : IndexedGrammar T} {A : g.nt} {σ : List g.flag} {w : List T}
    (p : NFParse g A σ w) (k : ℕ) (unused : ¬ p.ConsumesAt k) :
    NFParse g A (σ.eraseIdx k) w :=
  match p with
  | .binary hr hlhs hc hrhs left right =>
      NFParse.binary hr hlhs hc hrhs
        (left.eraseIdxOfNotConsumesAt k (fun h => unused (Or.inl h)))
        (right.eraseIdxOfNotConsumesAt k (fun h => unused (Or.inr h)))
  | .pop hr hlhs hc hrhs rest =>
      match k with
      | 0 => False.elim (unused (Or.inl rfl))
      | k + 1 =>
          NFParse.pop hr hlhs hc hrhs
            (rest.eraseIdxOfNotConsumesAt k (by
              intro h
              exact unused (by simpa [ConsumesAt] using h)))
  | .push hr hlhs hc hrhs rest =>
      NFParse.push hr hlhs hc hrhs
        (rest.eraseIdxOfNotConsumesAt (k + 1) (by
          simpa [ConsumesAt] using unused))
  | .terminal hr hlhs hc hrhs =>
      NFParse.terminal hr hlhs hc hrhs

/-- Proposition-level corollary of `eraseIdxOfNotConsumesAt`. -/
public theorem nfyield_eraseIdx_of_not_consumesAt
    {g : IndexedGrammar T} {A : g.nt} {σ : List g.flag} {w : List T}
    (p : NFParse g A σ w) (k : ℕ) (unused : ¬ p.ConsumesAt k) :
    NFYield g A (σ.eraseIdx k) w :=
  (p.eraseIdxOfNotConsumesAt k unused).toNFYield

/-! ## Productive-node accounting -/

/-- The number of terminal leaves in a concrete normal-form parse. -/
public def terminalCount {g : IndexedGrammar T} {A : g.nt} {σ : List g.flag} {w : List T} :
    NFParse g A σ w → ℕ
  | .binary _ _ _ _ left right => left.terminalCount + right.terminalCount
  | .pop _ _ _ _ rest => rest.terminalCount
  | .push _ _ _ _ rest => rest.terminalCount
  | .terminal _ _ _ _ => 1

/-- The number of binary nodes in a concrete normal-form parse. -/
public def binaryCount {g : IndexedGrammar T} {A : g.nt} {σ : List g.flag} {w : List T} :
    NFParse g A σ w → ℕ
  | .binary _ _ _ _ left right => left.binaryCount + right.binaryCount + 1
  | .pop _ _ _ _ rest => rest.binaryCount
  | .push _ _ _ _ rest => rest.binaryCount
  | .terminal _ _ _ _ => 0

/-- Productive events are binary expansions and terminal emissions. -/
public def productiveCount {g : IndexedGrammar T} {A : g.nt} {σ : List g.flag} {w : List T}
    (p : NFParse g A σ w) : ℕ :=
  p.binaryCount + p.terminalCount

/-- Terminal leaves count the length of the yield exactly. -/
@[simp] public theorem terminalCount_eq_yield_length
    {g : IndexedGrammar T} {A : g.nt} {σ : List g.flag} {w : List T}
    (p : NFParse g A σ w) :
    p.terminalCount = w.length := by
  induction p with
  | binary _ _ _ _ left right ihleft ihright =>
      simp [terminalCount, List.length_append, ihleft, ihright]
  | pop _ _ _ _ rest ih =>
      simpa [terminalCount] using ih
  | push _ _ _ _ rest ih =>
      simpa [terminalCount] using ih
  | terminal _ _ _ _ =>
      simp [terminalCount]

/-- A nonempty full binary parse has one fewer binary nodes than terminal leaves. -/
public theorem binaryCount_add_one_eq_terminalCount
    {g : IndexedGrammar T} {A : g.nt} {σ : List g.flag} {w : List T}
    (p : NFParse g A σ w) :
    p.binaryCount + 1 = p.terminalCount := by
  induction p with
  | binary _ _ _ _ left right ihleft ihright =>
      simp only [binaryCount, terminalCount]
      omega
  | pop _ _ _ _ rest ih =>
      simpa [binaryCount, terminalCount] using ih
  | push _ _ _ _ rest ih =>
      simpa [binaryCount, terminalCount] using ih
  | terminal _ _ _ _ =>
      simp [binaryCount, terminalCount]

/-- The number of productive events is at most twice the terminal yield length. -/
public theorem productiveCount_le_twice_yield_length
    {g : IndexedGrammar T} {A : g.nt} {σ : List g.flag} {w : List T}
    (p : NFParse g A σ w) :
    p.productiveCount ≤ 2 * w.length := by
  have ht := p.terminalCount_eq_yield_length
  have hb := p.binaryCount_add_one_eq_terminalCount
  simp only [productiveCount]
  omega

end NFParse

end IndexedGrammar
