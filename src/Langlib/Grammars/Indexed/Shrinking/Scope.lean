module

public import Langlib.Grammars.Indexed.NormalForm.Aho.ParseCertificate

@[expose]
public section

/-!
# Flag scopes in normal-form indexed parse trees

This file formalizes the scope construction used in Gilman's shrinking lemma.
For one occurrence in the root flag stack, `NFParse.scopeAt` follows every
branch until that occurrence is consumed.  Its ordered frontier consists of
terminals and of the continuation parses immediately below the consuming
pop.  Carrying those continuation parses makes both the frontier derivation
and the corresponding factorization of the terminal yield explicit.

## Reference

* R. H. Gilman, "A shrinking lemma for indexed languages",
  *Theoretical Computer Science* 163 (1996), 277--281.
-/

variable {T : Type}

namespace IndexedGrammar

/-- One leaf of a flag scope.  A pending leaf remembers the complete parse
below the pop which consumed the distinguished flag occurrence. -/
public inductive ScopePiece (g : IndexedGrammar T) (suffix : List g.flag) : Type where
  | terminal (a : T) : ScopePiece g suffix
  | pending {A : g.nt} {w : List T} (parse : NFParse g A suffix w) :
      ScopePiece g suffix

namespace ScopePiece

/-- The terminal factor contributed by one scope-frontier leaf. -/
public def word {g : IndexedGrammar T} {suffix : List g.flag} :
    ScopePiece g suffix → List T
  | .terminal a => [a]
  | .pending (w := w) _ => w

/-- The unstacked sentential symbol displayed by a scope-frontier leaf. -/
public def symbol {g : IndexedGrammar T} {suffix : List g.flag} :
    ScopePiece g suffix → g.nt ⊕ T
  | .terminal a => Sum.inr a
  | .pending (A := A) _ => Sum.inl A

/-- Interpret a scope piece as an indexed-grammar sentential symbol. -/
public def asISym {g : IndexedGrammar T} {suffix : List g.flag} :
    ScopePiece g suffix → g.ISym
  | .terminal a => ISym.terminal a
  | .pending (A := A) _ => ISym.indexed A suffix

@[simp] public theorem word_terminal {g : IndexedGrammar T} {suffix : List g.flag}
    (a : T) : (ScopePiece.terminal (g := g) (suffix := suffix) a).word = [a] := rfl

@[simp] public theorem word_pending {g : IndexedGrammar T} {suffix : List g.flag}
    {A : g.nt} {w : List T} (p : NFParse g A suffix w) :
    (ScopePiece.pending p).word = w := rfl

@[simp] public theorem symbol_terminal {g : IndexedGrammar T} {suffix : List g.flag}
    (a : T) : (ScopePiece.terminal (g := g) (suffix := suffix) a).symbol = Sum.inr a := rfl

@[simp] public theorem symbol_pending {g : IndexedGrammar T} {suffix : List g.flag}
    {A : g.nt} {w : List T} (p : NFParse g A suffix w) :
    (ScopePiece.pending p).symbol = Sum.inl A := rfl

@[simp] public theorem asISym_terminal {g : IndexedGrammar T} {suffix : List g.flag}
    (a : T) : (ScopePiece.terminal (g := g) (suffix := suffix) a).asISym =
      ISym.terminal a := rfl

@[simp] public theorem asISym_pending {g : IndexedGrammar T} {suffix : List g.flag}
    {A : g.nt} {w : List T} (p : NFParse g A suffix w) :
    (ScopePiece.pending p).asISym = ISym.indexed A suffix := rfl

public theorem word_ne_nil {g : IndexedGrammar T} {suffix : List g.flag}
    (piece : ScopePiece g suffix) : piece.word ≠ [] := by
  cases piece with
  | terminal => simp
  | pending parse =>
      exact List.ne_nil_of_length_pos parse.yield_length_pos

end ScopePiece

namespace NFParse

/-- Cut a concrete parse at the first consumption of the root-stack
occurrence numbered `k`.  The remaining stack below that occurrence is
`sigma.drop (k + 1)`, which is exactly the stack carried by pending frontier
leaves. -/
public def scopeAt {g : IndexedGrammar T} {A : g.nt} {sigma : List g.flag}
    {w : List T} (p : NFParse g A sigma w) (k : Nat) :
    List (ScopePiece g (sigma.drop (k + 1))) :=
  match p with
  | .binary _ _ _ _ left right => scopeAt left k ++ scopeAt right k
  | .pop _ _ _ _ rest =>
      match k with
      | 0 => [ScopePiece.pending rest]
      | k + 1 => scopeAt rest k
  | .push _ _ _ _ rest => scopeAt rest (k + 1)
  | .terminal (a := a) _ _ _ _ => [ScopePiece.terminal a]

/-- Concatenate the terminal factors represented by a scope frontier. -/
public def scopeWord {g : IndexedGrammar T} {suffix : List g.flag}
    (pieces : List (ScopePiece g suffix)) : List T :=
  pieces.flatMap ScopePiece.word

/-- Forget continuation certificates and retain the unstacked frontier word. -/
public def scopeSymbols {g : IndexedGrammar T} {suffix : List g.flag}
    (pieces : List (ScopePiece g suffix)) : List (g.nt ⊕ T) :=
  pieces.map ScopePiece.symbol

/-- Interpret an unstacked frontier word as a sentential form. -/
public def unstackedForm {g : IndexedGrammar T} (beta : List (g.nt ⊕ T)) :
    List g.ISym :=
  beta.map fun s =>
    match s with
    | Sum.inl A => ISym.indexed A []
    | Sum.inr a => ISym.terminal a

/-- Interpret a scope frontier at the concrete suffix carried by its pieces. -/
public def scopeForm {g : IndexedGrammar T} {suffix : List g.flag}
    (pieces : List (ScopePiece g suffix)) : List g.ISym :=
  pieces.map ScopePiece.asISym

@[simp] public theorem scopeWord_nil {g : IndexedGrammar T} {suffix : List g.flag} :
    scopeWord ([] : List (ScopePiece g suffix)) = ([] : List T) := rfl

@[simp] public theorem scopeWord_cons {g : IndexedGrammar T} {suffix : List g.flag}
    (piece : ScopePiece g suffix) (pieces : List (ScopePiece g suffix)) :
    scopeWord (piece :: pieces) = piece.word ++ scopeWord pieces := by
  simp [scopeWord]

@[simp] public theorem scopeWord_append {g : IndexedGrammar T} {suffix : List g.flag}
    (left right : List (ScopePiece g suffix)) :
    scopeWord (left ++ right) = scopeWord left ++ scopeWord right := by
  simp [scopeWord, List.flatMap_append]

@[simp] public theorem scopeSymbols_length {g : IndexedGrammar T}
    {suffix : List g.flag} (pieces : List (ScopePiece g suffix)) :
    (scopeSymbols pieces).length = pieces.length := by
  simp [scopeSymbols]

@[simp] public theorem scopeForm_eq_appendStackSuffixes_unstackedForm
    {g : IndexedGrammar T} {suffix : List g.flag}
    (pieces : List (ScopePiece g suffix)) :
    scopeForm pieces = appendStackSuffixes suffix (unstackedForm (scopeSymbols pieces)) := by
  induction pieces with
  | nil => rfl
  | cons piece pieces ih =>
      cases piece <;> simp_all [scopeForm, scopeSymbols, unstackedForm]

/-- Cutting a scope partitions, but never changes, the terminal yield. -/
public theorem scopeWord_scopeAt {g : IndexedGrammar T} {A : g.nt}
    {sigma : List g.flag} {w : List T} (p : NFParse g A sigma w) (k : Nat) :
    scopeWord (p.scopeAt k) = w := by
  induction p generalizing k with
  | binary _ _ _ _ left right ihleft ihrigh =>
      simp [scopeAt, ihleft, ihrigh]
  | pop _ _ _ _ rest ih =>
      cases k with
      | zero => simp [scopeAt]
      | succ k => simpa [scopeAt] using ih k
  | push _ _ _ _ rest ih =>
      simpa [scopeAt] using ih (k + 1)
  | terminal _ _ _ _ =>
      simp [scopeAt]

private theorem derives_append {g : IndexedGrammar T}
    {u u' v v' : List g.ISym} (hu : g.Derives u u') (hv : g.Derives v v') :
    g.Derives (u ++ v) (u' ++ v') := by
  exact (deri_with_suffix v hu).trans (deri_with_prefix u' hv)

/-- Independently finish every pending scope piece. -/
public theorem derives_scopeWord {g : IndexedGrammar T} {suffix : List g.flag}
    (pieces : List (ScopePiece g suffix)) :
    g.Derives (scopeForm pieces)
      ((scopeWord pieces).map fun a => (ISym.terminal a : g.ISym)) := by
  induction pieces with
  | nil => exact deri_self g []
  | cons piece pieces ih =>
      have hpiece : g.Derives [piece.asISym]
          (piece.word.map fun a => (ISym.terminal a : g.ISym)) := by
        cases piece with
        | terminal => exact deri_self g _
        | pending parse =>
            obtain ⟨_, hcounted⟩ := parse.toNFYield.exists_derivesIn
            exact derives_of_derivesIn hcounted
      simpa [scopeForm, scopeWord, List.map_append] using derives_append hpiece ih

/-- The concrete parse derives its scope frontier at the suffix below the
distinguished occurrence. -/
public theorem derives_scopeForm_scopeAt {g : IndexedGrammar T} {A : g.nt}
    {sigma : List g.flag} {w : List T} (p : NFParse g A sigma w) (k : Nat) :
    g.Derives [ISym.indexed A sigma] (scopeForm (p.scopeAt k)) := by
  induction p generalizing k with
  | binary hr hlhs hc hrhs left right ihleft ihrigh =>
      exact (deri_of_tran
        (NFYield.transforms_binary_of_rule (g := g) (σ := _)
          hr hlhs hc hrhs)).trans (by
        simpa [scopeAt, scopeForm, List.map_append] using
          derives_append (ihleft k) (ihrigh k))
  | pop hr hlhs hc hrhs rest ih =>
      cases k with
      | zero =>
          simpa [scopeAt, scopeForm] using deri_of_tran
            (NFYield.transforms_pop_of_rule (g := g) (ρ := _)
              hr hlhs hc hrhs)
      | succ k =>
          exact (deri_of_tran
            (NFYield.transforms_pop_of_rule (g := g) (ρ := _)
              hr hlhs hc hrhs)).trans (by simpa [scopeAt] using ih k)
  | push hr hlhs hc hrhs rest ih =>
      exact (deri_of_tran
        (NFYield.transforms_push_of_rule (g := g) (σ := _)
          hr hlhs hc hrhs)).trans (by simpa [scopeAt] using ih (k + 1))
  | terminal hr hlhs hc hrhs =>
      simpa [scopeAt, scopeForm] using deri_of_tran
        (NFYield.transforms_terminal_of_rule (g := g) (σ := _)
          hr hlhs hc hrhs)

/-- Remove the common suffix below a scope.  The same rule certificates derive
the unstacked frontier from the prefix ending at the distinguished occurrence. -/
public theorem derives_unstackedForm_scopeAt {g : IndexedGrammar T} {A : g.nt}
    {sigma : List g.flag} {w : List T} (p : NFParse g A sigma w) (k : Nat) :
    g.Derives [ISym.indexed A (sigma.take (k + 1))]
      (unstackedForm (scopeSymbols (p.scopeAt k))) := by
  induction p generalizing k with
  | binary hr hlhs hc hrhs left right ihleft ihrigh =>
      exact (deri_of_tran
        (NFYield.transforms_binary_of_rule (g := g) (σ := _)
          hr hlhs hc hrhs)).trans (by
        simpa [scopeAt, scopeSymbols, unstackedForm, List.map_append] using
          derives_append (ihleft k) (ihrigh k))
  | pop hr hlhs hc hrhs rest ih =>
      cases k with
      | zero =>
          simpa [scopeAt, scopeSymbols, unstackedForm] using deri_of_tran
            (NFYield.transforms_pop_of_rule (g := g) (ρ := [])
              hr hlhs hc hrhs)
      | succ k =>
          exact (deri_of_tran
            (NFYield.transforms_pop_of_rule (g := g) (ρ := _)
              hr hlhs hc hrhs)).trans (by
                simpa [scopeAt] using ih k)
  | push hr hlhs hc hrhs rest ih =>
      exact (deri_of_tran
        (NFYield.transforms_push_of_rule (g := g) (σ := _)
          hr hlhs hc hrhs)).trans (by
            simpa [scopeAt, Nat.add_assoc] using ih (k + 1))
  | terminal hr hlhs hc hrhs =>
      simpa [scopeAt, scopeSymbols, unstackedForm] using deri_of_tran
        (NFYield.transforms_terminal_of_rule (g := g) (σ := _)
          hr hlhs hc hrhs)

/-- Gilman's `beta(p)`: the full terminal yield at an empty stack, and the
unstacked frontier of the top flag scope at a nonempty stack. -/
public def beta {g : IndexedGrammar T} {A : g.nt} {sigma : List g.flag}
    {w : List T} (p : NFParse g A sigma w) : List (g.nt ⊕ T) :=
  match sigma with
  | [] => w.map Sum.inr
  | _ :: _ => scopeSymbols (p.scopeAt 0)

/-- The concrete scope pieces whose symbol word is `beta`.  At an empty
stack the pieces are the individual terminal leaves. -/
public def betaPieces {g : IndexedGrammar T} {A : g.nt} {sigma : List g.flag}
    {w : List T} (p : NFParse g A sigma w) :
    List (ScopePiece g sigma.tail) :=
  match sigma with
  | [] => w.map ScopePiece.terminal
  | _ :: _ => p.scopeAt 0

@[simp] public theorem scopeSymbols_betaPieces {g : IndexedGrammar T}
    {A : g.nt} {sigma : List g.flag} {w : List T}
    (p : NFParse g A sigma w) :
    scopeSymbols p.betaPieces = p.beta := by
  cases sigma <;> simp [betaPieces, beta, scopeSymbols]

@[simp] public theorem scopeWord_betaPieces {g : IndexedGrammar T}
    {A : g.nt} {sigma : List g.flag} {w : List T}
    (p : NFParse g A sigma w) :
    scopeWord p.betaPieces = w := by
  cases sigma with
  | nil =>
      simp [betaPieces, scopeWord, List.flatMap_map, Function.comp_def]
  | cons _ _ =>
      simpa [betaPieces] using p.scopeWord_scopeAt 0

@[simp] public theorem betaPieces_length {g : IndexedGrammar T}
    {A : g.nt} {sigma : List g.flag} {w : List T}
    (p : NFParse g A sigma w) :
    p.betaPieces.length = p.beta.length := by
  rw [← scopeSymbols_length p.betaPieces, scopeSymbols_betaPieces]

/-- The one-symbol source from which `beta` is derived. -/
public def betaSource {g : IndexedGrammar T} (A : g.nt) (sigma : List g.flag) :
    List g.ISym :=
  match sigma with
  | [] => [ISym.indexed A []]
  | f :: _ => [ISym.indexed A [f]]

@[simp] public theorem appendStackSuffixes_tail_betaSource
    {g : IndexedGrammar T} (A : g.nt) (sigma : List g.flag) :
    appendStackSuffixes sigma.tail (betaSource A sigma) =
      [ISym.indexed A sigma] := by
  cases sigma <;> simp [betaSource]

/-- Every parse-tree beta word is derivable from its unstacked source. -/
public theorem derives_beta {g : IndexedGrammar T} {A : g.nt}
    {sigma : List g.flag} {w : List T} (p : NFParse g A sigma w) :
    g.Derives (betaSource A sigma) (unstackedForm p.beta) := by
  cases sigma with
  | nil =>
      obtain ⟨_, hcounted⟩ := p.toNFYield.exists_derivesIn
      have hder := derives_of_derivesIn hcounted
      simpa [betaSource, beta, unstackedForm] using hder
  | cons f suffix =>
      simpa [betaSource, beta] using p.derives_unstackedForm_scopeAt 0

/-- A derivable unstacked subfrontier can be reattached to the concrete
suffix and its surviving pieces can then finish their original parses. -/
public theorem derives_scopeWord_of_derives_unstacked
    {g : IndexedGrammar T} {A : g.nt} {sigma : List g.flag}
    {x : List (g.nt ⊕ T)}
    (hder : g.Derives (betaSource A sigma) (unstackedForm x))
    (kept : List (ScopePiece g sigma.tail))
    (hkept : scopeSymbols kept = x) :
    g.Derives [ISym.indexed A sigma]
      ((scopeWord kept).map fun a => (ISym.terminal a : g.ISym)) := by
  have hlift := derives_appendStackSuffixes hder sigma.tail
  have hfront : g.Derives [ISym.indexed A sigma] (scopeForm kept) := by
    rw [appendStackSuffixes_tail_betaSource] at hlift
    rw [scopeForm_eq_appendStackSuffixes_unstackedForm, hkept]
    exact hlift
  exact hfront.trans (derives_scopeWord kept)

@[simp] public theorem beta_length_of_empty {g : IndexedGrammar T} {A : g.nt}
    {w : List T} (p : NFParse g A [] w) : p.beta.length = w.length := by
  simp [beta]

public theorem beta_length_eq_yield_of_stack_eq_nil
    {g : IndexedGrammar T} {A : g.nt} {sigma : List g.flag} {w : List T}
    (p : NFParse g A sigma w) (hstack : sigma = []) :
    p.beta.length = w.length := by
  subst sigma
  simp

@[simp] public theorem beta_length_of_nonempty {g : IndexedGrammar T} {A : g.nt}
    {f : g.flag} {suffix : List g.flag} {w : List T}
    (p : NFParse g A (f :: suffix) w) :
    p.beta.length = (p.scopeAt 0).length := by
  simp [beta, scopeSymbols]

public theorem beta_length_eq_scopeAt_zero_of_stack_ne_nil
    {g : IndexedGrammar T} {A : g.nt} {sigma : List g.flag} {w : List T}
    (p : NFParse g A sigma w) (hstack : sigma ≠ []) :
    p.beta.length = (p.scopeAt 0).length := by
  cases sigma with
  | nil => exact False.elim (hstack rfl)
  | cons _ _ => simp

@[simp] public theorem beta_binary {g : IndexedGrammar T}
    {A B C : g.nt} {sigma : List g.flag} {u v : List T}
    {r : IRule T g.nt g.flag}
    (hr : r ∈ g.rules) (hlhs : r.lhs = A) (hc : r.consume = none)
    (hrhs : r.rhs =
      [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none])
    (left : NFParse g B sigma u) (right : NFParse g C sigma v) :
    (NFParse.binary hr hlhs hc hrhs left right).beta =
      left.beta ++ right.beta := by
  cases sigma <;>
    simp [beta, scopeAt, scopeSymbols, List.map_append]

@[simp] public theorem beta_pop {g : IndexedGrammar T}
    {A B : g.nt} {f : g.flag} {suffix : List g.flag} {w : List T}
    {r : IRule T g.nt g.flag}
    (hr : r ∈ g.rules) (hlhs : r.lhs = A) (hc : r.consume = some f)
    (hrhs : r.rhs = [IRhsSymbol.nonterminal B none])
    (rest : NFParse g B suffix w) :
    (NFParse.pop hr hlhs hc hrhs rest).beta = [Sum.inl B] := by
  simp [beta, scopeAt, scopeSymbols]

@[simp] public theorem beta_terminal {g : IndexedGrammar T}
    {A : g.nt} {sigma : List g.flag} {a : T}
    {r : IRule T g.nt g.flag}
    (hr : r ∈ g.rules) (hlhs : r.lhs = A) (hc : r.consume = none)
    (hrhs : r.rhs = [IRhsSymbol.terminal a]) :
    (NFParse.terminal (σ := sigma) hr hlhs hc hrhs).beta = [Sum.inr a] := by
  cases sigma <;> simp [beta, scopeAt, scopeSymbols]

@[simp] public theorem beta_length_push_empty {g : IndexedGrammar T}
    {A B : g.nt} {f : g.flag} {w : List T}
    {r : IRule T g.nt g.flag}
    (hr : r ∈ g.rules) (hlhs : r.lhs = A) (hc : r.consume = none)
    (hrhs : r.rhs = [IRhsSymbol.nonterminal B (some f)])
    (rest : NFParse g B [f] w) :
    (NFParse.push hr hlhs hc hrhs rest).beta.length = w.length := by
  simp [beta]

@[simp] public theorem beta_length_push_nonempty {g : IndexedGrammar T}
    {A B : g.nt} {pushed top : g.flag} {suffix : List g.flag} {w : List T}
    {r : IRule T g.nt g.flag}
    (hr : r ∈ g.rules) (hlhs : r.lhs = A) (hc : r.consume = none)
    (hrhs : r.rhs = [IRhsSymbol.nonterminal B (some pushed)])
    (rest : NFParse g B (pushed :: top :: suffix) w) :
    (NFParse.push hr hlhs hc hrhs rest).beta.length =
      (rest.scopeAt 1).length := by
  simp [beta, scopeAt, scopeSymbols]

end NFParse

end IndexedGrammar
