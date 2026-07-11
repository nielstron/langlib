module

public import Langlib.Grammars.Indexed.NormalForm.Aho.Scheduler.Invariant

@[expose]
public section

/-!
# Pop certificates and continuations

Compressed pop paths, parse continuations, and rule certificates used by the scheduler.
-/

variable {T : Type}

namespace IndexedGrammar
namespace Aho

/-! ## Rule certificates used by the scheduler -/

/-! ### Canonical compression of a nonempty augmented-pop path -/

/-- A nonempty top-to-bottom sequence of augmented flag pops.  This is the semantic object
extracted from a maximal unary portion of the concrete parse before one productive event. -/
public inductive PopPath (g : IndexedGrammar T) :
    g.nt → List g.flag → g.nt → Prop where
  | one {A B : g.nt} {f : g.flag} (edge : AugPop g f A B) :
      PopPath g A [f] B
  | cons {A B C : g.nt} {f : g.flag} {flags : List g.flag}
      (edge : AugPop g f A B) (rest : PopPath g B flags C) :
      PopPath g A (f :: flags) C

/-- Neutral prefixes may be absorbed into the newly pre-saturated augmented pop relation. -/
public theorem augPop_preNeutral
    {g : IndexedGrammar T} {A X Y : g.nt} {f : g.flag}
    (hneutral : Neutral g A X) (hpop : AugPop g f X Y) : AugPop g f A Y := by
  rcases hpop with ⟨D, C, hprefix, hrule, hsuffix⟩
  exact ⟨D, C, hneutral.trans hprefix, hrule, hsuffix⟩

/-- Compress a syntactically nonempty concrete flag string. -/
public noncomputable def compressedFlags (g : IndexedGrammar T) [Fintype g.nt]
    (f : g.flag) : List g.flag → CFlag g
  | [] => cflagBase g f
  | f' :: flags => cflagComp g (cflagBase g f) (compressedFlags g f' flags)

namespace PopPath

/-- Absorb a neutral prefix into the first edge of a nonempty compressed pop path. -/
public theorem preNeutral {g : IndexedGrammar T} {A X Y : g.nt}
    {flags : List g.flag} (hneutral : Neutral g A X)
    (path : PopPath g X flags Y) : PopPath g A flags Y := by
  cases path with
  | one edge => exact .one (augPop_preNeutral hneutral edge)
  | cons edge rest => exact .cons (augPop_preNeutral hneutral edge) rest

/-- A pop path's flag string is nonempty. -/
public theorem flags_ne_nil {g : IndexedGrammar T} {A B : g.nt} {flags : List g.flag}
    (path : PopPath g A flags B) : flags ≠ [] := by
  cases path <;> simp

/-- The canonical compressed relation denotes exactly the path's concrete flag string. -/
public theorem denotes_compressedFlags {g : IndexedGrammar T} [Fintype g.nt]
    {A B : g.nt} {flags : List g.flag} (path : PopPath g A flags B) :
    ∃ f rest, flags = f :: rest ∧
      CFlag.Denotes g flags (compressedFlags g f rest) := by
  induction path with
  | @one A B f edge =>
      exact ⟨f, [], rfl, .base f⟩
  | @cons A B C f flags edge rest ih =>
      rcases ih with ⟨f', tail, hflags, hden⟩
      subst flags
      exact ⟨f, f' :: tail, rfl, .comp (.base f) hden⟩

/-- The endpoints of a pop path form an edge of its canonical compressed relation. -/
public theorem compressedFlags_edge {g : IndexedGrammar T} [Fintype g.nt]
    {A B : g.nt} {flags : List g.flag} (path : PopPath g A flags B) :
    ∃ f rest, flags = f :: rest ∧ compressedFlags g f rest A B = true := by
  induction path with
  | @one A B f edge =>
      refine ⟨f, [], rfl, ?_⟩
      simpa [compressedFlags] using (cflagBase_apply f A B).2 edge
  | @cons A B C f flags edge rest ih =>
      rcases ih with ⟨f', tail, hflags, hedge⟩
      subst flags
      refine ⟨f, f' :: tail, rfl, ?_⟩
      rw [compressedFlags, cflagComp_apply]
      exact ⟨B, (cflagBase_apply f A B).2 edge, hedge⟩

/-- Hence the compressed block accepted by a pop path is nonempty, as required by
`livePushCompress`. -/
public theorem compressedFlags_nonempty {g : IndexedGrammar T} [Fintype g.nt]
    {A B : g.nt} {flags : List g.flag} (path : PopPath g A flags B) :
    ∃ f rest, flags = f :: rest ∧ (compressedFlags g f rest).Nonempty := by
  rcases path.compressedFlags_edge with ⟨f, rest, hflags, hedge⟩
  exact ⟨f, rest, hflags, A, B, hedge⟩

/-- A pop path consumes its whole concrete block above every suffix. -/
public theorem derives {g : IndexedGrammar T} {A B : g.nt} {flags : List g.flag}
    (path : PopPath g A flags B) (suffix : List g.flag) :
    g.Derives [ISym.indexed A (flags ++ suffix)] [ISym.indexed B suffix] := by
  induction path generalizing suffix with
  | @one A B f edge =>
      simpa using augPop_derives edge suffix
  | @cons A B C f flags edge rest ih =>
      have hfirst := augPop_derives edge (flags ++ suffix)
      have hrest := ih suffix
      simpa [List.append_assoc] using hfirst.trans hrest

/-- Split the first edge from a path known to contain at least two concrete flags. -/
public theorem uncons {g : IndexedGrammar T} {A C : g.nt}
    {f f' : g.flag} {flags : List g.flag}
    (path : PopPath g A (f :: f' :: flags) C) :
    ∃ B, AugPop g f A B ∧ PopPath g B (f' :: flags) C := by
  cases path with
  | cons edge rest => exact ⟨_, edge, rest⟩

end PopPath

/-- A push, a stack-neutral unary segment, and the matching pop form a neutral derivation.
This is the cancellation used when a binary-free route temporarily pushes above the occurrence
it is following. -/
private theorem neutral_of_push_neutral_pop
    {g : IndexedGrammar T} {A B X Y : g.nt} {f : g.flag}
    (hpush : PushRule g A B f) (hneutral : Neutral g B X)
    (hpop : AugPop g f X Y) : Neutral g A Y := by
  have h₁ : g.Derives [ISym.indexed A []] [ISym.indexed B [f]] :=
    deri_of_tran (pushRule_transforms hpush [])
  have h₂ : g.Derives [ISym.indexed B [f]] [ISym.indexed X [f]] :=
    Neutral.lift_suffix hneutral [f]
  have h₃ : g.Derives [ISym.indexed X [f]] [ISym.indexed Y []] :=
    augPop_derives hpop []
  exact h₁.trans (h₂.trans h₃)

/-- A route containing no binary event factors into a neutral prefix followed by a compressed
pop path for exactly the inherited occurrences down through its target. -/
public theorem consumeRoute_factor_noBinary
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    {p : NFParse g A stack w} {k : ℕ}
    (route : NFParse.ConsumeRoute g p k) (hroute : route.NoBinary) :
    ∃ X Y, Neutral g A X ∧ PopPath g X (stack.take (k + 1)) Y := by
  induction route with
  | @binaryLeft A B C stack u v r hr hlhs hc hrhs left right k route ih =>
      exact False.elim hroute
  | @binaryRight A B C stack u v r hr hlhs hc hrhs left right k route ih =>
      exact False.elim hroute
  | @popHere A B f stack w r hr hlhs hc hrhs rest =>
      refine ⟨A, B, Neutral.refl g A, ?_⟩
      simpa using
        (PopPath.one (popRule_aug ⟨r, hr, hlhs, hc, hrhs⟩))
  | @popTail A B f stack w r hr hlhs hc hrhs rest k route ih =>
      rcases ih hroute with ⟨X, Y, hneutral, path⟩
      have hedge : AugPop g f A X :=
        ⟨A, B, Neutral.refl g A, ⟨r, hr, hlhs, hc, hrhs⟩, hneutral⟩
      refine ⟨A, Y, Neutral.refl g A, ?_⟩
      simpa [Nat.add_assoc] using (PopPath.cons hedge path)
  | @push A B f stack w r hr hlhs hc hrhs rest k route ih =>
      have hused : (NFParse.push hr hlhs hc hrhs rest).ConsumesAt k :=
        route.toConsumesAt
      have hk : k < stack.length :=
        (NFParse.push hr hlhs hc hrhs rest).consumesAt_lt_stack_length hused
      cases stack with
      | nil => simp at hk
      | cons f' stack =>
          rcases ih hroute with ⟨X, Y, hneutral, path⟩
          have path' : PopPath g X (f :: f' :: stack.take k) Y := by
            simpa [Nat.add_assoc] using path
          rcases path'.uncons with ⟨Z, hpop, restPath⟩
          have hcancel : Neutral g A Z :=
            neutral_of_push_neutral_pop
              ⟨r, hr, hlhs, hc, hrhs⟩ hneutral hpop
          exact ⟨Z, Y, hcancel, by simpa using restPath⟩

/-- Strengthened binary-free factorization retaining the residual concrete parse.  The resulting
compressed path starts at the current nonterminal (the neutral prefix is absorbed into its first
pre-saturated pop edge), and the residual parse is strictly smaller. -/
public theorem consumeRoute_popContinuation_noBinary
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    {p : NFParse g A stack w} {k : ℕ}
    (route : NFParse.ConsumeRoute g p k) (hroute : route.NoBinary) :
    ∃ Y suffix, ∃ rest : NFParse g Y suffix w,
      suffix = stack.drop (k + 1) ∧
      PopPath g A (stack.take (k + 1)) Y ∧ rest.nodeCount < p.nodeCount := by
  induction route with
  | @binaryLeft A B C stack u v r hr hlhs hc hrhs left right k route ih =>
      exact False.elim hroute
  | @binaryRight A B C stack u v r hr hlhs hc hrhs left right k route ih =>
      exact False.elim hroute
  | @popHere A B f stack w r hr hlhs hc hrhs rest =>
      refine ⟨B, stack, rest, by simp, ?_, ?_⟩
      · simpa using (PopPath.one (popRule_aug ⟨r, hr, hlhs, hc, hrhs⟩))
      · simp [NFParse.nodeCount]
  | @popTail A B f stack w r hr hlhs hc hrhs rest k route ih =>
      rcases ih hroute with ⟨Y, suffix, residual, hsuffix, path, hcount⟩
      refine ⟨Y, suffix, residual, ?_, ?_, ?_⟩
      · simpa [Nat.add_assoc] using hsuffix
      · simpa [Nat.add_assoc] using
          (PopPath.cons (popRule_aug ⟨r, hr, hlhs, hc, hrhs⟩) path)
      · simp only [NFParse.nodeCount]
        omega
  | @push A B f stack w r hr hlhs hc hrhs rest k route ih =>
      have hused : (NFParse.push hr hlhs hc hrhs rest).ConsumesAt k :=
        route.toConsumesAt
      have hk : k < stack.length :=
        (NFParse.push hr hlhs hc hrhs rest).consumesAt_lt_stack_length hused
      cases stack with
      | nil => simp at hk
      | cons f' stack =>
          rcases ih hroute with ⟨Y, suffix, residual, hsuffix, path, hcount⟩
          have path' : PopPath g B (f :: f' :: stack.take k) Y := by
            simpa [Nat.add_assoc] using path
          rcases path'.uncons with ⟨Z, hpop, restPath⟩
          have hcancel : Neutral g A Z :=
            neutral_of_push_neutral_pop
              ⟨r, hr, hlhs, hc, hrhs⟩ (Neutral.refl g B) hpop
          refine ⟨Y, suffix, residual, ?_, ?_, ?_⟩
          · simpa [Nat.add_assoc] using hsuffix
          · simpa using restPath.preNeutral hcancel
          · simp only [NFParse.nodeCount]
            omega

/-- Therefore a binary-free route always yields a nonempty canonical compressed relation for
the followed inherited prefix. -/
public theorem compressedFlags_nonempty_of_consumeRoute_noBinary
    {g : IndexedGrammar T} [Fintype g.nt]
    {A : g.nt} {f : g.flag} {stack : List g.flag} {w : List T}
    {p : NFParse g A (f :: stack) w} {k : ℕ}
    (route : NFParse.ConsumeRoute g p k) (hroute : route.NoBinary) :
    ∃ f₀ flags,
      (f :: stack).take (k + 1) = f₀ :: flags ∧
        (compressedFlags g f₀ flags).Nonempty := by
  rcases consumeRoute_factor_noBinary route hroute with ⟨X, Y, _hneutral, path⟩
  exact path.compressedFlags_nonempty

/-! ### Parse continuations after a compressed pop -/

/-- `PopContinuation p R` is the exact semantic witness needed to consume the compressed block
`R`: an edge of `R` reaches a nonterminal which still has a concrete parse of the same terminal
yield over the unrepresented suffix.  The scheduler may follow this witness even when it differs
from the unary choices made inside `p`; indexed-grammar nondeterminism only requires one accepting
continuation. -/
public structure PopContinuation {g : IndexedGrammar T} [Fintype g.nt]
    {A : g.nt} (flags suffix : List g.flag) {w : List T}
    (p : NFParse g A (flags ++ suffix) w) (R : CFlag g) where
  next : g.nt
  rest : NFParse g next suffix w
  edge : R A next = true

/-- A binary-free route to the last occurrence of a visible block produces an immediate viable
continuation for that whole block.  Its residual parse is strictly smaller. -/
public theorem exists_popContinuation_of_noBinary_route
    {g : IndexedGrammar T} [Fintype g.nt] {A : g.nt}
    {f : g.flag} {flags suffix : List g.flag} {w : List T}
    (parse : NFParse g A ((f :: flags) ++ suffix) w)
    (route : NFParse.ConsumeRoute g parse flags.length) (hroute : route.NoBinary) :
    ∃ continuation : PopContinuation (f :: flags) suffix parse
        (compressedFlags g f flags),
      continuation.rest.nodeCount < parse.nodeCount := by
  rcases consumeRoute_popContinuation_noBinary route hroute with
    ⟨Y, suffix', residual, hsuffix, path, hcount⟩
  have hdrop : ((f :: flags) ++ suffix).drop (flags.length + 1) = suffix := by
    simp
  have hstack : suffix' = suffix := hsuffix.trans hdrop
  let residual' : NFParse g Y suffix w := hstack ▸ residual
  have hresidualCount : residual'.nodeCount = residual.nodeCount :=
    NFParse.nodeCount_cast_stack residual hstack
  have path' : PopPath g A (f :: flags) Y := by
    simpa using path
  rcases path'.compressedFlags_edge with ⟨f', flags', hflags, hedge⟩
  simp only [List.cons.injEq] at hflags
  rcases hflags with ⟨rfl, rfl⟩
  refine ⟨⟨Y, residual', hedge⟩, ?_⟩
  change residual'.nodeCount < parse.nodeCount
  rw [hresidualCount]
  exact hcount

/-- A concrete top-pop parse constructor gives an immediate continuation for the base compressed
flag. -/
public def PopContinuation.ofPop
    {g : IndexedGrammar T} [Fintype g.nt] {A B : g.nt} {f : g.flag}
    {suffix : List g.flag} {w : List T} {r : IRule T g.nt g.flag}
    (hr : r ∈ g.rules) (hlhs : r.lhs = A) (hc : r.consume = some f)
    (hrhs : r.rhs = [IRhsSymbol.nonterminal B none])
    (rest : NFParse g B suffix w) :
    PopContinuation [f] suffix (NFParse.pop hr hlhs hc hrhs rest)
      (cflagBase g f) where
  next := B
  rest := rest
  edge := by
    rw [cflagBase_apply]
    exact popRule_aug ⟨r, hr, hlhs, hc, hrhs⟩

/-- A canonical `PopPath` followed by a parse of the residual stack gives a compressed-pop
continuation. -/
public def PopContinuation.ofPopPath
    {g : IndexedGrammar T} [Fintype g.nt] {A B : g.nt}
    {f : g.flag} {flags suffix : List g.flag} {w : List T}
    (parse : NFParse g A ((f :: flags) ++ suffix) w)
    (path : PopPath g A (f :: flags) B) (rest : NFParse g B suffix w) :
    PopContinuation (f :: flags) suffix
      parse (compressedFlags g f flags) where
  next := B
  rest := rest
  edge := by
    rcases path.compressedFlags_edge with ⟨f', flags', hflags, hedge⟩
    simp only [List.cons.injEq] at hflags
    rcases hflags with ⟨rfl, rfl⟩
    exact hedge

namespace PopContinuation

/-- A viable compressed continuation witnesses the nonemptiness side condition used when a
new flag is compressed into that block. -/
public theorem relation_nonempty {g : IndexedGrammar T} [Fintype g.nt]
    {A : g.nt} {flags suffix : List g.flag} {w : List T}
    {parse : NFParse g A (flags ++ suffix) w} {R : CFlag g}
    (continuation : PopContinuation flags suffix parse R) : R.Nonempty :=
  ⟨A, continuation.next, continuation.edge⟩

/-- Execute a viable compressed continuation and enter a plain residual task. -/
public theorem composite_popPlain {g : IndexedGrammar T} [Fintype g.nt]
    (input : List T) {A : g.nt} {flags suffix : List g.flag} {w : List T}
    {parse : NFParse g A (flags ++ suffix) w} {R : CFlag g}
    (continuation : PopContinuation flags suffix parse R) (d : IndexMark)
    (inputPos : ℕ) (alpha beta gamma : List (WorkSym g))
    (hfree : IndexFree beta) :
    CompositeStep g input
      ⟨inputPos, ⟨alpha ++ [.dollar], .live A,
        beta ++ .index R d :: gamma⟩⟩
  ⟨inputPos, ⟨alpha ++ [.dollar] ++ beta ++ [.index R d.markUsed, .dollar],
        .plain continuation.next, .close :: gamma⟩⟩ :=
  ⟨.popPlain R d A continuation.next, continuation.edge,
    Or.inl ⟨alpha, beta, gamma, hfree, rfl, rfl⟩⟩

/-- Execute a viable compressed continuation and enter a live residual task. -/
public theorem composite_popLive {g : IndexedGrammar T} [Fintype g.nt]
    (input : List T) {A : g.nt} {flags suffix : List g.flag} {w : List T}
    {parse : NFParse g A (flags ++ suffix) w} {R : CFlag g}
    (continuation : PopContinuation flags suffix parse R) (d : IndexMark)
    (hlater : d.later = true) (inputPos : ℕ)
    (alpha beta gamma : List (WorkSym g)) (hfree : IndexFree beta) :
    CompositeStep g input
      ⟨inputPos, ⟨alpha ++ [.dollar], .live A,
        beta ++ .index R d :: gamma⟩⟩
  ⟨inputPos, ⟨alpha ++ [.dollar] ++ beta ++ [.index R d.markUsed, .dollar],
        .live continuation.next, .close :: gamma⟩⟩ :=
  ⟨.popLive R d A continuation.next, continuation.edge, hlater,
    Or.inl ⟨alpha, beta, gamma, hfree, rfl, rfl⟩⟩

end PopContinuation

/-- The binary constructor of an `NFParse` supplies the corresponding augmented binary edge. -/
public theorem augBinary_of_nfparse_binary
    {g : IndexedGrammar T} {A B C : g.nt} {stack : List g.flag} {u v : List T}
    {r : IRule T g.nt g.flag}
    (hr : r ∈ g.rules) (hlhs : r.lhs = A) (hc : r.consume = none)
    (hrhs : r.rhs =
      [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none])
    (_left : NFParse g B stack u) (_right : NFParse g C stack v) :
    AugBinary g A B C :=
  binaryRule_aug ⟨r, hr, hlhs, hc, hrhs⟩

/-- The push constructor of an `NFParse` supplies the corresponding augmented push edge. -/
public theorem augPush_of_nfparse_push
    {g : IndexedGrammar T} {A B : g.nt} {f : g.flag}
    {stack : List g.flag} {w : List T} {r : IRule T g.nt g.flag}
    (hr : r ∈ g.rules) (hlhs : r.lhs = A) (hc : r.consume = none)
    (hrhs : r.rhs = [IRhsSymbol.nonterminal B (some f)])
    (_rest : NFParse g B (f :: stack) w) :
    AugPush g A B f :=
  pushRule_aug ⟨r, hr, hlhs, hc, hrhs⟩

/-- The terminal constructor of an `NFParse` supplies the corresponding augmented terminal
edge. -/
public theorem augTerminal_of_nfparse_terminal
    {g : IndexedGrammar T} {A : g.nt} {a : T}
    {r : IRule T g.nt g.flag}
    (hr : r ∈ g.rules) (hlhs : r.lhs = A) (hc : r.consume = none)
    (hrhs : r.rhs = [IRhsSymbol.terminal a]) :
    AugTerminal g A a :=
  terminalRule_aug ⟨r, hr, hlhs, hc, hrhs⟩

/-- A concrete top-pop rule is an edge of the base compressed flag used by the machine. -/
public theorem cflagBase_edge_of_nfparse_pop
    {g : IndexedGrammar T} {A B : g.nt} {f : g.flag}
    {stack : List g.flag} {w : List T} {r : IRule T g.nt g.flag}
    (hr : r ∈ g.rules) (hlhs : r.lhs = A) (hc : r.consume = some f)
    (hrhs : r.rhs = [IRhsSymbol.nonterminal B none])
    (_rest : NFParse g B stack w) :
    cflagBase g f A B = true := by
  rw [cflagBase_apply]
  exact popRule_aug ⟨r, hr, hlhs, hc, hrhs⟩


end Aho
end IndexedGrammar

