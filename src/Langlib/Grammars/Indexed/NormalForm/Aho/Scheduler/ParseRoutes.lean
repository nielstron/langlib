module

public import Langlib.Grammars.Indexed.NormalForm.Aho.ParseCertificate
public import Langlib.Grammars.Indexed.NormalForm.Aho.Scheduler.Accounting

@[expose]
public section

/-!
# Parse routes for Aho scheduling

Structural parse measures and canonical routes to consumed stack occurrences.
-/

variable {T : Type}

namespace IndexedGrammar
namespace NFParse

/-- Number of constructors in a concrete parse.  The direct scheduler decreases the sum of
these counts on every grammar-facing composite step. -/
public def nodeCount {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T} :
    NFParse g A stack w → ℕ
  | .binary _ _ _ _ left right => left.nodeCount + right.nodeCount + 1
  | .pop _ _ _ _ rest => rest.nodeCount + 1
  | .push _ _ _ _ rest => rest.nodeCount + 1
  | .terminal _ _ _ _ => 1

@[simp] public theorem nodeCount_pos
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    (p : NFParse g A stack w) : 0 < p.nodeCount := by
  cases p <;> simp [nodeCount]

/-- Transporting only the stack index of a parse does not change its constructor count. -/
public theorem nodeCount_cast_stack
    {g : IndexedGrammar T} {A : g.nt} {stack stack' : List g.flag} {w : List T}
    (p : NFParse g A stack w) (h : stack = stack') :
    (h ▸ p).nodeCount = p.nodeCount := by
  subst stack'
  rfl

/-- If a concrete parse consumes stack occurrence `k + 1`, it also consumes occurrence `k`.
Operationally, a derivation cannot reach a deeper stack occurrence without first popping the
one immediately above it. -/
public theorem consumesAt_of_consumesAt_succ
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    (p : NFParse g A stack w) (k : ℕ) :
    p.ConsumesAt (k + 1) → p.ConsumesAt k := by
  induction p generalizing k with
  | binary _ _ _ _ left right ihleft ihright =>
      intro h
      rcases h with h | h
      · exact Or.inl (ihleft k h)
      · exact Or.inr (ihright k h)
  | pop _ _ _ _ rest ih =>
      intro h
      cases k with
      | zero => exact Or.inl rfl
      | succ k =>
          exact Or.inr (ih k (by simpa [ConsumesAt] using h))
  | push _ _ _ _ rest ih =>
      intro h
      exact ih (k + 1) h
  | terminal _ _ _ _ =>
      simp [ConsumesAt]

/-- Consumption is downward closed in the stack-position order. -/
public theorem consumesAt_mono
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    (p : NFParse g A stack w) {i j : ℕ} (hij : i ≤ j)
    (hj : p.ConsumesAt j) : p.ConsumesAt i := by
  induction hij with
  | refl => exact hj
  | @step j hij ih =>
      exact ih (p.consumesAt_of_consumesAt_succ j hj)

/-- If the top inherited occurrence is unused, every deeper inherited occurrence is unused too.
This is the branch in which the scheduler may safely erase the inherited stack and run a plain
task. -/
public theorem not_consumesAt_of_not_consumesAt_zero
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    (p : NFParse g A stack w) (hzero : ¬ p.ConsumesAt 0) (k : ℕ) :
    ¬ p.ConsumesAt k := by
  intro hk
  exact hzero (p.consumesAt_mono (Nat.zero_le k) hk)

/-- A parse can only consume an occurrence which is actually present in its inherited stack. -/
public theorem consumesAt_lt_stack_length
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    (p : NFParse g A stack w) {k : ℕ} (hk : p.ConsumesAt k) :
    k < stack.length := by
  induction p generalizing k with
  | binary _ _ _ _ left right ihleft ihright =>
      rcases hk with hk | hk
      · exact ihleft hk
      · exact ihright hk
  | pop _ _ _ _ rest ih =>
      rcases hk with rfl | hk
      · simp
      · cases k with
        | zero => simp
        | succ k =>
            have := ih (by simpa [ConsumesAt] using hk)
            simp only [List.length_cons]
            omega
  | push _ _ _ _ rest ih =>
      have := ih hk
      simp only [List.length_cons] at this
      omega
  | terminal _ _ _ _ =>
      exact False.elim hk

/-- In particular, a task with empty inherited stack is necessarily plain. -/
public theorem not_consumesAt_of_stack_nil
    {g : IndexedGrammar T} {A : g.nt} {w : List T}
    (p : NFParse g A [] w) (k : ℕ) : ¬ p.ConsumesAt k := by
  intro hk
  have := p.consumesAt_lt_stack_length hk
  simp at this

/-! ## Chosen routes to consumed stack occurrences -/

/-- A data-carrying choice of one branch leading to the pop which consumes stack occurrence `k`.
Every binary node crossed by such a route contributes a nonempty off-path yield interval; those
intervals are the owners of uncompressed index blocks. -/
public inductive ConsumeRoute (g : IndexedGrammar T) :
    {A : g.nt} → {stack : List g.flag} → {w : List T} →
      NFParse g A stack w → ℕ → Type where
  | binaryLeft {A B C : g.nt} {stack : List g.flag} {u v : List T}
      {r : IRule T g.nt g.flag}
      {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = none}
      {hrhs : r.rhs =
        [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none]}
      {left : NFParse g B stack u} {right : NFParse g C stack v} {k : ℕ}
      (route : ConsumeRoute g left k) :
      ConsumeRoute g (NFParse.binary hr hlhs hc hrhs left right) k
  | binaryRight {A B C : g.nt} {stack : List g.flag} {u v : List T}
      {r : IRule T g.nt g.flag}
      {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = none}
      {hrhs : r.rhs =
        [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none]}
      {left : NFParse g B stack u} {right : NFParse g C stack v} {k : ℕ}
      (route : ConsumeRoute g right k) :
      ConsumeRoute g (NFParse.binary hr hlhs hc hrhs left right) k
  | popHere {A B : g.nt} {f : g.flag} {stack : List g.flag} {w : List T}
      {r : IRule T g.nt g.flag}
      {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = some f}
      {hrhs : r.rhs = [IRhsSymbol.nonterminal B none]}
      {rest : NFParse g B stack w} :
      ConsumeRoute g (NFParse.pop hr hlhs hc hrhs rest) 0
  | popTail {A B : g.nt} {f : g.flag} {stack : List g.flag} {w : List T}
      {r : IRule T g.nt g.flag}
      {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = some f}
      {hrhs : r.rhs = [IRhsSymbol.nonterminal B none]}
      {rest : NFParse g B stack w} {k : ℕ}
      (route : ConsumeRoute g rest k) :
      ConsumeRoute g (NFParse.pop hr hlhs hc hrhs rest) (k + 1)
  | push {A B : g.nt} {f : g.flag} {stack : List g.flag} {w : List T}
      {r : IRule T g.nt g.flag}
      {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = none}
      {hrhs : r.rhs = [IRhsSymbol.nonterminal B (some f)]}
      {rest : NFParse g B (f :: stack) w} {k : ℕ}
      (route : ConsumeRoute g rest (k + 1)) :
      ConsumeRoute g (NFParse.push hr hlhs hc hrhs rest) k

namespace ConsumeRoute

/-- Forget the chosen route and recover the proposition-valued consumption fact. -/
public def toConsumesAt
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    {p : NFParse g A stack w} {k : ℕ} : ConsumeRoute g p k → p.ConsumesAt k
  | .binaryLeft route => Or.inl route.toConsumesAt
  | .binaryRight route => Or.inr route.toConsumesAt
  | .popHere => Or.inl rfl
  | .popTail route => by simpa [NFParse.ConsumesAt] using route.toConsumesAt
  | .push route => route.toConsumesAt

/-- Every proposition-valued consumption fact admits a concrete route. -/
public theorem nonempty_of_consumesAt
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    (p : NFParse g A stack w) (k : ℕ) (used : p.ConsumesAt k) :
    Nonempty (ConsumeRoute g p k) := by
  induction p generalizing k with
  | binary _ _ _ _ left right ihleft ihright =>
      rcases used with used | used
      · rcases ihleft k used with ⟨route⟩
        exact ⟨.binaryLeft route⟩
      · rcases ihright k used with ⟨route⟩
        exact ⟨.binaryRight route⟩
  | pop _ _ _ _ rest ih =>
      cases k with
      | zero => exact ⟨.popHere⟩
      | succ k =>
          have hrest : rest.ConsumesAt k := by
            simpa [NFParse.ConsumesAt] using used
          rcases ih k hrest with ⟨route⟩
          exact ⟨.popTail route⟩
  | push _ _ _ _ rest ih =>
      rcases ih (k + 1) used with ⟨route⟩
      exact ⟨.push route⟩
  | terminal _ _ _ _ =>
      exact False.elim used

/-- Consumption and existence of a chosen route are equivalent. -/
public theorem nonempty_iff_consumesAt
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    (p : NFParse g A stack w) (k : ℕ) :
    Nonempty (ConsumeRoute g p k) ↔ p.ConsumesAt k := by
  constructor
  · rintro ⟨route⟩
    exact route.toConsumesAt
  · exact nonempty_of_consumesAt p k

/-- Choose a route from a known consumption fact. -/
public noncomputable def ofConsumesAt
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    (p : NFParse g A stack w) (k : ℕ) (used : p.ConsumesAt k) :
  ConsumeRoute g p k :=
  Classical.choice (nonempty_of_consumesAt p k used)

/-! ### Disjoint terminal owners along a consumption route -/

/-- Embed a position in a left child yield into the concatenated parent yield. -/
public def embedLeft {α : Type} (u v : List α) : Fin u.length → Fin (u ++ v).length :=
  fun i => ⟨i.1, by simp only [List.length_append]; omega⟩

/-- Embed a position in a right child yield into the concatenated parent yield. -/
public def embedRight {α : Type} (u v : List α) : Fin v.length → Fin (u ++ v).length :=
  fun i => ⟨u.length + i.1, by simp only [List.length_append]; omega⟩

public theorem embedLeft_injective {α : Type} (u v : List α) :
    Function.Injective (embedLeft u v) := by
  intro i j hij
  apply Fin.ext
  have hval := congrArg Fin.val hij
  simpa [embedLeft] using hval

public theorem embedRight_injective {α : Type} (u v : List α) :
    Function.Injective (embedRight u v) := by
  intro i j hij
  apply Fin.ext
  have hval := congrArg Fin.val hij
  simp only [embedRight] at hval
  omega

/-- At a binary event, charge the fresh block to the first terminal position of the child not
followed by the consumption route.  Recursively chosen barriers lie inside the followed child,
so all of these owners are distinct. -/
public def barrierOwners
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    {p : NFParse g A stack w} {k : ℕ} :
    ConsumeRoute g p k → List (Fin w.length)
  | .binaryLeft (u := u) (v := v) (right := right) route =>
      ⟨u.length, by
        have hv := right.yield_length_pos
        simp only [List.length_append]
        omega⟩ :: route.barrierOwners.map (embedLeft u v)
  | .binaryRight (u := u) (v := v) (left := left) route =>
      ⟨0, by
        have hu := left.yield_length_pos
        simp only [List.length_append]
        omega⟩ :: route.barrierOwners.map (embedRight u v)
  | .popHere => []
  | .popTail route => route.barrierOwners
  | .push route => route.barrierOwners

/-- Off-path owners selected at distinct binary events on one route are pairwise distinct. -/
public theorem barrierOwners_nodup
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    {p : NFParse g A stack w} {k : ℕ} (route : ConsumeRoute g p k) :
    route.barrierOwners.Nodup := by
  induction route with
  | @binaryLeft A B C stack u v r hr hlhs hc hrhs left right k route ih =>
      rw [barrierOwners, List.nodup_cons]
      constructor
      · intro hmem
        rcases List.mem_map.mp hmem with ⟨i, _hi, heq⟩
        have hval := congrArg Fin.val heq
        simp only [embedLeft] at hval
        exact (Nat.ne_of_lt i.isLt) hval
      · exact ih.map (embedLeft_injective u v)
  | @binaryRight A B C stack u v r hr hlhs hc hrhs left right k route ih =>
      rw [barrierOwners, List.nodup_cons]
      constructor
      · intro hmem
        rcases List.mem_map.mp hmem with ⟨i, _hi, heq⟩
        have hval := congrArg Fin.val heq
        have hu := left.yield_length_pos
        simp only [embedRight] at hval
        omega
      · exact ih.map (embedRight_injective u v)
  | popHere => simp [barrierOwners]
  | popTail route ih => simpa [barrierOwners] using ih
  | push route ih => simpa [barrierOwners] using ih

/-- Consequently the number of productive barriers on any one consumption route is bounded by
the terminal yield length. -/
public theorem barrierOwners_length_le
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    {p : NFParse g A stack w} {k : ℕ} (route : ConsumeRoute g p k) :
    route.barrierOwners.length ≤ w.length := by
  simpa using route.barrierOwners_nodup.length_le_card

/-- A route has no productive barrier exactly when it reaches its pop using only unary
push/pop constructors. -/
public def NoBinary
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    {p : NFParse g A stack w} {k : ℕ} : ConsumeRoute g p k → Prop
  | .binaryLeft _ | .binaryRight _ => False
  | .popHere => True
  | .popTail route => route.NoBinary
  | .push route => route.NoBinary

@[simp] public theorem noBinary_iff_barrierOwners_nil
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    {p : NFParse g A stack w} {k : ℕ} (route : ConsumeRoute g p k) :
    route.NoBinary ↔ route.barrierOwners = [] := by
  induction route with
  | binaryLeft route ih => simp [NoBinary, barrierOwners]
  | binaryRight route ih => simp [NoBinary, barrierOwners]
  | popHere => simp [NoBinary, barrierOwners]
  | popTail route ih => simpa [NoBinary, barrierOwners] using ih
  | push route ih => simpa [NoBinary, barrierOwners] using ih

end ConsumeRoute

end NFParse

end IndexedGrammar
