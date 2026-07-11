module

public import Langlib.Grammars.Indexed.NormalForm.AhoCorrectness

@[expose]
public section

/-!
# Completeness of Aho's marked compressed-index machine

This file contains the parse-directed scheduler for the marked machine.  The first structural
fact used by the scheduler is that consumption of an inherited stack occurrence is prefix
closed: reaching a deeper occurrence necessarily consumes every occurrence above it.  This is
what makes the plain/live choice local and makes a live push introduce another relevant index.
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

namespace Aho

/-! ## Ghost annotations and the global scheduling invariant -/

/-- Whether a pending parse task must retain the compressed stack to its right.  A plain task
does not consume the top inherited occurrence; prefix closure then says it consumes no inherited
occurrence.  A live task does consume the top occurrence and must be scheduled against the next
compressed-index token. -/
public inductive TaskMode {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag}
    {w : List T} (p : NFParse g A stack w) where
  | plain (unused : ¬ p.ConsumesAt 0) : TaskMode p
  | live (used : p.ConsumesAt 0) : TaskMode p

/-- A pending parse task, together with the terminal position which owns its work-tape payload.
The scheduler uses the left endpoint of the task's nonempty yield interval as `owner`. -/
public structure ScheduleTask (g : IndexedGrammar T) (input : List T) where
  A : g.nt
  stack : List g.flag
  yield : List T
  parse : NFParse g A stack yield
  pre : List T
  post : List T
  input_eq : input = pre ++ yield ++ post
  mode : TaskMode parse

namespace ScheduleTask

/-- The first terminal position in a pending task's nonempty yield. -/
public def owner {g : IndexedGrammar T} {input : List T}
    (task : ScheduleTask g input) : Fin input.length := by
  refine ⟨task.pre.length, ?_⟩
  have hyield := task.parse.yield_length_pos
  have hlength := congrArg List.length task.input_eq
  simp only [List.length_append] at hlength
  omega

/-- Erase the ghost parse and retain the finite work symbol seen by the machine. -/
public def workSym {g : IndexedGrammar T} {input : List T}
    (task : ScheduleTask g input) : WorkSym g :=
  match task.mode with
  | .plain _ => .plain task.A
  | .live _ => .live task.A

end ScheduleTask

/-- A compressed-index occurrence with its concrete denotation and terminal-position owner.
Only the finite relation and mark survive ghost erasure. -/
public structure ScheduleIndex (g : IndexedGrammar T) [Fintype g.nt]
    (input : List T) where
  flags : List g.flag
  relation : CFlag g
  mark : IndexMark
  denotes : CFlag.Denotes g flags relation
  owner : Fin (10 * input.length)

/-- Ghost-annotated symbols used by the parse-directed scheduler. -/
public inductive ScheduleAtom (g : IndexedGrammar T) [Fintype g.nt]
    (input : List T) where
  | task : ScheduleTask g input → ScheduleAtom g input
  | terminal : Fin input.length → T → ScheduleAtom g input
  | index : ScheduleIndex g input → ScheduleAtom g input
  | dollar : ScheduleAtom g input
  | close : Fin (10 * input.length) → ScheduleAtom g input
  | hash : ScheduleAtom g input

namespace ScheduleAtom

/-- Erase all scheduler-only data. -/
public def workSym {g : IndexedGrammar T} [Fintype g.nt] {input : List T} :
    ScheduleAtom g input → WorkSym g
  | .task t => t.workSym
  | .terminal _ a => .terminal a
  | .index idx => .index idx.relation idx.mark
  | .dollar => .dollar
  | .close _ => .close
  | .hash => .hash

/-- Owners of task/terminal payloads. -/
public def taskOwner? {g : IndexedGrammar T} [Fintype g.nt] {input : List T} :
    ScheduleAtom g input → Option (Fin input.length)
  | .task t => some t.owner
  | .terminal owner _ => some owner
  | _ => none

/-- Owners of compressed-index payloads. -/
public def indexOwner? {g : IndexedGrammar T} [Fintype g.nt] {input : List T} :
    ScheduleAtom g input → Option (Fin (10 * input.length))
  | .index idx => some idx.owner
  | _ => none

/-- The selected persistent-index owner charged by an open frame. -/
public def closeOwner? {g : IndexedGrammar T} [Fintype g.nt] {input : List T} :
    ScheduleAtom g input → Option (Fin (10 * input.length))
  | .close owner => some owner
  | _ => none

end ScheduleAtom

/-- A zipper over the ghost-annotated scheduler word. -/
public structure ScheduleCursor (g : IndexedGrammar T) [Fintype g.nt]
    (input : List T) where
  left : List (ScheduleAtom g input)
  focus : ScheduleAtom g input
  right : List (ScheduleAtom g input)

namespace ScheduleCursor

/-- The complete ghost word. -/
public def word {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (cursor : ScheduleCursor g input) : List (ScheduleAtom g input) :=
  cursor.left ++ cursor.focus :: cursor.right

/-- Erase a ghost cursor to the finite machine cursor. -/
public def erase {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (cursor : ScheduleCursor g input) : WorkCursor g :=
  { left := cursor.left.map ScheduleAtom.workSym
    focus := cursor.focus.workSym
    right := cursor.right.map ScheduleAtom.workSym }

@[simp] public theorem erase_word {g : IndexedGrammar T} [Fintype g.nt]
    {input : List T} (cursor : ScheduleCursor g input) :
    cursor.erase.word = cursor.word.map ScheduleAtom.workSym := by
  simp [erase, word, WorkCursor.word]

@[simp] public theorem erase_word_length {g : IndexedGrammar T} [Fintype g.nt]
    {input : List T} (cursor : ScheduleCursor g input) :
    cursor.erase.word.length = cursor.word.length := by
  simp

/-- Task/terminal owners present in the cursor. -/
public def taskOwners {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (cursor : ScheduleCursor g input) : List (Fin input.length) :=
  cursor.word.filterMap ScheduleAtom.taskOwner?

/-- Compressed-index owners present in the cursor. -/
public def indexOwners {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (cursor : ScheduleCursor g input) : List (Fin (10 * input.length)) :=
  cursor.word.filterMap ScheduleAtom.indexOwner?

/-- Persistent-index owners currently charged by open `$`/`close` frames. -/
public def frameOwners {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (cursor : ScheduleCursor g input) : List (Fin (10 * input.length)) :=
  cursor.word.filterMap ScheduleAtom.closeOwner?

/-- Number of currently open `$`/`close` frames. -/
public def frameCount {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (cursor : ScheduleCursor g input) : ℕ :=
  cursor.frameOwners.length

end ScheduleCursor

/-- Global invariant maintained by the compressed scheduler. Tasks are charged to terminal
positions, while persistent physical blocks satisfy the `6|input|` reusable-owner cap.
`shape_bound` accounts for one task/index square per payload, two delimiters per open frame,
and the fixed outer `$`/`#` pair. -/
public structure ScheduleInvariant {g : IndexedGrammar T} [Fintype g.nt]
    {input : List T} (cursor : ScheduleCursor g input) : Prop where
  taskOwners_nodup : cursor.taskOwners.Nodup
  indexOwners_nodup : cursor.indexOwners.Nodup
  frameOwners_nodup : cursor.frameOwners.Nodup
  frameOwners_subset_indexOwners : cursor.frameOwners ⊆ cursor.indexOwners
  taskCount_le : cursor.taskOwners.length ≤ input.length
  indexCount_le : cursor.indexOwners.length ≤ 6 * input.length
  shape_bound :
    cursor.word.length ≤ cursor.taskOwners.length + cursor.indexOwners.length +
      2 * cursor.frameCount + 2

namespace ScheduleInvariant

/-- Construct the global invariant from its qualitative ownership facts, the explicit persistent
owner bound, and the delimiter-shape bound. Unlike task owners, persistent owners live in
an ambient carrier larger than their reusable bank, so their `6|input|` bound is supplied
explicitly. -/
public theorem of_owner_nodup
    {g : IndexedGrammar T} [Fintype g.nt]
    {input : List T} {cursor : ScheduleCursor g input}
    (htasks : cursor.taskOwners.Nodup)
    (hindices : cursor.indexOwners.Nodup)
    (hframes : cursor.frameOwners.Nodup)
    (hframeSubset : cursor.frameOwners ⊆ cursor.indexOwners)
    (hindexCount : cursor.indexOwners.length ≤ 6 * input.length)
    (hshape : cursor.word.length ≤ cursor.taskOwners.length +
      cursor.indexOwners.length + 2 * cursor.frameCount + 2) :
    ScheduleInvariant cursor where
  taskOwners_nodup := htasks
  indexOwners_nodup := hindices
  frameOwners_nodup := hframes
  frameOwners_subset_indexOwners := hframeSubset
  taskCount_le := by
    simpa using htasks.length_le_card
  indexCount_le := hindexCount
  shape_bound := hshape

/-- Distinct open frames inject into the persistent indices which own them. -/
public theorem frameCount_le_indexCount {g : IndexedGrammar T} [Fintype g.nt]
    {input : List T} {cursor : ScheduleCursor g input}
    (hinv : ScheduleInvariant cursor) :
    cursor.frameCount ≤ cursor.indexOwners.length := by
  exact (List.subperm_of_subset hinv.frameOwners_nodup
    hinv.frameOwners_subset_indexOwners).length_le

/-- The accounting invariant implies a uniform twenty-one-squares-per-input-symbol bound. -/
public theorem word_length_le_twenty_one_mul {g : IndexedGrammar T} [Fintype g.nt]
    {input : List T} {cursor : ScheduleCursor g input}
    (hinv : ScheduleInvariant cursor) (hinput : 0 < input.length) :
    cursor.word.length ≤ 21 * input.length := by
  have htask := hinv.taskCount_le
  have hindex := hinv.indexCount_le
  have hframes := hinv.frameCount_le_indexCount
  have hshape := hinv.shape_bound
  omega

/-- Erasing scheduler annotations preserves the bound needed by `BoundedReaches`. -/
public theorem erase_within {g : IndexedGrammar T} [Fintype g.nt]
    {input : List T} {cursor : ScheduleCursor g input}
    (hinv : ScheduleInvariant cursor) (hinput : 0 < input.length)
    (inputPos : ℕ) :
    (Config.mk inputPos cursor.erase).Within (21 * input.length) := by
  change cursor.erase.word.length ≤ 21 * input.length
  rw [cursor.erase_word_length]
  exact hinv.word_length_le_twenty_one_mul hinput

/-- The two fixed boundary cells also cover the vacuous zero-length ambient carrier. -/
public theorem erase_within_max_two {g : IndexedGrammar T} [Fintype g.nt]
    {input : List T} {cursor : ScheduleCursor g input}
    (hinv : ScheduleInvariant cursor) (inputPos : ℕ) :
    (Config.mk inputPos cursor.erase).Within (max 2 (21 * input.length)) := by
  change cursor.erase.word.length ≤ max 2 (21 * input.length)
  rw [cursor.erase_word_length]
  have htask := hinv.taskCount_le
  have hindex := hinv.indexCount_le
  have hframes := hinv.frameCount_le_indexCount
  have hshape := hinv.shape_bound
  by_cases hinput : 0 < input.length
  · have hmax : max 2 (21 * input.length) = 21 * input.length := by
      omega
    rw [hmax]
    omega
  · have hzero : input.length = 0 := Nat.eq_zero_of_not_pos hinput
    simp only [hzero, Nat.mul_zero] at htask hindex
    simp only [hzero, Nat.mul_zero, max_eq_left (by omega)]
    omega

end ScheduleInvariant

/-! ## Invariant-carrying schedule witnesses -/

/-- A scheduler state consists of a ghost cursor, its input position, and the global ownership
invariant.  Erasing it gives an ordinary composite-machine configuration. -/
public structure ScheduleState (g : IndexedGrammar T) [Fintype g.nt]
    (input : List T) where
  inputPos : ℕ
  inputPos_le : inputPos ≤ input.length
  cursor : ScheduleCursor g input
  invariant : ScheduleInvariant cursor

namespace ScheduleState

/-- Forget all scheduler annotations. -/
public def config {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (state : ScheduleState g input) : Config g :=
  ⟨state.inputPos, state.cursor.erase⟩

/-- Every scheduler state is inside the target tape bound. -/
public theorem config_within {g : IndexedGrammar T} [Fintype g.nt]
    {input : List T} (state : ScheduleState g input) (hinput : 0 < input.length) :
    state.config.Within (21 * input.length) :=
  state.invariant.erase_within hinput state.inputPos

end ScheduleState

/-- A scheduler edge erases to one composite-machine edge.  Ownership data is carried by the
endpoint states, so a schedule is bounded by construction. -/
public def ScheduleStep (g : IndexedGrammar T) [Fintype g.nt] (input : List T)
    (state state' : ScheduleState g input) : Prop :=
  CompositeStep g input state.config state'.config

/-- An invariant-carrying finite schedule, recorded extensionally at the erased machine
configurations.  Ghost-owner relabellings therefore cost no executable step. -/
public def ScheduleReaches (g : IndexedGrammar T) [Fintype g.nt] (input : List T)
    (state state' : ScheduleState g input) : Prop :=
  BoundedReaches g input (max 2 (21 * input.length)) state.config state'.config

namespace ScheduleReaches

/-- The empty schedule at an invariant-carrying state. -/
public theorem refl {g : IndexedGrammar T} [Fintype g.nt]
    {input : List T} (state : ScheduleState g input) :
    ScheduleReaches g input state state :=
  BoundedReaches.refl
    (state.invariant.erase_within_max_two state.inputPos)

/-- Package one verified composite-machine edge between invariant-carrying scheduler states. -/
public theorem single {g : IndexedGrammar T} [Fintype g.nt]
    {input : List T} {state state' : ScheduleState g input}
    (step : CompositeStep g input state.config state'.config) :
    ScheduleReaches g input state state' :=
  BoundedReaches.single
    (state.invariant.erase_within_max_two state.inputPos)
    step
    (state'.invariant.erase_within_max_two state'.inputPos)

/-- Concatenate two invariant-carrying schedules at their common scheduler state. -/
public theorem trans {g : IndexedGrammar T} [Fintype g.nt]
    {input : List T} {state₁ state₂ state₃ : ScheduleState g input}
    (first : ScheduleReaches g input state₁ state₂)
    (second : ScheduleReaches g input state₂ state₃) :
    ScheduleReaches g input state₁ state₃ :=
  BoundedReaches.trans first second

/-- Change either endpoint's ghost annotations without changing its erased configuration. -/
public theorem congr_config {g : IndexedGrammar T} [Fintype g.nt]
    {input : List T} {state state' relabelled relabelled' : ScheduleState g input}
    (schedule : ScheduleReaches g input state state')
    (hstart : relabelled.config = state.config)
    (hend : relabelled'.config = state'.config) :
    ScheduleReaches g input relabelled relabelled' := by
  simpa [ScheduleReaches, hstart, hend] using schedule

/-- Erasing an invariant-carrying schedule produces `BoundedReaches` directly. -/
public theorem toBoundedReaches {g : IndexedGrammar T} [Fintype g.nt]
    {input : List T} {state state' : ScheduleState g input}
    (hinput : 0 < input.length) (schedule : ScheduleReaches g input state state') :
    BoundedReaches g input (21 * input.length) state.config state'.config := by
  have hmax : max 2 (21 * input.length) = 21 * input.length := by omega
  simpa [ScheduleReaches, hmax] using schedule

end ScheduleReaches

/-! ## Canonical endpoints -/

/-- The initial pending task is plain because its inherited stack is empty. -/
public def initialScheduleTask {g : IndexedGrammar T} [Fintype g.nt]
    {input : List T} (parse : NFParse g g.initial [] input) : ScheduleTask g input where
  A := g.initial
  stack := []
  yield := input
  parse := parse
  pre := []
  post := []
  input_eq := by simp
  mode := .plain (parse.not_consumesAt_of_stack_nil 0)

/-- Ghost cursor for Aho's initial `$ S #` configuration. -/
public def initialScheduleCursor {g : IndexedGrammar T} [Fintype g.nt]
    {input : List T} (parse : NFParse g g.initial [] input) : ScheduleCursor g input :=
  ⟨[.dollar], .task (initialScheduleTask parse), [.hash]⟩

/-- Ghost cursor for the final `$ #` configuration. -/
public def finalScheduleCursor (g : IndexedGrammar T) [Fintype g.nt]
    (input : List T) : ScheduleCursor g input :=
  ⟨[.dollar], .hash, []⟩

public theorem initialScheduleCursor_invariant {g : IndexedGrammar T} [Fintype g.nt]
    {input : List T} (parse : NFParse g g.initial [] input) :
    ScheduleInvariant (initialScheduleCursor parse) := by
  have hinput := parse.yield_length_pos
  constructor <;>
    simp [initialScheduleCursor, initialScheduleTask, ScheduleCursor.taskOwners,
      ScheduleCursor.indexOwners, ScheduleCursor.frameOwners, ScheduleCursor.frameCount,
      ScheduleCursor.word, ScheduleAtom.taskOwner?, ScheduleAtom.indexOwner?,
      ScheduleAtom.closeOwner?] <;>
    omega

public theorem finalScheduleCursor_invariant {g : IndexedGrammar T} [Fintype g.nt]
    (input : List T) : ScheduleInvariant (finalScheduleCursor g input) := by
  constructor <;>
    simp [finalScheduleCursor, ScheduleCursor.taskOwners, ScheduleCursor.indexOwners,
      ScheduleCursor.frameOwners, ScheduleCursor.frameCount, ScheduleCursor.word,
      ScheduleAtom.taskOwner?, ScheduleAtom.indexOwner?, ScheduleAtom.closeOwner?]

/-- Canonical invariant-carrying initial state. -/
public def initialScheduleState {g : IndexedGrammar T} [Fintype g.nt]
    {input : List T} (parse : NFParse g g.initial [] input) : ScheduleState g input where
  inputPos := 0
  inputPos_le := Nat.zero_le _
  cursor := initialScheduleCursor parse
  invariant := initialScheduleCursor_invariant parse

/-- Canonical invariant-carrying accepting state. -/
public def finalScheduleState (g : IndexedGrammar T) [Fintype g.nt]
    (input : List T) : ScheduleState g input where
  inputPos := input.length
  inputPos_le := le_rfl
  cursor := finalScheduleCursor g input
  invariant := finalScheduleCursor_invariant input

@[simp] public theorem initialScheduleState_config {g : IndexedGrammar T} [Fintype g.nt]
    {input : List T} (parse : NFParse g g.initial [] input) :
    (initialScheduleState parse).config = initialConfig g := by
  simp [initialScheduleState, ScheduleState.config, initialScheduleCursor,
    initialScheduleTask, ScheduleCursor.erase, ScheduleAtom.workSym,
    ScheduleTask.workSym, initialConfig]

@[simp] public theorem finalScheduleState_config {g : IndexedGrammar T} [Fintype g.nt]
    (input : List T) :
    (finalScheduleState g input).config = finalConfig g input.length := by
  simp [finalScheduleState, ScheduleState.config, finalScheduleCursor,
    ScheduleCursor.erase, ScheduleAtom.workSym, finalConfig]

/-- The exact remaining semantic obligation: construct an ownership-preserving schedule from a
concrete parse. -/
public def ParseScheduled {g : IndexedGrammar T} [Fintype g.nt]
    {input : List T} (parse : NFParse g g.initial [] input) : Prop :=
  ScheduleReaches g input (initialScheduleState parse) (finalScheduleState g input)

/-- Once the parse-directed schedule is constructed, its endpoint and ownership invariants give
full bounded completeness without any additional accounting argument. -/
public theorem complete_bounded_of_parseScheduled
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (parse : NFParse g g.initial [] input) (schedule : ParseScheduled parse) :
    BoundedReaches g input (21 * input.length)
      (initialConfig g) (finalConfig g input.length) := by
  have h := ScheduleReaches.toBoundedReaches parse.yield_length_pos schedule
  simpa using h

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

/-! ## Exact composite-move constructors -/

/-- Starting the first relevant stack block. -/
public theorem composite_plainPushUse_at
    {g : IndexedGrammar T} [Fintype g.nt] (input : List T)
    {A B : g.nt} {f : g.flag} (hpush : AugPush g A B f)
    (inputPos : ℕ) (alpha beta : List (WorkSym g)) :
    CompositeStep g input
      ⟨inputPos, ⟨alpha ++ [.dollar], .plain A, beta⟩⟩
      ⟨inputPos, ⟨alpha ++ [.dollar], .live B,
        .index (cflagBase g f) .firstPending :: beta⟩⟩ := by
  exact ⟨.plainPushUse A B f, hpush, alpha, beta, rfl, rfl⟩

/-- A live binary task whose two children both consume the represented stack. -/
public theorem composite_liveBinaryBoth_at
    {g : IndexedGrammar T} [Fintype g.nt] (input : List T)
    {A B C : g.nt} (hbinary : AugBinary g A B C)
    (inputPos : ℕ) (alpha : List (WorkSym g)) (Z : WorkSym g)
    (beta : List (WorkSym g)) :
    CompositeStep g input
      ⟨inputPos, ⟨alpha ++ [.dollar], .live A, Z :: beta⟩⟩
      ⟨inputPos, ⟨markProductivePrefix alpha ++ [.dollar], .live B,
        .live C :: Z :: beta⟩⟩ := by
  exact ⟨.liveBinaryBoth A B C, hbinary, alpha, Z, beta, rfl, rfl⟩

/-- A live binary task whose left child alone consumes the represented stack. -/
public theorem composite_liveBinaryLeft_at
    {g : IndexedGrammar T} [Fintype g.nt] (input : List T)
    {A B C : g.nt} (hbinary : AugBinary g A B C)
    (inputPos : ℕ) (alpha : List (WorkSym g)) (Z : WorkSym g)
    (beta : List (WorkSym g)) :
    CompositeStep g input
      ⟨inputPos, ⟨alpha ++ [.dollar], .live A, Z :: beta⟩⟩
      ⟨inputPos, ⟨markProductivePrefix alpha ++ [.dollar], .live B,
        .plain C :: Z :: beta⟩⟩ := by
  exact ⟨.liveBinaryLeft A B C, hbinary, alpha, Z, beta, rfl, rfl⟩

/-- A live binary task whose right child alone consumes the represented stack. -/
public theorem composite_liveBinaryRight_at
    {g : IndexedGrammar T} [Fintype g.nt] (input : List T)
    {A B C : g.nt} (hbinary : AugBinary g A B C)
    (inputPos : ℕ) (alpha : List (WorkSym g)) (Z : WorkSym g)
    (beta : List (WorkSym g)) :
    CompositeStep g input
      ⟨inputPos, ⟨alpha ++ [.dollar], .live A, Z :: beta⟩⟩
      ⟨inputPos, ⟨markProductivePrefix alpha ++ [.dollar], .plain B,
        .live C :: Z :: beta⟩⟩ := by
  exact ⟨.liveBinaryRight A B C, hbinary, alpha, Z, beta, rfl, rfl⟩

/-- Introduce a fresh relevant flag block above an already-live continuation. -/
public theorem composite_livePushFresh_at
    {g : IndexedGrammar T} [Fintype g.nt] (input : List T)
    {A B : g.nt} {f : g.flag} (hpush : AugPush g A B f)
    (inputPos : ℕ) (alpha : List (WorkSym g)) (Z : WorkSym g)
    (beta : List (WorkSym g)) :
    CompositeStep g input
      ⟨inputPos, ⟨alpha ++ [.dollar], .live A, Z :: beta⟩⟩
      ⟨inputPos, ⟨alpha ++ [.dollar], .live B,
        .index (cflagBase g f) .laterPending :: Z :: beta⟩⟩ := by
  exact ⟨.livePushFresh A B f, hpush, alpha, Z, beta, rfl, rfl⟩

/-- Compress a new pushed flag into the adjacent represented block. -/
public theorem composite_livePushCompress_at
    {g : IndexedGrammar T} [Fintype g.nt] (input : List T)
    {A B : g.nt} {f : g.flag} (R : CFlag g) (d : IndexMark)
    (hpush : AugPush g A B f)
    (hne : (cflagComp g (cflagBase g f) R).Nonempty)
    (inputPos : ℕ) (alpha beta : List (WorkSym g)) :
    CompositeStep g input
      ⟨inputPos, ⟨alpha ++ [.dollar], .live A, .index R d :: beta⟩⟩
      ⟨inputPos, ⟨alpha ++ [.dollar], .live B,
        .index (cflagComp g (cflagBase g f) R) d :: beta⟩⟩ := by
  exact ⟨.livePushCompress A B f R d, hpush, hne, alpha, beta, rfl, rfl⟩

/-- Consume a represented block and continue with a plain task in a fresh frame. -/
public theorem composite_popPlain_at
    {g : IndexedGrammar T} [Fintype g.nt] (input : List T)
    (R : CFlag g) (d : IndexMark) {A B : g.nt} (hedge : R A B = true)
    (inputPos : ℕ) (alpha beta gamma : List (WorkSym g))
    (hfree : IndexFree beta) :
    CompositeStep g input
      ⟨inputPos, ⟨alpha ++ [.dollar], .live A,
        beta ++ .index R d :: gamma⟩⟩
      ⟨inputPos, ⟨alpha ++ [.dollar] ++ beta ++ [.index R d.markUsed, .dollar],
        .plain B, .close :: gamma⟩⟩ := by
  exact ⟨.popPlain R d A B, hedge,
    Or.inl ⟨alpha, beta, gamma, hfree, rfl, rfl⟩⟩

/-- Consume a represented block and continue with a live task in a fresh frame. -/
public theorem composite_popLive_at
    {g : IndexedGrammar T} [Fintype g.nt] (input : List T)
    (R : CFlag g) (d : IndexMark) {A B : g.nt} (hedge : R A B = true)
    (hlater : d.later = true) (inputPos : ℕ)
    (alpha beta gamma : List (WorkSym g)) (hfree : IndexFree beta) :
    CompositeStep g input
      ⟨inputPos, ⟨alpha ++ [.dollar], .live A,
        beta ++ .index R d :: gamma⟩⟩
      ⟨inputPos, ⟨alpha ++ [.dollar] ++ beta ++ [.index R d.markUsed, .dollar],
        .live B, .close :: gamma⟩⟩ := by
  exact ⟨.popLive R d A B, hedge, hlater,
    Or.inl ⟨alpha, beta, gamma, hfree, rfl, rfl⟩⟩

/-- Consume an adjacent ephemeral block and discard its token before entering a plain
residual task.  The adjacency is what makes deletion ownership-safe: no pending sibling lies
between the active task and the selected block. -/
public theorem composite_popPlainErase_at
    {g : IndexedGrammar T} [Fintype g.nt] (input : List T)
    (R : CFlag g) (d : IndexMark) {A B : g.nt} (hedge : R A B = true)
    (inputPos : ℕ) (alpha gamma : List (WorkSym g)) :
    CompositeStep g input
      ⟨inputPos, ⟨alpha ++ [.dollar], .live A, .index R d :: gamma⟩⟩
      ⟨inputPos, ⟨alpha ++ [.dollar], .plain B, gamma⟩⟩ := by
  exact ⟨.popPlain R d A B, hedge, Or.inr ⟨alpha, gamma, rfl, rfl⟩⟩

/-- Adjacent ephemeral pop whose residual task still consumes a represented suffix. -/
public theorem composite_popLiveErase_at
    {g : IndexedGrammar T} [Fintype g.nt] (input : List T)
    (R : CFlag g) (d : IndexMark) {A B : g.nt} (hedge : R A B = true)
    (hlater : d.later = true) (inputPos : ℕ)
    (alpha gamma : List (WorkSym g)) :
    CompositeStep g input
      ⟨inputPos, ⟨alpha ++ [.dollar], .live A, .index R d :: gamma⟩⟩
      ⟨inputPos, ⟨alpha ++ [.dollar], .live B, gamma⟩⟩ := by
  exact ⟨.popLive R d A B, hedge, hlater,
    Or.inr ⟨alpha, gamma, rfl, rfl⟩⟩

/-- Remove an erasable represented block and expose its continuation. -/
public theorem composite_eraseIndex_at
    {g : IndexedGrammar T} [Fintype g.nt] (input : List T)
    (R : CFlag g) (d : IndexMark) (herase : d.erasable = true)
    (inputPos : ℕ) (alpha : List (WorkSym g)) (Z : WorkSym g)
    (beta : List (WorkSym g)) :
    CompositeStep g input
      ⟨inputPos, ⟨alpha ++ [.dollar], .index R d, Z :: beta⟩⟩
      ⟨inputPos, ⟨alpha ++ [.dollar], Z, beta⟩⟩ := by
  exact ⟨.eraseIndex R d, herase, alpha, Z, beta, rfl, rfl⟩

/-- Close a completed pop frame and reactivate its saved continuation. -/
public theorem composite_returnFrame_at
    {g : IndexedGrammar T} [Fintype g.nt] (input : List T)
    (inputPos : ℕ) (alpha : List (WorkSym g)) (Z : WorkSym g)
    (beta gamma : List (WorkSym g)) (hZ : Z ≠ WorkSym.dollar)
    (hfree : DollarFree beta) :
    CompositeStep g input
      ⟨inputPos, ⟨alpha ++ [.dollar, Z] ++ beta ++ [.dollar], .close, gamma⟩⟩
      ⟨inputPos, ⟨alpha ++ [.dollar], Z, beta ++ gamma⟩⟩ := by
  exact ⟨.returnFrame, alpha, Z, beta, gamma, hZ, hfree, rfl, rfl⟩

/-! ## Singleton visible-stack layouts

The first, unbounded, completeness runner uses one compressed token for every inherited flag
which is actually consumed.  Compression is only needed later for the linear accounting.  A
layout records the index-free (but possibly `close`-containing) gaps between those singleton
tokens.  The additional dollar-free fact is exactly what is needed when a completed pop frame
returns through such a gap. -/

public theorem IndexFree.append {g : IndexedGrammar T}
    {xs ys : List (WorkSym g)} (hxs : IndexFree xs) (hys : IndexFree ys) :
    IndexFree (xs ++ ys) := by
  intro R d hm
  simp only [List.mem_append] at hm
  exact hm.elim (hxs R d) (hys R d)

public theorem DollarFree.append {g : IndexedGrammar T}
    {xs ys : List (WorkSym g)} (hxs : DollarFree xs) (hys : DollarFree ys) :
    DollarFree (xs ++ ys) := by
  intro hm
  simp only [List.mem_append] at hm
  exact hm.elim hxs hys

public inductive SingletonLayout (g : IndexedGrammar T) [Fintype g.nt] :
    List g.flag → List (WorkSym g) → List (WorkSym g) → Prop where
  | nil (tail : List (WorkSym g)) : SingletonLayout g [] tail tail
  | cons {f : g.flag} {flags : List g.flag}
      {beta tail tail' : List (WorkSym g)} {d : IndexMark}
      (indexFree : IndexFree beta) (dollarFree : DollarFree beta)
      (later : flags ≠ [] → d.later = true)
      (rest : SingletonLayout g flags tail tail') :
      SingletonLayout g (f :: flags)
        (beta ++ WorkSym.index (cflagBase g f) d :: tail)
        (beta ++ WorkSym.index (cflagBase g f) d.markUsed :: tail')

namespace SingletonLayout

/-- Marking an already used index is idempotent. -/
@[simp] public theorem IndexMark.markUsed_idem (d : IndexMark) :
    d.markUsed.markUsed = d.markUsed := by
  cases d <;> rfl

@[simp] public theorem IndexMark.markUsed_later (d : IndexMark) :
    d.markUsed.later = d.later := by
  cases d <;> rfl

/-- Once all selected tokens have been used, selecting them again leaves the physical word
unchanged. -/
public theorem idempotent {g : IndexedGrammar T} [Fintype g.nt]
    {flags : List g.flag} {word used : List (WorkSym g)}
    (layout : SingletonLayout g flags word used) :
    SingletonLayout g flags used used := by
  induction layout with
  | nil tail => exact .nil tail
  | @cons f flags beta tail tail' d hindex hdollar hlater rest ih =>
      simpa using SingletonLayout.cons (f := f) (d := d.markUsed)
        hindex hdollar (fun hne => by
          simpa using hlater hne) ih

/-- Ordinary control symbols may be inserted before the first selected token.  In particular,
this is how a pending binary sibling or a crossed `close` is included in a pop gap. -/
public theorem prepend {g : IndexedGrammar T} [Fintype g.nt]
    {flags : List g.flag} {word used : List (WorkSym g)}
    (pref : List (WorkSym g)) (hindex : IndexFree pref)
    (hdollar : DollarFree pref) (layout : SingletonLayout g flags word used) :
    SingletonLayout g flags (pref ++ word) (pref ++ used) := by
  induction layout with
  | nil tail => exact .nil (pref ++ tail)
  | @cons f flags beta tail tail' d hbetaIndex hbetaDollar hlater rest _ih =>
      simpa [List.append_assoc] using SingletonLayout.cons (f := f) (d := d)
        (hindex.append hbetaIndex) (hdollar.append hbetaDollar) hlater rest

/-- Restrict a layout to its first `n` selected flags.  The remaining physical tokens become
part of the arbitrary unselected tail. -/
public theorem splitTake {g : IndexedGrammar T} [Fintype g.nt]
    {flags : List g.flag} {word used : List (WorkSym g)}
    (n : ℕ) (layout : SingletonLayout g flags word used) :
    ∃ middle,
      SingletonLayout g (flags.take n) word middle ∧
        SingletonLayout g flags middle used := by
  induction layout generalizing n with
  | nil tail => exact ⟨tail, by simpa using SingletonLayout.nil (g := g) tail,
      SingletonLayout.nil (g := g) tail⟩
  | @cons f flags beta tail tail' d hindex hdollar hlater rest ih =>
      cases n with
      | zero => exact ⟨_, .nil _, SingletonLayout.cons hindex hdollar hlater rest⟩
      | succ n =>
          rcases ih n with ⟨middle, hprefix, hremain⟩
          let next := beta ++ WorkSym.index (cflagBase g f) d.markUsed :: middle
          refine ⟨next, ?_, ?_⟩
          · exact SingletonLayout.cons (f := f) (d := d) hindex hdollar
              (fun hne => hlater (by
                intro hnil
                subst flags
                simp at hne)) hprefix
          · simpa [next] using SingletonLayout.cons (f := f)
              (d := d.markUsed) hindex hdollar
              (fun hne => by
                simpa using hlater hne) hremain

/-- Selecting the whole visible prefix reaches the all-used endpoint and leaves an idempotent
layout there. -/
public theorem splitAll {g : IndexedGrammar T} [Fintype g.nt]
    {flags : List g.flag} {word used : List (WorkSym g)}
    (layout : SingletonLayout g flags word used) :
    SingletonLayout g (flags.take flags.length) word used ∧
      SingletonLayout g flags used used := by
  simpa using And.intro layout layout.idempotent

/-- Any prefix of an all-used layout is itself an identity layout.  This is used when one binary
child has already consumed the whole visible prefix and the other child consumes only part. -/
public theorem idempotentTake {g : IndexedGrammar T} [Fintype g.nt]
    {flags : List g.flag} {word used : List (WorkSym g)}
    (n : ℕ) (layout : SingletonLayout g flags word used) :
    SingletonLayout g (flags.take n) used used := by
  induction layout generalizing n with
  | nil tail => simpa using SingletonLayout.nil (g := g) tail
  | @cons f flags beta tail tail' d hindex hdollar hlater rest ih =>
      cases n with
      | zero => exact .nil _
      | succ n =>
          simpa using SingletonLayout.cons (f := f) (d := d.markUsed)
            hindex hdollar (fun hne => by
              simpa using hlater (by
                intro hnil
                subst flags
                simp at hne)) (ih n)

end SingletonLayout

/-! ### Maximal consumed prefixes -/

/-- Before a known unused boundary, consumption consists of an initial segment. -/
public theorem NFParse.exists_consumedPrefix
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    (p : NFParse g A stack w) (n : ℕ) (hboundary : ¬ p.ConsumesAt n) :
    ∃ m ≤ n, (∀ k < m, p.ConsumesAt k) ∧ ¬ p.ConsumesAt m := by
  classical
  have hexists : ∃ k : ℕ, ¬ p.ConsumesAt k := ⟨n, hboundary⟩
  let m := Nat.find hexists
  refine ⟨m, Nat.find_min' hexists hboundary, ?_, Nat.find_spec hexists⟩
  intro k hk
  by_contra hnot
  exact Nat.find_min hexists hk hnot

/-! ## Ordinary parse-directed execution -/

/-- Focus the first symbol of a nonempty continuation word.  The empty fallback is convenient
for total statements; every use in the live runner is proved nonempty by its layout. -/
public def wordConfig (g : IndexedGrammar T) (inputPos : ℕ)
    (alpha word : List (WorkSym g)) : Config g :=
  match word with
  | [] => ⟨inputPos, ⟨alpha ++ [.dollar], .hash, []⟩⟩
  | z :: zs => ⟨inputPos, ⟨alpha ++ [.dollar], z, zs⟩⟩

/-- Productive moves leave an already stable frame prefix unchanged.  Initial and freshly
opened pop frames are stable. -/
public def StablePrefix {g : IndexedGrammar T} (alpha : List (WorkSym g)) : Prop :=
  markProductivePrefix alpha = alpha

@[simp] public theorem stablePrefix_nil (g : IndexedGrammar T) :
    StablePrefix (g := g) [] := by
  simp [StablePrefix]

public theorem stablePrefix_append_usedIndex {g : IndexedGrammar T}
    (alpha : List (WorkSym g)) (R : CFlag g) (d : IndexMark) :
    StablePrefix (alpha ++ [WorkSym.index R d.markUsed]) := by
  simp [StablePrefix]

public theorem SingletonLayout.input_ne_nil {g : IndexedGrammar T} [Fintype g.nt]
    {flags : List g.flag} {word used : List (WorkSym g)}
    (layout : SingletonLayout g flags word used) (hne : flags ≠ []) : word ≠ [] := by
  intro hnil
  cases layout <;> simp_all

public theorem SingletonLayout.output_ne_nil {g : IndexedGrammar T} [Fintype g.nt]
    {flags : List g.flag} {word used : List (WorkSym g)}
    (layout : SingletonLayout g flags word used) (hne : flags ≠ []) : used ≠ [] := by
  intro hnil
  cases layout <;> simp_all

/-! ### Stable-context constructors for the elementary moves -/

public theorem composite_plainBinary_stable
    {g : IndexedGrammar T} [Fintype g.nt] (input : List T)
    {A B C : g.nt} (hbinary : AugBinary g A B C)
    (inputPos : ℕ) (alpha beta : List (WorkSym g))
    (hstable : StablePrefix alpha) :
    CompositeStep g input
      ⟨inputPos, ⟨alpha ++ [.dollar], .plain A, beta⟩⟩
      ⟨inputPos, ⟨alpha ++ [.dollar], .plain B, .plain C :: beta⟩⟩ := by
  refine ⟨.plainBinary A B C, hbinary, alpha, beta, rfl, ?_⟩
  change markProductivePrefix alpha = alpha at hstable
  simpa [hstable]

public theorem composite_plainTerminal_stable
    {g : IndexedGrammar T} [Fintype g.nt] (input : List T)
    {A : g.nt} {a : T} (hterminal : AugTerminal g A a)
    (inputPos : ℕ) (alpha beta : List (WorkSym g))
    (hstable : StablePrefix alpha) :
    CompositeStep g input
      ⟨inputPos, ⟨alpha ++ [.dollar], .plain A, beta⟩⟩
      ⟨inputPos, ⟨alpha ++ [.dollar], .terminal a, beta⟩⟩ := by
  refine ⟨.plainTerminal A a, hterminal, alpha, beta, rfl, ?_⟩
  change markProductivePrefix alpha = alpha at hstable
  simpa [hstable]

public theorem composite_plainPushSkip_stable
    {g : IndexedGrammar T} [Fintype g.nt] (input : List T)
    {A B : g.nt} {f : g.flag} (hpush : AugPush g A B f)
    (inputPos : ℕ) (alpha beta : List (WorkSym g)) :
    CompositeStep g input
      ⟨inputPos, ⟨alpha ++ [.dollar], .plain A, beta⟩⟩
      ⟨inputPos, ⟨alpha ++ [.dollar], .plain B, beta⟩⟩ := by
  exact ⟨.plainPushSkip A B f, hpush, alpha, beta, rfl, rfl⟩

public theorem composite_matchTerminal_at
    {g : IndexedGrammar T} [Fintype g.nt] (input : List T)
    (a : T) (inputPos : ℕ) (alpha : List (WorkSym g))
    (Z : WorkSym g) (beta : List (WorkSym g))
    (hinput : input[inputPos]? = some a) :
    CompositeStep g input
      ⟨inputPos, ⟨alpha ++ [.dollar], .terminal a, Z :: beta⟩⟩
      ⟨inputPos + 1, ⟨alpha ++ [.dollar], Z, beta⟩⟩ := by
  exact ⟨.matchTerminal a, hinput, alpha, Z, beta, rfl, rfl⟩

/-- Mutual plain/live execution statement used by the singleton scheduler.  A plain task uses
none of its inherited stack.  A live task uses exactly the nonempty prefix `visible`; its
singleton layout may cross `close` markers but not another selected index or an open `$`.
Every selected token is used at the endpoint. -/
public theorem NFParse.singleton_runs
    {g : IndexedGrammar T} [Fintype g.nt]
    {A : g.nt} {stack : List g.flag} {w : List T}
    (parse : NFParse g A stack w) :
    (∀ (unused : ¬ parse.ConsumesAt 0) (pre post : List T)
        (alpha : List (WorkSym g)) (next : WorkSym g)
        (tail : List (WorkSym g)), StablePrefix alpha →
      Relation.ReflTransGen (CompositeStep g (pre ++ w ++ post))
        ⟨pre.length, ⟨alpha ++ [.dollar], .plain A, next :: tail⟩⟩
        (wordConfig g (pre ++ w).length alpha (next :: tail))) ∧
    (∀ (visible hidden : List g.flag) (word used : List (WorkSym g)),
      stack = visible ++ hidden → visible ≠ [] →
      (∀ k < visible.length, parse.ConsumesAt k) →
      (¬ parse.ConsumesAt visible.length) →
      SingletonLayout g visible word used →
      ∀ (pre post : List T) (alpha : List (WorkSym g)), StablePrefix alpha →
      Relation.ReflTransGen (CompositeStep g (pre ++ w ++ post))
        ⟨pre.length, ⟨alpha ++ [.dollar], .live A, word⟩⟩
        (wordConfig g (pre ++ w).length alpha used)) := by
  induction parse with
  | @binary A B C stack u v r hr hlhs hc hrhs left right ihleft ihright =>
      constructor
      · intro unused pre post alpha next tail hstable
        let input := pre ++ (u ++ v) ++ post
        let c₀ : Config g :=
          ⟨pre.length, ⟨alpha ++ [.dollar], .plain A, next :: tail⟩⟩
        let c₁ : Config g :=
          ⟨pre.length, ⟨alpha ++ [.dollar], .plain B,
            .plain C :: next :: tail⟩⟩
        let c₂ : Config g :=
          ⟨(pre ++ u).length, ⟨alpha ++ [.dollar], .plain C, next :: tail⟩⟩
        have hstep : CompositeStep g input c₀ c₁ := by
          exact composite_plainBinary_stable input
            (binaryRule_aug ⟨r, hr, hlhs, hc, hrhs⟩)
            pre.length alpha (next :: tail) hstable
        have hleft := ihleft.1 (fun h => unused (Or.inl h))
          pre (v ++ post) alpha (.plain C) (next :: tail) hstable
        have hleft' : Relation.ReflTransGen (CompositeStep g input) c₁ c₂ := by
          simpa [input, c₁, c₂, wordConfig, List.append_assoc] using hleft
        have hright := ihright.1 (fun h => unused (Or.inr h))
          (pre ++ u) post alpha next tail hstable
        have hright' : Relation.ReflTransGen (CompositeStep g input) c₂
            (wordConfig g (pre ++ (u ++ v)).length alpha (next :: tail)) := by
          simpa [input, c₂, List.append_assoc] using hright
        exact (Relation.ReflTransGen.single hstep).trans (hleft'.trans hright')
      · intro visible hidden word used hstack hne hall hboundary layout
          pre post alpha hstable
        let n := visible.length
        have hnpos : 0 < n := by
          exact List.length_pos_of_ne_nil hne
        have hboundLeft : ¬ left.ConsumesAt n := by
          intro h
          exact hboundary (Or.inl h)
        have hboundRight : ¬ right.ConsumesAt n := by
          intro h
          exact hboundary (Or.inr h)
        rcases IndexedGrammar.Aho.NFParse.exists_consumedPrefix left n hboundLeft with
          ⟨ml, hml, hallLeft, hfirstLeft⟩
        rcases IndexedGrammar.Aho.NFParse.exists_consumedPrefix right n hboundRight with
          ⟨mr, hmr, hallRight, hfirstRight⟩
        have hfull : ml = n ∨ mr = n := by
          have hdeep := hall (n - 1) (by omega)
          rcases hdeep with hdeep | hdeep
          · left
            have hlt : n - 1 < ml := by
              by_contra hnot
              have hle : ml ≤ n - 1 := Nat.le_of_not_gt hnot
              exact hfirstLeft (left.consumesAt_mono hle hdeep)
            omega
          · right
            have hlt : n - 1 < mr := by
              by_contra hnot
              have hle : mr ≤ n - 1 := Nat.le_of_not_gt hnot
              exact hfirstRight (right.consumesAt_mono hle hdeep)
            omega
        let leftSym : WorkSym g := if ml = 0 then .plain B else .live B
        let rightSym : WorkSym g := if mr = 0 then .plain C else .live C
        have hword : word ≠ [] := layout.input_ne_nil hne
        cases hwordEq : word with
        | nil => exact False.elim (hword hwordEq)
        | cons Z beta =>
          let input := pre ++ (u ++ v) ++ post
          let c₀ : Config g :=
            ⟨pre.length, ⟨alpha ++ [.dollar], .live A, word⟩⟩
          let c₁ : Config g :=
            ⟨pre.length, ⟨alpha ++ [.dollar], leftSym, rightSym :: word⟩⟩
          have hs : markProductivePrefix alpha = alpha := hstable
          have hstep : CompositeStep g input c₀ c₁ := by
            by_cases hml0 : ml = 0
            · by_cases hmr0 : mr = 0
              · have hp0 := hall 0 hnpos
                rcases hp0 with hp0 | hp0
                · exact False.elim (hfirstLeft (by simpa [hml0] using hp0))
                · exact False.elim (hfirstRight (by simpa [hmr0] using hp0))
              · simpa [input, c₀, c₁, leftSym, rightSym, hml0, hmr0,
                    hwordEq, hs] using
                  composite_liveBinaryRight_at input
                    (binaryRule_aug ⟨r, hr, hlhs, hc, hrhs⟩)
                    pre.length alpha Z beta
            · by_cases hmr0 : mr = 0
              · simpa [input, c₀, c₁, leftSym, rightSym, hml0, hmr0,
                    hwordEq, hs] using
                  composite_liveBinaryLeft_at input
                    (binaryRule_aug ⟨r, hr, hlhs, hc, hrhs⟩)
                    pre.length alpha Z beta
              · simpa [input, c₀, c₁, leftSym, rightSym, hml0, hmr0,
                    hwordEq, hs] using
                  composite_liveBinaryBoth_at input
                    (binaryRule_aug ⟨r, hr, hlhs, hc, hrhs⟩)
                    pre.length alpha Z beta
          rcases hfull with hleftFull | hrightFull
          · subst ml
            have hleftLayout : SingletonLayout g visible
                (rightSym :: word) (rightSym :: used) := by
              simpa using layout.prepend [rightSym]
                (by
                  by_cases h : mr = 0 <;> simp [IndexFree, rightSym, h])
                (by
                  by_cases h : mr = 0 <;> simp [DollarFree, rightSym, h])
            have hleftRun := ihleft.2 visible hidden (rightSym :: word)
              (rightSym :: used) hstack hne
              (by simpa [n] using hallLeft) (by simpa [n] using hfirstLeft)
              hleftLayout pre (v ++ post) alpha hstable
            have hleftRun' : Relation.ReflTransGen (CompositeStep g input) c₁
                ⟨(pre ++ u).length,
                  ⟨alpha ++ [.dollar], rightSym, used⟩⟩ := by
              simpa [input, c₁, leftSym, rightSym, n, hnpos.ne', wordConfig,
                List.append_assoc] using hleftRun
            have hrightRun : Relation.ReflTransGen (CompositeStep g input)
                ⟨(pre ++ u).length,
                  ⟨alpha ++ [.dollar], rightSym, used⟩⟩
                (wordConfig g (pre ++ (u ++ v)).length alpha used) := by
              by_cases hmr0 : mr = 0
              · have run := ihright.1 (by simpa [hmr0] using hfirstRight)
                    (pre ++ u) post alpha
                    (match used with | [] => .hash | z :: _ => z)
                    (match used with | [] => [] | _ :: zs => zs) hstable
                cases husedEq : used with
                | nil => exact False.elim (layout.output_ne_nil hne husedEq)
                | cons z zs =>
                  simpa [input, rightSym, hmr0, husedEq, wordConfig,
                    List.append_assoc] using
                      (ihright.1 (by simpa [hmr0] using hfirstRight)
                        (pre ++ u) post alpha z zs hstable)
              · have hvis : visible.take mr ≠ [] := by
                    apply List.ne_nil_of_length_pos
                    simp only [List.length_take]
                    omega
                have hmr' : mr ≤ visible.length := by simpa [n] using hmr
                have hstackRight : stack = visible.take mr ++
                    (visible.drop mr ++ hidden) := by
                  calc
                    stack = visible ++ hidden := hstack
                    _ = visible.take mr ++ (visible.drop mr ++ hidden) := by
                      rw [← List.append_assoc, List.take_append_drop]
                have hrightLayout := layout.idempotentTake mr
                have hallRight' : ∀ k < (visible.take mr).length,
                    right.ConsumesAt k := by
                  intro k hk
                  apply hallRight k
                  rwa [List.length_take, Nat.min_eq_left hmr'] at hk
                have run := ihright.2 (visible.take mr)
                  (visible.drop mr ++ hidden) used used hstackRight hvis
                  hallRight' (by
                    rwa [List.length_take, Nat.min_eq_left hmr'])
                  hrightLayout (pre ++ u) post alpha hstable
                simpa [input, rightSym, hmr0, wordConfig, List.append_assoc] using run
            simpa [input, c₀, hwordEq] using
              (Relation.ReflTransGen.single hstep).trans
                (hleftRun'.trans hrightRun)
          · subst mr
            obtain ⟨middle, hleftRun, hremain⟩ :
                ∃ middle,
                  Relation.ReflTransGen (CompositeStep g input) c₁
                    ⟨(pre ++ u).length,
                      ⟨alpha ++ [.dollar], .live C, middle⟩⟩ ∧
                    SingletonLayout g visible middle used := by
              by_cases hml0 : ml = 0
              · have hplain := ihleft.1 (by simpa [hml0] using hfirstLeft)
                    pre (v ++ post) alpha (.live C) word hstable
                refine ⟨word, ?_, layout⟩
                simpa [input, c₁, leftSym, rightSym, hml0, n, hnpos.ne',
                  wordConfig, List.append_assoc] using hplain
              · rcases layout.splitTake ml with ⟨middle, hprefix, hremain⟩
                have hvis : visible.take ml ≠ [] := by
                  apply List.ne_nil_of_length_pos
                  simp only [List.length_take]
                  omega
                have hml' : ml ≤ visible.length := by simpa [n] using hml
                have hstackLeft : stack = visible.take ml ++
                    (visible.drop ml ++ hidden) := by
                  calc
                    stack = visible ++ hidden := hstack
                    _ = visible.take ml ++ (visible.drop ml ++ hidden) := by
                      rw [← List.append_assoc, List.take_append_drop]
                have hpending : SingletonLayout g (visible.take ml)
                    (.live C :: word) (.live C :: middle) := by
                  simpa using hprefix.prepend [.live C]
                    (by simp [IndexFree]) (by simp [DollarFree])
                have run := ihleft.2 (visible.take ml)
                  (visible.drop ml ++ hidden) (.live C :: word) (.live C :: middle)
                  hstackLeft hvis (by
                    intro k hk
                    apply hallLeft k
                    rwa [List.length_take, Nat.min_eq_left hml'] at hk)
                  (by
                    rwa [List.length_take, Nat.min_eq_left hml']) hpending
                  pre (v ++ post) alpha hstable
                refine ⟨middle, ?_, hremain⟩
                simpa [input, c₁, leftSym, rightSym, hml0, n, hnpos.ne',
                  wordConfig, List.append_assoc] using run
            have hrightRun := ihright.2 visible hidden middle used hstack hne
              (by simpa [n] using hallRight) (by simpa [n] using hfirstRight)
              hremain (pre ++ u) post alpha hstable
            have hrightRun' : Relation.ReflTransGen (CompositeStep g input)
                ⟨(pre ++ u).length,
                  ⟨alpha ++ [.dollar], .live C, middle⟩⟩
                (wordConfig g (pre ++ (u ++ v)).length alpha used) := by
              simpa [input, List.append_assoc] using hrightRun
            simpa [input, c₀, hwordEq] using
              (Relation.ReflTransGen.single hstep).trans
                (hleftRun.trans hrightRun')
  | @pop A B f stack w r hr hlhs hc hrhs rest ih =>
      constructor
      · intro unused
        exact False.elim (unused (by simp [NFParse.ConsumesAt]))
      · intro visible hidden word used hstack hne hall hboundary layout
          pre post alpha hstable
        cases visible with
        | nil => exact False.elim (hne rfl)
        | cons f' visible =>
          have hheads : f = f' := (List.cons.inj hstack).1
          have htails : stack = visible ++ hidden := (List.cons.inj hstack).2
          subst f'
          cases layout with
          | @cons _ _ beta tail tail' d hindex hdollar hlater tailLayout =>
            let input := pre ++ w ++ post
            let selected := WorkSym.index (cflagBase g f) d.markUsed
            let innerAlpha := alpha ++ [.dollar] ++ beta ++ [selected]
            have hinnerStable : StablePrefix innerAlpha := by
              exact stablePrefix_append_usedIndex
                (alpha ++ [.dollar] ++ beta) (cflagBase g f) d
            have hallRest : ∀ k < visible.length, rest.ConsumesAt k := by
              intro k hk
              have hp := hall (k + 1) (by simp; omega)
              simpa [NFParse.ConsumesAt] using hp
            have hboundaryRest : ¬ rest.ConsumesAt visible.length := by
              intro hrest
              apply hboundary
              simpa [NFParse.ConsumesAt, Nat.add_comm, Nat.add_left_comm,
                Nat.add_assoc] using hrest
            have hpop : CompositeStep g input
                ⟨pre.length, ⟨alpha ++ [.dollar], .live A,
                  beta ++ .index (cflagBase g f) d :: tail⟩⟩
                ⟨pre.length, ⟨innerAlpha ++ [.dollar],
                  (if visible = [] then .plain B else .live B),
                  .close :: tail⟩⟩ := by
              by_cases hvis : visible = []
              · subst visible
                simpa [input, innerAlpha, selected] using
                  composite_popPlain_at input (cflagBase g f) d
                    (cflagBase_edge_of_nfparse_pop hr hlhs hc hrhs rest)
                    pre.length alpha beta tail hindex
              · have hlater : d.later = true := hlater hvis
                simpa [input, innerAlpha, selected, hvis] using
                  composite_popLive_at input (cflagBase g f) d
                    (cflagBase_edge_of_nfparse_pop hr hlhs hc hrhs rest)
                    hlater pre.length alpha beta tail hindex
            have hinside : Relation.ReflTransGen (CompositeStep g input)
                ⟨pre.length, ⟨innerAlpha ++ [.dollar],
                  (if visible = [] then .plain B else .live B),
                  .close :: tail⟩⟩
                ⟨(pre ++ w).length,
                  ⟨innerAlpha ++ [.dollar], .close, tail'⟩⟩ := by
              by_cases hvis : visible = []
              · subst visible
                cases tailLayout
                have hrun := ih.1 (by simpa using hboundaryRest)
                  pre post innerAlpha .close tail hinnerStable
                simpa [input, wordConfig] using hrun
              · have hvisible : visible ≠ [] := hvis
                have crossed : SingletonLayout g visible
                    (.close :: tail) (.close :: tail') := by
                  simpa using tailLayout.prepend [.close]
                    (by simp [IndexFree]) (by simp [DollarFree])
                have hrun := ih.2 visible hidden (.close :: tail)
                  (.close :: tail') htails hvisible hallRest hboundaryRest
                  crossed pre post innerAlpha hinnerStable
                simpa [input, wordConfig, hvis] using hrun
            have hreturn : CompositeStep g input
                ⟨(pre ++ w).length,
                  ⟨innerAlpha ++ [.dollar], .close, tail'⟩⟩
                (wordConfig g (pre ++ w).length alpha
                  (beta ++ selected :: tail')) := by
              cases beta with
              | nil =>
                  simpa [innerAlpha, selected, wordConfig] using
                    composite_returnFrame_at input (pre ++ w).length alpha selected
                      [] tail' (by simp [selected]) (by simp [DollarFree])
              | cons z zs =>
                  have hz : z ≠ WorkSym.dollar := by
                    intro hz
                    subst z
                    exact hdollar (by simp)
                  have hfree : DollarFree (zs ++ [selected]) := by
                    apply DollarFree.append
                    · intro hm
                      exact hdollar (by simp [hm])
                    · simp [DollarFree, selected]
                  simpa [innerAlpha, selected, wordConfig, List.append_assoc] using
                    composite_returnFrame_at input (pre ++ w).length alpha z
                      (zs ++ [selected]) tail' hz hfree
            have hallrun := (Relation.ReflTransGen.single hpop).trans
              (hinside.trans (Relation.ReflTransGen.single hreturn))
            simpa [input, selected, wordConfig] using hallrun
  | @push A B f stack w r hr hlhs hc hrhs rest ih =>
      constructor
      · intro unused pre post alpha next tail hstable
        by_cases htop : rest.ConsumesAt 0
        · let input := pre ++ w ++ post
          let token := WorkSym.index (cflagBase g f) .firstPending
          let tokenUsed := WorkSym.index (cflagBase g f) .firstUsed
          let c₁ : Config g :=
            ⟨pre.length, ⟨alpha ++ [.dollar], .live B, token :: next :: tail⟩⟩
          have hstep : CompositeStep g input
              ⟨pre.length, ⟨alpha ++ [.dollar], .plain A, next :: tail⟩⟩ c₁ :=
            composite_plainPushUse_at input
              (pushRule_aug ⟨r, hr, hlhs, hc, hrhs⟩)
              pre.length alpha (next :: tail)
          have hlayout : SingletonLayout g [f]
              (token :: next :: tail) (tokenUsed :: next :: tail) := by
            exact .cons (f := f) (beta := []) (d := .firstPending)
              (by simp [IndexFree]) (by simp [DollarFree])
              (by simp) (.nil (next :: tail))
          have hboundary : ¬ rest.ConsumesAt 1 := by
            simpa [NFParse.ConsumesAt] using unused
          have hrun := ih.2 [f] stack (token :: next :: tail)
            (tokenUsed :: next :: tail) (by simp) (by simp)
            (by
              intro k hk
              have hk0 : k = 0 := by simp at hk; omega
              simpa [hk0] using htop)
            (by simpa using hboundary) hlayout pre post alpha hstable
          have hrun' : Relation.ReflTransGen (CompositeStep g input) c₁
              ⟨(pre ++ w).length,
                ⟨alpha ++ [.dollar], tokenUsed, next :: tail⟩⟩ := by
            simpa [input, c₁, tokenUsed, wordConfig] using hrun
          have herase : CompositeStep g input
              ⟨(pre ++ w).length,
                ⟨alpha ++ [.dollar], tokenUsed, next :: tail⟩⟩
              (wordConfig g (pre ++ w).length alpha (next :: tail)) := by
            simpa [tokenUsed, wordConfig] using
              composite_eraseIndex_at input (cflagBase g f) .firstUsed rfl
                (pre ++ w).length alpha next tail
          exact (Relation.ReflTransGen.single hstep).trans
            (hrun'.trans (Relation.ReflTransGen.single herase))
        · have hstep : CompositeStep g (pre ++ w ++ post)
              ⟨pre.length, ⟨alpha ++ [.dollar], .plain A, next :: tail⟩⟩
              ⟨pre.length, ⟨alpha ++ [.dollar], .plain B, next :: tail⟩⟩ :=
            composite_plainPushSkip_stable (pre ++ w ++ post)
              (pushRule_aug ⟨r, hr, hlhs, hc, hrhs⟩)
              pre.length alpha (next :: tail)
          exact (Relation.ReflTransGen.single hstep).trans
            (ih.1 htop pre post alpha next tail hstable)
      · intro visible hidden word used hstack hne hall hboundary layout
          pre post alpha hstable
        have hword : word ≠ [] := layout.input_ne_nil hne
        have hused : used ≠ [] := layout.output_ne_nil hne
        cases hwordEq : word with
        | nil => exact False.elim (hword hwordEq)
        | cons Z beta =>
          cases husedEq : used with
          | nil => exact False.elim (hused husedEq)
          | cons Z' beta' =>
            let input := pre ++ w ++ post
            let token := WorkSym.index (cflagBase g f) .laterPending
            let tokenUsed := WorkSym.index (cflagBase g f) .laterUsed
            have hlayout : SingletonLayout g (f :: visible)
                (token :: word) (tokenUsed :: used) := by
              exact .cons (f := f) (beta := []) (d := .laterPending)
                (by simp [IndexFree]) (by simp [DollarFree])
                (fun _ => rfl) layout
            have hstack' : f :: stack = (f :: visible) ++ hidden := by
              simp [hstack]
            have hall' : ∀ k < (f :: visible).length, rest.ConsumesAt k := by
              intro k hk
              cases k with
              | zero =>
                  have hp0 : (NFParse.push hr hlhs hc hrhs rest).ConsumesAt 0 :=
                    hall 0 (List.length_pos_of_ne_nil hne)
                  have hr1 : rest.ConsumesAt 1 := hp0
                  exact rest.consumesAt_of_consumesAt_succ 0 hr1
              | succ k =>
                  have hk' : k < visible.length := by simpa using hk
                  exact hall k hk'
            have hboundary' : ¬ rest.ConsumesAt (f :: visible).length := by
              simpa [NFParse.ConsumesAt] using hboundary
            have hstep : CompositeStep g input
                ⟨pre.length, ⟨alpha ++ [.dollar], .live A, word⟩⟩
                ⟨pre.length, ⟨alpha ++ [.dollar], .live B, token :: word⟩⟩ := by
              simpa [input, token, hwordEq] using
                composite_livePushFresh_at input
                  (pushRule_aug ⟨r, hr, hlhs, hc, hrhs⟩)
                  pre.length alpha Z beta
            have hrun := ih.2 (f :: visible) hidden (token :: word)
              (tokenUsed :: used) hstack' (by simp) hall' hboundary'
              hlayout pre post alpha hstable
            have hrun' : Relation.ReflTransGen (CompositeStep g input)
                ⟨pre.length, ⟨alpha ++ [.dollar], .live B, token :: word⟩⟩
                ⟨(pre ++ w).length,
                  ⟨alpha ++ [.dollar], tokenUsed, used⟩⟩ := by
              simpa [input, token, tokenUsed, wordConfig] using hrun
            have herase : CompositeStep g input
                ⟨(pre ++ w).length,
                  ⟨alpha ++ [.dollar], tokenUsed, used⟩⟩
                (wordConfig g (pre ++ w).length alpha used) := by
              simpa [tokenUsed, wordConfig, husedEq] using
                composite_eraseIndex_at input (cflagBase g f) .laterUsed rfl
                  (pre ++ w).length alpha Z' beta'
            simpa [input, hwordEq, husedEq] using
              (Relation.ReflTransGen.single hstep).trans
                (hrun'.trans (Relation.ReflTransGen.single herase))
  | @terminal A stack a r hr hlhs hc hrhs =>
      constructor
      · intro _unused pre post alpha next tail hstable
        have hterminal := composite_plainTerminal_stable
          (pre ++ [a] ++ post) (terminalRule_aug ⟨r, hr, hlhs, hc, hrhs⟩)
          pre.length alpha (next :: tail) hstable
        have hinput : (pre ++ [a] ++ post)[pre.length]? = some a := by simp
        have hmatch := composite_matchTerminal_at (pre ++ [a] ++ post)
          a pre.length alpha next tail hinput
        simpa [wordConfig, List.append_assoc] using
          (Relation.ReflTransGen.single hterminal).trans
            (Relation.ReflTransGen.single hmatch)
      · intro visible hidden word used hstack hne hall
        exact False.elim (by
          have := hall 0 (List.length_pos_of_ne_nil hne)
          simpa [NFParse.ConsumesAt] using this)

/-- Every concrete normal-form parse has an ordinary accepting run of Aho's composite machine.
This is the unconditional semantic completeness theorem; the later accounting refinement only
strengthens the same construction with a uniform work bound. -/
public theorem complete_of_nfparse
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (parse : NFParse g g.initial [] input) :
    Relation.ReflTransGen (CompositeStep g input)
      (initialConfig g) (finalConfig g input.length) := by
  have hrun := (IndexedGrammar.Aho.NFParse.singleton_runs parse).1
    (parse.not_consumesAt_of_stack_nil 0)
    [] [] [] WorkSym.hash [] (stablePrefix_nil g)
  simpa [initialConfig, finalConfig, wordConfig] using hrun

end Aho
end IndexedGrammar
