module

public import Langlib.Grammars.Indexed.NormalForm.Aho.Scheduler.ParseRoutes
public import Langlib.Grammars.Indexed.NormalForm.Aho.Machine.Reachability

@[expose]
public section

/-!
# Aho scheduler state and invariants

Ghost tasks, cursor invariants, schedule reachability, and canonical endpoints.
-/

variable {T : Type}

namespace IndexedGrammar
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
    simp only [hzero, Nat.mul_zero]
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
      ScheduleAtom.closeOwner?] ;
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


end Aho
end IndexedGrammar
