module

public import Langlib.Grammars.Indexed.NormalForm.AhoGhostLayout
public import Langlib.Grammars.Indexed.NormalForm.AhoProductiveOwners

@[expose]
public section

/-!
# Canonical compressed relations used by the bounded runner

The physical block layout remembers only that a finite relation denotes its concrete flag
block.  Completeness also needs the converse normalization fact: because relational
composition is associative, every such provenance tree is equal to the canonical
right-associated relation `compressedFlags`.
-/

variable {T : Type}

namespace IndexedGrammar
namespace Aho

/-- A denoted compressed relation always represents a nonempty concrete block. -/
public theorem CFlag.Denotes.flags_ne_nil
    {g : IndexedGrammar T} [Fintype g.nt]
    {flags : List g.flag} {R : CFlag g}
    (h : CFlag.Denotes g flags R) : flags ≠ [] := by
  induction h with
  | base f => simp
  | @comp fs gs R S hR hS ihR ihS =>
      intro hnil
      have hlength := congrArg List.length hnil
      have hpos : 0 < fs.length := List.length_pos_of_ne_nil ihR
      simp only [List.length_append, List.length_nil] at hlength
      omega

/-- Canonical compression distributes over concatenation of two nonempty flag blocks. -/
public theorem compressedFlags_append
    {g : IndexedGrammar T} [Fintype g.nt]
    (f : g.flag) (fs : List g.flag) (h : g.flag) (hs : List g.flag) :
    compressedFlags g f (fs ++ h :: hs) =
      cflagComp g (compressedFlags g f fs) (compressedFlags g h hs) := by
  induction fs generalizing f with
  | nil => rfl
  | cons f' fs ih =>
      simp only [List.cons_append, compressedFlags]
      rw [ih]
      exact (cflagComp_assoc (cflagBase g f)
        (compressedFlags g f' fs) (compressedFlags g h hs)).symm

/-- Every provenance tree has a canonical nonempty flag-list presentation. -/
public theorem CFlag.Denotes.exists_eq_compressedFlags
    {g : IndexedGrammar T} [Fintype g.nt]
    {flags : List g.flag} {R : CFlag g}
    (h : CFlag.Denotes g flags R) :
    ∃ f rest, flags = f :: rest ∧ R = compressedFlags g f rest := by
  induction h with
  | base f => exact ⟨f, [], rfl, rfl⟩
  | @comp fs gs R S hR hS ihR ihS =>
      rcases ihR with ⟨f, fs', rfl, rfl⟩
      rcases ihS with ⟨h, hs', rfl, rfl⟩
      refine ⟨f, fs' ++ h :: hs', by simp, ?_⟩
      rw [compressedFlags_append]

/-- Provenance determines the compressed relation uniquely. -/
public theorem CFlag.Denotes.eq_compressedFlags
    {g : IndexedGrammar T} [Fintype g.nt]
    {f : g.flag} {flags : List g.flag} {R : CFlag g}
    (h : CFlag.Denotes g (f :: flags) R) :
    R = compressedFlags g f flags := by
  rcases h.exists_eq_compressedFlags with ⟨f', rest, hflags, hR⟩
  simp only [List.cons.injEq] at hflags
  rcases hflags with ⟨rfl, rfl⟩
  exact hR

/-! ### Event-free prefixes are unary pop paths -/

/-- If every productive event of a parse lies strictly below the occurrence selected by a
route, that route crosses no binary node.  This is the semantic reason an interval between two
consecutive event cuts can be represented by one atomic compressed relation. -/
public theorem NFParse.ConsumeRoute.noBinary_of_eventDepths_gt
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {k : ℕ}
    (route : NFParse.ConsumeRoute g parse k)
    (hevents : ∀ d ∈ parse.eventDepths, k < d) : route.NoBinary := by
  induction route with
  | @binaryLeft A B C stack u v r hr hlhs hc hrhs left right k route ih =>
      have hzero := hevents 0 (by simp [NFParse.eventDepths])
      omega
  | @binaryRight A B C stack u v r hr hlhs hc hrhs left right k route ih =>
      have hzero := hevents 0 (by simp [NFParse.eventDepths])
      omega
  | popHere => simp [NFParse.ConsumeRoute.NoBinary]
  | @popTail A B f stack w r hr hlhs hc hrhs rest k route ih =>
      apply ih
      intro d hd
      have hmem : d + 1 ∈
          (NFParse.pop hr hlhs hc hrhs rest).eventDepths := by
        exact Finset.mem_image.mpr ⟨d, hd, by omega⟩
      have := hevents (d + 1) hmem
      omega
  | @push A B f stack w r hr hlhs hc hrhs rest k route ih =>
      apply ih
      intro d hd
      have hmem : d.pred ∈
          (NFParse.push hr hlhs hc hrhs rest).eventDepths := by
        exact Finset.mem_image.mpr ⟨d, hd, rfl⟩
      have := hevents d.pred hmem
      cases d with
      | zero => simp at this
      | succ d => simp only [Nat.pred_succ] at this; omega

/-- A whole first block with no event at or above its last flag has an atomic viable pop
continuation.  The result works for the relation physically stored by `BlockLayout`, not only
for the syntactically canonical relation, because denotation provenance is unique. -/
public theorem exists_popContinuation_of_eventFree_block_with_owners
    {g : IndexedGrammar T} [Fintype g.nt]
    {A : g.nt} {block suffix : List g.flag} {w : List T}
    (parse : NFParse g A (block ++ suffix) w)
    {R : CFlag g} (hdenotes : CFlag.Denotes g block R)
    (hlast : parse.ConsumesAt (block.length - 1))
    (hevents : ∀ d ∈ parse.eventDepths, block.length - 1 < d) :
    ∃ continuation : PopContinuation block suffix parse R,
      continuation.rest.nodeCount < parse.nodeCount ∧
      (∀ j, continuation.rest.ConsumesAt j ↔
        parse.ConsumesAt (block.length + j)) ∧
      (∀ d, d ∈ continuation.rest.eventDepths ↔
        block.length + d ∈ parse.eventDepths) ∧
      ∀ d, continuation.rest.eventOwnerNat d =
        parse.eventOwnerNat (block.length + d) := by
  rcases hdenotes.exists_eq_compressedFlags with ⟨f, flags, hblock, hrelation⟩
  subst block
  simp only [List.length_cons, Nat.add_sub_cancel] at hlast hevents ⊢
  let route : NFParse.ConsumeRoute g parse flags.length :=
    NFParse.ConsumeRoute.ofConsumesAt parse flags.length hlast
  have hroute : route.NoBinary :=
    IndexedGrammar.Aho.NFParse.ConsumeRoute.noBinary_of_eventDepths_gt
      route hevents
  rcases consumeRoute_popContinuation_noBinary_with_owners route hroute with
    ⟨Y, suffix', rest, htransport⟩
  have hsuffix := htransport.1
  have path := htransport.2.1
  have hcount := htransport.2.2.1
  have hconsumes := htransport.2.2.2.1
  have hevents' := htransport.2.2.2.2.1
  have howners := htransport.2.2.2.2.2
  have hdrop : ((f :: flags) ++ suffix).drop (flags.length + 1) = suffix := by
    simp
  have hsuffix' : suffix' = suffix := hsuffix.trans hdrop
  let rest' : NFParse g Y suffix w := hsuffix' ▸ rest
  have hrestCount : rest'.nodeCount = rest.nodeCount :=
    NFParse.nodeCount_cast_stack rest hsuffix'
  have path' : PopPath g A (f :: flags) Y := by
    simpa using path
  have hedgeCanonical : compressedFlags g f flags A Y = true := by
    rcases path'.compressedFlags_edge with ⟨f', flags', hflags, hedge⟩
    simp only [List.cons.injEq] at hflags
    rcases hflags with ⟨rfl, rfl⟩
    exact hedge
  have hedge : R A Y = true := by
    rw [hrelation]
    exact hedgeCanonical
  let continuation : PopContinuation (f :: flags) suffix parse R :=
    ⟨Y, rest', hedge⟩
  refine ⟨continuation, ?_, ?_, ?_, ?_⟩
  · change rest'.nodeCount < parse.nodeCount
    rw [hrestCount]
    exact hcount
  · intro j
    change rest'.ConsumesAt j ↔ parse.ConsumesAt (flags.length + 1 + j)
    have hcast : rest'.ConsumesAt j ↔ rest.ConsumesAt j := by
      dsimp [rest']
      cases hsuffix'
      rfl
    rw [hcast, hconsumes]
  · intro d
    change d ∈ rest'.eventDepths ↔ flags.length + 1 + d ∈ parse.eventDepths
    have hcast : d ∈ rest'.eventDepths ↔ d ∈ rest.eventDepths := by
      dsimp [rest']
      cases hsuffix'
      rfl
    rw [hcast, hevents']
  · intro d
    change rest'.eventOwnerNat d = parse.eventOwnerNat (flags.length + 1 + d)
    have hcast : rest'.eventOwnerNat d = rest.eventOwnerNat d := by
      dsimp [rest']
      cases hsuffix'
      rfl
    rw [hcast, howners]

/-- Every productive event of `parse` is aligned with a whole compressed-block boundary. -/
public structure EventCompatible
    {g : IndexedGrammar T} [Fintype g.nt]
    {A : g.nt} {stack : List g.flag} {w : List T}
    (parse : NFParse g A stack w) (blocks : List (List g.flag)) where
  boundary : ∀ d ∈ parse.eventDepths, BlockLayout.Boundary blocks d

/-! ## Root-relative ghost schedule interfaces -/

/-- Package an arbitrary concrete parse task at its exact input interval. -/
public def scheduleTaskOfParse
    {g : IndexedGrammar T} {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    (parse : NFParse g A stack w) (pre post : List T)
    (input_eq : input = pre ++ w ++ post) (mode : TaskMode parse) :
    ScheduleTask g input where
  A := A
  stack := stack
  yield := w
  parse := parse
  pre := pre
  post := post
  input_eq := input_eq
  mode := mode

/-- Ghost analogue of `wordConfig`: focus the first continuation atom. -/
public def scheduleWordCursor
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (alpha word : List (ScheduleAtom g input)) : ScheduleCursor g input :=
  match word with
  | [] => ⟨alpha ++ [.dollar], .hash, []⟩
  | z :: zs => ⟨alpha ++ [.dollar], z, zs⟩

@[simp] public theorem scheduleWordCursor_erase
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (alpha word : List (ScheduleAtom g input)) :
    (scheduleWordCursor alpha word).erase =
      (wordConfig g 0 (alpha.map ScheduleAtom.workSym)
        (word.map ScheduleAtom.workSym)).work := by
  cases word <;> simp [scheduleWordCursor, wordConfig, ScheduleCursor.erase,
    ScheduleAtom.workSym]

/-- Build a scheduler state once interval arithmetic and the ownership invariant are known. -/
public def scheduleStateOfCursor
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (inputPos : ℕ) (hpos : inputPos ≤ input.length)
    (cursor : ScheduleCursor g input) (invariant : ScheduleInvariant cursor) :
    ScheduleState g input :=
  ⟨inputPos, hpos, cursor, invariant⟩

/-- The reusable generic-owner bank, partitioned into labels present on persistent indices and
labels still free.  The bank has exactly `4|input|` elements even though labels inhabit the
larger `Fin (6|input|)` carrier used to keep them disjoint from semantic tickets. -/
public structure IndexOwnerPool
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
  (cursor : ScheduleCursor g input) where
  free : List (Fin (10 * input.length))
  all_nodup : (cursor.indexOwners ++ free).Nodup
  all_perm : (cursor.indexOwners ++ free).Perm
    (genericOwnerRange g input)

namespace IndexOwnerPool

public theorem free_nodup
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {cursor : ScheduleCursor g input} (pool : IndexOwnerPool cursor) :
    pool.free.Nodup :=
  (List.nodup_append.mp pool.all_nodup).2.1

public theorem free_disjoint
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {cursor : ScheduleCursor g input} (pool : IndexOwnerPool cursor) :
    List.Disjoint cursor.indexOwners pool.free :=
  by
    intro owner hindices hfree
    exact (List.nodup_append.mp pool.all_nodup).2.2 owner hindices owner hfree rfl

/-- Every label in the generic owner universe is either present or remains free. -/
public theorem mem_indices_or_free
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {cursor : ScheduleCursor g input} (pool : IndexOwnerPool cursor)
    (owner : Fin (10 * input.length))
    (hgeneric : owner ∈ genericOwnerRange g input) :
    owner ∈ cursor.indexOwners ∨ owner ∈ pool.free := by
  have := pool.all_perm.mem_iff.mpr hgeneric
  simpa only [List.mem_append] using this

/-- An owner absent from the work tape is available in the exhaustive free pool. -/
public theorem mem_free_of_not_mem_indices
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {cursor : ScheduleCursor g input} (pool : IndexOwnerPool cursor)
    {owner : Fin (10 * input.length)}
    (hgeneric : owner ∈ genericOwnerRange g input)
    (howner : owner ∉ cursor.indexOwners) : owner ∈ pool.free :=
  (pool.mem_indices_or_free owner hgeneric).resolve_left howner

/-- Every persistent index owner comes from the generic pool universe. -/
public theorem mem_genericOwnerRange_of_mem_indices
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {cursor : ScheduleCursor g input} (pool : IndexOwnerPool cursor)
    {owner : Fin (10 * input.length)} (howner : owner ∈ cursor.indexOwners) :
    owner ∈ genericOwnerRange g input := by
  exact pool.all_perm.mem_iff.mp (List.mem_append_left _ howner)

/-- Every free label also comes from the generic pool universe. -/
public theorem mem_genericOwnerRange_of_mem_free
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {cursor : ScheduleCursor g input} (pool : IndexOwnerPool cursor)
    {owner : Fin (10 * input.length)} (howner : owner ∈ pool.free) :
    owner ∈ genericOwnerRange g input := by
  exact pool.all_perm.mem_iff.mp (List.mem_append_right _ howner)

/-- Exact conservation of the reusable bank. -/
public theorem index_count_add_free_length
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {cursor : ScheduleCursor g input} (pool : IndexOwnerPool cursor) :
    cursor.indexOwners.length + pool.free.length = 6 * input.length := by
  have hlength := pool.all_perm.length_eq
  simpa [genericOwnerRange_length] using hlength

/-- The generic bank, rather than the larger ambient owner carrier, bounds persistent
indices. -/
public theorem index_count_le
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {cursor : ScheduleCursor g input} (pool : IndexOwnerPool cursor) :
    cursor.indexOwners.length ≤ 6 * input.length := by
  have := pool.index_count_add_free_length
  omega

/-- A free reusable label leaves strict room for one more persistent index. -/
public theorem index_count_lt_of_free_ne_nil
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {cursor : ScheduleCursor g input} (pool : IndexOwnerPool cursor)
    (hfree : pool.free ≠ []) :
    cursor.indexOwners.length < 6 * input.length := by
  have hconserve := pool.index_count_add_free_length
  have hfreePos : 0 < pool.free.length := List.length_pos_of_ne_nil hfree
  omega

/-- A nonempty free suffix supplies a generic label directly, without attempting to allocate a
semantic event ticket. -/
public theorem exists_free_generic
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {cursor : ScheduleCursor g input} (pool : IndexOwnerPool cursor)
    (hfree : pool.free ≠ []) :
    ∃ owner : Fin (10 * input.length),
      owner ∈ pool.free ∧ owner ∈ genericOwnerRange g input := by
  cases hfreeList : pool.free with
  | nil => exact False.elim (hfree hfreeList)
  | cons owner rest =>
      refine ⟨owner, ?_, pool.mem_genericOwnerRange_of_mem_free ?_⟩ <;>
        simp [hfreeList]

/-- Scratch is not a reusable generic label and therefore cannot occur on a persistent index
described by this pool. -/
public theorem scratchOwner_not_mem_indices
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {cursor : ScheduleCursor g input} (pool : IndexOwnerPool cursor)
    (hinput : 0 < input.length) :
    ProductiveOwnerWindow.scratchOwner (g := g) hinput ∉ cursor.indexOwners := by
  intro hmem
  have hge := genericOwnerRange_val_ge
    (pool.mem_genericOwnerRange_of_mem_indices hmem)
  simp only [genericOwnerOffset, ProductiveOwnerWindow.scratchOwner_val] at hge
  omega

/-- Transient is likewise disjoint from every persistent owner described by the generic pool. -/
public theorem transientOwner_not_mem_indices
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {cursor : ScheduleCursor g input} (pool : IndexOwnerPool cursor)
    (hinput : 0 < input.length) :
    ProductiveOwnerWindow.transientOwner (g := g) hinput ∉ cursor.indexOwners := by
  intro hmem
  have hge := genericOwnerRange_val_ge
    (pool.mem_genericOwnerRange_of_mem_indices hmem)
  simp only [genericOwnerOffset, ProductiveOwnerWindow.transientOwner_val] at hge
  omega

end IndexOwnerPool


/-- Start cursor for a plain parse task. -/
public def plainScheduleCursor
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    (parse : NFParse g A stack w) (unused : ¬ parse.ConsumesAt 0)
    (pre post : List T) (input_eq : input = pre ++ w ++ post)
    (alpha : List (ScheduleAtom g input)) (next : ScheduleAtom g input)
    (tail : List (ScheduleAtom g input)) : ScheduleCursor g input :=
  ⟨alpha ++ [.dollar],
    .task (scheduleTaskOfParse parse pre post input_eq (.plain unused)), next :: tail⟩

/-- Start cursor for a live parse task. -/
public def liveScheduleCursor
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    (parse : NFParse g A stack w) (used : parse.ConsumesAt 0)
    (pre post : List T) (input_eq : input = pre ++ w ++ post)
    (alpha word : List (ScheduleAtom g input)) : ScheduleCursor g input :=
  ⟨alpha ++ [.dollar],
    .task (scheduleTaskOfParse parse pre post input_eq (.live used)), word⟩


end Aho
end IndexedGrammar
