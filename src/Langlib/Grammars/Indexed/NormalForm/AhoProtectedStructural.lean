module

public import Langlib.Grammars.Indexed.NormalForm.AhoProtectedRunner

@[expose]
public section

/-!
# Productive structural steps for protected tasks

The protected atomic runner handles a unary interval ending in a pop. At a productive binary
event the two children may consume different aligned prefixes of the shared protected layout;
at a push event the runner allocates a fresh compressed singleton.
-/

variable {T : Type}

namespace IndexedGrammar
namespace Aho

namespace BlockLayout.Boundary

/-- Strict growth of flattened nonempty block prefixes reflects the prefix-count order. -/
private theorem takeFlattenLengthReflectsLECurrent
    {g : IndexedGrammar T} [Fintype g.nt]
    {blocks : List (List g.flag)}
    (hne : ∀ block ∈ blocks, block ≠ [])
    {a b : ℕ} (ha : a ≤ blocks.length) (hb : b ≤ blocks.length)
    (hlength : (blocks.take a).flatten.length ≤
      (blocks.take b).flatten.length) : a ≤ b := by
  induction blocks generalizing a b with
  | nil =>
      simp only [List.length_nil] at ha hb
      omega
  | cons block blocks ih =>
      have hblock : block ≠ [] := hne block (by simp)
      have htail : ∀ candidate ∈ blocks, candidate ≠ [] := by
        intro candidate hmem
        exact hne candidate (by simp [hmem])
      cases a with
      | zero => exact Nat.zero_le _
      | succ a =>
          cases b with
          | zero =>
              simp only [List.take_succ_cons, List.flatten_cons, List.length_append,
                List.take_zero, List.flatten_nil, List.length_nil] at hlength
              have hpos := List.length_pos_of_ne_nil hblock
              omega
          | succ b =>
              have ha' : a ≤ blocks.length := by
                simp only [List.length_cons] at ha
                omega
              have hb' : b ≤ blocks.length := by
                simp only [List.length_cons] at hb
                omega
              have htailLength : (blocks.take a).flatten.length ≤
                  (blocks.take b).flatten.length := by
                simp only [List.take_succ_cons, List.flatten_cons,
                  List.length_append] at hlength
                omega
              exact Nat.succ_le_succ (ih htail ha' hb' htailLength)

/-- Local earlier-boundary block-count comparison used by the structural proof. -/
private theorem blockCountLEOfFlagCountLECurrent
    {g : IndexedGrammar T} [Fintype g.nt]
    {blocks : List (List g.flag)} {d e : ℕ}
    (hne : ∀ block ∈ blocks, block ≠ [])
    (left : BlockLayout.Boundary blocks d)
    (right : BlockLayout.Boundary blocks e) (hde : d ≤ e) :
    left.blockCount ≤ right.blockCount := by
  apply takeFlattenLengthReflectsLECurrent hne left.blockCount_le right.blockCount_le
  rw [← left.flagCount_eq, ← right.flagCount_eq]
  exact hde

/-- Restrict an earlier aligned boundary to the block prefix cut by a later boundary. -/
private def takeOfLECurrent
    {g : IndexedGrammar T} [Fintype g.nt]
    {blocks : List (List g.flag)} {d e : ℕ}
    (hne : ∀ block ∈ blocks, block ≠ [])
    (cut : BlockLayout.Boundary blocks e)
    (boundary : BlockLayout.Boundary blocks d) (hde : d ≤ e) :
    BlockLayout.Boundary (blocks.take cut.blockCount) d where
  blockCount := boundary.blockCount
  blockCount_le := by
    rw [List.length_take, Nat.min_eq_left cut.blockCount_le]
    exact blockCountLEOfFlagCountLECurrent hne boundary cut hde
  flagCount_eq := by
    have hcount := blockCountLEOfFlagCountLECurrent hne boundary cut hde
    simpa [List.take_take, Nat.min_eq_left hcount] using boundary.flagCount_eq

end BlockLayout.Boundary

namespace NFParse

/-- An unused occurrence bounds every productive event depth from above. -/
private theorem eventDepthLEOfNotConsumesAtCurrent
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    (parse : NFParse g A stack w) {m d : ℕ}
    (hboundary : ¬ parse.ConsumesAt m) (hd : d ∈ parse.eventDepths) : d ≤ m := by
  by_contra hnot
  have hmd : m < d := Nat.lt_of_not_ge hnot
  exact hboundary ((parse.consumesAt_iff_exists_mem_eventDepths_lt m).2
    ⟨d, hd, hmd⟩)

/-- A positive maximal consumed-prefix length is a productive event boundary. -/
private theorem maximalConsumedPrefixMemEventDepthsCurrent
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    (parse : NFParse g A stack w) {m : ℕ} (hm : 0 < m)
    (hall : ∀ k < m, parse.ConsumesAt k)
    (hboundary : ¬ parse.ConsumesAt m) : m ∈ parse.eventDepths := by
  have hprevious : parse.ConsumesAt (m - 1) := hall (m - 1) (by omega)
  rcases (parse.consumesAt_iff_exists_mem_eventDepths_lt (m - 1)).1 hprevious with
    ⟨d, hd, hlt⟩
  have hle := eventDepthLEOfNotConsumesAtCurrent parse hboundary hd
  have hdm : d = m := by omega
  exact hdm ▸ hd

end NFParse

namespace EventCompatible

/-- Restrict compatibility to an aligned maximal consumed prefix. -/
private def takeAtConsumedBoundaryCurrent
    {g : IndexedGrammar T} [Fintype g.nt]
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {blocks : List (List g.flag)}
    {m : ℕ} (layoutNonempty : ∀ block ∈ blocks, block ≠ [])
    (compatible : EventCompatible parse blocks)
    (cut : BlockLayout.Boundary blocks m)
    (hboundary : ¬ parse.ConsumesAt m) :
    EventCompatible parse (blocks.take cut.blockCount) where
  boundary d hd :=
    BlockLayout.Boundary.takeOfLECurrent layoutNonempty cut
      (compatible.boundary d hd)
      (NFParse.eventDepthLEOfNotConsumesAtCurrent parse hboundary hd)

end EventCompatible

/-- Owners aligned strictly after a maximal consumed boundary cannot be local event owners. -/
private theorem EventOwnedLayout.drop_outside_of_maximalBoundary
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w}
    {window : ProductiveOwnerWindow (input := input) parse}
    {blocks : List (List g.flag)}
    {owners : List (Fin (10 * input.length))}
    (ledger : EventOwnedLayout parse window blocks owners)
    (hne : ∀ block ∈ blocks, block ≠ []) {d : ℕ}
    (boundary : BlockLayout.Boundary blocks d)
    (hmax : ¬ parse.ConsumesAt d) :
    ∀ owner ∈ owners.drop boundary.blockCount,
      OutsideProductiveWindow window owner := by
  intro owner hmem
  rcases List.mem_iff_getElem.mp hmem with ⟨j, hj, hget⟩
  have hiOwners : boundary.blockCount + j < owners.length := by
    rw [List.length_drop] at hj
    omega
  have hiBlocks : boundary.blockCount + j < blocks.length := by
    rw [← ledger.owners_length]
    exact hiOwners
  let i : Fin blocks.length := ⟨boundary.blockCount + j, hiBlocks⟩
  have hgetGlobal : owners[boundary.blockCount + j] = owner := by
    simpa using hget
  have howner : blockOwnerAt owners ledger.owners_length i = owner := by
    simpa [blockOwnerAt, i] using hgetGlobal
  rcases ledger.owner_at i with hlocal | hout
  · rcases hlocal with ⟨hevent, _⟩
    have hdepth : blockEndpoint blocks i ≤ d := by
      by_contra hnot
      apply hmax
      exact (parse.consumesAt_iff_exists_mem_eventDepths_lt d).2
        ⟨blockEndpoint blocks i, hevent, Nat.lt_of_not_ge hnot⟩
    have hcount : i.val + 1 ≤ boundary.blockCount := by
      have h := BlockLayout.Boundary.blockCountLEOfFlagCountLECurrent hne
        (BlockLayout.Boundary.ofBlockCount blocks (i.val + 1) (by omega))
        boundary (by simpa [blockEndpoint] using hdepth)
      exact h
    dsimp [i] at hcount
    omega
  · simpa [howner] using hout

/-- Reclassify the owner suffix after a maximal child boundary as outside the active window. -/
private def ScheduleOwnerLedger.restrictAtMaximalBoundary
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w}
    {window : ProductiveOwnerWindow (input := input) parse}
    {cursor : ScheduleCursor g input}
    {blocks : List (List g.flag)}
    {owners : List (Fin (10 * input.length))}
    (ownerLedger : ScheduleOwnerLedger parse window cursor)
    (hactive : ownerLedger.active = owners)
    (layout : EventOwnedLayout parse window blocks owners)
    (hne : ∀ block ∈ blocks, block ≠ []) {d : ℕ}
    (boundary : BlockLayout.Boundary blocks d)
    (hmax : ¬ parse.ConsumesAt d) :
    ScheduleOwnerLedger parse window cursor where
  active := owners.take boundary.blockCount
  outside := owners.drop boundary.blockCount ++ ownerLedger.outside
  right_eq := by
    rw [ownerLedger.right_eq, hactive]
    conv_lhs => rw [← List.take_append_drop boundary.blockCount owners]
    simp only [List.append_assoc]
  outside_at owner hmem := by
    rcases List.mem_append.mp hmem with hdropped | houtside
    · exact layout.drop_outside_of_maximalBoundary hne boundary hmax owner hdropped
    · exact ownerLedger.outside_at owner houtside
  frames := ownerLedger.frames
  prefixLedger := ownerLedger.prefixLedger

/-- Restrict an event-owner layout to an aligned owner/block prefix. -/
private def EventOwnedLayout.take
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w}
    {window : ProductiveOwnerWindow (input := input) parse}
    {blocks : List (List g.flag)}
    {owners : List (Fin (10 * input.length))}
    (ledger : EventOwnedLayout parse window blocks owners) (n : ℕ)
    (compatible : EventCompatible parse (blocks.take n)) :
    EventOwnedLayout parse window (blocks.take n) (owners.take n) where
  compatible := compatible
  owners_length := by simp [ledger.owners_length]
  endpoint_pos := by
    intro i
    let iv := i.val
    have htake : iv < (blocks.take n).length := i.isLt
    simp only [List.length_take] at htake
    have hiBlocks : iv < blocks.length := by
      omega
    let j : Fin blocks.length := ⟨iv, hiBlocks⟩
    have hin : iv + 1 ≤ n := by
      omega
    simpa [blockEndpoint, iv, j, List.take_take, Nat.min_eq_left hin] using
      ledger.endpoint_pos j
  owner_at := by
    intro i
    let iv := i.val
    have htake : iv < (blocks.take n).length := i.isLt
    simp only [List.length_take] at htake
    have hiBlocks : iv < blocks.length := by
      omega
    let j : Fin blocks.length := ⟨iv, hiBlocks⟩
    have hin : iv + 1 ≤ n := by
      omega
    simpa [blockEndpoint, blockOwnerAt, iv, j, List.take_take,
      Nat.min_eq_left hin] using ledger.owner_at j

/-- Local carrier-current version of the marked-prefix layout lemma. -/
private theorem ScheduleBlockLayout.idempotentTakeCurrent
    {g : IndexedGrammar T} [Fintype g.nt]
    {input : List T} {flags : List g.flag} {blocks : List (List g.flag)}
    {owners : List (Fin (10 * input.length))}
    {word used : List (ScheduleAtom g input)}
    (n : ℕ) (layout : ScheduleBlockLayout g input flags blocks owners word used) :
    ScheduleBlockLayout g input (blocks.take n).flatten (blocks.take n)
      (owners.take n) used used := by
  induction layout generalizing n with
  | nil tail =>
      simpa using ScheduleBlockLayout.nil (g := g) (input := input) tail
  | @cons flags blocks owners beta tail tail' idx block_ne hindex hdollar hlater
      fresh rest ih =>
      cases n with
      | zero => exact .nil _
      | succ n =>
          simpa using ScheduleBlockLayout.cons (idx := idx.markUsed)
            block_ne hindex hdollar (fun hne => by
              simpa using hlater (by
                intro hflags
                have hblocks : blocks = [] :=
                  rest.erase.blocks_eq_nil_of_flags_eq_nil hflags
                subst blocks
                simp at hne))
            (by
              intro hmem
              exact fresh (List.mem_of_mem_take hmem)) (ih n)

/-- Local carrier-current version of splitting a layout at an aligned flag boundary. -/
private theorem ScheduleBlockLayout.splitAtBoundaryCurrent
    {g : IndexedGrammar T} [Fintype g.nt]
    {input : List T} {flags : List g.flag} {blocks : List (List g.flag)}
    {owners : List (Fin (10 * input.length))}
    {word used : List (ScheduleAtom g input)} {flagCount : ℕ}
    (layout : ScheduleBlockLayout g input flags blocks owners word used)
    (boundary : BlockLayout.Boundary blocks flagCount) :
    ∃ middle,
      ScheduleBlockLayout g input (flags.take flagCount)
        (blocks.take boundary.blockCount) (owners.take boundary.blockCount)
        word middle ∧
      ScheduleBlockLayout g input flags blocks owners middle used := by
  rcases layout.splitTake boundary.blockCount with ⟨middle, hprefix, hremain⟩
  refine ⟨middle, ?_, hremain⟩
  have htake : flags.take flagCount =
      (blocks.take boundary.blockCount).flatten := by
    calc
      flags.take flagCount =
          flags.take (blocks.take boundary.blockCount).flatten.length := by
            exact congrArg (List.take · flags) boundary.flagCount_eq
      _ = (blocks.take boundary.blockCount).flatten :=
        layout.erase.take_flatten_take boundary.blockCount
  simpa only [htake] using hprefix

private def IndexOwnerPool.transportProtectedStructural
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {old new : ScheduleCursor g input} (pool : IndexOwnerPool old)
    (hindices : new.indexOwners = old.indexOwners) : IndexOwnerPool new where
  free := pool.free
  all_nodup := by simpa [hindices] using pool.all_nodup
  all_perm := by simpa [hindices] using pool.all_perm

/-- Reindex resources along propositional equality of ghost cursors. -/
private def ScheduleRunResources.rebaseCursor
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {pre : List T}
    {old new : ScheduleCursor g input}
    (resources : ScheduleRunResources parse pre old) (h : new = old) :
    ScheduleRunResources parse pre new := h ▸ resources

@[simp] private theorem ScheduleRunResources.rebaseCursor_free
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {pre : List T}
    {old new : ScheduleCursor g input}
    (resources : ScheduleRunResources parse pre old) (h : new = old) :
    (resources.rebaseCursor h).pool.free = resources.pool.free := by
  cases h
  rfl

@[simp] private theorem ScheduleRunResources.rebaseCursor_window
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {pre : List T}
    {old new : ScheduleCursor g input}
    (resources : ScheduleRunResources parse pre old) (h : new = old) :
    (resources.rebaseCursor h).window = resources.window := by
  cases h
  rfl

@[simp] private theorem ScheduleRunResources.rebaseCursor_active
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {pre : List T}
    {old new : ScheduleCursor g input}
    (resources : ScheduleRunResources parse pre old) (h : new = old) :
    (resources.rebaseCursor h).ownerLedger.active =
      resources.ownerLedger.active := by
  cases h
  rfl

@[simp] private theorem ScheduleRunResources.rebaseCursor_ticketOf
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {pre : List T}
    {old new : ScheduleCursor g input}
    (resources : ScheduleRunResources parse pre old) (h : new = old) :
    (resources.rebaseCursor h).tickets.ticketOf = resources.tickets.ticketOf := by
  cases h
  rfl

/-- Strict parking transports through propositional cursor rebasing. -/
private theorem ScheduleRunResources.rebaseCursor_parkingBelow
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {pre : List T}
    {old new : ScheduleCursor g input}
    (resources : ScheduleRunResources parse pre old) (h : new = old)
    (hbelow : resources.tickets.ParkingBelow resources.window) :
    (resources.rebaseCursor h).tickets.ParkingBelow
      (resources.rebaseCursor h).window := by
  cases h
  exact hbelow

@[simp] private theorem ScheduleRunResources.rebaseCursor_semanticOwners
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {pre : List T}
    {old new : ScheduleCursor g input}
    (resources : ScheduleRunResources parse pre old) (h : new = old)
    (owners : List (Fin (10 * input.length))) :
    (resources.rebaseCursor h).tickets.semanticOwners owners =
      resources.tickets.semanticOwners owners := by
  cases h
  rfl

@[simp] private theorem ScheduleRunResources.rebaseCursor_ticketShadowBlocks
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {pre : List T}
    {old new : ScheduleCursor g input}
    (resources : ScheduleRunResources parse pre old) (h : new = old) :
    (resources.rebaseCursor h).ticketShadowBlocks =
      resources.ticketShadowBlocks := by
  cases h
  rfl

@[simp] private theorem ScheduleRunResources.rebaseCursor_ticketShadowOwners
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} {pre : List T}
    {old new : ScheduleCursor g input}
    (resources : ScheduleRunResources parse pre old) (h : new = old) :
    (resources.rebaseCursor h).ticketShadowOwners =
      resources.ticketShadowOwners := by
  cases h
  rfl

/-- Resource view for the left child of a binary fork.  The pending right child is classified
after the left yield interval; all inherited task owners retain their parent classification. -/
private def ScheduleRunResources.binaryLeftProtected
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A B : g.nt} {stack : List g.flag} {u v : List T}
    {parent : NFParse g A stack (u ++ v)} {leftParse : NFParse g B stack u}
    {pre : List T} {old fork : ScheduleCursor g input}
    (resources : ScheduleRunResources parent pre old)
    (rightOwner : Fin input.length)
    (hindices : fork.indexOwners = old.indexOwners)
    (htasks : fork.taskOwners.Perm (rightOwner :: old.taskOwners))
    (hrightVal : rightOwner.val = (pre ++ u).length)
    (hproductive : leftParse.productiveCount ≤ parent.productiveCount)
    (childWindow : ProductiveOwnerWindow (input := input) leftParse)
    (childLedger : ScheduleOwnerLedger leftParse childWindow fork)
    (tickets : IndexTicketLedger fork)
    (parkingAtOrBelow : tickets.ParkingAtOrBelow childWindow)
    (ticketOwnerLedger : tickets.SemanticScheduleOwnerLedger
      leftParse childWindow)
    (ticket_active_eq : ticketOwnerLedger.active =
      tickets.semanticOwners childLedger.active)
    (ticketShadowBlocks : List (List g.flag))
    (ticketShadowOwners : List (Fin (10 * input.length)))
    (ticketShadowOwners_subset : ticketShadowOwners ⊆ fork.indexOwners)
    (ticketShadowOwners_nodup : ticketShadowOwners.Nodup)
    (ticketShadowLedger : tickets.SemanticShadowOwnerLedger
      leftParse childWindow)
    (ticket_shadow_active_eq : ticketShadowLedger.active =
      tickets.semanticOwners ticketShadowOwners)
    (ticketShadowLayout : tickets.ShadowTicketLayout leftParse childWindow
      ticketShadowBlocks ticketShadowOwners) :
    ScheduleRunResources leftParse pre fork where
  pool := resources.pool.transportProtectedStructural hindices
  tickets := tickets
  window := childWindow
  parkingAtOrBelow := parkingAtOrBelow
  ownerLedger := childLedger
  ticketOwnerLedger := ticketOwnerLedger
  ticket_active_eq := ticket_active_eq
  ticketShadowBlocks := ticketShadowBlocks
  ticketShadowOwners := ticketShadowOwners
  ticketShadowOwners_subset := ticketShadowOwners_subset
  ticketShadowOwners_nodup := ticketShadowOwners_nodup
  ticketShadowLedger := ticketShadowLedger
  ticket_shadow_active_eq := ticket_shadow_active_eq
  ticketShadowLayout := ticketShadowLayout
  shadowLedger := ShadowOwnerLedger.ofGeneric
    (resources.pool.transportProtectedStructural hindices) childLedger
  shadow_active_eq := rfl
  charged := resources.charged
  charged_eq_indices := by simpa [hindices] using resources.charged_eq_indices
  charged_le_indices := by simpa [hindices] using resources.charged_le_indices
  productive_le_credit :=
    le_trans hproductive resources.productive_le_credit
  task_locality := by
    intro owner howner
    have hclass := htasks.mem_iff.mp howner
    simp only [List.mem_cons] at hclass
    rcases hclass with rfl | hold
    · right
      right
      simp only [List.length_append] at hrightVal ⊢
      omega
    · have hloc := resources.task_locality owner hold
      rcases hloc with heq | hbefore | hafter
      · exact Or.inl heq
      · exact Or.inr (Or.inl hbefore)
      · exact Or.inr (Or.inr (by
          simp only [List.length_append] at hafter ⊢
          omega))

/-- Resource view for the right child after the left task has disappeared. -/
private def ScheduleRunResources.binaryRightProtected
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    {A C : g.nt} {stack : List g.flag} {u v : List T}
    {parent : NFParse g A stack (u ++ v)} {rightParse : NFParse g C stack v}
    {pre : List T} {old fork rightCursor : ScheduleCursor g input}
    (resources : ScheduleRunResources parent pre old)
    (forkInv : ScheduleInvariant fork)
    (leftOwner rightOwner : Fin input.length)
    (hindices : rightCursor.indexOwners = old.indexOwners)
    (hforkTasks : fork.taskOwners.Perm (rightOwner :: old.taskOwners))
    (hfinishTasks : fork.taskOwners.Perm (leftOwner :: rightCursor.taskOwners))
    (hleftVal : leftOwner.val = pre.length)
    (hrightVal : rightOwner.val = (pre ++ u).length)
    (hproductive : rightParse.productiveCount ≤ parent.productiveCount)
    (childWindow : ProductiveOwnerWindow (input := input) rightParse)
    (childLedger : ScheduleOwnerLedger rightParse childWindow rightCursor)
    (tickets : IndexTicketLedger rightCursor)
    (parkingAtOrBelow : tickets.ParkingAtOrBelow childWindow)
    (ticketOwnerLedger : tickets.SemanticScheduleOwnerLedger
      rightParse childWindow)
    (ticket_active_eq : ticketOwnerLedger.active =
      tickets.semanticOwners childLedger.active)
    (ticketShadowBlocks : List (List g.flag))
    (ticketShadowOwners : List (Fin (10 * input.length)))
    (ticketShadowOwners_subset : ticketShadowOwners ⊆ rightCursor.indexOwners)
    (ticketShadowOwners_nodup : ticketShadowOwners.Nodup)
    (ticketShadowLedger : tickets.SemanticShadowOwnerLedger
      rightParse childWindow)
    (ticket_shadow_active_eq : ticketShadowLedger.active =
      tickets.semanticOwners ticketShadowOwners)
    (ticketShadowLayout : tickets.ShadowTicketLayout rightParse childWindow
      ticketShadowBlocks ticketShadowOwners) :
    ScheduleRunResources rightParse (pre ++ u) rightCursor where
  pool := resources.pool.transportProtectedStructural hindices
  tickets := tickets
  window := childWindow
  parkingAtOrBelow := parkingAtOrBelow
  ownerLedger := childLedger
  ticketOwnerLedger := ticketOwnerLedger
  ticket_active_eq := ticket_active_eq
  ticketShadowBlocks := ticketShadowBlocks
  ticketShadowOwners := ticketShadowOwners
  ticketShadowOwners_subset := ticketShadowOwners_subset
  ticketShadowOwners_nodup := ticketShadowOwners_nodup
  ticketShadowLedger := ticketShadowLedger
  ticket_shadow_active_eq := ticket_shadow_active_eq
  ticketShadowLayout := ticketShadowLayout
  shadowLedger := ShadowOwnerLedger.ofGeneric
    (resources.pool.transportProtectedStructural hindices) childLedger
  shadow_active_eq := rfl
  charged := resources.charged
  charged_eq_indices := by simpa [hindices] using resources.charged_eq_indices
  charged_le_indices := by simpa [hindices] using resources.charged_le_indices
  productive_le_credit :=
    le_trans hproductive resources.productive_le_credit
  task_locality := by
    intro owner howner
    have hconsNodup : (leftOwner :: rightCursor.taskOwners).Nodup :=
      hfinishTasks.nodup_iff.mp forkInv.taskOwners_nodup
    have hleftFresh : leftOwner ∉ rightCursor.taskOwners :=
      (List.nodup_cons.mp hconsNodup).1
    have hownerFork : owner ∈ fork.taskOwners :=
      hfinishTasks.mem_iff.mpr (List.mem_cons_of_mem leftOwner howner)
    have hclass := hforkTasks.mem_iff.mp hownerFork
    simp only [List.mem_cons] at hclass
    rcases hclass with hright | hold
    · left
      subst owner
      exact hrightVal
    · have hloc := resources.task_locality owner hold
      rcases hloc with heq | hbefore | hafter
      · have hownerEq : owner = leftOwner := by
          apply Fin.ext
          simpa [hleftVal] using heq
        exact False.elim (hleftFresh (hownerEq ▸ howner))
      · right
        left
        simp only [List.length_append]
        omega
      · right
        right
        simp only [List.length_append] at hafter ⊢
        omega

/-- Protected-mode entry with only the common non-strict parking bound.

This deliberately weaker interface is used only while sealing an overlay at a binary fork.
Both binary child windows start strictly after the parent base, so the implementation restores
`ParkingBelow` before invoking any ordinary child runner. -/
public def ProtectedScheduleRunAtOrBelow
    {g : IndexedGrammar T} [Fintype g.nt]
    {A : g.nt} {stack : List g.flag} {w : List T}
    (parse : NFParse g A stack w) : Prop :=
  ∀ {input : List T} (visible hidden : List g.flag)
    (blocks : List (List g.flag))
    (owners : List (Fin (10 * input.length)))
    (word used : List (ScheduleAtom g input))
    (hstack : stack = visible ++ hidden) (hne : visible ≠ [])
    (hall : ∀ k < visible.length, parse.ConsumesAt k)
    (hboundary : ¬ parse.ConsumesAt visible.length)
    (layout : ScheduleBlockLayout g input visible blocks owners word used)
    (compatible : EventCompatible parse blocks),
    ∀ (pre post : List T) (input_eq : input = pre ++ w ++ post)
      (alpha : List (ScheduleAtom g input))
      (hstable : StablePrefix (alpha.map ScheduleAtom.workSym))
      (hstart : ScheduleInvariant
        (liveScheduleCursor parse (by
          exact hall 0 (List.length_pos_of_ne_nil hne))
          pre post input_eq alpha word))
      (hframes : List.Disjoint owners
        (liveScheduleCursor parse (by
          exact hall 0 (List.length_pos_of_ne_nil hne))
          pre post input_eq alpha word).frameOwners)
      (hend : ScheduleInvariant (scheduleWordCursor alpha used))
      (resources : ScheduleRunResources parse pre
        (liveScheduleCursor parse (by
          exact hall 0 (List.length_pos_of_ne_nil hne))
          pre post input_eq alpha word))
      (hfree : resources.pool.free ≠ [])
      (parkingAtOrBelow : resources.tickets.ParkingAtOrBelow resources.window)
      (ownerLayout : EventOwnedLayout parse resources.window blocks owners)
      (shadowLayout : ShadowStartLayout parse resources.window blocks owners)
      (ticketOwnerLayout : resources.tickets.EventTicketLayout
        parse resources.window blocks owners)
      (ticketShadowContext : resources.TicketShadowContextExtends blocks owners)
      (ticketTransientFree : ∀ hinput : 0 < input.length,
        IndexTicket.transient hinput ∉
          (liveScheduleCursor parse (by
            exact hall 0 (List.length_pos_of_ne_nil hne))
            pre post input_eq alpha word).indexTickets
              resources.tickets.ticketOf)
      (hactive : resources.ownerLedger.active = owners)
      (transientFree : ∀ hinput : 0 < input.length,
        ProductiveOwnerWindow.transientOwner (g := g) hinput ∉
          (liveScheduleCursor parse (by
            exact hall 0 (List.length_pos_of_ne_nil hne))
            pre post input_eq alpha word).indexOwners)
      (scratchFree : ∀ hinput : 0 < input.length,
        ProductiveOwnerWindow.scratchOwner (g := g) hinput ∉
          (liveScheduleCursor parse (by
            exact hall 0 (List.length_pos_of_ne_nil hne))
            pre post input_eq alpha word).indexOwners),
      ScheduleReaches g input
        (scheduleStateOfCursor pre.length (by
          rw [input_eq]
          simp) _ hstart)
        (scheduleStateOfCursor (pre ++ w).length (by
          rw [input_eq]
          simp) _ hend)

/-- An at-or-below protected implementation is an ordinary protected implementation whenever
the caller supplies the ordinary strict bound. -/
public theorem ProtectedScheduleRunAtOrBelow.toProtectedScheduleRun
    {g : IndexedGrammar T} [Fintype g.nt]
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w}
    (run : ProtectedScheduleRunAtOrBelow parse) :
    ProtectedScheduleRun parse := by
  intro input visible hidden blocks owners word used hstack hne hall hboundary
    layout compatible pre post input_eq alpha hstable hstart hframes hend
    resources hfree parkingBelow ownerLayout shadowLayout ticketOwnerLayout
    ticketShadowContext ticketTransientFree hactive transientFree scratchFree
  exact run (input := input) visible hidden blocks owners word used hstack hne hall
    hboundary layout compatible pre post input_eq alpha hstable hstart hframes hend
    resources hfree parkingBelow.toAtOrBelow ownerLayout shadowLayout
    ticketOwnerLayout ticketShadowContext ticketTransientFree hactive transientFree
    scratchFree

/-- Split a protected binary task at the aligned maximal consumed prefixes of its children and
run the two terminal intervals in order, assuming only the parent non-strict parking bound. -/
public theorem protectedScheduleRun_binary_atOrBelow
    {g : IndexedGrammar T} [Fintype g.nt]
    {A B C : g.nt} {stack : List g.flag} {u v : List T}
    {r : IRule T g.nt g.flag}
    (hr : r ∈ g.rules) (hlhs : r.lhs = A) (hc : r.consume = none)
    (hrhs : r.rhs =
      [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none])
    (leftParse : NFParse g B stack u) (rightParse : NFParse g C stack v)
    (leftRuns : OrdinaryScheduleRuns leftParse)
    (rightRuns : OrdinaryScheduleRuns rightParse) :
    ProtectedScheduleRunAtOrBelow
      (NFParse.binary hr hlhs hc hrhs leftParse rightParse) := by
  intro input visible hidden blocks owners word used hstack hne hall hboundary
    layout compatible pre post input_eq alpha hstable hstart hframes hend
    resources hfree parkingAtOrBelow ownerLayout shadowLayout ticketOwnerLayout ticketShadowContext
    ticketTransientFree hactive transientFree scratchFree
  let parent : NFParse g A stack (u ++ v) :=
    .binary hr hlhs hc hrhs leftParse rightParse
  obtain ⟨parkedBlocks, parkedOwners, hcontextBlocks, hcontextOwners⟩ :=
    ticketShadowContext
  let n := visible.length
  have hnpos : 0 < n := List.length_pos_of_ne_nil hne
  have hboundLeft : ¬ leftParse.ConsumesAt n := fun h => hboundary (Or.inl h)
  have hboundRight : ¬ rightParse.ConsumesAt n := fun h => hboundary (Or.inr h)
  rcases IndexedGrammar.Aho.NFParse.exists_consumedPrefix leftParse n hboundLeft with
    ⟨ml, hml, hallLeft, hfirstLeft⟩
  rcases IndexedGrammar.Aho.NFParse.exists_consumedPrefix rightParse n hboundRight with
    ⟨mr, hmr, hallRight, hfirstRight⟩
  have hfull : ml = n ∨ mr = n := by
    have hdeep := hall (n - 1) (by omega)
    rcases hdeep with hdeep | hdeep
    · left
      have hlt : n - 1 < ml := by
        by_contra hnot
        exact hfirstLeft (leftParse.consumesAt_mono (Nat.le_of_not_gt hnot) hdeep)
      omega
    · right
      have hlt : n - 1 < mr := by
        by_contra hnot
        exact hfirstRight (rightParse.consumesAt_mono (Nat.le_of_not_gt hnot) hdeep)
      omega
  let leftMode : TaskMode leftParse :=
    if hzero : ml = 0 then
      .plain (by simpa [hzero] using hfirstLeft)
    else
      .live (hallLeft 0 (Nat.pos_of_ne_zero hzero))
  let rightMode : TaskMode rightParse :=
    if hzero : mr = 0 then
      .plain (by simpa [hzero] using hfirstRight)
    else
      .live (hallRight 0 (Nat.pos_of_ne_zero hzero))
  have leftInputEq : input = pre ++ u ++ (v ++ post) := by
    simpa [List.append_assoc] using input_eq
  have rightInputEq : input = (pre ++ u) ++ v ++ post := by
    simpa [List.append_assoc] using input_eq
  let parentUsed : parent.ConsumesAt 0 := hall 0 hnpos
  let parentTask : ScheduleTask g input :=
    scheduleTaskOfParse parent pre post input_eq (.live parentUsed)
  let leftTask : ScheduleTask g input :=
    scheduleTaskOfParse leftParse pre (v ++ post) leftInputEq leftMode
  let rightTask : ScheduleTask g input :=
    scheduleTaskOfParse rightParse (pre ++ u) post rightInputEq rightMode
  let startCursor : ScheduleCursor g input :=
    ⟨alpha ++ [.dollar], .task parentTask, word⟩
  let forkCursor : ScheduleCursor g input :=
    ⟨alpha ++ [.dollar], .task leftTask, .task rightTask :: word⟩
  have hstart' : ScheduleInvariant startCursor := by
    simpa [startCursor, parentTask, parent, liveScheduleCursor] using hstart
  have hleftOwner : leftTask.owner = parentTask.owner := by
    apply Fin.ext
    rfl
  have hrightFresh : rightTask.owner ∉ startCursor.taskOwners := by
    intro hmem
    have hloc := resources.task_locality rightTask.owner (by
      simpa [startCursor, parentTask, parent, liveScheduleCursor] using hmem)
    have hu := leftParse.yield_length_pos
    have hv := rightParse.yield_length_pos
    rcases hloc with heq | hlt | hafter
    · change (pre ++ u).length = pre.length at heq
      simp only [List.length_append] at heq
      omega
    · change (pre ++ u).length < pre.length at hlt
      simp only [List.length_append] at hlt
      omega
    · change pre.length + (u ++ v).length ≤ (pre ++ u).length at hafter
      simp only [List.length_append] at hafter
      omega
  have hfork : ScheduleInvariant forkCursor := by
    dsimp [forkCursor, startCursor]
    exact ScheduleInvariant.plainBinary (alpha ++ [ScheduleAtom.dollar]) word
      parentTask leftTask rightTask hleftOwner hrightFresh hstart'
  have hindicesFork : forkCursor.indexOwners = startCursor.indexOwners := by
    simp [forkCursor, startCursor, ScheduleCursor.indexOwners,
      ScheduleCursor.word, ScheduleAtom.indexOwner?, List.filterMap_append]
  let startLedger : ScheduleOwnerLedger parent resources.window startCursor := by
    simpa [startCursor, parentTask, parent, liveScheduleCursor] using
      resources.ownerLedger
  let startTickets : IndexTicketLedger startCursor := by
    simpa [startCursor, parentTask, parent, liveScheduleCursor] using
      resources.tickets
  let forkTickets : IndexTicketLedger forkCursor :=
    startTickets.transport (by rw [hindicesFork])
  have startParkingAtOrBelow :
      startTickets.ParkingAtOrBelow resources.window := by
    simpa [startTickets, startCursor, parentTask, parent, liveScheduleCursor] using
      parkingAtOrBelow
  have forkParkingAtOrBelow :
      forkTickets.ParkingAtOrBelow resources.window := by
    exact startParkingAtOrBelow.transport (by rw [hindicesFork])
  have leftParkingBelow :
      forkTickets.ParkingBelow resources.window.binaryLeft :=
    forkParkingAtOrBelow.toBelow_of_base_lt (by
      simp only [ProductiveOwnerWindow.binaryLeft_base]
      omega)
  let startTicketOwnerLedger : startTickets.SemanticScheduleOwnerLedger
      parent resources.window := by
    simpa [startTickets, startCursor, parentTask, parent, liveScheduleCursor] using
      resources.ticketOwnerLedger
  let startTicketShadowLedger : startTickets.SemanticShadowOwnerLedger
      parent resources.window := by
    simpa [startTickets, startCursor, parentTask, parent, liveScheduleCursor] using
      resources.ticketShadowLedger
  have startActive : startLedger.active = owners := by
    simpa [startLedger, startCursor, parentTask, parent, liveScheduleCursor] using
      hactive
  have startTicketActive : startTicketOwnerLedger.active =
      startTickets.semanticOwners owners := by
    have hbase : startTicketOwnerLedger.active =
        startTickets.semanticOwners startLedger.active := by
      simpa [startTicketOwnerLedger, startTickets, startLedger, startCursor,
        parentTask, parent, liveScheduleCursor] using resources.ticket_active_eq
    exact hbase.trans (congrArg startTickets.semanticOwners startActive)
  have startTicketShadowActive : startTicketShadowLedger.active =
      startTickets.semanticOwners resources.ticketShadowOwners := by
    simpa [startTicketShadowLedger, startTickets, startCursor, parentTask, parent,
      liveScheduleCursor] using resources.ticket_shadow_active_eq
  let startOwnerLayout : EventOwnedLayout parent resources.window blocks owners := by
    simpa [parent] using ownerLayout
  let startTicketOwnerLayout : startTickets.EventTicketLayout parent
      resources.window blocks owners := by
    simpa [startTickets, startCursor, parentTask, parent, liveScheduleCursor] using
      ticketOwnerLayout
  let startTicketShadowLayout : startTickets.ShadowTicketLayout parent
      resources.window resources.ticketShadowBlocks
        resources.ticketShadowOwners := by
    simpa [startTickets, startCursor, parentTask, parent, liveScheduleCursor] using
      resources.ticketShadowLayout
  have hframesFork : forkCursor.frameOwners = startCursor.frameOwners := by
    simp [forkCursor, startCursor, ScheduleCursor.frameOwners,
      ScheduleCursor.word, ScheduleAtom.closeOwner?, List.filterMap_append]
  have leftPrefixLedger : PrefixFrameLedger forkCursor :=
    startLedger.prefixLedger.transport
      (by simp [forkCursor, startCursor])
      (by rw [hframesFork])
  let leftOwnerLedger : ScheduleOwnerLedger leftParse
      resources.window.binaryLeft forkCursor :=
    startLedger.transport resources.window.binaryLeft
      (by
        simpa [forkCursor, startCursor, ScheduleAtom.indexOwner?] using
          startLedger.right_eq)
      (fun owner howner =>
        EventOwnedLayout.outside_binaryLeft resources.window
          (startLedger.outside_at owner howner))
      (by
        rw [hframesFork]
        exact startLedger.frames.binaryLeft)
      leftPrefixLedger
  let leftTicketPrefixLedger : PrefixFrameLedger forkTickets.semanticCursor :=
    startTicketOwnerLedger.prefixLedger.transport
      (by
        change
          ((forkCursor.left.map (ScheduleAtom.relabelTicketOwner
              forkTickets.semanticOwnerOf)).filterMap ScheduleAtom.indexOwner?).Perm
            ((startCursor.left.map (ScheduleAtom.relabelTicketOwner
              startTickets.semanticOwnerOf)).filterMap ScheduleAtom.indexOwner?)
        rw [ScheduleAtom.filterMap_indexOwner_relabelTicketOwner,
          ScheduleAtom.filterMap_indexOwner_relabelTicketOwner]
        have hfun : forkTickets.semanticOwnerOf =
            startTickets.semanticOwnerOf := by
          funext owner
          rfl
        rw [hfun])
      (by
        rw [forkTickets.semanticCursor_frameOwners,
          startTickets.semanticCursor_frameOwners]
        have hfun : forkTickets.semanticOwnerOf =
            startTickets.semanticOwnerOf := by
          funext owner
          rfl
        rw [hfun, hframesFork])
  let leftTicketOwnerLedger : forkTickets.SemanticScheduleOwnerLedger
      leftParse resources.window.binaryLeft :=
    startTicketOwnerLedger.transport resources.window.binaryLeft
      (by
        have hright := startTicketOwnerLedger.right_eq
        rw [startTickets.semanticCursor_right_indexOwners] at hright
        rw [forkTickets.semanticCursor_right_indexOwners]
        have hfun : forkTickets.semanticOwnerOf =
            startTickets.semanticOwnerOf := by
          funext owner
          rfl
        simpa [forkCursor, startCursor, hfun] using hright)
      (fun owner howner =>
        EventOwnedLayout.outside_binaryLeft resources.window
          (startTicketOwnerLedger.outside_at owner howner))
      (by
        simpa [forkTickets, startTickets, forkCursor, startCursor] using
          startTicketOwnerLedger.frames.binaryLeft)
      leftTicketPrefixLedger
  let leftTicketShadowLedger : forkTickets.SemanticShadowOwnerLedger
      leftParse resources.window.binaryLeft :=
    startTicketShadowLedger.transport resources.window.binaryLeft
      (by
        have hright := startTicketShadowLedger.right_eq
        rw [startTickets.semanticCursor_right_indexOwners] at hright
        rw [forkTickets.semanticCursor_right_indexOwners]
        have hfun : forkTickets.semanticOwnerOf =
            startTickets.semanticOwnerOf := by
          funext owner
          rfl
        simpa [forkCursor, startCursor, hfun] using hright)
      (fun owner howner => OutsideShadowWindow.binaryLeft resources.window
        (startTicketShadowLedger.outside_at owner howner))
      (by
        simpa [forkTickets, startTickets, forkCursor, startCursor] using
          startTicketShadowLedger.frames.binaryLeft)
      leftTicketPrefixLedger
  have transientFreeStart : ∀ hinput : 0 < input.length,
      ProductiveOwnerWindow.transientOwner (g := g) hinput ∉
        startCursor.indexOwners := by
    intro hinput
    simpa [startCursor, parentTask, parent, liveScheduleCursor] using
      transientFree hinput
  have scratchFreeStart : ∀ hinput : 0 < input.length,
      ProductiveOwnerWindow.scratchOwner (g := g) hinput ∉
        startCursor.indexOwners := by
    intro hinput
    simpa [startCursor, parentTask, parent, liveScheduleCursor] using
      scratchFree hinput
  have ticketTransientFreeStart : ∀ hinput : 0 < input.length,
      IndexTicket.transient hinput ∉
        startCursor.indexTickets startTickets.ticketOf := by
    intro hinput
    simpa [startTickets, startCursor, parentTask, parent, liveScheduleCursor] using
      ticketTransientFree hinput
  have transientFreeFork : ∀ hinput : 0 < input.length,
      ProductiveOwnerWindow.transientOwner (g := g) hinput ∉
        forkCursor.indexOwners := by
    intro hinput
    rw [hindicesFork]
    exact transientFreeStart hinput
  have scratchFreeFork : ∀ hinput : 0 < input.length,
      ProductiveOwnerWindow.scratchOwner (g := g) hinput ∉
        forkCursor.indexOwners := by
    intro hinput
    rw [hindicesFork]
    exact scratchFreeStart hinput
  have ticketTransientFreeFork : ∀ hinput : 0 < input.length,
      IndexTicket.transient hinput ∉
        forkCursor.indexTickets forkTickets.ticketOf := by
    intro hinput
    simpa [forkTickets, startTickets, ScheduleCursor.indexTickets,
      hindicesFork] using ticketTransientFreeStart hinput
  have htaskPerm : forkCursor.taskOwners.Perm
      (rightTask.owner :: startCursor.taskOwners) := by
    simp only [forkCursor, startCursor, ScheduleCursor.taskOwners_mk,
      ScheduleAtom.taskOwner?, List.filterMap_cons, List.filterMap_nil]
    rw [hleftOwner]
    simpa only [List.append_assoc] using
      (List.perm_middle
        (l₁ := (alpha ++ [ScheduleAtom.dollar]).filterMap
          ScheduleAtom.taskOwner? ++ [parentTask.owner])
        (l₂ := word.filterMap ScheduleAtom.taskOwner?)
        (a := rightTask.owner))
  have hleftProductive : leftParse.productiveCount ≤ parent.productiveCount := by
    simp [parent, NFParse.productiveCount, NFParse.binaryCount,
      NFParse.terminalCount]
    omega
  have hrightProductive : rightParse.productiveCount ≤ parent.productiveCount := by
    simp [parent, NFParse.productiveCount, NFParse.binaryCount,
      NFParse.terminalCount]
    omega
  have leftOwnerActive : leftOwnerLedger.active = owners := by
    simpa [leftOwnerLedger] using startActive
  have leftTicketActiveEq : leftTicketOwnerLedger.active =
      forkTickets.semanticOwners leftOwnerLedger.active := by
    change startTicketOwnerLedger.active =
      forkTickets.semanticOwners startLedger.active
    have hbase := startTicketActive
    rw [← startActive] at hbase
    simpa [forkTickets, startTickets, IndexTicketLedger.transport,
      IndexTicketLedger.semanticOwners, IndexTicketLedger.semanticOwnerOf] using hbase
  have leftTicketShadowActiveEq : leftTicketShadowLedger.active =
      forkTickets.semanticOwners resources.ticketShadowOwners := by
    change startTicketShadowLedger.active =
      forkTickets.semanticOwners resources.ticketShadowOwners
    have hbase := startTicketShadowActive
    simpa [forkTickets, startTickets, IndexTicketLedger.transport,
      IndexTicketLedger.semanticOwners, IndexTicketLedger.semanticOwnerOf] using hbase
  let leftTicketOwnerLayout : forkTickets.EventTicketLayout leftParse
      resources.window.binaryLeft blocks owners := by
    simpa [forkTickets, startTickets] using startTicketOwnerLayout.binaryLeft
  let leftTicketShadowLayout : forkTickets.ShadowTicketLayout leftParse
      resources.window.binaryLeft resources.ticketShadowBlocks
        resources.ticketShadowOwners := by
    simpa [forkTickets, startTickets] using startTicketShadowLayout.binaryLeft
  have leftTicketShadowOwnersSubset : resources.ticketShadowOwners ⊆
      forkCursor.indexOwners := by
    intro owner howner
    rw [hindicesFork]
    simpa [startCursor, parentTask, parent, liveScheduleCursor] using
      resources.ticketShadowOwners_subset howner
  let leftResources : ScheduleRunResources leftParse pre forkCursor :=
    resources.binaryLeftProtected rightTask.owner hindicesFork htaskPerm rfl
      hleftProductive resources.window.binaryLeft leftOwnerLedger forkTickets
      leftParkingBelow.toAtOrBelow leftTicketOwnerLedger leftTicketActiveEq
      resources.ticketShadowBlocks
      resources.ticketShadowOwners leftTicketShadowOwnersSubset
      resources.ticketShadowOwners_nodup leftTicketShadowLedger
      leftTicketShadowActiveEq leftTicketShadowLayout
  have leftResourcesTickets : leftResources.tickets = forkTickets := rfl
  have leftResourcesWindow : leftResources.window =
      resources.window.binaryLeft := rfl
  have hword : word ≠ [] := layout.input_ne_nil_of_flags_ne hne
  have hused : used ≠ [] := layout.output_ne_nil_of_flags_ne hne
  have hpos : pre.length ≤ input.length := by
    rw [input_eq]
    simp
  let startState : ScheduleState g input :=
    scheduleStateOfCursor pre.length hpos startCursor hstart'
  let forkState : ScheduleState g input :=
    scheduleStateOfCursor pre.length hpos forkCursor hfork
  have hs : markProductivePrefix (alpha.map ScheduleAtom.workSym) =
      alpha.map ScheduleAtom.workSym := hstable
  have hforkStep : ScheduleReaches g input startState forkState := by
    obtain ⟨next, tail, hwordEq⟩ := List.exists_cons_of_ne_nil hword
    subst word
    apply ScheduleReaches.single
    by_cases hml0 : ml = 0
    · by_cases hmr0 : mr = 0
      · have hp0 := hall 0 hnpos
        exact False.elim (hp0.elim
          (fun hp => hfirstLeft (by simpa [hml0] using hp))
          (fun hp => hfirstRight (by simpa [hmr0] using hp)))
      · have hstep := composite_liveBinaryRight_at input
          (binaryRule_aug ⟨r, hr, hlhs, hc, hrhs⟩) pre.length
          (alpha.map ScheduleAtom.workSym) next.workSym
          (tail.map ScheduleAtom.workSym)
        simpa [startState, forkState, scheduleStateOfCursor,
          ScheduleState.config, startCursor, forkCursor, parentTask, leftTask,
          rightTask, parent, leftMode, rightMode, hml0, hmr0,
          scheduleTaskOfParse, ScheduleCursor.erase, ScheduleAtom.workSym,
          ScheduleTask.workSym, List.map_append, hs] using hstep
    · by_cases hmr0 : mr = 0
      · have hstep := composite_liveBinaryLeft_at input
          (binaryRule_aug ⟨r, hr, hlhs, hc, hrhs⟩) pre.length
          (alpha.map ScheduleAtom.workSym) next.workSym
          (tail.map ScheduleAtom.workSym)
        simpa [startState, forkState, scheduleStateOfCursor,
          ScheduleState.config, startCursor, forkCursor, parentTask, leftTask,
          rightTask, parent, leftMode, rightMode, hml0, hmr0,
          scheduleTaskOfParse, ScheduleCursor.erase, ScheduleAtom.workSym,
          ScheduleTask.workSym, List.map_append, hs] using hstep
      · have hstep := composite_liveBinaryBoth_at input
          (binaryRule_aug ⟨r, hr, hlhs, hc, hrhs⟩) pre.length
          (alpha.map ScheduleAtom.workSym) next.workSym
          (tail.map ScheduleAtom.workSym)
        simpa [startState, forkState, scheduleStateOfCursor,
          ScheduleState.config, startCursor, forkCursor, parentTask, leftTask,
          rightTask, parent, leftMode, rightMode, hml0, hmr0,
          scheduleTaskOfParse, ScheduleCursor.erase, ScheduleAtom.workSym,
          ScheduleTask.workSym, List.map_append, hs] using hstep
  by_cases hleftFull : ml = n
  · have hml0 : ml ≠ 0 := by omega
    have leftUsed : leftParse.ConsumesAt 0 := hallLeft 0 (Nat.pos_of_ne_zero hml0)
    have leftCompatible : EventCompatible leftParse blocks :=
      EventCompatible.binaryLeft compatible
    have leftLayout : ScheduleBlockLayout g input visible blocks owners
        (.task rightTask :: word) (.task rightTask :: used) := by
      simpa using layout.prepend [.task rightTask]
        (by simp [ScheduleIndexFree]) (by simp [ScheduleDollarFree])
    have hforkMarked : ScheduleInvariant
        ⟨alpha ++ [.dollar], .task leftTask, .task rightTask :: used⟩ := by
      exact ScheduleInvariant.replaceRight (alpha ++ [ScheduleAtom.dollar])
        (.task leftTask) leftLayout hfork
    let rightCursor : ScheduleCursor g input :=
      ⟨alpha ++ [.dollar], .task rightTask, used⟩
    have hrightInv : ScheduleInvariant rightCursor := by
      dsimp [rightCursor]
      exact ScheduleInvariant.finishTask (alpha ++ [ScheduleAtom.dollar]) leftTask
        (.task rightTask) used hforkMarked
    have hleftFrames : List.Disjoint owners
        (liveScheduleCursor leftParse leftUsed pre (v ++ post) leftInputEq alpha
          (.task rightTask :: word)).frameOwners := by
      simpa [liveScheduleCursor, forkCursor, leftTask, leftMode, hml0,
        ScheduleCursor.frameOwners, ScheduleCursor.word,
        ScheduleAtom.closeOwner?, List.filterMap_append] using hframes
    have hleftCursorEq :
        liveScheduleCursor leftParse leftUsed pre (v ++ post) leftInputEq alpha
          (.task rightTask :: word) = forkCursor := by
      simp [liveScheduleCursor, forkCursor, leftTask, leftMode, hml0]
    let leftResources' : ScheduleRunResources leftParse pre
        (liveScheduleCursor leftParse leftUsed pre (v ++ post) leftInputEq alpha
          (.task rightTask :: word)) :=
      leftResources.rebaseCursor hleftCursorEq
    have hleftRun := leftRuns.2 (input := input) visible hidden blocks owners
      (.task rightTask :: word) (.task rightTask :: used) hstack hne
      (by simpa [hleftFull, n] using hallLeft)
      (by simpa [hleftFull, n] using hfirstLeft) leftLayout leftCompatible
      pre (v ++ post) leftInputEq alpha hstable
      (by simpa [forkCursor, leftTask, leftMode, hml0, liveScheduleCursor] using hfork)
      hleftFrames hrightInv leftResources' (by
        simpa [leftResources', leftResources,
          ScheduleRunResources.binaryLeftProtected,
          IndexOwnerPool.transportProtectedStructural] using hfree)
      (by
        exact ScheduleRunResources.rebaseCursor_parkingBelow leftResources
          hleftCursorEq (by
            simpa [leftResources,
              ScheduleRunResources.binaryLeftProtected] using leftParkingBelow))
      (by
        simpa [leftResources', leftResources,
          ScheduleRunResources.binaryLeftProtected] using
            startOwnerLayout.binaryLeft)
      (leftResources'.genericShadowStartLayout (by
          simpa [leftResources', leftResources,
            ScheduleRunResources.binaryLeftProtected, leftOwnerLedger] using
              startActive)
        (by simpa using (startOwnerLayout.binaryLeft).owners_length)
        shadowLayout.block_nonempty)
      (by
        change EventOwnedLayout leftParse
          (leftResources.rebaseCursor hleftCursorEq).window blocks
          ((leftResources.rebaseCursor hleftCursorEq).tickets.semanticOwners owners)
        rw [ScheduleRunResources.rebaseCursor_window,
          ScheduleRunResources.rebaseCursor_semanticOwners,
          leftResourcesWindow, leftResourcesTickets]
        exact leftTicketOwnerLayout)
      (by
        refine ⟨parkedBlocks, parkedOwners, ?_, ?_⟩
        · simpa [leftResources', leftResources,
            ScheduleRunResources.binaryLeftProtected] using hcontextBlocks
        · simpa [leftResources', leftResources,
            ScheduleRunResources.binaryLeftProtected] using hcontextOwners)
      (by
        intro hinput
        have h := ticketTransientFreeFork hinput
        change IndexTicket.transient hinput ∉
          (liveScheduleCursor leftParse leftUsed pre (v ++ post) leftInputEq alpha
            (.task rightTask :: word)).indexTickets
              (leftResources.rebaseCursor hleftCursorEq).tickets.ticketOf
        rw [ScheduleRunResources.rebaseCursor_ticketOf,
          leftResourcesTickets, ScheduleCursor.indexTickets, hleftCursorEq]
        exact h)
      (by
        simpa [leftResources', leftResources,
          ScheduleRunResources.binaryLeftProtected, leftOwnerLedger] using
            startActive)
      (by
        intro hinput
        have h := transientFreeFork hinput
        simpa [hleftCursorEq] using h)
      (by
        intro hinput
        have h := scratchFreeFork hinput
        simpa [hleftCursorEq] using h)
    have hleftRun' : ScheduleReaches g input forkState
        (scheduleStateOfCursor (pre ++ u).length (by
          rw [input_eq]
          simp) rightCursor hrightInv) := by
      simpa [forkState, forkCursor, rightCursor, scheduleStateOfCursor,
        liveScheduleCursor, leftTask, leftMode, hml0] using hleftRun
    have hindicesRight : rightCursor.indexOwners = startCursor.indexOwners := by
      simp only [rightCursor, startCursor, ScheduleCursor.indexOwners_mk,
        ScheduleAtom.indexOwner?, List.filterMap_cons, List.filterMap_nil,
        List.append_nil]
      exact congrArg ((alpha ++ [ScheduleAtom.dollar]).filterMap
        ScheduleAtom.indexOwner? ++ ·) layout.indexOwners_eq.symm
    have hfinishPerm : forkCursor.taskOwners.Perm
        (leftTask.owner :: rightCursor.taskOwners) := by
      simp only [forkCursor, rightCursor, ScheduleCursor.taskOwners_mk,
        ScheduleAtom.taskOwner?, List.filterMap_cons, List.filterMap_nil]
      rw [layout.taskOwners_eq]
      simpa only [List.append_assoc] using
        (List.perm_middle
          (l₁ := (alpha ++ [ScheduleAtom.dollar]).filterMap
            ScheduleAtom.taskOwner?)
          (l₂ := rightTask.owner :: used.filterMap ScheduleAtom.taskOwner?)
          (a := leftTask.owner))
    have hframesRight : rightCursor.frameOwners = startCursor.frameOwners := by
      simp only [rightCursor, startCursor, ScheduleCursor.frameOwners_mk,
        ScheduleAtom.closeOwner?, List.filterMap_cons, List.filterMap_nil,
        List.append_nil]
      exact congrArg ((alpha ++ [ScheduleAtom.dollar]).filterMap
        ScheduleAtom.closeOwner? ++ ·) layout.frameOwners_eq.symm
    have rightPrefixLedger : PrefixFrameLedger rightCursor :=
      startLedger.prefixLedger.transport
        (by simp [rightCursor, startCursor])
        (by rw [hframesRight])
    let rightFullLedger : ScheduleOwnerLedger rightParse
        resources.window.binaryRight rightCursor :=
      startLedger.transport resources.window.binaryRight
        (by
          calc
            rightCursor.right.filterMap ScheduleAtom.indexOwner? =
                startCursor.right.filterMap ScheduleAtom.indexOwner? := by
              simpa [rightCursor, startCursor] using layout.indexOwners_eq.symm
            _ = startLedger.active ++ startLedger.outside :=
              startLedger.right_eq)
        (fun owner howner =>
          EventOwnedLayout.outside_binaryRight resources.window
            (startLedger.outside_at owner howner))
        (by
          rw [hframesRight]
          exact startLedger.frames.binaryRight)
        rightPrefixLedger
    have rightFullActive : rightFullLedger.active = owners := by
      simpa [rightFullLedger] using startActive
    let rightFullLayout : EventOwnedLayout rightParse
        resources.window.binaryRight blocks owners :=
      startOwnerLayout.binaryRight
    let rightTickets : IndexTicketLedger rightCursor :=
      startTickets.transport (by rw [hindicesRight])
    have rightParkingBelow :
        rightTickets.ParkingBelow resources.window.binaryRight := by
      dsimp [rightTickets]
      exact startParkingAtOrBelow.transport_toBelow_of_base_lt
        (by rw [hindicesRight]) (by
          simp only [ProductiveOwnerWindow.binaryRight_base]
          omega)
    let rightTicketPrefixLedger : PrefixFrameLedger rightTickets.semanticCursor :=
      startTicketOwnerLedger.prefixLedger.transport
        (by
          change
            ((rightCursor.left.map (ScheduleAtom.relabelTicketOwner
                rightTickets.semanticOwnerOf)).filterMap
                ScheduleAtom.indexOwner?).Perm
              ((startCursor.left.map (ScheduleAtom.relabelTicketOwner
                startTickets.semanticOwnerOf)).filterMap ScheduleAtom.indexOwner?)
          rw [ScheduleAtom.filterMap_indexOwner_relabelTicketOwner,
            ScheduleAtom.filterMap_indexOwner_relabelTicketOwner]
          have hfun : rightTickets.semanticOwnerOf =
              startTickets.semanticOwnerOf := by
            funext owner
            rfl
          rw [hfun])
        (by
          rw [rightTickets.semanticCursor_frameOwners,
            startTickets.semanticCursor_frameOwners]
          have hfun : rightTickets.semanticOwnerOf =
              startTickets.semanticOwnerOf := by
            funext owner
            rfl
          rw [hfun, hframesRight])
    let rightFullTicketLedger : rightTickets.SemanticScheduleOwnerLedger
        rightParse resources.window.binaryRight :=
      startTicketOwnerLedger.transport resources.window.binaryRight
        (by
          have hright := startTicketOwnerLedger.right_eq
          rw [startTickets.semanticCursor_right_indexOwners] at hright
          rw [rightTickets.semanticCursor_right_indexOwners]
          have hfun : rightTickets.semanticOwnerOf =
              startTickets.semanticOwnerOf := by
            funext owner
            rfl
          have hfilter : rightCursor.right.filterMap ScheduleAtom.indexOwner? =
              startCursor.right.filterMap ScheduleAtom.indexOwner? := by
            simpa [rightCursor, startCursor] using layout.indexOwners_eq.symm
          rw [hfun, hfilter]
          exact hright)
        (fun owner howner => EventOwnedLayout.outside_binaryRight
          resources.window (startTicketOwnerLedger.outside_at owner howner))
        (by
          have hframes := startTicketOwnerLedger.frames.binaryRight
          rw [startTickets.semanticCursor_frameOwners] at hframes
          rw [rightTickets.semanticCursor_frameOwners]
          have hfun : rightTickets.semanticOwnerOf =
              startTickets.semanticOwnerOf := by
            funext owner
            rfl
          simpa [hfun, hframesRight] using hframes)
        rightTicketPrefixLedger
    let rightFullTicketShadowLedger : rightTickets.SemanticShadowOwnerLedger
        rightParse resources.window.binaryRight :=
      startTicketShadowLedger.transport resources.window.binaryRight
        (by
          have hright := startTicketShadowLedger.right_eq
          rw [startTickets.semanticCursor_right_indexOwners] at hright
          rw [rightTickets.semanticCursor_right_indexOwners]
          have hfun : rightTickets.semanticOwnerOf =
              startTickets.semanticOwnerOf := by
            funext owner
            rfl
          have hfilter : rightCursor.right.filterMap ScheduleAtom.indexOwner? =
              startCursor.right.filterMap ScheduleAtom.indexOwner? := by
            simpa [rightCursor, startCursor] using layout.indexOwners_eq.symm
          rw [hfun, hfilter]
          exact hright)
        (fun owner howner => OutsideShadowWindow.binaryRight resources.window
          (startTicketShadowLedger.outside_at owner howner))
        (by
          have hframes := startTicketShadowLedger.frames.binaryRight
          rw [startTickets.semanticCursor_frameOwners] at hframes
          rw [rightTickets.semanticCursor_frameOwners]
          have hfun : rightTickets.semanticOwnerOf =
              startTickets.semanticOwnerOf := by
            funext owner
            rfl
          simpa [hfun, hframesRight] using hframes)
        rightTicketPrefixLedger
    have rightFullTicketActive : rightFullTicketLedger.active =
        rightTickets.semanticOwners rightFullLedger.active := by
      change startTicketOwnerLedger.active =
        rightTickets.semanticOwners startLedger.active
      have hbase := startTicketActive
      rw [← startActive] at hbase
      simpa [rightTickets, startTickets, IndexTicketLedger.transport,
        IndexTicketLedger.semanticOwners, IndexTicketLedger.semanticOwnerOf] using hbase
    have rightFullTicketShadowActive : rightFullTicketShadowLedger.active =
        rightTickets.semanticOwners resources.ticketShadowOwners := by
      change startTicketShadowLedger.active =
        rightTickets.semanticOwners resources.ticketShadowOwners
      have hbase := startTicketShadowActive
      simpa [rightTickets, startTickets, IndexTicketLedger.transport,
        IndexTicketLedger.semanticOwners, IndexTicketLedger.semanticOwnerOf] using hbase
    let rightFullTicketLayout : rightTickets.EventTicketLayout rightParse
        resources.window.binaryRight blocks owners := by
      simpa [rightTickets, startTickets] using startTicketOwnerLayout.binaryRight
    let rightFullTicketShadowLayout : rightTickets.ShadowTicketLayout rightParse
        resources.window.binaryRight resources.ticketShadowBlocks
          resources.ticketShadowOwners := by
      simpa [rightTickets, startTickets] using startTicketShadowLayout.binaryRight
    have rightTicketShadowOwnersSubset : resources.ticketShadowOwners ⊆
        rightCursor.indexOwners := by
      intro owner howner
      rw [hindicesRight]
      simpa [startCursor, parentTask, parent, liveScheduleCursor] using
        resources.ticketShadowOwners_subset howner
    have transientFreeRight : ∀ hinput : 0 < input.length,
        ProductiveOwnerWindow.transientOwner (g := g) hinput ∉
          rightCursor.indexOwners := by
      intro hinput
      rw [hindicesRight]
      exact transientFreeStart hinput
    have scratchFreeRight : ∀ hinput : 0 < input.length,
        ProductiveOwnerWindow.scratchOwner (g := g) hinput ∉
          rightCursor.indexOwners := by
      intro hinput
      rw [hindicesRight]
      exact scratchFreeStart hinput
    have ticketTransientFreeRight : ∀ hinput : 0 < input.length,
        IndexTicket.transient hinput ∉
          rightCursor.indexTickets rightTickets.ticketOf := by
      intro hinput
      simpa [rightTickets, startTickets, ScheduleCursor.indexTickets,
        hindicesRight] using ticketTransientFreeStart hinput
    by_cases hmr0 : mr = 0
    · have rightUnused : ¬ rightParse.ConsumesAt 0 := by
        simpa [hmr0] using hfirstRight
      have hblocksNonempty : ∀ block ∈ blocks, block ≠ [] :=
        layout.erase.blocks_nonempty
      let rightLedger : ScheduleOwnerLedger rightParse
          resources.window.binaryRight rightCursor :=
        rightFullLedger.restrictAtMaximalBoundary rightFullActive
          rightFullLayout hblocksNonempty (BlockLayout.Boundary.start blocks)
          rightUnused
      have rightActive : rightLedger.active = [] := by
        change owners.take (BlockLayout.Boundary.start blocks).blockCount = []
        rfl
      let rightTicketLedger : rightTickets.SemanticScheduleOwnerLedger rightParse
          resources.window.binaryRight :=
        rightFullTicketLedger.restrictAtMaximalBoundary rightFullTicketActive
          (by rw [rightFullActive]; exact rightFullTicketLayout)
          hblocksNonempty (BlockLayout.Boundary.start blocks)
          rightUnused
      have rightTicketActive : rightTicketLedger.active =
          rightTickets.semanticOwners rightLedger.active := by
        change (rightTickets.semanticOwners rightFullLedger.active).take 0 =
          rightTickets.semanticOwners (owners.take 0)
        rw [rightFullActive]
        simp [IndexTicketLedger.semanticOwners]
      let rightResources : ScheduleRunResources rightParse (pre ++ u) rightCursor :=
        resources.binaryRightProtected hfork leftTask.owner rightTask.owner
          hindicesRight htaskPerm hfinishPerm rfl rfl hrightProductive
          resources.window.binaryRight rightLedger rightTickets
          rightParkingBelow.toAtOrBelow rightTicketLedger
          rightTicketActive resources.ticketShadowBlocks
          resources.ticketShadowOwners rightTicketShadowOwnersSubset
          resources.ticketShadowOwners_nodup rightFullTicketShadowLedger
          rightFullTicketShadowActive rightFullTicketShadowLayout
      have rightResourcesTickets : rightResources.tickets = rightTickets := rfl
      obtain ⟨next, tail, husedEq⟩ := List.exists_cons_of_ne_nil hused
      subst used
      have hrightCursorEq :
          plainScheduleCursor rightParse rightUnused (pre ++ u) post rightInputEq
            alpha next tail = rightCursor := by
        simp [plainScheduleCursor, rightCursor, rightTask, rightMode, hmr0]
      let rightResources' : ScheduleRunResources rightParse (pre ++ u)
          (plainScheduleCursor rightParse rightUnused (pre ++ u) post rightInputEq
            alpha next tail) := rightResources.rebaseCursor hrightCursorEq
      have hrightRun := rightRuns.1 (input := input) rightUnused (pre ++ u) post
        rightInputEq alpha next tail hstable
        (by simpa [rightCursor, rightTask, rightMode, hmr0,
          plainScheduleCursor] using hrightInv)
        hend rightResources' (by
          simpa [rightResources', rightResources,
            ScheduleRunResources.binaryRightProtected,
            IndexOwnerPool.transportProtectedStructural] using hfree)
        (by
          exact ScheduleRunResources.rebaseCursor_parkingBelow rightResources
            hrightCursorEq (by
              simpa [rightResources,
                ScheduleRunResources.binaryRightProtected] using rightParkingBelow))
        (by
          simpa [rightResources', rightResources,
            ScheduleRunResources.binaryRightProtected] using rightActive)
        (rightResources'.genericShadowStartLayout (by
            simpa [rightResources', rightResources,
              ScheduleRunResources.binaryRightProtected] using rightActive)
          (by simp)
          (by simp))
        (by
          intro hinput
          have h := ticketTransientFreeRight hinput
          change IndexTicket.transient hinput ∉
            (plainScheduleCursor rightParse rightUnused (pre ++ u) post rightInputEq
              alpha next tail).indexTickets
                (rightResources.rebaseCursor hrightCursorEq).tickets.ticketOf
          rw [ScheduleRunResources.rebaseCursor_ticketOf, rightResourcesTickets,
            ScheduleCursor.indexTickets, hrightCursorEq]
          exact h)
        (by
          intro hinput
          have h := transientFreeRight hinput
          simpa [hrightCursorEq] using h)
        (by
          intro hinput
          have h := scratchFreeRight hinput
          simpa [hrightCursorEq] using h)
      have hrightRun' : ScheduleReaches g input
          (scheduleStateOfCursor (pre ++ u).length (by
            rw [input_eq]
            simp) rightCursor hrightInv)
          (scheduleStateOfCursor ((pre ++ u) ++ v).length (by
            rw [input_eq]
            simp) (scheduleWordCursor alpha (next :: tail)) hend) := by
        simpa [rightCursor, rightTask, rightMode, hmr0,
          plainScheduleCursor, scheduleStateOfCursor] using hrightRun
      simpa [startState, rightCursor, rightTask, rightMode, hmr0,
        liveScheduleCursor, scheduleStateOfCursor, List.append_assoc] using
        hforkStep.trans (hleftRun'.trans hrightRun')
    · have hmrPos : 0 < mr := Nat.pos_of_ne_zero hmr0
      have hmrEvent : mr ∈ rightParse.eventDepths :=
        IndexedGrammar.Aho.NFParse.maximalConsumedPrefixMemEventDepthsCurrent
          rightParse hmrPos hallRight hfirstRight
      let cut : BlockLayout.Boundary blocks mr :=
        (EventCompatible.binaryRight compatible).boundary mr hmrEvent
      have hblocksNonempty : ∀ block ∈ blocks, block ≠ [] :=
        layout.erase.blocks_nonempty
      have htake : visible.take mr = (blocks.take cut.blockCount).flatten := by
        calc
          visible.take mr =
              visible.take (blocks.take cut.blockCount).flatten.length := by
                exact congrArg (List.take · visible) cut.flagCount_eq
          _ = (blocks.take cut.blockCount).flatten :=
            layout.erase.take_flatten_take cut.blockCount
      have rightLayout : ScheduleBlockLayout g input (visible.take mr)
          (blocks.take cut.blockCount) (owners.take cut.blockCount) used used := by
        simpa only [htake] using
          ScheduleBlockLayout.idempotentTakeCurrent cut.blockCount layout
      have rightCompatible : EventCompatible rightParse
          (blocks.take cut.blockCount) :=
        EventCompatible.takeAtConsumedBoundaryCurrent hblocksNonempty
          (EventCompatible.binaryRight compatible) cut hfirstRight
      let rightLedger : ScheduleOwnerLedger rightParse
          resources.window.binaryRight rightCursor :=
        rightFullLedger.restrictAtMaximalBoundary rightFullActive
          rightFullLayout hblocksNonempty cut hfirstRight
      have rightActive : rightLedger.active = owners.take cut.blockCount := by
        rfl
      let rightOwnerLayout : EventOwnedLayout rightParse
          resources.window.binaryRight (blocks.take cut.blockCount)
            (owners.take cut.blockCount) :=
        rightFullLayout.take cut.blockCount rightCompatible
      let rightTicketLedger : rightTickets.SemanticScheduleOwnerLedger rightParse
          resources.window.binaryRight :=
        rightFullTicketLedger.restrictAtMaximalBoundary rightFullTicketActive
          (by rw [rightFullActive]; exact rightFullTicketLayout)
          hblocksNonempty cut hfirstRight
      have rightTicketActive : rightTicketLedger.active =
          rightTickets.semanticOwners rightLedger.active := by
        change (rightTickets.semanticOwners rightFullLedger.active).take cut.blockCount =
          rightTickets.semanticOwners (owners.take cut.blockCount)
        rw [rightFullActive]
        simp [IndexTicketLedger.semanticOwners, List.map_take]
      let rightTicketOwnerLayout : rightTickets.EventTicketLayout rightParse
          resources.window.binaryRight (blocks.take cut.blockCount)
            (owners.take cut.blockCount) := by
        change EventOwnedLayout rightParse resources.window.binaryRight
          (blocks.take cut.blockCount)
          (List.map rightTickets.semanticOwnerOf (owners.take cut.blockCount))
        rw [List.map_take]
        exact rightFullTicketLayout.take cut.blockCount rightCompatible
      let rightResources : ScheduleRunResources rightParse (pre ++ u) rightCursor :=
        resources.binaryRightProtected hfork leftTask.owner rightTask.owner
          hindicesRight htaskPerm hfinishPerm rfl rfl hrightProductive
          resources.window.binaryRight rightLedger rightTickets
          rightParkingBelow.toAtOrBelow rightTicketLedger
          rightTicketActive resources.ticketShadowBlocks
          resources.ticketShadowOwners rightTicketShadowOwnersSubset
          resources.ticketShadowOwners_nodup rightFullTicketShadowLedger
          rightFullTicketShadowActive rightFullTicketShadowLayout
      have rightResourcesTickets : rightResources.tickets = rightTickets := rfl
      have rightResourcesWindow : rightResources.window =
          resources.window.binaryRight := rfl
      have hrightStack : stack = visible.take mr ++
          (visible.drop mr ++ hidden) := by
        calc
          stack = visible ++ hidden := hstack
          _ = visible.take mr ++ (visible.drop mr ++ hidden) := by
            rw [← List.append_assoc, List.take_append_drop]
      have hrightVisible : visible.take mr ≠ [] := by
        apply List.ne_nil_of_length_pos
        have hmr' : mr ≤ visible.length := by simpa [n] using hmr
        rw [List.length_take, Nat.min_eq_left hmr']
        exact hmrPos
      have hrightFrames : List.Disjoint (owners.take cut.blockCount)
          (liveScheduleCursor rightParse (hallRight 0 hmrPos) (pre ++ u) post
            rightInputEq alpha used).frameOwners := by
        apply List.disjoint_left.mpr
        intro owner howner hframe
        apply (List.disjoint_left.mp hframes) (List.mem_of_mem_take howner)
        have heq :
            (liveScheduleCursor rightParse (hallRight 0 hmrPos) (pre ++ u) post
              rightInputEq alpha used).frameOwners = startCursor.frameOwners := by
          simp only [liveScheduleCursor, startCursor, ScheduleCursor.frameOwners_mk,
            ScheduleAtom.closeOwner?, List.filterMap_cons, List.filterMap_nil,
            List.append_nil]
          exact congrArg ((alpha ++ [ScheduleAtom.dollar]).filterMap
            ScheduleAtom.closeOwner? ++ ·) layout.frameOwners_eq.symm
        exact heq ▸ hframe
      have hrightCursorEq :
          liveScheduleCursor rightParse (hallRight 0 hmrPos) (pre ++ u) post
            rightInputEq alpha used = rightCursor := by
        simp [liveScheduleCursor, rightCursor, rightTask, rightMode, hmr0]
      let rightResources' : ScheduleRunResources rightParse (pre ++ u)
          (liveScheduleCursor rightParse (hallRight 0 hmrPos) (pre ++ u) post
            rightInputEq alpha used) := rightResources.rebaseCursor hrightCursorEq
      have hrightRun := rightRuns.2 (input := input) (visible.take mr)
        (visible.drop mr ++ hidden) (blocks.take cut.blockCount)
        (owners.take cut.blockCount) used used hrightStack hrightVisible
        (by
          intro k hk
          apply hallRight k
          rwa [List.length_take, Nat.min_eq_left hmr] at hk)
        (by rwa [List.length_take, Nat.min_eq_left hmr]) rightLayout
        rightCompatible (pre ++ u) post rightInputEq alpha hstable
        (by simpa [rightCursor, rightTask, rightMode, hmr0,
          liveScheduleCursor] using hrightInv)
        hrightFrames hend rightResources' (by
          simpa [rightResources', rightResources,
            ScheduleRunResources.binaryRightProtected,
            IndexOwnerPool.transportProtectedStructural] using hfree)
        (by
          exact ScheduleRunResources.rebaseCursor_parkingBelow rightResources
            hrightCursorEq (by
              simpa [rightResources,
                ScheduleRunResources.binaryRightProtected] using rightParkingBelow))
        (by
          simpa [rightResources', rightResources,
            ScheduleRunResources.binaryRightProtected] using rightOwnerLayout)
        (rightResources'.genericShadowStartLayout (by
            simpa [rightResources', rightResources,
              ScheduleRunResources.binaryRightProtected] using rightActive)
          (by simpa using rightOwnerLayout.owners_length)
          (by
            intro block hmem
            exact shadowLayout.block_nonempty block
              (List.mem_of_mem_take hmem)))
        (by
          change EventOwnedLayout rightParse
            (rightResources.rebaseCursor hrightCursorEq).window
            (blocks.take cut.blockCount)
            ((rightResources.rebaseCursor hrightCursorEq).tickets.semanticOwners
              (owners.take cut.blockCount))
          rw [ScheduleRunResources.rebaseCursor_window,
            ScheduleRunResources.rebaseCursor_semanticOwners,
            rightResourcesWindow, rightResourcesTickets]
          exact rightTicketOwnerLayout)
        (by
          refine ⟨blocks.drop cut.blockCount ++ parkedBlocks,
            owners.drop cut.blockCount ++ parkedOwners, ?_, ?_⟩
          · change (rightResources.rebaseCursor hrightCursorEq).ticketShadowBlocks =
              blocks.take cut.blockCount ++
                (blocks.drop cut.blockCount ++ parkedBlocks)
            rw [ScheduleRunResources.rebaseCursor_ticketShadowBlocks]
            change resources.ticketShadowBlocks = _
            rw [hcontextBlocks, ← List.append_assoc,
              List.take_append_drop]
          · change (rightResources.rebaseCursor hrightCursorEq).ticketShadowOwners =
              owners.take cut.blockCount ++
                (owners.drop cut.blockCount ++ parkedOwners)
            rw [ScheduleRunResources.rebaseCursor_ticketShadowOwners]
            change resources.ticketShadowOwners = _
            rw [hcontextOwners, ← List.append_assoc,
              List.take_append_drop])
        (by
          intro hinput
          have h := ticketTransientFreeRight hinput
          change IndexTicket.transient hinput ∉
            (liveScheduleCursor rightParse (hallRight 0 hmrPos) (pre ++ u) post
              rightInputEq alpha used).indexTickets
                (rightResources.rebaseCursor hrightCursorEq).tickets.ticketOf
          rw [ScheduleRunResources.rebaseCursor_ticketOf, rightResourcesTickets,
            ScheduleCursor.indexTickets, hrightCursorEq]
          exact h)
        (by
          simpa [rightResources', rightResources,
            ScheduleRunResources.binaryRightProtected] using rightActive)
        (by
          intro hinput
          have h := transientFreeRight hinput
          simpa [hrightCursorEq] using h)
        (by
          intro hinput
          have h := scratchFreeRight hinput
          simpa [hrightCursorEq] using h)
      have hrightRun' : ScheduleReaches g input
          (scheduleStateOfCursor (pre ++ u).length (by
            rw [input_eq]
            simp) rightCursor hrightInv)
          (scheduleStateOfCursor ((pre ++ u) ++ v).length (by
            rw [input_eq]
            simp) (scheduleWordCursor alpha used) hend) := by
        simpa [rightCursor, rightTask, rightMode, hmr0,
          liveScheduleCursor, scheduleStateOfCursor] using hrightRun
      simpa [startState, rightCursor, rightTask, rightMode, hmr0,
        liveScheduleCursor, scheduleStateOfCursor, List.append_assoc] using
        hforkStep.trans (hleftRun'.trans hrightRun')
  · have hrightFull : mr = n := hfull.resolve_left hleftFull
    have hmr0 : mr ≠ 0 := by omega
    have rightUsed : rightParse.ConsumesAt 0 := hallRight 0 (Nat.pos_of_ne_zero hmr0)
    have rightCompatible : EventCompatible rightParse blocks :=
      EventCompatible.binaryRight compatible
    by_cases hml0 : ml = 0
    · have leftUnused : ¬ leftParse.ConsumesAt 0 := by
        simpa [hml0] using hfirstLeft
      have hblocksNonempty : ∀ block ∈ blocks, block ≠ [] :=
        layout.erase.blocks_nonempty
      let leftZeroLedger : ScheduleOwnerLedger leftParse
          resources.window.binaryLeft forkCursor :=
        leftOwnerLedger.restrictAtMaximalBoundary
          (by simpa [leftOwnerLedger] using startActive)
          startOwnerLayout.binaryLeft hblocksNonempty
          (BlockLayout.Boundary.start blocks) leftUnused
      have leftZeroActive : leftZeroLedger.active = [] := by
        change owners.take (BlockLayout.Boundary.start blocks).blockCount = []
        rfl
      let leftZeroTicketLedger : forkTickets.SemanticScheduleOwnerLedger leftParse
          resources.window.binaryLeft :=
        leftTicketOwnerLedger.restrictAtMaximalBoundary leftTicketActiveEq
          (by rw [leftOwnerActive]; exact leftTicketOwnerLayout)
          hblocksNonempty (BlockLayout.Boundary.start blocks) leftUnused
      have leftZeroTicketActive : leftZeroTicketLedger.active =
          forkTickets.semanticOwners leftZeroLedger.active := by
        change (forkTickets.semanticOwners leftOwnerLedger.active).take 0 =
          forkTickets.semanticOwners (owners.take 0)
        rw [leftOwnerActive]
        simp [IndexTicketLedger.semanticOwners]
      let leftZeroResources : ScheduleRunResources leftParse pre forkCursor :=
        resources.binaryLeftProtected rightTask.owner hindicesFork htaskPerm rfl
          hleftProductive resources.window.binaryLeft leftZeroLedger forkTickets
          leftParkingBelow.toAtOrBelow leftZeroTicketLedger leftZeroTicketActive
          resources.ticketShadowBlocks
          resources.ticketShadowOwners leftTicketShadowOwnersSubset
          resources.ticketShadowOwners_nodup leftTicketShadowLedger
          leftTicketShadowActiveEq leftTicketShadowLayout
      have leftZeroResourcesTickets : leftZeroResources.tickets = forkTickets := rfl
      let rightCursor : ScheduleCursor g input :=
        ⟨alpha ++ [.dollar], .task rightTask, word⟩
      have hrightInv : ScheduleInvariant rightCursor := by
        dsimp [rightCursor, forkCursor]
        exact ScheduleInvariant.finishTask (alpha ++ [ScheduleAtom.dollar]) leftTask
          (.task rightTask) word hfork
      have hleftCursorEq :
          plainScheduleCursor leftParse leftUnused pre (v ++ post) leftInputEq alpha
            (.task rightTask) word = forkCursor := by
        simp [plainScheduleCursor, forkCursor, leftTask, leftMode, hml0]
      let leftResources' : ScheduleRunResources leftParse pre
          (plainScheduleCursor leftParse leftUnused pre (v ++ post) leftInputEq alpha
            (.task rightTask) word) := leftZeroResources.rebaseCursor hleftCursorEq
      have hleftRun := leftRuns.1 (input := input) leftUnused pre (v ++ post)
        leftInputEq alpha (.task rightTask) word hstable
        (by simpa [forkCursor, leftTask, leftMode, hml0,
          plainScheduleCursor] using hfork)
        hrightInv leftResources' (by
          simpa [leftResources', leftZeroResources,
            ScheduleRunResources.binaryLeftProtected,
            IndexOwnerPool.transportProtectedStructural] using hfree)
        (by
          exact ScheduleRunResources.rebaseCursor_parkingBelow leftZeroResources
            hleftCursorEq (by
              simpa [leftZeroResources,
                ScheduleRunResources.binaryLeftProtected] using leftParkingBelow))
        (by
          simpa [leftResources', leftZeroResources,
            ScheduleRunResources.binaryLeftProtected] using leftZeroActive)
        (leftResources'.genericShadowStartLayout (by
            simpa [leftResources', leftZeroResources,
              ScheduleRunResources.binaryLeftProtected] using leftZeroActive)
          (by simp)
          (by simp))
        (by
          intro hinput
          have h := ticketTransientFreeFork hinput
          change IndexTicket.transient hinput ∉
            (plainScheduleCursor leftParse leftUnused pre (v ++ post) leftInputEq
              alpha (.task rightTask) word).indexTickets
                (leftZeroResources.rebaseCursor hleftCursorEq).tickets.ticketOf
          rw [ScheduleRunResources.rebaseCursor_ticketOf,
            leftZeroResourcesTickets, ScheduleCursor.indexTickets, hleftCursorEq]
          exact h)
        (by
          intro hinput
          have h := transientFreeFork hinput
          simpa [hleftCursorEq] using h)
        (by
          intro hinput
          have h := scratchFreeFork hinput
          simpa [hleftCursorEq] using h)
      have hleftRun' : ScheduleReaches g input forkState
          (scheduleStateOfCursor (pre ++ u).length (by
            rw [input_eq]
            simp) rightCursor hrightInv) := by
        simpa [forkState, forkCursor, rightCursor, scheduleStateOfCursor,
          plainScheduleCursor, leftTask, leftMode, hml0] using hleftRun
      have hindicesRight : rightCursor.indexOwners = startCursor.indexOwners := by
        simp [rightCursor, startCursor, ScheduleCursor.indexOwners,
          ScheduleCursor.word, ScheduleAtom.indexOwner?, List.filterMap_append]
      have hfinishPerm : forkCursor.taskOwners.Perm
          (leftTask.owner :: rightCursor.taskOwners) := by
        simp only [forkCursor, rightCursor, ScheduleCursor.taskOwners_mk,
          ScheduleAtom.taskOwner?, List.filterMap_cons, List.filterMap_nil]
        simpa only [List.append_assoc] using
          (List.perm_middle
            (l₁ := (alpha ++ [ScheduleAtom.dollar]).filterMap
              ScheduleAtom.taskOwner?)
            (l₂ := rightTask.owner :: word.filterMap ScheduleAtom.taskOwner?)
            (a := leftTask.owner))
      have hframesRight : rightCursor.frameOwners = startCursor.frameOwners := by
        simp [rightCursor, startCursor, ScheduleCursor.frameOwners,
          ScheduleCursor.word, ScheduleAtom.closeOwner?, List.filterMap_append]
      have rightPrefixLedger : PrefixFrameLedger rightCursor :=
        startLedger.prefixLedger.transport
          (by simp [rightCursor, startCursor])
          (by rw [hframesRight])
      let rightOwnerLedger : ScheduleOwnerLedger rightParse
          resources.window.binaryRight rightCursor :=
        startLedger.transport resources.window.binaryRight
          (by
            simpa [rightCursor, startCursor, ScheduleAtom.indexOwner?] using
              startLedger.right_eq)
          (fun owner howner =>
            EventOwnedLayout.outside_binaryRight resources.window
              (startLedger.outside_at owner howner))
          (by
            rw [hframesRight]
            exact startLedger.frames.binaryRight)
          rightPrefixLedger
      have rightActive : rightOwnerLedger.active = owners := by
        simpa [rightOwnerLedger] using startActive
      let rightTickets : IndexTicketLedger rightCursor :=
        startTickets.transport (by rw [hindicesRight])
      have rightParkingBelow :
          rightTickets.ParkingBelow resources.window.binaryRight := by
        dsimp [rightTickets]
        exact startParkingAtOrBelow.transport_toBelow_of_base_lt
          (by rw [hindicesRight]) (by
            simp only [ProductiveOwnerWindow.binaryRight_base]
            omega)
      let rightTicketPrefixLedger : PrefixFrameLedger rightTickets.semanticCursor :=
          startTicketOwnerLedger.prefixLedger.transport
            (by
              change
                ((rightCursor.left.map (ScheduleAtom.relabelTicketOwner
                    rightTickets.semanticOwnerOf)).filterMap
                    ScheduleAtom.indexOwner?).Perm
                  ((startCursor.left.map (ScheduleAtom.relabelTicketOwner
                    startTickets.semanticOwnerOf)).filterMap ScheduleAtom.indexOwner?)
              rw [ScheduleAtom.filterMap_indexOwner_relabelTicketOwner,
                ScheduleAtom.filterMap_indexOwner_relabelTicketOwner]
              have hfun : rightTickets.semanticOwnerOf =
                  startTickets.semanticOwnerOf := by
                funext owner
                rfl
              rw [hfun])
            (by
              rw [rightTickets.semanticCursor_frameOwners,
                startTickets.semanticCursor_frameOwners]
              have hfun : rightTickets.semanticOwnerOf =
                  startTickets.semanticOwnerOf := by
                funext owner
                rfl
              rw [hfun, hframesRight])
      let rightTicketOwnerLedger : rightTickets.SemanticScheduleOwnerLedger
          rightParse resources.window.binaryRight :=
        startTicketOwnerLedger.transport resources.window.binaryRight
          (by
            have hright := startTicketOwnerLedger.right_eq
            rw [startTickets.semanticCursor_right_indexOwners] at hright
            rw [rightTickets.semanticCursor_right_indexOwners]
            have hfun : rightTickets.semanticOwnerOf =
                startTickets.semanticOwnerOf := by
              funext owner
              rfl
            simpa [rightCursor, startCursor, hfun] using hright)
          (fun owner howner => EventOwnedLayout.outside_binaryRight
            resources.window (startTicketOwnerLedger.outside_at owner howner))
          (by
            have hframes := startTicketOwnerLedger.frames.binaryRight
            rw [startTickets.semanticCursor_frameOwners] at hframes
            rw [rightTickets.semanticCursor_frameOwners]
            have hfun : rightTickets.semanticOwnerOf =
                startTickets.semanticOwnerOf := by
              funext owner
              rfl
            simpa [hfun, hframesRight] using hframes)
          rightTicketPrefixLedger
      let rightTicketShadowLedger : rightTickets.SemanticShadowOwnerLedger
          rightParse resources.window.binaryRight :=
        startTicketShadowLedger.transport resources.window.binaryRight
          (by
            have hright := startTicketShadowLedger.right_eq
            rw [startTickets.semanticCursor_right_indexOwners] at hright
            rw [rightTickets.semanticCursor_right_indexOwners]
            have hfun : rightTickets.semanticOwnerOf =
                startTickets.semanticOwnerOf := by
              funext owner
              rfl
            simpa [rightCursor, startCursor, hfun] using hright)
          (fun owner howner => OutsideShadowWindow.binaryRight resources.window
            (startTicketShadowLedger.outside_at owner howner))
          (by
            have hframes := startTicketShadowLedger.frames.binaryRight
            rw [startTickets.semanticCursor_frameOwners] at hframes
            rw [rightTickets.semanticCursor_frameOwners]
            have hfun : rightTickets.semanticOwnerOf =
                startTickets.semanticOwnerOf := by
              funext owner
              rfl
            simpa [hfun, hframesRight] using hframes)
          rightTicketPrefixLedger
      have rightTicketActive : rightTicketOwnerLedger.active =
          rightTickets.semanticOwners rightOwnerLedger.active := by
        change startTicketOwnerLedger.active =
          rightTickets.semanticOwners startLedger.active
        have hbase := startTicketActive
        rw [← startActive] at hbase
        simpa [rightTickets, startTickets, IndexTicketLedger.transport,
          IndexTicketLedger.semanticOwners, IndexTicketLedger.semanticOwnerOf] using hbase
      have rightTicketShadowActive : rightTicketShadowLedger.active =
          rightTickets.semanticOwners resources.ticketShadowOwners := by
        change startTicketShadowLedger.active =
          rightTickets.semanticOwners resources.ticketShadowOwners
        have hbase := startTicketShadowActive
        simpa [rightTickets, startTickets, IndexTicketLedger.transport,
          IndexTicketLedger.semanticOwners, IndexTicketLedger.semanticOwnerOf] using hbase
      let rightTicketOwnerLayout : rightTickets.EventTicketLayout rightParse
          resources.window.binaryRight blocks owners := by
        simpa [rightTickets, startTickets] using startTicketOwnerLayout.binaryRight
      let rightTicketShadowLayout : rightTickets.ShadowTicketLayout rightParse
          resources.window.binaryRight resources.ticketShadowBlocks
            resources.ticketShadowOwners := by
        simpa [rightTickets, startTickets] using startTicketShadowLayout.binaryRight
      have rightTicketShadowOwnersSubset : resources.ticketShadowOwners ⊆
          rightCursor.indexOwners := by
        intro owner howner
        rw [hindicesRight]
        simpa [startCursor, parentTask, parent, liveScheduleCursor] using
          resources.ticketShadowOwners_subset howner
      have transientFreeRight : ∀ hinput : 0 < input.length,
          ProductiveOwnerWindow.transientOwner (g := g) hinput ∉
            rightCursor.indexOwners := by
        intro hinput
        rw [hindicesRight]
        exact transientFreeStart hinput
      have scratchFreeRight : ∀ hinput : 0 < input.length,
          ProductiveOwnerWindow.scratchOwner (g := g) hinput ∉
            rightCursor.indexOwners := by
        intro hinput
        rw [hindicesRight]
        exact scratchFreeStart hinput
      have ticketTransientFreeRight : ∀ hinput : 0 < input.length,
          IndexTicket.transient hinput ∉
            rightCursor.indexTickets rightTickets.ticketOf := by
        intro hinput
        simpa [rightTickets, startTickets, ScheduleCursor.indexTickets,
          hindicesRight] using ticketTransientFreeStart hinput
      let rightResources : ScheduleRunResources rightParse (pre ++ u) rightCursor :=
        resources.binaryRightProtected hfork leftTask.owner rightTask.owner
          hindicesRight htaskPerm hfinishPerm rfl rfl hrightProductive
          resources.window.binaryRight rightOwnerLedger rightTickets
          rightParkingBelow.toAtOrBelow rightTicketOwnerLedger rightTicketActive
          resources.ticketShadowBlocks
          resources.ticketShadowOwners rightTicketShadowOwnersSubset
          resources.ticketShadowOwners_nodup rightTicketShadowLedger
          rightTicketShadowActive rightTicketShadowLayout
      have rightResourcesTickets : rightResources.tickets = rightTickets := rfl
      have rightResourcesWindow : rightResources.window =
          resources.window.binaryRight := rfl
      have hrightCursorEq :
          liveScheduleCursor rightParse rightUsed (pre ++ u) post rightInputEq
            alpha word = rightCursor := by
        simp [liveScheduleCursor, rightCursor, rightTask, rightMode, hmr0]
      let rightResources' : ScheduleRunResources rightParse (pre ++ u)
          (liveScheduleCursor rightParse rightUsed (pre ++ u) post rightInputEq
            alpha word) := rightResources.rebaseCursor hrightCursorEq
      have hrightFrames : List.Disjoint owners
          (liveScheduleCursor rightParse rightUsed (pre ++ u) post rightInputEq
            alpha word).frameOwners := by
        simpa [liveScheduleCursor, startCursor, rightTask, rightMode, hmr0,
          ScheduleCursor.frameOwners, ScheduleCursor.word,
          ScheduleAtom.closeOwner?, List.filterMap_append] using hframes
      have hrightRun := rightRuns.2 (input := input) visible hidden blocks owners
        word used hstack hne (by simpa [hrightFull, n] using hallRight)
        (by simpa [hrightFull, n] using hfirstRight) layout rightCompatible
        (pre ++ u) post rightInputEq alpha hstable
        (by simpa [rightCursor, rightTask, rightMode, hmr0,
          liveScheduleCursor] using hrightInv)
        hrightFrames hend rightResources' (by
          simpa [rightResources', rightResources,
            ScheduleRunResources.binaryRightProtected,
            IndexOwnerPool.transportProtectedStructural] using hfree)
        (by
          exact ScheduleRunResources.rebaseCursor_parkingBelow rightResources
            hrightCursorEq (by
              simpa [rightResources,
                ScheduleRunResources.binaryRightProtected] using rightParkingBelow))
        (by
          simpa [rightResources', rightResources,
            ScheduleRunResources.binaryRightProtected] using
              startOwnerLayout.binaryRight)
        (rightResources'.genericShadowStartLayout (by
            simpa [rightResources', rightResources,
              ScheduleRunResources.binaryRightProtected] using rightActive)
          (by simpa using (startOwnerLayout.binaryRight).owners_length)
          shadowLayout.block_nonempty)
        (by
          change EventOwnedLayout rightParse
            (rightResources.rebaseCursor hrightCursorEq).window blocks
            ((rightResources.rebaseCursor hrightCursorEq).tickets.semanticOwners
              owners)
          rw [ScheduleRunResources.rebaseCursor_window,
            ScheduleRunResources.rebaseCursor_semanticOwners,
            rightResourcesWindow, rightResourcesTickets]
          exact rightTicketOwnerLayout)
        (by
          refine ⟨parkedBlocks, parkedOwners, ?_, ?_⟩
          · simpa [rightResources', rightResources,
              ScheduleRunResources.binaryRightProtected] using hcontextBlocks
          · simpa [rightResources', rightResources,
              ScheduleRunResources.binaryRightProtected] using hcontextOwners)
        (by
          intro hinput
          have h := ticketTransientFreeRight hinput
          change IndexTicket.transient hinput ∉
            (liveScheduleCursor rightParse rightUsed (pre ++ u) post rightInputEq
              alpha word).indexTickets
                (rightResources.rebaseCursor hrightCursorEq).tickets.ticketOf
          rw [ScheduleRunResources.rebaseCursor_ticketOf, rightResourcesTickets,
            ScheduleCursor.indexTickets, hrightCursorEq]
          exact h)
        (by
          simpa [rightResources', rightResources,
            ScheduleRunResources.binaryRightProtected] using rightActive)
        (by
          intro hinput
          have h := transientFreeRight hinput
          simpa [hrightCursorEq] using h)
        (by
          intro hinput
          have h := scratchFreeRight hinput
          simpa [hrightCursorEq] using h)
      have hrightRun' : ScheduleReaches g input
          (scheduleStateOfCursor (pre ++ u).length (by
            rw [input_eq]
            simp) rightCursor hrightInv)
          (scheduleStateOfCursor ((pre ++ u) ++ v).length (by
            rw [input_eq]
            simp) (scheduleWordCursor alpha used) hend) := by
        simpa [rightCursor, rightTask, rightMode, hmr0,
          liveScheduleCursor, scheduleStateOfCursor] using hrightRun
      simpa [startState, rightCursor, rightTask, rightMode, hmr0,
        liveScheduleCursor, scheduleStateOfCursor, List.append_assoc] using
        hforkStep.trans (hleftRun'.trans hrightRun')
    · have hmlPos : 0 < ml := Nat.pos_of_ne_zero hml0
      have hmlEvent : ml ∈ leftParse.eventDepths :=
        IndexedGrammar.Aho.NFParse.maximalConsumedPrefixMemEventDepthsCurrent
          leftParse hmlPos hallLeft hfirstLeft
      let cut : BlockLayout.Boundary blocks ml :=
        (EventCompatible.binaryLeft compatible).boundary ml hmlEvent
      rcases ScheduleBlockLayout.splitAtBoundaryCurrent layout cut with
        ⟨middle, prefixLayout, remainingLayout⟩
      have hblocksNonempty : ∀ block ∈ blocks, block ≠ [] :=
        layout.erase.blocks_nonempty
      have leftCompatible : EventCompatible leftParse
          (blocks.take cut.blockCount) :=
        EventCompatible.takeAtConsumedBoundaryCurrent hblocksNonempty
          (EventCompatible.binaryLeft compatible) cut hfirstLeft
      let leftCutLedger : ScheduleOwnerLedger leftParse
          resources.window.binaryLeft forkCursor :=
        leftOwnerLedger.restrictAtMaximalBoundary
          (by simpa [leftOwnerLedger] using startActive)
          startOwnerLayout.binaryLeft hblocksNonempty cut hfirstLeft
      have leftCutActive : leftCutLedger.active = owners.take cut.blockCount := by
        rfl
      let leftCutTicketLedger : forkTickets.SemanticScheduleOwnerLedger leftParse
          resources.window.binaryLeft :=
        leftTicketOwnerLedger.restrictAtMaximalBoundary leftTicketActiveEq
          (by rw [leftOwnerActive]; exact leftTicketOwnerLayout)
          hblocksNonempty cut hfirstLeft
      have leftCutTicketActive : leftCutTicketLedger.active =
          forkTickets.semanticOwners leftCutLedger.active := by
        change (forkTickets.semanticOwners leftOwnerLedger.active).take cut.blockCount =
          forkTickets.semanticOwners (owners.take cut.blockCount)
        rw [leftOwnerActive]
        simp [IndexTicketLedger.semanticOwners, List.map_take]
      let leftCutResources : ScheduleRunResources leftParse pre forkCursor :=
        resources.binaryLeftProtected rightTask.owner hindicesFork htaskPerm rfl
          hleftProductive resources.window.binaryLeft leftCutLedger forkTickets
          leftParkingBelow.toAtOrBelow leftCutTicketLedger leftCutTicketActive
          resources.ticketShadowBlocks
          resources.ticketShadowOwners leftTicketShadowOwnersSubset
          resources.ticketShadowOwners_nodup leftTicketShadowLedger
          leftTicketShadowActiveEq leftTicketShadowLayout
      have leftCutResourcesTickets : leftCutResources.tickets = forkTickets := rfl
      have leftCutResourcesWindow : leftCutResources.window =
          resources.window.binaryLeft := rfl
      let leftOwnerLayout : EventOwnedLayout leftParse
          resources.window.binaryLeft (blocks.take cut.blockCount)
            (owners.take cut.blockCount) :=
        (startOwnerLayout.binaryLeft).take cut.blockCount leftCompatible
      let leftTicketOwnerCutLayout : forkTickets.EventTicketLayout leftParse
          resources.window.binaryLeft (blocks.take cut.blockCount)
            (owners.take cut.blockCount) := by
        change EventOwnedLayout leftParse resources.window.binaryLeft
          (blocks.take cut.blockCount)
          (List.map forkTickets.semanticOwnerOf (owners.take cut.blockCount))
        rw [List.map_take]
        exact leftTicketOwnerLayout.take cut.blockCount leftCompatible
      have pendingLayout : ScheduleBlockLayout g input (visible.take ml)
          (blocks.take cut.blockCount) (owners.take cut.blockCount)
          (.task rightTask :: word) (.task rightTask :: middle) := by
        simpa using prefixLayout.prepend [.task rightTask]
          (by simp [ScheduleIndexFree]) (by simp [ScheduleDollarFree])
      have hforkMarked : ScheduleInvariant
          ⟨alpha ++ [.dollar], .task leftTask, .task rightTask :: middle⟩ :=
        ScheduleInvariant.replaceRight (alpha ++ [ScheduleAtom.dollar])
          (.task leftTask) pendingLayout hfork
      let rightCursor : ScheduleCursor g input :=
        ⟨alpha ++ [.dollar], .task rightTask, middle⟩
      have hrightInv : ScheduleInvariant rightCursor := by
        dsimp [rightCursor]
        exact ScheduleInvariant.finishTask (alpha ++ [ScheduleAtom.dollar]) leftTask
          (.task rightTask) middle hforkMarked
      have hleftStack : stack = visible.take ml ++
          (visible.drop ml ++ hidden) := by
        calc
          stack = visible ++ hidden := hstack
          _ = visible.take ml ++ (visible.drop ml ++ hidden) := by
            rw [← List.append_assoc, List.take_append_drop]
      have hml' : ml ≤ visible.length := by simpa [n] using hml
      have hleftVisible : visible.take ml ≠ [] := by
        apply List.ne_nil_of_length_pos
        rw [List.length_take, Nat.min_eq_left hml']
        exact hmlPos
      have hleftFrames : List.Disjoint (owners.take cut.blockCount)
          (liveScheduleCursor leftParse (hallLeft 0 hmlPos) pre (v ++ post)
            leftInputEq alpha (.task rightTask :: word)).frameOwners := by
        apply List.disjoint_left.mpr
        intro owner howner hframe
        apply (List.disjoint_left.mp hframes) (List.mem_of_mem_take howner)
        simpa [liveScheduleCursor, startCursor, leftTask, leftMode, hml0,
          ScheduleCursor.frameOwners, ScheduleCursor.word,
          ScheduleAtom.closeOwner?, List.filterMap_append] using hframe
      have hleftCursorEq :
          liveScheduleCursor leftParse (hallLeft 0 hmlPos) pre (v ++ post)
            leftInputEq alpha (.task rightTask :: word) = forkCursor := by
        simp [liveScheduleCursor, forkCursor, leftTask, leftMode, hml0]
      let leftResources' : ScheduleRunResources leftParse pre
          (liveScheduleCursor leftParse (hallLeft 0 hmlPos) pre (v ++ post)
            leftInputEq alpha (.task rightTask :: word)) :=
        leftCutResources.rebaseCursor hleftCursorEq
      have hleftRun := leftRuns.2 (input := input) (visible.take ml)
        (visible.drop ml ++ hidden) (blocks.take cut.blockCount)
        (owners.take cut.blockCount) (.task rightTask :: word)
        (.task rightTask :: middle) hleftStack hleftVisible
        (by
          intro k hk
          apply hallLeft k
          rwa [List.length_take, Nat.min_eq_left hml'] at hk)
        (by rwa [List.length_take, Nat.min_eq_left hml']) pendingLayout
        leftCompatible pre (v ++ post) leftInputEq alpha hstable
        (by simpa [forkCursor, leftTask, leftMode, hml0,
          liveScheduleCursor] using hfork)
        hleftFrames hrightInv leftResources' (by
          simpa [leftResources', leftCutResources,
            ScheduleRunResources.binaryLeftProtected,
            IndexOwnerPool.transportProtectedStructural] using hfree)
        (by
          exact ScheduleRunResources.rebaseCursor_parkingBelow leftCutResources
            hleftCursorEq (by
              simpa [leftCutResources,
                ScheduleRunResources.binaryLeftProtected] using leftParkingBelow))
        (by
          simpa [leftResources', leftCutResources,
            ScheduleRunResources.binaryLeftProtected] using leftOwnerLayout)
        (leftResources'.genericShadowStartLayout (by
            simpa [leftResources', leftCutResources,
              ScheduleRunResources.binaryLeftProtected] using leftCutActive)
          (by simpa using leftOwnerLayout.owners_length)
          (by
            intro block hmem
            exact shadowLayout.block_nonempty block
              (List.mem_of_mem_take hmem)))
        (by
          change EventOwnedLayout leftParse
            (leftCutResources.rebaseCursor hleftCursorEq).window
            (blocks.take cut.blockCount)
            ((leftCutResources.rebaseCursor hleftCursorEq).tickets.semanticOwners
              (owners.take cut.blockCount))
          rw [ScheduleRunResources.rebaseCursor_window,
            ScheduleRunResources.rebaseCursor_semanticOwners,
            leftCutResourcesWindow, leftCutResourcesTickets]
          exact leftTicketOwnerCutLayout)
        (by
          refine ⟨blocks.drop cut.blockCount ++ parkedBlocks,
            owners.drop cut.blockCount ++ parkedOwners, ?_, ?_⟩
          · change (leftCutResources.rebaseCursor hleftCursorEq).ticketShadowBlocks =
              blocks.take cut.blockCount ++
                (blocks.drop cut.blockCount ++ parkedBlocks)
            rw [ScheduleRunResources.rebaseCursor_ticketShadowBlocks]
            change resources.ticketShadowBlocks = _
            rw [hcontextBlocks, ← List.append_assoc,
              List.take_append_drop]
          · change (leftCutResources.rebaseCursor hleftCursorEq).ticketShadowOwners =
              owners.take cut.blockCount ++
                (owners.drop cut.blockCount ++ parkedOwners)
            rw [ScheduleRunResources.rebaseCursor_ticketShadowOwners]
            change resources.ticketShadowOwners = _
            rw [hcontextOwners, ← List.append_assoc,
              List.take_append_drop])
        (by
          intro hinput
          have h := ticketTransientFreeFork hinput
          change IndexTicket.transient hinput ∉
            (liveScheduleCursor leftParse (hallLeft 0 hmlPos) pre (v ++ post)
              leftInputEq alpha (.task rightTask :: word)).indexTickets
                (leftCutResources.rebaseCursor hleftCursorEq).tickets.ticketOf
          rw [ScheduleRunResources.rebaseCursor_ticketOf, leftCutResourcesTickets,
            ScheduleCursor.indexTickets, hleftCursorEq]
          exact h)
        (by
          simpa [leftResources', leftCutResources,
            ScheduleRunResources.binaryLeftProtected] using leftCutActive)
        (by
          intro hinput
          have h := transientFreeFork hinput
          simpa [hleftCursorEq] using h)
        (by
          intro hinput
          have h := scratchFreeFork hinput
          simpa [hleftCursorEq] using h)
      have hleftRun' : ScheduleReaches g input forkState
          (scheduleStateOfCursor (pre ++ u).length (by
            rw [input_eq]
            simp) rightCursor hrightInv) := by
        simpa [forkState, forkCursor, rightCursor, scheduleStateOfCursor,
          liveScheduleCursor, leftTask, leftMode, hml0] using hleftRun
      have hindicesRight : rightCursor.indexOwners = startCursor.indexOwners := by
        simp only [rightCursor, startCursor, ScheduleCursor.indexOwners_mk,
          ScheduleAtom.indexOwner?, List.filterMap_cons, List.filterMap_nil,
          List.append_nil]
        exact congrArg ((alpha ++ [ScheduleAtom.dollar]).filterMap
          ScheduleAtom.indexOwner? ++ ·) prefixLayout.indexOwners_eq.symm
      have hfinishPerm : forkCursor.taskOwners.Perm
          (leftTask.owner :: rightCursor.taskOwners) := by
        simp only [forkCursor, rightCursor, ScheduleCursor.taskOwners_mk,
          ScheduleAtom.taskOwner?, List.filterMap_cons, List.filterMap_nil]
        rw [prefixLayout.taskOwners_eq]
        simpa only [List.append_assoc] using
          (List.perm_middle
            (l₁ := (alpha ++ [ScheduleAtom.dollar]).filterMap
              ScheduleAtom.taskOwner?)
            (l₂ := rightTask.owner :: middle.filterMap ScheduleAtom.taskOwner?)
            (a := leftTask.owner))
      have hframesRight : rightCursor.frameOwners = startCursor.frameOwners := by
        simp only [rightCursor, startCursor, ScheduleCursor.frameOwners_mk,
          ScheduleAtom.closeOwner?, List.filterMap_cons, List.filterMap_nil,
          List.append_nil]
        exact congrArg ((alpha ++ [ScheduleAtom.dollar]).filterMap
          ScheduleAtom.closeOwner? ++ ·) prefixLayout.frameOwners_eq.symm
      have rightPrefixLedger : PrefixFrameLedger rightCursor :=
        startLedger.prefixLedger.transport
          (by simp [rightCursor, startCursor])
          (by rw [hframesRight])
      let rightOwnerLedger : ScheduleOwnerLedger rightParse
          resources.window.binaryRight rightCursor :=
        startLedger.transport resources.window.binaryRight
          (by
            calc
              rightCursor.right.filterMap ScheduleAtom.indexOwner? =
                  startCursor.right.filterMap ScheduleAtom.indexOwner? := by
                simpa [rightCursor, startCursor] using
                  prefixLayout.indexOwners_eq.symm
              _ = startLedger.active ++ startLedger.outside :=
                startLedger.right_eq)
          (fun owner howner =>
            EventOwnedLayout.outside_binaryRight resources.window
              (startLedger.outside_at owner howner))
          (by
            rw [hframesRight]
            exact startLedger.frames.binaryRight)
          rightPrefixLedger
      have rightActive : rightOwnerLedger.active = owners := by
        simpa [rightOwnerLedger] using startActive
      let rightTickets : IndexTicketLedger rightCursor :=
        startTickets.transport (by rw [hindicesRight])
      have rightParkingBelow :
          rightTickets.ParkingBelow resources.window.binaryRight := by
        dsimp [rightTickets]
        exact startParkingAtOrBelow.transport_toBelow_of_base_lt
          (by rw [hindicesRight]) (by
            simp only [ProductiveOwnerWindow.binaryRight_base]
            omega)
      let rightTicketPrefixLedger : PrefixFrameLedger rightTickets.semanticCursor :=
          startTicketOwnerLedger.prefixLedger.transport
            (by
              change
                ((rightCursor.left.map (ScheduleAtom.relabelTicketOwner
                    rightTickets.semanticOwnerOf)).filterMap
                    ScheduleAtom.indexOwner?).Perm
                  ((startCursor.left.map (ScheduleAtom.relabelTicketOwner
                    startTickets.semanticOwnerOf)).filterMap ScheduleAtom.indexOwner?)
              rw [ScheduleAtom.filterMap_indexOwner_relabelTicketOwner,
                ScheduleAtom.filterMap_indexOwner_relabelTicketOwner]
              have hfun : rightTickets.semanticOwnerOf =
                  startTickets.semanticOwnerOf := by
                funext owner
                rfl
              rw [hfun])
            (by
              rw [rightTickets.semanticCursor_frameOwners,
                startTickets.semanticCursor_frameOwners]
              have hfun : rightTickets.semanticOwnerOf =
                  startTickets.semanticOwnerOf := by
                funext owner
                rfl
              rw [hfun, hframesRight])
      let rightTicketOwnerLedger : rightTickets.SemanticScheduleOwnerLedger
          rightParse resources.window.binaryRight :=
        startTicketOwnerLedger.transport resources.window.binaryRight
          (by
            have hright := startTicketOwnerLedger.right_eq
            rw [startTickets.semanticCursor_right_indexOwners] at hright
            rw [rightTickets.semanticCursor_right_indexOwners]
            have hfun : rightTickets.semanticOwnerOf =
                startTickets.semanticOwnerOf := by
              funext owner
              rfl
            have hfilter : rightCursor.right.filterMap ScheduleAtom.indexOwner? =
                startCursor.right.filterMap ScheduleAtom.indexOwner? := by
              simpa [rightCursor, startCursor] using
                prefixLayout.indexOwners_eq.symm
            rw [hfun, hfilter]
            exact hright)
          (fun owner howner => EventOwnedLayout.outside_binaryRight
            resources.window (startTicketOwnerLedger.outside_at owner howner))
          (by
            have hframes := startTicketOwnerLedger.frames.binaryRight
            rw [startTickets.semanticCursor_frameOwners] at hframes
            rw [rightTickets.semanticCursor_frameOwners]
            have hfun : rightTickets.semanticOwnerOf =
                startTickets.semanticOwnerOf := by
              funext owner
              rfl
            simpa [hfun, hframesRight] using hframes)
          rightTicketPrefixLedger
      let rightTicketShadowLedger : rightTickets.SemanticShadowOwnerLedger
          rightParse resources.window.binaryRight :=
        startTicketShadowLedger.transport resources.window.binaryRight
          (by
            have hright := startTicketShadowLedger.right_eq
            rw [startTickets.semanticCursor_right_indexOwners] at hright
            rw [rightTickets.semanticCursor_right_indexOwners]
            have hfun : rightTickets.semanticOwnerOf =
                startTickets.semanticOwnerOf := by
              funext owner
              rfl
            have hfilter : rightCursor.right.filterMap ScheduleAtom.indexOwner? =
                startCursor.right.filterMap ScheduleAtom.indexOwner? := by
              simpa [rightCursor, startCursor] using
                prefixLayout.indexOwners_eq.symm
            rw [hfun, hfilter]
            exact hright)
          (fun owner howner => OutsideShadowWindow.binaryRight resources.window
            (startTicketShadowLedger.outside_at owner howner))
          (by
            have hframes := startTicketShadowLedger.frames.binaryRight
            rw [startTickets.semanticCursor_frameOwners] at hframes
            rw [rightTickets.semanticCursor_frameOwners]
            have hfun : rightTickets.semanticOwnerOf =
                startTickets.semanticOwnerOf := by
              funext owner
              rfl
            simpa [hfun, hframesRight] using hframes)
          rightTicketPrefixLedger
      have rightTicketActive : rightTicketOwnerLedger.active =
          rightTickets.semanticOwners rightOwnerLedger.active := by
        change startTicketOwnerLedger.active =
          rightTickets.semanticOwners startLedger.active
        have hbase := startTicketActive
        rw [← startActive] at hbase
        simpa [rightTickets, startTickets, IndexTicketLedger.transport,
          IndexTicketLedger.semanticOwners, IndexTicketLedger.semanticOwnerOf] using hbase
      have rightTicketShadowActive : rightTicketShadowLedger.active =
          rightTickets.semanticOwners resources.ticketShadowOwners := by
        change startTicketShadowLedger.active =
          rightTickets.semanticOwners resources.ticketShadowOwners
        have hbase := startTicketShadowActive
        simpa [rightTickets, startTickets, IndexTicketLedger.transport,
          IndexTicketLedger.semanticOwners, IndexTicketLedger.semanticOwnerOf] using hbase
      let rightTicketOwnerLayout : rightTickets.EventTicketLayout rightParse
          resources.window.binaryRight blocks owners := by
        simpa [rightTickets, startTickets] using startTicketOwnerLayout.binaryRight
      let rightTicketShadowLayout : rightTickets.ShadowTicketLayout rightParse
          resources.window.binaryRight resources.ticketShadowBlocks
            resources.ticketShadowOwners := by
        simpa [rightTickets, startTickets] using startTicketShadowLayout.binaryRight
      have rightTicketShadowOwnersSubset : resources.ticketShadowOwners ⊆
          rightCursor.indexOwners := by
        intro owner howner
        rw [hindicesRight]
        simpa [startCursor, parentTask, parent, liveScheduleCursor] using
          resources.ticketShadowOwners_subset howner
      have transientFreeRight : ∀ hinput : 0 < input.length,
          ProductiveOwnerWindow.transientOwner (g := g) hinput ∉
            rightCursor.indexOwners := by
        intro hinput
        rw [hindicesRight]
        exact transientFreeStart hinput
      have scratchFreeRight : ∀ hinput : 0 < input.length,
          ProductiveOwnerWindow.scratchOwner (g := g) hinput ∉
            rightCursor.indexOwners := by
        intro hinput
        rw [hindicesRight]
        exact scratchFreeStart hinput
      have ticketTransientFreeRight : ∀ hinput : 0 < input.length,
          IndexTicket.transient hinput ∉
            rightCursor.indexTickets rightTickets.ticketOf := by
        intro hinput
        simpa [rightTickets, startTickets, ScheduleCursor.indexTickets,
          hindicesRight] using ticketTransientFreeStart hinput
      let rightResources : ScheduleRunResources rightParse (pre ++ u) rightCursor :=
        resources.binaryRightProtected hfork leftTask.owner rightTask.owner
          hindicesRight htaskPerm hfinishPerm rfl rfl hrightProductive
          resources.window.binaryRight rightOwnerLedger rightTickets
          rightParkingBelow.toAtOrBelow rightTicketOwnerLedger rightTicketActive
          resources.ticketShadowBlocks
          resources.ticketShadowOwners rightTicketShadowOwnersSubset
          resources.ticketShadowOwners_nodup rightTicketShadowLedger
          rightTicketShadowActive rightTicketShadowLayout
      have rightResourcesTickets : rightResources.tickets = rightTickets := rfl
      have rightResourcesWindow : rightResources.window =
          resources.window.binaryRight := rfl
      have hrightCursorEq :
          liveScheduleCursor rightParse rightUsed (pre ++ u) post rightInputEq
            alpha middle = rightCursor := by
        simp [liveScheduleCursor, rightCursor, rightTask, rightMode, hmr0]
      let rightResources' : ScheduleRunResources rightParse (pre ++ u)
          (liveScheduleCursor rightParse rightUsed (pre ++ u) post rightInputEq
            alpha middle) := rightResources.rebaseCursor hrightCursorEq
      have hrightFrames : List.Disjoint owners
          (liveScheduleCursor rightParse rightUsed (pre ++ u) post rightInputEq
            alpha middle).frameOwners := by
        apply List.disjoint_left.mpr
        intro owner howner hframe
        apply (List.disjoint_left.mp hframes) howner
        have heq :
            (liveScheduleCursor rightParse rightUsed (pre ++ u) post rightInputEq
              alpha middle).frameOwners = startCursor.frameOwners := by
          simp only [liveScheduleCursor, startCursor, ScheduleCursor.frameOwners_mk,
            ScheduleAtom.closeOwner?, List.filterMap_cons, List.filterMap_nil,
            List.append_nil]
          exact congrArg ((alpha ++ [ScheduleAtom.dollar]).filterMap
            ScheduleAtom.closeOwner? ++ ·) prefixLayout.frameOwners_eq.symm
        exact heq ▸ hframe
      have hrightRun := rightRuns.2 (input := input) visible hidden blocks owners
        middle used hstack hne (by simpa [hrightFull, n] using hallRight)
        (by simpa [hrightFull, n] using hfirstRight) remainingLayout
        rightCompatible (pre ++ u) post rightInputEq alpha hstable
        (by simpa [rightCursor, rightTask, rightMode, hmr0,
          liveScheduleCursor] using hrightInv)
        hrightFrames hend rightResources' (by
          simpa [rightResources', rightResources,
            ScheduleRunResources.binaryRightProtected,
            IndexOwnerPool.transportProtectedStructural] using hfree)
        (by
          exact ScheduleRunResources.rebaseCursor_parkingBelow rightResources
            hrightCursorEq (by
              simpa [rightResources,
                ScheduleRunResources.binaryRightProtected] using rightParkingBelow))
        (by
          simpa [rightResources', rightResources,
            ScheduleRunResources.binaryRightProtected] using
              startOwnerLayout.binaryRight)
        (rightResources'.genericShadowStartLayout (by
            simpa [rightResources', rightResources,
              ScheduleRunResources.binaryRightProtected] using rightActive)
          (by simpa using (startOwnerLayout.binaryRight).owners_length)
          shadowLayout.block_nonempty)
        (by
          change EventOwnedLayout rightParse
            (rightResources.rebaseCursor hrightCursorEq).window blocks
            ((rightResources.rebaseCursor hrightCursorEq).tickets.semanticOwners
              owners)
          rw [ScheduleRunResources.rebaseCursor_window,
            ScheduleRunResources.rebaseCursor_semanticOwners,
            rightResourcesWindow, rightResourcesTickets]
          exact rightTicketOwnerLayout)
        (by
          refine ⟨parkedBlocks, parkedOwners, ?_, ?_⟩
          · simpa [rightResources', rightResources,
              ScheduleRunResources.binaryRightProtected] using hcontextBlocks
          · simpa [rightResources', rightResources,
              ScheduleRunResources.binaryRightProtected] using hcontextOwners)
        (by
          intro hinput
          have h := ticketTransientFreeRight hinput
          change IndexTicket.transient hinput ∉
            (liveScheduleCursor rightParse rightUsed (pre ++ u) post rightInputEq
              alpha middle).indexTickets
                (rightResources.rebaseCursor hrightCursorEq).tickets.ticketOf
          rw [ScheduleRunResources.rebaseCursor_ticketOf, rightResourcesTickets,
            ScheduleCursor.indexTickets, hrightCursorEq]
          exact h)
        (by
          simpa [rightResources', rightResources,
            ScheduleRunResources.binaryRightProtected] using rightActive)
        (by
          intro hinput
          have h := transientFreeRight hinput
          simpa [hrightCursorEq] using h)
        (by
          intro hinput
          have h := scratchFreeRight hinput
          simpa [hrightCursorEq] using h)
      have hrightRun' : ScheduleReaches g input
          (scheduleStateOfCursor (pre ++ u).length (by
            rw [input_eq]
            simp) rightCursor hrightInv)
          (scheduleStateOfCursor ((pre ++ u) ++ v).length (by
            rw [input_eq]
            simp) (scheduleWordCursor alpha used) hend) := by
        simpa [rightCursor, rightTask, rightMode, hmr0,
          liveScheduleCursor, scheduleStateOfCursor] using hrightRun
      simpa [startState, rightCursor, rightTask, rightMode, hmr0,
        liveScheduleCursor, scheduleStateOfCursor, List.append_assoc] using
        hforkStep.trans (hleftRun'.trans hrightRun')

/-- Ordinary protected binary entry.  The strict parent invariant supplies the weaker premise
of the shared binary implementation. -/
public theorem protectedScheduleRun_binary
    {g : IndexedGrammar T} [Fintype g.nt]
    {A B C : g.nt} {stack : List g.flag} {u v : List T}
    {r : IRule T g.nt g.flag}
    (hr : r ∈ g.rules) (hlhs : r.lhs = A) (hc : r.consume = none)
    (hrhs : r.rhs =
      [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none])
    (leftParse : NFParse g B stack u) (rightParse : NFParse g C stack v)
    (leftRuns : OrdinaryScheduleRuns leftParse)
    (rightRuns : OrdinaryScheduleRuns rightParse) :
    ProtectedScheduleRun
      (NFParse.binary hr hlhs hc hrhs leftParse rightParse) :=
  ProtectedScheduleRunAtOrBelow.toProtectedScheduleRun
    (protectedScheduleRun_binary_atOrBelow hr hlhs hc hrhs leftParse rightParse
      leftRuns rightRuns)

/-- Complete protected-mode constructor dispatch under the mutual strong-induction hypothesis. -/
public theorem protectedScheduleRun_of_smaller
    {g : IndexedGrammar T} [Fintype g.nt]
    {A : g.nt} {stack : List g.flag} {w : List T}
    (parse : NFParse g A stack w)
    (ih : ∀ {B : g.nt} {residualStack : List g.flag} {v : List T}
      (q : NFParse g B residualStack v), q.nodeCount < parse.nodeCount →
        OrdinaryScheduleRuns q)
    (overlayIH : ∀ {B : g.nt} {residualStack : List g.flag} {v : List T}
      (q : NFParse g B residualStack v), q.nodeCount < parse.nodeCount →
        OverlayScheduleRun q) :
    ProtectedScheduleRun parse := by
  cases parse with
  | @binary A B C stack u v r hr hlhs hc hrhs leftParse rightParse =>
      apply protectedScheduleRun_binary hr hlhs hc hrhs leftParse rightParse
      · apply ih leftParse
        simp only [NFParse.nodeCount]
        omega
      · apply ih rightParse
        simp only [NFParse.nodeCount]
        omega
  | @pop A B f stack w r hr hlhs hc hrhs rest =>
      apply protectedScheduleRun_atomicPop
        (NFParse.pop hr hlhs hc hrhs rest)
      · intro d hd
        rcases Finset.mem_image.mp hd with ⟨e, he, hed⟩
        omega
      · intro B residualStack residual hcount
        exact ih residual hcount
  | @push A B f stack w r hr hlhs hc hrhs rest =>
      let parent : NFParse g A stack w := .push hr hlhs hc hrhs rest
      change ProtectedScheduleRun parent
      by_cases hzero : 0 ∈ parent.eventDepths
      · apply protectedScheduleRun_pushFresh hr hlhs hc hrhs rest
          (by simpa [parent] using hzero)
        apply overlayIH rest
        simp [NFParse.nodeCount]
      · apply protectedScheduleRun_atomicPop parent
        · intro d hd
          exact Nat.pos_of_ne_zero (fun hd0 => hzero (hd0 ▸ hd))
        · intro C residualStack residual hcount
          exact ih residual hcount
  | @terminal A stack a r hr hlhs hc hrhs =>
      exact protectedScheduleRun_terminal_false hr hlhs hc hrhs

end Aho
end IndexedGrammar
