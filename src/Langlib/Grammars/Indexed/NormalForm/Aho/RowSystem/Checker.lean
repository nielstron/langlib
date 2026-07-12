module

public import Langlib.Grammars.Indexed.NormalForm.Aho.Machine.BoundaryScans
public import Langlib.Automata.LinearBounded.CertifiedRowSystem

@[expose]
public section

/-!
# Certified row checker for Aho's machine

The packed rows in `Aho.Machine.PaddedRows` retain the active work-head bit. Consequently every
composite move is a regular relation on two aligned rows. Insertions and deletions only shift the
remaining suffix by at most two slots: the checker below remembers the preceding two old and new
slots.

The per-cell certificate chooses the finite composite rule and the phase reached after each of the
twenty-one logical slots in that cell. Phase choices only resolve regular-expression boundaries; all
grammar predicates, symbols, active bits, input-consumption bits, and delayed suffix equalities are
checked by the finite control.
-/

open List Relation Classical

variable {T : Type}

namespace IndexedGrammar
namespace Aho

/-! ## Logical-slot verifier -/

/-- Finite phases shared by the fourteen composite-certificate cases. -/
public inductive WorkPhase where
  | prefix
  | marked
  | stage1
  | stage2
  | stage3
  | popBeta
  | returnBeta
  | minus1First
  | suffixSame
  | suffixPlus1
  | suffixPlus2
  | suffixMinus1
  | suffixMinus2
  | dead
deriving DecidableEq, Fintype

/-- Two slots of lookbehind on each aligned work track.  The outer option distinguishes "no
slot has been read" from a previously read padding blank. -/
public structure WorkHistory (g : IndexedGrammar T) where
  old1 : Option (Option (WorkSlot g))
  old2 : Option (Option (WorkSlot g))
  new1 : Option (Option (WorkSlot g))
  new2 : Option (Option (WorkSlot g))

public noncomputable instance WorkHistory.instDecidableEq {g : IndexedGrammar T} :
    DecidableEq (WorkHistory g) :=
  Classical.decEq _

public noncomputable instance WorkHistory.instFintype {g : IndexedGrammar T}
    [Fintype T] [Fintype g.nt] : Fintype (WorkHistory g) := by
  classical
  let encode : WorkHistory g →
      Option (Option (WorkSlot g)) × Option (Option (WorkSlot g)) ×
        Option (Option (WorkSlot g)) × Option (Option (WorkSlot g)) :=
    fun h => (h.old1, h.old2, h.new1, h.new2)
  exact Fintype.ofInjective encode (by
    intro x y h
    cases x
    cases y
    simp_all [encode])

/-- State of the logical-slot scan.  `oldEnded` and `newEnded` enforce the canonical
`some* none*` padding shape. -/
public structure WorkScanState (g : IndexedGrammar T) where
  phase : WorkPhase
  history : WorkHistory g
  oldEnded : Bool
  newEnded : Bool

public noncomputable instance WorkScanState.instDecidableEq {g : IndexedGrammar T} :
    DecidableEq (WorkScanState g) :=
  Classical.decEq _

public noncomputable instance WorkScanState.instFintype {g : IndexedGrammar T}
    [Fintype T] [Fintype g.nt] : Fintype (WorkScanState g) := by
  classical
  let encode : WorkScanState g → WorkPhase × WorkHistory g × Bool × Bool :=
    fun s => (s.phase, s.history, s.oldEnded, s.newEnded)
  exact Fintype.ofInjective encode (by
    intro x y h
    cases x
    cases y
    simp_all [encode])

public def initialWorkScan (g : IndexedGrammar T) : WorkScanState g :=
  ⟨.prefix, ⟨none, none, none, none⟩, false, false⟩

public def inactive (z : WorkSym g) : Option (WorkSlot g) :=
  some ⟨false, z⟩

public def active (z : WorkSym g) : Option (WorkSlot g) :=
  some ⟨true, z⟩

public def InactiveOpt : Option (WorkSlot g) → Prop
  | none => True
  | some s => s.active = false

public def InactiveSome (x : Option (WorkSlot g)) : Prop :=
  ∃ z, x = inactive z

public def InactiveNonIndex (x : Option (WorkSlot g)) : Prop :=
  ∃ z, x = inactive z ∧ z.isIndex = false

public def SameInactiveSome (x y : Option (WorkSlot g)) : Prop :=
  ∃ z, x = inactive z ∧ y = inactive z

public def ProductiveMarked (old new : Option (WorkSlot g)) : Prop :=
  ∃ R d,
    old = inactive (WorkSym.index R d) ∧
      new = inactive (WorkSym.index R d.markUsed)

public def ProductiveBoundaryOK (h : WorkHistory g) : Prop :=
  match h.old1, h.new1 with
  | some (some ⟨false, WorkSym.index R d⟩), some new =>
      new = inactive (WorkSym.index R d.markUsed)
  | _, _ => True

public def Boundary (old new : Option (WorkSlot g)) : Prop :=
  old = inactive WorkSym.dollar ∧ new = inactive WorkSym.dollar

public def sameSuffix (old new : Option (WorkSlot g)) : Prop :=
  old = new ∧ InactiveOpt old

public def plus1Suffix (h : WorkHistory g)
    (old new : Option (WorkSlot g)) : Prop :=
  InactiveOpt old ∧ InactiveOpt new ∧ h.old1 = some new

public def plus2Suffix (h : WorkHistory g)
    (old new : Option (WorkSlot g)) : Prop :=
  InactiveOpt old ∧ InactiveOpt new ∧ h.old2 = some new

public def minus1Suffix (h : WorkHistory g)
    (old new : Option (WorkSlot g)) : Prop :=
  InactiveOpt old ∧ InactiveOpt new ∧ h.new1 = some old

public def minus2Suffix (h : WorkHistory g)
    (old new : Option (WorkSlot g)) : Prop :=
  InactiveOpt old ∧ InactiveOpt new ∧ h.new2 = some old

public def sameSymbolFirstMinus1 (h : WorkHistory g)
    (old new : Option (WorkSlot g)) : Prop :=
  InactiveOpt new ∧
    ∃ z, old = inactive z ∧ h.new1 = some (active z)

public def prefixEdge (productive : Bool) (phase next : WorkPhase)
    (h : WorkHistory g) (old new : Option (WorkSlot g)) : Prop :=
  match phase, next with
  | .prefix, .prefix => SameInactiveSome old new
  | .prefix, .marked => productive = true ∧ ProductiveMarked old new
  | .prefix, .stage1 =>
      Boundary old new ∧ (productive = false ∨ ProductiveBoundaryOK h)
  | .marked, .stage1 => productive = true ∧ Boundary old new
  | _, _ => False

public def insertOneEdge (productive : Bool)
    (oldFocus newFocus inserted : WorkSym g) (needOldSome : Bool)
    (phase next : WorkPhase) (h : WorkHistory g)
    (old new : Option (WorkSlot g)) : Prop :=
  prefixEdge productive phase next h old new ∨
    (phase = .stage1 ∧ next = .stage2 ∧
      old = active oldFocus ∧ new = active newFocus) ∨
    (phase = .stage2 ∧ next = .suffixPlus1 ∧
      (if needOldSome then InactiveSome old else InactiveOpt old) ∧
      new = inactive inserted) ∨
    (phase = .suffixPlus1 ∧ next = .suffixPlus1 ∧
      plus1Suffix h old new)

public def replaceOneEdge (productive : Bool)
    (oldFocus newFocus : WorkSym g)
    (phase next : WorkPhase) (h : WorkHistory g)
    (old new : Option (WorkSlot g)) : Prop :=
  prefixEdge productive phase next h old new ∨
    (phase = .stage1 ∧ next = .suffixSame ∧
      old = active oldFocus ∧ new = active newFocus) ∨
    (phase = .suffixSame ∧ next = .suffixSame ∧ sameSuffix old new)

public def replaceTwoEdge
    (oldFocus newFocus oldNext newNext : WorkSym g)
    (phase next : WorkPhase) (h : WorkHistory g)
    (old new : Option (WorkSlot g)) : Prop :=
  prefixEdge false phase next h old new ∨
    (phase = .stage1 ∧ next = .stage2 ∧
      old = active oldFocus ∧ new = active newFocus) ∨
    (phase = .stage2 ∧ next = .suffixSame ∧
      old = inactive oldNext ∧ new = inactive newNext) ∨
    (phase = .suffixSame ∧ next = .suffixSame ∧ sameSuffix old new)

public def deleteOneEdge
    (focusOK : Option (WorkSlot g) → Prop)
    (phase next : WorkPhase) (h : WorkHistory g)
    (old new : Option (WorkSlot g)) : Prop :=
  prefixEdge false phase next h old new ∨
    (phase = .stage1 ∧ next = .minus1First ∧
      focusOK old ∧ ∃ z, new = active z) ∨
    (phase = .minus1First ∧ next = .suffixMinus1 ∧
      sameSymbolFirstMinus1 h old new) ∨
    (phase = .suffixMinus1 ∧ next = .suffixMinus1 ∧
      minus1Suffix h old new)

/-- The finite aligned-slot edge relation for one Aho composite certificate. -/
public def WorkEdge (g : IndexedGrammar T) [Fintype g.nt]
    (cert : CompositeCert g) (phase next : WorkPhase) (h : WorkHistory g)
    (old new : Option (WorkSlot g)) : Prop :=
  match cert with
  | .plainBinary A B C =>
      AugBinary g A B C ∧
        insertOneEdge true (WorkSym.plain A) (WorkSym.plain B) (WorkSym.plain C)
          false phase next h old new
  | .plainTerminal A a =>
      AugTerminal g A a ∧
        replaceOneEdge true (WorkSym.plain A) (WorkSym.terminal a)
          phase next h old new
  | .plainPushSkip A B f =>
      AugPush g A B f ∧
        replaceOneEdge false (WorkSym.plain A) (WorkSym.plain B)
          phase next h old new
  | .plainPushUse A B f =>
      AugPush g A B f ∧
        insertOneEdge false (WorkSym.plain A) (WorkSym.live B)
          (WorkSym.index (cflagBase g f) .firstPending) false phase next h old new
  | .liveBinaryBoth A B C =>
      AugBinary g A B C ∧
        insertOneEdge true (WorkSym.live A) (WorkSym.live B) (WorkSym.live C)
          true phase next h old new
  | .liveBinaryLeft A B C =>
      AugBinary g A B C ∧
        insertOneEdge true (WorkSym.live A) (WorkSym.live B) (WorkSym.plain C)
          true phase next h old new
  | .liveBinaryRight A B C =>
      AugBinary g A B C ∧
        insertOneEdge true (WorkSym.live A) (WorkSym.plain B) (WorkSym.live C)
          true phase next h old new
  | .livePushFresh A B f =>
      AugPush g A B f ∧
        insertOneEdge false (WorkSym.live A) (WorkSym.live B)
          (WorkSym.index (cflagBase g f) .laterPending) true phase next h old new
  | .livePushCompress A B f R d =>
      AugPush g A B f ∧ (cflagComp g (cflagBase g f) R).Nonempty ∧
        replaceTwoEdge (WorkSym.live A) (WorkSym.live B) (WorkSym.index R d)
          (WorkSym.index (cflagComp g (cflagBase g f) R) d) phase next h old new
  | .popPlain R d A B =>
      R A B = true ∧
        (prefixEdge false phase next h old new ∨
          (phase = .stage1 ∧ next = .popBeta ∧
            old = active (WorkSym.live A) ∧ InactiveSome new) ∨
          (phase = .popBeta ∧ next = .popBeta ∧
            InactiveNonIndex old ∧
            h.new1 = some old ∧ InactiveOpt new) ∨
          (phase = .popBeta ∧ next = .stage2 ∧
            old = inactive (WorkSym.index R d) ∧
            h.new1 = some (inactive (WorkSym.index R d.markUsed)) ∧
            new = inactive WorkSym.dollar) ∨
          (phase = .stage2 ∧ next = .stage3 ∧
            InactiveOpt old ∧ new = active (WorkSym.plain B)) ∨
          (phase = .stage3 ∧ next = .suffixPlus2 ∧
            InactiveOpt old ∧ new = inactive WorkSym.close) ∨
          (phase = .suffixPlus2 ∧ next = .suffixPlus2 ∧
            plus2Suffix h old new) ∨
          (phase = .stage1 ∧ next = .minus1First ∧
            old = active (WorkSym.live A) ∧ new = active (WorkSym.plain B)) ∨
          (phase = .minus1First ∧ next = .suffixMinus1 ∧
            old = inactive (WorkSym.index R d) ∧ InactiveOpt new) ∨
          (phase = .suffixMinus1 ∧ next = .suffixMinus1 ∧
            minus1Suffix h old new))
  | .popLive R d A B =>
      R A B = true ∧ d.later = true ∧
        (prefixEdge false phase next h old new ∨
          (phase = .stage1 ∧ next = .popBeta ∧
            old = active (WorkSym.live A) ∧ InactiveSome new) ∨
          (phase = .popBeta ∧ next = .popBeta ∧
            InactiveNonIndex old ∧
            h.new1 = some old ∧ InactiveOpt new) ∨
          (phase = .popBeta ∧ next = .stage2 ∧
            old = inactive (WorkSym.index R d) ∧
            h.new1 = some (inactive (WorkSym.index R d.markUsed)) ∧
            new = inactive WorkSym.dollar) ∨
          (phase = .stage2 ∧ next = .stage3 ∧
            InactiveOpt old ∧ new = active (WorkSym.live B)) ∨
          (phase = .stage3 ∧ next = .suffixPlus2 ∧
            InactiveOpt old ∧ new = inactive WorkSym.close) ∨
          (phase = .suffixPlus2 ∧ next = .suffixPlus2 ∧
            plus2Suffix h old new) ∨
          (phase = .stage1 ∧ next = .minus1First ∧
            old = active (WorkSym.live A) ∧ new = active (WorkSym.live B)) ∨
          (phase = .minus1First ∧ next = .suffixMinus1 ∧
            old = inactive (WorkSym.index R d) ∧ InactiveOpt new) ∨
          (phase = .suffixMinus1 ∧ next = .suffixMinus1 ∧
            minus1Suffix h old new))
  | .matchTerminal a =>
      deleteOneEdge (fun old => old = active (WorkSym.terminal a))
        phase next h old new
  | .eraseIndex R d =>
      d.erasable = true ∧
        deleteOneEdge (fun old => old = active (WorkSym.index R d))
          phase next h old new
  | .returnFrame =>
      prefixEdge false phase next h old new ∨
        (phase = .stage1 ∧ next = .returnBeta ∧
          ∃ z, z ≠ WorkSym.dollar ∧ old = inactive z ∧ new = active z) ∨
        (phase = .returnBeta ∧ next = .returnBeta ∧
          sameSuffix old new ∧ old ≠ inactive WorkSym.dollar) ∨
        (phase = .returnBeta ∧ next = .stage2 ∧
          old = inactive WorkSym.dollar ∧ InactiveOpt new) ∨
        (phase = .stage2 ∧ next = .suffixMinus2 ∧
          old = active WorkSym.close ∧ InactiveOpt new) ∨
        (phase = .suffixMinus2 ∧ next = .suffixMinus2 ∧
          minus2Suffix h old new)

/-- The grammar-side side condition carried by a composite certificate. -/
public def CertEnabled (g : IndexedGrammar T) [Fintype g.nt] : CompositeCert g → Prop
  | .plainBinary A B C => AugBinary g A B C
  | .plainTerminal A a => AugTerminal g A a
  | .plainPushSkip A B f => AugPush g A B f
  | .plainPushUse A B f => AugPush g A B f
  | .liveBinaryBoth A B C => AugBinary g A B C
  | .liveBinaryLeft A B C => AugBinary g A B C
  | .liveBinaryRight A B C => AugBinary g A B C
  | .livePushFresh A B f => AugPush g A B f
  | .livePushCompress A B f R _ =>
      AugPush g A B f ∧ (cflagComp g (cflagBase g f) R).Nonempty
  | .popPlain R _ A B => R A B = true
  | .popLive R d A B => R A B = true ∧ d.later = true
  | .matchTerminal _ => True
  | .eraseIndex _ d => d.erasable = true
  | .returnFrame => True

/-- Composite rules whose `alpha` prefix is changed by Aho's productive mark operation. -/
public def CompositeCert.productive : CompositeCert g → Bool
  | .plainBinary .. => true
  | .plainTerminal .. => true
  | .liveBinaryBoth .. => true
  | .liveBinaryLeft .. => true
  | .liveBinaryRight .. => true
  | _ => false

public theorem workEdge_prefix_iff (g : IndexedGrammar T) [Fintype g.nt]
    (cert : CompositeCert g) (phase next : WorkPhase) (h : WorkHistory g)
    (old new : Option (WorkSlot g))
    (hphase : phase = .prefix ∨ phase = .marked) :
    WorkEdge g cert phase next h old new ↔
      CertEnabled g cert ∧ prefixEdge cert.productive phase next h old new := by
  rcases hphase with rfl | rfl <;>
    cases cert <;> simp [WorkEdge, CertEnabled, CompositeCert.productive,
      insertOneEdge, replaceOneEdge, replaceTwoEdge, deleteOneEdge, and_assoc]

public def paddingOK (ended : Bool) (slot : Option (WorkSlot g)) : Prop :=
  ended = false ∨ slot = none

public def updateHistory (h : WorkHistory g)
    (old new : Option (WorkSlot g)) : WorkHistory g :=
  ⟨some old, h.old1, some new, h.new1⟩

/-- Execute one aligned logical-slot check. -/
public noncomputable def workSlotStep (g : IndexedGrammar T) [Fintype g.nt]
    (cert : CompositeCert g) (state : WorkScanState g)
    (old new : Option (WorkSlot g)) (next : WorkPhase) : WorkScanState g := by
  classical
  exact if state.phase ≠ .dead ∧
      paddingOK state.oldEnded old ∧ paddingOK state.newEnded new ∧
      WorkEdge g cert state.phase next state.history old new then
    ⟨next, updateHistory state.history old new,
      state.oldEnded || old.isNone, state.newEnded || new.isNone⟩
  else
    ⟨.dead, updateHistory state.history old new, true, true⟩

public theorem workSlotStep_prefix_same (g : IndexedGrammar T) [Fintype g.nt]
    (cert : CompositeCert g) (h : WorkHistory g) (z : WorkSym g)
    (henabled : CertEnabled g cert) :
    workSlotStep g cert ⟨.prefix, h, false, false⟩
        (inactive z) (inactive z) .prefix =
      ⟨.prefix, updateHistory h (inactive z) (inactive z), false, false⟩ := by
  classical
  unfold workSlotStep
  rw [if_pos]
  · rfl
  · refine ⟨by simp, by simp [paddingOK], by simp [paddingOK], ?_⟩
    rw [workEdge_prefix_iff g cert .prefix .prefix h _ _ (by simp)]
    simp [henabled, prefixEdge, SameInactiveSome]

public theorem workSlotStep_prefix_mark (g : IndexedGrammar T) [Fintype g.nt]
    (cert : CompositeCert g) (h : WorkHistory g) (R : CFlag g) (d : IndexMark)
    (henabled : CertEnabled g cert) (hproductive : cert.productive = true) :
    workSlotStep g cert ⟨.prefix, h, false, false⟩
        (inactive (WorkSym.index R d))
        (inactive (WorkSym.index R d.markUsed)) .marked =
      ⟨.marked, updateHistory h (inactive (WorkSym.index R d))
        (inactive (WorkSym.index R d.markUsed)), false, false⟩ := by
  classical
  unfold workSlotStep
  rw [if_pos]
  · rfl
  · refine ⟨by simp, by simp [paddingOK], by simp [paddingOK], ?_⟩
    rw [workEdge_prefix_iff g cert .prefix .marked h _ _ (by simp)]
    refine ⟨henabled, ?_⟩
    simp only [prefixEdge, hproductive, true_and]
    exact ⟨R, d, rfl, rfl⟩

public theorem workSlotStep_prefix_boundary (g : IndexedGrammar T) [Fintype g.nt]
    (cert : CompositeCert g) (h : WorkHistory g)
    (henabled : CertEnabled g cert)
    (hboundary : cert.productive = false ∨ ProductiveBoundaryOK h) :
    workSlotStep g cert ⟨.prefix, h, false, false⟩
        (inactive WorkSym.dollar) (inactive WorkSym.dollar) .stage1 =
      ⟨.stage1, updateHistory h (inactive WorkSym.dollar)
        (inactive WorkSym.dollar), false, false⟩ := by
  classical
  unfold workSlotStep
  rw [if_pos]
  · rfl
  · refine ⟨by simp, by simp [paddingOK], by simp [paddingOK], ?_⟩
    rw [workEdge_prefix_iff g cert .prefix .stage1 h _ _ (by simp)]
    simp [henabled, prefixEdge, Boundary, hboundary]

public theorem workSlotStep_marked_boundary (g : IndexedGrammar T) [Fintype g.nt]
    (cert : CompositeCert g) (h : WorkHistory g)
    (henabled : CertEnabled g cert) (hproductive : cert.productive = true) :
    workSlotStep g cert ⟨.marked, h, false, false⟩
        (inactive WorkSym.dollar) (inactive WorkSym.dollar) .stage1 =
      ⟨.stage1, updateHistory h (inactive WorkSym.dollar)
        (inactive WorkSym.dollar), false, false⟩ := by
  classical
  unfold workSlotStep
  rw [if_pos]
  · rfl
  · refine ⟨by simp, by simp [paddingOK], by simp [paddingOK], ?_⟩
    rw [workEdge_prefix_iff g cert .marked .stage1 h _ _ (by simp)]
    simp [henabled, prefixEdge, Boundary, hproductive]

/-- Run a list of aligned logical slots and phase choices. -/
public noncomputable def evalWorkSlots (g : IndexedGrammar T) [Fintype g.nt]
    (cert : CompositeCert g) : WorkScanState g →
      List (Option (WorkSlot g)) → List (Option (WorkSlot g)) →
      List WorkPhase → WorkScanState g
  | state, [], [], [] => state
  | state, old :: olds, new :: news, next :: choices =>
      evalWorkSlots g cert (workSlotStep g cert state old new next) olds news choices
  | state, _, _, _ => { state with phase := .dead }

public def historySame (h : WorkHistory g) (xs : List (WorkSym g)) : WorkHistory g :=
  xs.foldl (fun h z => updateHistory h (inactive z) (inactive z)) h

public theorem evalWorkSlots_prefix_same (g : IndexedGrammar T) [Fintype g.nt]
    (cert : CompositeCert g) (h : WorkHistory g) (xs : List (WorkSym g))
    (henabled : CertEnabled g cert) :
    evalWorkSlots g cert ⟨.prefix, h, false, false⟩
        (xs.map inactive) (xs.map inactive) (List.replicate xs.length .prefix) =
      ⟨.prefix, historySame h xs, false, false⟩ := by
  induction xs generalizing h with
  | nil => rfl
  | cons z xs ih =>
      simp only [List.map_cons, List.length_cons, List.replicate_succ, evalWorkSlots,
        historySame, List.foldl_cons]
      rw [workSlotStep_prefix_same g cert h z henabled]
      exact ih _

/-- Run the twenty-one logical slots packed in one physical row cell. -/
public noncomputable def evalWorkBlock (g : IndexedGrammar T) [Fintype g.nt]
    (cert : CompositeCert g) (state : WorkScanState g)
    (old new : WorkBlock g) (choices : Fin workWidth → WorkPhase) : WorkScanState g :=
  evalWorkSlots g cert state (List.ofFn old) (List.ofFn new) (List.ofFn choices)

public theorem evalWorkSlots_append (g : IndexedGrammar T) [Fintype g.nt]
    (cert : CompositeCert g) (state : WorkScanState g)
    (old₁ old₂ new₁ new₂ : List (Option (WorkSlot g)))
    (choices₁ choices₂ : List WorkPhase)
    (h₁ : old₁.length = new₁.length) (h₂ : old₁.length = choices₁.length) :
    evalWorkSlots g cert state (old₁ ++ old₂) (new₁ ++ new₂)
        (choices₁ ++ choices₂) =
      evalWorkSlots g cert (evalWorkSlots g cert state old₁ new₁ choices₁)
        old₂ new₂ choices₂ := by
  induction old₁ generalizing state new₁ choices₁ with
  | nil =>
      cases new₁ <;> cases choices₁ <;> simp_all [evalWorkSlots]
  | cons old old₁ ih =>
      cases new₁ with
      | nil => simp at h₁
      | cons new new₁ =>
          cases choices₁ with
          | nil => simp at h₂
          | cons choice choices₁ =>
              simp only [List.length_cons, Nat.succ.injEq] at h₁ h₂
              simp only [List.cons_append, evalWorkSlots]
              exact ih _ _ _ h₁ h₂

/-- Fold a list of physical blocks; useful for relating the cell checker to one flat slot scan. -/
public noncomputable def evalWorkBlocks (g : IndexedGrammar T) [Fintype g.nt]
    (cert : CompositeCert g) : WorkScanState g →
      List (WorkBlock g) → List (WorkBlock g) →
      List (Fin workWidth → WorkPhase) → WorkScanState g
  | state, [], [], [] => state
  | state, old :: olds, new :: news, choices :: rest =>
      evalWorkBlocks g cert (evalWorkBlock g cert state old new choices) olds news rest
  | state, _, _, _ => { state with phase := .dead }

/-- Extract all work blocks when every cell is in running form. -/
public def runBlocks {g : IndexedGrammar T} :
    List (RowCell g) → Option (List (WorkBlock g))
  | [] => some []
  | .run cell :: row => (runBlocks row).map (cell.block :: ·)
  | .input _ :: _ => none

/-- The consecutive packed blocks beginning at logical cell offset `cell`. -/
public def packedBlockList (g : IndexedGrammar T) (work : List (WorkSlot g))
    (cell : ℕ) (n : ℕ) : List (WorkBlock g) :=
  List.ofFn fun i : Fin n => packedCell workWidth work (cell + i.val)

@[simp] public theorem runBlocks_encodeRunRowFrom (g : IndexedGrammar T)
    (work : List (WorkSlot g)) (inputPos cell : ℕ) (w : List T) :
    runBlocks (encodeRunRowFrom g work inputPos cell w) =
      some (packedBlockList g work cell w.length) := by
  induction w generalizing cell with
  | nil => rfl
  | cons a w ih =>
      simp [encodeRunRowFrom, runBlocks, packedBlockList, List.ofFn_succ, ih,
        Nat.add_comm, Nat.add_left_comm]

/-- Reblock a flat phase function into one twenty-one-phase certificate per physical row cell. -/
public def phaseBlockList (n : ℕ) (phases : Fin (n * workWidth) → WorkPhase) :
    List (Fin workWidth → WorkPhase) :=
  List.ofFn fun i : Fin n => fun j : Fin workWidth =>
    phases ⟨i.val * workWidth + j.val, by
      calc
        i.val * workWidth + j.val < i.val * workWidth + workWidth :=
          Nat.add_lt_add_left j.isLt _
        _ = (i.val + 1) * workWidth := by simp [Nat.add_mul]
        _ ≤ n * workWidth := Nat.mul_le_mul_right workWidth (Nat.succ_le_of_lt i.isLt)⟩

@[simp] public theorem phaseBlockList_length (n : ℕ)
    (phases : Fin (n * workWidth) → WorkPhase) :
    (phaseBlockList n phases).length = n := by
  simp [phaseBlockList]

public theorem phaseBlockList_flatten (n : ℕ)
    (phases : Fin (n * workWidth) → WorkPhase) :
    (phaseBlockList n phases).flatMap List.ofFn = List.ofFn phases := by
  simpa [phaseBlockList, List.flatMap] using (List.ofFn_mul phases).symm

/-- The full aligned slot stream of a bounded logical work word. -/
public def paddedWork (n : ℕ) (work : List (WorkSlot g)) :
    List (Option (WorkSlot g)) :=
  List.ofFn fun k : Fin (n * workWidth) => work[k.val]?

@[simp] public theorem paddedWork_length (n : ℕ) (work : List (WorkSlot g)) :
    (paddedWork n work).length = n * workWidth := by
  simp [paddedWork]

public theorem paddedWork_eq_append (n : ℕ) (work : List (WorkSlot g))
    (hwork : work.length ≤ n * workWidth) :
    paddedWork n work = work.map some ++
      List.replicate (n * workWidth - work.length) none := by
  apply List.ext_getElem
  · simp [paddedWork, hwork]
  · intro k hk₁ hk₂
    simp only [paddedWork, List.getElem_ofFn]
    by_cases hk : k < work.length
    · rw [List.getElem_append_left (by simp [hk])]
      simp [hk]
    · have hge : work.length ≤ k := Nat.le_of_not_gt hk
      rw [List.getElem_append_right (by simp [hge])]
      simp [List.getElem?_eq_none hge]

public def lastOldNone (h : WorkHistory g) : Prop := h.old1 = some none
public def lastTwoOldNone (h : WorkHistory g) : Prop :=
  h.old1 = some none ∧ h.old2 = some none
public def lastNewNone (h : WorkHistory g) : Prop := h.new1 = some none
public def lastTwoNewNone (h : WorkHistory g) : Prop :=
  h.new1 = some none ∧ h.new2 = some none

/-- Successful terminal phases, including the padding needed to prevent truncated insertions. -/
public noncomputable def workScanDone (state : WorkScanState g) : Bool :=
  decide <| match state.phase with
  | .suffixSame => True
  | .suffixPlus1 => lastOldNone state.history
  | .suffixPlus2 => lastTwoOldNone state.history
  | .suffixMinus1 => lastNewNone state.history
  | .suffixMinus2 => lastTwoNewNone state.history
  | _ => False

/-! ## Physical-row verifier -/

public inductive InputPhase where
  | prefix
  | tail
  | matched
  | dead
deriving DecidableEq, Fintype

public noncomputable def inputStep (cert : CompositeCert g) (phase : InputPhase)
    (old new : RunCell g) : InputPhase :=
  if old.input ≠ new.input then .dead else
  match cert, phase, old.consumed, new.consumed with
  | .matchTerminal _, .prefix, true, true => .prefix
  | .matchTerminal a, .prefix, false, true => if old.input = a then .matched else .dead
  | .matchTerminal _, .matched, false, false => .matched
  | .matchTerminal _, _, _, _ => .dead
  | _, .prefix, true, true => .prefix
  | _, .prefix, false, false => .tail
  | _, .tail, false, false => .tail
  | _, _, _, _ => .dead

public noncomputable def inputDone (cert : CompositeCert g) : InputPhase → Bool
  | .prefix => decide (match cert with | .matchTerminal _ => False | _ => True)
  | .tail => decide (match cert with | .matchTerminal _ => False | _ => True)
  | .matched => decide (match cert with | .matchTerminal _ => True | _ => False)
  | .dead => false

/-- Fold the independent immutable-input/consumption-bit check over running cells. -/
public noncomputable def evalInputBlocks (cert : CompositeCert g) : InputPhase →
    List (RunCell g) → List (RunCell g) → InputPhase
  | q, [], [] => q
  | q, old :: olds, new :: news =>
      evalInputBlocks cert (inputStep cert q old new) olds news
  | _, _, _ => .dead

/-- One physical-row certificate.  The same composite certificate must be repeated along the row;
the phase block may vary from cell to cell. -/
public inductive RowCert (g : IndexedGrammar T) where
  | init : RowCert g
  | composite : CompositeCert g → (Fin workWidth → WorkPhase) → RowCert g

public noncomputable instance RowCert.instDecidableEq {g : IndexedGrammar T} :
    DecidableEq (RowCert g) :=
  Classical.decEq _

public noncomputable instance RowCert.instFintype {g : IndexedGrammar T}
    [Fintype T] [Fintype g.nt] [Fintype g.flag] : Fintype (RowCert g) := by
  classical
  let encode : RowCert g → Unit ⊕ (CompositeCert g × (Fin workWidth → WorkPhase))
    | .init => Sum.inl ()
    | .composite cert phases => Sum.inr (cert, phases)
  exact Fintype.ofInjective encode (by
    intro x y h
    cases x <;> cases y <;> simp_all [encode])

public inductive RowState (g : IndexedGrammar T) where
  | start
  | init : BoundaryScanState → RowState g
  | composite : CompositeCert g → InputPhase → WorkScanState g → RowState g
  | dead

public noncomputable instance RowState.instDecidableEq {g : IndexedGrammar T} :
    DecidableEq (RowState g) :=
  Classical.decEq _

public noncomputable instance RowState.instFintype {g : IndexedGrammar T}
    [Fintype T] [Fintype g.nt] [Fintype g.flag] : Fintype (RowState g) := by
  classical
  let encode : RowState g →
      Unit ⊕ BoundaryScanState ⊕ (CompositeCert g × InputPhase × WorkScanState g) ⊕ Unit
    | .start => Sum.inl ()
    | .init q => Sum.inr (Sum.inl q)
    | .composite cert iq wq => Sum.inr (Sum.inr (Sum.inl (cert, iq, wq)))
    | .dead => Sum.inr (Sum.inr (Sum.inr ()))
  exact Fintype.ofInjective encode (by
    intro x y h
    cases x <;> cases y <;> simp_all [encode])

public noncomputable def compositeCell (g : IndexedGrammar T) [Fintype g.nt]
    (cert : CompositeCert g) (input : InputPhase) (work : WorkScanState g)
    (old new : RowCell g) (phases : Fin workWidth → WorkPhase) : RowState g :=
  match old, new with
  | .run old, .run new =>
      .composite cert (inputStep cert input old new)
        (evalWorkBlock g cert work old.block new.block phases)
  | _, _ => .dead

/-- One physical-cell transition of the complete row verifier. -/
public noncomputable def rowStepCell (g : IndexedGrammar T) [Fintype g.nt] :
    RowState g → RowCell g → RowCell g → RowCert g → RowState g
  | .start, old, new, .init => .init (initScanCell g .first old new)
  | .init q, old, new, .init => .init (initScanCell g q old new)
  | .start, old, new, .composite cert phases =>
      compositeCell g cert .prefix (initialWorkScan g) old new phases
  | .composite cert input work, old, new, .composite cert' phases =>
      if cert = cert' then compositeCell g cert input work old new phases else .dead
  | _, _, _, _ => .dead

@[simp] public theorem rowStepCell_composite_same (g : IndexedGrammar T) [Fintype g.nt]
    (cert : CompositeCert g) (input : InputPhase) (work : WorkScanState g)
    (old new : RunCell g) (phases : Fin workWidth → WorkPhase) :
    rowStepCell g (.composite cert input work) (.run old) (.run new)
        (.composite cert phases) =
      .composite cert (inputStep cert input old new)
        (evalWorkBlock g cert work old.block new.block phases) := by
  classical
  simp [rowStepCell, compositeCell]

@[simp] public theorem rowStepCell_composite_start (g : IndexedGrammar T) [Fintype g.nt]
    (cert : CompositeCert g) (old new : RunCell g)
    (phases : Fin workWidth → WorkPhase) :
    rowStepCell g .start (.run old) (.run new) (.composite cert phases) =
      .composite cert (inputStep cert .prefix old new)
        (evalWorkBlock g cert (initialWorkScan g) old.block new.block phases) := by
  rfl

public noncomputable def rowStepDone : RowState g → Bool
  | .init .tail => true
  | .composite cert input work => inputDone cert input && workScanDone work
  | _ => false

/-- The certified row system implementing initialized and composite Aho steps. -/
public noncomputable def ahoRowSystem (g : IndexedGrammar T) [Fintype g.nt] :
    CertifiedRowSystem T (RowCell g) (RowCert g) (RowState g) BoundaryScanState where
  inputCell := RowCell.input
  stepStart := .start
  stepCell := rowStepCell g
  stepDone := rowStepDone
  finalStart := .first
  finalCell := finalScanCell g
  finalDone := fun q => decide (q = .tail)

@[simp] public theorem ahoRowSystem_stepCell (g : IndexedGrammar T) [Fintype g.nt]
    (q : RowState g) (old new : RowCell g) (cert : RowCert g) :
    (ahoRowSystem g).stepCell q old new cert = rowStepCell g q old new cert := rfl

public def RowState.Closed : RowState g → Prop
  | .composite _ _ _ => True
  | .dead => True
  | _ => False

public theorem rowStepCell_closed (g : IndexedGrammar T) [Fintype g.nt]
    {state : RowState g} (hstate : state.Closed)
    (old new : RowCell g) (cert : RowCert g) :
    (rowStepCell g state old new cert).Closed := by
  cases state with
  | start => simp [RowState.Closed] at hstate
  | init q => simp [RowState.Closed] at hstate
  | dead => simp [rowStepCell, RowState.Closed]
  | composite chosen input work =>
      cases cert with
      | init => simp [rowStepCell, RowState.Closed]
      | composite chosen' phases =>
          classical
          by_cases hcert : chosen = chosen'
          · subst chosen'
            cases old <;> cases new <;>
              simp [rowStepCell, compositeCell, RowState.Closed]
          · simp [rowStepCell, hcert, RowState.Closed]

public theorem evalStep_closed (g : IndexedGrammar T) [Fintype g.nt]
    {state : RowState g} (hstate : state.Closed)
    (old new : List (RowCell g)) (certs : List (RowCert g))
    {result : RowState g}
    (h : (ahoRowSystem g).evalStep state old new certs = some result) :
    result.Closed := by
  induction old generalizing state new certs with
  | nil =>
      cases new <;> cases certs <;>
        simp [CertifiedRowSystem.evalStep] at h
      simpa [h] using hstate
  | cons old olds ih =>
      cases new with
      | nil => simp [CertifiedRowSystem.evalStep] at h
      | cons new news =>
          cases certs with
          | nil => simp [CertifiedRowSystem.evalStep] at h
          | cons cert certs =>
              simp only [CertifiedRowSystem.evalStep, ahoRowSystem] at h
              exact ih (rowStepCell_closed g hstate old new cert) _ _ h

public theorem evalStep_init_from (g : IndexedGrammar T) [Fintype g.nt]
    (q : BoundaryScanState) (old new : List (RowCell g))
    (hlen : old.length = new.length) :
    (ahoRowSystem g).evalStep (.init q) old new
        (List.replicate old.length (.init : RowCert g)) =
      some (.init (evalInitScan g q old new)) := by
  induction old generalizing new q with
  | nil =>
      cases new <;> simp_all [CertifiedRowSystem.evalStep, evalInitScan]
  | cons old olds ih =>
      cases new with
      | nil => simp at hlen
      | cons new news =>
          simp only [List.length_cons, Nat.succ.injEq] at hlen
          simp only [ahoRowSystem, evalInitScan]
          exact ih _ _ hlen

public theorem evalStep_init_start (g : IndexedGrammar T) [Fintype g.nt]
    (old new : List (RowCell g)) (hne : old ≠ [])
    (hlen : old.length = new.length) :
    (ahoRowSystem g).evalStep .start old new
        (List.replicate old.length (.init : RowCert g)) =
      some (.init (evalInitScan g .first old new)) := by
  cases old with
  | nil => exact (hne rfl).elim
  | cons old olds =>
      cases new with
      | nil => simp at hlen
      | cons new news =>
          simp only [List.length_cons, Nat.succ.injEq] at hlen
          simp only [ahoRowSystem, evalInitScan]
          exact evalStep_init_from g (initScanCell g .first old new) olds news hlen

private theorem evalStep_init_sound_from (g : IndexedGrammar T) [Fintype g.nt]
    (q q' : BoundaryScanState) (old new : List (RowCell g)) (certs : List (RowCert g))
    (h : (ahoRowSystem g).evalStep (.init q) old new certs = some (.init q')) :
    evalInitScan g q old new = q' := by
  induction old generalizing q q' new certs with
  | nil =>
      cases new <;> cases certs <;>
        simp [CertifiedRowSystem.evalStep, evalInitScan] at h ⊢
      exact h
  | cons old olds ih =>
      cases new with
      | nil => simp [CertifiedRowSystem.evalStep] at h
      | cons new news =>
          cases certs with
          | nil => simp [CertifiedRowSystem.evalStep] at h
          | cons cert certs =>
              cases cert with
              | composite chosen phases =>
                  simp only [CertifiedRowSystem.evalStep, ahoRowSystem, rowStepCell] at h
                  have hclosed := evalStep_closed g (by simp [RowState.Closed])
                    olds news certs h
                  simp [RowState.Closed] at hclosed
              | init =>
                  simp only [CertifiedRowSystem.evalStep, ahoRowSystem, rowStepCell] at h
                  simp only [evalInitScan]
                  exact ih _ _ _ _ h

public theorem evalStep_init_sound (g : IndexedGrammar T) [Fintype g.nt]
    (old new : List (RowCell g)) (certs : List (RowCert g)) (q : BoundaryScanState)
    (h : (ahoRowSystem g).evalStep .start old new certs = some (.init q)) :
    evalInitScan g .first old new = q := by
  cases old with
  | nil =>
      cases new <;> cases certs <;>
        simp [CertifiedRowSystem.evalStep] at h
  | cons old olds =>
      cases new with
      | nil => simp [CertifiedRowSystem.evalStep] at h
      | cons new news =>
          cases certs with
          | nil => simp [CertifiedRowSystem.evalStep] at h
          | cons cert certs =>
              cases cert with
              | composite chosen phases =>
                  simp only [CertifiedRowSystem.evalStep, ahoRowSystem, rowStepCell] at h
                  have hs :
                      (compositeCell g chosen .prefix (initialWorkScan g)
                        old new phases).Closed := by
                    cases old <;> cases new <;>
                      simp [compositeCell, RowState.Closed]
                  have hclosed : (RowState.init q).Closed :=
                    evalStep_closed g hs olds news certs h
                  simp [RowState.Closed] at hclosed
              | init =>
                  simp only [CertifiedRowSystem.evalStep, ahoRowSystem, rowStepCell] at h
                  simp only [evalInitScan]
                  exact evalStep_init_sound_from g _ _ _ _ _ h

/-- Every semantic initialization step has a certified-row witness. -/
public theorem rowStep_of_paddedInitStep (g : IndexedGrammar T) [Fintype g.nt]
    {old new : List (RowCell g)} (h : PaddedInitStep g old new) :
    (ahoRowSystem g).RowStep old new := by
  rcases h with ⟨w, hw, rfl, rfl⟩
  refine ⟨List.replicate w.length (.init : RowCert g), .init .tail, ?_, rfl⟩
  have hscan : evalInitScan g .first (inputRow g w)
      (encodeRunRow g w (initialConfig g)) = .tail :=
    (evalInitScan_iff_paddedInitStep g _ _).2 ⟨w, hw, rfl, rfl⟩
  have heval := evalStep_init_start g (inputRow g w)
    (encodeRunRow g w (initialConfig g)) (by simpa [inputRow] using hw) (by simp)
  rw [hscan] at heval
  simpa [ahoRowSystem, inputRow] using heval

/-- If a successful certified scan finishes in initialization mode, it is exactly an
initialization row step. -/
public theorem paddedInitStep_of_evalStep_init (g : IndexedGrammar T) [Fintype g.nt]
    {old new : List (RowCell g)} {certs : List (RowCert g)} {q : BoundaryScanState}
    (heval : (ahoRowSystem g).evalStep .start old new certs = some (.init q))
    (hdone : rowStepDone (.init q : RowState g) = true) :
    PaddedInitStep g old new := by
  have hq : q = .tail := by
    cases q <;> simp [rowStepDone] at hdone ⊢
  subst q
  apply (evalInitScan_iff_paddedInitStep g old new).1
  exact evalStep_init_sound g old new certs .tail heval

public theorem evalFinal_ahoRowSystem (g : IndexedGrammar T) [Fintype g.nt]
    (q : BoundaryScanState) (row : List (RowCell g)) :
    (ahoRowSystem g).evalFinal q row = evalFinalScan g q row := by
  induction row generalizing q with
  | nil => rfl
  | cons cell row ih =>
      simp only [CertifiedRowSystem.evalFinal, List.foldl_cons, evalFinalScan]
      exact ih _

/-- The target component of the certified system is exactly Aho's final padded row. -/
public theorem final_ahoRowSystem_iff (g : IndexedGrammar T) [Fintype g.nt]
    (row : List (RowCell g)) :
    (ahoRowSystem g).Final row ↔ FinalRow g row := by
  rw [CertifiedRowSystem.Final, evalFinal_ahoRowSystem]
  simp only [ahoRowSystem]
  rw [show (decide (evalFinalScan g .first row = BoundaryScanState.tail) = true) ↔
      evalFinalScan g .first row = .tail by simp]
  exact evalFinalScan_iff_finalRow g row

end Aho
end IndexedGrammar
