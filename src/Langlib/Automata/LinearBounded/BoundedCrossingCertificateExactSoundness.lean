module

public import Langlib.Automata.LinearBounded.BoundedCrossing
public import Langlib.Automata.LinearBounded.BoundedCrossingCertificateSoundness
public import Langlib.Automata.LinearBounded.BoundedCrossingTraceCertificate

@[expose]
public section

/-!
# Crossing-count-preserving soundness of spatial certificates

The ordinary synchronization theorem reconstructs an accepting computation from a row of
compatible one-cell histories.  Here the same recursion retains the concrete `StepTrace` and
accounts for every physical boundary crossing.

The invariant is deliberately stated using the row's *remaining* shared interface lists.  A
stationary or clamped step preserves every interface.  A genuine move across boundary `b`
consumes exactly one state from that boundary's interface and crosses exactly `b`.  Consequently
the reconstructed suffix crosses each boundary no more often than the corresponding remaining
profile length.  Applying `InitialRealization.profileBound` recovers the original uniform cap.

All results are uniform in the tape alphabet, state type, cap, and positive tape width, including
the one-cell case where there are no internal boundaries.
-/

namespace LBA.BoundedCrossing.Soundness

universe u v
variable {Γ : Type u} {Λ : Type v}

/-- Updating one cell without changing its right interface preserves every right interface. -/
theorem Row.right_set_same {M : LBA.Machine Γ Λ} {n : ℕ} (row : Row M n)
    (i : Fin (n + 1)) (cell : PackedCell M (atLeft i) (atRight i))
    (hright : cell.right = (row i).right) (j : Fin (n + 1)) :
    ((row.set i cell) j).right = (row j).right := by
  by_cases hji : j = i
  · subst j
    simpa using hright
  · exact congrArg PackedCell.right (Row.set_apply_of_ne row i j cell hji)

/-- Updating the two cells adjacent to `b` changes only the right interface of the left cell. -/
theorem Row.right_set_adjacent {M : LBA.Machine Γ Λ} {n : ℕ} (row : Row M n)
    (b : Fin n)
    (lc : PackedCell M (atLeft b.castSucc) (atRight b.castSucc))
    (rc : PackedCell M (atLeft b.succ) (atRight b.succ))
    (newShared : List Λ) (hshared : lc.right = newShared)
    (hright : rc.right = (row b.succ).right) (b' : Fin n) :
    (((row.set b.castSucc lc).set b.succ rc) b'.castSucc).right =
      if b' = b then newShared else (row b'.castSucc).right := by
  by_cases hbb : b' = b
  · subst b'
    rw [if_pos rfl]
    rw [Row.set_right_of_ne _ _ _ _ (Fin.castSucc_ne_succ b),
      Row.set_right_of_eq _ _ _ _ rfl]
    exact hshared
  · rw [if_neg hbb]
    have hleft : b'.castSucc ≠ b.castSucc := by
      intro h
      apply hbb
      exact Fin.ext (by simpa using congrArg Fin.val h)
    by_cases hrightCell : b'.castSucc = b.succ
    · rw [Row.set_right_of_eq _ _ _ _ hrightCell, hright]
      exact congrArg (fun i => (row i).right) hrightCell.symm
    · rw [Row.set_right_of_ne _ _ _ _ hrightCell,
        Row.set_right_of_ne _ _ _ _ hleft]

/-- No tape boundary is crossed when the source and target heads agree. -/
theorem not_crossesBoundary_of_head_eq {n : ℕ} (b : Fin n)
    (source target : DLBA.Cfg Γ Λ n)
    (hhead : source.tape.head = target.tape.head) :
    ¬ LBA.StepTrace.CrossesBoundary b source target := by
  simp only [LBA.StepTrace.CrossesBoundary, LBA.StepTrace.CrossesRight,
    LBA.StepTrace.CrossesLeft, LBA.StepTrace.HeadAtOrLeft,
    LBA.StepTrace.HeadRight]
  have hval := congrArg Fin.val hhead
  omega

/-- A move from `b + 1` to `b` crosses exactly boundary `b`. -/
theorem crossesBoundary_move_left_iff {n : ℕ} (b b' : Fin n)
    (source target : DLBA.Cfg Γ Λ n)
    (hsource : source.tape.head = b.succ)
    (htarget : target.tape.head = b.castSucc) :
    LBA.StepTrace.CrossesBoundary b' source target ↔ b' = b := by
  simp only [LBA.StepTrace.CrossesBoundary, LBA.StepTrace.CrossesRight,
    LBA.StepTrace.CrossesLeft, LBA.StepTrace.HeadAtOrLeft,
    LBA.StepTrace.HeadRight]
  constructor
  · rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
    · have hs := congrArg Fin.val hsource
      have ht := congrArg Fin.val htarget
      simp at hs ht
      omega
    · apply Fin.ext
      have hs := congrArg Fin.val hsource
      have ht := congrArg Fin.val htarget
      simp at hs ht
      omega
  · rintro rfl
    right
    constructor
    · have hs := congrArg Fin.val hsource
      simp at hs
      omega
    · have ht := congrArg Fin.val htarget
      simp at ht
      omega

/-- A move from `b` to `b + 1` crosses exactly boundary `b`. -/
theorem crossesBoundary_move_right_iff {n : ℕ} (b b' : Fin n)
    (source target : DLBA.Cfg Γ Λ n)
    (hsource : source.tape.head = b.castSucc)
    (htarget : target.tape.head = b.succ) :
    LBA.StepTrace.CrossesBoundary b' source target ↔ b' = b := by
  simp only [LBA.StepTrace.CrossesBoundary, LBA.StepTrace.CrossesRight,
    LBA.StepTrace.CrossesLeft, LBA.StepTrace.HeadAtOrLeft,
    LBA.StepTrace.HeadRight]
  constructor
  · rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
    · apply Fin.ext
      have hs := congrArg Fin.val hsource
      have ht := congrArg Fin.val htarget
      simp at hs ht
      omega
    · have hs := congrArg Fin.val hsource
      have ht := congrArg Fin.val htarget
      simp at hs ht
      omega
  · rintro rfl
    left
    constructor
    · have hs := congrArg Fin.val hsource
      simp at hs
      omega
    · have ht := congrArg Fin.val htarget
      simp at ht
      omega

/-- A concrete accepting trace whose future crossings are bounded by the row's unconsumed
profiles. -/
def HasProfileBoundedAcceptingTrace {M : LBA.Machine Γ Λ} {n : ℕ}
    (row : Row M n) (head : Fin (n + 1)) (q : Λ) : Prop :=
  ∃ target, ∃ trace : LBA.StepTrace M (cfgOf row head q) target,
    M.accept target.state = true ∧
      ∀ b : Fin n, trace.crossingCount b ≤ (row b.castSucc).right.length

/-- Synchronize a row of local histories into one concrete accepting trace.  At every boundary,
the trace uses no more crossings than the length of the row's still-unconsumed shared profile. -/
theorem boundedAcceptingTrace_of_active_row {M : LBA.Machine Γ Λ} {n : ℕ}
    (row : Row M n) (head : Fin (n + 1)) (q : Λ)
    {left right : List Λ} {terminal : Bool}
    (active : CellRun M (atLeft head) (atRight head)
      (.active q (row head).phase.symbol) left right terminal)
    (hleft : (row head).left = left) (hright : (row head).right = right)
    (hterminal : (row head).terminal = terminal)
    (hsize : active.size = (row head).run.size)
    (halign : Aligned row head q) (hmatched : BoundaryMatched row) :
    HasProfileBoundedAcceptingTrace row head q := by
  cases active with
  | terminal haccept =>
      exact ⟨cfgOf row head q, .refl _, haccept, fun b => by simp⟩
  | @stationary _ _ nextState written direction left right terminal henabled hstays rest =>
      let cell : PackedCell M (atLeft head) (atRight head) :=
        ⟨.active nextState written, left, right, terminal, rest⟩
      let nextRow := row.set head cell
      have hphase : cell.phase = .active nextState written := rfl
      have hstep : LBA.Step M (cfgOf row head q) (cfgOf nextRow head nextState) :=
        step_set_head henabled hstays cell hphase
      have halign' : Aligned nextRow head nextState := halign.set_head cell hphase
      have hmatched' : BoundaryMatched nextRow :=
        hmatched.set_same_interfaces head cell hleft.symm hright.symm
      have hweight : nextRow.weight < row.weight := by
        apply Row.weight_set_lt
        dsimp [cell]
        rw [← hsize]
        simp [CellRun.size]
      rcases boundedAcceptingTrace_of_active_row nextRow head nextState
          (nextRow.activeRun halign') rfl rfl rfl
          (PackedCell.size_castPhase _ _ _) halign' hmatched' with
        ⟨target, trace, haccept, hbound⟩
      refine ⟨target, .head hstep trace, haccept, ?_⟩
      intro b
      simp only [LBA.StepTrace.crossingCount]
      have hno : ¬ LBA.StepTrace.CrossesBoundary b (cfgOf row head q)
          (cfgOf nextRow head nextState) :=
        not_crossesBoundary_of_head_eq b _ _ rfl
      rw [if_neg hno, zero_add]
      have hi := hbound b
      have hinterface := Row.right_set_same row head cell hright.symm b.castSucc
      exact hi.trans_eq (congrArg List.length hinterface)
  | @exitLeft _ _ nextState written direction left right terminal henabled hexits rest =>
      cases direction with
      | right => exact False.elim hexits
      | stay => exact False.elim hexits
      | left =>
        have hnotFirst : head.val ≠ 0 := by
          simpa [DirectionExitsLeft, atLeft] using hexits
        have hpos : 0 < head.val := by omega
        have hboundHead : head.val - 1 < n := by
          have := head.isLt
          omega
        let b : Fin n := ⟨head.val - 1, hboundHead⟩
        have hhead : b.succ = head := by
          apply Fin.ext
          simp [b]
          omega
        have halignB : Aligned row b.succ q := by simpa only [hhead] using halign
        have hleftB : (row b.succ).left = nextState :: left :=
          (congrArg (fun k => (row k).left) hhead).trans hleft
        have hrightB : (row b.succ).right = right :=
          (congrArg (fun k => (row k).right) hhead).trans hright
        have henabledB :
            (nextState, written, .left) ∈ M.transition q (row b.succ).phase.symbol := by
          rw [congrArg (fun k => (row k).phase.symbol) hhead]
          exact henabled
        have hexitsB : DirectionExitsLeft (atLeft b.succ) .left := by
          simpa only [hhead] using hexits
        have hflagLeft : atLeft head = atLeft b.succ := congrArg atLeft hhead.symm
        have hflagRight : atRight head = atRight b.succ := congrArg atRight hhead.symm
        let restB : CellRun M (atLeft b.succ) (atRight b.succ)
            (.outside .left written) left right terminal :=
          castCellRunFlags rest hflagLeft hflagRight
        have hsizeB : (CellRun.exitLeft henabledB hexitsB restB).size =
            (row b.succ).run.size := by
          change restB.size + 1 = (row b.succ).run.size
          have hrowSize := congrArg (fun k => (row k).run.size) hhead
          change (row b.succ).run.size = (row head).run.size at hrowSize
          change rest.size + 1 = (row head).run.size at hsize
          rw [hrowSize]
          simpa [restB] using hsize
        have hneighborPhase :
            (row b.castSucc).phase = .outside .right (row b.castSucc).phase.symbol :=
          halignB.left_of_lt (by simp)
        have hneighborRight : (row b.castSucc).right = nextState :: left :=
          (hmatched.2.2 b).trans hleftB
        let enter : CellRun M (atLeft b.castSucc) (atRight b.castSucc)
            (.outside .right (row b.castSucc).phase.symbol) (row b.castSucc).left
              (nextState :: left) (row b.castSucc).terminal :=
          (row b.castSucc).castRun hneighborPhase rfl hneighborRight rfl
        let neighborRest := peelEnterRight enter
        let lc : PackedCell M (atLeft b.castSucc) (atRight b.castSucc) :=
          ⟨.active nextState (row b.castSucc).phase.symbol, (row b.castSucc).left,
            left, (row b.castSucc).terminal, neighborRest⟩
        let rc : PackedCell M (atLeft b.succ) (atRight b.succ) :=
          ⟨.outside .left written, left, right, terminal, restB⟩
        let nextRow := (row.set b.castSucc lc).set b.succ rc
        have hlphase : lc.phase = .active nextState (row b.castSucc).phase.symbol := rfl
        have hrphase : rc.phase = .outside .left written := rfl
        have hstep : LBA.Step M (cfgOf row b.succ q)
            (cfgOf nextRow b.castSucc nextState) :=
          step_set_move_left b henabledB lc rc hlphase hrphase rfl
        have halign' : Aligned nextRow b.castSucc nextState :=
          halignB.set_move_left b lc rc hlphase hrphase
        have hmatched' : BoundaryMatched nextRow := by
          apply hmatched.set_adjacent b lc rc
          · rfl
          · rfl
          · exact hrightB.symm
        have henterSize : enter.size = (row b.castSucc).run.size := by
          dsimp [enter]
          exact PackedCell.size_castRun _ _ _ _ _
        have hneighborDecrease : lc.run.size < (row b.castSucc).run.size := by
          dsimp [lc, neighborRest]
          have hpeel := size_peelEnterRight enter
          omega
        have hweightFirst : (row.set b.castSucc lc).weight < row.weight :=
          Row.weight_set_lt _ _ _ hneighborDecrease
        have hactiveUnchanged :
            ((row.set b.castSucc lc) b.succ).run.size = (row b.succ).run.size := by
          rw [Row.set_apply_of_ne row b.castSucc b.succ lc
            (Fin.castSucc_ne_succ b).symm]
        have hactiveDecrease : rc.run.size <
            ((row.set b.castSucc lc) b.succ).run.size := by
          dsimp [rc]
          rw [hactiveUnchanged, ← hsizeB]
          simp [CellRun.size]
        have hweightSecond : nextRow.weight < (row.set b.castSucc lc).weight :=
          Row.weight_set_lt _ _ _ hactiveDecrease
        have hweight : nextRow.weight < row.weight := lt_trans hweightSecond hweightFirst
        rcases boundedAcceptingTrace_of_active_row nextRow b.castSucc nextState
            (nextRow.activeRun halign') rfl rfl rfl
            (PackedCell.size_castPhase _ _ _) halign' hmatched' with
          ⟨target, trace, haccept, htrace⟩
        have result : HasProfileBoundedAcceptingTrace row b.succ q := by
          refine ⟨target, .head hstep trace, haccept, ?_⟩
          intro b'
          simp only [LBA.StepTrace.crossingCount]
          by_cases hbb : b' = b
          · subst b'
            have hcross : LBA.StepTrace.CrossesBoundary b (cfgOf row b.succ q)
                (cfgOf nextRow b.castSucc nextState) :=
              (crossesBoundary_move_left_iff b b _ _ rfl rfl).2 rfl
            rw [if_pos hcross]
            have hsuffix := htrace b
            have hinterface := Row.right_set_adjacent row b lc rc left rfl hrightB.symm b
            have hinterface' : (nextRow b.castSucc).right = left := by
              simpa using hinterface
            rw [hinterface'] at hsuffix
            rw [hneighborRight]
            simp only [List.length_cons]
            omega
          · have hnocross : ¬ LBA.StepTrace.CrossesBoundary b'
                (cfgOf row b.succ q) (cfgOf nextRow b.castSucc nextState) := by
              intro hcross
              exact hbb ((crossesBoundary_move_left_iff b b' _ _ rfl rfl).1 hcross)
            rw [if_neg hnocross, zero_add]
            have hsuffix := htrace b'
            have hinterface := Row.right_set_adjacent row b lc rc left rfl hrightB.symm b'
            rw [if_neg hbb] at hinterface
            exact hsuffix.trans_eq (congrArg List.length hinterface)
        simpa only [hhead] using result
  | @exitRight _ _ nextState written direction left right terminal henabled hexits rest =>
      cases direction with
      | left => exact False.elim hexits
      | stay => exact False.elim hexits
      | right =>
        have hnotLast : head.val ≠ n := by
          simpa [DirectionExitsRight, atRight] using hexits
        have hlt : head.val < n := by omega
        let b : Fin n := ⟨head.val, hlt⟩
        have hhead : b.castSucc = head := by
          apply Fin.ext
          rfl
        have halignB : Aligned row b.castSucc q := by simpa only [hhead] using halign
        have hleftB : (row b.castSucc).left = left := by simpa only [hhead] using hleft
        have hrightB : (row b.castSucc).right = nextState :: right := by
          simpa only [hhead] using hright
        have henabledB :
            (nextState, written, .right) ∈ M.transition q (row b.castSucc).phase.symbol := by
          simpa only [hhead] using henabled
        have hexitsB : DirectionExitsRight (atRight b.castSucc) .right := by
          simpa only [hhead] using hexits
        let restB : CellRun M (atLeft b.castSucc) (atRight b.castSucc)
            (.outside .right written) left right terminal := by
          simpa only [hhead] using rest
        have hsizeB : (CellRun.exitRight henabledB hexitsB restB).size =
            (row b.castSucc).run.size := by
          simpa only [hhead] using hsize
        have hneighborPhase :
            (row b.succ).phase = .outside .left (row b.succ).phase.symbol :=
          halignB.right_of_lt (by simp)
        have hneighborLeft : (row b.succ).left = nextState :: right := by
          exact (hrightB.symm.trans (hmatched.2.2 b)).symm
        let enter : CellRun M (atLeft b.succ) (atRight b.succ)
            (.outside .left (row b.succ).phase.symbol) (nextState :: right)
              (row b.succ).right (row b.succ).terminal :=
          (row b.succ).castRun hneighborPhase hneighborLeft rfl rfl
        let neighborRest := peelEnterLeft enter
        let lc : PackedCell M (atLeft b.castSucc) (atRight b.castSucc) :=
          ⟨.outside .right written, left, right, terminal, restB⟩
        let rc : PackedCell M (atLeft b.succ) (atRight b.succ) :=
          ⟨.active nextState (row b.succ).phase.symbol, right,
            (row b.succ).right, (row b.succ).terminal, neighborRest⟩
        let nextRow := (row.set b.castSucc lc).set b.succ rc
        have hlphase : lc.phase = .outside .right written := rfl
        have hrphase : rc.phase = .active nextState (row b.succ).phase.symbol := rfl
        have hstep : LBA.Step M (cfgOf row b.castSucc q)
            (cfgOf nextRow b.succ nextState) :=
          step_set_move_right b henabledB lc rc hlphase hrphase rfl
        have halign' : Aligned nextRow b.succ nextState :=
          halignB.set_move_right b lc rc hlphase hrphase
        have hmatched' : BoundaryMatched nextRow := by
          apply hmatched.set_adjacent b lc rc
          · exact hleftB.symm
          · rfl
          · rfl
        have hweightFirst : (row.set b.castSucc lc).weight < row.weight := by
          apply Row.weight_set_lt
          dsimp [lc]
          rw [← hsizeB]
          simp [CellRun.size]
        have hneighborUnchanged :
            ((row.set b.castSucc lc) b.succ).run.size = (row b.succ).run.size := by
          rw [Row.set_apply_of_ne row b.castSucc b.succ lc
            (Fin.castSucc_ne_succ b).symm]
        have henterSize : enter.size = (row b.succ).run.size := by
          dsimp [enter]
          exact PackedCell.size_castRun _ _ _ _ _
        have hneighborDecrease : rc.run.size <
            ((row.set b.castSucc lc) b.succ).run.size := by
          dsimp [rc, neighborRest]
          have hpeel := size_peelEnterLeft enter
          omega
        have hweightSecond : nextRow.weight < (row.set b.castSucc lc).weight :=
          Row.weight_set_lt _ _ _ hneighborDecrease
        have hweight : nextRow.weight < row.weight := lt_trans hweightSecond hweightFirst
        rcases boundedAcceptingTrace_of_active_row nextRow b.succ nextState
            (nextRow.activeRun halign') rfl rfl rfl
            (PackedCell.size_castPhase _ _ _) halign' hmatched' with
          ⟨target, trace, haccept, htrace⟩
        have result : HasProfileBoundedAcceptingTrace row b.castSucc q := by
          refine ⟨target, .head hstep trace, haccept, ?_⟩
          intro b'
          simp only [LBA.StepTrace.crossingCount]
          by_cases hbb : b' = b
          · subst b'
            have hcross : LBA.StepTrace.CrossesBoundary b (cfgOf row b.castSucc q)
                (cfgOf nextRow b.succ nextState) :=
              (crossesBoundary_move_right_iff b b _ _ rfl rfl).2 rfl
            rw [if_pos hcross]
            have hsuffix := htrace b
            have hinterface := Row.right_set_adjacent row b lc rc right rfl rfl b
            have hinterface' : (nextRow b.castSucc).right = right := by
              simpa using hinterface
            rw [hinterface'] at hsuffix
            rw [hrightB]
            simp only [List.length_cons]
            omega
          · have hnocross : ¬ LBA.StepTrace.CrossesBoundary b'
                (cfgOf row b.castSucc q) (cfgOf nextRow b.succ nextState) := by
              intro hcross
              exact hbb ((crossesBoundary_move_right_iff b b' _ _ rfl rfl).1 hcross)
            rw [if_neg hnocross, zero_add]
            have hsuffix := htrace b'
            have hinterface := Row.right_set_adjacent row b lc rc right rfl rfl b'
            rw [if_neg hbb] at hinterface
            exact hsuffix.trans_eq (congrArg List.length hinterface)
        simpa only [hhead] using result
termination_by row.weight

/-- A uniform cap on the row's shared profiles becomes the same cap on the reconstructed trace. -/
theorem acceptsWithBound_of_active_row
    {M : LBA.Machine Γ Λ} {n bound : ℕ}
    (row : Row M n) (head : Fin (n + 1)) (q : Λ)
    {left right : List Λ} {terminal : Bool}
    (active : CellRun M (atLeft head) (atRight head)
      (.active q (row head).phase.symbol) left right terminal)
    (hleft : (row head).left = left) (hright : (row head).right = right)
    (hterminal : (row head).terminal = terminal)
    (hsize : active.size = (row head).run.size)
    (halign : Aligned row head q) (hmatched : BoundaryMatched row)
    (hprofiles : ∀ b : Fin n, (row b.castSucc).right.length ≤ bound) :
    AcceptsWithBound M (cfgOf row head q) bound := by
  rcases boundedAcceptingTrace_of_active_row row head q active hleft hright hterminal hsize
      halign hmatched with ⟨target, trace, haccept, hcross⟩
  exact ⟨target, trace, haccept, fun b => (hcross b).trans (hprofiles b)⟩

/-- Aligned rows with uniformly bounded shared profiles have a bounded accepting trace. -/
theorem acceptsWithBound_of_aligned_row
    {M : LBA.Machine Γ Λ} {n bound : ℕ}
    (row : Row M n) (head : Fin (n + 1)) (q : Λ)
    (halign : Aligned row head q) (hmatched : BoundaryMatched row)
    (hprofiles : ∀ b : Fin n, (row b.castSucc).right.length ≤ bound) :
    AcceptsWithBound M (cfgOf row head q) bound :=
  acceptsWithBound_of_active_row row head q (row.activeRun halign) rfl rfl rfl
    (PackedCell.size_castPhase _ _ _) halign hmatched hprofiles

/-- A list-level spatial certificate reconstructs an accepting trace satisfying its advertised
crossing cap. -/
theorem acceptsWithBound_of_listCellCertificate
    (M : LBA.Machine Γ Λ) (bound : ℕ) {first : Γ} {rest : List Γ}
    (certificate : ListCellCertificate M bound (first :: rest)) :
    AcceptsWithBound M (LBA.initCfgList M (first :: rest) (by simp)) bound := by
  rcases initialRealization_of_certificate M bound certificate with ⟨realization⟩
  have haccepts := acceptsWithBound_of_aligned_row realization.row
    ⟨0, Nat.zero_lt_succ _⟩ M.initial realization.aligned realization.matched
    realization.profileBound
  rw [realization.cfgOf_eq_initCfgList] at haccepts
  exact haccepts

/-- Transporting a bounded trace along an equality of tape-width indices preserves its cap. -/
theorem castCfg_acceptsWithBound {M : LBA.Machine Γ Λ} {n m bound : ℕ}
    (h : n = m) {cfg : DLBA.Cfg Γ Λ n}
    (haccept : AcceptsWithBound M cfg bound) :
    AcceptsWithBound M (castCfg h cfg) bound := by
  subst m
  exact haccept

/-- A width-indexed spatial certificate reconstructs a bounded accepting trace from the exact
function-valued initial configuration. -/
theorem acceptsWithBound_initialCfgFn_of_cellCertificate
    (M : LBA.Machine Γ Λ) (bound n : ℕ) (input : Fin (n + 1) → Γ)
    (certificate : CellCertificate M bound input) :
    AcceptsWithBound M (initialCfgFn M input) bound := by
  let word := input 0 :: List.ofFn (fun i : Fin n => input i.succ)
  have hlength : word.length - 1 = n := by simp [word]
  have hcertificate : ListCellCertificate M bound word := by
    change ListCellCertificate M bound (List.ofFn input) at certificate
    rw [List.ofFn_succ] at certificate
    simpa only [word] using certificate
  have haccepts : AcceptsWithBound M (LBA.initCfgList M word (by simp [word])) bound := by
    exact acceptsWithBound_of_listCellCertificate M bound hcertificate
  have hcast := castCfg_acceptsWithBound hlength haccepts
  rw [castCfg_initCfgList_decomposed_eq_initialCfgFn M input hlength] at hcast
  exact hcast

/-- Profile-NFA membership is sound for bounded-crossing acceptance from the exact initial
configuration. -/
theorem acceptsWithBound_initialCfgFn_of_mem_profileNFA
    (M : LBA.Machine Γ Λ) (bound n : ℕ) (input : Fin (n + 1) → Γ)
    (hmem : List.ofFn input ∈ (profileNFA M bound).accepts) :
    AcceptsWithBound M (initialCfgFn M input) bound := by
  rcases (mem_profileNFA_iff_nonempty_cellCertificate M bound n input).1 hmem with
    ⟨certificate⟩
  exact acceptsWithBound_initialCfgFn_of_cellCertificate M bound n input certificate

/-- Exact machine-level correctness of the bounded-profile NFA. -/
theorem mem_profileNFA_iff_acceptsWithBound_initialCfgFn
    (M : LBA.Machine Γ Λ) (bound n : ℕ) (input : Fin (n + 1) → Γ) :
    List.ofFn input ∈ (profileNFA M bound).accepts ↔
      AcceptsWithBound M (initialCfgFn M input) bound := by
  constructor
  · exact acceptsWithBound_initialCfgFn_of_mem_profileNFA M bound n input
  · intro haccept
    apply mem_profileNFA_of_acceptsWithBound haccept
    · rfl
    · rfl

end LBA.BoundedCrossing.Soundness

end
