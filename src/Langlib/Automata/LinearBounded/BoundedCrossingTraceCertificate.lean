module

public import Langlib.Automata.LinearBounded.BoundedCrossing
public import Langlib.Automata.LinearBounded.BoundedCrossingCertificate

@[expose]
public section

/-!
# Completeness of bounded crossing certificates

A concrete accepting LBA trace projects to one Type-valued local history per physical tape cell.
The histories share the trace's chronological crossing sequence literally at each internal
boundary.  Packaging sequences of bounded length as finite profiles gives the spatial certificate
used by `profileNFA`: writes, stationary moves, physical clamping, an arbitrary accepting final
head, and the one-cell tape are all handled directly.
-/

namespace LBA.BoundedCrossing

universe u v

variable {Γ : Type u} {Λ : Type v}

/-! The exact local projection of one global configuration. -/

def atLeft {n : ℕ} (i : Fin (n + 1)) : Bool := decide (i.val = 0)
def atRight {n : ℕ} (i : Fin (n + 1)) : Bool := decide (i.val = n)

def phaseAt {n : ℕ} (cfg : DLBA.Cfg Γ Λ n) (i : Fin (n + 1)) : Phase Γ Λ :=
  if cfg.tape.head = i then .active cfg.state (cfg.tape.contents i)
  else if cfg.tape.head.val < i.val then .outside .left (cfg.tape.contents i)
  else .outside .right (cfg.tape.contents i)

def leftSequence {n : ℕ} {M : LBA.Machine Γ Λ}
    {source target : DLBA.Cfg Γ Λ n} (i : Fin (n + 1))
    (trace : LBA.StepTrace M source target) : List Λ :=
  if h : 0 < i.val then
    LBA.StepTrace.crossingSequence ⟨i.val - 1, by omega⟩ trace
  else []

def rightSequence {n : ℕ} {M : LBA.Machine Γ Λ}
    {source target : DLBA.Cfg Γ Λ n} (i : Fin (n + 1))
    (trace : LBA.StepTrace M source target) : List Λ :=
  if h : i.val < n then
    LBA.StepTrace.crossingSequence ⟨i.val, h⟩ trace
  else []

def terminalAt {n : ℕ} (cfg : DLBA.Cfg Γ Λ n) (i : Fin (n + 1)) : Bool :=
  decide (cfg.tape.head = i)

@[simp] theorem leftSequence_refl {n : ℕ} {M : LBA.Machine Γ Λ}
    (cfg : DLBA.Cfg Γ Λ n) (i : Fin (n + 1)) :
    leftSequence i (.refl cfg : LBA.StepTrace M cfg cfg) = [] := by
  simp [leftSequence]

@[simp] theorem rightSequence_refl {n : ℕ} {M : LBA.Machine Γ Λ}
    (cfg : DLBA.Cfg Γ Λ n) (i : Fin (n + 1)) :
    rightSequence i (.refl cfg : LBA.StepTrace M cfg cfg) = [] := by
  simp [rightSequence]

theorem terminalAt_eq_true_iff {n : ℕ} (cfg : DLBA.Cfg Γ Λ n) (i : Fin (n + 1)) :
    terminalAt cfg i = true ↔ cfg.tape.head = i := by
  simp [terminalAt]

/-! Start with the terminal configuration; this already handles the one-cell tape. -/

def terminalCellRun {n : ℕ} {M : LBA.Machine Γ Λ}
    (cfg : DLBA.Cfg Γ Λ n) (haccept : M.accept cfg.state = true)
    (i : Fin (n + 1)) :
    CellRun M (atLeft i) (atRight i) (phaseAt cfg i) [] [] (terminalAt cfg i) := by
  by_cases hi : cfg.tape.head = i
  · simp only [phaseAt, if_pos hi, terminalAt]
    simp only [hi, decide_true]
    exact .terminal haccept
  · simp only [phaseAt, if_neg hi, terminalAt]
    simp only [hi, decide_false]
    by_cases hside : cfg.tape.head.val < i.val
    · simp only [if_pos hside]
      exact .idleLeft _
    · simp only [if_neg hside]
      exact .idleRight _

private theorem not_crosses_of_same_head {n : ℕ}
    (b : Fin n) (old new : DLBA.Cfg Γ Λ n)
    (hhead : old.tape.head = new.tape.head) :
    ¬ LBA.StepTrace.CrossesBoundary b old new := by
  simp only [LBA.StepTrace.CrossesBoundary, LBA.StepTrace.CrossesRight,
    LBA.StepTrace.CrossesLeft, LBA.StepTrace.HeadAtOrLeft,
    LBA.StepTrace.HeadRight]
  rw [hhead]
  omega

private theorem phaseAt_stay_at_head {n : ℕ}
    (old : DLBA.Cfg Γ Λ n) (i : Fin (n + 1)) (q' : Λ) (written : Γ)
    (hi : old.tape.head = i) :
    phaseAt (⟨q', (old.tape.write written).moveHead .stay⟩ : DLBA.Cfg Γ Λ n) i =
      .active q' written := by
  simp [phaseAt, DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, hi,
    Function.update_self]

private theorem phaseAt_stay_away {n : ℕ}
    (old : DLBA.Cfg Γ Λ n) (i : Fin (n + 1)) (q' : Λ) (written : Γ)
    (hi : old.tape.head ≠ i) :
    phaseAt (⟨q', (old.tape.write written).moveHead .stay⟩ : DLBA.Cfg Γ Λ n) i =
      phaseAt old i := by
  simp only [phaseAt, DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write,
    hi, ↓reduceIte]
  rw [Function.update_of_ne hi.symm]

private def prependStay {n : ℕ} {M : LBA.Machine Γ Λ}
    (old : DLBA.Cfg Γ Λ n) (q' : Λ) (written : Γ)
    (henabled : (q', written, DLBA.Dir.stay) ∈ M.transition old.state old.tape.read)
    {target : DLBA.Cfg Γ Λ n}
    (tail : LBA.StepTrace M
      ⟨q', (old.tape.write written).moveHead .stay⟩ target)
    (i : Fin (n + 1))
    (rest : CellRun M (atLeft i) (atRight i)
      (phaseAt (⟨q', (old.tape.write written).moveHead .stay⟩ : DLBA.Cfg Γ Λ n) i)
      (leftSequence i tail) (rightSequence i tail) (terminalAt target i)) :
    CellRun M (atLeft i) (atRight i) (phaseAt old i)
      (leftSequence i (.head ⟨q', written, .stay, henabled, rfl⟩ tail))
      (rightSequence i (.head ⟨q', written, .stay, henabled, rfl⟩ tail))
      (terminalAt target i) := by
  let new : DLBA.Cfg Γ Λ n :=
    ⟨q', (old.tape.write written).moveHead .stay⟩
  have hhead : old.tape.head = new.tape.head := by
    rfl
  have hcross (b : Fin n) : ¬ LBA.StepTrace.CrossesBoundary b old new :=
    not_crosses_of_same_head b old new hhead
  by_cases hi : old.tape.head = i
  · have r : CellRun M (atLeft i) (atRight i) (.active q' written)
        (leftSequence i tail) (rightSequence i tail) (terminalAt target i) := by
      rw [phaseAt_stay_at_head old i q' written hi] at rest
      exact rest
    have built := CellRun.stationary henabled (by trivial) r
    simpa only [phaseAt, if_pos hi, hi, DLBA.BoundedTape.read, leftSequence,
      rightSequence, LBA.StepTrace.crossingSequence, new, hcross, if_false] using built
  · have heq : phaseAt new i = phaseAt old i := by
      exact phaseAt_stay_away old i q' written hi
    have r : CellRun M (atLeft i) (atRight i) (phaseAt old i)
        (leftSequence i tail) (rightSequence i tail) (terminalAt target i) := by
      simpa only [new, heq] using rest
    simpa only [leftSequence, rightSequence, LBA.StepTrace.crossingSequence,
      new, hcross, if_false] using r

private theorem crosses_iff_heads {n : ℕ} (b : Fin n)
    (old new : DLBA.Cfg Γ Λ n) :
    LBA.StepTrace.CrossesBoundary b old new ↔
      (old.tape.head.val ≤ b.val ∧ b.val < new.tape.head.val) ∨
      (b.val < old.tape.head.val ∧ new.tape.head.val ≤ b.val) := by
  rfl

private theorem leftSequence_head_eq_tail {n : ℕ} {M : LBA.Machine Γ Λ}
    {old new target : DLBA.Cfg Γ Λ n} (i : Fin (n + 1))
    (hstep : LBA.Step M old new) (tail : LBA.StepTrace M new target)
    (hnone : ∀ h : 0 < i.val,
      ¬ LBA.StepTrace.CrossesBoundary (⟨i.val - 1, by omega⟩ : Fin n) old new) :
    leftSequence i (.head hstep tail) = leftSequence i tail := by
  simp only [leftSequence]
  split
  · rename_i h
    have hn : ¬ LBA.StepTrace.CrossesBoundary
        (⟨i.val - 1, by omega⟩ : Fin n) old new := by
      simpa only using hnone h
    simp [LBA.StepTrace.crossingSequence, hn]
  · rfl

private theorem rightSequence_head_eq_tail {n : ℕ} {M : LBA.Machine Γ Λ}
    {old new target : DLBA.Cfg Γ Λ n} (i : Fin (n + 1))
    (hstep : LBA.Step M old new) (tail : LBA.StepTrace M new target)
    (hnone : ∀ h : i.val < n,
      ¬ LBA.StepTrace.CrossesBoundary (⟨i.val, h⟩ : Fin n) old new) :
    rightSequence i (.head hstep tail) = rightSequence i tail := by
  simp only [rightSequence]
  split
  · rename_i h
    have hn : ¬ LBA.StepTrace.CrossesBoundary (⟨i.val, h⟩ : Fin n) old new :=
      hnone h
    simp [LBA.StepTrace.crossingSequence, hn]
  · rfl

private theorem leftSequence_head_eq_cons {n : ℕ} {M : LBA.Machine Γ Λ}
    {old new target : DLBA.Cfg Γ Λ n} (i : Fin (n + 1))
    (hstep : LBA.Step M old new) (tail : LBA.StepTrace M new target)
    (hi : 0 < i.val)
    (hcross : LBA.StepTrace.CrossesBoundary
      (⟨i.val - 1, by omega⟩ : Fin n) old new) :
    leftSequence i (.head hstep tail) = new.state :: leftSequence i tail := by
  simp [leftSequence, LBA.StepTrace.crossingSequence, hi, hcross]

private theorem rightSequence_head_eq_cons {n : ℕ} {M : LBA.Machine Γ Λ}
    {old new target : DLBA.Cfg Γ Λ n} (i : Fin (n + 1))
    (hstep : LBA.Step M old new) (tail : LBA.StepTrace M new target)
    (hi : i.val < n)
    (hcross : LBA.StepTrace.CrossesBoundary (⟨i.val, hi⟩ : Fin n) old new) :
    rightSequence i (.head hstep tail) = new.state :: rightSequence i tail := by
  simp [rightSequence, LBA.StepTrace.crossingSequence, hi, hcross]

private def prependLeft {n : ℕ} {M : LBA.Machine Γ Λ}
    (old : DLBA.Cfg Γ Λ n) (q' : Λ) (written : Γ)
    (henabled : (q', written, DLBA.Dir.left) ∈ M.transition old.state old.tape.read)
    {target : DLBA.Cfg Γ Λ n}
    (tail : LBA.StepTrace M
      ⟨q', (old.tape.write written).moveHead .left⟩ target)
    (i : Fin (n + 1))
    (rest : CellRun M (atLeft i) (atRight i)
      (phaseAt (⟨q', (old.tape.write written).moveHead .left⟩ : DLBA.Cfg Γ Λ n) i)
      (leftSequence i tail) (rightSequence i tail) (terminalAt target i)) :
    CellRun M (atLeft i) (atRight i) (phaseAt old i)
      (leftSequence i (.head ⟨q', written, .left, henabled, rfl⟩ tail))
      (rightSequence i (.head ⟨q', written, .left, henabled, rfl⟩ tail))
      (terminalAt target i) := by
  let new : DLBA.Cfg Γ Λ n :=
    ⟨q', (old.tape.write written).moveHead .left⟩
  have hstep : LBA.Step M old new := ⟨q', written, .left, henabled, rfl⟩
  by_cases hinside : 0 < old.tape.head.val
  · have hnewval : new.tape.head.val = old.tape.head.val - 1 := by
      simp [new, DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, hinside]
    by_cases hiOld : old.tape.head = i
    · have hiPos : 0 < i.val := by simpa [hiOld] using hinside
      have hnewNe : new.tape.head ≠ i := by
        intro h
        have := congrArg Fin.val h
        omega
      have hnewLt : new.tape.head.val < i.val := by
        rw [hnewval]
        have : old.tape.head.val = i.val := congrArg Fin.val hiOld
        omega
      have hphaseNew : phaseAt new i = .outside .left written := by
        simp only [phaseAt, if_neg hnewNe, if_pos hnewLt]
        simp [new, DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, hiOld]
      have r : CellRun M (atLeft i) (atRight i) (.outside .left written)
          (leftSequence i tail) (rightSequence i tail) (terminalAt target i) := by
        rw [hphaseNew] at rest
        exact rest
      have hexit : DirectionExitsLeft (atLeft i) .left := by
        change decide (i.val = 0) = false
        simp [show i.val ≠ 0 by omega]
      have built := CellRun.exitLeft henabled hexit r
      have hcrossLeft : LBA.StepTrace.CrossesBoundary
          (⟨i.val - 1, by omega⟩ : Fin n) old new := by
        rw [crosses_iff_heads]
        right
        constructor <;> simp only [hiOld, hnewval]
        · omega
        · omega
      have hnoRight : ∀ h : i.val < n,
          ¬ LBA.StepTrace.CrossesBoundary (⟨i.val, h⟩ : Fin n) old new := by
        intro h hcross
        rw [crosses_iff_heads] at hcross
        simp only [hiOld, hnewval] at hcross
        omega
      have hleftSeq := leftSequence_head_eq_cons i hstep tail hiPos hcrossLeft
      have hrightSeq := rightSequence_head_eq_tail i hstep tail hnoRight
      rw [hleftSeq, hrightSeq]
      simpa only [phaseAt, if_pos hiOld, hiOld, DLBA.BoundedTape.read] using built
    · by_cases hiNew : new.tape.head = i
      · have holdGt : i.val < old.tape.head.val := by
          have hv := congrArg Fin.val hiNew
          simp only [hnewval] at hv
          omega
        have holdNe : old.tape.head ≠ i := hiOld
        have hphaseOld : phaseAt old i = .outside .right (old.tape.contents i) := by
          simp [phaseAt, holdNe, show ¬ old.tape.head.val < i.val by omega]
        have hphaseNew : phaseAt new i = .active q' (old.tape.contents i) := by
          simp only [phaseAt, if_pos hiNew]
          simp [new, DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write,
            Ne.symm hiOld]
        have r : CellRun M (atLeft i) (atRight i) (.active q' (old.tape.contents i))
            (leftSequence i tail) (rightSequence i tail) (terminalAt target i) := by
          rw [hphaseNew] at rest
          exact rest
        have built := CellRun.enterRight r
        have hiNotRight : ¬ i.val = n := by
          intro hEq
          have := old.tape.head.isLt
          omega
        have hiLtN : i.val < n := by omega
        have hcrossRight : LBA.StepTrace.CrossesBoundary
            (⟨i.val, hiLtN⟩ : Fin n) old new := by
          rw [crosses_iff_heads]
          right
          have hv := congrArg Fin.val hiNew
          simp only [hnewval] at hv
          simp only [hiNew]
          omega
        have hnoLeft : ∀ h : 0 < i.val,
            ¬ LBA.StepTrace.CrossesBoundary (⟨i.val - 1, by omega⟩ : Fin n) old new := by
          intro h hcross
          rw [crosses_iff_heads] at hcross
          simp only [hiNew] at hcross
          have hv := congrArg Fin.val hiNew
          simp only [hnewval] at hv
          omega
        have hleftSeq := leftSequence_head_eq_tail i hstep tail hnoLeft
        have hrightSeq := rightSequence_head_eq_cons i hstep tail hiLtN hcrossRight
        rw [hleftSeq, hrightSeq, hphaseOld]
        exact built
      · have hcontents : new.tape.contents i = old.tape.contents i := by
          simp [new, DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write,
            Ne.symm hiOld]
        have hsameSide : (old.tape.head.val < i.val) ↔ (new.tape.head.val < i.val) := by
          rw [hnewval]
          have holdNeVal : old.tape.head.val ≠ i.val := by
            intro h; exact hiOld (Fin.ext h)
          have hnewNeVal : old.tape.head.val - 1 ≠ i.val := by
            intro h
            exact hiNew (Fin.ext (hnewval.trans h))
          omega
        have hphase : phaseAt new i = phaseAt old i := by
          simp only [phaseAt, if_neg hiNew, if_neg hiOld, hcontents]
          by_cases hs : old.tape.head.val < i.val
          · have hsnew : new.tape.head.val < i.val := hsameSide.mp hs
            simp only [if_pos hsnew, if_pos hs]
          · have hsnew : ¬ new.tape.head.val < i.val := fun h => hs (hsameSide.mpr h)
            simp only [if_neg hsnew, if_neg hs]
        have hnoLeft : ∀ h : 0 < i.val,
            ¬ LBA.StepTrace.CrossesBoundary (⟨i.val - 1, by omega⟩ : Fin n) old new := by
          intro h hcross
          rw [crosses_iff_heads] at hcross
          change (old.tape.head.val ≤ i.val - 1 ∧ i.val - 1 < new.tape.head.val) ∨
            (i.val - 1 < old.tape.head.val ∧ new.tape.head.val ≤ i.val - 1) at hcross
          rw [hnewval] at hcross
          have holdNeVal : old.tape.head.val ≠ i.val := by
            intro hv; exact hiOld (Fin.ext hv)
          have hnewNeVal : old.tape.head.val - 1 ≠ i.val := by
            intro hv
            exact hiNew (Fin.ext (hnewval.trans hv))
          omega
        have hnoRight : ∀ h : i.val < n,
            ¬ LBA.StepTrace.CrossesBoundary (⟨i.val, h⟩ : Fin n) old new := by
          intro h hcross
          rw [crosses_iff_heads] at hcross
          change (old.tape.head.val ≤ i.val ∧ i.val < new.tape.head.val) ∨
            (i.val < old.tape.head.val ∧ new.tape.head.val ≤ i.val) at hcross
          rw [hnewval] at hcross
          have holdNeVal : old.tape.head.val ≠ i.val := by
            intro hv; exact hiOld (Fin.ext hv)
          have hnewNeVal : old.tape.head.val - 1 ≠ i.val := by
            intro hv
            exact hiNew (Fin.ext (hnewval.trans hv))
          omega
        have hleftSeq := leftSequence_head_eq_tail i hstep tail hnoLeft
        have hrightSeq := rightSequence_head_eq_tail i hstep tail hnoRight
        rw [hphase] at rest
        rw [hleftSeq, hrightSeq]
        exact rest
  · have hzero : old.tape.head.val = 0 := by omega
    have hhead : old.tape.head = new.tape.head := by
      apply Fin.ext
      simp [new, DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, hinside]
    have hcross (b : Fin n) : ¬ LBA.StepTrace.CrossesBoundary b old new :=
      not_crosses_of_same_head b old new hhead
    by_cases hi : old.tape.head = i
    · have hiZero : i.val = 0 := by simpa [hi] using hzero
      have hphaseNew : phaseAt new i = .active q' written := by
        have hnewi : new.tape.head = i := hhead.symm.trans hi
        simp only [phaseAt, if_pos hnewi]
        simp [new, DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, hi]
      have r : CellRun M (atLeft i) (atRight i) (.active q' written)
          (leftSequence i tail) (rightSequence i tail) (terminalAt target i) := by
        rw [hphaseNew] at rest
        exact rest
      have hstay : DirectionStaysLocal (atLeft i) (atRight i) .left := by
        simp [DirectionStaysLocal, atLeft, hiZero]
      have built := CellRun.stationary henabled hstay r
      have hleftSeq := leftSequence_head_eq_tail i hstep tail (fun _ => hcross _)
      have hrightSeq := rightSequence_head_eq_tail i hstep tail (fun _ => hcross _)
      rw [hleftSeq, hrightSeq]
      simpa only [phaseAt, if_pos hi, hi, DLBA.BoundedTape.read] using built
    · have hcontents : new.tape.contents i = old.tape.contents i := by
        simp [new, DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, Ne.symm hi]
      have hphase : phaseAt new i = phaseAt old i := by
        have hnewNe : new.tape.head ≠ i := fun h => hi (hhead.trans h)
        simp only [phaseAt, if_neg hnewNe, if_neg hi, hcontents]
        by_cases hs : old.tape.head.val < i.val
        · simp [hs, show new.tape.head.val < i.val by simpa [hhead] using hs]
        · simp [hs, show ¬ new.tape.head.val < i.val by simpa [hhead] using hs]
      have hleftSeq := leftSequence_head_eq_tail i hstep tail (fun _ => hcross _)
      have hrightSeq := rightSequence_head_eq_tail i hstep tail (fun _ => hcross _)
      rw [hphase] at rest
      rw [hleftSeq, hrightSeq]
      exact rest

private def prependRight {n : ℕ} {M : LBA.Machine Γ Λ}
    (old : DLBA.Cfg Γ Λ n) (q' : Λ) (written : Γ)
    (henabled : (q', written, DLBA.Dir.right) ∈ M.transition old.state old.tape.read)
    {target : DLBA.Cfg Γ Λ n}
    (tail : LBA.StepTrace M
      ⟨q', (old.tape.write written).moveHead .right⟩ target)
    (i : Fin (n + 1))
    (rest : CellRun M (atLeft i) (atRight i)
      (phaseAt (⟨q', (old.tape.write written).moveHead .right⟩ : DLBA.Cfg Γ Λ n) i)
      (leftSequence i tail) (rightSequence i tail) (terminalAt target i)) :
    CellRun M (atLeft i) (atRight i) (phaseAt old i)
      (leftSequence i (.head ⟨q', written, .right, henabled, rfl⟩ tail))
      (rightSequence i (.head ⟨q', written, .right, henabled, rfl⟩ tail))
      (terminalAt target i) := by
  let new : DLBA.Cfg Γ Λ n :=
    ⟨q', (old.tape.write written).moveHead .right⟩
  have hstep : LBA.Step M old new := ⟨q', written, .right, henabled, rfl⟩
  by_cases hinside : old.tape.head.val < n
  · have hnewval : new.tape.head.val = old.tape.head.val + 1 := by
      simp [new, DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, hinside]
    by_cases hiOld : old.tape.head = i
    · have hiLt : i.val < n := by simpa [hiOld] using hinside
      have hnewNe : new.tape.head ≠ i := by
        intro h
        have := congrArg Fin.val h
        omega
      have hnewGt : i.val < new.tape.head.val := by
        rw [hnewval]
        have : old.tape.head.val = i.val := congrArg Fin.val hiOld
        omega
      have hphaseNew : phaseAt new i = .outside .right written := by
        simp only [phaseAt, if_neg hnewNe,
          if_neg (show ¬ new.tape.head.val < i.val by omega)]
        simp [new, DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, hiOld]
      have r : CellRun M (atLeft i) (atRight i) (.outside .right written)
          (leftSequence i tail) (rightSequence i tail) (terminalAt target i) := by
        rw [hphaseNew] at rest
        exact rest
      have hexit : DirectionExitsRight (atRight i) .right := by
        change decide (i.val = n) = false
        simp [show i.val ≠ n by omega]
      have built := CellRun.exitRight henabled hexit r
      have hcrossRight : LBA.StepTrace.CrossesBoundary
          (⟨i.val, hiLt⟩ : Fin n) old new := by
        rw [crosses_iff_heads]
        left
        simp only [hiOld, hnewval]
        omega
      have hnoLeft : ∀ h : 0 < i.val,
          ¬ LBA.StepTrace.CrossesBoundary (⟨i.val - 1, by omega⟩ : Fin n) old new := by
        intro h hcross
        rw [crosses_iff_heads] at hcross
        simp only [hiOld, hnewval] at hcross
        omega
      have hleftSeq := leftSequence_head_eq_tail i hstep tail hnoLeft
      have hrightSeq := rightSequence_head_eq_cons i hstep tail hiLt hcrossRight
      rw [hleftSeq, hrightSeq]
      simpa only [phaseAt, if_pos hiOld, hiOld, DLBA.BoundedTape.read] using built
    · by_cases hiNew : new.tape.head = i
      · have holdLt : old.tape.head.val < i.val := by
          have hv := congrArg Fin.val hiNew
          simp only [hnewval] at hv
          omega
        have hphaseOld : phaseAt old i = .outside .left (old.tape.contents i) := by
          simp [phaseAt, hiOld, holdLt]
        have hphaseNew : phaseAt new i = .active q' (old.tape.contents i) := by
          simp only [phaseAt, if_pos hiNew]
          simp [new, DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write,
            Ne.symm hiOld]
        have r : CellRun M (atLeft i) (atRight i) (.active q' (old.tape.contents i))
            (leftSequence i tail) (rightSequence i tail) (terminalAt target i) := by
          rw [hphaseNew] at rest
          exact rest
        have built := CellRun.enterLeft r
        have hiPos : 0 < i.val := by omega
        have hcrossLeft : LBA.StepTrace.CrossesBoundary
            (⟨i.val - 1, by omega⟩ : Fin n) old new := by
          rw [crosses_iff_heads]
          left
          have hv := congrArg Fin.val hiNew
          simp only [hnewval] at hv
          simp only [hiNew]
          omega
        have hnoRight : ∀ h : i.val < n,
            ¬ LBA.StepTrace.CrossesBoundary (⟨i.val, h⟩ : Fin n) old new := by
          intro h hcross
          rw [crosses_iff_heads] at hcross
          simp only [hiNew] at hcross
          have hv := congrArg Fin.val hiNew
          simp only [hnewval] at hv
          omega
        have hleftSeq := leftSequence_head_eq_cons i hstep tail hiPos hcrossLeft
        have hrightSeq := rightSequence_head_eq_tail i hstep tail hnoRight
        rw [hleftSeq, hrightSeq, hphaseOld]
        exact built
      · have hcontents : new.tape.contents i = old.tape.contents i := by
          simp [new, DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write,
            Ne.symm hiOld]
        have hsameSide : (old.tape.head.val < i.val) ↔ (new.tape.head.val < i.val) := by
          rw [hnewval]
          have holdNeVal : old.tape.head.val ≠ i.val := by
            intro h; exact hiOld (Fin.ext h)
          have hnewNeVal : old.tape.head.val + 1 ≠ i.val := by
            intro h
            exact hiNew (Fin.ext (hnewval.trans h))
          omega
        have hphase : phaseAt new i = phaseAt old i := by
          simp only [phaseAt, if_neg hiNew, if_neg hiOld, hcontents]
          by_cases hs : old.tape.head.val < i.val
          · have hsnew : new.tape.head.val < i.val := hsameSide.mp hs
            simp only [if_pos hsnew, if_pos hs]
          · have hsnew : ¬ new.tape.head.val < i.val := fun h => hs (hsameSide.mpr h)
            simp only [if_neg hsnew, if_neg hs]
        have hnoLeft : ∀ h : 0 < i.val,
            ¬ LBA.StepTrace.CrossesBoundary (⟨i.val - 1, by omega⟩ : Fin n) old new := by
          intro h hcross
          rw [crosses_iff_heads] at hcross
          change (old.tape.head.val ≤ i.val - 1 ∧ i.val - 1 < new.tape.head.val) ∨
            (i.val - 1 < old.tape.head.val ∧ new.tape.head.val ≤ i.val - 1) at hcross
          rw [hnewval] at hcross
          have holdNeVal : old.tape.head.val ≠ i.val := by
            intro hv; exact hiOld (Fin.ext hv)
          have hnewNeVal : old.tape.head.val + 1 ≠ i.val := by
            intro hv
            exact hiNew (Fin.ext (hnewval.trans hv))
          omega
        have hnoRight : ∀ h : i.val < n,
            ¬ LBA.StepTrace.CrossesBoundary (⟨i.val, h⟩ : Fin n) old new := by
          intro h hcross
          rw [crosses_iff_heads] at hcross
          change (old.tape.head.val ≤ i.val ∧ i.val < new.tape.head.val) ∨
            (i.val < old.tape.head.val ∧ new.tape.head.val ≤ i.val) at hcross
          rw [hnewval] at hcross
          have holdNeVal : old.tape.head.val ≠ i.val := by
            intro hv; exact hiOld (Fin.ext hv)
          have hnewNeVal : old.tape.head.val + 1 ≠ i.val := by
            intro hv
            exact hiNew (Fin.ext (hnewval.trans hv))
          omega
        have hleftSeq := leftSequence_head_eq_tail i hstep tail hnoLeft
        have hrightSeq := rightSequence_head_eq_tail i hstep tail hnoRight
        rw [hphase] at rest
        rw [hleftSeq, hrightSeq]
        exact rest
  · have hlast : old.tape.head.val = n := by
      have hle : old.tape.head.val ≤ n := by omega
      omega
    have hhead : old.tape.head = new.tape.head := by
      apply Fin.ext
      simp [new, DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, hinside]
    have hcross (b : Fin n) : ¬ LBA.StepTrace.CrossesBoundary b old new :=
      not_crosses_of_same_head b old new hhead
    by_cases hi : old.tape.head = i
    · have hiLast : i.val = n := by simpa [hi] using hlast
      have hphaseNew : phaseAt new i = .active q' written := by
        have hnewi : new.tape.head = i := hhead.symm.trans hi
        simp only [phaseAt, if_pos hnewi]
        simp [new, DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, hi]
      have r : CellRun M (atLeft i) (atRight i) (.active q' written)
          (leftSequence i tail) (rightSequence i tail) (terminalAt target i) := by
        rw [hphaseNew] at rest
        exact rest
      have hstay : DirectionStaysLocal (atLeft i) (atRight i) .right := by
        simp [DirectionStaysLocal, atRight, hiLast]
      have built := CellRun.stationary henabled hstay r
      have hleftSeq := leftSequence_head_eq_tail i hstep tail (fun _ => hcross _)
      have hrightSeq := rightSequence_head_eq_tail i hstep tail (fun _ => hcross _)
      rw [hleftSeq, hrightSeq]
      simpa only [phaseAt, if_pos hi, hi, DLBA.BoundedTape.read] using built
    · have hcontents : new.tape.contents i = old.tape.contents i := by
        simp [new, DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, Ne.symm hi]
      have hphase : phaseAt new i = phaseAt old i := by
        have hnewNe : new.tape.head ≠ i := fun h => hi (hhead.trans h)
        simp only [phaseAt, if_neg hnewNe, if_neg hi, hcontents]
        by_cases hs : old.tape.head.val < i.val
        · simp only [if_pos hs, if_pos (show new.tape.head.val < i.val by
            simpa [hhead] using hs)]
        · simp only [if_neg hs, if_neg (show ¬ new.tape.head.val < i.val by
            simpa [hhead] using hs)]
      have hleftSeq := leftSequence_head_eq_tail i hstep tail (fun _ => hcross _)
      have hrightSeq := rightSequence_head_eq_tail i hstep tail (fun _ => hcross _)
      rw [hphase] at rest
      rw [hleftSeq, hrightSeq]
      exact rest

/-- Every concrete accepting trace projects to a complete Type-valued local history at each
physical cell.  The two list indices are literally the chronological crossing sequences of the
trace. -/
theorem nonempty_cellRun_of_accepting_trace {n : ℕ} {M : LBA.Machine Γ Λ}
    {source target : DLBA.Cfg Γ Λ n}
    (trace : LBA.StepTrace M source target)
    (haccept : M.accept target.state = true) (i : Fin (n + 1)) :
    Nonempty <| CellRun M (atLeft i) (atRight i) (phaseAt source i)
      (leftSequence i trace) (rightSequence i trace) (terminalAt target i) := by
  induction trace with
  | refl => simpa using Nonempty.intro (terminalCellRun _ haccept i)
  | @head source next target hstep tail ih =>
      rcases ih haccept with ⟨rest⟩
      rcases hstep with ⟨nextState, written, direction, henabled, hnext⟩
      subst next
      cases direction with
      | stay => exact ⟨prependStay source nextState written henabled tail i rest⟩
      | left => exact ⟨prependLeft source nextState written henabled tail i rest⟩
      | right => exact ⟨prependRight source nextState written henabled tail i rest⟩

private theorem phaseAt_initial {n : ℕ} {M : LBA.Machine Γ Λ}
    (source : DLBA.Cfg Γ Λ n)
    (hstate : source.state = M.initial) (hhead : source.tape.head.val = 0)
    (i : Fin (n + 1)) :
    phaseAt source i =
      (if atLeft i then .active M.initial (source.tape.contents i)
       else .outside .left (source.tape.contents i)) := by
  by_cases hi : i.val = 0
  · have hEq : source.tape.head = i := Fin.ext (hhead.trans hi.symm)
    simp [phaseAt, atLeft, hi, hEq, hstate]
  · have hNe : source.tape.head ≠ i := by
      intro h
      have := congrArg Fin.val h
      omega
    have hLt : source.tape.head.val < i.val := by omega
    simp [phaseAt, atLeft, hi, hNe, hLt]

theorem cellCompatible_of_accepting_trace {n : ℕ} {M : LBA.Machine Γ Λ}
    {source target : DLBA.Cfg Γ Λ n}
    (trace : LBA.StepTrace M source target)
    (haccept : M.accept target.state = true)
    (hstate : source.state = M.initial) (hhead : source.tape.head.val = 0)
    (i : Fin (n + 1)) :
    CellCompatible M (atLeft i) (atRight i) (source.tape.contents i)
      (leftSequence i trace) (rightSequence i trace) (terminalAt target i) := by
  unfold CellCompatible
  rw [← phaseAt_initial source hstate hhead i]
  exact nonempty_cellRun_of_accepting_trace trace haccept i

def traceProfile {n bound : ℕ} {M : LBA.Machine Γ Λ}
    {source target : DLBA.Cfg Γ Λ n}
    (trace : LBA.StepTrace M source target)
    (hbound : ∀ b : Fin n,
      (LBA.StepTrace.crossingSequence b trace).length ≤ bound)
    (b : Fin n) : Profile Λ bound :=
  Profile.ofList (LBA.StepTrace.crossingSequence b trace) (hbound b)

@[simp] theorem traceProfile_list {n bound : ℕ} {M : LBA.Machine Γ Λ}
    {source target : DLBA.Cfg Γ Λ n}
    (trace : LBA.StepTrace M source target)
    (hbound : ∀ b : Fin n,
      (LBA.StepTrace.crossingSequence b trace).length ≤ bound)
    (b : Fin n) :
    (traceProfile trace hbound b).list = LBA.StepTrace.crossingSequence b trace := rfl

theorem cellCompatible_profiles_of_accepting_trace {n bound : ℕ}
    {M : LBA.Machine Γ Λ} {source target : DLBA.Cfg Γ Λ n}
    (trace : LBA.StepTrace M source target)
    (haccept : M.accept target.state = true)
    (hstate : source.state = M.initial) (hhead : source.tape.head.val = 0)
    (hbound : ∀ b : Fin n,
      (LBA.StepTrace.crossingSequence b trace).length ≤ bound)
    (i : Fin (n + 1)) :
    CellCompatible M (atLeft i) (atRight i) (source.tape.contents i)
      (if h : 0 < i.val then
        (traceProfile trace hbound (⟨i.val - 1, by omega⟩ : Fin n)).list else [])
      (if h : i.val < n then
        (traceProfile trace hbound (⟨i.val, h⟩ : Fin n)).list else [])
      (terminalAt target i) := by
  simpa only [traceProfile_list, leftSequence, rightSequence] using
    cellCompatible_of_accepting_trace trace haccept hstate hhead i

def cellSymbolsFrom {n : Nat} (contents : Fin (n + 1) → Γ)
    (start count : Nat) (hbound : start + count ≤ n + 1) : List Γ :=
  List.ofFn fun j : Fin count => contents ⟨start + j.val, by omega⟩

@[simp] theorem cellSymbolsFrom_zero {n start : Nat}
    (contents : Fin (n + 1) → Γ) (hbound : start + 0 ≤ n + 1) :
    cellSymbolsFrom contents start 0 hbound = [] := rfl

theorem cellSymbolsFrom_succ {n start count : Nat}
    (contents : Fin (n + 1) → Γ) (hbound : start + (count + 1) ≤ n + 1) :
    cellSymbolsFrom contents start (count + 1) hbound =
      contents ⟨start, by omega⟩ ::
        cellSymbolsFrom contents (start + 1) count (by omega) := by
  simp only [cellSymbolsFrom, List.ofFn_succ]
  congr 1
  apply congrArg List.ofFn
  funext j
  apply congrArg contents
  apply Fin.ext
  simp only [Fin.val_succ]
  omega

private theorem nonempty_pendingCertificate_of_accepting_trace
    {n bound : Nat} {M : LBA.Machine Γ Λ}
    {source target : DLBA.Cfg Γ Λ n}
    (trace : LBA.StepTrace M source target)
    (haccept : M.accept target.state = true)
    (hstate : source.state = M.initial) (hhead : source.tape.head.val = 0)
    (hbound : ∀ b : Fin n,
      (LBA.StepTrace.crossingSequence b trace).length ≤ bound)
    (i : Nat) (hiPos : 0 < i) (hiLe : i ≤ n)
    (seen : Bool) (hseen : seen = true ↔ target.tape.head.val < i) :
    Nonempty <| PendingCellCertificate M bound
      (source.tape.contents ⟨i, by omega⟩)
      (traceProfile trace hbound (⟨i - 1, by omega⟩ : Fin n)) seen
      (cellSymbolsFrom source.tape.contents (i + 1) (n - i) (by omega)) := by
  by_cases hiLast : i = n
  · subst i
    let index : Fin (n + 1) := ⟨n, by omega⟩
    have hc := cellCompatible_profiles_of_accepting_trace trace haccept hstate hhead
      hbound index
    have hleft : 0 < index.val := by simpa [index] using hiPos
    have hn0 : n ≠ 0 := by omega
    have hcompatible : CellCompatible M false true
        (source.tape.contents index)
        (traceProfile trace hbound (⟨n - 1, by omega⟩ : Fin n)).list []
        (terminalAt target index) := by
      simpa [index, atLeft, atRight, hleft, hn0] using hc
    have hnotBoth : ¬ (seen = true ∧ terminalAt target index = true) := by
      rintro ⟨hs, ht⟩
      have hslt := hseen.mp hs
      have hEq := (terminalAt_eq_true_iff target index).mp ht
      have hv := congrArg Fin.val hEq
      dsimp only [index] at hv
      omega
    have hsome : (seen || terminalAt target index) = true := by
      apply Bool.or_eq_true_iff.mpr
      by_cases hs : target.tape.head.val < n
      · exact Or.inl (hseen.mpr hs)
      · right
        apply (terminalAt_eq_true_iff target index).mpr
        apply Fin.ext
        dsimp only [index]
        have := target.tape.head.isLt
        omega
    have certificate := PendingCellCertificate.last hcompatible hnotBoth hsome
    simpa [index, cellSymbolsFrom] using Nonempty.intro certificate
  · have hiLt : i < n := by omega
    let index : Fin (n + 1) := ⟨i, by omega⟩
    let nextIndex : Fin (n + 1) := ⟨i + 1, by omega⟩
    have hc := cellCompatible_profiles_of_accepting_trace trace haccept hstate hhead
      hbound index
    have hi0 : i ≠ 0 := by omega
    have hin : i ≠ n := by omega
    have hcompatible : CellCompatible M false false
        (source.tape.contents index)
        (traceProfile trace hbound (⟨i - 1, by omega⟩ : Fin n)).list
        (traceProfile trace hbound (⟨i, hiLt⟩ : Fin n)).list
        (terminalAt target index) := by
      simpa [index, atLeft, atRight, hiPos, hiLt, hi0, hin] using hc
    have hnotBoth : ¬ (seen = true ∧ terminalAt target index = true) := by
      rintro ⟨hs, ht⟩
      have hslt := hseen.mp hs
      have hEq := (terminalAt_eq_true_iff target index).mp ht
      have hv := congrArg Fin.val hEq
      dsimp only [index] at hv
      omega
    have hseenNext : (seen || terminalAt target index) = true ↔
        target.tape.head.val < i + 1 := by
      constructor
      · intro h
        rcases Bool.or_eq_true_iff.mp h with hs | ht
        · exact Nat.lt_succ_of_lt (hseen.mp hs)
        · have hEq := (terminalAt_eq_true_iff target index).mp ht
          have hv := congrArg Fin.val hEq
          dsimp only [index] at hv
          omega
      · intro h
        apply Bool.or_eq_true_iff.mpr
        by_cases hs : target.tape.head.val < i
        · exact Or.inl (hseen.mpr hs)
        · right
          apply (terminalAt_eq_true_iff target index).mpr
          apply Fin.ext
          dsimp only [index]
          omega
    rcases nonempty_pendingCertificate_of_accepting_trace trace haccept hstate hhead
      hbound (i + 1) (by omega) (by omega)
      (seen || terminalAt target index) hseenNext with ⟨tail⟩
    have tail' : PendingCellCertificate M bound
        (source.tape.contents nextIndex)
        (traceProfile trace hbound (⟨i, hiLt⟩ : Fin n))
        (seen || terminalAt target index)
        (cellSymbolsFrom source.tape.contents (i + 2) (n - (i + 1)) (by omega)) := by
      simpa [nextIndex] using tail
    have certificate := PendingCellCertificate.more hcompatible hnotBoth tail'
    have hrest :
        cellSymbolsFrom source.tape.contents (i + 1) (n - i) (by omega) =
          source.tape.contents nextIndex ::
            cellSymbolsFrom source.tape.contents (i + 2) (n - (i + 1)) (by omega) := by
      have hs := cellSymbolsFrom_succ source.tape.contents
        (start := i + 1) (count := n - (i + 1)) (by omega)
      have hcount : n - i = n - (i + 1) + 1 := by omega
      dsimp only [nextIndex]
      simpa only [hcount, Nat.add_assoc] using hs
    rw [hrest]
    exact ⟨certificate⟩
termination_by n - i

/-- Completeness of the bounded spatial certificate: an accepting initial-head trace whose
chronological profile at every internal boundary has length at most `bound` supplies exactly the
shared profiles and exactly one terminal cell required by `CellCertificate`. -/
theorem nonempty_cellCertificate_of_accepting_trace
    {n bound : Nat} {M : LBA.Machine Γ Λ}
    {source target : DLBA.Cfg Γ Λ n}
    (trace : LBA.StepTrace M source target)
    (haccept : M.accept target.state = true)
    (hstate : source.state = M.initial) (hhead : source.tape.head.val = 0)
    (hbound : ∀ b : Fin n,
      (LBA.StepTrace.crossingSequence b trace).length ≤ bound) :
    Nonempty (CellCertificate M bound source.tape.contents) := by
  cases n with
  | zero =>
      let index : Fin 1 := ⟨0, by omega⟩
      have hc := cellCompatible_profiles_of_accepting_trace trace haccept hstate hhead
        hbound index
      have hterminal : terminalAt target index = true := by
        apply (terminalAt_eq_true_iff target index).mpr
        apply Fin.ext
        omega
      rw [hterminal] at hc
      have hcompatible : CellCompatible M true true
          (source.tape.contents index) [] [] true := by
        simpa [index, atLeft, atRight, hterminal] using hc
      have certificate : ListCellCertificate M bound [source.tape.contents index] :=
        .one hcompatible
      simpa [CellCertificate, index, List.ofFn_succ] using Nonempty.intro certificate
  | succ n =>
      let first : Fin (n + 2) := ⟨0, by omega⟩
      let second : Fin (n + 2) := ⟨1, by omega⟩
      let right : Profile Λ bound := traceProfile trace hbound (⟨0, by omega⟩ : Fin (n + 1))
      let terminal := terminalAt target first
      have hc := cellCompatible_profiles_of_accepting_trace trace haccept hstate hhead
        hbound first
      have hcompatible : CellCompatible M true false
          (source.tape.contents first) [] right.list terminal := by
        simpa [first, right, terminal, atLeft, atRight] using hc
      have hseen : terminal = true ↔ target.tape.head.val < 1 := by
        constructor
        · intro ht
          have hEq := (terminalAt_eq_true_iff target first).mp ht
          have hv := congrArg Fin.val hEq
          dsimp only [first] at hv
          omega
        · intro ht
          apply (terminalAt_eq_true_iff target first).mpr
          apply Fin.ext
          dsimp only [first]
          omega
      rcases nonempty_pendingCertificate_of_accepting_trace trace haccept hstate hhead
        hbound 1 (by omega) (by omega) terminal hseen with ⟨tail⟩
      have tail' : PendingCellCertificate M bound
          (source.tape.contents second) right terminal
          (cellSymbolsFrom source.tape.contents 2 n (by omega)) := by
        simpa [second, right] using tail
      have certificate := ListCellCertificate.many right terminal hcompatible tail'
      have htotal : List.ofFn source.tape.contents =
          cellSymbolsFrom source.tape.contents 0 (n + 2) (by omega) := by
        unfold cellSymbolsFrom
        apply congrArg List.ofFn
        funext j
        apply congrArg source.tape.contents
        apply Fin.ext
        simp
      have hfirst := cellSymbolsFrom_succ source.tape.contents
        (start := 0) (count := n + 1) (by omega)
      have hsecond := cellSymbolsFrom_succ source.tape.contents
        (start := 1) (count := n) (by omega)
      change Nonempty (ListCellCertificate M bound (List.ofFn source.tape.contents))
      rw [htotal, hfirst, hsecond]
      simpa [first, second] using Nonempty.intro certificate



/-- Immediate automaton-level completeness corollary. -/
theorem mem_profileNFA_of_accepting_trace
    {n bound : Nat} {M : LBA.Machine Γ Λ}
    {source target : DLBA.Cfg Γ Λ n}
    (trace : LBA.StepTrace M source target)
    (haccept : M.accept target.state = true)
    (hstate : source.state = M.initial) (hhead : source.tape.head.val = 0)
    (hbound : ∀ b : Fin n,
      (LBA.StepTrace.crossingSequence b trace).length ≤ bound) :
    List.ofFn source.tape.contents ∈ (profileNFA M bound).accepts := by
  exact (mem_profileNFA_iff_nonempty_cellCertificate M bound n source.tape.contents).2
    (nonempty_cellCertificate_of_accepting_trace trace haccept hstate hhead hbound)

/-- A bounded-crossing accepting witness from an initial-state, leftmost-head configuration is
accepted by the finite profile automaton. -/
theorem mem_profileNFA_of_acceptsWithBound
    {n bound : Nat} {M : LBA.Machine Γ Λ}
    {source : DLBA.Cfg Γ Λ n}
    (haccept : AcceptsWithBound M source bound)
    (hstate : source.state = M.initial) (hhead : source.tape.head.val = 0) :
    List.ofFn source.tape.contents ∈ (profileNFA M bound).accepts := by
  obtain ⟨target, trace, hfinal, hcross⟩ := haccept
  apply mem_profileNFA_of_accepting_trace trace hfinal hstate hhead
  intro b
  simpa using hcross b

end LBA.BoundedCrossing

end
