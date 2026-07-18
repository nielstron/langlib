module

public import Langlib.Automata.LinearBounded.BoundedCrossingCertificate
public import Langlib.Automata.LinearBounded.StepTraceCrossing
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Tactic

@[expose]
public section

/-!
# Soundness of bounded-crossing spatial certificates

A row of neighboring-compatible one-cell histories is not merely a collection of local checks:
it synchronizes to a genuine global LBA computation.  This module proves that fact by following
the unique active cell.  A stationary or physically clamped transition peels one local
constructor; a genuine head move peels the active cell's exit together with the adjacent cell's
matching entry.  The sum of all local-history sizes is a well-founded decreasing measure.

The construction works for every positive tape width, including a one-cell tape, permits writes
and clamped endpoint moves, and allows the accepting state to occur at any cell.  The final
sections realize list- and width-indexed `CellCertificate` values as synchronized rows, retain
the profile length bound, and derive ordinary LBA acceptance from the exact function-valued
initial configuration.
-/

namespace LBA.BoundedCrossing

universe u v
variable {Γ : Type u} {Λ : Type v}

namespace Phase

def symbol : Phase Γ Λ → Γ
  | .active _ a => a
  | .outside _ a => a

end Phase

namespace Soundness

def atLeft {n : ℕ} (i : Fin (n + 1)) : Bool := decide (i.val = 0)
def atRight {n : ℕ} (i : Fin (n + 1)) : Bool := decide (i.val = n)

def castCellRunFlags {M : LBA.Machine Γ Λ} {al ar al' ar' : Bool}
    {phase : Phase Γ Λ} {left right : List Λ} {terminal : Bool}
    (run : CellRun M al ar phase left right terminal)
    (hl : al = al') (hr : ar = ar') :
    CellRun M al' ar' phase left right terminal := by
  rw [← hl, ← hr]
  exact run

@[simp] theorem size_castCellRunFlags {M : LBA.Machine Γ Λ} {al ar al' ar' : Bool}
    {phase : Phase Γ Λ} {left right : List Λ} {terminal : Bool}
    (run : CellRun M al ar phase left right terminal)
    (hl : al = al') (hr : ar = ar') :
    (castCellRunFlags run hl hr).size = run.size := by
  subst al'
  subst ar'
  rfl

structure PackedCell (M : LBA.Machine Γ Λ) (al ar : Bool) where
  phase : Phase Γ Λ
  left : List Λ
  right : List Λ
  terminal : Bool
  run : CellRun M al ar phase left right terminal

def PackedCell.castFlags {M : LBA.Machine Γ Λ} {al ar al' ar' : Bool}
    (cell : PackedCell M al ar) (hl : al = al') (hr : ar = ar') :
    PackedCell M al' ar' :=
  ⟨cell.phase, cell.left, cell.right, cell.terminal,
    castCellRunFlags cell.run hl hr⟩

@[simp] theorem PackedCell.phase_castFlags {M : LBA.Machine Γ Λ} {al ar al' ar' : Bool}
    (cell : PackedCell M al ar) (hl : al = al') (hr : ar = ar') :
    (cell.castFlags hl hr).phase = cell.phase := rfl

@[simp] theorem PackedCell.left_castFlags {M : LBA.Machine Γ Λ} {al ar al' ar' : Bool}
    (cell : PackedCell M al ar) (hl : al = al') (hr : ar = ar') :
    (cell.castFlags hl hr).left = cell.left := rfl

@[simp] theorem PackedCell.right_castFlags {M : LBA.Machine Γ Λ} {al ar al' ar' : Bool}
    (cell : PackedCell M al ar) (hl : al = al') (hr : ar = ar') :
    (cell.castFlags hl hr).right = cell.right := rfl

abbrev Row (M : LBA.Machine Γ Λ) (n : ℕ) :=
  (i : Fin (n + 1)) → PackedCell M (atLeft i) (atRight i)

def Row.symbols {M : LBA.Machine Γ Λ} {n : ℕ} (row : Row M n) : Fin (n + 1) → Γ :=
  fun i => row i |>.phase.symbol

def expectedPhase {M : LBA.Machine Γ Λ} {n : ℕ}
    (row : Row M n) (head : Fin (n + 1)) (q : Λ) (i : Fin (n + 1)) : Phase Γ Λ :=
  if i = head then .active q (row i).phase.symbol
  else if i.val < head.val then .outside .right (row i).phase.symbol
  else .outside .left (row i).phase.symbol

def Aligned {M : LBA.Machine Γ Λ} {n : ℕ}
    (row : Row M n) (head : Fin (n + 1)) (q : Λ) : Prop :=
  ∀ i, (row i).phase = expectedPhase row head q i

def BoundaryMatched {M : LBA.Machine Γ Λ} {n : ℕ} (row : Row M n) : Prop :=
  (row ⟨0, Nat.zero_lt_succ _⟩).left = [] ∧
  (row ⟨n, Nat.lt_succ_self _⟩).right = [] ∧
  ∀ b : Fin n, (row b.castSucc).right = (row b.succ).left

def cfgOf {M : LBA.Machine Γ Λ} {n : ℕ}
    (row : Row M n) (head : Fin (n + 1)) (q : Λ) : DLBA.Cfg Γ Λ n :=
  ⟨q, ⟨row.symbols, head⟩⟩

def Row.weight {M : LBA.Machine Γ Λ} {n : ℕ} (row : Row M n) : ℕ :=
  ∑ i, (row i).run.size

@[simp] theorem expectedPhase_head {M : LBA.Machine Γ Λ} {n : ℕ}
    (row : Row M n) (head : Fin (n + 1)) (q : Λ) :
    expectedPhase row head q head = .active q (row head).phase.symbol := by
  simp [expectedPhase]

theorem Aligned.at_head {M : LBA.Machine Γ Λ} {n : ℕ}
    {row : Row M n} {head : Fin (n + 1)} {q : Λ} (h : Aligned row head q) :
    (row head).phase = .active q (row head).phase.symbol := by
  simpa using h head

theorem Aligned.left_of_lt {M : LBA.Machine Γ Λ} {n : ℕ}
    {row : Row M n} {head i : Fin (n + 1)} {q : Λ} (h : Aligned row head q)
    (hi : i.val < head.val) :
    (row i).phase = .outside .right (row i).phase.symbol := by
  simpa [expectedPhase, Fin.ne_of_lt hi, hi] using h i

theorem Aligned.right_of_lt {M : LBA.Machine Γ Λ} {n : ℕ}
    {row : Row M n} {head i : Fin (n + 1)} {q : Λ} (h : Aligned row head q)
    (hi : head.val < i.val) :
    (row i).phase = .outside .left (row i).phase.symbol := by
  have hnot : ¬ i.val < head.val := by omega
  simpa [expectedPhase, Fin.ne_of_gt hi, hnot] using h i

def peelEnterLeft {M : LBA.Machine Γ Λ} {al ar : Bool} {a : Γ} {q : Λ}
    {left right : List Λ} {terminal : Bool}
    (run : CellRun M al ar (.outside .left a) (q :: left) right terminal) :
    CellRun M al ar (.active q a) left right terminal := by
  cases run with
  | enterLeft rest => exact rest

def peelEnterRight {M : LBA.Machine Γ Λ} {al ar : Bool} {a : Γ} {q : Λ}
    {left right : List Λ} {terminal : Bool}
    (run : CellRun M al ar (.outside .right a) left (q :: right) terminal) :
    CellRun M al ar (.active q a) left right terminal := by
  cases run with
  | enterRight rest => exact rest

theorem size_peelEnterLeft {M : LBA.Machine Γ Λ} {al ar : Bool} {a : Γ} {q : Λ}
    {left right : List Λ} {terminal : Bool}
    (run : CellRun M al ar (.outside .left a) (q :: left) right terminal) :
    (peelEnterLeft run).size + 1 = run.size := by
  cases run with
  | enterLeft rest => rfl

theorem size_peelEnterRight {M : LBA.Machine Γ Λ} {al ar : Bool} {a : Γ} {q : Λ}
    {left right : List Λ} {terminal : Bool}
    (run : CellRun M al ar (.outside .right a) left (q :: right) terminal) :
    (peelEnterRight run).size + 1 = run.size := by
  cases run with
  | enterRight rest => rfl

def Row.set {M : LBA.Machine Γ Λ} {n : ℕ} (row : Row M n) (i : Fin (n + 1))
    (cell : PackedCell M (atLeft i) (atRight i)) : Row M n :=
  Function.update row i cell

@[simp] theorem Row.set_apply_self {M : LBA.Machine Γ Λ} {n : ℕ} (row : Row M n)
    (i : Fin (n + 1)) (cell : PackedCell M (atLeft i) (atRight i)) :
    row.set i cell i = cell := by
  simp [Row.set]

@[simp] theorem Row.set_apply_of_ne {M : LBA.Machine Γ Λ} {n : ℕ} (row : Row M n)
    (i j : Fin (n + 1)) (cell : PackedCell M (atLeft i) (atRight i)) (h : j ≠ i) :
    row.set i cell j = row j := by
  simp [Row.set, h]

theorem Row.set_left_of_eq {M : LBA.Machine Γ Λ} {n : ℕ} (row : Row M n)
    (i j : Fin (n + 1)) (cell : PackedCell M (atLeft i) (atRight i)) (h : j = i) :
    (row.set i cell j).left = cell.left := by
  subst j
  simp

theorem Row.set_right_of_eq {M : LBA.Machine Γ Λ} {n : ℕ} (row : Row M n)
    (i j : Fin (n + 1)) (cell : PackedCell M (atLeft i) (atRight i)) (h : j = i) :
    (row.set i cell j).right = cell.right := by
  subst j
  simp

theorem Row.set_left_of_ne {M : LBA.Machine Γ Λ} {n : ℕ} (row : Row M n)
    (i j : Fin (n + 1)) (cell : PackedCell M (atLeft i) (atRight i)) (h : j ≠ i) :
    (row.set i cell j).left = (row j).left := by
  rw [Row.set_apply_of_ne row i j cell h]

theorem Row.set_right_of_ne {M : LBA.Machine Γ Λ} {n : ℕ} (row : Row M n)
    (i j : Fin (n + 1)) (cell : PackedCell M (atLeft i) (atRight i)) (h : j ≠ i) :
    (row.set i cell j).right = (row j).right := by
  rw [Row.set_apply_of_ne row i j cell h]

theorem Row.set_phase_of_eq {M : LBA.Machine Γ Λ} {n : ℕ} (row : Row M n)
    (i j : Fin (n + 1)) (cell : PackedCell M (atLeft i) (atRight i)) (h : j = i) :
    (row.set i cell j).phase = cell.phase := by
  subst j
  simp

theorem Row.set_phase_of_ne {M : LBA.Machine Γ Λ} {n : ℕ} (row : Row M n)
    (i j : Fin (n + 1)) (cell : PackedCell M (atLeft i) (atRight i)) (h : j ≠ i) :
    (row.set i cell j).phase = (row j).phase := by
  rw [Row.set_apply_of_ne row i j cell h]

theorem Row.weight_set_lt {M : LBA.Machine Γ Λ} {n : ℕ} (row : Row M n)
    (i : Fin (n + 1)) (cell : PackedCell M (atLeft i) (atRight i))
    (hsize : cell.run.size < (row i).run.size) :
    (row.set i cell).weight < row.weight := by
  classical
  unfold Row.weight
  rw [Finset.sum_eq_add_sum_diff_singleton (s := Finset.univ) (i := i) (f := fun j =>
      ((row.set i cell) j).run.size) (by simp)]
  rw [Finset.sum_eq_add_sum_diff_singleton (s := Finset.univ) (i := i) (f := fun j =>
      (row j).run.size) (by simp)]
  rw [Row.set_apply_self]
  have hsums :
      (∑ x ∈ Finset.univ \ {i}, ((row.set i cell) x).run.size) =
        ∑ x ∈ Finset.univ \ {i}, (row x).run.size := by
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_singleton] at hj
    rw [Row.set_apply_of_ne row i j cell hj]
  rw [hsums]
  exact Nat.add_lt_add_right hsize _

def PackedCell.castPhase {M : LBA.Machine Γ Λ} {al ar : Bool}
    (cell : PackedCell M al ar) (p : Phase Γ Λ) (h : cell.phase = p) :
    CellRun M al ar p cell.left cell.right cell.terminal := by
  rw [← h]
  exact cell.run

def PackedCell.castRun {M : LBA.Machine Γ Λ} {al ar : Bool}
    (cell : PackedCell M al ar) {p : Phase Γ Λ} {left right : List Λ}
    {terminal : Bool} (hp : cell.phase = p) (hl : cell.left = left)
    (hr : cell.right = right) (ht : cell.terminal = terminal) :
    CellRun M al ar p left right terminal := by
  rw [← hp, ← hl, ← hr, ← ht]
  exact cell.run

@[simp] theorem PackedCell.size_castPhase {M : LBA.Machine Γ Λ} {al ar : Bool}
    (cell : PackedCell M al ar) (p : Phase Γ Λ) (h : cell.phase = p) :
    (cell.castPhase p h).size = cell.run.size := by
  subst p
  rfl

@[simp] theorem PackedCell.size_castRun {M : LBA.Machine Γ Λ} {al ar : Bool}
    (cell : PackedCell M al ar) {p : Phase Γ Λ} {left right : List Λ}
    {terminal : Bool} (hp : cell.phase = p) (hl : cell.left = left)
    (hr : cell.right = right) (ht : cell.terminal = terminal) :
    (cell.castRun hp hl hr ht).size = cell.run.size := by
  subst p
  subst left
  subst right
  subst terminal
  rfl

def Row.activeRun {M : LBA.Machine Γ Λ} {n : ℕ} {row : Row M n}
    {head : Fin (n + 1)} {q : Λ} (h : Aligned row head q) :
    CellRun M (atLeft head) (atRight head)
      (.active q (row head).phase.symbol) (row head).left (row head).right
      (row head).terminal :=
  (row head).castPhase _ h.at_head

theorem BoundaryMatched.congr {M : LBA.Machine Γ Λ} {n : ℕ}
    {row row' : Row M n} (h : BoundaryMatched row)
    (hleft : ∀ i, (row' i).left = (row i).left)
    (hright : ∀ i, (row' i).right = (row i).right) :
    BoundaryMatched row' := by
  rcases h with ⟨hl, hr, hm⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [hleft]
    exact hl
  · rw [hright]
    exact hr
  · intro b
    rw [hright, hleft]
    exact hm b

theorem BoundaryMatched.set_same_interfaces {M : LBA.Machine Γ Λ} {n : ℕ}
    {row : Row M n} (h : BoundaryMatched row) (i : Fin (n + 1))
    (cell : PackedCell M (atLeft i) (atRight i))
    (hl : cell.left = (row i).left) (hr : cell.right = (row i).right) :
    BoundaryMatched (row.set i cell) := by
  apply h.congr
  · intro j
    by_cases hj : j = i
    · subst j
      simpa using hl
    · simp [Row.set_apply_of_ne, hj]
  · intro j
    by_cases hj : j = i
    · subst j
      simpa using hr
    · simp [Row.set_apply_of_ne, hj]

theorem Fin.castSucc_ne_succ {n : ℕ} (b : Fin n) :
    b.castSucc ≠ b.succ := by
  intro h
  have := congrArg Fin.val h
  simp at this

theorem BoundaryMatched.set_adjacent {M : LBA.Machine Γ Λ} {n : ℕ}
    {row : Row M n} (h : BoundaryMatched row) (b : Fin n)
    (lc : PackedCell M (atLeft b.castSucc) (atRight b.castSucc))
    (rc : PackedCell M (atLeft b.succ) (atRight b.succ))
    (hl_outer : lc.left = (row b.castSucc).left)
    (hshared : lc.right = rc.left)
    (hr_outer : rc.right = (row b.succ).right) :
    BoundaryMatched ((row.set b.castSucc lc).set b.succ rc) := by
  classical
  rcases h with ⟨houterL, houterR, hmatch⟩
  refine ⟨?_, ?_, ?_⟩
  · let z : Fin (n + 1) := ⟨0, Nat.zero_lt_succ n⟩
    have hzs : z ≠ b.succ := by
      intro heq
      have hv := congrArg Fin.val heq
      simp [z] at hv
    rw [Row.set_left_of_ne _ _ _ _ hzs]
    by_cases hz : z = b.castSucc
    · rw [Row.set_left_of_eq _ _ _ _ hz, hl_outer]
      have := houterL
      change (row z).left = [] at this
      exact (congrArg (fun k => (row k).left) hz.symm).trans this
    · rw [Row.set_left_of_ne _ _ _ _ hz]
      change (row z).left = []
      exact houterL
  · let last : Fin (n + 1) := ⟨n, Nat.lt_succ_self n⟩
    have hnl : last ≠ b.castSucc := by
      intro heq
      have hv := congrArg Fin.val heq
      have hb := b.isLt
      simp [last] at hv
      omega
    by_cases hn : last = b.succ
    · rw [Row.set_right_of_eq _ _ _ _ hn, hr_outer]
      have hout : (row last).right = [] := houterR
      exact (congrArg (fun k => (row k).right) hn.symm).trans hout
    · rw [Row.set_right_of_ne _ _ _ _ hn, Row.set_right_of_ne _ _ _ _ hnl]
      change (row last).right = []
      exact houterR
  · intro b'
    by_cases hb : b' = b
    · subst b'
      rw [Row.set_right_of_ne _ _ _ _ (Fin.castSucc_ne_succ b),
        Row.set_right_of_eq _ _ _ _ rfl, Row.set_left_of_eq _ _ _ _ rfl]
      exact hshared
    · have hll : b'.castSucc ≠ b.castSucc := by
        intro heq
        apply hb
        apply Fin.ext
        simpa using congrArg Fin.val heq
      have hrr : b'.succ ≠ b.succ := by
        intro heq
        apply hb
        exact Fin.ext (by simpa using congrArg Fin.val heq)
      by_cases hrl : b'.succ = b.castSucc
      · have hleftSucc : b'.castSucc ≠ b.succ := by
          intro heq
          have h1 := congrArg Fin.val hrl
          have h2 := congrArg Fin.val heq
          simp at h1 h2
          omega
        rw [Row.set_right_of_ne _ _ _ _ hleftSucc,
          Row.set_right_of_ne _ _ _ _ hll,
          Row.set_left_of_ne _ _ _ _ hrr,
          Row.set_left_of_eq _ _ _ _ hrl, hl_outer]
        have hm := hmatch b'
        rw [hrl] at hm
        exact hm
      · by_cases hlr : b'.castSucc = b.succ
        · have hrightCast : b'.succ ≠ b.castSucc := hrl
          rw [Row.set_right_of_eq _ _ _ _ hlr,
            Row.set_left_of_ne _ _ _ _ hrr,
            Row.set_left_of_ne _ _ _ _ hrightCast,
            hr_outer]
          have hm := hmatch b'
          rw [hlr] at hm
          exact hm
        · rw [Row.set_right_of_ne _ _ _ _ hlr,
            Row.set_right_of_ne _ _ _ _ hll,
            Row.set_left_of_ne _ _ _ _ hrr,
            Row.set_left_of_ne _ _ _ _ hrl]
          exact hmatch b'

theorem Aligned.set_head {M : LBA.Machine Γ Λ} {n : ℕ}
    {row : Row M n} {head : Fin (n + 1)} {q q' : Λ} (h : Aligned row head q)
    (cell : PackedCell M (atLeft head) (atRight head)) {written : Γ}
    (hphase : cell.phase = .active q' written) :
    Aligned (row.set head cell) head q' := by
  intro i
  by_cases hi : i = head
  · subst i
    rw [Row.set_phase_of_eq _ _ _ _ rfl, hphase]
    unfold expectedPhase
    rw [if_pos rfl]
    congr 2
    have hs := congrArg Phase.symbol hphase
    simpa [Phase.symbol] using hs.symm
  · rw [Row.set_phase_of_ne _ _ _ _ hi]
    have hold := h i
    simpa [expectedPhase, hi, Row.set_phase_of_ne, Phase.symbol] using hold

theorem lt_succ_iff_lt_castSucc_of_ne {n : ℕ} (i : Fin (n + 1)) (b : Fin n)
    (h : i ≠ b.castSucc) :
    i.val < b.succ.val ↔ i.val < b.castSucc.val := by
  have hval : i.val ≠ b.val := by
    intro hv
    apply h
    exact Fin.ext (by simpa using hv)
  simp
  omega

theorem Aligned.set_move_right {M : LBA.Machine Γ Λ} {n : ℕ}
    {row : Row M n} {q q' : Λ} (b : Fin n) (h : Aligned row b.castSucc q)
    (lc : PackedCell M (atLeft b.castSucc) (atRight b.castSucc))
    (rc : PackedCell M (atLeft b.succ) (atRight b.succ))
    {leftWritten rightSymbol : Γ}
    (hlphase : lc.phase = .outside .right leftWritten)
    (hrphase : rc.phase = .active q' rightSymbol) :
    Aligned ((row.set b.castSucc lc).set b.succ rc) b.succ q' := by
  intro i
  by_cases hir : i = b.succ
  · rw [Row.set_phase_of_eq _ _ _ _ hir, hrphase]
    unfold expectedPhase
    rw [if_pos hir]
    congr 2
    have hs := congrArg Phase.symbol hrphase
    have hnew := congrArg Phase.symbol
      (Row.set_phase_of_eq (row.set b.castSucc lc) b.succ i rc hir)
    have hs' : rightSymbol = rc.phase.symbol := by
      simpa [Phase.symbol] using hs.symm
    exact hs'.trans hnew.symm
  · rw [Row.set_phase_of_ne _ _ _ _ hir]
    by_cases hil : i = b.castSucc
    · rw [Row.set_phase_of_eq _ _ _ _ hil, hlphase]
      have hv : i.val < b.succ.val := by simp [hil]
      unfold expectedPhase
      rw [if_neg hir, if_pos hv]
      congr 2
      have hs := congrArg Phase.symbol hlphase
      have hnew1 := congrArg Phase.symbol
        (Row.set_phase_of_ne (row.set b.castSucc lc) b.succ i rc hir)
      have hnew2 := congrArg Phase.symbol
        (Row.set_phase_of_eq row b.castSucc i lc hil)
      have hs' : leftWritten = lc.phase.symbol := by
        simpa [Phase.symbol] using hs.symm
      exact hs'.trans (hnew1.trans hnew2).symm
    · rw [Row.set_phase_of_ne _ _ _ _ hil]
      have hold := h i
      have hgap := lt_succ_iff_lt_castSucc_of_ne i b hil
      have hneold : i ≠ b.castSucc := hil
      by_cases hs : i.val < b.castSucc.val
      · have hs' : i.val < b.succ.val := hgap.mpr hs
        have hsb : i.val < b.val := by simpa using hs
        have hsb' : i.val ≤ b.val := by simpa using hs'
        simpa [expectedPhase, hir, hneold, hsb, hsb', Row.set_phase_of_ne] using hold
      · have hs' : ¬ i.val < b.succ.val := fun hh => hs (hgap.mp hh)
        have hsb : ¬ i.val < b.val := by simpa using hs
        have hsb' : ¬ i.val ≤ b.val := by simpa using hs'
        simpa [expectedPhase, hir, hneold, hsb, hsb', Row.set_phase_of_ne] using hold

theorem Aligned.set_move_left {M : LBA.Machine Γ Λ} {n : ℕ}
    {row : Row M n} {q q' : Λ} (b : Fin n) (h : Aligned row b.succ q)
    (lc : PackedCell M (atLeft b.castSucc) (atRight b.castSucc))
    (rc : PackedCell M (atLeft b.succ) (atRight b.succ))
    {leftSymbol rightWritten : Γ}
    (hlphase : lc.phase = .active q' leftSymbol)
    (hrphase : rc.phase = .outside .left rightWritten) :
    Aligned ((row.set b.castSucc lc).set b.succ rc) b.castSucc q' := by
  intro i
  by_cases hir : i = b.succ
  · rw [Row.set_phase_of_eq _ _ _ _ hir, hrphase]
    have hv : b.castSucc.val < i.val := by simp [hir]
    unfold expectedPhase
    rw [if_neg (Fin.ne_of_gt hv), if_neg (by omega)]
    congr 2
    have hs := congrArg Phase.symbol hrphase
    have hnew := congrArg Phase.symbol
      (Row.set_phase_of_eq (row.set b.castSucc lc) b.succ i rc hir)
    have hs' : rightWritten = rc.phase.symbol := by
      simpa [Phase.symbol] using hs.symm
    exact hs'.trans hnew.symm
  · rw [Row.set_phase_of_ne _ _ _ _ hir]
    by_cases hil : i = b.castSucc
    · rw [Row.set_phase_of_eq _ _ _ _ hil, hlphase]
      unfold expectedPhase
      rw [if_pos hil]
      congr 2
      have hs := congrArg Phase.symbol hlphase
      have hnew1 := congrArg Phase.symbol
        (Row.set_phase_of_ne (row.set b.castSucc lc) b.succ i rc hir)
      have hnew2 := congrArg Phase.symbol
        (Row.set_phase_of_eq row b.castSucc i lc hil)
      have hs' : leftSymbol = lc.phase.symbol := by
        simpa [Phase.symbol] using hs.symm
      exact hs'.trans (hnew1.trans hnew2).symm
    · rw [Row.set_phase_of_ne _ _ _ _ hil]
      have hold := h i
      have hgap := lt_succ_iff_lt_castSucc_of_ne i b hil
      by_cases hs : i.val < b.castSucc.val
      · have hs' : i.val < b.succ.val := hgap.mpr hs
        have hsb : i.val < b.val := by simpa using hs
        have hsb' : i.val ≤ b.val := by simpa using hs'
        simpa [expectedPhase, hir, hil, hsb, hsb', Row.set_phase_of_ne] using hold
      · have hs' : ¬ i.val < b.succ.val := fun hh => hs (hgap.mp hh)
        have hsb : ¬ i.val < b.val := by simpa using hs
        have hsb' : ¬ i.val ≤ b.val := by simpa using hs'
        simpa [expectedPhase, hir, hil, hsb, hsb', Row.set_phase_of_ne] using hold

theorem moveHead_stays {n : ℕ} (tape : DLBA.BoundedTape Γ n) (d : DLBA.Dir)
    (h : DirectionStaysLocal (atLeft tape.head) (atRight tape.head) d) :
    (tape.moveHead d).head = tape.head := by
  cases d with
  | stay => rfl
  | left =>
      have hz : tape.head.val = 0 := by
        simpa [DirectionStaysLocal, atLeft] using h
      simp [DLBA.BoundedTape.moveHead, hz]
  | right =>
      have hn : tape.head.val = n := by
        simpa [DirectionStaysLocal, atRight] using h
      simp [DLBA.BoundedTape.moveHead, hn]

theorem Row.symbols_set_head {M : LBA.Machine Γ Λ} {n : ℕ} (row : Row M n)
    (head : Fin (n + 1)) (cell : PackedCell M (atLeft head) (atRight head))
    {written : Γ} (hphase : cell.phase = .active q written) :
    (row.set head cell).symbols = Function.update row.symbols head written := by
  funext i
  by_cases hi : i = head
  · subst i
    simp only [Row.symbols]
    have hnew := congrArg Phase.symbol
      (Row.set_phase_of_eq row head head cell rfl)
    have hs := congrArg Phase.symbol hphase
    calc
      (row.set head cell head).phase.symbol = cell.phase.symbol := hnew
      _ = written := by simpa [Phase.symbol] using hs
      _ = Function.update row.symbols head written head := by simp
  · simp only [Row.symbols]
    have hnew := congrArg Phase.symbol (Row.set_phase_of_ne row head i cell hi)
    calc
      (row.set head cell i).phase.symbol = (row i).phase.symbol := hnew
      _ = Function.update row.symbols head written i := by
        simp [hi, Row.symbols]

theorem Row.symbols_set_move_right {M : LBA.Machine Γ Λ} {n : ℕ} (row : Row M n)
    (b : Fin n)
    (lc : PackedCell M (atLeft b.castSucc) (atRight b.castSucc))
    (rc : PackedCell M (atLeft b.succ) (atRight b.succ))
    {written neighborSymbol : Γ}
    (hlphase : lc.phase = .outside .right written)
    (hrphase : rc.phase = .active q neighborSymbol)
    (hneighbor : neighborSymbol = (row b.succ).phase.symbol) :
    ((row.set b.castSucc lc).set b.succ rc).symbols =
      Function.update row.symbols b.castSucc written := by
  funext i
  by_cases hir : i = b.succ
  · have hnew := congrArg Phase.symbol
      (Row.set_phase_of_eq (row.set b.castSucc lc) b.succ i rc hir)
    simp only [Row.symbols]
    have hs := congrArg Phase.symbol hrphase
    calc
      (((row.set b.castSucc lc).set b.succ rc) i).phase.symbol = rc.phase.symbol := hnew
      _ = neighborSymbol := by simpa [Phase.symbol] using hs
      _ = (row b.succ).phase.symbol := hneighbor
      _ = (row i).phase.symbol := congrArg (fun k => (row k).phase.symbol) hir.symm
      _ = Function.update row.symbols b.castSucc written i := by
        simp [show i ≠ b.castSucc by
          intro heq
          exact Fin.castSucc_ne_succ b (heq.symm.trans hir), Row.symbols]
  · have hnew1 := congrArg Phase.symbol
      (Row.set_phase_of_ne (row.set b.castSucc lc) b.succ i rc hir)
    by_cases hil : i = b.castSucc
    · have hnew2 := congrArg Phase.symbol
        (Row.set_phase_of_eq row b.castSucc i lc hil)
      have hs := congrArg Phase.symbol hlphase
      calc
        (((row.set b.castSucc lc).set b.succ rc) i).phase.symbol = lc.phase.symbol :=
          hnew1.trans hnew2
        _ = written := by simpa [Phase.symbol] using hs
        _ = Function.update row.symbols b.castSucc written i := by
          simp [Function.update_apply, hil]
    · have hnew2 := congrArg Phase.symbol
        (Row.set_phase_of_ne row b.castSucc i lc hil)
      exact (hnew1.trans hnew2).trans (by
        simp [hil, Row.symbols])

theorem Row.symbols_set_move_left {M : LBA.Machine Γ Λ} {n : ℕ} (row : Row M n)
    (b : Fin n)
    (lc : PackedCell M (atLeft b.castSucc) (atRight b.castSucc))
    (rc : PackedCell M (atLeft b.succ) (atRight b.succ))
    {written neighborSymbol : Γ}
    (hlphase : lc.phase = .active q neighborSymbol)
    (hrphase : rc.phase = .outside .left written)
    (hneighbor : neighborSymbol = (row b.castSucc).phase.symbol) :
    ((row.set b.castSucc lc).set b.succ rc).symbols =
      Function.update row.symbols b.succ written := by
  funext i
  by_cases hir : i = b.succ
  · have hnew := congrArg Phase.symbol
      (Row.set_phase_of_eq (row.set b.castSucc lc) b.succ i rc hir)
    have hs := congrArg Phase.symbol hrphase
    calc
      (((row.set b.castSucc lc).set b.succ rc) i).phase.symbol = rc.phase.symbol := hnew
      _ = written := by simpa [Phase.symbol] using hs
      _ = Function.update row.symbols b.succ written i := by
        simp [Function.update_apply, hir]
  · simp only [Row.symbols]
    have hnew1 := congrArg Phase.symbol
      (Row.set_phase_of_ne (row.set b.castSucc lc) b.succ i rc hir)
    by_cases hil : i = b.castSucc
    · have hnew2 := congrArg Phase.symbol
        (Row.set_phase_of_eq row b.castSucc i lc hil)
      have hs := congrArg Phase.symbol hlphase
      calc
        (((row.set b.castSucc lc).set b.succ rc) i).phase.symbol = lc.phase.symbol :=
          hnew1.trans hnew2
        _ = neighborSymbol := by simpa [Phase.symbol] using hs
        _ = (row b.castSucc).phase.symbol := hneighbor
        _ = (row i).phase.symbol := congrArg (fun k => (row k).phase.symbol) hil.symm
        _ = Function.update row.symbols b.succ written i := by
          simp [hir, Row.symbols]
    · have hnew2 := congrArg Phase.symbol
        (Row.set_phase_of_ne row b.castSucc i lc hil)
      exact (hnew1.trans hnew2).trans (by
        simp [hir, Row.symbols])

theorem step_set_head {M : LBA.Machine Γ Λ} {n : ℕ} {row : Row M n}
    {head : Fin (n + 1)} {q q' : Λ} {written : Γ} {d : DLBA.Dir}
    (henabled : (q', written, d) ∈ M.transition q (row head).phase.symbol)
    (hstays : DirectionStaysLocal (atLeft head) (atRight head) d)
    (cell : PackedCell M (atLeft head) (atRight head))
    (hphase : cell.phase = .active q' written) :
    LBA.Step M (cfgOf row head q) (cfgOf (row.set head cell) head q') := by
  refine ⟨q', written, d, ?_, ?_⟩
  · simpa [cfgOf, DLBA.BoundedTape.read, Row.symbols] using henabled
  · apply congrArg (fun tape => DLBA.Cfg.mk q' tape)
    congr 1
    · exact Row.symbols_set_head row head cell hphase
    · exact (moveHead_stays ((cfgOf row head q).tape.write written) d hstays).symm

theorem step_set_move_right {M : LBA.Machine Γ Λ} {n : ℕ} {row : Row M n}
    {q q' : Λ} (b : Fin n) {written neighborSymbol : Γ}
    (henabled : (q', written, .right) ∈ M.transition q (row b.castSucc).phase.symbol)
    (lc : PackedCell M (atLeft b.castSucc) (atRight b.castSucc))
    (rc : PackedCell M (atLeft b.succ) (atRight b.succ))
    (hlphase : lc.phase = .outside .right written)
    (hrphase : rc.phase = .active q' neighborSymbol)
    (hneighbor : neighborSymbol = (row b.succ).phase.symbol) :
    LBA.Step M (cfgOf row b.castSucc q)
      (cfgOf ((row.set b.castSucc lc).set b.succ rc) b.succ q') := by
  refine ⟨q', written, .right, ?_, ?_⟩
  · simpa [cfgOf, DLBA.BoundedTape.read, Row.symbols] using henabled
  · apply congrArg (fun tape => DLBA.Cfg.mk q' tape)
    congr 1
    · exact Row.symbols_set_move_right row b lc rc hlphase hrphase hneighbor
    · apply Fin.ext
      simp [cfgOf, DLBA.BoundedTape.write]

theorem step_set_move_left {M : LBA.Machine Γ Λ} {n : ℕ} {row : Row M n}
    {q q' : Λ} (b : Fin n) {written neighborSymbol : Γ}
    (henabled : (q', written, .left) ∈ M.transition q (row b.succ).phase.symbol)
    (lc : PackedCell M (atLeft b.castSucc) (atRight b.castSucc))
    (rc : PackedCell M (atLeft b.succ) (atRight b.succ))
    (hlphase : lc.phase = .active q' neighborSymbol)
    (hrphase : rc.phase = .outside .left written)
    (hneighbor : neighborSymbol = (row b.castSucc).phase.symbol) :
    LBA.Step M (cfgOf row b.succ q)
      (cfgOf ((row.set b.castSucc lc).set b.succ rc) b.castSucc q') := by
  refine ⟨q', written, .left, ?_, ?_⟩
  · simpa [cfgOf, DLBA.BoundedTape.read, Row.symbols] using henabled
  · apply congrArg (fun tape => DLBA.Cfg.mk q' tape)
    congr 1
    · exact Row.symbols_set_move_left row b lc rc hlphase hrphase hneighbor

theorem accepts_of_active_row {M : LBA.Machine Γ Λ} {n : ℕ} (row : Row M n)
    (head : Fin (n + 1)) (q : Λ) {left right : List Λ} {terminal : Bool}
    (active : CellRun M (atLeft head) (atRight head)
      (.active q (row head).phase.symbol) left right terminal)
    (hleft : (row head).left = left) (hright : (row head).right = right)
    (hterminal : (row head).terminal = terminal)
    (hsize : active.size = (row head).run.size)
    (halign : Aligned row head q) (hmatched : BoundaryMatched row) :
    LBA.Accepts M (cfgOf row head q) := by
  cases active with
  | terminal haccept =>
      -- Acceptance is existential in a reached global configuration.  Once the active cell is
      -- accepting, any still-unused local suffixes elsewhere in the row are irrelevant.
      exact ⟨cfgOf row head q, Relation.ReflTransGen.refl, haccept⟩
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
      have haccepts : LBA.Accepts M (cfgOf nextRow head nextState) :=
        accepts_of_active_row nextRow head nextState (nextRow.activeRun halign') rfl rfl rfl
          (PackedCell.size_castPhase _ _ _) halign' hmatched'
      rcases haccepts with ⟨target, hreach, haccept⟩
      exact ⟨target, Relation.ReflTransGen.head hstep hreach, haccept⟩
  | @exitLeft _ _ nextState written direction left right terminal henabled hexits rest =>
      cases direction with
      | right => exact False.elim hexits
      | stay => exact False.elim hexits
      | left =>
        have hnotFirst : head.val ≠ 0 := by
          simpa [DirectionExitsLeft, atLeft] using hexits
        have hpos : 0 < head.val := by omega
        have hbound : head.val - 1 < n := by
          have := head.isLt
          omega
        let b : Fin n := ⟨head.val - 1, hbound⟩
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
        have hflagLeft : atLeft head = atLeft b.succ :=
          congrArg atLeft hhead.symm
        have hflagRight : atRight head = atRight b.succ :=
          congrArg atRight hhead.symm
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
          rw [Row.set_apply_of_ne row b.castSucc b.succ lc (Fin.castSucc_ne_succ b).symm]
        have hactiveDecrease : rc.run.size < ((row.set b.castSucc lc) b.succ).run.size := by
          dsimp [rc]
          rw [hactiveUnchanged, ← hsizeB]
          simp [CellRun.size]
        have hweightSecond : nextRow.weight < (row.set b.castSucc lc).weight :=
          Row.weight_set_lt _ _ _ hactiveDecrease
        have hweight : nextRow.weight < row.weight := lt_trans hweightSecond hweightFirst
        have haccepts : LBA.Accepts M (cfgOf nextRow b.castSucc nextState) :=
          accepts_of_active_row nextRow b.castSucc nextState (nextRow.activeRun halign')
            rfl rfl rfl (PackedCell.size_castPhase _ _ _) halign' hmatched'
        rcases haccepts with ⟨target, hreach, haccept⟩
        have result : LBA.Accepts M (cfgOf row b.succ q) :=
          ⟨target, Relation.ReflTransGen.head hstep hreach, haccept⟩
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
            (nextState, written, .right) ∈
              M.transition q (row b.castSucc).phase.symbol := by
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
          rw [Row.set_apply_of_ne row b.castSucc b.succ lc (Fin.castSucc_ne_succ b).symm]
        have henterSize : enter.size = (row b.succ).run.size := by
          dsimp [enter]
          exact PackedCell.size_castRun _ _ _ _ _
        have hneighborDecrease : rc.run.size < ((row.set b.castSucc lc) b.succ).run.size := by
          dsimp [rc, neighborRest]
          have hpeel := size_peelEnterLeft enter
          omega
        have hweightSecond : nextRow.weight < (row.set b.castSucc lc).weight := by
          exact Row.weight_set_lt _ _ _ hneighborDecrease
        have hweight : nextRow.weight < row.weight := lt_trans hweightSecond hweightFirst
        have haccepts : LBA.Accepts M (cfgOf nextRow b.succ nextState) :=
          accepts_of_active_row nextRow b.succ nextState (nextRow.activeRun halign')
            rfl rfl rfl (PackedCell.size_castPhase _ _ _) halign' hmatched'
        rcases haccepts with ⟨target, hreach, haccept⟩
        have result : LBA.Accepts M (cfgOf row b.castSucc q) :=
          ⟨target, Relation.ReflTransGen.head hstep hreach, haccept⟩
        simpa only [hhead] using result
termination_by row.weight

theorem accepts_of_aligned_row {M : LBA.Machine Γ Λ} {n : ℕ} (row : Row M n)
    (head : Fin (n + 1)) (q : Λ) (halign : Aligned row head q)
    (hmatched : BoundaryMatched row) :
    LBA.Accepts M (cfgOf row head q) :=
  accepts_of_active_row row head q (row.activeRun halign) rfl rfl rfl
    (PackedCell.size_castPhase _ _ _) halign hmatched

/-! ## Realizing the spatial certificate as an initial synchronized row -/

structure PendingRealization (M : LBA.Machine Γ Λ) (bound : ℕ) (old : Γ) (left : List Λ)
    (rest : List Γ) where
  row : (j : Fin (rest.length + 1)) →
    PackedCell M false (decide (j.val = rest.length))
  symbol : ∀ j, (row j).phase.symbol = (old :: rest).get j
  phase : ∀ j, (row j).phase = .outside .left (row j).phase.symbol
  leftEdge : (row ⟨0, Nat.zero_lt_succ _⟩).left = left
  rightEdge : (row ⟨rest.length, Nat.lt_succ_self _⟩).right = []
  matched : ∀ b : Fin rest.length, (row b.castSucc).right = (row b.succ).left
  profileBound : ∀ b : Fin rest.length, (row b.castSucc).right.length ≤ bound

theorem pendingRealization_of_certificate (M : LBA.Machine Γ Λ) (bound : ℕ) :
    ∀ {old : Γ} {left : Profile Λ bound} {seen : Bool} {rest : List Γ},
      PendingCellCertificate M bound old left seen rest →
        Nonempty (PendingRealization M bound old left.list rest)
  | _, _, _, _, .last compatible _ _ => by
      rcases compatible with ⟨run⟩
      let cell : PackedCell M false true :=
        ⟨.outside .left _, _, [], _, run⟩
      let row : (j : Fin 1) → PackedCell M false (decide (j.val = 0)) :=
        fun j => cell.castFlags rfl (by simp [Fin.eq_zero j])
      refine ⟨⟨row, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
      · intro j
        have hj : j = 0 := Fin.eq_zero j
        subst j
        simp [row, cell, Phase.symbol]
      · intro j
        have hj : j = 0 := Fin.eq_zero j
        subst j
        simp [row, cell, Phase.symbol]
      · simp [row, cell]
      · simp [row, cell]
      · intro b
        exact Fin.elim0 b
      · intro b
        exact Fin.elim0 b
  | _, _, _, _, @PendingCellCertificate.more _ _ _ _ old left seen new rest right terminal
      compatible _ tail => by
      rcases compatible with ⟨run⟩
      rcases pendingRealization_of_certificate M bound tail with ⟨tailRow⟩
      let cell : PackedCell M false false :=
        ⟨.outside .left _, _, _, _, run⟩
      let row : (j : Fin (rest.length + 2)) →
          PackedCell M false (decide (j.val = rest.length + 1)) :=
        fun j => Fin.cases
          (cell.castFlags rfl (by simp))
          (fun k => (tailRow.row k).castFlags rfl (by simp)) j
      refine ⟨⟨row, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
      · intro j
        refine Fin.cases ?_ (fun k => ?_) j
        · simp [row, cell, Phase.symbol]
        · simpa [row] using tailRow.symbol k
      · intro j
        refine Fin.cases ?_ (fun k => ?_) j
        · simp [row, cell, Phase.symbol]
        · simpa [row] using tailRow.phase k
      · simp [row, cell]
      · have hlast : (⟨rest.length + 1, by omega⟩ : Fin (rest.length + 2)) =
            (⟨rest.length, Nat.lt_succ_self _⟩ : Fin (rest.length + 1)).succ := by
          apply Fin.ext
          simp
        change (row ⟨rest.length + 1, by omega⟩).right = []
        rw [hlast]
        simpa [row] using tailRow.rightEdge
      · intro b
        refine Fin.cases ?_ (fun k => ?_) b
        · simpa [row, cell] using tailRow.leftEdge.symm
        · simpa [row] using tailRow.matched k
      · intro b
        refine Fin.cases ?_ (fun k => ?_) b
        · change right.list.length ≤ bound
          rw [Profile.length_list]
          omega
        · simpa [row] using tailRow.profileBound k

structure InitialRealization (M : LBA.Machine Γ Λ) (bound : ℕ) (first : Γ) (rest : List Γ) where
  row : Row M rest.length
  symbol : ∀ i, (row i).phase.symbol = (first :: rest).get i
  aligned : Aligned row ⟨0, Nat.zero_lt_succ _⟩ M.initial
  matched : BoundaryMatched row
  profileBound : ∀ b : Fin rest.length, (row b.castSucc).right.length ≤ bound

theorem initialRealization_of_certificate (M : LBA.Machine Γ Λ) (bound : ℕ)
    {first : Γ} {rest : List Γ} :
    ListCellCertificate M bound (first :: rest) →
      Nonempty (InitialRealization M bound first rest)
  | .one compatible => by
      rcases compatible with ⟨run⟩
      let cell : PackedCell M true true :=
        ⟨.active M.initial first, [], [], true, run⟩
      let row : Row M 0 := fun i =>
        cell.castFlags (by simp [atLeft, Fin.eq_zero i])
          (by simp [atRight, Fin.eq_zero i])
      refine ⟨⟨row, ?_, ?_, ?_, ?_⟩⟩
      · intro i
        have hi : i = 0 := Fin.eq_zero i
        subst i
        simp [row, cell, Phase.symbol]
      · intro i
        have hi : i = 0 := Fin.eq_zero i
        subst i
        simp [expectedPhase, row, cell, Phase.symbol]
      · refine ⟨?_, ?_, ?_⟩
        · simp [row, cell]
        · simp [row, cell]
        · intro b
          exact Fin.elim0 b
      · intro b
        exact Fin.elim0 b
  | @ListCellCertificate.many _ _ _ _ first second rest right terminal
      compatible tail => by
      rcases compatible with ⟨run⟩
      rcases pendingRealization_of_certificate M bound tail with ⟨tailRow⟩
      let cell : PackedCell M true false :=
        ⟨.active M.initial first, [], right.list, terminal, run⟩
      let row : Row M (rest.length + 1) := fun i => Fin.cases
        (cell.castFlags (by simp [atLeft]) (by simp [atRight]))
        (fun k => (tailRow.row k).castFlags
          (by simp [atLeft]) (by simp [atRight])) i
      refine ⟨⟨row, ?_, ?_, ?_, ?_⟩⟩
      · intro i
        refine Fin.cases ?_ (fun k => ?_) i
        · simp [row, cell, Phase.symbol]
        · simpa [row] using tailRow.symbol k
      · intro i
        refine Fin.cases ?_ (fun k => ?_) i
        · simp [expectedPhase, row, cell, Phase.symbol]
        · have hphase := tailRow.phase k
          simpa [Aligned, expectedPhase, row, Phase.symbol] using hphase
      · refine ⟨?_, ?_, ?_⟩
        · simp [row, cell]
        · have hlast : (⟨rest.length + 1, by omega⟩ : Fin (rest.length + 2)) =
              (⟨rest.length, Nat.lt_succ_self _⟩ : Fin (rest.length + 1)).succ := by
            apply Fin.ext
            simp
          change (row ⟨rest.length + 1, by omega⟩).right = []
          rw [hlast]
          simpa [row] using tailRow.rightEdge
        · intro b
          refine Fin.cases ?_ (fun k => ?_) b
          · simpa [row, cell] using tailRow.leftEdge.symm
          · simpa [row] using tailRow.matched k
      · intro b
        refine Fin.cases ?_ (fun k => ?_) b
        · change right.list.length ≤ bound
          rw [Profile.length_list]
          omega
        · simpa [row] using tailRow.profileBound k

theorem InitialRealization.cfgOf_eq_initCfgList {M : LBA.Machine Γ Λ}
    {bound : ℕ} {first : Γ} {rest : List Γ}
    (realization : InitialRealization M bound first rest) :
    cfgOf realization.row ⟨0, Nat.zero_lt_succ _⟩ M.initial =
      LBA.initCfgList M (first :: rest) (by simp) := by
  apply congrArg (fun tape => DLBA.Cfg.mk M.initial tape)
  congr 1
  · funext i
    change (realization.row i).phase.symbol = _
    rw [realization.symbol i]
    rfl

theorem accepts_of_listCellCertificate (M : LBA.Machine Γ Λ) (bound : ℕ)
    {first : Γ} {rest : List Γ}
    (certificate : ListCellCertificate M bound (first :: rest)) :
    LBA.Accepts M (LBA.initCfgList M (first :: rest) (by simp)) := by
  rcases initialRealization_of_certificate M bound certificate with ⟨realization⟩
  have haccepts := accepts_of_aligned_row realization.row
    ⟨0, Nat.zero_lt_succ _⟩ M.initial realization.aligned realization.matched
  rw [realization.cfgOf_eq_initCfgList] at haccepts
  exact haccepts

theorem accepts_of_cellCertificate (M : LBA.Machine Γ Λ) (bound n : ℕ)
    (input : Fin (n + 1) → Γ) (certificate : CellCertificate M bound input) :
    LBA.Accepts M (LBA.initCfgList M
      (input 0 :: List.ofFn (fun i : Fin n => input i.succ)) (by simp)) := by
  change ListCellCertificate M bound (List.ofFn input) at certificate
  rw [List.ofFn_succ] at certificate
  exact accepts_of_listCellCertificate M bound certificate

def initialCfgFn (M : LBA.Machine Γ Λ) {n : ℕ} (input : Fin (n + 1) → Γ) :
    DLBA.Cfg Γ Λ n :=
  ⟨M.initial, ⟨input, ⟨0, Nat.zero_lt_succ _⟩⟩⟩

def castCfg {n m : ℕ} (h : n = m) (cfg : DLBA.Cfg Γ Λ n) : DLBA.Cfg Γ Λ m :=
  h ▸ cfg

def reindexCfg {n m : ℕ} (h : n = m) (cfg : DLBA.Cfg Γ Λ n) : DLBA.Cfg Γ Λ m :=
  ⟨cfg.state,
    ⟨fun i => cfg.tape.contents (Fin.cast (congrArg (· + 1) h.symm) i),
      Fin.cast (congrArg (· + 1) h) cfg.tape.head⟩⟩

theorem castCfg_eq_reindexCfg {n m : ℕ} (h : n = m) (cfg : DLBA.Cfg Γ Λ n) :
    castCfg h cfg = reindexCfg h cfg := by
  subst m
  simp [castCfg, reindexCfg]

theorem castCfg_accepts {M : LBA.Machine Γ Λ} {n m : ℕ} (h : n = m)
    {cfg : DLBA.Cfg Γ Λ n} (haccepts : LBA.Accepts M cfg) :
    LBA.Accepts M (castCfg h cfg) := by
  subst m
  exact haccepts

theorem castCfg_initCfgList_ofFn_eq_initialCfgFn (M : LBA.Machine Γ Λ) {n : ℕ}
    (input : Fin (n + 1) → Γ)
    (hlen : (List.ofFn input).length - 1 = n) :
    castCfg hlen (LBA.initCfgList M (List.ofFn input) (by simp)) = initialCfgFn M input := by
  rw [castCfg_eq_reindexCfg]
  apply congrArg (fun tape => DLBA.Cfg.mk M.initial tape)
  congr 1
  · funext i
    simp only [LBA.initCfgList, LBA.loadList]
    rw [List.get_ofFn]
    congr 1

theorem castCfg_initCfgList_decomposed_eq_initialCfgFn (M : LBA.Machine Γ Λ) {n : ℕ}
    (input : Fin (n + 1) → Γ)
    (hlen : (input 0 :: List.ofFn (fun i : Fin n => input i.succ)).length - 1 = n) :
    castCfg hlen (LBA.initCfgList M
      (input 0 :: List.ofFn (fun i : Fin n => input i.succ)) (by simp)) =
        initialCfgFn M input := by
  rw [castCfg_eq_reindexCfg]
  apply congrArg (fun tape => DLBA.Cfg.mk M.initial tape)
  congr 1
  funext i
  simp only [LBA.initCfgList, LBA.loadList]
  refine Fin.cases ?_ (fun k => ?_) i
  · simp
  · simp

theorem accepts_initialCfgFn_of_cellCertificate (M : LBA.Machine Γ Λ) (bound n : ℕ)
    (input : Fin (n + 1) → Γ) (certificate : CellCertificate M bound input) :
    LBA.Accepts M (initialCfgFn M input) := by
  let word := input 0 :: List.ofFn (fun i : Fin n => input i.succ)
  have hlength : word.length - 1 = n := by simp [word]
  have haccepts : LBA.Accepts M (LBA.initCfgList M word (by simp [word])) := by
    simpa only [word] using accepts_of_cellCertificate M bound n input certificate
  have hcast := castCfg_accepts hlength haccepts
  rw [castCfg_initCfgList_decomposed_eq_initialCfgFn M input hlength] at hcast
  exact hcast

end LBA.BoundedCrossing.Soundness

end
