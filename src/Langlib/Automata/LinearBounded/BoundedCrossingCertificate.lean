module

public import Langlib.Automata.LinearBounded.BoundedCrossingProfiles

@[expose]
public section

/-!
# Spatial certificates for bounded crossing profiles

`profileNFA` guesses one bounded crossing profile at every internal tape boundary.  This file
packages those guesses as a finite row of cell-local histories and proves an exact correspondence
between accepting NFA paths and such rows.  Adjacent cells share the very same profile, endpoint
flags are fixed by their physical positions, and exactly one cell contains the terminal accepting
event.

The correspondence is uniform over every nonempty finite tape width, including width one.
-/

namespace LBA.BoundedCrossing

universe u v

variable {Gamma : Type u} {State : Type v}

/-- A spatial certificate for the cells at and to the right of a pending scan state.  `left` is
literally the profile shared with the previous cell.  A `more` node chooses the profile shared
with the next cell and the current cell's terminal bit; `last` closes the right edge. -/
inductive PendingCellCertificate (M : LBA.Machine Gamma State) (bound : Nat) :
    (old : Gamma) → (left : Profile State bound) → (seen : Bool) → List Gamma →
      Type (max u v)
  | last {old left seen terminal}
      (compatible : CellCompatible M false true old left.list [] terminal)
      (notBoth : ¬ (seen = true ∧ terminal = true))
      (someTerminal : (seen || terminal) = true) :
      PendingCellCertificate M bound old left seen []
  | more {old left seen new rest right terminal}
      (compatible : CellCompatible M false false old left.list right.list terminal)
      (notBoth : ¬ (seen = true ∧ terminal = true))
      (tail : PendingCellCertificate M bound new right (seen || terminal) rest) :
      PendingCellCertificate M bound old left seen (new :: rest)

/-- A spatial certificate for a nonempty list of tape cells.  Adjacent nodes share the same
bounded profile, and every node has its own terminal-event bit. -/
inductive ListCellCertificate (M : LBA.Machine Gamma State) (bound : Nat) :
    List Gamma → Type (max u v)
  | one {symbol}
      (compatible : CellCompatible M true true symbol [] [] true) :
      ListCellCertificate M bound [symbol]
  | many {first second rest}
      (right : Profile State bound) (terminal : Bool)
      (compatible : CellCompatible M true false first [] right.list terminal)
      (tail : PendingCellCertificate M bound second right terminal rest) :
      ListCellCertificate M bound (first :: second :: rest)

/-- Width-indexed presentation of `ListCellCertificate`. -/
abbrev CellCertificate (M : LBA.Machine Gamma State) (bound : Nat) {n : Nat}
    (input : Fin (n + 1) → Gamma) :=
  ListCellCertificate M bound (List.ofFn input)

private theorem pendingCertificate_iff_acceptingPath
    (M : LBA.Machine Gamma State) (bound : Nat) (old : Gamma)
    (left : Profile State bound) (seen : Bool) (rest : List Gamma) :
    Nonempty (PendingCellCertificate M bound old left seen rest) ↔
      ∃ target, target ∈ (profileNFA M bound).accept ∧
        Nonempty ((profileNFA M bound).Path (.pending old left seen) target rest) := by
  induction rest generalizing old left seen with
  | nil =>
      constructor
      · rintro ⟨certificate⟩
        cases certificate with
        | @last _ _ _ terminal compatible notBoth someTerminal =>
            exact ⟨ScanState.pending old left seen,
              ⟨terminal, compatible, notBoth, someTerminal⟩,
              ⟨.nil (ScanState.pending old left seen)⟩⟩
      · rintro ⟨target, haccept, ⟨path⟩⟩
        cases path
        change ∃ terminal : Bool,
          CellCompatible M false true old left.list [] terminal ∧
          ¬ (seen = true ∧ terminal = true) ∧
          (seen || terminal) = true at haccept
        rcases haccept with ⟨terminal, compatible, notBoth, someTerminal⟩
        exact ⟨.last compatible notBoth someTerminal⟩
  | cons new rest ih =>
      constructor
      · rintro ⟨certificate⟩
        cases certificate with
        | @more _ _ _ _ _ right terminal compatible notBoth tail =>
            rcases (ih _ _ _).1 ⟨tail⟩ with ⟨target, haccept, ⟨tailPath⟩⟩
            exact ⟨target, haccept,
              ⟨.cons (ScanState.pending new right (seen || terminal))
                (ScanState.pending old left seen) target new rest
                ⟨right, terminal, compatible, notBoth, rfl⟩ tailPath⟩⟩
      · rintro ⟨target, haccept, ⟨path⟩⟩
        cases path with
        | cons next _ _ _ _ step tailPath =>
            change ∃ (right : Profile State bound) (terminal : Bool),
              CellCompatible M false false old left.list right.list terminal ∧
              ¬ (seen = true ∧ terminal = true) ∧
              next = .pending new right (seen || terminal) at step
            rcases step with ⟨right, terminal, compatible, notBoth, rfl⟩
            rcases (ih _ _ _).2 ⟨target, haccept, ⟨tailPath⟩⟩ with ⟨tail⟩
            exact ⟨.more compatible notBoth tail⟩

private theorem nonempty_listCertificate_iff_acceptingPath
    (M : LBA.Machine Gamma State) (bound : Nat) (first : Gamma) (rest : List Gamma) :
    Nonempty (ListCellCertificate M bound (first :: rest)) ↔
      ∃ target, target ∈ (profileNFA M bound).accept ∧
        Nonempty ((profileNFA M bound).Path .before target (first :: rest)) := by
  constructor
  · rintro ⟨certificate⟩
    cases certificate with
    | @one _ compatible =>
        exact ⟨ScanState.first first, compatible,
          ⟨.cons (ScanState.first first) ScanState.before (ScanState.first first) first [] rfl
            (.nil (ScanState.first first))⟩⟩
    | @many _ second rest right terminal compatible tail =>
        rcases (pendingCertificate_iff_acceptingPath M bound _ _ _ _).1 ⟨tail⟩ with
          ⟨target, haccept, ⟨tailPath⟩⟩
        exact ⟨target, haccept,
          ⟨.cons (ScanState.first first) ScanState.before target first (second :: rest) rfl
            (.cons (ScanState.pending second right terminal) (ScanState.first first) target
              second rest ⟨right, terminal, compatible, rfl⟩ tailPath)⟩⟩
  · rintro ⟨target, haccept, ⟨path⟩⟩
    cases path with
    | cons afterFirst _ _ _ _ firstStep afterFirstPath =>
        change afterFirst = .first first at firstStep
        subst afterFirst
        cases rest with
        | nil =>
            cases afterFirstPath
            exact ⟨.one haccept⟩
        | cons second rest =>
            cases afterFirstPath with
            | cons pending _ _ _ _ secondStep tailPath =>
                change ∃ (right : Profile State bound) (terminal : Bool),
                  CellCompatible M true false first [] right.list terminal ∧
                  pending = .pending second right terminal at secondStep
                rcases secondStep with ⟨right, terminal, compatible, rfl⟩
                rcases (pendingCertificate_iff_acceptingPath M bound _ _ _ _).2
                    ⟨target, haccept, ⟨tailPath⟩⟩ with ⟨tail⟩
                exact ⟨.many right terminal compatible tail⟩

/-- Exact list-level spatial characterization of the profile NFA. -/
theorem mem_profileNFA_iff_nonempty_listCellCertificate
    (M : LBA.Machine Gamma State) (bound : Nat) (first : Gamma) (rest : List Gamma) :
    first :: rest ∈ (profileNFA M bound).accepts ↔
      Nonempty (ListCellCertificate M bound (first :: rest)) := by
  rw [NFA.accepts_iff_exists_path]
  constructor
  · rintro ⟨start, hstart, target, haccept, path⟩
    change start = .before at hstart
    subst start
    exact (nonempty_listCertificate_iff_acceptingPath M bound first rest).2
      ⟨target, haccept, path⟩
  · intro certificate
    rcases (nonempty_listCertificate_iff_acceptingPath M bound first rest).1 certificate with
      ⟨target, haccept, path⟩
    exact ⟨.before, rfl, target, haccept, path⟩

/-- Exact width-indexed spatial characterization, uniformly for every positive tape width,
including width one (`n = 0`). -/
theorem mem_profileNFA_iff_nonempty_cellCertificate
    (M : LBA.Machine Gamma State) (bound n : Nat) (input : Fin (n + 1) → Gamma) :
    List.ofFn input ∈ (profileNFA M bound).accepts ↔
      Nonempty (CellCertificate M bound input) := by
  change List.ofFn input ∈ (profileNFA M bound).accepts ↔
    Nonempty (ListCellCertificate M bound (List.ofFn input))
  rw [List.ofFn_succ]
  exact mem_profileNFA_iff_nonempty_listCellCertificate M bound _ _

end LBA.BoundedCrossing

end
