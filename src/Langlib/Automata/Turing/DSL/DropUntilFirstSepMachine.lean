module

public import Langlib.Automata.Turing.DSL.TakeWhileNeSepMachine
public import Langlib.Automata.Turing.DSL.TM0BlockRealizability
public import Mathlib.Computability.TMToPartrec
import Langlib.Automata.Turing.DSL.InnerBlockRealizability
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Height.Basic
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Tactic.Cases
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
@[expose]
public section



/-! # DropUntilFirstSep is Block-Realizable

We prove `dropUntilFirstSep sep` is block-realizable via a simple TM0 machine
that scans right, erasing cells until it finds `sep`, erases `sep`, and halts.

The machine has four states:
- `erase` (initial): If current cell is `sep`, write default → `wSep`.
  If current cell is `default`, halt. Otherwise, write default → `wOther`.
- `wSep`: move right → `done`.
- `wOther`: move right → `erase`.
- `done`: halt.

## Key results

- `dufsM`: the drop-until-first-separator TM0 machine.
- `dufs_reaches_halts`: exact reaching behavior on separator-containing blocks.
- `tm0_dropUntilFirstSep_blockSepAnySuffix`: separator-delimited block
  realizability for `dropUntilFirstSep`.
-/

open Turing PartrecToTM2 TM2to1

/-! ### Machine definition -/

/-- State type for the dropUntilFirstSep TM0 machine. -/
public inductive DUFSState where
  | erase    -- scanning/erasing cells
  | wSep     -- just wrote default over a sep cell
  | wOther   -- just wrote default over a non-sep cell
  | done     -- halted
  deriving DecidableEq

instance : Inhabited DUFSState := ⟨.erase⟩

instance : Fintype DUFSState where
  elems := {.erase, .wSep, .wOther, .done}
  complete := by intro x; cases x <;> simp

/-- The dropUntilFirstSep TM0 machine. -/
@[expose]
public noncomputable def dufsM {Γ : Type} [Inhabited Γ] [DecidableEq Γ]
    (sep : Γ) : @TM0.Machine Γ DUFSState ⟨.erase⟩ := fun q a =>
  match q with
  | .erase =>
    if a = sep then some (.wSep, .write default)
    else if a = default then none
    else some (.wOther, .write default)
  | .wSep => some (.done, .move Dir.right)
  | .wOther => some (.erase, .move Dir.right)
  | .done => none

/-! ### Correctness -/

/-
Erasing through the block to find sep: the machine reaches a halting
    configuration with the correct tape contents.
-/
public theorem dufs_reaches_halts {Γ : Type} [Inhabited Γ] [DecidableEq Γ]
    (sep : Γ) (hsep : sep ≠ default)
    (block suffix : List Γ)
    (hblock : ∀ g ∈ block, g ≠ default) :
    ∃ q, Reaches (TM0.step (dufsM sep))
      (TM0.init (block ++ default :: suffix))
      ⟨q, Tape.mk₁ (dropUntilFirstSep sep block ++ default :: suffix)⟩ ∧
    TM0.step (dufsM sep)
      ⟨q, Tape.mk₁ (dropUntilFirstSep sep block ++ default :: suffix)⟩ = none := by
  induction' block with c block ih generalizing suffix;
  · unfold TM0.step;
    unfold dufsM; simp +decide [ Tape.mk₁ ] ;
    use DUFSState.erase;
    constructor;
    · constructor;
    · simp +decide [ Tape.mk₂, Tape.head ];
      unfold dropUntilFirstSep; aesop;
  · by_cases hc : c = sep <;> simp_all +decide [ dropUntilFirstSep ];
    · refine' ⟨ DUFSState.done, _, _ ⟩;
      · refine' Relation.ReflTransGen.head _ _;
        exact ⟨ DUFSState.wSep, Tape.write default ( Tape.mk₁ ( sep :: ( block ++ default :: suffix ) ) ) ⟩;
        · unfold TM0.step;
          unfold dufsM; simp +decide [ hblock ] ;
          exact ⟨ TM0.Stmt.write default, by unfold TM0.init; aesop ⟩;
        · refine' Relation.ReflTransGen.head _ _;
          exact ⟨ DUFSState.done, Tape.move Dir.right ( Tape.write default ( Tape.mk₁ ( sep :: ( block ++ default :: suffix ) ) ) ) ⟩;
          · unfold dufsM; aesop;
          · convert Relation.ReflTransGen.refl using 1;
            exact congr_arg _ ( by exact? );
      · exact?;
    · obtain ⟨ q, hq₁, hq₂ ⟩ := ih suffix; use q; simp_all +decide [ Reaches ] ;
      have h_step : TM0.step (dufsM sep) ⟨.erase, Tape.mk₁ (c :: (block ++ default :: suffix))⟩ = some ⟨.wOther, Tape.write default (Tape.mk₁ (c :: (block ++ default :: suffix)))⟩ := by
        unfold TM0.step; simp +decide [ hc, hblock ] ;
        exact ⟨ _, if_neg hc |> fun h => h.trans ( if_neg hblock.1 ), rfl ⟩;
      have h_step : TM0.step (dufsM sep) ⟨.wOther, Tape.write default (Tape.mk₁ (c :: (block ++ default :: suffix)))⟩ = some ⟨.erase, Tape.move Dir.right (Tape.write default (Tape.mk₁ (c :: (block ++ default :: suffix))))⟩ := by
        unfold TM0.step; simp +decide [ dufsM ] ;
      have h_step : Tape.move Dir.right (Tape.write default (Tape.mk₁ (c :: (block ++ default :: suffix)))) = Tape.mk₁ (block ++ default :: suffix) := by
        convert tape_erase_step c ( block ++ default :: suffix ) using 1;
      exact .single ( by aesop ) |> Relation.ReflTransGen.trans <| .single ( by aesop ) |> Relation.ReflTransGen.trans <| hq₁

/-! ### Main result -/

/-- `dropUntilFirstSep sep` is block-realizable for any `sep ≠ default`. -/
public theorem tm0_dropUntilFirstSep_block {Γ : Type} [Inhabited Γ] [DecidableEq Γ] [Fintype Γ]
    (sep : Γ) (hsep : sep ≠ default) :
    TM0RealizesBlock Γ (dropUntilFirstSep sep) := by
  refine ⟨DUFSState, inferInstance, inferInstance, dufsM sep, ?_⟩
  intro block suffix hblock hsuffix hfblock
  obtain ⟨q, h_reaches, h_halts⟩ := dufs_reaches_halts sep hsep block suffix hblock
  constructor
  · exact Part.dom_iff_mem.mpr ⟨_, Turing.mem_eval.mpr ⟨h_reaches, h_halts⟩⟩
  · intro h
    have h_mem := Turing.mem_eval.mpr ⟨h_reaches, h_halts⟩
    exact (Part.mem_unique (Part.get_mem h) h_mem).symm ▸ rfl

/-- `dropUntilFirstSep sep` is strong blank-delimited block-realizable: the
machine halts as soon as it reaches `sep` or the boundary blank, so it never
needs any invariant on the suffix after that boundary. -/
theorem tm0_dropUntilFirstSep_blockAnySuffix
    {Γ : Type} [Inhabited Γ] [DecidableEq Γ] [Fintype Γ]
    (sep : Γ) (hsep : sep ≠ default) :
    TM0RealizesBlockAnySuffix Γ (dropUntilFirstSep sep) := by
  refine ⟨DUFSState, inferInstance, inferInstance, dufsM sep, ?_⟩
  intro block suffix hblock hfblock
  obtain ⟨q, h_reaches, h_halts⟩ := dufs_reaches_halts sep hsep block suffix hblock
  constructor
  · exact Part.dom_iff_mem.mpr ⟨_, Turing.mem_eval.mpr ⟨h_reaches, h_halts⟩⟩
  · intro h
    have h_mem := Turing.mem_eval.mpr ⟨h_reaches, h_halts⟩
    exact (Part.mem_unique (Part.get_mem h) h_mem).symm ▸ rfl

/-- Separator-bounded `dropUntilFirstSep`, with an unrestricted suffix after
the outer separator. -/
theorem tm0_dropUntilFirstSep_blockSepAnySuffix
    {Γ : Type} [Inhabited Γ] [DecidableEq Γ] [Fintype Γ]
    (sep outerSep : Γ) (hsep : sep ≠ default) :
    TM0RealizesBlockSepAnySuffix Γ outerSep (dropUntilFirstSep sep) :=
  tm0RealizesBlockAnySuffix_toBlockSepAnySuffix
    (tm0_dropUntilFirstSep_blockAnySuffix sep hsep)
