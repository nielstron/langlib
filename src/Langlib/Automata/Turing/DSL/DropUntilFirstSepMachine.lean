import Mathlib
import Langlib.Automata.Turing.DSL.BlockRealizability
import Langlib.Automata.Turing.DSL.DropWhileNeSep
import Langlib.Automata.Turing.DSL.TakeWhileBlock

/-! # DropUntilFirstSep is Block-Realizable

We prove `dropUntilFirstSep sep` is block-realizable via a simple TM0 machine
that scans right, erasing cells until it finds `sep`, erases `sep`, and halts.

The machine has four states:
- `erase` (initial): If current cell is `sep`, write default → `wSep`.
  If current cell is `default`, halt. Otherwise, write default → `wOther`.
- `wSep`: move right → `done`.
- `wOther`: move right → `erase`.
- `done`: halt.
-/

open Turing PartrecToTM2 TM2to1

/-! ### Machine definition -/

/-- State type for the dropUntilFirstSep TM0 machine. -/
inductive DUFSState where
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
noncomputable def dufsM {Γ : Type} [Inhabited Γ] [DecidableEq Γ]
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
theorem dufs_reaches_halts {Γ : Type} [Inhabited Γ] [DecidableEq Γ]
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
theorem tm0_dropUntilFirstSep_block {Γ : Type} [Inhabited Γ] [DecidableEq Γ] [Fintype Γ]
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