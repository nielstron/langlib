module

public import Langlib.Automata.LinearBounded.AcyclicClock.ReadyEncoding

@[expose]
public section

/-!
# Connecting semantic clock layers to operational Ready checkpoints

`StrictClockLayering` represents an exact clock layer by a canonical digit list of physical-tape
length.  The operational compiler stores digits as a function indexed by tape cells.  This file
bridges those two representations and packages semantic clocked configurations as Ready
checkpoints with arbitrary harmless trails.
-/

open Classical

namespace LBA.AcyclicClock

variable {T Γ Λ : Type*}
variable [Fintype T] [Fintype Γ] [Fintype Λ] [Nonempty Λ]

/-- Cell-indexed form of the canonical operational row numeral for a semantic clock layer. -/
public def semanticDigits
    (n : ℕ)
    (layer :
      Fin
        (Fintype.card
          (DLBA.Cfg (SourceAlpha T Γ) Λ n) + 1)) :
    Fin (n + 1) → ClockDigit T Γ Λ :=
  fun index =>
    (LBA.StrictClockLayering.encodeSemanticLayer
      (Γ := SourceAlpha T Γ) (Λ := Λ) n layer).get
        (Fin.cast
          (LBA.StrictClockLayering.length_encodeSemanticLayer
            (Γ := SourceAlpha T Γ) (Λ := Λ) n layer).symm
          index)

/-- Converting the cell-indexed digits back to a list recovers the exact semantic-layer row. -/
public theorem ofFn_semanticDigits
    (n : ℕ)
    (layer :
      Fin
        (Fintype.card
          (DLBA.Cfg (SourceAlpha T Γ) Λ n) + 1)) :
    List.ofFn (semanticDigits (T := T) (Γ := Γ) (Λ := Λ) n layer) =
      LBA.StrictClockLayering.encodeSemanticLayer
        (Γ := SourceAlpha T Γ) (Λ := Λ) n layer := by
  apply List.ext_get
  · simp
  · intro index hleft hright
    simp only [List.get_ofFn, semanticDigits]
    congr

/-- Numeric value of the operational digit function is exactly the semantic layer index. -/
public theorem value_semanticDigits
    (n : ℕ)
    (layer :
      Fin
        (Fintype.card
          (DLBA.Cfg (SourceAlpha T Γ) Λ n) + 1)) :
    (clockCodec (T := T) (Γ := Γ) (Λ := Λ)).value
        (List.ofFn
          (semanticDigits (T := T) (Γ := Γ) (Λ := Λ) n layer)) =
      layer.val := by
  rw [ofFn_semanticDigits]
  exact
    LBA.StrictClockLayering.value_encodeSemanticLayer
      (Γ := SourceAlpha T Γ) (Λ := Λ) n layer

/-- The bottom semantic layer is the all-zero operational digit function. -/
public theorem semanticDigits_bottom
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (cfg : DLBA.Cfg (SourceAlpha T Γ) Λ n) :
    semanticDigits (T := T) (Γ := Γ) (Λ := Λ) n
        (LBA.StrictClockLayering.bottom cfg).2 =
      fun _ => clockZero M := by
  funext index
  have hlayer :
      (LBA.StrictClockLayering.bottom cfg).2 =
        (⟨0, by omega⟩ :
          Fin (Fintype.card (DLBA.Cfg (SourceAlpha T Γ) Λ n) + 1)) :=
    Fin.ext rfl
  rw [hlayer]
  simp [semanticDigits,
    LBA.StrictClockLayering.encodeSemanticLayer,
    LBA.StrictClockLayering.encodeLayerRow,
    RowNumeral.DigitCodec.zeroRow, clockZero]
  rfl

/-- A semantic strict-clock edge becomes one nonoverflowing increment of the operational digit
function. -/
public theorem increment_semanticDigits_of_clockedStep
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ}
    {old new :
      LBA.StrictClockLayering.ClockedCfg
        (SourceAlpha T Γ) Λ n}
    (hstep : LBA.StrictClockLayering.ClockedStep M old new) :
    (clockCodec (T := T) (Γ := Γ) (Λ := Λ)).increment
        (List.ofFn
          (semanticDigits (T := T) (Γ := Γ) (Λ := Λ) n old.2)) =
      (List.ofFn
          (semanticDigits (T := T) (Γ := Γ) (Λ := Λ) n new.2),
        false) := by
  rw [ofFn_semanticDigits, ofFn_semanticDigits]
  exact
    LBA.StrictClockLayering.increment_encodeSemanticLayer_of_clockedStep M hstep

/-- Operational checkpoint encoding of a semantic clocked configuration. -/
public def semanticCheckpointCfg
    (n : ℕ)
    (clocked :
      LBA.StrictClockLayering.ClockedCfg
        (SourceAlpha T Γ) Λ n)
    (trails : ReadyTrails n) :
    DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n :=
  checkpointCfg clocked.1
    (semanticDigits (T := T) (Γ := Γ) (Λ := Λ) n clocked.2)
    trails

@[simp]
public theorem semanticCheckpointCfg_state
    (n : ℕ)
    (clocked :
      LBA.StrictClockLayering.ClockedCfg
        (SourceAlpha T Γ) Λ n)
    (trails : ReadyTrails n) :
    (semanticCheckpointCfg (T := T) (Γ := Γ) (Λ := Λ)
      n clocked trails).state =
        .ready clocked.1.state := rfl

/-- The clear-trail checkpoint at semantic layer zero is exactly the canonical zero-clock
encoding. -/
public theorem semanticCheckpointCfg_bottom_clear
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (cfg : DLBA.Cfg (SourceAlpha T Γ) Λ n) :
    semanticCheckpointCfg (T := T) (Γ := Γ) (Λ := Λ)
        n (LBA.StrictClockLayering.bottom cfg) (ReadyTrails.clear n) =
      canonicalCfg M cfg := by
  unfold semanticCheckpointCfg
  rw [semanticDigits_bottom M cfg, checkpointCfg_clear]
  exact (canonicalCfg_eq_readyCfg_zero M cfg).symm

/-- The complete physical clock value of a semantic checkpoint is its exact layer. -/
public theorem clockValue_semanticCheckpointCfg
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    (n : ℕ)
    (clocked :
      LBA.StrictClockLayering.ClockedCfg
        (SourceAlpha T Γ) Λ n)
    (trails : ReadyTrails n) :
    clockValue M
        (semanticCheckpointCfg (T := T) (Γ := Γ) (Λ := Λ)
      n clocked trails).tape =
      clocked.2.val := by
  change
    clockValue M
      (checkpointTape clocked.1.tape
        (semanticDigits (T := T) (Γ := Γ) (Λ := Λ) n clocked.2)
        trails) =
      clocked.2.val
  rw [clockValue_checkpointTape]
  exact value_semanticDigits n clocked.2

end LBA.AcyclicClock

end
