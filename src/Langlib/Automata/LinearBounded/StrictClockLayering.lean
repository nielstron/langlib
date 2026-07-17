module

public import Langlib.Automata.LinearBounded.LayeredReachability
public import Langlib.Automata.LinearBounded.Definition
public import Langlib.Automata.LinearBounded.RowEnumeration
import Mathlib.Tactic

@[expose]
public section

/-!
# Strict clock layering for bounded LBA configurations

This file isolates the semantic clock construction behind an acyclic presentation of
fixed-width LBA reachability.  It does **not** construct a one-tape LBA implementing the clock.

For a fixed tape width, a clocked configuration is an ordinary bounded configuration paired
with a layer from zero through the number of source configurations.  A strict clocked step
advances the layer by exactly one and performs one genuine source-machine step.  Consequently:

* ordinary fixed-width reachability is equivalent to reaching the same target at some layer;
* LBA acceptance is equivalent to strict clock-layer reachability of an accepting target;
* the entire clocked graph is acyclic, including vertices unrelated to a canonical input;
* arbitrary uniform bounds on immediate indegree and outdegree are preserved.

The final section gives a concrete same-width capacity bound.  With

`B = 2 * |Γ| * |Λ|`,

one base-`B` digit per physical tape cell has strictly more values than the entire bounded
configuration space.  Hence every semantic clock layer used here can be injected into a row of
`n + 1` such digits.  This file proves only the resource theorem; the `AcyclicClock` modules
implement and globally validate those digit rows by local LBA microsteps.
-/

namespace LBA.StrictClockLayering

open Relation

variable {Γ Λ : Type*} [Fintype Γ] [Fintype Λ]

/-! ## The exact finite clock -/

/-- A fixed-width LBA configuration paired with a clock layer from zero through the number of
source configurations. -/
public abbrev ClockedCfg (Γ Λ : Type*) [Fintype Γ] [Fintype Λ] (n : ℕ) :=
  LayeredReachability.Vertex (DLBA.Cfg Γ Λ n)

/-- Place a source configuration at clock layer zero. -/
@[expose]
public def bottom {n : ℕ} (cfg : DLBA.Cfg Γ Λ n) : ClockedCfg Γ Λ n :=
  LayeredReachability.bottom cfg

/-- Place a source configuration at an arbitrary valid clock layer. -/
@[expose]
public noncomputable def atLayer {n : ℕ} (cfg : DLBA.Cfg Γ Λ n)
    (layer : ℕ) (hlayer : layer ≤ Fintype.card (DLBA.Cfg Γ Λ n)) :
    ClockedCfg Γ Λ n :=
  LayeredReachability.atLayer cfg layer hlayer

/-- Strict clock-layer simulation of one genuine source-machine step. -/
@[expose]
public def ClockedStep (M : LBA.Machine Γ Λ) {n : ℕ} :
    ClockedCfg Γ Λ n → ClockedCfg Γ Λ n → Prop :=
  LayeredReachability.StrictEdge (LBA.Step M)

/-- Every strict clocked step increases the clock coordinate by exactly one. -/
public theorem clockedStep_layer_succ (M : LBA.Machine Γ Λ) {n : ℕ}
    {old new : ClockedCfg Γ Λ n} (hstep : ClockedStep M old new) :
    new.2.val = old.2.val + 1 :=
  hstep.1

/-- Every nonempty strict clocked path strictly increases the clock coordinate. -/
public theorem clockedTransGen_layer_lt (M : LBA.Machine Γ Λ) {n : ℕ}
    {old new : ClockedCfg Γ Λ n}
    (hpath : TransGen (ClockedStep M) old new) :
    old.2.val < new.2.val :=
  LayeredReachability.strictTransGen_layer_lt hpath

/-- The complete strict clock-layer graph is acyclic at every fixed tape width. -/
public theorem clockedStep_acyclic (M : LBA.Machine Γ Λ) (n : ℕ) :
    ∀ cfg : ClockedCfg Γ Λ n, ¬ TransGen (ClockedStep M) cfg cfg :=
  LayeredReachability.strict_no_transGen_self (LBA.Step M)

/-- Fixed-width source reachability is exactly strict clock-layer reachability of the same
target at some layer.  There are no padding edges in the clocked relation. -/
public theorem reaches_iff_exists_clocked_reaches
    (M : LBA.Machine Γ Λ) {n : ℕ}
    (source target : DLBA.Cfg Γ Λ n) :
    LBA.Reaches M source target ↔
      ∃ layer, ∃ hlayer : layer ≤ Fintype.card (DLBA.Cfg Γ Λ n),
        ReflTransGen (ClockedStep M)
          (bottom source) (atLayer target layer hlayer) := by
  simpa only [LBA.Reaches, ClockedStep, bottom, atLayer] using
    LayeredReachability.reaches_iff_exists_strictLayer_reaches
      (LBA.Step M) source target

/-- Fixed-width LBA acceptance is exactly reachability of an accepting source configuration
at some strict clock layer. -/
public theorem accepts_iff_exists_clocked_accept
    (M : LBA.Machine Γ Λ) {n : ℕ}
    (source : DLBA.Cfg Γ Λ n) :
    LBA.Accepts M source ↔
      ∃ target : DLBA.Cfg Γ Λ n,
        M.accept target.state = true ∧
          ∃ layer, ∃ hlayer : layer ≤ Fintype.card (DLBA.Cfg Γ Λ n),
            ReflTransGen (ClockedStep M)
              (bottom source) (atLayer target layer hlayer) := by
  constructor
  · rintro ⟨target, hreach, haccept⟩
    exact ⟨target, haccept,
      (reaches_iff_exists_clocked_reaches M source target).1 hreach⟩
  · rintro ⟨target, haccept, hreach⟩
    exact ⟨target,
      (reaches_iff_exists_clocked_reaches M source target).2 hreach,
      haccept⟩

/-! ## Directed-degree preservation -/

/-- Pointwise, strict clock layering cannot increase the number of distinct successors. -/
public theorem clockedStep_outdegree_le
    (M : LBA.Machine Γ Λ) {n : ℕ} (old : ClockedCfg Γ Λ n) :
    Set.encard {new | ClockedStep M old new} ≤
      Set.encard {target | LBA.Step M old.1 target} :=
  LayeredReachability.strictEdge_outdegree_le (LBA.Step M) old

/-- Pointwise, strict clock layering cannot increase the number of distinct predecessors. -/
public theorem clockedStep_indegree_le
    (M : LBA.Machine Γ Λ) {n : ℕ} (new : ClockedCfg Γ Λ n) :
    Set.encard {old | ClockedStep M old new} ≤
      Set.encard {source | LBA.Step M source new.1} :=
  LayeredReachability.strictEdge_indegree_le (LBA.Step M) new

/-- Every uniform source outdegree bound is preserved by strict clock layering. -/
public theorem clockedStep_outdegreeAtMost
    (M : LBA.Machine Γ Λ) {n : ℕ} {bound : ℕ∞}
    (hbound :
      LayeredReachability.OutdegreeAtMost bound
        (LBA.Step M : DLBA.Cfg Γ Λ n → DLBA.Cfg Γ Λ n → Prop)) :
    LayeredReachability.OutdegreeAtMost bound
      (ClockedStep M : ClockedCfg Γ Λ n → ClockedCfg Γ Λ n → Prop) :=
  LayeredReachability.strictEdge_outdegreeAtMost hbound

/-- Every uniform source indegree bound is preserved by strict clock layering. -/
public theorem clockedStep_indegreeAtMost
    (M : LBA.Machine Γ Λ) {n : ℕ} {bound : ℕ∞}
    (hbound :
      LayeredReachability.IndegreeAtMost bound
        (LBA.Step M : DLBA.Cfg Γ Λ n → DLBA.Cfg Γ Λ n → Prop)) :
    LayeredReachability.IndegreeAtMost bound
      (ClockedStep M : ClockedCfg Γ Λ n → ClockedCfg Γ Λ n → Prop) :=
  LayeredReachability.strictEdge_indegreeAtMost hbound

/-- Simultaneous arbitrary indegree and outdegree bounds are preserved by strict clock
layering. -/
public theorem clockedStep_directedDegreeAtMost
    (M : LBA.Machine Γ Λ) {n : ℕ} {bound : ℕ∞}
    (hbound :
      LayeredReachability.DirectedDegreeAtMost bound
        (LBA.Step M : DLBA.Cfg Γ Λ n → DLBA.Cfg Γ Λ n → Prop)) :
    LayeredReachability.DirectedDegreeAtMost bound
      (ClockedStep M : ClockedCfg Γ Λ n → ClockedCfg Γ Λ n → Prop) :=
  LayeredReachability.strictEdge_directedDegreeAtMost hbound

/-! ## A concrete same-width exponential clock capacity -/

section Capacity

/-- A constant clock radix large enough to dominate the source alphabet and state set. -/
@[expose]
public def clockRadix (Γ Λ : Type*) [Fintype Γ] [Fintype Λ] : ℕ :=
  Nat.mul (Nat.mul 2 (Fintype.card Γ)) (Fintype.card Λ)

/-- The number of base-`clockRadix` rows having one digit per physical tape cell. -/
@[expose]
public def clockCapacity (Γ Λ : Type*) [Fintype Γ] [Fintype Λ] (n : ℕ) : ℕ :=
  clockRadix (Γ := Γ) (Λ := Λ) ^ (n + 1)

/-- One clock digit. -/
public abbrev ClockDigit (Γ Λ : Type*) [Fintype Γ] [Fintype Λ] :=
  Fin (clockRadix (Γ := Γ) (Λ := Λ))

/-- A same-width row of clock digits. -/
public abbrev ClockRow (Γ Λ : Type*) [Fintype Γ] [Fintype Λ] (n : ℕ) :=
  Fin (n + 1) → ClockDigit (Γ := Γ) (Λ := Λ)

/-- The explicit radix-order codec on the concrete `Fin clockRadix` digit type. -/
public def clockCodec (Γ Λ : Type*) [Fintype Γ] [Fintype Λ] :
    RowNumeral.DigitCodec (ClockDigit (Γ := Γ) (Λ := Λ)) where
  toFin := finCongr (Fintype.card_fin _).symm

@[simp]
public theorem clockCodec_radix :
    (clockCodec (Γ := Γ) (Λ := Λ)).radix =
      clockRadix (Γ := Γ) (Λ := Λ) := by
  simp [RowNumeral.DigitCodec.radix]

/-- Same-width clock rows have exactly the advertised exponential capacity. -/
public theorem card_clockRow (n : ℕ) :
    Fintype.card (ClockRow (Γ := Γ) (Λ := Λ) n) =
      clockCapacity (Γ := Γ) (Λ := Λ) n := by
  simp [ClockRow, ClockDigit, clockCapacity, clockRadix]

variable [Nonempty Γ] [Nonempty Λ]

/-- The chosen radix is positive. -/
public theorem clockRadix_pos :
    0 < clockRadix (Γ := Γ) (Λ := Λ) := by
  exact Nat.mul_pos
    (Nat.mul_pos (show 0 < (2 : ℕ) by decide)
      (Fintype.card_pos_iff.mpr inferInstance))
    (Fintype.card_pos_iff.mpr inferInstance)

/-- The concrete clock digit type is inhabited because the chosen radix is positive. -/
public instance instNonemptyClockDigit :
    Nonempty (ClockDigit (Γ := Γ) (Λ := Λ)) :=
  ⟨⟨0, clockRadix_pos (Γ := Γ) (Λ := Λ)⟩⟩

/-- The concrete base-`2 * |Γ| * |Λ|` same-width clock has strictly more values than the
entire fixed-width source configuration space. -/
public theorem card_cfg_lt_clockCapacity (n : ℕ) :
    Fintype.card (DLBA.Cfg Γ Λ n) <
      clockCapacity (Γ := Γ) (Λ := Λ) n := by
  let W := n + 1
  let g := Fintype.card Γ
  let q := Fintype.card Λ
  have hg : 0 < g := Fintype.card_pos_iff.mpr inferInstance
  have hq : 0 < q := Fintype.card_pos_iff.mpr inferInstance
  have hfactor : 0 < q * g ^ W :=
    Nat.mul_pos hq (Nat.pow_pos hg)
  have hpowq : q ≤ q ^ W :=
    Nat.le_pow (by simp [W])
  rw [DLBA.card_cfg]
  simp only [clockCapacity, clockRadix]
  change q * g ^ W * W < (2 * g * q) ^ W
  calc
    q * g ^ W * W < q * g ^ W * 2 ^ W :=
      Nat.mul_lt_mul_of_pos_left W.lt_two_pow_self hfactor
    _ ≤ q ^ W * g ^ W * 2 ^ W := by
      gcongr
    _ = (2 * g * q) ^ W := by
      simp only [mul_pow]
      ac_rfl

/-- The exact clock layers `0, ..., |Cfg|` all fit into a same-width clock row. -/
public theorem card_exactLayers_le_clockRow (n : ℕ) :
    Fintype.card
        (Fin (Fintype.card (DLBA.Cfg Γ Λ n) + 1)) ≤
      Fintype.card (ClockRow (Γ := Γ) (Λ := Λ) n) := by
  rw [Fintype.card_fin, card_clockRow]
  exact Nat.succ_le_iff.mpr (card_cfg_lt_clockCapacity (Γ := Γ) (Λ := Λ) n)

/-- A concrete injection of every exact semantic clock layer into a same-width digit row. -/
public noncomputable def encodeClockLayer (n : ℕ) :
    Fin (Fintype.card (DLBA.Cfg Γ Λ n) + 1) ↪
      ClockRow (Γ := Γ) (Λ := Λ) n where
  toFun layer :=
    (Fintype.equivFin (ClockRow (Γ := Γ) (Λ := Λ) n)).symm
      (Fin.castLE
        (by
          simpa using
            card_exactLayers_le_clockRow (Γ := Γ) (Λ := Λ) n)
        layer)
  inj' := by
    intro left right heq
    apply Fin.ext
    have hfin := congrArg
      (Fintype.equivFin (ClockRow (Γ := Γ) (Λ := Λ) n)) heq
    simpa using congrArg Fin.val hfin

/-! ### Operational row-numeral encoding

Unlike `encodeClockLayer`, the following representation is not chosen through an arbitrary
equivalence with a function space.  It is the canonical least-significant-digit-first odometer
from `RowNumeral`: layer `k` is obtained by applying `nextRow` exactly `k` times to the all-zero
row. -/

/-- Canonical same-width numeral for a natural clock layer.  Values at or above the capacity
wrap around; all semantic layers used below are proved to be strictly in range. -/
@[expose]
public def encodeLayerRow (n layer : ℕ) :
    List (ClockDigit (Γ := Γ) (Λ := Λ)) :=
  let E := clockCodec (Γ := Γ) (Λ := Λ)
  E.nextRow^[layer] (E.zeroRow (n + 1))

/-- Every encoded layer uses exactly one digit per physical tape cell. -/
@[simp]
public theorem length_encodeLayerRow (n layer : ℕ) :
    (encodeLayerRow (Γ := Γ) (Λ := Λ) n layer).length = n + 1 := by
  simp [encodeLayerRow]

/-- Below the concrete exponential capacity, the row numeral has exactly the requested value. -/
public theorem value_encodeLayerRow {n layer : ℕ}
    (hlayer : layer < clockCapacity (Γ := Γ) (Λ := Λ) n) :
    (clockCodec (Γ := Γ) (Λ := Λ)).value
        (encodeLayerRow (Γ := Γ) (Λ := Λ) n layer) = layer := by
  apply (clockCodec (Γ := Γ) (Λ := Λ)).value_iterate_nextRow_zeroRow
  simpa [clockCapacity] using hlayer

/-- In-range natural layers have distinct concrete odometer rows. -/
public theorem encodeLayerRow_injective_of_lt_capacity {n left right : ℕ}
    (hleft : left < clockCapacity (Γ := Γ) (Λ := Λ) n)
    (hright : right < clockCapacity (Γ := Γ) (Λ := Λ) n)
    (hrows :
      encodeLayerRow (Γ := Γ) (Λ := Λ) n left =
        encodeLayerRow (Γ := Γ) (Λ := Λ) n right) :
    left = right := by
  have hvalue := congrArg
    (clockCodec (Γ := Γ) (Λ := Λ)).value hrows
  simpa [value_encodeLayerRow hleft, value_encodeLayerRow hright] using hvalue

/-- Encoding a successor layer is one application of the concrete row successor. -/
public theorem encodeLayerRow_succ (n layer : ℕ) :
    encodeLayerRow (Γ := Γ) (Λ := Λ) n (layer + 1) =
      (clockCodec (Γ := Γ) (Λ := Λ)).nextRow
        (encodeLayerRow (Γ := Γ) (Λ := Λ) n layer) := by
  simp [encodeLayerRow, Function.iterate_succ_apply']

/-- Every layer strictly below the source-configuration count has a nonoverflowing next row. -/
public theorem increment_encodeLayerRow_not_overflow
    {n layer : ℕ} (hlayer : layer < Fintype.card (DLBA.Cfg Γ Λ n)) :
    ((clockCodec (Γ := Γ) (Λ := Λ)).increment
      (encodeLayerRow (Γ := Γ) (Λ := Λ) n layer)).2 = false := by
  have hcfg :=
    card_cfg_lt_clockCapacity (Γ := Γ) (Λ := Λ) n
  have hlayerCapacity :
      layer < clockCapacity (Γ := Γ) (Λ := Λ) n :=
    hlayer.trans hcfg
  let E := clockCodec (Γ := Γ) (Λ := Λ)
  have hlayerRadix :
      layer < E.radix ^ (n + 1) := by
    simpa [E, clockCapacity] using hlayerCapacity
  have hsuccRadix :
      layer + 1 < E.radix ^ (n + 1) := by
    simpa [E, clockCapacity] using hlayer.succ_le.trans_lt hcfg
  have hno :=
    (E.increment_iterate_nextRow_not_overflow_iff hlayerRadix).2 hsuccRadix
  simpa [encodeLayerRow, E] using hno

/-- The canonical row attached to an exact semantic layer. -/
@[expose]
public def encodeSemanticLayer (n : ℕ)
    (layer : Fin (Fintype.card (DLBA.Cfg Γ Λ n) + 1)) :
    List (ClockDigit (Γ := Γ) (Λ := Λ)) :=
  encodeLayerRow (Γ := Γ) (Λ := Λ) n layer.val

/-- Exact semantic layers also use precisely one digit per physical tape cell. -/
@[simp]
public theorem length_encodeSemanticLayer (n : ℕ)
    (layer : Fin (Fintype.card (DLBA.Cfg Γ Λ n) + 1)) :
    (encodeSemanticLayer (Γ := Γ) (Λ := Λ) n layer).length = n + 1 :=
  length_encodeLayerRow n layer.val

/-- The concrete numeral of an exact semantic layer evaluates to its layer index. -/
public theorem value_encodeSemanticLayer (n : ℕ)
    (layer : Fin (Fintype.card (DLBA.Cfg Γ Λ n) + 1)) :
    (clockCodec (Γ := Γ) (Λ := Λ)).value
        (encodeSemanticLayer (Γ := Γ) (Λ := Λ) n layer) = layer.val := by
  apply value_encodeLayerRow
  exact (Nat.le_of_lt_succ layer.isLt).trans_lt
    (card_cfg_lt_clockCapacity (Γ := Γ) (Λ := Λ) n)

/-- The operational row encoding is injective on all exact semantic layers. -/
public theorem encodeSemanticLayer_injective (n : ℕ) :
    Function.Injective
      (encodeSemanticLayer (Γ := Γ) (Λ := Λ) n) := by
  intro left right hrows
  apply Fin.ext
  have hvalue := congrArg
    (clockCodec (Γ := Γ) (Λ := Λ)).value hrows
  simpa [value_encodeSemanticLayer] using hvalue

/-- A semantic strict-clock step is represented by one concrete row-numeral successor. -/
public theorem encodeSemanticLayer_of_clockedStep
    (M : LBA.Machine Γ Λ) {n : ℕ}
    {old new : ClockedCfg Γ Λ n}
    (hstep : ClockedStep M old new) :
    encodeSemanticLayer (Γ := Γ) (Λ := Λ) n new.2 =
      (clockCodec (Γ := Γ) (Λ := Λ)).nextRow
        (encodeSemanticLayer (Γ := Γ) (Λ := Λ) n old.2) := by
  change encodeLayerRow (Γ := Γ) (Λ := Λ) n new.2.val =
    (clockCodec (Γ := Γ) (Λ := Λ)).nextRow
      (encodeLayerRow (Γ := Γ) (Λ := Λ) n old.2.val)
  rw [hstep.1]
  exact encodeLayerRow_succ n old.2.val

/-- The concrete row increment associated with every semantic strict-clock edge is
nonoverflowing. -/
public theorem increment_encodeSemanticLayer_not_overflow_of_clockedStep
    (M : LBA.Machine Γ Λ) {n : ℕ}
    {old new : ClockedCfg Γ Λ n}
    (hstep : ClockedStep M old new) :
    ((clockCodec (Γ := Γ) (Λ := Λ)).increment
      (encodeSemanticLayer (Γ := Γ) (Λ := Λ) n old.2)).2 = false := by
  apply increment_encodeLayerRow_not_overflow
  have hnew : new.2.val ≤ Fintype.card (DLBA.Cfg Γ Λ n) :=
    Nat.le_of_lt_succ new.2.isLt
  have holdSucc :
      old.2.val + 1 ≤ Fintype.card (DLBA.Cfg Γ Λ n) := by
    rwa [← hstep.1]
  exact Nat.lt_of_succ_le holdSucc

/-- Combined operational form: a semantic strict-clock edge is exactly one nonoverflowing
canonical row increment. -/
public theorem increment_encodeSemanticLayer_of_clockedStep
    (M : LBA.Machine Γ Λ) {n : ℕ}
    {old new : ClockedCfg Γ Λ n}
    (hstep : ClockedStep M old new) :
    (clockCodec (Γ := Γ) (Λ := Λ)).increment
        (encodeSemanticLayer (Γ := Γ) (Λ := Λ) n old.2) =
      (encodeSemanticLayer (Γ := Γ) (Λ := Λ) n new.2, false) := by
  apply Prod.ext
  · simpa [RowNumeral.DigitCodec.nextRow] using
      (encodeSemanticLayer_of_clockedStep M hstep).symm
  · exact increment_encodeSemanticLayer_not_overflow_of_clockedStep M hstep

/-- The finite-state synchronous successor checker accepts the concrete rows associated with
every semantic strict-clock edge. -/
public theorem checkSucc_encodeSemanticLayer_of_clockedStep
    (M : LBA.Machine Γ Λ) {n : ℕ}
    {old new : ClockedCfg Γ Λ n}
    (hstep : ClockedStep M old new) :
    (clockCodec (Γ := Γ) (Λ := Λ)).checkSucc
        (encodeSemanticLayer (Γ := Γ) (Λ := Λ) n old.2)
        (encodeSemanticLayer (Γ := Γ) (Λ := Λ) n new.2) = true := by
  rw [(clockCodec (Γ := Γ) (Λ := Λ)).checkSucc_eq_true_iff]
  have hinc := increment_encodeSemanticLayer_of_clockedStep M hstep
  exact ⟨(congrArg Prod.fst hinc).symm, congrArg Prod.snd hinc⟩

end Capacity

end LBA.StrictClockLayering

end
