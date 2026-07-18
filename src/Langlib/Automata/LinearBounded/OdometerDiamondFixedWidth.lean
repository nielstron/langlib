module

public import Langlib.Automata.LinearBounded.OdometerDiamondRowSystem
import Mathlib.Tactic

@[expose]
public section

/-!
# The complete fixed-width odometer relation

`OdometerDiamondRowSystem.rowStep_iff_exists_encoded_edge` characterizes every accepted
positive-width row step, including steps whose endpoints were not assumed canonical in advance.
This file transfers the semantic three-matching cover to the complete type of rows of a fixed
width.  Rows outside the canonical image have no incident edge and therefore do not disturb
biuniqueness, the one-edge path bound, or acyclicity.

The statements are also restated at width `n + 1`.  Thus the result ranges over every nonempty
physical row width without an artificial lower bound on `n`; the cell alphabet is the explicitly
fixed finite alphabet from the odometer system.
It remains a theorem about the certified row relation, not about the administrative configuration
graph of the LBA which recognizes its reachability language.
-/

namespace OdometerDiamondRowSystem

open Relation

/-! ## Fixed-width rows and the exact relation -/

/-- The complete type of rows having width `w`, canonical or malformed. -/
public abbrev FixedRow (w : ℕ) := { row : List Cell // row.length = w }

/-- Regard a semantic odometer vertex as a row of its prescribed width. -/
@[expose]
public def fixedEncode {w : ℕ} (vertex : Vertex w) : FixedRow w :=
  ⟨encode vertex, encode_length vertex⟩

/-- The canonical embedding remains injective at every positive width. -/
public theorem fixedEncode_injective {w : ℕ} (hw : 0 < w) :
    Function.Injective (@fixedEncode w) := by
  intro left right heq
  apply encode_injective hw
  exact congrArg Subtype.val heq

/-- The complete certified transition relation on rows of one fixed width. -/
@[expose]
public def FixedWidthStep {w : ℕ} (old new : FixedRow w) : Prop :=
  system.RowStep old.1 new.1

/-- At positive width every edge of the complete row relation has canonical endpoints and is
exactly one semantic odometer edge.  Malformed rows occur in the ambient type but have no edge. -/
public theorem fixedWidthStep_iff_exists_encoded_edge {w : ℕ} (hw : 0 < w)
    (old new : FixedRow w) :
    FixedWidthStep old new ↔
      ∃ source destination : Vertex w,
        old = fixedEncode source ∧ new = fixedEncode destination ∧ Edge source destination := by
  constructor
  · intro hstep
    obtain ⟨source, destination, hold, hnew, hedge⟩ :=
      (rowStep_iff_exists_encoded_edge hw old.property).mp hstep
    refine ⟨source, destination, ?_, ?_, hedge⟩
    · exact Subtype.ext hold
    · exact Subtype.ext hnew
  · rintro ⟨source, destination, rfl, rfl, hedge⟩
    exact rowStep_of_edge hw hedge

/-- A fixed-width row is active exactly when it is the encoding of a semantic odometer vertex. -/
@[expose]
public def FixedWidthActive {w : ℕ} (row : FixedRow w) : Prop :=
  ∃ vertex : Vertex w, row = fixedEncode vertex

/-- At positive width, the active rows are precisely those incident with a complete row edge.
This makes the isolation of every malformed ambient row explicit. -/
public theorem fixedWidthActive_iff_incident {w : ℕ} (hw : 0 < w)
    (row : FixedRow w) :
    FixedWidthActive row ↔
      (∃ next, FixedWidthStep row next) ∨
        ∃ previous, FixedWidthStep previous row := by
  constructor
  · rintro ⟨vertex, rfl⟩
    cases vertex with
    | junction index =>
        apply Or.inl
        refine ⟨fixedEncode (.branch index false), ?_⟩
        apply (fixedWidthStep_iff_exists_encoded_edge hw _ _).mpr
        exact ⟨.junction index, .branch index false, rfl, rfl, by simp [Edge]⟩
    | branch index choice =>
        apply Or.inr
        refine ⟨fixedEncode (.junction index), ?_⟩
        apply (fixedWidthStep_iff_exists_encoded_edge hw _ _).mpr
        exact ⟨.junction index, .branch index choice, rfl, rfl, by simp [Edge]⟩
    | merge index =>
        apply Or.inr
        refine ⟨fixedEncode (.branch index false), ?_⟩
        apply (fixedWidthStep_iff_exists_encoded_edge hw _ _).mpr
        exact ⟨.branch index false, .merge index, rfl, rfl, by simp [Edge]⟩
    | target =>
        apply Or.inr
        have hcapacity : 0 < 2 ^ w := pow_pos (by omega) w
        let finalIndex : Fin (2 ^ w) := ⟨2 ^ w - 1, by omega⟩
        refine ⟨fixedEncode (.merge finalIndex), ?_⟩
        apply (fixedWidthStep_iff_exists_encoded_edge hw _ _).mpr
        refine ⟨.merge finalIndex, .target, rfl, rfl, ?_⟩
        simp only [Edge]
        dsimp only [finalIndex]
        omega
  · rintro (⟨next, hstep⟩ | ⟨previous, hstep⟩)
    · obtain ⟨source, destination, hold, -, -⟩ :=
        (fixedWidthStep_iff_exists_encoded_edge hw row next).mp hstep
      exact ⟨source, hold⟩
    · obtain ⟨source, destination, -, hrow, -⟩ :=
        (fixedWidthStep_iff_exists_encoded_edge hw previous row).mp hstep
      exact ⟨destination, hrow⟩

/-- A positive-width row is malformed exactly when it has neither an outgoing nor an incoming
accepted row step. -/
public theorem not_fixedWidthActive_iff_isolated {w : ℕ} (hw : 0 < w)
    (row : FixedRow w) :
    ¬ FixedWidthActive row ↔
      (∀ next, ¬ FixedWidthStep row next) ∧
        ∀ previous, ¬ FixedWidthStep previous row := by
  constructor
  · intro hinactive
    constructor
    · intro next hstep
      exact hinactive ((fixedWidthActive_iff_incident hw row).mpr
        (Or.inl ⟨next, hstep⟩))
    · intro previous hstep
      exact hinactive ((fixedWidthActive_iff_incident hw row).mpr
        (Or.inr ⟨previous, hstep⟩))
  · rintro ⟨hnext, hprevious⟩ hactive
    rcases (fixedWidthActive_iff_incident hw row).mp hactive with
      ⟨next, hstep⟩ | ⟨previous, hstep⟩
    · exact hnext next hstep
    · exact hprevious previous hstep

/-! ## Three matchings on the complete row type -/

/-- Pull one semantic matching color onto the complete fixed-width row type. -/
@[expose]
public def FixedWidthLayer {w : ℕ} (color : Fin 3) :
    FixedRow w → FixedRow w → Prop :=
  fun old new ↦ ∃ source destination : Vertex w,
    old = fixedEncode source ∧ new = fixedEncode destination ∧ Layer color source destination

/-- The complete fixed-width row relation is exactly the union of its three pulled-back colors,
and every accepted edge has a unique color. -/
public theorem fixedWidthStep_iff_existsUnique_layer {w : ℕ} (hw : 0 < w)
    (old new : FixedRow w) :
    FixedWidthStep old new ↔ ∃! color : Fin 3, FixedWidthLayer color old new := by
  constructor
  · intro hstep
    obtain ⟨source, destination, rfl, rfl, hedge⟩ :=
      (fixedWidthStep_iff_exists_encoded_edge hw old new).mp hstep
    obtain ⟨color, hcolor, hunique⟩ :=
      (edge_iff_existsUnique_layer source destination).mp hedge
    refine ⟨color, ⟨source, destination, rfl, rfl, hcolor⟩, ?_⟩
    intro other hother
    obtain ⟨otherSource, otherTarget, hold, hnew, hotherLayer⟩ := hother
    have hsource : otherSource = source :=
      fixedEncode_injective hw (hold.symm)
    have htarget : otherTarget = destination :=
      fixedEncode_injective hw (hnew.symm)
    subst otherSource
    subst otherTarget
    exact hunique other hotherLayer
  · rintro ⟨color, ⟨source, destination, hold, hnew, hcolor⟩, -⟩
    apply (fixedWidthStep_iff_exists_encoded_edge hw old new).mpr
    exact ⟨source, destination, hold, hnew,
      layer_sub_edge color source destination hcolor⟩

/-- Every pulled-back color is functional and cofunctional on the complete row type. -/
public theorem fixedWidthLayer_biUnique {w : ℕ} (hw : 0 < w) (color : Fin 3) :
    Relator.BiUnique (@FixedWidthLayer w color) := by
  have hinjective := fixedEncode_injective (w := w) hw
  constructor
  · intro left right destination hleft hright
    obtain ⟨leftSource, leftTarget, hleft, hleftTarget, hleftLayer⟩ := hleft
    obtain ⟨rightSource, rightTarget, hright, hrightTarget, hrightLayer⟩ := hright
    have htarget : leftTarget = rightTarget := by
      apply hinjective
      exact hleftTarget.symm.trans hrightTarget
    subst rightTarget
    have hsource : leftSource = rightSource :=
      (layer_biUnique color).1 hleftLayer hrightLayer
    subst rightSource
    exact hleft.trans hright.symm
  · intro source left right hleft hright
    obtain ⟨leftSource, leftTarget, hleftSource, hleft, hleftLayer⟩ := hleft
    obtain ⟨rightSource, rightTarget, hrightSource, hright, hrightLayer⟩ := hright
    have hsource : leftSource = rightSource := by
      apply hinjective
      exact hleftSource.symm.trans hrightSource
    subst rightSource
    have htarget : leftTarget = rightTarget :=
      (layer_biUnique color).2 hleftLayer hrightLayer
    subst rightTarget
    exact hleft.trans hright.symm

/-- No two edges of a pulled-back color are composable, even through a malformed ambient row. -/
public theorem fixedWidthLayer_pathLengthAtMostOne {w : ℕ} (hw : 0 < w) (color : Fin 3) :
    LinearTwoDiforestReachability.PathLengthAtMostOne (@FixedWidthLayer w color) := by
  intro first middle last hfirst hlast
  obtain ⟨firstSource, firstTarget, -, hfirstMiddle, hfirstLayer⟩ := hfirst
  obtain ⟨lastSource, lastTarget, hlastMiddle, -, hlastLayer⟩ := hlast
  have hmiddle : firstTarget = lastSource := by
    apply encode_injective hw
    exact congrArg Subtype.val (hfirstMiddle.symm.trans hlastMiddle)
  subst lastSource
  exact layer_pathLengthAtMostOne color hfirstLayer hlastLayer

/-! ## Acyclicity of the complete relation -/

/-- Decode a row in the canonical image, using the source vertex only as a harmless default for
an isolated malformed row. -/
noncomputable def fixedDecode {w : ℕ} (row : FixedRow w) : Vertex w :=
  if h : ∃ vertex, row = fixedEncode vertex then Classical.choose h else source w

/-- Decoding reverses canonical encoding at positive width. -/
public theorem fixedDecode_fixedEncode {w : ℕ} (hw : 0 < w) (vertex : Vertex w) :
    fixedDecode (fixedEncode vertex) = vertex := by
  unfold fixedDecode
  split
  · rename_i h
    apply fixedEncode_injective hw
    exact (Classical.choose_spec h).symm
  · rename_i h
    exact (h ⟨vertex, rfl⟩).elim

/-- Decoding maps every complete row step to a semantic edge. -/
public theorem edge_fixedDecode_of_fixedWidthStep {w : ℕ} (hw : 0 < w)
    {old new : FixedRow w} (hstep : FixedWidthStep old new) :
    Edge (fixedDecode old) (fixedDecode new) := by
  obtain ⟨source, destination, rfl, rfl, hedge⟩ :=
    (fixedWidthStep_iff_exists_encoded_edge hw old new).mp hstep
  simpa [fixedDecode_fixedEncode hw] using hedge

/-- The complete positive-width certified row relation is acyclic; malformed rows are isolated
and canonical rows inherit the strict semantic rank. -/
public theorem fixedWidthStep_acyclic {w : ℕ} (hw : 0 < w) (row : FixedRow w) :
    ¬ TransGen (@FixedWidthStep w) row row := by
  intro hcycle
  have hsemantic : TransGen (@Edge w) (fixedDecode row) (fixedDecode row) :=
    TransGen.lift fixedDecode (fun _ _ hstep ↦ edge_fixedDecode_of_fixedWidthStep hw hstep)
      hcycle
  exact acyclic w (fixedDecode row) hsemantic

/-! ## Bound-free physical-width restatement -/

/-- For every physical width parameter `n`, all rows of width `n + 1` form an acyclic exact
union of three directed matchings. -/
public theorem complete_nonempty_width_threeMatching (n : ℕ) :
    (∀ old new : FixedRow (n + 1),
        FixedWidthStep old new ↔ ∃! color : Fin 3, FixedWidthLayer color old new) ∧
      (∀ color, Relator.BiUnique (@FixedWidthLayer (n + 1) color) ∧
        LinearTwoDiforestReachability.PathLengthAtMostOne
          (@FixedWidthLayer (n + 1) color)) ∧
      ∀ row, ¬ TransGen (@FixedWidthStep (n + 1)) row row := by
  have hw : 0 < n + 1 := Nat.zero_lt_succ n
  exact ⟨fun old new ↦ fixedWidthStep_iff_existsUnique_layer hw old new,
    fun color ↦ ⟨fixedWidthLayer_biUnique hw color,
      fixedWidthLayer_pathLengthAtMostOne hw color⟩,
    fixedWidthStep_acyclic hw⟩

end OdometerDiamondRowSystem

end
