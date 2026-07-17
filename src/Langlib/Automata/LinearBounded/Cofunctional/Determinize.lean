module

public import Langlib.Automata.LinearBounded.Cofunctional
public import Langlib.Automata.LinearBounded.Cofunctional.Resources
import Mathlib.Tactic

@[expose]
public section

/-!
# Same-width deterministic search data for cofunctional LBAs

A cofunctional finite LBA can be decided by a deterministic exhaustive search:

1. enumerate every possible accepting target configuration;
2. from each target, repeatedly find its unique predecessor;
3. accept if the canonical source configuration is reached;
4. abandon a target after one configuration-space worth of predecessor steps.

`Cofunctional.lean` proves this algorithm correct as a finite Boolean search.
`Cofunctional/Resources.lean` proves that configurations and the complete backtracking counter
fit into rows of exactly the input width.

This file joins those two results.  It packages a successful search as a *same-width witness*
containing:

* the accepting target;
* its canonical width-preserving row encoding;
* a proof that the target row occurs in the canonical row enumeration;
* an equally wide fuel row whose numeric value is the backtracking depth; and
* the successful bounded predecessor traversal.

The final language theorem also records the explicit empty-word bit used by Langlib's marker-free
`LanguageRecognized` presentation.

These theorems are the semantic and resource specification for a concrete same-tape compiler.
They do **not** yet define the low-level `DLBA.Machine` that performs the nested sweeps.  Such a
machine needs deterministic microcode for row initialization, target enumeration, predecessor
enumeration, edge-verifier scans, copying, and fuel increment, together with an operational
simulation proof.  No reusable deterministic multi-track sweep compiler currently exists in the
repository.
-/

namespace LBA.CofunctionalDeterminize

open CofunctionalResources

variable {Γ Λ : Type*}

/-- The finite row alphabet used to enumerate encoded configurations. -/
public abbrev ConfigCell (Γ Λ : Type*) :=
  LBA.RowCell Unit Γ Λ

public instance : Nonempty (ConfigCell Γ Λ) :=
  ⟨LBA.RowCell.raw ()⟩

/-- Canonical same-width list encoding of a bounded configuration. -/
@[expose]
public def encodeCfgRow {n : ℕ} (cfg : DLBA.Cfg Γ Λ n) :
    List (ConfigCell Γ Λ) :=
  List.ofFn (encodeCfgCell cfg)

@[simp]
public theorem length_encodeCfgRow {n : ℕ} (cfg : DLBA.Cfg Γ Λ n) :
    (encodeCfgRow cfg).length = n + 1 := by
  simp [encodeCfgRow]

variable [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]

/-- The canonical codec used for target-configuration rows. -/
public noncomputable def configCodec :
    RowNumeral.DigitCodec (ConfigCell Γ Λ) :=
  RowNumeral.fintypeCodec (ConfigCell Γ Λ)

omit [DecidableEq Γ] [DecidableEq Λ] in
/-- Every encoded configuration occurs in the canonical enumeration of rows of the same width. -/
public theorem encodeCfgRow_mem_rowEnumeration {n : ℕ}
    (cfg : DLBA.Cfg Γ Λ n) :
    encodeCfgRow cfg ∈
      (configCodec (Γ := Γ) (Λ := Λ)).rowEnumeration (n + 1) := by
  rw [(configCodec (Γ := Γ) (Λ := Λ)).mem_rowEnumeration_iff]
  exact length_encodeCfgRow cfg

omit [DecidableEq Γ] [DecidableEq Λ] in
/-- The exact canonical enumeration position of an encoded configuration is its row numeral
value. -/
public theorem iterate_nextRow_encodeCfgRow {n : ℕ}
    (cfg : DLBA.Cfg Γ Λ n) :
    (configCodec (Γ := Γ) (Λ := Λ)).nextRow^[
        (configCodec (Γ := Γ) (Λ := Λ)).value (encodeCfgRow cfg)]
      ((configCodec (Γ := Γ) (Λ := Λ)).zeroRow (n + 1)) =
        encodeCfgRow cfg := by
  simpa using
    (configCodec (Γ := Γ) (Λ := Λ)).iterate_nextRow_value_eq
      (encodeCfgRow cfg)

/-- A successful cofunctional search, with every unbounded-looking object represented by a row
of exactly the source tape width.

The target row is explicitly required to occur in the canonical row enumeration.  The fuel row
uses the strictly larger `Option ConfigCell` radix, so it represents all depths up to the complete
configuration-space cardinality, including the endpoint. -/
public structure SameWidthWitness
    (M : LBA.Machine Γ Λ) {n : ℕ} (source : DLBA.Cfg Γ Λ n) where
  target : DLBA.Cfg Γ Λ n
  steps : ℕ
  targetRow : List (ConfigCell Γ Λ)
  fuelRow : List (Option (ConfigCell Γ Λ))
  target_accepts : M.accept target.state = true
  targetRow_eq : targetRow = encodeCfgRow target
  targetRow_mem :
    targetRow ∈ (configCodec (Γ := Γ) (Λ := Λ)).rowEnumeration (n + 1)
  fuelRow_length : fuelRow.length = n + 1
  fuelRow_value :
    (RowNumeral.fuelCodec (ConfigCell Γ Λ)).value fuelRow = steps
  steps_le : steps ≤ Fintype.card (DLBA.Cfg Γ Λ n)
  backtrack_eq : M.backtrack target steps = some source

/-- Cofunctional acceptance is equivalent to the existence of a successful same-width search
witness. -/
public theorem sameWidthWitness_iff_accepts
    (M : LBA.Machine Γ Λ) (hco : M.Cofunctional)
    {n : ℕ} (source : DLBA.Cfg Γ Λ n) :
    Nonempty (SameWidthWitness M source) ↔ LBA.Accepts M source := by
  constructor
  · rintro ⟨⟨target, steps, targetRow, fuelRow, haccept, _targetRowEq,
      _targetRowMem, _fuelLength, _fuelValue, hsteps, hbacktrack⟩⟩
    exact (M.accepts_iff_exists_backtrack_le_card hco source).2
      ⟨target, haccept, steps, hsteps, hbacktrack⟩
  · intro haccepts
    obtain ⟨target, haccept, steps, hsteps, hbacktrack⟩ :=
      (M.accepts_iff_exists_backtrack_le_card hco source).1 haccepts
    obtain ⟨fuelRow, hfuelLength, hfuelValue⟩ :=
      exists_fuelRow_of_le_card_cfg (Γ := Γ) (Λ := Λ) n steps hsteps
    exact ⟨{
      target := target
      steps := steps
      targetRow := encodeCfgRow target
      fuelRow := fuelRow
      target_accepts := haccept
      targetRow_eq := rfl
      targetRow_mem := encodeCfgRow_mem_rowEnumeration target
      fuelRow_length := hfuelLength
      fuelRow_value := hfuelValue
      steps_le := hsteps
      backtrack_eq := hbacktrack }⟩

variable {T : Type*}

/-- Same-width nonempty-input witness for a marker-free LBA presentation. -/
public def LanguageWitness
    (M : LBA.Machine Γ Λ) (embed : T → Γ) (w : List T) : Prop :=
  ∃ hw : w.map embed ≠ [],
    Nonempty (SameWidthWitness M (LBA.initCfgList M (w.map embed) hw))

/-- The explicit-empty-bit marker-free language of a cofunctional LBA is characterized by:

* the supplied Boolean bit on the empty word;
* a successful same-width exhaustive-backtracking witness on every nonempty word.

This theorem is a specification for the missing concrete `DLBA.Machine`; it is not itself a
class-level `is_DLBA` result. -/
public theorem mem_languageRecognized_iff_sameWidthWitness
    (M : LBA.Machine Γ Λ) (hco : M.Cofunctional)
    (embed : T → Γ) (acceptEmpty : Bool) (w : List T) :
    w ∈ LBA.LanguageRecognized M embed acceptEmpty ↔
      (acceptEmpty = true ∧ w = []) ∨ LanguageWitness M embed w := by
  constructor
  · rintro (hempty | hnonempty)
    · exact Or.inl hempty
    · right
      rcases hnonempty with ⟨hw, haccepts⟩
      exact ⟨hw, (sameWidthWitness_iff_accepts M hco _).2 haccepts⟩
  · rintro (hempty | hwitness)
    · exact Or.inl hempty
    · right
      rcases hwitness with ⟨hw, hwitness⟩
      exact ⟨hw, (sameWidthWitness_iff_accepts M hco _).1 hwitness⟩

end LBA.CofunctionalDeterminize

end
