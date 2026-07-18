module

public import Langlib.Automata.LinearBounded.StepTraceCrossing
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Tactic

@[expose]
public section

/-!
# Simple LBA traces bounded by physical head movement

This module relates the length of a nonrepeating finite LBA computation to its tape-head
movement.  A trace is *simple* when its complete list of configurations has no duplicate.
Its `totalCrossingCount` sums the crossing counts over all physical boundaries.

A step whose head really moves crosses exactly one boundary.  This remains true with the
bounded tape's clamping semantics: a left move at the left endpoint, a right move at the right
endpoint, and a `stay` move cross no boundary.  A simple trace is then split into maximal blocks
with stationary head.  Throughout one such block, all cells outside the head are invariant, so
the current configuration is determined by the local pair `(state, read symbol)`.  Consequently
each block contains at most `|Λ| * |Γ|` configurations.

Summing the blocks gives

`trace.length + 1 ≤ (|Λ| * |Γ|) * (trace.totalCrossingCount + 1)`.

All statements are uniform in the finite state and tape-symbol types.  They also include the
one-cell case `n = 0`: there are no physical boundaries then, and the entire simple trace is one
stationary block.
-/

namespace LBA.StepTrace

universe u v
variable {Γ : Type u} {Λ : Type v} {n : ℕ}
variable {M : LBA.Machine Γ Λ}
variable {source target : DLBA.Cfg Γ Λ n}

def vertices : {source target : DLBA.Cfg Γ Λ n} →
    LBA.StepTrace M source target → List (DLBA.Cfg Γ Λ n)
  | _, _, .refl cfg => [cfg]
  | source, _, .head _ rest => source :: vertices rest

@[simp] theorem vertices_refl (cfg : DLBA.Cfg Γ Λ n) :
    vertices (.refl cfg : LBA.StepTrace M cfg cfg) = [cfg] := rfl

@[simp] theorem vertices_head {next : DLBA.Cfg Γ Λ n}
    (h : LBA.Step M source next) (rest : LBA.StepTrace M next target) :
    vertices (.head h rest) = source :: vertices rest := rfl

@[simp] theorem vertices_length (trace : LBA.StepTrace M source target) :
    trace.vertices.length = trace.length + 1 := by
  induction trace with
  | refl => rfl
  | head h rest ih => simp [vertices, length, ih, Nat.add_comm]

theorem vertices_isChain (trace : LBA.StepTrace M source target) :
    trace.vertices.IsChain (LBA.Step M) := by
  induction trace with
  | refl => simp [vertices]
  | head h rest ih =>
      cases rest with
      | refl cfg => simpa [vertices] using h
      | @head next next' target h' rest' =>
          simp only [vertices]
          exact List.isChain_cons.2 ⟨by simpa [vertices] using h, ih⟩

def Simple (trace : LBA.StepTrace M source target) : Prop := trace.vertices.Nodup

theorem crossingCount_le_length (b : Fin n)
    (trace : LBA.StepTrace M source target) :
    crossingCount b trace ≤ trace.length := by
  induction trace with
  | refl => simp
  | head h rest ih =>
      simp only [crossingCount, length]
      split <;> omega

/-- Across one machine step, at most one physical tape boundary can be crossed.

This explicitly covers clamped left/right moves at the end cells and `stay` moves: in
those cases no boundary is crossed. -/
theorem crossesBoundary_unique_of_step
    {old new : DLBA.Cfg Γ Λ n} (hstep : LBA.Step M old new)
    {b c : Fin n}
    (hb : CrossesBoundary b old new)
    (hc : CrossesBoundary c old new) : b = c := by
  rcases hstep with ⟨state, written, direction, henabled, rfl⟩
  cases direction with
  | left =>
      by_cases hpos : 0 < old.tape.head.val
      · have htape :
            ((old.tape.write written).moveHead .left).head.val =
              old.tape.head.val - 1 := by
          simp [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead, hpos]
        simp only [CrossesBoundary, CrossesRight, CrossesLeft,
          HeadAtOrLeft, HeadRight] at hb hc
        rw [htape] at hb hc
        ext
        rcases hb with hb | hb <;> rcases hc with hc | hc <;> omega
      · have htape :
            ((old.tape.write written).moveHead .left).head.val =
              old.tape.head.val := by
          simp [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead, hpos]
        simp only [CrossesBoundary, CrossesRight, CrossesLeft,
          HeadAtOrLeft, HeadRight] at hb
        rw [htape] at hb
        rcases hb with hb | hb <;> omega
  | right =>
      by_cases hlt : old.tape.head.val < n
      · have htape :
            ((old.tape.write written).moveHead .right).head.val =
              old.tape.head.val + 1 := by
          simp [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead, hlt]
        simp only [CrossesBoundary, CrossesRight, CrossesLeft,
          HeadAtOrLeft, HeadRight] at hb hc
        rw [htape] at hb hc
        ext
        rcases hb with hb | hb <;> rcases hc with hc | hc <;> omega
      · have htape :
            ((old.tape.write written).moveHead .right).head.val =
              old.tape.head.val := by
          simp [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead, hlt]
        simp only [CrossesBoundary, CrossesRight, CrossesLeft,
          HeadAtOrLeft, HeadRight] at hb
        rw [htape] at hb
        rcases hb with hb | hb <;> omega
  | stay =>
      simp [CrossesBoundary, CrossesRight, CrossesLeft,
        HeadAtOrLeft, HeadRight, DLBA.BoundedTape.write,
        DLBA.BoundedTape.moveHead] at hb
      rcases hb with hb | hb <;> omega

/-- Distinct head positions are separated by at least one physical boundary. -/
theorem exists_crossesBoundary_of_head_ne
    {old new : DLBA.Cfg Γ Λ n}
    (hhead : new.tape.head ≠ old.tape.head) :
    ∃ b : Fin n, CrossesBoundary b old new := by
  have hval : new.tape.head.val ≠ old.tape.head.val := by
    intro h
    exact hhead (Fin.ext h)
  by_cases hlt : old.tape.head.val < new.tape.head.val
  · let b : Fin n := ⟨old.tape.head.val, by
      have hnew := new.tape.head.isLt
      omega⟩
    exact ⟨b, Or.inl ⟨by simp [HeadAtOrLeft, b], by
      simp only [HeadRight, b]
      exact hlt⟩⟩
  · have hrev : new.tape.head.val < old.tape.head.val := by omega
    let b : Fin n := ⟨new.tape.head.val, by
      have hold := old.tape.head.isLt
      omega⟩
    exact ⟨b, Or.inr ⟨by
      simp only [HeadRight, b]
      exact hrev, by simp [HeadAtOrLeft, b]⟩⟩

/-- A step that physically moves the head crosses exactly one boundary. -/
theorem step_crossingIndicators_sum_eq_one_of_head_ne
    {old new : DLBA.Cfg Γ Λ n} (hstep : LBA.Step M old new)
    (hhead : new.tape.head ≠ old.tape.head) :
    (∑ b : Fin n, if CrossesBoundary b old new then (1 : ℕ) else 0) = 1 := by
  classical
  obtain ⟨b, hb⟩ := exists_crossesBoundary_of_head_ne hhead
  rw [← Finset.card_filter]
  apply Finset.card_eq_one.mpr
  refine ⟨b, ?_⟩
  ext c
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor
  · intro hc
    exact crossesBoundary_unique_of_step hstep hc hb
  · rintro rfl
    exact hb

/-- Total physical head movement, counted as boundary crossings. -/
def totalCrossingCount (trace : LBA.StepTrace M source target) : ℕ :=
  ∑ b : Fin n, crossingCount b trace

@[simp] theorem totalCrossingCount_refl (cfg : DLBA.Cfg Γ Λ n) :
    totalCrossingCount (.refl cfg : LBA.StepTrace M cfg cfg) = 0 := by
  simp [totalCrossingCount]

theorem totalCrossingCount_head {next : DLBA.Cfg Γ Λ n}
    (hstep : LBA.Step M source next)
    (rest : LBA.StepTrace M next target) :
    totalCrossingCount (.head hstep rest) =
      (if next.tape.head = source.tape.head then 0 else 1) +
        totalCrossingCount rest := by
  classical
  simp only [totalCrossingCount, crossingCount, Finset.sum_add_distrib]
  by_cases hhead : next.tape.head = source.tape.head
  · have hz :
        (∑ b : Fin n,
          if CrossesBoundary b source next then (1 : ℕ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro b hb
      have hn : ¬ CrossesBoundary b source next := by
        simp [CrossesBoundary, CrossesRight, CrossesLeft,
          HeadAtOrLeft, HeadRight, hhead]
      simp [hn]
    rw [hz, if_pos hhead]
  · rw [step_crossingIndicators_sum_eq_one_of_head_ne hstep hhead,
      if_neg hhead]

/-- The total crossing count of one step is exactly the indicator that its head position
changes.  In particular, a clamped endpoint move contributes zero. -/
@[simp] theorem totalCrossingCount_single
    (hstep : LBA.Step M source target) :
    totalCrossingCount (single hstep) =
      if target.tape.head = source.tape.head then 0 else 1 := by
  simpa [single] using
    (totalCrossingCount_head hstep
      (.refl target : LBA.StepTrace M target target))

@[simp] theorem totalCrossingCount_append
    (first : LBA.StepTrace M source middle)
    (second : LBA.StepTrace M middle target) :
    totalCrossingCount (append first second) =
      totalCrossingCount first + totalCrossingCount second := by
  simp only [totalCrossingCount, crossingCount_append,
    Finset.sum_add_distrib]

theorem vertices_eq_source_cons (trace : LBA.StepTrace M source target) :
    ∃ tail, trace.vertices = source :: tail := by
  cases trace with
  | refl => exact ⟨[], rfl⟩
  | head h rest => exact ⟨rest.vertices, rfl⟩

theorem vertices_prefix_append (first : LBA.StepTrace M source middle)
    (second : LBA.StepTrace M middle target) :
    first.vertices <+: (append first second).vertices := by
  induction first with
  | refl cfg =>
      obtain ⟨tail, hvertices⟩ := second.vertices_eq_source_cons
      exact ⟨tail, by simpa [append] using hvertices.symm⟩
  | head h rest ih =>
      obtain ⟨tail, hprefix⟩ := ih second
      exact ⟨tail, by simpa [vertices, append] using congrArg (List.cons source) hprefix⟩

theorem vertices_suffix_append (first : LBA.StepTrace M source middle)
    (second : LBA.StepTrace M middle target) :
    second.vertices <:+ (append first second).vertices := by
  induction first with
  | refl cfg => exact ⟨[], rfl⟩
  | @head source next middle h rest ih =>
      obtain ⟨pre, hsuffix⟩ := ih second
      exact ⟨source :: pre, by
        simpa [vertices, append] using
          (congrArg (List.cons source) hsuffix)⟩

/-! ## Quantitative loop erasure -/

noncomputable local instance configurationDecidableEq :
    DecidableEq (DLBA.Cfg Γ Λ n) := Classical.decEq _

/-- Retain the suffix of a trace beginning at an occurrence of `cfg`.

This is an internal operation used by `eraseLoops`. -/
noncomputable def suffixFromMem :
    {source target cfg : DLBA.Cfg Γ Λ n} →
    (trace : LBA.StepTrace M source target) →
    cfg ∈ trace.vertices → LBA.StepTrace M cfg target
  | _, _, cfg, .refl base, hmem => by
      have heq : cfg = base := by
        simpa only [vertices_refl, List.mem_singleton] using hmem
      subst cfg
      exact .refl base
  | source, _, cfg, .head (next := next) hstep rest, hmem => by
      by_cases heq : cfg = source
      · subst cfg
        exact .head hstep rest
      · exact suffixFromMem rest (by
          simpa only [vertices_head, List.mem_cons, heq, false_or] using hmem)

private theorem vertices_suffix_suffixFromMem
    (trace : LBA.StepTrace M source target)
    {cfg : DLBA.Cfg Γ Λ n} (hmem : cfg ∈ trace.vertices) :
    (suffixFromMem trace hmem).vertices <:+ trace.vertices := by
  induction trace with
  | refl base =>
      have heq : cfg = base := by
        simpa only [vertices_refl, List.mem_singleton] using hmem
      subst cfg
      simpa only [suffixFromMem] using
        (List.suffix_refl
          (vertices (.refl base : LBA.StepTrace M base base)))
  | @head source next target hstep rest ih =>
      by_cases heq : cfg = source
      · subst cfg
        simpa only [suffixFromMem, dite_true] using
          (List.suffix_refl
            (vertices (.head hstep rest : LBA.StepTrace M source target)))
      · have hmemRest : cfg ∈ rest.vertices := by
          simpa only [vertices_head, List.mem_cons, heq, false_or] using hmem
        have hsuffix := ih hmemRest
        simpa only [suffixFromMem, heq, dite_false, vertices_head] using
          hsuffix.trans (List.suffix_cons source rest.vertices)

private theorem crossingCount_suffixFromMem_le
    (trace : LBA.StepTrace M source target)
    {cfg : DLBA.Cfg Γ Λ n} (hmem : cfg ∈ trace.vertices)
    (b : Fin n) :
    (suffixFromMem trace hmem).crossingCount b ≤ trace.crossingCount b := by
  induction trace with
  | refl base =>
      have heq : cfg = base := by
        simpa only [vertices_refl, List.mem_singleton] using hmem
      subst cfg
      exact Nat.le_refl 0
  | @head source next target hstep rest ih =>
      by_cases heq : cfg = source
      · subst cfg
        simp only [suffixFromMem, dite_true]
        exact Nat.le_refl _
      · have hmemRest : cfg ∈ rest.vertices := by
          simpa only [vertices_head, List.mem_cons, heq, false_or] using hmem
        have hle := ih hmemRest
        simp only [suffixFromMem, heq, dite_false, crossingCount]
        omega

private theorem length_suffixFromMem_le
    (trace : LBA.StepTrace M source target)
    {cfg : DLBA.Cfg Γ Λ n} (hmem : cfg ∈ trace.vertices) :
    (suffixFromMem trace hmem).length ≤ trace.length := by
  induction trace with
  | refl base =>
      have heq : cfg = base := by
        simpa only [vertices_refl, List.mem_singleton] using hmem
      subst cfg
      exact Nat.le_refl 0
  | @head source next target hstep rest ih =>
      by_cases heq : cfg = source
      · subst cfg
        simp only [suffixFromMem, dite_true]
        exact Nat.le_refl _
      · have hmemRest : cfg ∈ rest.vertices := by
          simpa only [vertices_head, List.mem_cons, heq, false_or] using hmem
        have hle := ih hmemRest
        simp only [suffixFromMem, heq, dite_false, length]
        omega

/-- Delete configuration cycles from a concrete trace while retaining its endpoints.

When the source of a step already occurs in the recursively shortened suffix, the entire
intervening closed walk is discarded.  The construction is classical only because equality of
arbitrary configurations is selected noncomputably. -/
noncomputable def eraseLoops : {source target : DLBA.Cfg Γ Λ n} →
    LBA.StepTrace M source target → LBA.StepTrace M source target
  | _, _, .refl cfg => .refl cfg
  | source, _, .head hstep rest =>
      let erased := eraseLoops rest
      if hmem : source ∈ erased.vertices then
        suffixFromMem erased hmem
      else
        .head hstep erased

/-- Loop erasure produces a trace with no repeated configuration. -/
theorem eraseLoops_simple (trace : LBA.StepTrace M source target) :
    (eraseLoops trace).Simple := by
  induction trace with
  | refl cfg => simp [eraseLoops, Simple]
  | @head source next target hstep rest ih =>
      simp only [eraseLoops]
      split
      · next hmem =>
        exact (vertices_suffix_suffixFromMem (eraseLoops rest) hmem).nodup ih
      · next hmem =>
        rw [Simple] at ih ⊢
        simpa only [vertices_head, List.nodup_cons] using And.intro hmem ih

/-- Deleting loops cannot increase the number of crossings of any fixed boundary. -/
theorem crossingCount_eraseLoops_le (trace : LBA.StepTrace M source target)
    (b : Fin n) :
    (eraseLoops trace).crossingCount b ≤ trace.crossingCount b := by
  induction trace with
  | refl cfg => exact Nat.le_refl 0
  | @head source next target hstep rest ih =>
      simp only [eraseLoops]
      split
      · next hmem =>
        have hsuffix := crossingCount_suffixFromMem_le
          (eraseLoops rest) hmem b
        simp only [crossingCount]
        omega
      · next hmem =>
        simp only [crossingCount]
        omega

/-- Deleting loops cannot increase trace length. -/
theorem length_eraseLoops_le (trace : LBA.StepTrace M source target) :
    (eraseLoops trace).length ≤ trace.length := by
  induction trace with
  | refl cfg => exact Nat.le_refl 0
  | @head source next target hstep rest ih =>
      simp only [eraseLoops]
      split
      · next hmem =>
        have hsuffix := length_suffixFromMem_le (eraseLoops rest) hmem
        simp only [length]
        omega
      · next hmem =>
        simp only [length]
        omega

/-- Every concrete run has a simple subrun with the same endpoints, no greater length, and no
greater crossing count at any boundary. -/
theorem exists_simple_crossingCount_le
    (trace : LBA.StepTrace M source target) :
    ∃ shortened : LBA.StepTrace M source target,
      shortened.Simple ∧
        shortened.length ≤ trace.length ∧
        ∀ b : Fin n,
          shortened.crossingCount b ≤ trace.crossingCount b := by
  exact ⟨eraseLoops trace, eraseLoops_simple trace,
    length_eraseLoops_le trace, crossingCount_eraseLoops_le trace⟩

/-! ## The unrestricted finite-configuration bound -/

/-- A simple trace visits at most every configuration once.

This is the configuration-space counterpart of the finer crossing bounds below.  It makes no
assumption about head movement and remains valid for a one-cell tape (`n = 0`) and for empty
finite symbol or state types. -/
theorem length_add_one_le_card_cfg
    [Fintype Γ] [Fintype Λ]
    (trace : LBA.StepTrace M source target) (hsimple : trace.Simple) :
    trace.length + 1 ≤ Fintype.card (DLBA.Cfg Γ Λ n) := by
  rw [← vertices_length]
  exact hsimple.length_le_card

/-- The unrestricted simple-trace bound with the configuration cardinality expanded into its
state, tape-content, and head-position factors. -/
theorem length_add_one_le_card_mul_pow_mul
    [Fintype Γ] [Fintype Λ]
    (trace : LBA.StepTrace M source target) (hsimple : trace.Simple) :
    trace.length + 1 ≤
      Fintype.card Λ * Fintype.card Γ ^ (n + 1) * (n + 1) := by
  simpa only [DLBA.card_cfg] using length_add_one_le_card_cfg trace hsimple

/-- Every concrete run has a same-endpoint simple subrun whose number of visited configurations
is at most the full finite configuration-space cardinality.

The shortened run is no longer than the original one.  No crossing, acyclicity, or determinism
hypothesis is needed. -/
theorem exists_simple_length_add_one_le_card_cfg
    [Fintype Γ] [Fintype Λ]
    (trace : LBA.StepTrace M source target) :
    ∃ shortened : LBA.StepTrace M source target,
      shortened.Simple ∧
        shortened.length ≤ trace.length ∧
        shortened.length + 1 ≤ Fintype.card (DLBA.Cfg Γ Λ n) := by
  obtain ⟨shortened, hsimple, hlength, _hcross⟩ :=
    exists_simple_crossingCount_le trace
  exact ⟨shortened, hsimple, hlength,
    length_add_one_le_card_cfg shortened hsimple⟩

/-- Every concrete run has a same-endpoint simple subrun satisfying the expanded finite
configuration-space bound. -/
theorem exists_simple_length_add_one_le_card_mul_pow_mul
    [Fintype Γ] [Fintype Λ]
    (trace : LBA.StepTrace M source target) :
    ∃ shortened : LBA.StepTrace M source target,
      shortened.Simple ∧
        shortened.length ≤ trace.length ∧
        shortened.length + 1 ≤
          Fintype.card Λ * Fintype.card Γ ^ (n + 1) * (n + 1) := by
  obtain ⟨shortened, hsimple, hlength, _hbound⟩ :=
    exists_simple_length_add_one_le_card_cfg trace
  exact ⟨shortened, hsimple, hlength,
    length_add_one_le_card_mul_pow_mul shortened hsimple⟩

/-- Ordinary nondeterministic LBA acceptance has an accepting simple trace bounded by the full
finite configuration space. -/
theorem exists_simple_acceptingTrace_of_accepts
    [Fintype Γ] [Fintype Λ]
    (haccept : LBA.Accepts M source) :
    ∃ final : DLBA.Cfg Γ Λ n,
      ∃ trace : LBA.StepTrace M source final,
        M.accept final.state = true ∧
          trace.Simple ∧
          trace.length + 1 ≤ Fintype.card (DLBA.Cfg Γ Λ n) := by
  obtain ⟨final, hreach, hfinal⟩ := haccept
  obtain ⟨trace⟩ := nonempty_iff_reaches.mpr hreach
  obtain ⟨shortened, hsimple, _hlength, hbound⟩ :=
    exists_simple_length_add_one_le_card_cfg trace
  exact ⟨final, shortened, hfinal, hsimple, hbound⟩

/-- Ordinary nondeterministic LBA acceptance has an accepting simple trace with the full
configuration cardinality written explicitly. -/
theorem exists_simple_acceptingTrace_card_mul_pow_mul_of_accepts
    [Fintype Γ] [Fintype Λ]
    (haccept : LBA.Accepts M source) :
    ∃ final : DLBA.Cfg Γ Λ n,
      ∃ trace : LBA.StepTrace M source final,
        M.accept final.state = true ∧
          trace.Simple ∧
          trace.length + 1 ≤
            Fintype.card Λ * Fintype.card Γ ^ (n + 1) * (n + 1) := by
  obtain ⟨final, trace, hfinal, hsimple, _hbound⟩ :=
    exists_simple_acceptingTrace_of_accepts haccept
  exact ⟨final, trace, hfinal, hsimple,
    length_add_one_le_card_mul_pow_mul trace hsimple⟩

end LBA.StepTrace

namespace LBA.StepTrace

universe u v
variable {Γ : Type u} {Λ : Type v} {n : ℕ}
variable {M : LBA.Machine Γ Λ}

def Outside (h : Fin (n + 1)) := {i : Fin (n + 1) // i ≠ h} → Γ

def outside (h : Fin (n + 1)) (cfg : DLBA.Cfg Γ Λ n) : Outside (Γ := Γ) h :=
  fun i => cfg.tape.contents i.1

theorem outside_eq_of_step_of_head_eq
    {old new : DLBA.Cfg Γ Λ n} (hstep : LBA.Step M old new)
    (hhead : new.tape.head = old.tape.head) :
    outside old.tape.head new = outside old.tape.head old := by
  rcases hstep with ⟨state, written, direction, henabled, rfl⟩
  funext i
  simp only [outside]
  simp [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, i.2]

def localView (cfg : DLBA.Cfg Γ Λ n) : Λ × Γ :=
  (cfg.state, cfg.tape.read)

theorem eq_of_head_eq_of_outside_eq_of_localView_eq
    {left right : DLBA.Cfg Γ Λ n}
    (hhead : left.tape.head = right.tape.head)
    (hout : outside left.tape.head left = outside left.tape.head right)
    (hlocal : localView left = localView right) : left = right := by
  rcases left with ⟨leftState, ⟨leftContents, leftHead⟩⟩
  rcases right with ⟨rightState, ⟨rightContents, rightHead⟩⟩
  simp only [localView, DLBA.BoundedTape.read] at hlocal
  have hstate : leftState = rightState := congrArg Prod.fst hlocal
  have hread : leftContents leftHead = rightContents rightHead :=
    congrArg Prod.snd hlocal
  subst rightState
  simp only at hhead
  subst rightHead
  apply congrArg (fun tape => DLBA.Cfg.mk leftState tape)
  apply congrArg (fun contents => DLBA.BoundedTape.mk contents leftHead)
  funext i
  by_cases hi : i = leftHead
  · subst i
    exact hread
  · have := congrFun hout (⟨i, hi⟩ : {j : Fin (n + 1) // j ≠ leftHead})
    exact this

inductive StationaryTrace (M : LBA.Machine Γ Λ) :
    DLBA.Cfg Γ Λ n → DLBA.Cfg Γ Λ n → Type (max u v) where
  | refl (cfg : DLBA.Cfg Γ Λ n) : StationaryTrace M cfg cfg
  | head {source next target : DLBA.Cfg Γ Λ n}
      (hstep : LBA.Step M source next)
      (hhead : next.tape.head = source.tape.head)
      (rest : StationaryTrace M next target) : StationaryTrace M source target

namespace StationaryTrace

variable {source target : DLBA.Cfg Γ Λ n}

def configurations : {source target : DLBA.Cfg Γ Λ n} →
    StationaryTrace M source target → List (DLBA.Cfg Γ Λ n)
  | _, _, .refl cfg => [cfg]
  | source, _, .head _ _ rest => source :: configurations rest

def length : {source target : DLBA.Cfg Γ Λ n} →
    StationaryTrace M source target → ℕ
  | _, _, .refl _ => 0
  | _, _, .head _ _ rest => length rest + 1

def toStepTrace : {source target : DLBA.Cfg Γ Λ n} →
    StationaryTrace M source target → LBA.StepTrace M source target
  | _, _, .refl cfg => .refl cfg
  | _, _, .head hstep _ rest => .head hstep (toStepTrace rest)

@[simp] theorem configurations_toStepTrace
    (trace : StationaryTrace M source target) :
    trace.toStepTrace.vertices = trace.configurations := by
  induction trace with
  | refl => rfl
  | head hstep hhead rest ih => simp [toStepTrace, configurations, ih]

@[simp] theorem length_toStepTrace (trace : StationaryTrace M source target) :
    trace.toStepTrace.length = trace.length := by
  induction trace with
  | refl => rfl
  | head hstep hhead rest ih =>
      change rest.toStepTrace.length + 1 = rest.length + 1
      omega

@[simp] theorem totalCrossingCount_toStepTrace
    (trace : StationaryTrace M source target) :
    trace.toStepTrace.totalCrossingCount = 0 := by
  induction trace with
  | refl => simp [toStepTrace]
  | @head source next target hstep hhead rest ih =>
      rw [toStepTrace, LBA.StepTrace.totalCrossingCount_head]
      simp [hhead, ih]

@[simp] theorem configurations_length (trace : StationaryTrace M source target) :
    trace.configurations.length = trace.length + 1 := by
  induction trace with
  | refl => rfl
  | head hstep hhead rest ih => simp [configurations, length, ih]

theorem head_eq_source_of_mem (trace : StationaryTrace M source target)
    {cfg : DLBA.Cfg Γ Λ n} (hmem : cfg ∈ trace.configurations) :
    cfg.tape.head = source.tape.head := by
  induction trace with
  | refl base =>
      have hcfg : cfg = base := by simpa [configurations] using hmem
      subst cfg
      rfl
  | @head source next target hstep hhead rest ih =>
      simp only [configurations, List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · rfl
      · exact (ih hmem).trans hhead

theorem outside_eq_source_of_mem (trace : StationaryTrace M source target)
    {cfg : DLBA.Cfg Γ Λ n} (hmem : cfg ∈ trace.configurations) :
    outside source.tape.head cfg = outside source.tape.head source := by
  induction trace with
  | refl base =>
      have hcfg : cfg = base := by simpa [configurations] using hmem
      subst cfg
      rfl
  | @head source next target hstep hhead rest ih =>
      simp only [configurations, List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · rfl
      · have hcfgNext := rest.head_eq_source_of_mem hmem
        have houtRest := ih hmem
        have houtStep := outside_eq_of_step_of_head_eq hstep hhead
        rw [hhead] at houtRest
        exact houtRest.trans houtStep

theorem eq_of_mem_of_localView_eq (trace : StationaryTrace M source target)
    {left right : DLBA.Cfg Γ Λ n}
    (hleft : left ∈ trace.configurations)
    (hright : right ∈ trace.configurations)
    (hlocal : localView left = localView right) : left = right := by
  apply eq_of_head_eq_of_outside_eq_of_localView_eq
  · exact (trace.head_eq_source_of_mem hleft).trans
      (trace.head_eq_source_of_mem hright).symm
  · have houtLeft := trace.outside_eq_source_of_mem hleft
    have houtRight := trace.outside_eq_source_of_mem hright
    have hhead := trace.head_eq_source_of_mem hleft
    rw [hhead]
    exact houtLeft.trans houtRight.symm
  · exact hlocal

theorem configurations_length_le_card_localView
    [Fintype Γ] [Fintype Λ]
    (trace : StationaryTrace M source target)
    (hsimple : trace.configurations.Nodup) :
    trace.configurations.length ≤ Fintype.card Λ * Fintype.card Γ := by
  let views := trace.configurations.map localView
  have hnodup : views.Nodup := by
    apply hsimple.map_on
    intro left hleft right hright heq
    exact trace.eq_of_mem_of_localView_eq hleft hright heq
  have hcard := hnodup.length_le_card
  simpa [views, Fintype.card_prod] using hcard

end StationaryTrace

inductive HeadMovementTrace (M : LBA.Machine Γ Λ) :
    DLBA.Cfg Γ Λ n → DLBA.Cfg Γ Λ n → Type (max u v) where
  | finish {source target : DLBA.Cfg Γ Λ n}
      (stationary : StationaryTrace M source target) :
      HeadMovementTrace M source target
  | move {source junction next target : DLBA.Cfg Γ Λ n}
      (stationary : StationaryTrace M source junction)
      (hstep : LBA.Step M junction next)
      (hmove : next.tape.head ≠ junction.tape.head)
      (rest : HeadMovementTrace M next target) :
      HeadMovementTrace M source target

namespace HeadMovementTrace

variable {source target : DLBA.Cfg Γ Λ n}

def toStepTrace : {source target : DLBA.Cfg Γ Λ n} →
    HeadMovementTrace M source target → LBA.StepTrace M source target
  | _, _, .finish stationary => stationary.toStepTrace
  | _, _, .move stationary hstep _ rest =>
      LBA.StepTrace.append stationary.toStepTrace
        (.head hstep rest.toStepTrace)

def movementCount : {source target : DLBA.Cfg Γ Λ n} →
    HeadMovementTrace M source target → ℕ
  | _, _, .finish _ => 0
  | _, _, .move _ _ _ rest => rest.movementCount + 1

def prependStationary {source next target : DLBA.Cfg Γ Λ n}
    (hstep : LBA.Step M source next)
    (hhead : next.tape.head = source.tape.head) :
    HeadMovementTrace M next target → HeadMovementTrace M source target
  | .finish stationary => .finish (.head hstep hhead stationary)
  | .move stationary moveStep hmove rest =>
      .move (.head hstep hhead stationary) moveStep hmove rest

def ofStepTrace : {source target : DLBA.Cfg Γ Λ n} →
    LBA.StepTrace M source target → HeadMovementTrace M source target
  | _, _, .refl cfg => .finish (.refl cfg)
  | source, _, .head (next := next) hstep rest =>
      if hhead : next.tape.head = source.tape.head then
        prependStationary hstep hhead (ofStepTrace rest)
      else .move (.refl _) hstep hhead (ofStepTrace rest)

@[simp] theorem toStepTrace_prependStationary
    {source next target : DLBA.Cfg Γ Λ n}
    (hstep : LBA.Step M source next)
    (hhead : next.tape.head = source.tape.head)
    (trace : HeadMovementTrace M next target) :
    (prependStationary hstep hhead trace).toStepTrace =
      .head hstep trace.toStepTrace := by
  cases trace <;> rfl

@[simp] theorem movementCount_prependStationary
    {source next target : DLBA.Cfg Γ Λ n}
    (hstep : LBA.Step M source next)
    (hhead : next.tape.head = source.tape.head)
    (trace : HeadMovementTrace M next target) :
    (prependStationary hstep hhead trace).movementCount =
      trace.movementCount := by
  cases trace <;> rfl

@[simp] theorem toStepTrace_ofStepTrace
    (trace : LBA.StepTrace M source target) :
    (ofStepTrace trace).toStepTrace = trace := by
  induction trace with
  | refl => rfl
  | @head source next target hstep rest ih =>
      simp only [ofStepTrace]
      split
      · simp [ih]
      · simp [toStepTrace, StationaryTrace.toStepTrace,
          LBA.StepTrace.append, ih]

@[simp] theorem totalCrossingCount_toStepTrace
    (trace : HeadMovementTrace M source target) :
    trace.toStepTrace.totalCrossingCount = trace.movementCount := by
  induction trace with
  | finish stationary =>
      simp [toStepTrace, movementCount]
  | @move source junction next target stationary hstep hmove rest ih =>
      simp only [toStepTrace, movementCount,
        LBA.StepTrace.totalCrossingCount_append,
        StationaryTrace.totalCrossingCount_toStepTrace,
        zero_add, LBA.StepTrace.totalCrossingCount_head]
      rw [if_neg hmove, ih]
      omega

@[simp] theorem movementCount_ofStepTrace
    (trace : LBA.StepTrace M source target) :
    (ofStepTrace trace).movementCount = trace.totalCrossingCount := by
  rw [← totalCrossingCount_toStepTrace, toStepTrace_ofStepTrace]

/-- A simple trace has at most `card Λ * card Γ` configurations between two
successive physical head movements.  Summing those blocks gives the global bound. -/
theorem length_add_one_le_card_mul_movementCount_add_one
    [Fintype Γ] [Fintype Λ]
    (trace : HeadMovementTrace M source target)
    (hsimple : trace.toStepTrace.Simple) :
    trace.toStepTrace.length + 1 ≤
      (Fintype.card Λ * Fintype.card Γ) * (trace.movementCount + 1) := by
  induction trace with
  | finish stationary =>
      have hconfig : stationary.configurations.Nodup := by
        simpa [toStepTrace, LBA.StepTrace.Simple] using hsimple
      have hcard := stationary.configurations_length_le_card_localView hconfig
      simpa [toStepTrace, movementCount] using hcard
  | @move source junction next target stationary hstep hmove rest ih =>
      change
        (LBA.StepTrace.append stationary.toStepTrace
          (.head hstep rest.toStepTrace)).vertices.Nodup at hsimple
      have hstationaryVertices : stationary.toStepTrace.vertices.Nodup := by
        exact hsimple.sublist
          (LBA.StepTrace.vertices_prefix_append stationary.toStepTrace
            (.head hstep rest.toStepTrace)).sublist
      have hstationary : stationary.configurations.Nodup := by
        simpa using hstationaryVertices
      have hstationaryCard :=
        stationary.configurations_length_le_card_localView hstationary
      have hstationaryLength :
          stationary.length + 1 ≤ Fintype.card Λ * Fintype.card Γ := by
        simpa using hstationaryCard
      have hrestToSecond :
          rest.toStepTrace.vertices <:+
            (LBA.StepTrace.head hstep rest.toStepTrace).vertices := by
        exact ⟨[junction], rfl⟩
      have hsecondToFull :
          (LBA.StepTrace.head hstep rest.toStepTrace).vertices <:+
            (LBA.StepTrace.append stationary.toStepTrace
              (LBA.StepTrace.head hstep rest.toStepTrace)).vertices :=
        LBA.StepTrace.vertices_suffix_append stationary.toStepTrace
          (LBA.StepTrace.head hstep rest.toStepTrace)
      have hrestSimple : rest.toStepTrace.Simple := by
        exact hsimple.sublist
          ((hrestToSecond.trans hsecondToFull).sublist)
      have hrestLength := ih hrestSimple
      calc
        (LBA.StepTrace.append stationary.toStepTrace
              (.head hstep rest.toStepTrace)).length + 1 =
            (stationary.length + 1) + (rest.toStepTrace.length + 1) := by
          simp only [LBA.StepTrace.length_append,
            StationaryTrace.length_toStepTrace, LBA.StepTrace.length]
          omega
        _ ≤ (Fintype.card Λ * Fintype.card Γ) +
              (Fintype.card Λ * Fintype.card Γ) *
                (rest.movementCount + 1) :=
          Nat.add_le_add hstationaryLength hrestLength
        _ = (Fintype.card Λ * Fintype.card Γ) *
              ((HeadMovementTrace.move stationary hstep hmove rest).movementCount + 1) := by
          simp [movementCount, Nat.mul_add, Nat.add_comm]

end HeadMovementTrace

/-- The desired simple-trace estimate, stated directly using total boundary crossings.

It is valid also for a one-cell tape (`n = 0`): then there are no physical
boundaries, so simplicity bounds the entire run by the finite local view. -/
theorem length_add_one_le_card_mul_totalCrossingCount_add_one
    [Fintype Γ] [Fintype Λ]
    (trace : LBA.StepTrace M source target) (hsimple : trace.Simple) :
    trace.length + 1 ≤
      (Fintype.card Λ * Fintype.card Γ) *
        (trace.totalCrossingCount + 1) := by
  let decomposed := HeadMovementTrace.ofStepTrace trace
  have hdecomposedSimple : decomposed.toStepTrace.Simple := by
    simpa [decomposed] using hsimple
  have hbound :=
    HeadMovementTrace.length_add_one_le_card_mul_movementCount_add_one decomposed
      hdecomposedSimple
  simpa [decomposed] using hbound

/-- A uniform per-boundary crossing cap gives a bound using the tape width directly.

There are exactly `n` physical boundaries on a tape of `n + 1` cells.  Thus if every boundary
is crossed at most `c` times, the total crossing count is at most `n * c`. -/
theorem length_add_one_le_card_mul_boundaryCap_add_one
    [Fintype Γ] [Fintype Λ]
    (trace : LBA.StepTrace M source target) (hsimple : trace.Simple) (c : ℕ)
    (hcross : ∀ b : Fin n, crossingCount b trace ≤ c) :
    trace.length + 1 ≤
      (Fintype.card Λ * Fintype.card Γ) * (n * c + 1) := by
  have htotal : trace.totalCrossingCount ≤ n * c := by
    calc
      trace.totalCrossingCount = ∑ b : Fin n, crossingCount b trace := rfl
      _ ≤ ∑ _b : Fin n, c := Finset.sum_le_sum fun b _ ↦ hcross b
      _ = n * c := by simp
  calc
    trace.length + 1 ≤
        (Fintype.card Λ * Fintype.card Γ) *
          (trace.totalCrossingCount + 1) :=
      length_add_one_le_card_mul_totalCrossingCount_add_one trace hsimple
    _ ≤ (Fintype.card Λ * Fintype.card Γ) * (n * c + 1) := by
      exact Nat.mul_le_mul_left _ (Nat.add_le_add_right htotal 1)

/-- An arbitrary trace with a uniform boundary-crossing cap can be shortened, without changing
its endpoints, to a simple trace satisfying the sharp linear length estimate.

No simplicity or acyclicity promise is required of the original machine or run: loop erasure
removes repeated configurations and can only decrease each individual crossing count. -/
theorem exists_simple_length_add_one_le_card_mul_boundaryCap_add_one
    [Fintype Γ] [Fintype Λ]
    (trace : LBA.StepTrace M source target) (c : ℕ)
    (hcross : ∀ b : Fin n, crossingCount b trace ≤ c) :
    ∃ shortened : LBA.StepTrace M source target,
      shortened.Simple ∧
        shortened.length ≤ trace.length ∧
        (∀ b : Fin n,
          shortened.crossingCount b ≤ trace.crossingCount b) ∧
        shortened.length + 1 ≤
          (Fintype.card Λ * Fintype.card Γ) * (n * c + 1) := by
  obtain ⟨shortened, hsimple, hlength, hshortCross⟩ :=
    exists_simple_crossingCount_le trace
  have hcap : ∀ b : Fin n, shortened.crossingCount b ≤ c :=
    fun b ↦ (hshortCross b).trans (hcross b)
  exact ⟨shortened, hsimple, hlength, hshortCross,
    length_add_one_le_card_mul_boundaryCap_add_one
      shortened hsimple c hcap⟩

end LBA.StepTrace

end
