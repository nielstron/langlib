module

public import Langlib.Automata.LinearBounded.BoundedDegree
import Mathlib.Tactic

@[expose]
public section

/-!
# Acyclicity of the degree-two serializers

The outgoing and incoming serializers used by `Machine.boundedDegree` do not introduce
configuration cycles.  This is a global statement, over every configuration at every tape
width, rather than merely an invariant about runs from a canonical input.

For a finite acyclic configuration graph, the number of ancestors of a configuration is a
strictly increasing rank along every genuine machine step.  Each serializer also has a finite
phase rank:

* the binary outgoing scan advances from `ready` through strictly shrinking `remaining` sets;
* the incoming serializer advances from `arrived`, through its merge chain, to `base` and
  `written`.

The only edge that resets either phase is an edge that performs a genuine source-machine step.
Lexicographically combining the ancestor rank with the phase rank proves that every serialized
step strictly increases a natural-valued potential.  In particular, the compiler gadgets have
no hidden microcycles.
-/

namespace LBA

open Classical Relation

variable {Γ Λ : Type*}

/-- Every configuration graph of `M`, at every bounded tape width, is acyclic. -/
public def Machine.ConfigurationAcyclic (M : Machine Γ Λ) : Prop :=
  ∀ (n : ℕ) (cfg : DLBA.Cfg Γ Λ n), ¬ TransGen (Step M) cfg cfg

namespace AcyclicBoundedDegree

/-- Configurations that can reach `cfg`, including `cfg` itself. -/
private noncomputable def ancestors
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) {n : ℕ} (cfg : DLBA.Cfg Γ Λ n) :
    Finset (DLBA.Cfg Γ Λ n) :=
  Finset.univ.filter fun source => Reaches M source cfg

/-- The finite ancestor-count rank of a bounded configuration. -/
private noncomputable def configurationRank
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) {n : ℕ} (cfg : DLBA.Cfg Γ Λ n) : ℕ :=
  (ancestors M cfg).card

private theorem mem_ancestors_iff
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) {n : ℕ} {source target : DLBA.Cfg Γ Λ n} :
    source ∈ ancestors M target ↔ Reaches M source target := by
  simp [ancestors]

private theorem not_reaches_back_of_step
    (M : Machine Γ Λ) (hacyclic : M.ConfigurationAcyclic)
    {n : ℕ} {source target : DLBA.Cfg Γ Λ n}
    (hstep : Step M source target) :
    ¬ Reaches M target source := by
  intro hback
  rcases reflTransGen_iff_eq_or_transGen.mp hback with heq | hpath
  · subst target
    exact hacyclic n source (TransGen.single hstep)
  · exact hacyclic n target (hpath.tail hstep)

/-- Ancestor count strictly increases on every edge of a finite acyclic configuration graph. -/
private theorem configurationRank_lt_of_step
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) (hacyclic : M.ConfigurationAcyclic)
    {n : ℕ} {source target : DLBA.Cfg Γ Λ n}
    (hstep : Step M source target) :
    configurationRank M source < configurationRank M target := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro cfg hcfg
    rw [mem_ancestors_iff] at hcfg ⊢
    exact hcfg.tail hstep
  · intro heq
    have htarget : target ∈ ancestors M target := by
      rw [mem_ancestors_iff]
      exact .refl
    have hnot : target ∉ ancestors M source := by
      rw [mem_ancestors_iff]
      exact not_reaches_back_of_step M hacyclic hstep
    exact hnot (by simpa [heq] using htarget)

/-- Any natural-valued potential that strictly increases on each edge rules out cycles. -/
private theorem acyclic_of_potential
    {V : Type*} (edge : V → V → Prop) (potential : V → ℕ)
    (hstep : ∀ {old new}, edge old new → potential old < potential new) :
    ∀ vertex, ¬ TransGen edge vertex vertex := by
  have hpath : ∀ {old new}, TransGen edge old new →
      potential old < potential new := by
    intro old new path
    induction path with
    | single hedge =>
        exact hstep hedge
    | tail hpath hedge ih =>
        exact ih.trans (hstep hedge)
  intro vertex hcycle
  exact (Nat.lt_irrefl _) (hpath hcycle)

/-- A lower major rank dominates an arbitrary phase reset when phases stay below the stride. -/
private theorem lexPotential_lt
    {major major' phase phase' stride : ℕ}
    (hmajor : major < major') (hphase : phase < stride) :
    major * stride + phase < major' * stride + phase' := by
  calc
    major * stride + phase < major * stride + stride :=
      Nat.add_lt_add_left hphase _
    _ = (major + 1) * stride := by simp [Nat.add_mul]
    _ ≤ major' * stride :=
      Nat.mul_le_mul_right stride (Nat.succ_le_iff.mpr hmajor)
    _ ≤ major' * stride + phase' := Nat.le_add_right _ _

private theorem write_read_stay {n : ℕ} (tape : DLBA.BoundedTape Γ n) :
    (tape.write tape.read).moveHead .stay = tape := by
  cases tape
  simp [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead,
    Function.update_eq_self]

/-! ## The binary outgoing serializer -/

private noncomputable def binaryPhase
    [Fintype Γ] [Fintype Λ]
    (state : BinaryBranchState Γ Λ) : ℕ :=
  match state with
  | .ready _ => 0
  | .scan _ _ remaining =>
      Fintype.card (Move Γ Λ) - remaining.card + 1

private theorem binaryPhase_lt_stride
    [Fintype Γ] [Fintype Λ]
    (state : BinaryBranchState Γ Λ) :
    binaryPhase state < Fintype.card (Move Γ Λ) + 2 := by
  cases state with
  | ready q =>
      simp [binaryPhase]
  | scan q expected remaining =>
      have hcard : remaining.card ≤ Fintype.card (Move Γ Λ) :=
        Finset.card_le_univ _
      simp only [binaryPhase]
      omega

private noncomputable def binaryPotential
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) {n : ℕ}
    (cfg : DLBA.Cfg Γ (BinaryBranchState Γ Λ) n) : ℕ :=
  configurationRank M (binaryProjectCfg cfg) *
      (Fintype.card (Move Γ Λ) + 2) +
    binaryPhase cfg.state

private theorem pickMove_mem
    [DecidableEq Γ] [DecidableEq Λ]
    {remaining : Finset (Move Γ Λ)} {move : Move Γ Λ}
    (hpick : pickMove remaining = some move) :
    move ∈ remaining := by
  rw [pickMove, List.head?_eq_some_iff] at hpick
  obtain ⟨tail, hlist⟩ := hpick
  rw [← Finset.mem_toList, hlist]
  simp

private theorem mem_binary_ready_iff
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) (q : Λ) (symbol : Γ)
    (out : BinaryBranchState Γ Λ × Γ × DLBA.Dir) :
    out ∈ M.binaryBranch.transition (.ready q) symbol ↔
      out = (.scan q symbol Finset.univ, symbol, .stay) := by
  simp [Machine.binaryBranch]

private theorem mem_binary_scan_iff
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) (q : Λ) (expected symbol : Γ)
    (remaining : Finset (Move Γ Λ))
    (out : BinaryBranchState Γ Λ × Γ × DLBA.Dir) :
    out ∈ M.binaryBranch.transition (.scan q expected remaining) symbol ↔
      symbol = expected ∧
        ∃ move, pickMove remaining = some move ∧
          (out =
              (.scan q expected (remaining.erase move), symbol, .stay) ∨
            (move ∈ M.transition q expected ∧
              out = (.ready move.1, move.2.1, move.2.2))) := by
  by_cases hsymbol : symbol = expected
  · subst expected
    cases hpick : pickMove remaining with
    | none =>
        simp [Machine.binaryBranch, hpick]
    | some move =>
        by_cases henabled : move ∈ M.transition q symbol
        · simp [Machine.binaryBranch, hpick, henabled]
        · simp [Machine.binaryBranch, hpick, henabled]
  · simp [Machine.binaryBranch, hsymbol]

private theorem binaryPotential_lt_of_step
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) (hacyclic : M.ConfigurationAcyclic)
    {n : ℕ}
    {cfg cfg' : DLBA.Cfg Γ (BinaryBranchState Γ Λ) n}
    (hstep : Step M.binaryBranch cfg cfg') :
    binaryPotential M cfg < binaryPotential M cfg' := by
  rcases cfg with ⟨state, tape⟩
  rcases hstep with ⟨next, written, direction, hmem, rfl⟩
  cases state with
  | ready q =>
      have hout :=
        (mem_binary_ready_iff M q tape.read (next, written, direction)).1 hmem
      simp only [Prod.mk.injEq] at hout
      rcases hout with ⟨rfl, rfl, rfl⟩
      have htape := write_read_stay tape
      simp only [binaryPotential, binaryProjectCfg, BinaryBranchState.original,
        binaryPhase, Finset.card_univ, Nat.sub_self]
      rw [htape]
      omega
  | scan q expected remaining =>
      obtain ⟨hsymbol, selected, hpick, hskip | ⟨henabled, happly⟩⟩ :=
        (mem_binary_scan_iff M q expected tape.read remaining
          (next, written, direction)).1 hmem
      · simp only [Prod.mk.injEq] at hskip
        rcases hskip with ⟨rfl, rfl, rfl⟩
        have hselected : selected ∈ remaining := pickMove_mem hpick
        have hcard :
            (remaining.erase selected).card + 1 = remaining.card :=
          Finset.card_erase_add_one hselected
        have htape := write_read_stay tape
        simp only [binaryPotential, binaryProjectCfg, BinaryBranchState.original,
          binaryPhase]
        rw [htape]
        have hle : remaining.card ≤ Fintype.card (Move Γ Λ) :=
          Finset.card_le_univ _
        have hle' :
            (remaining.erase selected).card ≤ Fintype.card (Move Γ Λ) :=
          Finset.card_le_univ _
        omega
      · simp only [Prod.mk.injEq] at happly
        rcases happly with ⟨rfl, rfl, rfl⟩
        have horiginal :
            Step M
              (⟨q, tape⟩ : DLBA.Cfg Γ Λ n)
              ⟨selected.1,
                (tape.write selected.2.1).moveHead selected.2.2⟩ := by
          rw [← hsymbol] at henabled
          exact ⟨selected.1, selected.2.1, selected.2.2, henabled, rfl⟩
        have hrank := configurationRank_lt_of_step M hacyclic horiginal
        apply lexPotential_lt hrank
        exact binaryPhase_lt_stride (.scan q expected remaining)

/-- Binary outgoing serialization preserves global configuration-graph acyclicity. -/
public theorem configurationAcyclic_binaryBranch
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) (hacyclic : M.ConfigurationAcyclic) :
    M.binaryBranch.ConfigurationAcyclic := by
  intro n cfg
  exact acyclic_of_potential (Step M.binaryBranch) (binaryPotential M)
    (binaryPotential_lt_of_step M hacyclic) cfg

/-! ## The incoming-edge serializer -/

private theorem write_write_read {n : ℕ} (tape : DLBA.BoundedTape Γ n)
    (written : Γ) :
    (tape.write written).write tape.read = tape := by
  cases tape
  simp [DLBA.BoundedTape.write, Function.update_eq_self]

private theorem restore_then_write
    [DecidableEq Γ] {n : ℕ} (tape : DLBA.BoundedTape Γ n)
    (old written : Γ) (hread : tape.read = written) :
    (tape.write old).write written = tape := by
  subst written
  rw [write_write_read]

private noncomputable def incomingPhase
    [Fintype Γ] [Fintype Λ]
    (state : IncomingState Γ Λ) : ℕ :=
  match state with
  | .arrived _ _ => 0
  | .merge _ index => index.val + 1
  | .base _ => Fintype.card (IncomingTag Γ Λ) + 1
  | .written _ _ => Fintype.card (IncomingTag Γ Λ) + 2

private theorem incomingPhase_lt_stride
    [Fintype Γ] [Fintype Λ]
    (state : IncomingState Γ Λ) :
    incomingPhase state < Fintype.card (IncomingTag Γ Λ) + 3 := by
  cases state with
  | arrived target tag =>
      simp [incomingPhase]
  | merge target index =>
      have := index.isLt
      simp only [incomingPhase]
      omega
  | base q =>
      simp [incomingPhase]
  | written target tag =>
      simp [incomingPhase]

private noncomputable def incomingPotential
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) {n : ℕ}
    (cfg : DLBA.Cfg Γ (IncomingState Γ Λ) n) : ℕ :=
  configurationRank M (incomingProjectCfg cfg) *
      (Fintype.card (IncomingTag Γ Λ) + 3) +
    incomingPhase cfg.state

private theorem incomingPotential_lt_of_step
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) (hacyclic : M.ConfigurationAcyclic)
    {n : ℕ}
    {cfg cfg' : DLBA.Cfg Γ (IncomingState Γ Λ) n}
    (hstep : Step M.serializeIncoming cfg cfg') :
    incomingPotential M cfg < incomingPotential M cfg' := by
  rcases cfg with ⟨state, tape⟩
  rcases hstep with ⟨next, written, direction, hmem, rfl⟩
  cases state with
  | base q =>
      simp only [Machine.serializeIncoming] at hmem
      rcases hmem with ⟨move, henabled, hmove⟩
      simp only [Prod.mk.injEq] at hmove
      rcases hmove with ⟨rfl, rfl, rfl⟩
      have htape :
          (((tape.write move.2.1).moveHead .stay).write tape.read) = tape := by
        simpa only [DLBA.BoundedTape.moveHead] using
          write_write_read tape move.2.1
      simp only [incomingPotential, incomingProjectCfg, incomingPhase]
      rw [htape]
      omega
  | written target tag =>
      simp only [Machine.serializeIncoming] at hmem
      split at hmem
      · next henabled =>
          simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨rfl, rfl, rfl⟩
          have horiginal :
              Step M
                ⟨tag.source, tape.write tag.old⟩
                (⟨target,
                  (tape.write tape.read).moveHead tag.direction⟩ :
                  DLBA.Cfg Γ Λ n) := by
            refine ⟨target, tag.written, tag.direction, ?_, ?_⟩
            · simpa [DLBA.BoundedTape.write] using henabled.2
            · have hrestore :
                  (tape.write tag.old).write tag.written = tape :=
                restore_then_write tape tag.old tag.written henabled.1
              have hcopy : tape.write tape.read = tape := by
                simpa only [DLBA.BoundedTape.moveHead] using
                  write_read_stay tape
              rw [hrestore, hcopy]
          have hrank := configurationRank_lt_of_step M hacyclic horiginal
          apply lexPotential_lt hrank
          exact incomingPhase_lt_stride (.written target tag)
      · simp at hmem
  | arrived target tag =>
      simp only [Machine.serializeIncoming, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl, rfl⟩
      have htape := write_read_stay tape
      simp only [incomingPotential, incomingProjectCfg, incomingPhase]
      rw [htape]
      have hindex :
          (incomingIndex tag).val <
            Fintype.card (IncomingTag Γ Λ) :=
        (incomingIndex tag).isLt
      omega
  | merge target index =>
      simp only [Machine.serializeIncoming] at hmem
      split at hmem
      · next hnext =>
          simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨rfl, rfl, rfl⟩
          have htape := write_read_stay tape
          simp only [incomingPotential, incomingProjectCfg, incomingPhase]
          rw [htape]
          omega
      · next hlast =>
          simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨rfl, rfl, rfl⟩
          have htape := write_read_stay tape
          simp only [incomingPotential, incomingProjectCfg, incomingPhase]
          rw [htape]
          have hindex := index.isLt
          omega

/-- Incoming-edge serialization preserves global configuration-graph acyclicity. -/
public theorem configurationAcyclic_serializeIncoming
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) (hacyclic : M.ConfigurationAcyclic) :
    M.serializeIncoming.ConfigurationAcyclic := by
  intro n cfg
  exact acyclic_of_potential (Step M.serializeIncoming) (incomingPotential M)
    (incomingPotential_lt_of_step M hacyclic) cfg

/-- Simultaneous incoming/outgoing degree reduction preserves global acyclicity. -/
public theorem configurationAcyclic_boundedDegree
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) (hacyclic : M.ConfigurationAcyclic) :
    M.boundedDegree.ConfigurationAcyclic :=
  configurationAcyclic_serializeIncoming M.binaryBranch
    (configurationAcyclic_binaryBranch M hacyclic)

/-- On an acyclic source machine, `boundedDegree` has globally acyclic configuration graphs and
both directed configuration degrees at most two, uniformly over every tape width. -/
public theorem boundedDegree_acyclic_and_degreeAtMostTwo
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) (hacyclic : M.ConfigurationAcyclic) :
    M.boundedDegree.ConfigurationAcyclic ∧
      M.boundedDegree.ConfigurationDegreeAtMostTwo :=
  ⟨configurationAcyclic_boundedDegree M hacyclic,
    M.boundedDegree_configurationDegreeAtMostTwo⟩

end AcyclicBoundedDegree

end LBA

/-- Languages having a canonical endmarker LBA presentation whose entire configuration graph is
acyclic at every tape width. -/
public def is_AcyclicLBA
    {T : Type} [Fintype T] [DecidableEq T] (L : Language T) : Prop :=
  ∃ (Γ Λ : Type) (_ : Fintype Γ) (_ : Fintype Λ)
    (_ : DecidableEq Γ) (_ : DecidableEq Λ)
    (M : LBA.Machine (LBA.EndAlpha T Γ) Λ),
    M.ConfigurationAcyclic ∧ LBA.LanguageEnd M = L

/-- Languages having a globally acyclic canonical endmarker LBA presentation whose configuration
indegree and outdegree are both at most two at every tape width. -/
public def is_AcyclicBoundedDegreeLBA
    {T : Type} [Fintype T] [DecidableEq T] (L : Language T) : Prop :=
  ∃ (Γ Λ : Type) (_ : Fintype Γ) (_ : Fintype Λ)
    (_ : DecidableEq Γ) (_ : DecidableEq Λ)
    (M : LBA.Machine (LBA.EndAlpha T Γ) Λ),
    M.ConfigurationAcyclic ∧
      M.ConfigurationDegreeAtMostTwo ∧
      LBA.LanguageEnd M = L

/-- Forgetting the global acyclicity witness gives an ordinary LBA presentation. -/
public theorem is_LBA_of_is_AcyclicLBA
    {T : Type} [Fintype T] [DecidableEq T] {L : Language T}
    (hL : is_AcyclicLBA L) :
    is_LBA L := by
  rcases hL with
    ⟨Γ, Λ, hΓ, hΛ, hdecΓ, hdecΛ, M, _hacyclic, hM⟩
  exact ⟨Γ, Λ, hΓ, hΛ, hdecΓ, hdecΛ, M, hM⟩

/-- A globally acyclic degree-two presentation is in particular an ordinary LBA presentation. -/
public theorem is_LBA_of_is_AcyclicBoundedDegreeLBA
    {T : Type} [Fintype T] [DecidableEq T] {L : Language T}
    (hL : is_AcyclicBoundedDegreeLBA L) :
    is_LBA L := by
  rcases hL with
    ⟨Γ, Λ, hΓ, hΛ, hdecΓ, hdecΛ, M, _hacyclic, _hdegree, hM⟩
  exact ⟨Γ, Λ, hΓ, hΛ, hdecΓ, hdecΛ, M, hM⟩

/-- Once a language has a globally acyclic LBA presentation, simultaneously imposing
configuration indegree and outdegree at most two loses no expressive power. -/
public theorem is_AcyclicLBA_iff_is_AcyclicBoundedDegreeLBA
    {T : Type} [Fintype T] [DecidableEq T] (L : Language T) :
    is_AcyclicLBA L ↔ is_AcyclicBoundedDegreeLBA L := by
  constructor
  · rintro ⟨Γ, Λ, hΓ, hΛ, hdecΓ, hdecΛ, M, hacyclic, hM⟩
    letI := hΓ
    letI := hΛ
    letI := hdecΓ
    letI := hdecΛ
    refine ⟨Γ,
      LBA.IncomingState (LBA.EndAlpha T Γ)
        (LBA.BinaryBranchState (LBA.EndAlpha T Γ) Λ),
      hΓ, inferInstance, hdecΓ, inferInstance, M.boundedDegree,
      LBA.AcyclicBoundedDegree.configurationAcyclic_boundedDegree M hacyclic,
      M.boundedDegree_configurationDegreeAtMostTwo, ?_⟩
    exact M.languageEnd_boundedDegree_eq.trans hM
  · rintro ⟨Γ, Λ, hΓ, hΛ, hdecΓ, hdecΛ, M, hacyclic, _hdegree, hM⟩
    exact ⟨Γ, Λ, hΓ, hΛ, hdecΓ, hdecΛ, M, hacyclic, hM⟩

end
