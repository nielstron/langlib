import Mathlib.Computability.NFA
import Langlib.Classes.DeterministicContextFree.Totalization.EpsilonPhase

/-! # P-Automata for DPDA Epsilon Saturation

This file contains the finite automaton layer and saturation construction for
DPDA epsilon phases.  The saturated P-automaton relations recognize exactly the
stack prefixes whose epsilon phase can reach either a stable configuration or a
final control state.
-/

open PDA

namespace DPDA

variable {Q S : Type}

/-- States of a P-automaton: original control states plus one distinguished sink
state used by target automata for arbitrary stack suffixes. -/
abbrev PAutState (Q : Type) := Q ⊕ Unit

namespace PAutState

/-- Embed an original DPDA state as a P-automaton state. -/
def control (q : Q) : PAutState Q := Sum.inl q

/-- Distinguished target/sink state. -/
def sink : PAutState Q := Sum.inr ()

end PAutState

/-- A path through a stack-reading relation.  Symbols are read top-to-bottom. -/
inductive RelPath (R : PAutState Q → S → PAutState Q → Prop) :
    PAutState Q → List S → PAutState Q → Prop
  | nil (p) : RelPath R p [] p
  | cons {p m r Z γ} : R p Z m → RelPath R m γ r → RelPath R p (Z :: γ) r

namespace RelPath

theorem append {R : PAutState Q → S → PAutState Q → Prop}
    {p m r : PAutState Q} {γ δ : List S}
    (h₁ : RelPath R p γ m) (h₂ : RelPath R m δ r) :
    RelPath R p (γ ++ δ) r := by
  induction h₁ with
  | nil _ => simpa using h₂
  | cons hstep _ ih => exact RelPath.cons hstep (ih h₂)

theorem of_append_left {R : PAutState Q → S → PAutState Q → Prop}
    {p r : PAutState Q} {γ δ : List S}
    (h : RelPath R p (γ ++ δ) r) :
    ∃ m, RelPath R p γ m ∧ RelPath R m δ r := by
  induction γ generalizing p with
  | nil => exact ⟨p, RelPath.nil p, by simpa using h⟩
  | cons Z γ ih =>
      cases h with
      | cons hstep hrest =>
          obtain ⟨m, hγ, hδ⟩ := ih hrest
          exact ⟨m, RelPath.cons hstep hγ, hδ⟩

theorem mono {R₁ R₂ : PAutState Q → S → PAutState Q → Prop}
    (hsub : ∀ {p Z r}, R₁ p Z r → R₂ p Z r)
    {p r : PAutState Q} {γ : List S}
    (h : RelPath R₁ p γ r) :
    RelPath R₂ p γ r := by
  induction h with
  | nil p => exact RelPath.nil p
  | cons hstep _ ih => exact RelPath.cons (hsub hstep) ih

end RelPath

/-- The NFA whose transitions are exactly a stack-reading relation. -/
def relNFA (R : PAutState Q → S → PAutState Q → Prop)
    (start : PAutState Q) (accept : Set (PAutState Q)) :
    NFA S (PAutState Q) where
  step p Z := { r | R p Z r }
  start := {start}
  accept := accept

theorem relPath_iff_nonempty_nfa_path
    {R : PAutState Q → S → PAutState Q → Prop}
    {start accept} {p r : PAutState Q} {γ : List S} :
    RelPath R p γ r ↔ Nonempty ((relNFA R start accept).Path p r γ) := by
  constructor
  · intro h
    induction h with
    | nil p => exact ⟨NFA.Path.nil p⟩
    | cons hstep _ ih =>
        obtain ⟨path⟩ := ih
        exact ⟨NFA.Path.cons _ _ _ _ _ hstep path⟩
  · rintro ⟨path⟩
    induction path with
    | nil p => exact RelPath.nil p
    | cons m p r Z γ hstep _ ih =>
        exact RelPath.cons hstep ih

/-- The DFA obtained by subset construction from a stack-reading relation. -/
def relDFA (R : PAutState Q → S → PAutState Q → Prop)
    (start : PAutState Q) (accept : Set (PAutState Q)) :
    DFA S (Set (PAutState Q)) :=
  (relNFA R start accept).toDFA

/-- Correctness of the relation DFA: it accepts exactly the stacks labeling a path
from `start` to an accepting P-automaton state. -/
theorem relDFA_accepts_iff
    {R : PAutState Q → S → PAutState Q → Prop}
    {start : PAutState Q} {accept : Set (PAutState Q)} {γ : List S} :
    γ ∈ (relDFA R start accept).accepts ↔
      ∃ r, r ∈ accept ∧ RelPath R start γ r := by
  unfold relDFA
  rw [NFA.toDFA_correct]
  rw [NFA.accepts_iff_exists_path]
  constructor
  · rintro ⟨s, hs, r, hr, hpath⟩
    simp [relNFA] at hs
    subst s
    exact ⟨r, hr, (relPath_iff_nonempty_nfa_path (start := start) (accept := accept)).2 hpath⟩
  · rintro ⟨r, hr, hpath⟩
    exact
      ⟨start, by simp [relNFA], r, hr,
        (relPath_iff_nonempty_nfa_path (start := start) (accept := accept)).1 hpath⟩

/-- The relation recognized from an original control state by the relation DFA. -/
theorem relDFA_evalFrom_control_iff
    {R : PAutState Q → S → PAutState Q → Prop}
    {q : Q} {accept : Set (PAutState Q)} {γ : List S} :
    (relDFA R (PAutState.control q) accept).evalFrom
        (relDFA R (PAutState.control q) accept).start γ ∈
        (relDFA R (PAutState.control q) accept).accept ↔
      ∃ r, r ∈ accept ∧ RelPath R (PAutState.control q) γ r := by
  exact relDFA_accepts_iff

section Saturation

variable {T : Type} [Fintype Q] [Fintype T] [Fintype S]

/-- A relation is saturated for the epsilon rules of a DPDA if every pushdown
epsilon step can be summarized by a single stack-reading transition. -/
def EpsilonStepSaturated (M : DPDA Q T S)
    (R : PAutState Q → S → PAutState Q → Prop) : Prop :=
  ∀ {q p : Q} {Z : S} {β : List S} {r : PAutState Q},
    M.epsilon_transition q Z = some (p, β) →
    RelPath R (PAutState.control p) β r →
    R (PAutState.control q) Z r

/-- Least saturated relation containing a base P-automaton relation. -/
def epsilonSaturationRel (M : DPDA Q T S)
    (base : PAutState Q → S → PAutState Q → Prop) :
    PAutState Q → S → PAutState Q → Prop :=
  fun p Z r =>
    ∀ R : PAutState Q → S → PAutState Q → Prop,
      (∀ {p Z r}, base p Z r → R p Z r) →
      EpsilonStepSaturated M R →
      R p Z r

theorem base_subset_epsilonSaturationRel (M : DPDA Q T S)
    {base : PAutState Q → S → PAutState Q → Prop} :
    ∀ {p Z r}, base p Z r → epsilonSaturationRel M base p Z r := by
  intro p Z r hbase R hbase_subset _hsat
  exact hbase_subset hbase

theorem epsilonSaturationRel_saturated (M : DPDA Q T S)
    (base : PAutState Q → S → PAutState Q → Prop) :
    EpsilonStepSaturated M (epsilonSaturationRel M base) := by
  intro q p Z β r hε hpath R hbase hsat
  exact hsat hε (RelPath.mono (fun h => h R hbase hsat) hpath)

/-- Base target relation for stopping epsilon phases.  A control state with no
epsilon transition on the current top symbol is a target; the sink consumes the
unexamined suffix. -/
def stopTargetBase (M : DPDA Q T S) :
    PAutState Q → S → PAutState Q → Prop
  | .inl q, Z, .inr () => M.epsilon_transition q Z = none
  | .inr (), _, .inr () => True
  | _, _, _ => False

/-- Empty stack is stable for every control state; after detecting a stable top,
the sink accepts the remaining suffix. -/
def stopTargetAccept : Set (PAutState Q) :=
  Set.univ

/-- Saturated relation recognizing stacks from which the forced epsilon phase
reaches a stable configuration. -/
def stopSaturationRel (M : DPDA Q T S) :
    PAutState Q → S → PAutState Q → Prop :=
  epsilonSaturationRel M (stopTargetBase M)

/-- Base target relation for epsilon reachability to a final state. -/
def finalTargetBase (M : DPDA Q T S) :
    PAutState Q → S → PAutState Q → Prop
  | .inl q, _, .inr () => q ∈ M.final_states
  | .inr (), _, .inr () => True
  | _, _, _ => False

/-- Accepting P-automaton states for final-state epsilon reachability. -/
def finalTargetAccept (M : DPDA Q T S) : Set (PAutState Q)
  | .inl q => q ∈ M.final_states
  | .inr () => True

/-- Saturated relation recognizing stacks from which epsilon reachability can hit
an original final state. -/
def finalSaturationRel (M : DPDA Q T S) :
    PAutState Q → S → PAutState Q → Prop :=
  epsilonSaturationRel M (finalTargetBase M)

/-- Candidate DFA for the stop-lookahead language at control state `q`. -/
def stopSaturationDFA (M : DPDA Q T S) (q : Q) :
    DFA S (Set (PAutState Q)) :=
  relDFA (stopSaturationRel M) (PAutState.control q) stopTargetAccept

/-- Candidate DFA for the epsilon-final-reachability language at control state `q`. -/
def finalSaturationDFA (M : DPDA Q T S) (q : Q) :
    DFA S (Set (PAutState Q)) :=
  relDFA (finalSaturationRel M) (PAutState.control q) (finalTargetAccept M)

theorem stopSaturationDFA_accepts_iff (M : DPDA Q T S) (q : Q) (γ : List S) :
    γ ∈ (stopSaturationDFA M q).accepts ↔
      ∃ r, RelPath (stopSaturationRel M) (PAutState.control q) γ r := by
  unfold stopSaturationDFA
  rw [relDFA_accepts_iff]
  simp [stopTargetAccept]

/-- A relation preserves a target stack language if one transition consumes one
stack symbol while preserving target membership for every suffix. -/
def RelationPreservesTarget
    (R : PAutState Q → S → PAutState Q → Prop)
    (Target : PAutState Q → List S → Prop) : Prop :=
  ∀ {p r : PAutState Q} {Z : S}, R p Z r → ∀ δ, Target r δ → Target p (Z :: δ)

omit [Fintype Q] [Fintype S] in
theorem RelPath.preservesTarget
    {R : PAutState Q → S → PAutState Q → Prop}
    {Target : PAutState Q → List S → Prop}
    (hR : RelationPreservesTarget R Target)
    {p r : PAutState Q} {γ δ : List S}
    (hpath : RelPath R p γ r) (htarget : Target r δ) :
    Target p (γ ++ δ) := by
  induction hpath with
  | nil p => simpa using htarget
  | cons hstep _ ih =>
      exact hR hstep _ (ih htarget)

/-- Semantic target for stopping: controls represent genuine DPDA configurations;
the sink means the target has already been reached and the rest of the stack is ignored. -/
def stopTarget (M : DPDA Q T S) : PAutState Q → List S → Prop
  | .inl q, γ => ∃ cstable, M.EpsilonStopsAt (q, γ) cstable
  | .inr (), _ => True

theorem stopTarget_nil (M : DPDA Q T S) (r : PAutState Q) :
    stopTarget M r [] := by
  cases r with
  | inl q =>
      exact ⟨(q, []), Relation.ReflTransGen.refl, by simp [EpsilonStable]⟩
  | inr u => cases u; trivial

theorem stopSaturationRel_preservesTarget (M : DPDA Q T S) :
    RelationPreservesTarget (stopSaturationRel M) (stopTarget M) := by
  intro p r Z hrel δ htarget
  let semanticRel : PAutState Q → S → PAutState Q → Prop :=
    fun p Z r => ∀ δ, stopTarget M r δ → stopTarget M p (Z :: δ)
  have hbase : ∀ {p Z r}, stopTargetBase M p Z r → semanticRel p Z r := by
    intro p Z r hbase δ htarget
    cases p with
    | inl q =>
        cases r with
        | inl r =>
            simp [stopTargetBase] at hbase
        | inr u =>
            cases u
            exact ⟨(q, Z :: δ), Relation.ReflTransGen.refl, by
              simpa [EpsilonStable] using hbase⟩
    | inr u =>
        cases u
        cases r with
        | inl r =>
            simp [stopTargetBase] at hbase
        | inr u =>
            cases u
            trivial
  have hsat : EpsilonStepSaturated M semanticRel := by
    intro q p Z β r hε hpath δ htarget
    have hafter : stopTarget M (PAutState.control p) (β ++ δ) :=
      RelPath.preservesTarget (R := semanticRel) (Target := stopTarget M)
        (by intro p r Z h δ htarget; exact h δ htarget) hpath htarget
    obtain ⟨cstable, hstops⟩ := hafter
    exact epsilonStopsAt_of_step
      (M := M) (c := (q, Z :: δ)) (c₁ := (p, β ++ δ))
      ⟨β, hε, rfl⟩ ⟨cstable, hstops⟩
  exact hrel semanticRel hbase hsat δ htarget

theorem stopSaturationRel_path_sound (M : DPDA Q T S)
    {p r : PAutState Q} {γ δ : List S}
    (hpath : RelPath (stopSaturationRel M) p γ r)
    (htarget : stopTarget M r δ) :
    stopTarget M p (γ ++ δ) :=
  RelPath.preservesTarget (R := stopSaturationRel M) (Target := stopTarget M)
    (stopSaturationRel_preservesTarget M) hpath htarget

theorem stopSaturationDFA_sound (M : DPDA Q T S) (q : Q) (γ : List S) :
    γ ∈ (stopSaturationDFA M q).accepts →
      ∃ cstable, M.EpsilonStopsAt (q, γ) cstable := by
  intro h
  obtain ⟨r, hpath⟩ := (stopSaturationDFA_accepts_iff M q γ).1 h
  have htarget := stopSaturationRel_path_sound M hpath (stopTarget_nil M r)
  simpa [stopTarget] using htarget

theorem stopSaturationRel_sink_path (M : DPDA Q T S) (γ : List S) :
    RelPath (stopSaturationRel M) (PAutState.sink : PAutState Q) γ PAutState.sink := by
  induction γ with
  | nil => exact RelPath.nil PAutState.sink
  | cons Z γ ih =>
      exact RelPath.cons
        (base_subset_epsilonSaturationRel M (base := stopTargetBase M) (by
          simp [stopTargetBase, PAutState.sink]))
        ih

theorem stopSaturationRel_path_of_stable (M : DPDA Q T S)
    {q : Q} {γ : List S}
    (hstable : M.EpsilonStable (q, γ)) :
    ∃ r, RelPath (stopSaturationRel M) (PAutState.control q) γ r := by
  cases γ with
  | nil => exact ⟨PAutState.control q, RelPath.nil (PAutState.control q)⟩
  | cons Z γ =>
      refine ⟨PAutState.sink, RelPath.cons ?_ (stopSaturationRel_sink_path M γ)⟩
      exact base_subset_epsilonSaturationRel M (base := stopTargetBase M) (by
        simpa [stopTargetBase, PAutState.control, PAutState.sink, EpsilonStable] using hstable)

theorem stopSaturationRel_path_of_epsilonStopsAt (M : DPDA Q T S)
    {q : Q} {γ : List S} {cstable : EpsilonConf Q S}
    (hstops : M.EpsilonStopsAt (q, γ) cstable) :
    ∃ r, RelPath (stopSaturationRel M) (PAutState.control q) γ r := by
  obtain ⟨hreach, hstable⟩ := hstops
  have hmain :
      ∀ {c₀ c₁ : EpsilonConf Q S},
        M.EpsilonReaches c₀ c₁ →
        M.EpsilonStable c₁ →
        ∃ r, RelPath (stopSaturationRel M) (PAutState.control c₀.1) c₀.2 r := by
    intro c₀ c₁ hreach
    induction hreach using Relation.ReflTransGen.head_induction_on with
    | refl =>
        intro hstable
        rcases c₀ with ⟨q, γ⟩
        exact stopSaturationRel_path_of_stable M hstable
    | @head c₀ c₁ hstep hrest ih =>
        intro hstable
        rcases c₀ with ⟨q, γ⟩
        rcases c₁ with ⟨p, γ'⟩
        obtain ⟨r, hpathRest⟩ := ih hstable
        cases γ with
        | nil => cases hstep
        | cons Z δ =>
            obtain ⟨β, hε, hγ'⟩ := hstep
            subst γ'
            obtain ⟨m, hβ, hδ⟩ :=
              RelPath.of_append_left (R := stopSaturationRel M)
                (γ := β) (δ := δ) hpathRest
            refine ⟨r, RelPath.cons ?_ hδ⟩
            exact (epsilonSaturationRel_saturated M (stopTargetBase M)) hε hβ
  exact hmain hreach hstable

theorem stopSaturationDFA_complete (M : DPDA Q T S) (q : Q) (γ : List S) :
    (∃ cstable, M.EpsilonStopsAt (q, γ) cstable) →
      γ ∈ (stopSaturationDFA M q).accepts := by
  rintro ⟨cstable, hstops⟩
  obtain ⟨r, hpath⟩ := stopSaturationRel_path_of_epsilonStopsAt M hstops
  exact (stopSaturationDFA_accepts_iff M q γ).2 ⟨r, hpath⟩

theorem stopSaturationDFA_correct (M : DPDA Q T S) (q : Q) (γ : List S) :
    γ ∈ (stopSaturationDFA M q).accepts ↔
      ∃ cstable, M.EpsilonStopsAt (q, γ) cstable :=
  ⟨stopSaturationDFA_sound M q γ, stopSaturationDFA_complete M q γ⟩

theorem finalSaturationDFA_accepts_iff (M : DPDA Q T S) (q : Q) (γ : List S) :
    γ ∈ (finalSaturationDFA M q).accepts ↔
      ∃ r, r ∈ finalTargetAccept M ∧
        RelPath (finalSaturationRel M) (PAutState.control q) γ r := by
  exact relDFA_accepts_iff

/-- Semantic target for final-state epsilon reachability. -/
def finalTarget (M : DPDA Q T S) : PAutState Q → List S → Prop
  | .inl q, γ =>
      ∃ qf γf, M.EpsilonReaches (q, γ) (qf, γf) ∧ qf ∈ M.final_states
  | .inr (), _ => True

theorem finalTarget_nil_iff (M : DPDA Q T S) (r : PAutState Q) :
    finalTarget M r [] ↔ r ∈ finalTargetAccept M := by
  cases r with
  | inl q =>
      constructor
      · rintro ⟨qf, γf, hreach, hfinal⟩
        have hsame := PDA.reaches_on_empty_stack
          (pda := M.toPDA)
          (epsilonReaches_toPDA (M := M) (w := ([] : List T)) hreach)
        simp at hsame
        rcases hsame with ⟨_, _, rfl⟩
        exact hfinal
      · intro hfinal
        exact ⟨q, [], Relation.ReflTransGen.refl, hfinal⟩
  | inr u =>
      cases u
      constructor <;> intro _ <;> trivial

theorem finalSaturationRel_preservesTarget (M : DPDA Q T S) :
    RelationPreservesTarget (finalSaturationRel M) (finalTarget M) := by
  intro p r Z hrel δ htarget
  let semanticRel : PAutState Q → S → PAutState Q → Prop :=
    fun p Z r => ∀ δ, finalTarget M r δ → finalTarget M p (Z :: δ)
  have hbase : ∀ {p Z r}, finalTargetBase M p Z r → semanticRel p Z r := by
    intro p Z r hbase δ htarget
    cases p with
    | inl q =>
        cases r with
        | inl r =>
            simp [finalTargetBase] at hbase
        | inr u =>
            cases u
            exact ⟨q, Z :: δ, Relation.ReflTransGen.refl, hbase⟩
    | inr u =>
        cases u
        cases r with
        | inl r =>
            simp [finalTargetBase] at hbase
        | inr u =>
            cases u
            trivial
  have hsat : EpsilonStepSaturated M semanticRel := by
    intro q p Z β r hε hpath δ htarget
    have hafter : finalTarget M (PAutState.control p) (β ++ δ) :=
      RelPath.preservesTarget (R := semanticRel) (Target := finalTarget M)
        (by intro p r Z h δ htarget; exact h δ htarget) hpath htarget
    obtain ⟨qf, γf, hreach, hfinal⟩ := hafter
    exact ⟨qf, γf,
      Relation.ReflTransGen.trans
        (Relation.ReflTransGen.single (by
          exact (⟨β, hε, rfl⟩ : M.EpsilonStep (q, Z :: δ) (p, β ++ δ))))
        hreach,
      hfinal⟩
  exact hrel semanticRel hbase hsat δ htarget

theorem finalSaturationRel_path_sound (M : DPDA Q T S)
    {p r : PAutState Q} {γ δ : List S}
    (hpath : RelPath (finalSaturationRel M) p γ r)
    (htarget : finalTarget M r δ) :
    finalTarget M p (γ ++ δ) :=
  RelPath.preservesTarget (R := finalSaturationRel M) (Target := finalTarget M)
    (finalSaturationRel_preservesTarget M) hpath htarget

theorem finalSaturationDFA_sound (M : DPDA Q T S) (q : Q) (γ : List S) :
    γ ∈ (finalSaturationDFA M q).accepts →
      ∃ qf γf, M.EpsilonReaches (q, γ) (qf, γf) ∧ qf ∈ M.final_states := by
  intro h
  obtain ⟨r, hr, hpath⟩ := (finalSaturationDFA_accepts_iff M q γ).1 h
  have htargetNil : finalTarget M r [] := (finalTarget_nil_iff M r).2 hr
  have htarget := finalSaturationRel_path_sound M hpath htargetNil
  simpa [finalTarget] using htarget

theorem finalSaturationRel_sink_path (M : DPDA Q T S) (γ : List S) :
    RelPath (finalSaturationRel M) (PAutState.sink : PAutState Q) γ PAutState.sink := by
  induction γ with
  | nil => exact RelPath.nil PAutState.sink
  | cons Z γ ih =>
      exact RelPath.cons
        (base_subset_epsilonSaturationRel M (base := finalTargetBase M) (by
          simp [finalTargetBase, PAutState.sink]))
        ih

theorem finalSaturationRel_path_of_final (M : DPDA Q T S)
    {q : Q} {γ : List S}
    (hfinal : q ∈ M.final_states) :
    ∃ r, r ∈ finalTargetAccept M ∧
      RelPath (finalSaturationRel M) (PAutState.control q) γ r := by
  cases γ with
  | nil =>
      exact ⟨PAutState.control q, hfinal, RelPath.nil (PAutState.control q)⟩
  | cons Z γ =>
      refine ⟨PAutState.sink, trivial, ?_⟩
      exact RelPath.cons
        (base_subset_epsilonSaturationRel M (base := finalTargetBase M) (by
          simpa [finalTargetBase, PAutState.control, PAutState.sink] using hfinal))
        (finalSaturationRel_sink_path M γ)

theorem finalSaturationRel_path_of_epsilonReaches_final (M : DPDA Q T S)
    {q qf : Q} {γ γf : List S}
    (hreach : M.EpsilonReaches (q, γ) (qf, γf))
    (hfinal : qf ∈ M.final_states) :
    ∃ r, r ∈ finalTargetAccept M ∧
      RelPath (finalSaturationRel M) (PAutState.control q) γ r := by
  have hmain :
      ∀ {c₀ c₁ : EpsilonConf Q S},
        M.EpsilonReaches c₀ c₁ →
        c₁.1 ∈ M.final_states →
        ∃ r, r ∈ finalTargetAccept M ∧
          RelPath (finalSaturationRel M) (PAutState.control c₀.1) c₀.2 r := by
    intro c₀ c₁ hreach
    induction hreach using Relation.ReflTransGen.head_induction_on with
    | refl =>
        intro hfinal
        rcases c₀ with ⟨q, γ⟩
        exact finalSaturationRel_path_of_final M hfinal
    | @head c₀ c₁ hstep hrest ih =>
        intro hfinal
        rcases c₀ with ⟨q, γ⟩
        rcases c₁ with ⟨p, γ'⟩
        obtain ⟨r, hr, hpathRest⟩ := ih hfinal
        cases γ with
        | nil => cases hstep
        | cons Z δ =>
            obtain ⟨β, hε, hγ'⟩ := hstep
            subst γ'
            obtain ⟨m, hβ, hδ⟩ :=
              RelPath.of_append_left (R := finalSaturationRel M)
                (γ := β) (δ := δ) hpathRest
            refine ⟨r, hr, RelPath.cons ?_ hδ⟩
            exact (epsilonSaturationRel_saturated M (finalTargetBase M)) hε hβ
  exact hmain hreach hfinal

theorem finalSaturationDFA_complete (M : DPDA Q T S) (q : Q) (γ : List S) :
    (∃ qf γf, M.EpsilonReaches (q, γ) (qf, γf) ∧ qf ∈ M.final_states) →
      γ ∈ (finalSaturationDFA M q).accepts := by
  rintro ⟨qf, γf, hreach, hfinal⟩
  obtain ⟨r, hr, hpath⟩ :=
    finalSaturationRel_path_of_epsilonReaches_final M hreach hfinal
  exact (finalSaturationDFA_accepts_iff M q γ).2 ⟨r, hr, hpath⟩

theorem finalSaturationDFA_correct (M : DPDA Q T S) (q : Q) (γ : List S) :
    γ ∈ (finalSaturationDFA M q).accepts ↔
      ∃ qf γf, M.EpsilonReaches (q, γ) (qf, γf) ∧ qf ∈ M.final_states :=
  ⟨finalSaturationDFA_sound M q γ, finalSaturationDFA_complete M q γ⟩

end Saturation

end DPDA
