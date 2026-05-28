module

public import Langlib.Automata.DeterministicPushdown.Definition
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



/-! # Epsilon Phases of a DPDA

Before a DPDA can safely be complemented by flipping final states, its forced
epsilon-only phases must be accounted for.  This file records the semantic
objects used by the totalization construction: epsilon-only one-step motion,
epsilon-only reachability, stable configurations, and divergence.
-/

open PDA

namespace DPDA

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

/-- The stack/control part of a DPDA configuration, ignoring the unchanged input. -/
@[expose]
public abbrev EpsilonConf (Q S : Type) := Q × List S

/-- One forced epsilon step on the control/stack part of a configuration. -/
@[expose]
public def EpsilonStep (M : DPDA Q T S) :
    EpsilonConf Q S → EpsilonConf Q S → Prop
  | (q, Z :: γ), (p, γ') => ∃ β, M.epsilon_transition q Z = some (p, β) ∧ γ' = β ++ γ
  | (_, []), _ => False

/-- The deterministic successor function for one epsilon step, if one exists. -/
@[expose]
public def epsilonNext? (M : DPDA Q T S) : EpsilonConf Q S → Option (EpsilonConf Q S)
  | (q, Z :: γ) =>
      match M.epsilon_transition q Z with
      | some (p, β) => some (p, β ++ γ)
      | none => none
  | (_, []) => none

/-- Epsilon-only reachability on the control/stack part of a configuration. -/
@[expose]
public def EpsilonReaches (M : DPDA Q T S) :
    EpsilonConf Q S → EpsilonConf Q S → Prop :=
  Relation.ReflTransGen M.EpsilonStep

/-- A control/stack configuration is stable when no epsilon transition is forced. -/
@[expose]
public def EpsilonStable (M : DPDA Q T S) : EpsilonConf Q S → Prop
  | (_, []) => True
  | (q, Z :: _) => M.epsilon_transition q Z = none

/-- An epsilon phase stops at a stable control/stack configuration. -/
@[expose]
public def EpsilonStopsAt (M : DPDA Q T S) (c c' : EpsilonConf Q S) : Prop :=
  M.EpsilonReaches c c' ∧ M.EpsilonStable c'

/-- An infinite epsilon-only computation from a control/stack configuration. -/
def EpsilonDiverges (M : DPDA Q T S) (c : EpsilonConf Q S) : Prop :=
  ∃ run : ℕ → EpsilonConf Q S, run 0 = c ∧ ∀ n, M.EpsilonStep (run n) (run (n + 1))

@[simp]
theorem epsilonNext?_nil (M : DPDA Q T S) (q : Q) :
    M.epsilonNext? (q, []) = none :=
  rfl

public theorem epsilonStep_iff_next?_eq_some (M : DPDA Q T S) (c c' : EpsilonConf Q S) :
    M.EpsilonStep c c' ↔ M.epsilonNext? c = some c' := by
  rcases c with ⟨q, γ⟩
  rcases c' with ⟨p, γ'⟩
  rcases γ with _ | ⟨Z, γ⟩
  · simp [EpsilonStep, epsilonNext?]
  · cases hε : M.epsilon_transition q Z with
    | none =>
        simp [EpsilonStep, epsilonNext?, hε]
    | some out =>
        rcases out with ⟨p', β⟩
        constructor
        · rintro ⟨β', hβ', rfl⟩
          simp [hε] at hβ'
          simp [epsilonNext?, hε, hβ']
        · intro h
          simp [epsilonNext?, hε] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨β, hε, rfl⟩

public theorem epsilonStable_iff_next?_eq_none (M : DPDA Q T S) (c : EpsilonConf Q S) :
    M.EpsilonStable c ↔ M.epsilonNext? c = none := by
  rcases c with ⟨q, γ⟩
  rcases γ with _ | ⟨Z, γ⟩
  · simp [EpsilonStable, epsilonNext?]
  · cases hε : M.epsilon_transition q Z <;> simp [EpsilonStable, epsilonNext?, hε]

theorem exists_epsilonStep_of_not_stable (M : DPDA Q T S) {c : EpsilonConf Q S}
    (h : ¬ M.EpsilonStable c) :
    ∃ c', M.EpsilonStep c c' := by
  rw [epsilonStable_iff_next?_eq_none] at h
  cases hn : M.epsilonNext? c with
  | none => exact (h hn).elim
  | some c' =>
      exact ⟨c', (epsilonStep_iff_next?_eq_some M c c').2 hn⟩

public theorem not_epsilonStep_of_stable (M : DPDA Q T S) {c c' : EpsilonConf Q S}
    (hstable : M.EpsilonStable c) :
    ¬ M.EpsilonStep c c' := by
  rw [epsilonStable_iff_next?_eq_none] at hstable
  rw [epsilonStep_iff_next?_eq_some]
  rw [hstable]
  simp

public theorem epsilonStep_deterministic (M : DPDA Q T S) {c c₁ c₂ : EpsilonConf Q S}
    (h₁ : M.EpsilonStep c c₁) (h₂ : M.EpsilonStep c c₂) :
    c₁ = c₂ := by
  rw [epsilonStep_iff_next?_eq_some] at h₁ h₂
  exact Option.some.inj (h₁.symm.trans h₂)

public theorem epsilonStep_suffix_of_stops {M : DPDA Q T S} {c c₁ cfinal : EpsilonConf Q S}
    (hstep : M.EpsilonStep c c₁)
    (hstops : M.EpsilonStopsAt c cfinal) :
    M.EpsilonStopsAt c₁ cfinal := by
  obtain ⟨hreach, hstable⟩ := hstops
  induction hreach using Relation.ReflTransGen.head_induction_on with
  | refl =>
      exact (not_epsilonStep_of_stable M hstable hstep).elim
  | head hfirst hrest _ =>
      have hsame := epsilonStep_deterministic M hstep hfirst
      subst hsame
      exact ⟨hrest, hstable⟩

public theorem epsilonReaches_suffix_of_stops {M : DPDA Q T S} {c c₁ cfinal : EpsilonConf Q S}
    (hreach : M.EpsilonReaches c c₁)
    (hstops : M.EpsilonStopsAt c cfinal) :
    M.EpsilonStopsAt c₁ cfinal := by
  induction hreach with
  | refl => exact hstops
  | tail _ hstep ih =>
      exact epsilonStep_suffix_of_stops hstep ih

public theorem epsilonStopsAt_of_step {M : DPDA Q T S} {c c₁ : EpsilonConf Q S}
    (hstep : M.EpsilonStep c c₁)
    (hstops : ∃ cfinal, M.EpsilonStopsAt c₁ cfinal) :
    ∃ cfinal, M.EpsilonStopsAt c cfinal := by
  obtain ⟨cfinal, hreach, hstable⟩ := hstops
  exact ⟨cfinal,
    Relation.ReflTransGen.trans (Relation.ReflTransGen.single hstep) hreach,
    hstable⟩

/-- The canonical epsilon run that follows the deterministic epsilon successor while it exists. -/
noncomputable def epsilonRun (M : DPDA Q T S) (c : EpsilonConf Q S) : ℕ → EpsilonConf Q S
  | 0 => c
  | n + 1 => (M.epsilonNext? (M.epsilonRun c n)).getD (M.epsilonRun c n)

theorem epsilonRun_zero (M : DPDA Q T S) (c : EpsilonConf Q S) :
    M.epsilonRun c 0 = c :=
  rfl

theorem epsilonRun_succ (M : DPDA Q T S) (c : EpsilonConf Q S) (n : ℕ) :
    M.epsilonRun c (n + 1) =
      (M.epsilonNext? (M.epsilonRun c n)).getD (M.epsilonRun c n) :=
  rfl

theorem epsilonReaches_epsilonRun_of_all_steps {M : DPDA Q T S} {c : EpsilonConf Q S}
    (hstep : ∀ n, M.EpsilonStep (M.epsilonRun c n) (M.epsilonRun c (n + 1))) :
    ∀ n, M.EpsilonReaches c (M.epsilonRun c n) := by
  intro n
  induction n with
  | zero => exact Relation.ReflTransGen.refl
  | succ n ih => exact Relation.ReflTransGen.tail ih (hstep n)

/-- Semantically, a deterministic epsilon phase either reaches a stable configuration
or has an infinite epsilon-only run.  The later finite-state totalizer must implement
this split using regular stack lookahead. -/
theorem epsilonPhase_stops_or_diverges (M : DPDA Q T S) (c : EpsilonConf Q S) :
    (∃ c', M.EpsilonStopsAt c c') ∨ M.EpsilonDiverges c := by
  classical
  by_cases hstop : ∃ c', M.EpsilonStopsAt c c'
  · exact Or.inl hstop
  · right
    refine ⟨M.epsilonRun c, rfl, ?_⟩
    intro n
    have hreach : M.EpsilonReaches c (M.epsilonRun c n) := by
      induction n with
      | zero => exact Relation.ReflTransGen.refl
      | succ n ih =>
          have hnot_stable : ¬ M.EpsilonStable (M.epsilonRun c n) := by
            intro hstable
            exact hstop ⟨M.epsilonRun c n, ih, hstable⟩
          obtain ⟨cnext, hnext⟩ := exists_epsilonStep_of_not_stable M hnot_stable
          have hnext_eq : M.epsilonNext? (M.epsilonRun c n) = some cnext :=
            (epsilonStep_iff_next?_eq_some M (M.epsilonRun c n) cnext).1 hnext
          have hs : M.epsilonRun c (n + 1) = cnext := by
            simp [epsilonRun_succ, hnext_eq]
          exact Relation.ReflTransGen.tail ih (hs ▸ hnext)
    have hnot_stable : ¬ M.EpsilonStable (M.epsilonRun c n) := by
      intro hstable
      exact hstop ⟨M.epsilonRun c n, hreach, hstable⟩
    obtain ⟨cnext, hnext⟩ := exists_epsilonStep_of_not_stable M hnot_stable
    have hnext_eq : M.epsilonNext? (M.epsilonRun c n) = some cnext :=
      (epsilonStep_iff_next?_eq_some M (M.epsilonRun c n) cnext).1 hnext
    have hs : M.epsilonRun c (n + 1) = cnext := by
      simp [epsilonRun_succ, hnext_eq]
    exact hs ▸ hnext

/-- Lift one semantic epsilon step to the underlying PDA step relation, for any fixed input. -/
public theorem epsilonStep_toPDA {M : DPDA Q T S} {c c' : EpsilonConf Q S} {w : List T}
    (h : M.EpsilonStep c c') :
    @PDA.Reaches₁ Q T S _ _ _ M.toPDA
      ⟨c.1, w, c.2⟩ ⟨c'.1, w, c'.2⟩ := by
  rcases c with ⟨q, γ⟩
  rcases c' with ⟨p, γ'⟩
  rcases γ with _ | ⟨Z, γ⟩
  · cases h
  · obtain ⟨β, hβ, rfl⟩ := h
    cases w with
    | nil =>
        change ⟨p, [], β ++ γ⟩ ∈ PDA.step (pda := M.toPDA) ⟨q, [], Z :: γ⟩
        exact ⟨p, β, by simp [DPDA.toPDA, hβ], rfl⟩
    | cons a w =>
        change ⟨p, a :: w, β ++ γ⟩ ∈ PDA.step (pda := M.toPDA) ⟨q, a :: w, Z :: γ⟩
        exact Set.mem_union_right _
          ⟨p, β, by simp [DPDA.toPDA, hβ], rfl⟩

/-- Lift epsilon-only reachability to ordinary PDA reachability, preserving the input. -/
public theorem epsilonReaches_toPDA {M : DPDA Q T S} {c c' : EpsilonConf Q S} {w : List T}
    (h : M.EpsilonReaches c c') :
    @PDA.Reaches Q T S _ _ _ M.toPDA
      ⟨c.1, w, c.2⟩ ⟨c'.1, w, c'.2⟩ := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact Relation.ReflTransGen.tail ih (epsilonStep_toPDA (w := w) hstep)

public theorem epsilonStep_of_toPDA_empty_step {M : DPDA Q T S} {q p : Q} {γ γ' : List S}
    (h : @PDA.Reaches₁ Q T S _ _ _ M.toPDA ⟨q, [], γ⟩ ⟨p, [], γ'⟩) :
    M.EpsilonStep (q, γ) (p, γ') := by
  cases γ with
  | nil => simp [PDA.Reaches₁, PDA.step] at h
  | cons Z rest =>
      simp [PDA.Reaches₁, PDA.step, DPDA.toPDA] at h
      obtain ⟨β, hβ, rfl⟩ := h
      cases hε : M.epsilon_transition q Z with
      | none =>
          simp [hε] at hβ
      | some out =>
          rcases out with ⟨r, δ⟩
          simp [hε] at hβ
          rcases hβ with ⟨rfl, hβ⟩
          subst β
          exact ⟨δ, hε, rfl⟩

public theorem epsilonReaches_of_toPDA_empty_reaches {M : DPDA Q T S} {q p : Q} {γ γ' : List S}
    (h : @PDA.Reaches Q T S _ _ _ M.toPDA ⟨q, [], γ⟩ ⟨p, [], γ'⟩) :
    M.EpsilonReaches (q, γ) (p, γ') := by
  rw [PDA.reaches_iff_reachesIn] at h
  obtain ⟨n, hn⟩ := h
  induction n generalizing p γ' with
  | zero =>
      have heq := PDA.reachesIn_zero hn
      injection heq with hp _ hγ
      subst hp
      subst hγ
      exact Relation.ReflTransGen.refl
  | succ n ih =>
      obtain ⟨c, hprev, hone⟩ := PDA.reachesIn_iff_split_last.mpr hn
      rcases c with ⟨r, inputMid, stackMid⟩
      have hinputMid : inputMid = [] := by
        obtain ⟨u, hu⟩ := PDA.decreasing_input (PDA.reaches_of_reachesIn hprev)
        simp at hu
        exact hu.2
      subst inputMid
      exact Relation.ReflTransGen.tail (ih hprev)
        (epsilonStep_of_toPDA_empty_step (PDA.reaches₁_iff_reachesIn_one.mpr hone))

public theorem stable_reaches_nonempty_decompose {M : DPDA Q T S}
    {q qf : Q} {a : T} {w : List T} {Z : S} {γ γf : List S}
    (hstable : M.epsilon_transition q Z = none)
    (hreach : @PDA.Reaches Q T S _ _ _ M.toPDA
      ⟨q, a :: w, Z :: γ⟩ ⟨qf, [], γf⟩) :
    ∃ p β,
      M.transition q a Z = some (p, β) ∧
      @PDA.Reaches Q T S _ _ _ M.toPDA
        ⟨p, w, β ++ γ⟩ ⟨qf, [], γf⟩ := by
  rw [PDA.reaches_iff_reachesIn] at hreach
  obtain ⟨n, hn⟩ := hreach
  cases n with
  | zero =>
      have heq := PDA.reachesIn_zero hn
      injection heq with _ hinput _
      cases hinput
  | succ n =>
      obtain ⟨c, hone, hrest⟩ := PDA.reachesIn_iff_split_first.mpr hn
      rw [← PDA.reaches₁_iff_reachesIn_one] at hone
      rcases c with ⟨r, input', stack'⟩
      simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, hstable] at hone
      obtain ⟨β, hβ, rfl, rfl⟩ := hone
      cases hδ : M.transition q a Z with
      | none =>
          simp [hδ] at hβ
      | some out =>
          rcases out with ⟨p, δ⟩
          simp [hδ] at hβ
          rcases hβ with ⟨hr, hstack⟩
          subst r
          subst β
          refine ⟨p, δ, rfl, ?_⟩
          exact PDA.reaches_of_reachesIn hrest

public theorem toPDA_reaches_suffix_of_epsilonStep_nonempty {M : DPDA Q T S}
    {c c' : EpsilonConf Q S} {qf : Q} {a : T} {w : List T} {γf : List S}
    (hstep : M.EpsilonStep c c')
    (hreach : @PDA.Reaches Q T S _ _ _ M.toPDA
      ⟨c.1, a :: w, c.2⟩ ⟨qf, [], γf⟩) :
    @PDA.Reaches Q T S _ _ _ M.toPDA
      ⟨c'.1, a :: w, c'.2⟩ ⟨qf, [], γf⟩ := by
  rcases c with ⟨q, γ⟩
  rcases c' with ⟨p, γ'⟩
  cases γ with
  | nil => cases hstep
  | cons Z γ =>
      obtain ⟨β, hε, rfl⟩ := hstep
      rw [PDA.reaches_iff_reachesIn] at hreach
      obtain ⟨n, hn⟩ := hreach
      cases n with
      | zero =>
          have heq := PDA.reachesIn_zero hn
          injection heq with _ hinput _
          cases hinput
      | succ n =>
          obtain ⟨c, hone, hrest⟩ := PDA.reachesIn_iff_split_first.mpr hn
          rw [← PDA.reaches₁_iff_reachesIn_one] at hone
          rcases c with ⟨r, input', stack'⟩
          have hno : M.transition q a Z = none :=
            M.no_mixed q Z (by simp [hε]) a
          simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, hε, hno] at hone
          rcases hone with ⟨hr, hinput, hstack⟩
          subst input'
          subst stack'
          simpa [hr] using PDA.reaches_of_reachesIn hrest

public theorem toPDA_reaches_suffix_of_epsilonReaches_nonempty {M : DPDA Q T S}
    {c c' : EpsilonConf Q S} {qf : Q} {a : T} {w : List T} {γf : List S}
    (heps : M.EpsilonReaches c c')
    (hreach : @PDA.Reaches Q T S _ _ _ M.toPDA
      ⟨c.1, a :: w, c.2⟩ ⟨qf, [], γf⟩) :
    @PDA.Reaches Q T S _ _ _ M.toPDA
      ⟨c'.1, a :: w, c'.2⟩ ⟨qf, [], γf⟩ := by
  induction heps with
  | refl => exact hreach
  | tail _ hstep ih =>
      exact toPDA_reaches_suffix_of_epsilonStep_nonempty hstep ih

public theorem epsilonStopsAt_of_toPDA_reaches_nonempty {M : DPDA Q T S}
    {q qf : Q} {a : T} {w : List T} {γ γf : List S}
    (hreach : @PDA.Reaches Q T S _ _ _ M.toPDA
      ⟨q, a :: w, γ⟩ ⟨qf, [], γf⟩) :
    ∃ cstable, M.EpsilonStopsAt (q, γ) cstable := by
  rw [PDA.reaches_iff_reachesIn] at hreach
  obtain ⟨n, hn⟩ := hreach
  induction n generalizing q γ with
  | zero =>
      have heq := PDA.reachesIn_zero hn
      injection heq with _ hinput _
      cases hinput
  | succ n ih =>
      cases γ with
      | nil =>
          exact ⟨(q, []), Relation.ReflTransGen.refl, by simp [EpsilonStable]⟩
      | cons Z γ =>
          cases hε : M.epsilon_transition q Z with
          | none =>
              exact ⟨(q, Z :: γ), Relation.ReflTransGen.refl, by
                simp [EpsilonStable, hε]⟩
          | some out =>
              rcases out with ⟨p, β⟩
              obtain ⟨c, hone, hrest⟩ := PDA.reachesIn_iff_split_first.mpr hn
              rw [← PDA.reaches₁_iff_reachesIn_one] at hone
              rcases c with ⟨r, input', stack'⟩
              have hno : M.transition q a Z = none :=
                M.no_mixed q Z (by simp [hε]) a
              simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, hε, hno] at hone
              rcases hone with ⟨hr, hinput, hstack⟩
              subst input'
              subst stack'
              have hεr : M.epsilon_transition q Z = some (r, β) := by
                rw [hr]
                exact hε
              have hstep : M.EpsilonStep (q, Z :: γ) (r, β ++ γ) :=
                ⟨β, hεr, rfl⟩
              exact epsilonStopsAt_of_step hstep (ih hrest)

end DPDA
