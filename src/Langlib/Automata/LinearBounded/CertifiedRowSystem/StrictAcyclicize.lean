module

public import Langlib.Automata.LinearBounded.CertifiedRowSystem.Acyclicize
public import Langlib.Automata.LinearBounded.LayeredReachability
import Mathlib.Tactic

@[expose]
public section

/-!
# Strict acyclicization of certified row systems

The padded clock in `Acyclicize` permits a source-row stutter at every layer.  That is convenient
when the target must occur at one prescribed final clock value, but it can increase both directed
degrees by one.

This file uses a strict clock instead.  Every clocked edge consists of one genuine source edge
and one nonoverflowing fuel increment.  A final source row may be accepted at any clock value.
Deleting the stutters from a bounded padded path gives the required strict path, so the
row-reachability language is still preserved.  Since the next fuel row is uniquely determined,
and a nonoverflowing successor has at most one predecessor of the same width, arbitrary uniform
in- and outdegree bounds are preserved.
-/

open Classical Relation

namespace CertifiedRowSystem

/-- A uniform bound on the number of immediate successor rows. -/
public def RowOutdegreeAtMost {I A C Q F : Type*} (bound : ℕ∞)
    (D : CertifiedRowSystem I A C Q F) : Prop :=
  ∀ old, Set.encard {new | D.RowStep old new} ≤ bound

/-- A uniform bound on the number of immediate predecessor rows. -/
public def RowIndegreeAtMost {I A C Q F : Type*} (bound : ℕ∞)
    (D : CertifiedRowSystem I A C Q F) : Prop :=
  ∀ new, Set.encard {old | D.RowStep old new} ≤ bound

/-- Simultaneous uniform bounds on both directed row degrees. -/
public def RowDirectedDegreeAtMost {I A C Q F : Type*} (bound : ℕ∞)
    (D : CertifiedRowSystem I A C Q F) : Prop :=
  RowOutdegreeAtMost bound D ∧ RowIndegreeAtMost bound D

namespace StrictAcyclicize

variable {I A Q F : Type*}

/-- State of the product of the source-edge verifier and the fuel-successor verifier. -/
public structure StepState (Q : Type*) where
  source : Q
  fuel : RowNumeral.CarryState
  deriving DecidableEq

public noncomputable instance StepState.instFintype [Fintype Q] :
    Fintype (StepState Q) := by
  classical
  exact Fintype.ofInjective
    (fun q : StepState Q => (q.source, q.fuel))
    (by intro x y h; cases x; cases y; simp_all)

/-- Project the source track. -/
public def sourceRow (row : List (A × Option A)) : List A :=
  row.map Prod.fst

/-- Project the strict fuel track. -/
public def fuelRow (row : List (A × Option A)) : List (Option A) :=
  row.map Prod.snd

/-- Pair a ranked source row with a canonical fuel value. -/
public noncomputable def clockedRankRow [Fintype A] [Nonempty A]
    (n : Nat) (row : Complement.RankVertex A n) (fuel : Nat) :
    List (A × Option A) :=
  (Complement.rankRow n row).zip (Acyclicize.fuelNumeral n fuel)

@[simp]
public theorem sourceRow_clockedRankRow [Fintype A] [Nonempty A]
    (n : Nat) (row : Complement.RankVertex A n) (fuel : Nat) :
    sourceRow (clockedRankRow n row fuel) = Complement.rankRow n row := by
  apply List.map_fst_zip
  simp

@[simp]
public theorem fuelRow_clockedRankRow [Fintype A] [Nonempty A]
    (n : Nat) (row : Complement.RankVertex A n) (fuel : Nat) :
    fuelRow (clockedRankRow n row fuel) = Acyclicize.fuelNumeral n fuel := by
  apply List.map_snd_zip
  simp

/-- Add a same-width strict, nonoverflowing clock to a unit-certified row system. -/
public noncomputable def system [Fintype A] [DecidableEq A]
    (D : CertifiedRowSystem I A Unit Q F) :
    CertifiedRowSystem I (A × Option A) Unit (StepState Q) F where
  inputCell i := (D.inputCell i, (RowNumeral.fuelCodec A).zero)
  stepStart := ⟨D.stepStart, .carry⟩
  stepCell q old new _ :=
    { source := D.stepCell q.source old.1 new.1 ()
      fuel := (RowNumeral.fuelCodec A).succStep q.fuel old.2 new.2 }
  stepDone q :=
    D.stepDone q.source && decide (q.fuel = .done)
  finalStart := D.finalStart
  finalCell q cell := D.finalCell q cell.1
  finalDone := D.finalDone

@[simp]
public theorem sourceRow_input [Fintype A] [DecidableEq A]
    (D : CertifiedRowSystem I A Unit Q F) (input : List I) :
    sourceRow (input.map (system D).inputCell) = input.map D.inputCell := by
  simp [sourceRow, system]

@[simp]
public theorem fuelRow_input [Fintype A] [DecidableEq A]
    (D : CertifiedRowSystem I A Unit Q F) (input : List I) :
    fuelRow (input.map (system D).inputCell) =
      (RowNumeral.fuelCodec A).zeroRow input.length := by
  simp [fuelRow, system, Function.comp_def, RowNumeral.DigitCodec.zeroRow]

/-- The product verifier decomposes into its two component scans. -/
public theorem evalStep_system_iff [Fintype A] [DecidableEq A]
    (D : CertifiedRowSystem I A Unit Q F)
    {q out : StepState Q} {old new : List (A × Option A)} {cert : List Unit} :
    (system D).evalStep q old new cert = some out ↔
      D.evalStep q.source (sourceRow old) (sourceRow new) cert = some out.source ∧
        (RowNumeral.fuelCodec A).evalSucc q.fuel
          (fuelRow old) (fuelRow new) = some out.fuel := by
  induction old generalizing q out new cert with
  | nil =>
      cases q
      cases out
      cases new <;> cases cert <;>
        simp [CertifiedRowSystem.evalStep, sourceRow, fuelRow,
          RowNumeral.DigitCodec.evalSucc]
  | cons old olds ih =>
      cases new with
      | nil =>
          cases cert <;>
            simp [CertifiedRowSystem.evalStep, sourceRow, fuelRow]
      | cons new news =>
          cases cert with
          | nil =>
              simp [CertifiedRowSystem.evalStep, sourceRow, fuelRow]
          | cons _ certs =>
              rw [CertifiedRowSystem.evalStep, ih]
              simp only [sourceRow, fuelRow, List.map_cons,
                CertifiedRowSystem.evalStep, RowNumeral.DigitCodec.evalSucc]
              rfl

/-- A strict clocked row step is exactly a genuine source edge and one nonoverflowing fuel
increment. -/
public theorem rowStep_system_iff [Fintype A] [DecidableEq A]
    (D : CertifiedRowSystem I A Unit Q F) (old new : List (A × Option A)) :
    (system D).RowStep old new ↔
      D.RowStep (sourceRow old) (sourceRow new) ∧
        fuelRow new = (RowNumeral.fuelCodec A).nextRow (fuelRow old) ∧
        ((RowNumeral.fuelCodec A).increment (fuelRow old)).2 = false := by
  constructor
  · rintro ⟨cert, out, heval, hdone⟩
    have heval' := (evalStep_system_iff D).1 heval
    have hdone' :
        D.stepDone out.source = true ∧ out.fuel = .done := by
      simpa [system, Bool.and_eq_true] using hdone
    refine ⟨⟨cert, out.source, heval'.1, hdone'.1⟩, ?_⟩
    apply ((RowNumeral.fuelCodec A).evalSucc_eq_done_iff
      (fuelRow old) (fuelRow new)).1
    simpa [hdone'.2] using heval'.2
  · rintro ⟨⟨cert, sourceOut, hsource, hdone⟩, hnext, hno⟩
    let out : StepState Q := ⟨sourceOut, .done⟩
    refine ⟨cert, out, ?_, ?_⟩
    · apply (evalStep_system_iff D).2
      refine ⟨hsource, ?_⟩
      apply ((RowNumeral.fuelCodec A).evalSucc_eq_done_iff
        (fuelRow old) (fuelRow new)).2
      exact ⟨hnext, hno⟩
    · simp [system, out, hdone]

/-- Every strict clocked edge raises the fuel value by exactly one. -/
public theorem fuelValue_step [Fintype A] [DecidableEq A]
    (D : CertifiedRowSystem I A Unit Q F) {old new : List (A × Option A)}
    (hstep : (system D).RowStep old new) :
    (RowNumeral.fuelCodec A).value (fuelRow new) =
      (RowNumeral.fuelCodec A).value (fuelRow old) + 1 := by
  obtain ⟨_, hnext, hno⟩ := (rowStep_system_iff D old new).1 hstep
  rw [hnext]
  exact (RowNumeral.fuelCodec A).value_increment_of_not_overflow (fuelRow old) hno

/-- The strict clocked row relation is acyclic. -/
private theorem fuelValue_lt_of_transGen [Fintype A] [DecidableEq A]
    (D : CertifiedRowSystem I A Unit Q F) {old new : List (A × Option A)}
    (hpath : TransGen (system D).RowStep old new) :
    (RowNumeral.fuelCodec A).value (fuelRow old) <
      (RowNumeral.fuelCodec A).value (fuelRow new) := by
  induction hpath with
  | single hstep =>
      rw [fuelValue_step D hstep]
      omega
  | tail hpath hstep ih =>
      exact ih.trans (by rw [fuelValue_step D hstep]; omega)

/-- The strict clocked row relation is acyclic. -/
public theorem no_transGen_self [Fintype A] [DecidableEq A]
    (D : CertifiedRowSystem I A Unit Q F) (row : List (A × Option A)) :
    ¬ TransGen (system D).RowStep row row := by
  intro hcycle
  exact (Nat.lt_irrefl _) (fuelValue_lt_of_transGen D hcycle)

private theorem project_reach [Fintype A] [DecidableEq A]
    (D : CertifiedRowSystem I A Unit Q F) {old new : List (A × Option A)}
    (hreach : ReflTransGen (system D).RowStep old new) :
    ReflTransGen D.RowStep (sourceRow old) (sourceRow new) := by
  induction hreach with
  | refl => exact .refl
  | tail hreach hstep ih =>
      exact ih.tail ((rowStep_system_iff D _ _).1 hstep).1

@[simp]
public theorem final_system_iff [Fintype A] [DecidableEq A]
    (D : CertifiedRowSystem I A Unit Q F) (row : List (A × Option A)) :
    (system D).Final row ↔ D.Final (sourceRow row) := by
  change D.finalDone
      (List.foldl (fun q cell => D.finalCell q cell.1) D.finalStart row) = true ↔
    D.finalDone (List.foldl D.finalCell D.finalStart (row.map Prod.fst)) = true
  rw [List.foldl_map]

private theorem input_eq_clockedRankRow [Fintype A] [DecidableEq A] [Nonempty A]
    (D : CertifiedRowSystem I A Unit Q F) (input : List I) :
    input.map (system D).inputCell =
      clockedRankRow input.length
        (Complement.sourceRank input.length (input.map D.inputCell) (by simp)) 0 := by
  apply List.ext_get
  · simp [clockedRankRow]
  · intro i hi₁ hi₂
    simp only [List.length_map] at hi₁
    simp [clockedRankRow, system, Complement.rankRow_sourceRank,
      RowNumeral.DigitCodec.zeroRow, List.getElem_zip]

/-- Delete padded moves while lifting the remaining genuine edges to the strict clock. -/
public theorem exists_lift_paddedPath [Fintype A] [DecidableEq A] [Nonempty A]
    (D : CertifiedRowSystem I A Unit Q F) {n steps : Nat}
    {source target : Complement.RankVertex A n}
    (hn : 0 < n) (hsteps : steps ≤ Fintype.card A ^ n)
    (hpath : FiniteReachabilityCounting.PaddedPath
      (Complement.rankEdge D n) source steps target) :
    ∃ used, ∃ _hused : used ≤ steps,
      ReflTransGen (system D).RowStep
        (clockedRankRow n source 0) (clockedRankRow n target used) := by
  induction hpath with
  | zero =>
      exact ⟨0, Nat.zero_le _, .refl⟩
  | @succ k old new hpath hmove ih =>
      have hk : k ≤ Fintype.card A ^ n := by omega
      obtain ⟨used, hused, hreach⟩ := ih hk
      rcases hmove with rfl | hedge
      · exact ⟨used, hused.trans (Nat.le_succ k), hreach⟩
      · have husedSucc : used + 1 ≤ k + 1 := Nat.add_le_add_right hused 1
        refine ⟨used + 1, husedSucc, hreach.tail ?_⟩
        apply (rowStep_system_iff D _ _).2
        refine ⟨by simpa using hedge, ?_, ?_⟩
        · simp only [fuelRow_clockedRankRow]
          exact (Acyclicize.nextRow_fuelNumeral n used).symm
        · have hcap :
              used + 1 < (RowNumeral.fuelCodec A).radix ^ n := by
            exact lt_of_le_of_lt (husedSucc.trans hsteps)
              (RowNumeral.rowCapacity_lt_fuelCapacity A hn)
          have husedCap :
              used < (RowNumeral.fuelCodec A).radix ^ n := by omega
          have hno :=
            ((RowNumeral.fuelCodec A).increment_iterate_nextRow_not_overflow_iff
              husedCap).2 hcap
          simpa only [fuelRow_clockedRankRow, Acyclicize.fuelNumeral] using hno

/-- Strict clocking preserves the row-reachability language exactly. -/
public theorem rowReachLanguage_system [Fintype A] [DecidableEq A]
    (D : CertifiedRowSystem I A Unit Q F) :
    (system D).rowReachLanguage = D.rowReachLanguage := by
  funext input
  apply propext
  constructor
  · rintro ⟨hinput, row, hreach, hfinal⟩
    refine ⟨hinput, sourceRow row, ?_, (final_system_iff D row).1 hfinal⟩
    simpa using project_reach D hreach
  · rintro ⟨hinput, finalRow, hreach, hfinal⟩
    cases input with
    | nil => exact (hinput rfl).elim
    | cons first rest =>
        letI : Nonempty A := ⟨D.inputCell first⟩
        let input : List I := first :: rest
        let n := input.length
        have hn : 0 < n := by simp [n, input]
        let source : Complement.RankVertex A n :=
          Complement.sourceRank n (input.map D.inputCell) (by simp [n])
        have hsource :
            Complement.rankRow n source = input.map D.inputCell :=
          Complement.rankRow_sourceRank n _ _
        have hreach' :
            ReflTransGen D.RowStep (Complement.rankRow n source) finalRow := by
          simpa [hsource, input] using hreach
        obtain ⟨target, htarget, hrank⟩ :=
          Complement.rankReach_complete D n hreach'
        letI : DecidableRel (Complement.rankEdge D n) := Classical.decRel _
        have hmem :
            target ∈ FiniteReachabilityCounting.reached
              (Complement.rankEdge D n) source
              (Fintype.card (Complement.RankVertex A n)) :=
          (FiniteReachabilityCounting.mem_reached_card_iff
            (edge := Complement.rankEdge D n) (source := source)).2 hrank
        have hpath :
            FiniteReachabilityCounting.PaddedPath
              (Complement.rankEdge D n) source (Fintype.card A ^ n) target := by
          have := (FiniteReachabilityCounting.mem_reached_iff_paddedPath
            (edge := Complement.rankEdge D n) (source := source)).1 hmem
          simpa [Complement.RankVertex] using this
        obtain ⟨used, _, hclocked⟩ :=
          exists_lift_paddedPath D hn (Nat.le_refl _) hpath
        refine ⟨by simp, clockedRankRow n target used, ?_, ?_⟩
        · change ReflTransGen (system D).RowStep
            (input.map (system D).inputCell) (clockedRankRow n target used)
          rw [input_eq_clockedRankRow D input]
          exact hclocked
        · apply (final_system_iff D _).2
          simpa [htarget] using hfinal

private theorem row_eq_of_projections_eq
    {row₁ row₂ : List (A × Option A)}
    (hsource : sourceRow row₁ = sourceRow row₂)
    (hfuel : fuelRow row₁ = fuelRow row₂) :
    row₁ = row₂ := by
  induction row₁ generalizing row₂ with
  | nil =>
      cases row₂
      · rfl
      · simp [sourceRow] at hsource
  | cons cell row ih =>
      cases row₂ with
      | nil => simp [sourceRow] at hsource
      | cons cell₂ row₂ =>
          simp only [sourceRow, fuelRow, List.map_cons,
            List.cons.injEq] at hsource hfuel
          have hcell : cell = cell₂ := Prod.ext hsource.1 hfuel.1
          subst cell₂
          exact congrArg (List.cons cell) (ih hsource.2 hfuel.2)

/-- Strict clocking cannot increase a fixed row's outdegree. -/
public theorem rowOutdegree_le [Fintype A] [DecidableEq A]
    (D : CertifiedRowSystem I A Unit Q F) (old : List (A × Option A)) :
    Set.encard {new | (system D).RowStep old new} ≤
      Set.encard {row | D.RowStep (sourceRow old) row} := by
  apply Set.encard_le_encard_of_injOn (f := sourceRow)
  · intro new hnew
    exact ((rowStep_system_iff D old new).1 hnew).1
  · intro left hleft right hright hprojection
    apply row_eq_of_projections_eq hprojection
    rw [((rowStep_system_iff D old left).1 hleft).2.1,
      ((rowStep_system_iff D old right).1 hright).2.1]

/-- Strict clocking cannot increase a fixed row's indegree. -/
public theorem rowIndegree_le [Fintype A] [DecidableEq A]
    (D : CertifiedRowSystem I A Unit Q F) (new : List (A × Option A)) :
    Set.encard {old | (system D).RowStep old new} ≤
      Set.encard {row | D.RowStep row (sourceRow new)} := by
  apply Set.encard_le_encard_of_injOn (f := sourceRow)
  · intro old hold
    exact ((rowStep_system_iff D old new).1 hold).1
  · intro left hleft right hright hprojection
    apply row_eq_of_projections_eq hprojection
    apply (RowNumeral.fuelCodec A).value_injective_of_length_eq
    · have hleftLength := (system D).rowStep_length hleft
      have hrightLength := (system D).rowStep_length hright
      simpa [fuelRow] using hleftLength.trans hrightLength.symm
    · have hleftValue := fuelValue_step D hleft
      have hrightValue := fuelValue_step D hright
      omega

/-- Strict clocking preserves every uniform outdegree bound. -/
public theorem rowOutdegreeAtMost [Fintype A] [DecidableEq A]
    {bound : ℕ∞} (D : CertifiedRowSystem I A Unit Q F)
    (hbound : RowOutdegreeAtMost bound D) :
    RowOutdegreeAtMost bound (system D) := by
  intro old
  exact (rowOutdegree_le D old).trans (hbound (sourceRow old))

/-- Strict clocking preserves every uniform indegree bound. -/
public theorem rowIndegreeAtMost [Fintype A] [DecidableEq A]
    {bound : ℕ∞} (D : CertifiedRowSystem I A Unit Q F)
    (hbound : RowIndegreeAtMost bound D) :
    RowIndegreeAtMost bound (system D) := by
  intro new
  exact (rowIndegree_le D new).trans (hbound (sourceRow new))

/-- Strict clocking preserves simultaneous arbitrary directed-degree bounds. -/
public theorem rowDirectedDegreeAtMost [Fintype A] [DecidableEq A]
    {bound : ℕ∞} (D : CertifiedRowSystem I A Unit Q F)
    (hbound : RowDirectedDegreeAtMost bound D) :
    RowDirectedDegreeAtMost bound (system D) :=
  ⟨rowOutdegreeAtMost D hbound.1, rowIndegreeAtMost D hbound.2⟩

end StrictAcyclicize

/-- The strict same-width clocked system. -/
public noncomputable abbrev strictAcyclicize {I A Q F : Type*}
    [Fintype A] [DecidableEq A] (D : CertifiedRowSystem I A Unit Q F) :=
  StrictAcyclicize.system D

public theorem rowStep_strictAcyclicize_iff {I A Q F : Type*}
    [Fintype A] [DecidableEq A] (D : CertifiedRowSystem I A Unit Q F)
    (old new : List (A × Option A)) :
    (strictAcyclicize D).RowStep old new ↔
      D.RowStep (StrictAcyclicize.sourceRow old) (StrictAcyclicize.sourceRow new) ∧
        StrictAcyclicize.fuelRow new =
          (RowNumeral.fuelCodec A).nextRow (StrictAcyclicize.fuelRow old) ∧
        ((RowNumeral.fuelCodec A).increment
          (StrictAcyclicize.fuelRow old)).2 = false :=
  StrictAcyclicize.rowStep_system_iff D old new

public theorem rowAcyclic_strictAcyclicize {I A Q F : Type*}
    [Fintype A] [DecidableEq A] (D : CertifiedRowSystem I A Unit Q F) :
    RowAcyclic (strictAcyclicize D) :=
  fun row => StrictAcyclicize.no_transGen_self D row

public theorem rowReachLanguage_strictAcyclicize {I A Q F : Type*}
    [Fintype A] [DecidableEq A] (D : CertifiedRowSystem I A Unit Q F) :
    (strictAcyclicize D).rowReachLanguage = D.rowReachLanguage :=
  StrictAcyclicize.rowReachLanguage_system D

public theorem rowDirectedDegreeAtMost_strictAcyclicize {I A Q F : Type*}
    [Fintype A] [DecidableEq A] {bound : ℕ∞}
    (D : CertifiedRowSystem I A Unit Q F)
    (hbound : RowDirectedDegreeAtMost bound D) :
    RowDirectedDegreeAtMost bound (strictAcyclicize D) :=
  StrictAcyclicize.rowDirectedDegreeAtMost D hbound

end CertifiedRowSystem

end
