module

public import Langlib.Automata.LinearBounded.CertifiedRowSystem.Characterization
public import Langlib.Automata.LinearBounded.CertifiedRowSystem.Complement.RankGraph
import Mathlib.Tactic

@[expose]
public section

/-!
# Acyclic certified row reachability

Adjoining a same-width clock does not simplify the certified-row formulation of the first LBA
problem.  Given a unit-certified row system `D` over rows in `A`, `acyclicize D` uses rows in

`A × Option A`.

The first track follows a `D` edge or stutters, while the second track is a base-`Option A`
counter that makes one nonoverflowing successor step.  Consequently every row step strictly
increases the counter value and the new row relation is acyclic.

For a nonempty width `n`, the counter has `(card A + 1) ^ n` values, strictly more than the
`card A ^ n` source rows.  Every source path can therefore be shortened and padded to exactly
`card A ^ n` steps, then lifted to the clocked system.  This preserves the row-reachability
language exactly.
-/

open Classical Relation

namespace CertifiedRowSystem

namespace Acyclicize

variable {I A Q F : Type*}

/-- State of the combined source-edge, stutter, and fuel-successor verifier. -/
public structure StepState (Q : Type*) where
  source : Q
  sourceEq : Bool
  fuel : RowNumeral.CarryState
  deriving DecidableEq

public noncomputable instance StepState.instFintype [Fintype Q] :
    Fintype (StepState Q) := by
  classical
  exact Fintype.ofInjective
    (fun q : StepState Q => (q.source, q.sourceEq, q.fuel))
    (by intro x y h; cases x; cases y; simp_all)

/-- Project the source track from a clocked row. -/
public def sourceRow (row : List (A × Option A)) : List A :=
  row.map Prod.fst

/-- Project the fuel track from a clocked row. -/
public def fuelRow (row : List (A × Option A)) : List (Option A) :=
  row.map Prod.snd

/-- The canonical base-`Option A` numeral of fixed width `n`. -/
public noncomputable def fuelNumeral [Fintype A] (n k : Nat) : List (Option A) :=
  (RowNumeral.fuelCodec A).nextRow^[k] ((RowNumeral.fuelCodec A).zeroRow n)

@[simp]
public theorem length_fuelNumeral [Fintype A] (n k : Nat) :
    (fuelNumeral (A := A) n k).length = n := by
  simp [fuelNumeral]

@[simp]
public theorem fuelNumeral_zero [Fintype A] (n : Nat) :
    fuelNumeral (A := A) n 0 = (RowNumeral.fuelCodec A).zeroRow n :=
  rfl

public theorem nextRow_fuelNumeral [Fintype A] (n k : Nat) :
    (RowNumeral.fuelCodec A).nextRow (fuelNumeral (A := A) n k) =
      fuelNumeral n (k + 1) := by
  simp [fuelNumeral, Function.iterate_succ_apply']

/-- Pair a ranked source row with a canonical fuel numeral. -/
public noncomputable def clockedRankRow [Fintype A] [Nonempty A]
    (n : Nat) (row : Complement.RankVertex A n) (fuel : Nat) :
    List (A × Option A) :=
  (Complement.rankRow n row).zip (fuelNumeral n fuel)

@[simp]
public theorem sourceRow_clockedRankRow [Fintype A] [Nonempty A]
    (n : Nat) (row : Complement.RankVertex A n) (fuel : Nat) :
    sourceRow (clockedRankRow n row fuel) = Complement.rankRow n row := by
  apply List.map_fst_zip
  simp

@[simp]
public theorem fuelRow_clockedRankRow [Fintype A] [Nonempty A]
    (n : Nat) (row : Complement.RankVertex A n) (fuel : Nat) :
    fuelRow (clockedRankRow n row fuel) = fuelNumeral n fuel := by
  apply List.map_snd_zip
  simp

/-- Add a same-width, nonoverflowing clock to a unit-certified row system. -/
public noncomputable def system [Fintype A] [DecidableEq A]
    (D : CertifiedRowSystem I A Unit Q F) :
    CertifiedRowSystem I (A × Option A) Unit (StepState Q) F where
  inputCell i := (D.inputCell i, (RowNumeral.fuelCodec A).zero)
  stepStart := ⟨D.stepStart, true, .carry⟩
  stepCell q old new _ :=
    { source := D.stepCell q.source old.1 new.1 ()
      sourceEq := q.sourceEq && decide (old.1 = new.1)
      fuel := (RowNumeral.fuelCodec A).succStep q.fuel old.2 new.2 }
  stepDone q :=
    (D.stepDone q.source || q.sourceEq) && decide (q.fuel = .done)
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

/-- The combined verifier decomposes into the source verifier, equality scan, and fuel
successor scan. -/
public theorem evalStep_system_iff [Fintype A] [DecidableEq A]
    (D : CertifiedRowSystem I A Unit Q F)
    {q out : StepState Q} {old new : List (A × Option A)} {cert : List Unit} :
    (system D).evalStep q old new cert = some out ↔
      D.evalStep q.source (sourceRow old) (sourceRow new) cert = some out.source ∧
        (RowNumeral.fuelCodec A).evalSucc q.fuel
            (fuelRow old) (fuelRow new) = some out.fuel ∧
          out.sourceEq =
            (q.sourceEq && decide (sourceRow old = sourceRow new)) := by
  induction old generalizing q out new cert with
  | nil =>
      cases q with
      | mk qSource qEq qFuel =>
          cases out with
          | mk outSource outEq outFuel =>
              cases new <;> cases cert <;>
                simp [CertifiedRowSystem.evalStep, sourceRow, fuelRow,
                  RowNumeral.DigitCodec.evalSucc]
              all_goals aesop
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
              rw [CertifiedRowSystem.evalStep]
              rw [ih]
              simp only [sourceRow, fuelRow, List.map_cons,
                CertifiedRowSystem.evalStep, RowNumeral.DigitCodec.evalSucc]
              constructor
              · rintro ⟨hsource, hfuel, hEq⟩
                refine ⟨hsource, hfuel, ?_⟩
                simpa [system, Bool.and_assoc, and_iff_left_iff_imp] using hEq
              · rintro ⟨hsource, hfuel, hEq⟩
                refine ⟨hsource, hfuel, ?_⟩
                simpa [system, Bool.and_assoc, and_iff_left_iff_imp] using hEq

private theorem exists_evalStep_unit_of_length
    (D : CertifiedRowSystem I A Unit Q F) (q : Q) (old new : List A)
    (hlen : old.length = new.length) :
    ∃ out, D.evalStep q old new (List.replicate old.length ()) = some out := by
  induction old generalizing q new with
  | nil =>
      have hnew : new = [] := List.length_eq_zero_iff.mp (by simpa using hlen.symm)
      subst new
      exact ⟨q, rfl⟩
  | cons old olds ih =>
      cases new with
      | nil => simp at hlen
      | cons new news =>
          obtain ⟨out, hout⟩ :=
            ih (D.stepCell q old new ()) news (by simpa using hlen)
          exact ⟨out, by
            simpa [CertifiedRowSystem.evalStep, List.replicate_succ] using hout⟩

/-- A clocked row step is exactly a source edge or stutter together with one
nonoverflowing fuel increment. -/
public theorem rowStep_system_iff [Fintype A] [DecidableEq A]
    (D : CertifiedRowSystem I A Unit Q F) (old new : List (A × Option A)) :
    (system D).RowStep old new ↔
      (D.RowStep (sourceRow old) (sourceRow new) ∨
        sourceRow old = sourceRow new) ∧
      fuelRow new = (RowNumeral.fuelCodec A).nextRow (fuelRow old) ∧
      ((RowNumeral.fuelCodec A).increment (fuelRow old)).2 = false := by
  constructor
  · rintro ⟨cert, out, heval, hdone⟩
    have heval' := (evalStep_system_iff D).1 heval
    have hdone' :
        (D.stepDone out.source = true ∨ out.sourceEq = true) ∧
          out.fuel = .done := by
      simpa [system, Bool.and_eq_true, Bool.or_eq_true] using hdone
    have hfuel :
        fuelRow new = (RowNumeral.fuelCodec A).nextRow (fuelRow old) ∧
          ((RowNumeral.fuelCodec A).increment (fuelRow old)).2 = false := by
      apply ((RowNumeral.fuelCodec A).evalSucc_eq_done_iff
        (fuelRow old) (fuelRow new)).1
      simpa [hdone'.2] using heval'.2.1
    refine ⟨?_, hfuel⟩
    rcases hdone'.1 with hsource | heq
    · exact Or.inl ⟨cert, out.source, heval'.1, hsource⟩
    · right
      have hflag :
          out.sourceEq = decide (sourceRow old = sourceRow new) := by
        simpa [system] using heval'.2.2
      rw [hflag] at heq
      simpa using heq
  · rintro ⟨hsource, hnext, hno⟩
    have hfuel :
        (RowNumeral.fuelCodec A).evalSucc .carry
            (fuelRow old) (fuelRow new) = some .done := by
      apply ((RowNumeral.fuelCodec A).evalSucc_eq_done_iff
        (fuelRow old) (fuelRow new)).2
      exact ⟨hnext, hno⟩
    rcases hsource with hstep | heq
    · obtain ⟨cert, q, heval, hdone⟩ := hstep
      let out : StepState Q :=
        ⟨q, decide (sourceRow old = sourceRow new), .done⟩
      refine ⟨cert, out, ?_, ?_⟩
      · apply (evalStep_system_iff D).2
        exact ⟨heval, hfuel, by simp [out, system]⟩
      · simp [system, out, hdone]
    · have hlen : (sourceRow old).length = (sourceRow new).length :=
        congrArg List.length heq
      obtain ⟨q, heval⟩ :
          ∃ q, D.evalStep D.stepStart (sourceRow old) (sourceRow new)
            (List.replicate (sourceRow old).length ()) = some q := by
        exact exists_evalStep_unit_of_length D D.stepStart _ _ hlen
      let out : StepState Q := ⟨q, true, .done⟩
      refine ⟨List.replicate (sourceRow old).length (), out, ?_, ?_⟩
      · apply (evalStep_system_iff D).2
        refine ⟨heval, hfuel, ?_⟩
        simp [out, system, heq]
      · simp [system, out]

/-- A clocked row step raises the numeric fuel value by exactly one. -/
public theorem fuelValue_step [Fintype A] [DecidableEq A]
    (D : CertifiedRowSystem I A Unit Q F) {old new : List (A × Option A)}
    (hstep : (system D).RowStep old new) :
    (RowNumeral.fuelCodec A).value (fuelRow new) =
      (RowNumeral.fuelCodec A).value (fuelRow old) + 1 := by
  obtain ⟨_, hnext, hno⟩ := (rowStep_system_iff D old new).1 hstep
  rw [hnext]
  exact (RowNumeral.fuelCodec A).value_increment_of_not_overflow (fuelRow old) hno

/-- Every clocked row step strictly increases the numeric fuel value. -/
public theorem fuelValue_lt_of_step [Fintype A] [DecidableEq A]
    (D : CertifiedRowSystem I A Unit Q F) {old new : List (A × Option A)}
    (hstep : (system D).RowStep old new) :
    (RowNumeral.fuelCodec A).value (fuelRow old) <
      (RowNumeral.fuelCodec A).value (fuelRow new) := by
  rw [fuelValue_step D hstep]
  omega

/-- Every nonempty clocked path strictly increases the numeric fuel value. -/
public theorem fuelValue_lt_of_transGen [Fintype A] [DecidableEq A]
    (D : CertifiedRowSystem I A Unit Q F) {old new : List (A × Option A)}
    (hpath : TransGen (system D).RowStep old new) :
    (RowNumeral.fuelCodec A).value (fuelRow old) <
      (RowNumeral.fuelCodec A).value (fuelRow new) := by
  induction hpath with
  | single hstep =>
      exact fuelValue_lt_of_step D hstep
  | tail hpath hstep ih =>
      exact ih.trans (fuelValue_lt_of_step D hstep)

/-- The clocked row relation has no nontrivial directed cycle. -/
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
  | refl =>
      exact .refl
  | tail hreach hstep ih =>
      rcases ((rowStep_system_iff D _ _).1 hstep).1 with hedge | hstutter
      · exact ih.tail hedge
      · simpa [hstutter] using ih

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

/-- Lift a padded rank-graph path to the clocked row system. -/
public theorem lift_paddedPath [Fintype A] [DecidableEq A] [Nonempty A]
    (D : CertifiedRowSystem I A Unit Q F) {n steps : Nat}
    {source target : Complement.RankVertex A n}
    (hn : 0 < n) (hsteps : steps ≤ Fintype.card A ^ n)
    (hpath : FiniteReachabilityCounting.PaddedPath
      (Complement.rankEdge D n) source steps target) :
    ReflTransGen (system D).RowStep
      (clockedRankRow n source 0) (clockedRankRow n target steps) := by
  induction hpath with
  | zero =>
      exact .refl
  | @succ k old new hpath hmove ih =>
      have hk : k ≤ Fintype.card A ^ n := by omega
      have hreach := ih hk
      apply hreach.tail
      apply (rowStep_system_iff D _ _).2
      constructor
      · rcases hmove with rfl | hedge
        · exact Or.inr (by simp)
        · exact Or.inl (by simpa using hedge)
      · constructor
        · simp only [fuelRow_clockedRankRow]
          exact (nextRow_fuelNumeral n k).symm
        · have hcap :
              k + 1 < (RowNumeral.fuelCodec A).radix ^ n := by
            exact lt_of_le_of_lt hsteps
              (RowNumeral.rowCapacity_lt_fuelCapacity A hn)
          have hkcap :
              k < (RowNumeral.fuelCodec A).radix ^ n := by omega
          have hno :=
            ((RowNumeral.fuelCodec A).increment_iterate_nextRow_not_overflow_iff
              hkcap).2 hcap
          simpa only [fuelRow_clockedRankRow, fuelNumeral] using hno

/-- The clocked construction preserves the row-reachability language exactly. -/
public theorem rowReachLanguage_system [Fintype A] [DecidableEq A]
    (D : CertifiedRowSystem I A Unit Q F) :
    (system D).rowReachLanguage = D.rowReachLanguage := by
  funext input
  apply propext
  constructor
  · rintro ⟨hinput, row, hreach, hfinal⟩
    refine ⟨hinput, sourceRow row, ?_, ?_⟩
    · simpa using project_reach D hreach
    · exact (final_system_iff D row).1 hfinal
  · rintro ⟨hinput, finalRow, hreach, hfinal⟩
    cases input with
    | nil =>
        exact (hinput rfl).elim
    | cons first rest =>
        letI : Nonempty A := ⟨D.inputCell first⟩
        let input : List I := first :: rest
        let n := input.length
        have hn : 0 < n := by simp [n, input]
        let source : Complement.RankVertex A n :=
          Complement.sourceRank n (input.map D.inputCell) (by simp [n])
        have hsource :
            Complement.rankRow n source = input.map D.inputCell := by
          exact Complement.rankRow_sourceRank n _ _
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
        have hclocked :
            ReflTransGen (system D).RowStep
              (clockedRankRow n source 0)
              (clockedRankRow n target (Fintype.card A ^ n)) :=
          lift_paddedPath D hn (Nat.le_refl _) hpath
        refine ⟨by simp, clockedRankRow n target (Fintype.card A ^ n), ?_, ?_⟩
        · change ReflTransGen (system D).RowStep
            (input.map (system D).inputCell)
            (clockedRankRow n target (Fintype.card A ^ n))
          rw [input_eq_clockedRankRow D input]
          exact hclocked
        · apply (final_system_iff D _).2
          simpa [htarget] using hfinal

end Acyclicize

/-- Add a same-width, nonoverflowing base-`Option A` clock to a unit-certified row system. -/
public noncomputable abbrev acyclicize {I A Q F : Type*}
    [Fintype A] [DecidableEq A] (D : CertifiedRowSystem I A Unit Q F) :=
  Acyclicize.system D

/-- A certified row relation is acyclic when its transitive closure is irreflexive. -/
public def RowAcyclic {I A C Q F : Type*}
    (D : CertifiedRowSystem I A C Q F) : Prop :=
  ∀ row, ¬ TransGen D.RowStep row row

/-- Exact semantic description of a step in `acyclicize D`. -/
public theorem rowStep_acyclicize_iff {I A Q F : Type*}
    [Fintype A] [DecidableEq A] (D : CertifiedRowSystem I A Unit Q F)
    (old new : List (A × Option A)) :
    (acyclicize D).RowStep old new ↔
      (D.RowStep (Acyclicize.sourceRow old) (Acyclicize.sourceRow new) ∨
        Acyclicize.sourceRow old = Acyclicize.sourceRow new) ∧
      Acyclicize.fuelRow new =
        (RowNumeral.fuelCodec A).nextRow (Acyclicize.fuelRow old) ∧
      ((RowNumeral.fuelCodec A).increment (Acyclicize.fuelRow old)).2 = false :=
  Acyclicize.rowStep_system_iff D old new

/-- The clocked construction is acyclic. -/
public theorem rowAcyclic_acyclicize {I A Q F : Type*}
    [Fintype A] [DecidableEq A] (D : CertifiedRowSystem I A Unit Q F) :
    RowAcyclic (acyclicize D) :=
  fun row => Acyclicize.no_transGen_self D row

/-- Clocking preserves the row-reachability language exactly. -/
public theorem rowReachLanguage_acyclicize {I A Q F : Type*}
    [Fintype A] [DecidableEq A] (D : CertifiedRowSystem I A Unit Q F) :
    (acyclicize D).rowReachLanguage = D.rowReachLanguage :=
  Acyclicize.rowReachLanguage_system D

/-- The restriction of unit-certified row determinization to acyclic row systems. -/
public def EveryAcyclicUnitCertificateRowReachLanguageIsDLBA
    (T : Type) [Fintype T] [DecidableEq T] : Prop :=
  ∀ (A Q F : Type)
    [Fintype A] [Fintype Q] [Fintype F]
    [DecidableEq A] [DecidableEq Q] [DecidableEq F]
    (D : CertifiedRowSystem T A Unit Q F),
    RowAcyclic D → is_DLBA D.rowReachLanguage

/-- Restricting unit-certified row reachability to acyclic systems does not weaken the
determinization problem. -/
public theorem everyUnitCertificateRowReach_iff_acyclic
    {T : Type} [Fintype T] [DecidableEq T] :
    EveryUnitCertificateRowReachLanguageIsDLBA T ↔
      EveryAcyclicUnitCertificateRowReachLanguageIsDLBA T := by
  constructor
  · intro hrows A Q F hA hQ hF hdA hdQ hdF D _
    letI := hA
    letI := hQ
    letI := hF
    letI := hdA
    letI := hdQ
    letI := hdF
    exact hrows A Q F D
  · intro hrows A Q F hA hQ hF hdA hdQ hdF D
    letI := hA
    letI := hQ
    letI := hF
    letI := hdA
    letI := hdQ
    letI := hdF
    have hdet : is_DLBA (acyclicize D).rowReachLanguage :=
      hrows (A × Option A) (Acyclicize.StepState Q) F (acyclicize D)
        (rowAcyclic_acyclicize D)
    simpa [rowReachLanguage_acyclicize D] using hdet

/-- The first LBA problem is exactly deterministic reachability even for acyclic,
unit-certified row systems. -/
public theorem lba_subset_dlba_iff_acyclicUnitCertificateRowReach
    {T : Type} [Fintype T] [DecidableEq T] :
    ((LBA : Set (Language T)) ⊆ DLBA) ↔
      EveryAcyclicUnitCertificateRowReachLanguageIsDLBA T :=
  lba_subset_dlba_iff_unitCertificateRowReach.trans
    everyUnitCertificateRowReach_iff_acyclic

/-- Equality of LBA and DLBA is exactly deterministic reachability for acyclic,
unit-certified fixed-width row systems. -/
public theorem lba_eq_dlba_iff_acyclicUnitCertificateRowReach
    {T : Type} [Fintype T] [DecidableEq T] :
    ((LBA : Set (Language T)) = DLBA) ↔
      EveryAcyclicUnitCertificateRowReachLanguageIsDLBA T :=
  lba_eq_dlba_iff_unitCertificateRowReach.trans
    everyUnitCertificateRowReach_iff_acyclic

end CertifiedRowSystem

end
