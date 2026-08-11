module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.CertificateRuns
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.DerivedPairQuotient
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.DerivedRepeat
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.OrdinaryGroundRuns

@[expose]
public section

/-!
# Continuing certificate-derived pairs along a fixed trace

The balancing construction changes the pair attached to a prefix word, so
the next selected segment cannot be justified only from the raw residual pair
stored by `TracePath`.  Proposition 31(3) supplies the missing fact: every
derived pair has the same quotient trace language.  Consequently the
remaining segment of the fixed trace executes from both derived components,
and the primary transition rules derive the resulting pair at the later
prefix.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

namespace TracePath

/-- A later certificate-derived pair obtained by actually following the
fixed path segment from an earlier derived pair. -/
public structure DerivedPairAt.ContinuationTo
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {start : ℕ}
    (source : path.DerivedPairAt start)
    (later : ℕ) where
  target : path.DerivedPairAt later
  left_run :
    g.run? (path.segmentWord start (later - start)) source.left =
      some target.left
  right_run :
    g.run? (path.segmentWord start (later - start)) source.right =
      some target.right

/-- Every derived pair can be continued to every later prefix of the same
trace path.  The resulting pair need not be the raw residual pair. -/
public theorem DerivedPairAt.exists_continuationTo
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    (hground : g.groundPairCode initialLeft initialRight = true)
    (hinitial : g.TraceEquivalent initialLeft initialRight)
    {start later : ℕ}
    (source : path.DerivedPairAt start)
    (hle : start ≤ later) :
    Nonempty (source.ContinuationTo later) := by
  let length := later - start
  have hlevel : start + length = later := by
    exact Nat.add_sub_of_le hle
  have hword :
      path.word start ++ path.segmentWord start length =
        path.word later := by
    calc
      path.word start ++ path.segmentWord start length =
          path.word (start + length) :=
        (path.word_add start length).symm
      _ = path.word later := congrArg path.word hlevel
  have htraceLater : g.IsTrace initialLeft (path.word later) := by
    unfold IsTrace
    rw [path.left_run later]
    rfl
  have htrace :
      g.IsTrace initialLeft
        (path.word start ++ path.segmentWord start length) := by
    rw [hword]
    exact htraceLater
  have laws := guardedContextLaws_of_wellFormed hg
  obtain ⟨leftTarget, rightTarget, hleftRun, hrightRun⟩ :=
    source.derivation.exists_pair_runs_of_append_trace
      laws hinitial htrace
  let hgroundSteps : g.PreservesGroundSteps :=
    preservesGroundSteps_of_wellFormed hg
  obtain ⟨actions, hlabels⟩ :=
    path.exists_actions_segmentWord hgroundSteps hground start length
  have hleftActions :
      g.runActions? actions source.left = some leftTarget := by
    simpa [runActions?, ← hlabels] using hleftRun
  have hrightActions :
      g.runActions? actions source.right = some rightTarget := by
    simpa [runActions?, ← hlabels] using hrightRun
  have hsourceEquivalent :=
    source.derivation.pair_traceEquivalent_of_initial laws hinitial
  have htargetDerivation :
      CertificateDerivable g initialLeft initialRight []
        (.pair (path.word start ++ actions.map Sum.inl)
          leftTarget rightTarget) :=
    source.derivation.follow_runActions hgroundSteps
      hsourceEquivalent hleftActions hrightActions
  let target : path.DerivedPairAt later :=
    { left := leftTarget
      right := rightTarget
      derivation := by
        rw [← hword]
        simpa [hlabels] using htargetDerivation }
  exact ⟨
    { target := target
      left_run := by
        simpa [length, target] using hleftRun
      right_run := by
        simpa [length, target] using hrightRun }⟩

/-- The canonically chosen continuation target after `length` labels. -/
public noncomputable def DerivedPairAt.continuationAt
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    (hground : g.groundPairCode initialLeft initialRight = true)
    (hinitial : g.TraceEquivalent initialLeft initialRight)
    {start : ℕ}
    (source : path.DerivedPairAt start)
    (length : ℕ) :
    source.ContinuationTo (start + length) :=
  Classical.choice
    (source.exists_continuationTo hg hground hinitial (by omega))

/-- A certificate-derived pair determines a common infinite continuation path
carrying exactly the remaining labels of the original fixed path. -/
public noncomputable def DerivedPairAt.continuationPath
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    (hground : g.groundPairCode initialLeft initialRight = true)
    (hinitial : g.TraceEquivalent initialLeft initialRight)
    {start : ℕ}
    (source : path.DerivedPairAt start) :
    TracePath g source.left source.right where
  word n := path.segmentWord start n
  left n := (source.continuationAt hg hground hinitial n).target.left
  right n := (source.continuationAt hg hground hinitial n).target.right
  starts_word := by simp [TracePath.segmentWord]
  starts_left := by
    have hrun :=
      (source.continuationAt hg hground hinitial 0).left_run
    simpa [TracePath.segmentWord] using hrun.symm
  starts_right := by
    have hrun :=
      (source.continuationAt hg hground hinitial 0).right_run
    simpa [TracePath.segmentWord] using hrun.symm
  step n := by
    let current :=
      source.continuationAt hg hground hinitial n
    let next :=
      source.continuationAt hg hground hinitial (n + 1)
    let label := path.nextLabel (start + n)
    refine ⟨label, ?_, ?_, ?_⟩
    · simp [TracePath.segmentWord, label]
    · have hcurrent :
          g.run? (path.segmentWord start n) source.left =
            some current.target.left := by
        simpa [current] using current.left_run
      have hnext :
          g.run? (path.segmentWord start (n + 1)) source.left =
            some next.target.left := by
        simpa [next] using next.left_run
      have hsegment :
          path.segmentWord start (n + 1) =
            path.segmentWord start n ++ [label] := by
        simp [TracePath.segmentWord, label]
      rw [hsegment, g.run?_append, hcurrent] at hnext
      simpa [current, next, label] using hnext
    · have hcurrent :
          g.run? (path.segmentWord start n) source.right =
            some current.target.right := by
        simpa [current] using current.right_run
      have hnext :
          g.run? (path.segmentWord start (n + 1)) source.right =
            some next.target.right := by
        simpa [next] using next.right_run
      have hsegment :
          path.segmentWord start (n + 1) =
            path.segmentWord start n ++ [label] := by
        simp [TracePath.segmentWord, label]
      rw [hsegment, g.run?_append, hcurrent] at hnext
      simpa [current, next, label] using hnext

@[simp] public theorem DerivedPairAt.continuationPath_word
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    (hground : g.groundPairCode initialLeft initialRight = true)
    (hinitial : g.TraceEquivalent initialLeft initialRight)
    {start : ℕ}
    (source : path.DerivedPairAt start)
    (n : ℕ) :
    (source.continuationPath hg hground hinitial).word n =
      path.segmentWord start n := rfl

/-- Exact correspondence between relative continuation windows and original
path windows. -/
public theorem DerivedPairAt.continuationPath_segmentWord
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    (hground : g.groundPairCode initialLeft initialRight = true)
    (hinitial : g.TraceEquivalent initialLeft initialRight)
    {start : ℕ}
    (source : path.DerivedPairAt start)
    (offset length : ℕ) :
    (source.continuationPath hg hground hinitial).segmentWord
        offset length =
      path.segmentWord (start + offset) length := by
  let continuation :=
    source.continuationPath hg hground hinitial
  have hcontinuation :=
    continuation.word_add offset length
  have horiginal :=
    path.segmentWord_add start offset length
  change
    path.segmentWord start (offset + length) =
      path.segmentWord start offset ++
        continuation.segmentWord offset length at hcontinuation
  rw [horiginal] at hcontinuation
  exact (List.append_cancel_left hcontinuation).symm

/-- A repeat on a derived pair's continuation path is a derived repeat on
the original path, at the corresponding absolute prefix levels. -/
public theorem DerivedPairAt.hasDerivedRepeat_of_continuationPath_hasRepeat
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    (hground : g.groundPairCode initialLeft initialRight = true)
    (hinitial : g.TraceEquivalent initialLeft initialRight)
    {start : ℕ}
    (source : path.DerivedPairAt start)
    (hrepeat :
      (source.continuationPath hg hground hinitial).HasRepeat) :
    path.HasDerivedRepeat := by
  obtain ⟨i, j, hij, hleft, hright⟩ := hrepeat
  let earlier :=
    (source.continuationAt hg hground hinitial i).target
  let later :=
    (source.continuationAt hg hground hinitial j).target
  refine ⟨start + i, start + j, earlier, later,
    Nat.add_lt_add_left hij start, ?_, ?_⟩
  · simpa [earlier, later, DerivedPairAt.continuationPath] using hleft
  · simpa [earlier, later, DerivedPairAt.continuationPath] using hright

/-- Absence of a derived repeat therefore excludes raw repetition on every
derived continuation path. -/
public theorem DerivedPairAt.continuationPath_hasNoRepeat
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    (hground : g.groundPairCode initialLeft initialRight = true)
    (hinitial : g.TraceEquivalent initialLeft initialRight)
    (hnoRepeat : ¬path.HasDerivedRepeat)
    {start : ℕ}
    (source : path.DerivedPairAt start) :
    ¬(source.continuationPath hg hground hinitial).HasRepeat := by
  intro hrepeat
  exact hnoRepeat
    (source.hasDerivedRepeat_of_continuationPath_hasRepeat
      hg hground hinitial hrepeat)

end TracePath

end EncodedFirstOrderGrammar

end DCFEquivalence
