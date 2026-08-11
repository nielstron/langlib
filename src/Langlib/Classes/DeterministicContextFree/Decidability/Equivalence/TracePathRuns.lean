module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.BalancingSegments

@[expose]
public section

/-!
# Runs and certificates along an infinite common trace path

`TracePath` records its two residual sequences one transition at a time.  The
balancing construction uses the equivalent prefix form: the accumulated word
executes from the initial pair to the residual pair at every level.  This file
packages that conversion together with the semantic and certificate
invariants propagated along the path.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- The accumulated path word executes to the recorded left residual. -/
public theorem TracePath.left_run
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    (path : TracePath g initialLeft initialRight) (n : ℕ) :
    g.run? (path.word n) initialLeft = some (path.left n) := by
  induction n with
  | zero => simp [path.starts_word, path.starts_left]
  | succ n ih =>
      obtain ⟨label, hword, hleft, _hright⟩ := path.step n
      rw [show n + 1 = n.succ by omega, hword, g.run?_append, ih]
      simp [hleft]

/-- The accumulated path word executes to the recorded right residual. -/
public theorem TracePath.right_run
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    (path : TracePath g initialLeft initialRight) (n : ℕ) :
    g.run? (path.word n) initialRight = some (path.right n) := by
  induction n with
  | zero => simp [path.starts_word, path.starts_right]
  | succ n ih =>
      obtain ⟨label, hword, _hleft, hright⟩ := path.step n
      rw [show n + 1 = n.succ by omega, hword, g.run?_append, ih]
      simp [hright]

/-- Trace equivalence is retained at every residual pair of a common path. -/
public theorem TracePath.residual_traceEquivalent
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    (path : TracePath g initialLeft initialRight)
    (hinitial : g.TraceEquivalent initialLeft initialRight) (n : ℕ) :
    g.TraceEquivalent (path.left n) (path.right n) :=
  hinitial.residual (path.left_run n) (path.right_run n)

/-- Groundness of both initial terms is retained along a common path. -/
public theorem TracePath.residual_ground
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    (path : TracePath g initialLeft initialRight)
    (hgroundSteps : g.PreservesGroundSteps)
    (hground : g.groundPairCode initialLeft initialRight = true) (n : ℕ) :
    g.groundPairCode (path.left n) (path.right n) = true := by
  unfold groundPairCode at hground ⊢
  rw [Bool.and_eq_true] at hground ⊢
  constructor
  · apply (RegularTerm.groundCode_eq_true_iff g.ranks _).mpr
    exact hgroundSteps.ground_of_run
      ((RegularTerm.groundCode_eq_true_iff g.ranks _).mp hground.1)
      (path.left_run n)
  · apply (RegularTerm.groundCode_eq_true_iff g.ranks _).mpr
    exact hgroundSteps.ground_of_run
      ((RegularTerm.groundCode_eq_true_iff g.ranks _).mp hground.2)
      (path.right_run n)

/-- Every recorded residual pair is derivable under the empty basis at its
accumulated path word. -/
public theorem TracePath.pair_derivable
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    (path : TracePath g initialLeft initialRight)
    (hgroundSteps : g.PreservesGroundSteps)
    (hground : g.groundPairCode initialLeft initialRight = true)
    (hinitial : g.TraceEquivalent initialLeft initialRight) (n : ℕ) :
    CertificateDerivable g initialLeft initialRight []
      (.pair (path.word n) (path.left n) (path.right n)) := by
  induction n with
  | zero => simpa [path.starts_word, path.starts_left, path.starts_right] using
      (CertificateDerivable.axiom (basis := ([] : List BasisPair)) hground)
  | succ n ih =>
      obtain ⟨label, hword, hleft, hright⟩ := path.step n
      have hequivalent := path.residual_traceEquivalent hinitial n
      have happrox : g.traceApproxCode 1 (path.left n) (path.right n) = true := by
        apply (g.traceApproxCode_eq_true_iff 1 _ _).mpr
        exact (g.traceEquivalent_iff_forall_traceApprox _ _).mp
          hequivalent 1
      have hnextGround := path.residual_ground hgroundSteps hground (n + 1)
      rw [hword]
      exact CertificateDerivable.transition ih happrox hleft hright hnextGround

end EncodedFirstOrderGrammar

end DCFEquivalence
