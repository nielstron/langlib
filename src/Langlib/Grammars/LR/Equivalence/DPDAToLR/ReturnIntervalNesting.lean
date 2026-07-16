module

public import Langlib.Automata.DeterministicPushdown.Basics.Determinism
public import Langlib.Grammars.LR.Equivalence.DPDAToLR.RetainedFrameRun
public import Langlib.Grammars.LR.Equivalence.DPDAToLR.UsefulCycles

/-!
# Nesting of retained pushdown return intervals

A run which removes one displayed stack symbol while retaining the suffix
below it is a return interval.  Two such intervals on one deterministic run
may be disjoint or nested, but cannot strictly cross before a productive
continuation.  At a putative crossing, each interval boundary occurs inside
the other retained-frame run.  The resulting two suffix equations force the
retained frames to coincide, leaving a nonempty cycle at the common return
configuration.
-/

@[expose]
public section

open PDA

namespace DPDA

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

private theorem reachesIn_trans_exact
    {P : PDA Q T S} {n m : ℕ} {a b c : PDA.conf P}
    (hab : P.ReachesIn n a b) (hbc : P.ReachesIn m b c) :
    P.ReachesIn (n + m) a c := by
  induction hbc with
  | refl => simpa using hab
  | @step m b middle c hprefix hlast ih =>
      simpa [Nat.add_assoc] using PDA.ReachesIn.step (ih hab) hlast

private theorem transGen_of_reachesIn_pos
    {P : PDA Q T S} {n : ℕ} {a b : PDA.conf P}
    (hn : 0 < n) (h : P.ReachesIn n a b) :
    Relation.TransGen (@PDA.Reaches₁ Q T S _ _ _ P) a b := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  obtain ⟨middle, hfirst, hrest⟩ :=
    PDA.reachesIn_iff_split_first.mpr (by simpa [Nat.add_comm] using h)
  exact Relation.TransGen.head'
    (PDA.reaches₁_iff_reachesIn_one.mpr hfirst)
    (PDA.reaches_of_reachesIn hrest)

/-- A retained-frame computation which starts directly at its retained
frame has length zero: a PDA has no step from the corresponding stripped
empty stack. -/
private theorem retainedFrameRun_eq_zero_of_start_stack
    {P : PDA Q T S} {frame : List S} {n : ℕ}
    {c d : PDA.conf P}
    (h : PDA.RetainedFrameRun P frame n c d)
    (hc : c.stack = frame) : n = 0 := by
  induction h with
  | refl => rfl
  | @step n start q' p input' output upper upper' run last ih =>
      have hn : n = 0 := ih hc
      subst n
      have hmiddle := PDA.reachesIn_zero run.toReachesIn
      have hstack := congrArg PDA.conf.stack hmiddle
      have hupper : upper = [] := by
        apply List.append_cancel_right (bs := frame)
        simpa [hc] using hstack.symm
      subst upper
      simpa [PDA.Reaches₁, PDA.step] using last

public theorem retainedFrameRun_eq_zero_of_start_at_frame
    {P : PDA Q T S} {frame : List S} {n : ℕ}
    {q : Q} {input : List T} {d : PDA.conf P}
    (h : PDA.RetainedFrameRun P frame n
      ⟨q, input, frame⟩ d) : n = 0 :=
  retainedFrameRun_eq_zero_of_start_stack h rfl

/-- Two one-symbol net-pop intervals on a deterministic run cannot strictly
cross before a productive empty-stack continuation.

The first interval starts after `n` steps and lasts `a + b` steps.  The
second starts after `n + a` steps and lasts `b + c` steps.  Thus `b > 0`
places the second start strictly inside the first interval, while `c > 0`
places the second endpoint strictly after the first endpoint.  Both runs
retain their respective suffixes and return to the same state and input. -/
public theorem no_strictly_crossing_retained_returns (M : DPDA Q T S)
    {root : PDA.conf M.toPDA} {n a b c : ℕ}
    {q₁ q₂ returnState final : Q}
    {input₁ input₂ returnInput : List T}
    {Z₁ Z₂ : S} {frame₁ frame₂ : List S}
    (hprefix₁ : M.toPDA.ReachesIn n root
      ⟨q₁, input₁, Z₁ :: frame₁⟩)
    (hreturn₁ : PDA.RetainedFrameRun M.toPDA frame₁ (a + b)
      ⟨q₁, input₁, Z₁ :: frame₁⟩
      ⟨returnState, returnInput, frame₁⟩)
    (hprefix₂ : M.toPDA.ReachesIn (n + a) root
      ⟨q₂, input₂, Z₂ :: frame₂⟩)
    (hreturn₂ : PDA.RetainedFrameRun M.toPDA frame₂ (b + c)
      ⟨q₂, input₂, Z₂ :: frame₂⟩
      ⟨returnState, returnInput, frame₂⟩)
    (hb : 0 < b) (hc : 0 < c)
    (huseful : M.toPDA.Reaches
      ⟨returnState, returnInput, frame₂⟩ ⟨final, [], []⟩) :
    False := by
  obtain ⟨insideState₁, insideInput₁, upper₁,
      hbefore₁, hafter₁⟩ := hreturn₁.split_add
  have hatSecondStart :
      (⟨insideState₁, insideInput₁, upper₁ ++ frame₁⟩ :
          PDA.conf M.toPDA) =
        ⟨q₂, input₂, Z₂ :: frame₂⟩ := by
    exact M.toPDA_reachesIn_deterministic
      (reachesIn_trans_exact hprefix₁ hbefore₁.toReachesIn)
      hprefix₂
  have hupper₁ : upper₁ ≠ [] := by
    intro hempty
    subst upper₁
    have hzero := retainedFrameRun_eq_zero_of_start_at_frame hafter₁
    omega
  obtain ⟨insideState₂, insideInput₂, upper₂,
      hbefore₂, hafter₂⟩ := hreturn₂.split_add
  have hatFirstReturn :
      (⟨insideState₂, insideInput₂, upper₂ ++ frame₂⟩ :
          PDA.conf M.toPDA) =
        ⟨returnState, returnInput, frame₁⟩ := by
    have hleft : M.toPDA.ReachesIn (n + a + b) root
        ⟨insideState₂, insideInput₂, upper₂ ++ frame₂⟩ :=
      reachesIn_trans_exact hprefix₂ hbefore₂.toReachesIn
    have hright : M.toPDA.ReachesIn (n + (a + b)) root
        ⟨returnState, returnInput, frame₁⟩ :=
      reachesIn_trans_exact hprefix₁ hreturn₁.toReachesIn
    exact M.toPDA_reachesIn_deterministic (by
      simpa [Nat.add_assoc] using hleft) hright
  have hstackStart := congrArg PDA.conf.stack hatSecondStart
  have hstackReturn := congrArg PDA.conf.stack hatFirstReturn
  change upper₁ ++ frame₁ = Z₂ :: frame₂ at hstackStart
  change upper₂ ++ frame₂ = frame₁ at hstackReturn
  have hlengthStart := congrArg List.length hstackStart
  have hlengthReturn := congrArg List.length hstackReturn
  simp only [List.length_append, List.length_cons] at hlengthStart hlengthReturn
  have hupper₁Length : upper₁.length = 1 := by
    have hpositive : 0 < upper₁.length :=
      List.length_pos_of_ne_nil hupper₁
    omega
  have hupper₂Length : upper₂.length = 0 := by omega
  have hupper₂ : upper₂ = [] := List.length_eq_zero_iff.mp hupper₂Length
  subst upper₂
  have hframe : frame₂ = frame₁ := by simpa using hstackReturn
  subst frame₂
  have hcycleIn : M.toPDA.ReachesIn c
      ⟨returnState, returnInput, frame₁⟩
      ⟨returnState, returnInput, frame₁⟩ := by
    have hcycleIn' := hafter₂.toReachesIn
    rw [hatFirstReturn] at hcycleIn'
    exact hcycleIn'
  have hcycle := transGen_of_reachesIn_pos hc hcycleIn
  exact M.toPDA_no_cycle_before_empty_stack hcycle huseful

end DPDA
