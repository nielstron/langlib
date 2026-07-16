module

public import Langlib.Automata.Pushdown.Definition

/-!
# Counted PDA runs retaining a stack frame

`PDA.RetainedFrameRun P frame n c d` records a selected counted run whose
steps all occur strictly above the unchanged stack suffix `frame`.  Each step
stores its frame-free source and target; the indexed configurations are the
corresponding configurations with `frame` appended.  This is stronger than
bare reachability in a nondeterministic PDA and permits the retained frame to
be replaced uniformly.
-/

@[expose]
public section

namespace PDA

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

/-- A counted run together with a selected stack suffix which no step
examines or changes. -/
public inductive RetainedFrameRun (P : PDA Q T S) (frame : List S) :
    ℕ → conf P → conf P → Prop
  | refl (q : Q) (input : List T) (upper : List S) :
      RetainedFrameRun P frame 0
        ⟨q, input, upper ++ frame⟩ ⟨q, input, upper ++ frame⟩
  | step {n : ℕ} {start : conf P}
      {q p : Q} {input output : List T} {upper upper' : List S}
      (run : RetainedFrameRun P frame n start
        ⟨q, input, upper ++ frame⟩)
      (last : P.Reaches₁ ⟨q, input, upper⟩ ⟨p, output, upper'⟩) :
      RetainedFrameRun P frame (n + 1) start
        ⟨p, output, upper' ++ frame⟩

/-- Exact one-step stack locality.  Unlike the legacy
`PDA.Reaches₁.append_stack`, an impossible empty-stack source does not turn
the statement into a reflexive reachability result. -/
private theorem reaches₁_append_stack_exact
    {P : PDA Q T S} {c d : conf P}
    (h : P.Reaches₁ c d) (suffix : List S) :
    P.Reaches₁ (c.appendStack suffix) (d.appendStack suffix) := by
  rcases c with ⟨q, input, stack⟩
  cases stack with
  | nil => simp [PDA.Reaches₁, PDA.step] at h
  | cons Z rest =>
      rcases PDA.reaches₁_push h with
          ⟨a, tail, next, replacement, rfl, rfl, htransition⟩ |
          ⟨next, replacement, rfl, htransition⟩
      · exact Or.inl ⟨next, replacement, htransition, by
          simp [PDA.conf.appendStack, List.append_assoc]⟩
      · cases input with
        | nil =>
            exact ⟨next, replacement, htransition, by
              simp [PDA.conf.appendStack, List.append_assoc]⟩
        | cons a tail =>
            exact Or.inr ⟨next, replacement, htransition, by
              simp [PDA.conf.appendStack, List.append_assoc]⟩

/-- Forgetting the retained-frame certificate gives the corresponding
counted run of the original PDA. -/
public theorem RetainedFrameRun.toReachesIn
    {P : PDA Q T S} {frame : List S} {n : ℕ} {c d : conf P}
    (h : RetainedFrameRun P frame n c d) : P.ReachesIn n c d := by
  induction h with
  | refl => exact PDA.ReachesIn.refl _
  | step run last ih =>
      exact PDA.ReachesIn.step ih
        (reaches₁_append_stack_exact last frame)

/-- Append an untouched input suffix uniformly to a retained-frame run. -/
public theorem RetainedFrameRun.appendInput
    {P : PDA Q T S} {frame : List S} {n : ℕ} {c d : conf P}
    (h : RetainedFrameRun P frame n c d) (suffix : List T) :
    RetainedFrameRun P frame n (c.appendInput suffix)
      (d.appendInput suffix) := by
  induction h with
  | refl q input upper =>
      exact RetainedFrameRun.refl q (input ++ suffix) upper
  | @step n start q p input output upper upper' run last ih =>
      have last' : P.Reaches₁
          ((⟨q, input, upper⟩ : conf P).appendInput suffix)
          ((⟨p, output, upper'⟩ : conf P).appendInput suffix) := by
        apply PDA.reaches₁_iff_reachesIn_one.mpr
        exact (PDA.unconsumed_input_N (pda := P) suffix).mp
          (PDA.reaches₁_iff_reachesIn_one.mp last)
      simpa [conf.appendInput] using RetainedFrameRun.step ih last'

/-- Any counted run can be lifted under an arbitrary retained stack frame. -/
public theorem RetainedFrameRun.ofReachesIn
    {P : PDA Q T S} {frame : List S} {n : ℕ} {c d : conf P}
    (h : P.ReachesIn n c d) :
    RetainedFrameRun P frame n (c.appendStack frame)
      (d.appendStack frame) := by
  induction h with
  | refl => exact RetainedFrameRun.refl _ _ _
  | step run last ih =>
      exact RetainedFrameRun.step ih last

/-- `reframing old new c c'` replaces the selected suffix `old` of `c` by
`new`, preserving the control state, input, and the stack prefix above it. -/
private def reframing (old new : List S) {P : PDA Q T S}
    (c c' : conf P) : Prop :=
  c.state = c'.state ∧ c.input = c'.input ∧
    ∃ upper : List S,
      c.stack = upper ++ old ∧ c'.stack = upper ++ new

private theorem RetainedFrameRun.changeFrame_exists
    {P : PDA Q T S} {frame newFrame : List S}
    {n : ℕ} {c d : conf P}
    (h : RetainedFrameRun P frame n c d) :
    ∃ c' d' : conf P,
      reframing frame newFrame c c' ∧
      reframing frame newFrame d d' ∧
      RetainedFrameRun P newFrame n c' d' := by
  induction h with
  | refl q input upper =>
      exact ⟨⟨q, input, upper ++ newFrame⟩,
        ⟨q, input, upper ++ newFrame⟩,
        ⟨rfl, rfl, upper, rfl, rfl⟩,
        ⟨rfl, rfl, upper, rfl, rfl⟩,
        RetainedFrameRun.refl q input upper⟩
  | @step n start q p input output upper upper' run last ih =>
      obtain ⟨start', middle', hstart, hmiddle, run'⟩ := ih
      rcases middle' with ⟨middleState, middleInput, middleStack⟩
      rcases hmiddle with
        ⟨hstate, hinput, savedUpper, hsavedOld, hsavedNew⟩
      change q = middleState at hstate
      change input = middleInput at hinput
      change upper ++ frame = savedUpper ++ frame at hsavedOld
      change middleStack = savedUpper ++ newFrame at hsavedNew
      have hsavedUpper : savedUpper = upper :=
        (List.append_cancel_right hsavedOld).symm
      subst middleState
      subst middleInput
      subst savedUpper
      subst middleStack
      exact ⟨start', ⟨p, output, upper' ++ newFrame⟩,
        hstart, ⟨rfl, rfl, upper', rfl, rfl⟩,
        RetainedFrameRun.step run' last⟩

/-- Replace the untouched suffix of a retained-frame run. -/
public theorem RetainedFrameRun.changeFrame
    {P : PDA Q T S} {frame : List S} {n : ℕ}
    {q p : Q} {input output : List T} {upper upper' : List S}
    (h : RetainedFrameRun P frame n
      ⟨q, input, upper ++ frame⟩ ⟨p, output, upper' ++ frame⟩)
    (newFrame : List S) :
    RetainedFrameRun P newFrame n
      ⟨q, input, upper ++ newFrame⟩
      ⟨p, output, upper' ++ newFrame⟩ := by
  obtain ⟨start, finish, hstart, hfinish, run⟩ :=
    h.changeFrame_exists (newFrame := newFrame)
  rcases start with ⟨startState, startInput, startStack⟩
  rcases hstart with
    ⟨hstartState, hstartInput, savedStart, hstartOld, hstartNew⟩
  change q = startState at hstartState
  change input = startInput at hstartInput
  change upper ++ frame = savedStart ++ frame at hstartOld
  change startStack = savedStart ++ newFrame at hstartNew
  have hsavedStart : savedStart = upper :=
    (List.append_cancel_right hstartOld).symm
  subst startState
  subst startInput
  subst savedStart
  subst startStack
  rcases finish with ⟨finishState, finishInput, finishStack⟩
  rcases hfinish with
    ⟨hfinishState, hfinishInput, savedFinish, hfinishOld, hfinishNew⟩
  change p = finishState at hfinishState
  change output = finishInput at hfinishInput
  change upper' ++ frame = savedFinish ++ frame at hfinishOld
  change finishStack = savedFinish ++ newFrame at hfinishNew
  have hsavedFinish : savedFinish = upper' :=
    (List.append_cancel_right hfinishOld).symm
  subst finishState
  subst finishInput
  subst savedFinish
  subst finishStack
  exact run

/-- The final configuration of a retained-frame run exposes its retained
suffix. -/
public theorem RetainedFrameRun.end_shape
    {P : PDA Q T S} {frame : List S} {n : ℕ} {c d : conf P}
    (h : RetainedFrameRun P frame n c d) :
    ∃ (q : Q) (input : List T) (upper : List S),
      d = ⟨q, input, upper ++ frame⟩ := by
  cases h with
  | refl q input upper => exact ⟨q, input, upper, rfl⟩
  | step run last => exact ⟨_, _, _, rfl⟩

private theorem RetainedFrameRun.eq_zero_of_start_stack
    {P : PDA Q T S} {frame : List S} {n : ℕ} {start finish : conf P}
    (h : RetainedFrameRun P frame n start finish)
    (hstack : start.stack = frame) : n = 0 := by
  induction h with
  | refl => rfl
  | @step n start middleState finalState middleInput finalInput
      upper upper' run last ih =>
      have hn : n = 0 := ih hstack
      subst n
      have hmiddle := PDA.reachesIn_zero run.toReachesIn
      have hupper : upper = [] := by
        apply List.append_cancel_right (bs := frame)
        simpa [hstack] using congrArg conf.stack hmiddle
      subst upper
      simpa [PDA.Reaches₁, PDA.step] using last

/-- A retained-frame run starting with no stack above its retained suffix is
necessarily reflexive: a PDA has no transition from the corresponding
stripped empty-stack configuration. -/
public theorem RetainedFrameRun.eq_zero_of_start_at_frame
    {P : PDA Q T S} {frame : List S} {n : ℕ}
    {q : Q} {input : List T} {finish : conf P}
    (h : RetainedFrameRun P frame n ⟨q, input, frame⟩ finish) :
    n = 0 :=
  h.eq_zero_of_start_stack rfl

/-- Split a retained-frame run at an exact step count.  The intermediate
configuration exposes the same retained suffix. -/
public theorem RetainedFrameRun.split_add
    {P : PDA Q T S} {frame : List S} {n m : ℕ} {c d : conf P}
    (h : RetainedFrameRun P frame (n + m) c d) :
    ∃ (q : Q) (input : List T) (upper : List S),
      RetainedFrameRun P frame n c ⟨q, input, upper ++ frame⟩ ∧
      RetainedFrameRun P frame m ⟨q, input, upper ++ frame⟩ d := by
  induction m generalizing d with
  | zero =>
      obtain ⟨q, input, upper, rfl⟩ := h.end_shape
      exact ⟨q, input, upper, by simpa using h,
        RetainedFrameRun.refl q input upper⟩
  | succ m ih =>
      rw [Nat.add_succ] at h
      cases h with
      | step run last =>
          obtain ⟨q, input, upper, left, right⟩ := ih run
          exact ⟨q, input, upper, left,
            RetainedFrameRun.step right last⟩

end PDA
