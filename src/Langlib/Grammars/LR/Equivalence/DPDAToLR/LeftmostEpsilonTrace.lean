module

public import Langlib.Grammars.LR.Equivalence.DPDAToLR.CrossInputStep
public import Langlib.Grammars.LR.Equivalence.DPDAToLR.RetainedFrameRun
public import Langlib.Grammars.LR.Equivalence.DPDAToLR.VisibleAnchorSemantics

/-!
# Forward traces of zero-visible leftmost descent

A zero-visible grammar tail alternates cost-free structural changes with
epsilon transitions of the normalized empty-stack PDA.  The grammar target
state is irrelevant to the physical cut, but the boundary between the
displayed stack and the hidden zipper context is essential.  The positions
below retain exactly that boundary.
-/

@[expose]
public section

open Language PDA

namespace DPDA_to_LR

noncomputable section

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

/-- Physical position of a zero-visible leftmost descent.  Grammar return
targets are omitted; displayed stack and hidden context remain separate. -/
public inductive LeftmostEpsilonPosition (M : DPDA Q T S)
  | root
  | single (state : State M) (top : StackSymbol M)
      (context : List (StackSymbol M))
  | list (state : State M) (displayed : List (StackSymbol M))
      (context : List (StackSymbol M))

/-- The concrete PDA configuration represented by a position on a chosen
unconsumed input tail. -/
@[expose]
public def LeftmostEpsilonPosition.conf (M : DPDA Q T S)
    (input : List T) : LeftmostEpsilonPosition M →
      PDA.conf (emptyStackPDA M)
  | .root =>
      ⟨(emptyStackPDA M).initial_state, input,
        [(emptyStackPDA M).start_symbol]⟩
  | .single q Z context => ⟨q, input, Z :: context⟩
  | .list q gamma context => ⟨q, input, gamma ++ context⟩

/-- Forget the target-state index of a characteristic nonterminal while
retaining its physical displayed-stack boundary. -/
@[expose]
public def leftmostEpsilonPositionOf (M : DPDA Q T S)
    (A : Nonterminal M) (context : List (StackSymbol M)) :
    LeftmostEpsilonPosition M :=
  match A with
  | PDA_to_CFG.N.start => .root
  | PDA_to_CFG.N.single q Z _ => .single q Z context
  | PDA_to_CFG.N.list q gamma _ => .list q gamma context

/-- Forgetting the grammar target preserves the exact concrete cut. -/
public theorem leftmostEpsilonPositionOf_conf (M : DPDA Q T S)
    (A : Nonterminal M) (context : List (StackSymbol M)) (input : List T) :
    (leftmostEpsilonPositionOf M A context).conf M input =
      ⟨spineCutState M A, input, spineCutStack M A context⟩ := by
  cases A <;> rfl

/-- One forward zero-visible event.  `start` and `split` only change the
grammar view of a physical cut; `epsilon` is one actual PDA step. -/
public inductive LeftmostEpsilonStep (M : DPDA Q T S) :
    LeftmostEpsilonPosition M → LeftmostEpsilonPosition M → Prop
  | start : LeftmostEpsilonStep M .root
      (.list (emptyStackPDA M).initial_state
        [(emptyStackPDA M).start_symbol] [])
  | split
      {q : State M} {Z : StackSymbol M}
      {gamma context : List (StackSymbol M)} :
      LeftmostEpsilonStep M (.list q (Z :: gamma) context)
        (.single q Z (gamma ++ context))
  | epsilon
      {q next : State M} {Z : StackSymbol M}
      {replacement context : List (StackSymbol M)}
      (transition : (next, replacement) ∈
        (emptyStackPDA M).transition_fun' q Z) :
      LeftmostEpsilonStep M (.single q Z context)
        (.list next replacement context)

/-- Forward reflexive-transitive closure, oriented so induction exposes the
first structural event. -/
public inductive LeftmostEpsilonTrace (M : DPDA Q T S) :
    LeftmostEpsilonPosition M → LeftmostEpsilonPosition M → Prop
  | refl (position : LeftmostEpsilonPosition M) :
      LeftmostEpsilonTrace M position position
  | head {start middle finish : LeftmostEpsilonPosition M}
      (first : LeftmostEpsilonStep M start middle)
      (rest : LeftmostEpsilonTrace M middle finish) :
      LeftmostEpsilonTrace M start finish

/-- Append one structural event to a forward trace. -/
public theorem LeftmostEpsilonTrace.snoc (M : DPDA Q T S)
    {start middle finish : LeftmostEpsilonPosition M}
    (trace : LeftmostEpsilonTrace M start middle)
    (last : LeftmostEpsilonStep M middle finish) :
    LeftmostEpsilonTrace M start finish := by
  induction trace with
  | refl => exact .head last (.refl _)
  | head first rest ih => exact .head first (ih last)

/-- A zero-visible tail forgets to a forward leftmost trace. -/
public theorem ZeroVisibleTail.leftmostEpsilonTrace
    (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {preWord : List T}
    {anchor current : Nonterminal M}
    {anchorSuffix currentSuffix : List T}
    {anchorContext currentContext : List (StackSymbol M)}
    (h : ZeroVisibleTail M p preWord anchor anchorSuffix anchorContext
      current currentSuffix currentContext) :
    LeftmostEpsilonTrace M
      (leftmostEpsilonPositionOf M anchor anchorContext)
      (leftmostEpsilonPositionOf M current currentContext) := by
  induction h with
  | refl => exact .refl _
  | start previous hrule ih =>
      simpa [leftmostEpsilonPositionOf] using ih.snoc M .start
  | epsilon previous transition hrule ih =>
      simpa [leftmostEpsilonPositionOf] using
        ih.snoc M (.epsilon transition)
  | splitLeft previous hlength hrule hright ih =>
      simpa [leftmostEpsilonPositionOf] using ih.snoc M .split

/-- Every structural event is ordinary reachability on any fixed input tail.
The two grammar-only events are literal equality of physical cuts. -/
public theorem LeftmostEpsilonStep.reaches (M : DPDA Q T S)
    {start finish : LeftmostEpsilonPosition M}
    (step : LeftmostEpsilonStep M start finish) (input : List T) :
    (emptyStackPDA M).Reaches (start.conf M input) (finish.conf M input) := by
  cases step with
  | start =>
      change (emptyStackPDA M).Reaches
        ⟨(emptyStackPDA M).initial_state, input,
          [(emptyStackPDA M).start_symbol]⟩
        ⟨(emptyStackPDA M).initial_state, input,
          [(emptyStackPDA M).start_symbol]⟩
      exact Relation.ReflTransGen.refl
  | @split q Z gamma context =>
      change (emptyStackPDA M).Reaches
        ⟨q, input, Z :: gamma ++ context⟩
        ⟨q, input, Z :: (gamma ++ context)⟩
      simpa using (Relation.ReflTransGen.refl : (emptyStackPDA M).Reaches
        ⟨q, input, Z :: gamma ++ context⟩
        ⟨q, input, Z :: gamma ++ context⟩)
  | @epsilon q next Z replacement context transition =>
      have hcore : (emptyStackPDA M).Reaches₁
          ⟨q, [], Z :: context⟩
          ⟨next, [], replacement ++ context⟩ :=
        ⟨next, replacement, transition, by simp⟩
      have hstep : (emptyStackPDA M).Reaches₁
          ⟨q, input, Z :: context⟩
          ⟨next, input, replacement ++ context⟩ := by
        apply PDA.reaches₁_iff_reachesIn_one.mpr
        have hlift := (PDA.unconsumed_input_N
          (pda := emptyStackPDA M) input).mp
          (PDA.reaches₁_iff_reachesIn_one.mp hcore)
        simpa [PDA.conf.appendInput] using hlift
      exact Relation.ReflTransGen.single hstep

/-- Operational realization of a complete forward trace. -/
public theorem LeftmostEpsilonTrace.reaches (M : DPDA Q T S)
    {start finish : LeftmostEpsilonPosition M}
    (trace : LeftmostEpsilonTrace M start finish) (input : List T) :
    (emptyStackPDA M).Reaches (start.conf M input) (finish.conf M input) := by
  induction trace with
  | refl => exact Relation.ReflTransGen.refl
  | head first rest ih => exact (first.reaches M input).trans ih

/-- Control state carried by a leftmost epsilon position. -/
@[expose]
public def LeftmostEpsilonPosition.state' (M : DPDA Q T S) :
    LeftmostEpsilonPosition M → State M
  | .root => (emptyStackPDA M).initial_state
  | .single q _ _ => q
  | .list q _ _ => q

/-- Stack prefix displayed by a leftmost epsilon position. -/
@[expose]
public def LeftmostEpsilonPosition.upper (M : DPDA Q T S) :
    LeftmostEpsilonPosition M → List (StackSymbol M)
  | .root => [(emptyStackPDA M).start_symbol]
  | .single _ Z _ => [Z]
  | .list _ gamma _ => gamma

/-- Hidden stack context carried below a leftmost epsilon position. -/
@[expose]
public def LeftmostEpsilonPosition.context' (M : DPDA Q T S) :
    LeftmostEpsilonPosition M → List (StackSymbol M)
  | .root => []
  | .single _ _ context => context
  | .list _ _ context => context

/-- At empty input a position is its displayed prefix followed by its hidden
context. -/
public theorem LeftmostEpsilonPosition.conf_nil_eq (M : DPDA Q T S)
    (position : LeftmostEpsilonPosition M) :
    position.conf M [] =
      ⟨position.state' M, [], position.upper M ++ position.context' M⟩ := by
  cases position <;> simp [LeftmostEpsilonPosition.conf,
    LeftmostEpsilonPosition.state', LeftmostEpsilonPosition.upper,
    LeftmostEpsilonPosition.context']

/-- Concatenate two runs which retain the same stack frame. -/
public theorem retainedFrameRun_trans
    {P : PDA Q T S} {frame : List S} {n m : ℕ} {a b c : PDA.conf P}
    (h₁ : PDA.RetainedFrameRun P frame n a b)
    (h₂ : PDA.RetainedFrameRun P frame m b c) :
    PDA.RetainedFrameRun P frame (n + m) a c := by
  induction h₂ with
  | refl => simpa using h₁
  | step run last ih =>
      simpa [Nat.add_assoc] using PDA.RetainedFrameRun.step (ih h₁) last

/-- Every structural step preserves any selected suffix of the hidden
context.  The returned prefix records what was added above that suffix. -/
public theorem LeftmostEpsilonStep.retainedFrameRun
    (M : DPDA Q T S)
    {start finish : LeftmostEpsilonPosition M}
    (step : LeftmostEpsilonStep M start finish)
    {frame added : List (StackSymbol M)}
    (hcontext : start.context' M = added ++ frame) :
    ∃ (n : ℕ) (added' : List (StackSymbol M)),
      finish.context' M = added' ++ frame ∧
      PDA.RetainedFrameRun (emptyStackPDA M) frame n
        (start.conf M []) (finish.conf M []) := by
  cases step with
  | start =>
      have hframe : frame = [] := by
        simpa [LeftmostEpsilonPosition.context'] using
          (List.append_eq_nil_iff.mp hcontext.symm).2
      subst frame
      refine ⟨0, [], by simp [LeftmostEpsilonPosition.context'], ?_⟩
      simpa [LeftmostEpsilonPosition.conf] using
        (PDA.RetainedFrameRun.refl
          (P := emptyStackPDA M) (frame := [])
          (emptyStackPDA M).initial_state []
          [(emptyStackPDA M).start_symbol])
  | @split q Z gamma context =>
      change context = added ++ frame at hcontext
      refine ⟨0, gamma ++ added, ?_, ?_⟩
      · simp [LeftmostEpsilonPosition.context', hcontext,
          List.append_assoc]
      · rw [LeftmostEpsilonPosition.conf_nil_eq,
          LeftmostEpsilonPosition.conf_nil_eq]
        simpa [LeftmostEpsilonPosition.state',
          LeftmostEpsilonPosition.upper,
          LeftmostEpsilonPosition.context', hcontext,
          List.append_assoc] using
          (PDA.RetainedFrameRun.refl
            (P := emptyStackPDA M) (frame := frame) q []
            (Z :: gamma ++ added))
  | @epsilon q next Z replacement context transition =>
      change context = added ++ frame at hcontext
      subst context
      refine ⟨1, added, ?_, ?_⟩
      · simp [LeftmostEpsilonPosition.context']
      · have core : (emptyStackPDA M).Reaches₁
            ⟨q, [], Z :: added⟩ ⟨next, [], replacement ++ added⟩ := by
          exact ⟨next, replacement, transition, by simp⟩
        rw [LeftmostEpsilonPosition.conf_nil_eq,
          LeftmostEpsilonPosition.conf_nil_eq]
        simpa [LeftmostEpsilonPosition.state',
          LeftmostEpsilonPosition.upper,
          LeftmostEpsilonPosition.context',
          List.append_assoc] using
          (PDA.RetainedFrameRun.step
            (PDA.RetainedFrameRun.refl
              (P := emptyStackPDA M) (frame := frame) q [] (Z :: added))
            core)

/-- A whole leftmost epsilon trace preserves any selected suffix of the
starting hidden context. -/
public theorem LeftmostEpsilonTrace.retainedFrameRun
    (M : DPDA Q T S)
    {start finish : LeftmostEpsilonPosition M}
    (trace : LeftmostEpsilonTrace M start finish)
    {frame added : List (StackSymbol M)}
    (hcontext : start.context' M = added ++ frame) :
    ∃ (n : ℕ) (added' : List (StackSymbol M)),
      finish.context' M = added' ++ frame ∧
      PDA.RetainedFrameRun (emptyStackPDA M) frame n
        (start.conf M []) (finish.conf M []) := by
  induction trace generalizing added with
  | refl position =>
      refine ⟨0, added, hcontext, ?_⟩
      rw [position.conf_nil_eq]
      simpa [hcontext, List.append_assoc] using
        (PDA.RetainedFrameRun.refl
          (P := emptyStackPDA M) (frame := frame)
          (position.state' M) [] (position.upper M ++ added))
  | @head start middle finish first rest ih =>
      obtain ⟨n₁, added₁, hmiddle, run₁⟩ :=
        first.retainedFrameRun M hcontext
      obtain ⟨n₂, added₂, hfinish, run₂⟩ := ih hmiddle
      exact ⟨n₁ + n₂, added₂, hfinish,
        retainedFrameRun_trans run₁ run₂⟩

/-- A trace beginning at a single-stack-symbol position retains its entire
hidden context. -/
public theorem LeftmostEpsilonTrace.fromSingle_exists_retainedFrameRun
    (M : DPDA Q T S)
    {q : State M} {Z : StackSymbol M}
    {context : List (StackSymbol M)}
    {finish : LeftmostEpsilonPosition M}
    (trace : LeftmostEpsilonTrace M (.single q Z context) finish) :
    ∃ (n : ℕ) (added : List (StackSymbol M)),
      finish.context' M = added ++ context ∧
      PDA.RetainedFrameRun (emptyStackPDA M) context n
        ((.single q Z context : LeftmostEpsilonPosition M).conf M [])
        (finish.conf M []) := by
  exact trace.retainedFrameRun M (frame := context) (added := [])
    (by simp [LeftmostEpsilonPosition.context'])

/-- Two productive forward zero-visible traces from one structural position
are prefix-comparable.  The endpoints and the untouched input tails may
differ; one-symbol lookahead and global usefulness synchronize every actual
epsilon transition, while `start` and `split` align definitionally. -/
public theorem leftmostEpsilonTrace_productive_comparable
    (M : DPDA Q T S)
    {start finish₁ finish₂ : LeftmostEpsilonPosition M}
    {final₁ final₂ : State M}
    {suffix₁ suffix₂ whole₁ whole₂ : List T}
    (trace₁ : LeftmostEpsilonTrace M start finish₁)
    (trace₂ : LeftmostEpsilonTrace M start finish₂)
    (global₁ : (emptyStackPDA M).Reaches
      ⟨(emptyStackPDA M).initial_state, whole₁,
        [(emptyStackPDA M).start_symbol]⟩
      (start.conf M suffix₁))
    (global₂ : (emptyStackPDA M).Reaches
      ⟨(emptyStackPDA M).initial_state, whole₂,
        [(emptyStackPDA M).start_symbol]⟩
      (start.conf M suffix₂))
    (useful₁ : (emptyStackPDA M).Reaches
      (finish₁.conf M suffix₁) ⟨final₁, [], []⟩)
    (useful₂ : (emptyStackPDA M).Reaches
      (finish₂.conf M suffix₂) ⟨final₂, [], []⟩)
    (hlook : suffix₁.take 1 = suffix₂.take 1) :
    LeftmostEpsilonTrace M finish₁ finish₂ ∨
      LeftmostEpsilonTrace M finish₂ finish₁ := by
  induction trace₁ generalizing finish₂ whole₁ whole₂ with
  | refl position => exact Or.inl trace₂
  | @head start middle finish₁ first₁ rest₁ ih =>
      cases trace₂ with
      | refl => exact Or.inr (.head first₁ rest₁)
      | @head _ middle₂ finish₂ first₂ rest₂ =>
          cases first₁ <;> cases first₂
          case start.start =>
            exact ih rest₂ global₁ global₂ useful₁ useful₂
          case split.split =>
            apply ih rest₂
            · simpa [LeftmostEpsilonPosition.conf, List.append_assoc]
                using global₁
            · simpa [LeftmostEpsilonPosition.conf, List.append_assoc]
                using global₂
            · exact useful₁
            · exact useful₂
          case epsilon.epsilon =>
            rename_i q next₁ Z replacement₁ context transition₁
              next₂ replacement₂ transition₂
            have step₁ : (emptyStackPDA M).Reaches₁
                ⟨q, suffix₁, Z :: context⟩
                ⟨next₁, suffix₁, replacement₁ ++ context⟩ := by
              have hcore : (emptyStackPDA M).Reaches₁
                  ⟨q, [], Z :: context⟩
                  ⟨next₁, [], replacement₁ ++ context⟩ :=
                ⟨next₁, replacement₁, transition₁, by simp⟩
              apply PDA.reaches₁_iff_reachesIn_one.mpr
              have hlift := (PDA.unconsumed_input_N
                (pda := emptyStackPDA M) suffix₁).mp
                (PDA.reaches₁_iff_reachesIn_one.mp hcore)
              simpa [PDA.conf.appendInput] using hlift
            have step₂ : (emptyStackPDA M).Reaches₁
                ⟨q, suffix₂, Z :: context⟩
                ⟨next₂, suffix₂, replacement₂ ++ context⟩ := by
              have hcore : (emptyStackPDA M).Reaches₁
                  ⟨q, [], Z :: context⟩
                  ⟨next₂, [], replacement₂ ++ context⟩ :=
                ⟨next₂, replacement₂, transition₂, by simp⟩
              apply PDA.reaches₁_iff_reachesIn_one.mpr
              have hlift := (PDA.unconsumed_input_N
                (pda := emptyStackPDA M) suffix₂).mp
                (PDA.reaches₁_iff_reachesIn_one.mp hcore)
              simpa [PDA.conf.appendInput] using hlift
            have successorUseful₁ : (emptyStackPDA M).Reaches
                ⟨next₁, suffix₁, replacement₁ ++ context⟩
                ⟨final₁, [], []⟩ := by
              simpa [LeftmostEpsilonPosition.conf] using
                (rest₁.reaches M suffix₁).trans useful₁
            have successorUseful₂ : (emptyStackPDA M).Reaches
                ⟨next₂, suffix₂, replacement₂ ++ context⟩
                ⟨final₂, [], []⟩ := by
              simpa [LeftmostEpsilonPosition.conf] using
                (rest₂.reaches M suffix₂).trans useful₂
            obtain ⟨hnext, hstack, hinput⟩ :=
              emptyStack_globally_useful_step_cross_input M hlook
                (by simpa [LeftmostEpsilonPosition.conf] using global₁)
                (by simpa [LeftmostEpsilonPosition.conf] using global₂)
                step₁ step₂ successorUseful₁ successorUseful₂
            have hnext' : next₁ = next₂ := by simpa using hnext
            have hreplacement : replacement₁ = replacement₂ :=
              List.append_cancel_right hstack
            subst next₂
            subst replacement₂
            apply ih rest₂
            · simpa [LeftmostEpsilonPosition.conf] using global₁.tail step₁
            · simpa [LeftmostEpsilonPosition.conf] using global₂.tail step₂
            · exact useful₁
            · exact useful₂

private theorem leftmostEpsilonTrace_empty_position_unique
    (M : DPDA Q T S)
    {start finish₁ finish₂ : LeftmostEpsilonPosition M}
    {final₁ final₂ : State M}
    {suffix₁ suffix₂ whole₁ whole₂ : List T}
    (trace₁ : LeftmostEpsilonTrace M start finish₁)
    (trace₂ : LeftmostEpsilonTrace M start finish₂)
    (empty₁ : ∃ q context, finish₁ = .list q [] context)
    (empty₂ : ∃ q context, finish₂ = .list q [] context)
    (global₁ : (emptyStackPDA M).Reaches
      ⟨(emptyStackPDA M).initial_state, whole₁,
        [(emptyStackPDA M).start_symbol]⟩
      (start.conf M suffix₁))
    (global₂ : (emptyStackPDA M).Reaches
      ⟨(emptyStackPDA M).initial_state, whole₂,
        [(emptyStackPDA M).start_symbol]⟩
      (start.conf M suffix₂))
    (useful₁ : (emptyStackPDA M).Reaches
      (finish₁.conf M suffix₁)
      ⟨final₁, [], []⟩)
    (useful₂ : (emptyStackPDA M).Reaches
      (finish₂.conf M suffix₂)
      ⟨final₂, [], []⟩)
    (hlook : suffix₁.take 1 = suffix₂.take 1) :
    finish₁ = finish₂ := by
  induction trace₁ generalizing finish₂ whole₁ whole₂ with
  | refl position =>
      rcases empty₁ with ⟨q₁, context₁, rfl⟩
      cases trace₂ with
      | refl => rfl
      | head first rest => cases first
  | @head start middle finish first₁ rest₁ ih =>
      cases trace₂ with
      | refl =>
          rcases empty₂ with ⟨q₂, context₂, rfl⟩
          cases first₁
      | @head _ middle₂ _ first₂ rest₂ =>
          cases first₁ <;> cases first₂
          case start.start =>
            apply ih rest₂ empty₁ empty₂ global₁ global₂
              useful₁ useful₂
          case split.split =>
            apply ih rest₂ empty₁ empty₂
            · simpa [LeftmostEpsilonPosition.conf, List.append_assoc]
                using global₁
            · simpa [LeftmostEpsilonPosition.conf, List.append_assoc]
                using global₂
            · exact useful₁
            · exact useful₂
          case epsilon.epsilon =>
            rename_i q next₁ Z replacement₁ context transition₁
              next₂ replacement₂ transition₂
            have step₁ : (emptyStackPDA M).Reaches₁
                ⟨q, suffix₁, Z :: context⟩
                ⟨next₁, suffix₁, replacement₁ ++ context⟩ := by
              have hcore : (emptyStackPDA M).Reaches₁
                  ⟨q, [], Z :: context⟩
                  ⟨next₁, [], replacement₁ ++ context⟩ :=
                ⟨next₁, replacement₁, transition₁, by simp⟩
              apply PDA.reaches₁_iff_reachesIn_one.mpr
              have hlift := (PDA.unconsumed_input_N
                (pda := emptyStackPDA M) suffix₁).mp
                (PDA.reaches₁_iff_reachesIn_one.mp hcore)
              simpa [PDA.conf.appendInput] using hlift
            have step₂ : (emptyStackPDA M).Reaches₁
                ⟨q, suffix₂, Z :: context⟩
                ⟨next₂, suffix₂, replacement₂ ++ context⟩ := by
              have hcore : (emptyStackPDA M).Reaches₁
                  ⟨q, [], Z :: context⟩
                  ⟨next₂, [], replacement₂ ++ context⟩ :=
                ⟨next₂, replacement₂, transition₂, by simp⟩
              apply PDA.reaches₁_iff_reachesIn_one.mpr
              have hlift := (PDA.unconsumed_input_N
                (pda := emptyStackPDA M) suffix₂).mp
                (PDA.reaches₁_iff_reachesIn_one.mp hcore)
              simpa [PDA.conf.appendInput] using hlift
            have successorUseful₁ : (emptyStackPDA M).Reaches
                ⟨next₁, suffix₁, replacement₁ ++ context⟩
                ⟨final₁, [], []⟩ := by
              simpa [LeftmostEpsilonPosition.conf] using
                (rest₁.reaches M suffix₁).trans useful₁
            have successorUseful₂ : (emptyStackPDA M).Reaches
                ⟨next₂, suffix₂, replacement₂ ++ context⟩
                ⟨final₂, [], []⟩ := by
              simpa [LeftmostEpsilonPosition.conf] using
                (rest₂.reaches M suffix₂).trans useful₂
            obtain ⟨hnext, hstack, hinput⟩ :=
              emptyStack_globally_useful_step_cross_input M hlook
                (by simpa [LeftmostEpsilonPosition.conf] using global₁)
                (by simpa [LeftmostEpsilonPosition.conf] using global₂)
                step₁ step₂ successorUseful₁ successorUseful₂
            have hnext' : next₁ = next₂ := by simpa using hnext
            have hreplacement : replacement₁ = replacement₂ :=
              List.append_cancel_right hstack
            subst next₂
            subst replacement₂
            apply ih rest₂ empty₁ empty₂
            · simpa [LeftmostEpsilonPosition.conf] using global₁.tail step₁
            · simpa [LeftmostEpsilonPosition.conf] using global₂.tail step₂
            · exact useful₁
            · exact useful₂

/-- Productive zero-visible traces from the same structural position and
with the same one-symbol lookahead have the same empty-list return state.

The theorem is stronger than equal-count synchronization: the two traces may
contain different numbers of epsilon transitions.  Forward structural
induction rules this out before the displayed stack first becomes empty. -/
public theorem leftmostEpsilonTrace_empty_state_unique
    (M : DPDA Q T S)
    {start : LeftmostEpsilonPosition M}
    {q₁ q₂ final₁ final₂ : State M}
    {context₁ context₂ : List (StackSymbol M)}
    {suffix₁ suffix₂ whole₁ whole₂ : List T}
    (trace₁ : LeftmostEpsilonTrace M start (.list q₁ [] context₁))
    (trace₂ : LeftmostEpsilonTrace M start (.list q₂ [] context₂))
    (global₁ : (emptyStackPDA M).Reaches
      ⟨(emptyStackPDA M).initial_state, whole₁,
        [(emptyStackPDA M).start_symbol]⟩
      (start.conf M suffix₁))
    (global₂ : (emptyStackPDA M).Reaches
      ⟨(emptyStackPDA M).initial_state, whole₂,
        [(emptyStackPDA M).start_symbol]⟩
      (start.conf M suffix₂))
    (useful₁ : (emptyStackPDA M).Reaches
      ((.list q₁ [] context₁ : LeftmostEpsilonPosition M).conf M suffix₁)
      ⟨final₁, [], []⟩)
    (useful₂ : (emptyStackPDA M).Reaches
      ((.list q₂ [] context₂ : LeftmostEpsilonPosition M).conf M suffix₂)
      ⟨final₂, [], []⟩)
    (hlook : suffix₁.take 1 = suffix₂.take 1) :
    q₁ = q₂ := by
  have heq := leftmostEpsilonTrace_empty_position_unique M trace₁ trace₂
    ⟨q₁, context₁, rfl⟩ ⟨q₂, context₂, rfl⟩
    global₁ global₂ useful₁ useful₂ hlook
  injection heq

/-- If one productive epsilon parent is a structural descendant of another,
and both epsilon transitions enter the same displayed child, then their
exposed heads agree.  A strict descendant would make the child cut repeat
with either the same context or a nonempty inserted context, contradicting
usefulness in both cases. -/
private theorem
    leftmostEpsilonTrace_converging_epsilon_heads_eq_of_trace
    (M : DPDA Q T S)
    {q₁ q₂ next final₁ final₂ : State M}
    {Z₁ Z₂ : StackSymbol M}
    {gamma context₁ context₂ : List (StackSymbol M)}
    {suffix₁ suffix₂ whole₁ whole₂ : List T}
    (between : LeftmostEpsilonTrace M
      (.single q₁ Z₁ context₁) (.single q₂ Z₂ context₂))
    (transition₁ : (next, gamma) ∈
      (emptyStackPDA M).transition_fun' q₁ Z₁)
    (transition₂ : (next, gamma) ∈
      (emptyStackPDA M).transition_fun' q₂ Z₂)
    (global₁ : (emptyStackPDA M).Reaches
      ⟨(emptyStackPDA M).initial_state, whole₁,
        [(emptyStackPDA M).start_symbol]⟩
      ((.single q₁ Z₁ context₁ : LeftmostEpsilonPosition M).conf M
        suffix₁))
    (global₂ : (emptyStackPDA M).Reaches
      ⟨(emptyStackPDA M).initial_state, whole₂,
        [(emptyStackPDA M).start_symbol]⟩
      ((.single q₁ Z₁ context₁ : LeftmostEpsilonPosition M).conf M
        suffix₂))
    (useful₁ : (emptyStackPDA M).Reaches
      ((.list next gamma context₁ : LeftmostEpsilonPosition M).conf M
        suffix₁)
      ⟨final₁, [], []⟩)
    (useful₂ : (emptyStackPDA M).Reaches
      ((.list next gamma context₂ : LeftmostEpsilonPosition M).conf M
        suffix₂)
      ⟨final₂, [], []⟩)
    (hlook : suffix₁.take 1 = suffix₂.take 1) :
    q₁ = q₂ ∧ Z₁ = Z₂ := by
  cases between with
  | refl => exact ⟨rfl, rfl⟩
  | @head _ middle _ first rest =>
      cases first with
      | @epsilon _ firstNext _ firstGamma _ firstTransition =>
          have directStep₁ : (emptyStackPDA M).Reaches₁
              ⟨q₁, suffix₁, Z₁ :: context₁⟩
              ⟨next, suffix₁, gamma ++ context₁⟩ := by
            have core : (emptyStackPDA M).Reaches₁
                ⟨q₁, [], Z₁ :: context₁⟩
                ⟨next, [], gamma ++ context₁⟩ :=
              ⟨next, gamma, transition₁, by simp⟩
            apply PDA.reaches₁_iff_reachesIn_one.mpr
            simpa [PDA.conf.appendInput] using
              ((PDA.unconsumed_input_N
                (pda := emptyStackPDA M) suffix₁).mp
                (PDA.reaches₁_iff_reachesIn_one.mp core))
          have firstStep : (emptyStackPDA M).Reaches₁
              ⟨q₁, suffix₂, Z₁ :: context₁⟩
              ⟨firstNext, suffix₂, firstGamma ++ context₁⟩ := by
            have core : (emptyStackPDA M).Reaches₁
                ⟨q₁, [], Z₁ :: context₁⟩
                ⟨firstNext, [], firstGamma ++ context₁⟩ :=
              ⟨firstNext, firstGamma, firstTransition, by simp⟩
            apply PDA.reaches₁_iff_reachesIn_one.mpr
            simpa [PDA.conf.appendInput] using
              ((PDA.unconsumed_input_N
                (pda := emptyStackPDA M) suffix₂).mp
                (PDA.reaches₁_iff_reachesIn_one.mp core))
          have directStep₂ : (emptyStackPDA M).Reaches₁
              ⟨q₂, suffix₂, Z₂ :: context₂⟩
              ⟨next, suffix₂, gamma ++ context₂⟩ := by
            have core : (emptyStackPDA M).Reaches₁
                ⟨q₂, [], Z₂ :: context₂⟩
                ⟨next, [], gamma ++ context₂⟩ :=
              ⟨next, gamma, transition₂, by simp⟩
            apply PDA.reaches₁_iff_reachesIn_one.mpr
            simpa [PDA.conf.appendInput] using
              ((PDA.unconsumed_input_N
                (pda := emptyStackPDA M) suffix₂).mp
                (PDA.reaches₁_iff_reachesIn_one.mp core))
          have restUseful₂ : (emptyStackPDA M).Reaches
              ⟨firstNext, suffix₂, firstGamma ++ context₁⟩
              ⟨final₂, [], []⟩ := by
            simpa [LeftmostEpsilonPosition.conf] using
              (rest.reaches M suffix₂).trans
                ((Relation.ReflTransGen.single directStep₂).trans useful₂)
          obtain ⟨hnext, hstack, _⟩ :=
            emptyStack_globally_useful_step_cross_input M hlook
              (by simpa [LeftmostEpsilonPosition.conf] using global₁)
              (by simpa [LeftmostEpsilonPosition.conf] using global₂)
              directStep₁ firstStep useful₁ restUseful₂
          have hfirstNext : firstNext = next := hnext.symm
          have hfirstGamma : firstGamma = gamma :=
            (List.append_cancel_right hstack).symm
          subst firstNext
          subst firstGamma
          let childTrace := rest.snoc M
            (LeftmostEpsilonStep.epsilon transition₂)
          obtain ⟨n, added, hcontext₂, retained⟩ :=
            childTrace.retainedFrameRun M
              (frame := context₁) (added := [])
              (by simp [LeftmostEpsilonPosition.context'])
          have contextEq : context₂ = added ++ context₁ := by
            simpa [childTrace, LeftmostEpsilonPosition.context'] using
              hcontext₂
          have retainedAligned :
              PDA.RetainedFrameRun (emptyStackPDA M) context₁ n
                ⟨next, [], gamma ++ context₁⟩
                ⟨next, [], (gamma ++ added) ++ context₁⟩ := by
            simpa [childTrace, LeftmostEpsilonPosition.conf,
              LeftmostEpsilonPosition.context', contextEq,
              List.append_assoc] using retained
          by_cases hadded : added = []
          · subst added
            have hcycle : Relation.TransGen
                (@PDA.Reaches₁ _ _ _ _ _ _ (emptyStackPDA M))
                ⟨next, suffix₂, gamma ++ context₁⟩
                ⟨next, suffix₂, gamma ++ context₁⟩ := by
              have cycle := Relation.TransGen.tail'
                (rest.reaches M suffix₂) directStep₂
              simpa [contextEq] using cycle
            exact False.elim <| emptyStack_no_useful_cycle M hcycle
              (by simpa [contextEq] using useful₂)
          · have stripped := retainedAligned.changeFrame
                ([] : List (StackSymbol M))
            exfalso
            apply emptyStack_no_useful_stack_growth M
              (q := next) (base := gamma) (extra := added)
              (context := context₁) (input := suffix₂)
              (final := final₂)
            · exact PDA.reaches_of_reachesIn (by
                simpa using stripped.toReachesIn)
            · exact hadded
            · simpa [contextEq, List.append_assoc] using useful₂

/-- Two productive leftmost epsilon traces which converge through epsilon
transitions to the same displayed list child have equal source state and
exposed stack symbol.

The traces may have different hidden stack contexts and different
unconsumed input tails.  It is enough that their tails have the same
one-symbol lookahead and that each child cut has an empty-stack
continuation. -/
public theorem leftmostEpsilonTrace_converging_epsilon_heads_eq
    (M : DPDA Q T S)
    {start : LeftmostEpsilonPosition M}
    {q₁ q₂ next final₁ final₂ : State M}
    {Z₁ Z₂ : StackSymbol M}
    {gamma context₁ context₂ : List (StackSymbol M)}
    {suffix₁ suffix₂ whole₁ whole₂ : List T}
    (trace₁ : LeftmostEpsilonTrace M start (.single q₁ Z₁ context₁))
    (trace₂ : LeftmostEpsilonTrace M start (.single q₂ Z₂ context₂))
    (transition₁ : (next, gamma) ∈
      (emptyStackPDA M).transition_fun' q₁ Z₁)
    (transition₂ : (next, gamma) ∈
      (emptyStackPDA M).transition_fun' q₂ Z₂)
    (global₁ : (emptyStackPDA M).Reaches
      ⟨(emptyStackPDA M).initial_state, whole₁,
        [(emptyStackPDA M).start_symbol]⟩
      (start.conf M suffix₁))
    (global₂ : (emptyStackPDA M).Reaches
      ⟨(emptyStackPDA M).initial_state, whole₂,
        [(emptyStackPDA M).start_symbol]⟩
      (start.conf M suffix₂))
    (useful₁ : (emptyStackPDA M).Reaches
      ((.list next gamma context₁ : LeftmostEpsilonPosition M).conf M
        suffix₁)
      ⟨final₁, [], []⟩)
    (useful₂ : (emptyStackPDA M).Reaches
      ((.list next gamma context₂ : LeftmostEpsilonPosition M).conf M
        suffix₂)
      ⟨final₂, [], []⟩)
    (hlook : suffix₁.take 1 = suffix₂.take 1) :
    q₁ = q₂ ∧ Z₁ = Z₂ := by
  have parentUseful₁ : (emptyStackPDA M).Reaches
      ((.single q₁ Z₁ context₁ : LeftmostEpsilonPosition M).conf M
        suffix₁)
      ⟨final₁, [], []⟩ :=
    ((LeftmostEpsilonStep.epsilon transition₁).reaches M suffix₁).trans
      useful₁
  have parentUseful₂ : (emptyStackPDA M).Reaches
      ((.single q₂ Z₂ context₂ : LeftmostEpsilonPosition M).conf M
        suffix₂)
      ⟨final₂, [], []⟩ :=
    ((LeftmostEpsilonStep.epsilon transition₂).reaches M suffix₂).trans
      useful₂
  rcases leftmostEpsilonTrace_productive_comparable M trace₁ trace₂
      global₁ global₂ parentUseful₁ parentUseful₂ hlook with
    between | between
  · exact leftmostEpsilonTrace_converging_epsilon_heads_eq_of_trace M
      between transition₁ transition₂
      (global₁.trans (trace₁.reaches M suffix₁))
      (global₂.trans (trace₁.reaches M suffix₂))
      useful₁ useful₂ hlook
  · obtain ⟨hq, hZ⟩ :=
      leftmostEpsilonTrace_converging_epsilon_heads_eq_of_trace M
        between transition₂ transition₁
        (global₂.trans (trace₂.reaches M suffix₂))
        (global₁.trans (trace₂.reaches M suffix₁))
        useful₂ useful₁ hlook.symm
    exact ⟨hq.symm, hZ.symm⟩

end

end DPDA_to_LR
