module

public import Langlib.Grammars.LR.Equivalence.DPDAToLR.CrossInputStep

/-!
# Useful-path determinism across a changed input suffix

Two useful wrapper runs may start with different complete input words.  If the
words share the prefix consumed by one run, their first residual symbols agree,
and the runs have the same number of steps, the other run consumes exactly the
same prefix and reaches the same control state and stack.
-/

@[expose]
public section

open PDA

namespace DPDA_to_LR

noncomputable section

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

private theorem prefix_eq_of_reaches_to_cons
    (M : DPDA Q T S)
    {pre tail : List T} {n : ℕ} {a : T}
    {q : EState M} {Z : EStack M} {stack : List (EStack M)}
    (h : (emptyStackPDA M).ReachesIn n
      ⟨(emptyStackPDA M).initial_state, pre ++ tail,
        [(emptyStackPDA M).start_symbol]⟩
      ⟨q, a :: tail, Z :: stack⟩) :
    ∃ consumed : List T, pre = consumed ++ [a] := by
  obtain ⟨consumed, hconsumed⟩ :=
    PDA.decreasing_input (PDA.reaches_of_reachesIn h)
  refine ⟨consumed, ?_⟩
  apply List.append_left_injective tail
  simpa [List.append_assoc] using hconsumed

/-- Equal-length useful runs synchronize even when their untouched input
suffixes differ.  The first displayed endpoint is the no-overrun hypothesis:
it has consumed precisely `prefix` and none of `tail₁`. -/
public theorem emptyStack_globally_useful_reachesIn_cross_input
    (M : DPDA Q T S)
    {pre tail₁ tail₂ residual₂ : List T} {n : ℕ}
    {q₁ q₂ final₁ final₂ : EState M}
    {gamma₁ gamma₂ : List (EStack M)}
    (h₁ : (emptyStackPDA M).ReachesIn n
      ⟨(emptyStackPDA M).initial_state, pre ++ tail₁,
        [(emptyStackPDA M).start_symbol]⟩
      ⟨q₁, tail₁, gamma₁⟩)
    (h₂ : (emptyStackPDA M).ReachesIn n
      ⟨(emptyStackPDA M).initial_state, pre ++ tail₂,
        [(emptyStackPDA M).start_symbol]⟩
      ⟨q₂, residual₂, gamma₂⟩)
    (huseful₁ : (emptyStackPDA M).Reaches
      ⟨q₁, tail₁, gamma₁⟩ ⟨final₁, [], []⟩)
    (huseful₂ : (emptyStackPDA M).Reaches
      ⟨q₂, residual₂, gamma₂⟩ ⟨final₂, [], []⟩)
    (hlook : tail₁.take 1 = tail₂.take 1) :
    (⟨q₂, residual₂, gamma₂⟩ : PDA.conf (emptyStackPDA M)) =
      ⟨q₁, tail₂, gamma₁⟩ := by
  induction n generalizing pre tail₁ tail₂ residual₂
      q₁ q₂ gamma₁ gamma₂ with
  | zero =>
      have hzero₁ := PDA.reachesIn_zero h₁
      have hzero₂ := PDA.reachesIn_zero h₂
      have hinput := congrArg PDA.conf.input hzero₁
      have hprefix : pre = [] := by
        apply List.eq_nil_of_length_eq_zero
        have hlength := congrArg List.length hinput
        simp only [List.length_append] at hlength
        omega
      subst pre
      have hstate₁ := congrArg PDA.conf.state hzero₁
      have hstack₁ := congrArg PDA.conf.stack hzero₁
      have hstate₂ := congrArg PDA.conf.state hzero₂
      have hinput₂ := congrArg PDA.conf.input hzero₂
      have hstack₂ := congrArg PDA.conf.stack hzero₂
      apply PDA.conf.ext
      · exact hstate₂.symm.trans hstate₁
      · simpa using hinput₂.symm
      · exact hstack₂.symm.trans hstack₁
  | succ n ih =>
      obtain ⟨before₁, hprefix₁, hlast₁⟩ :=
        PDA.reachesIn_iff_split_last.mpr h₁
      obtain ⟨before₂, hprefix₂, hlast₂⟩ :=
        PDA.reachesIn_iff_split_last.mpr h₂
      have hstep₁ := PDA.reaches₁_iff_reachesIn_one.mpr hlast₁
      have hstep₂ := PDA.reaches₁_iff_reachesIn_one.mpr hlast₂
      have hbeforeUseful₁ : (emptyStackPDA M).Reaches
          before₁ ⟨final₁, [], []⟩ :=
        (Relation.ReflTransGen.single hstep₁).trans huseful₁
      have hbeforeUseful₂ : (emptyStackPDA M).Reaches
          before₂ ⟨final₂, [], []⟩ :=
        (Relation.ReflTransGen.single hstep₂).trans huseful₂
      rcases before₁ with ⟨source₁, input₁, stack₁⟩
      rcases before₂ with ⟨source₂, input₂, stack₂⟩
      cases stack₁ with
      | nil => simp [PDA.Reaches₁, PDA.step] at hstep₁
      | cons Z rest =>
          rcases PDA.reaches₁_push hstep₁ with hread₁ | hepsilon₁
          · rcases hread₁ with
              ⟨a, readTail, next, replacement, hinput₁,
                hendpoint₁, htransition₁⟩
            obtain ⟨rfl, rfl, rfl⟩ := PDA.conf.mk.inj hendpoint₁
            subst input₁
            obtain ⟨consumed, hprefixEq⟩ :=
              prefix_eq_of_reaches_to_cons M hprefix₁
            have hprefix₁' := hprefix₁
            have hprefix₂' := hprefix₂
            rw [hprefixEq] at hprefix₁' hprefix₂'
            simp only [List.append_assoc, List.singleton_append] at hprefix₁' hprefix₂'
            have hbeforeEq := ih hprefix₁' hprefix₂'
              hbeforeUseful₁ hbeforeUseful₂ (by simp)
            have hsourceEq : source₂ = source₁ :=
              congrArg PDA.conf.state hbeforeEq
            have hinputEq : input₂ = a :: tail₂ :=
              congrArg PDA.conf.input hbeforeEq
            have hstackEq : stack₂ = Z :: rest :=
              congrArg PDA.conf.stack hbeforeEq
            subst source₂
            subst input₂
            subst stack₂
            obtain ⟨hstate, hstack, hinputs⟩ :=
              emptyStack_globally_useful_step_cross_input M
                (by simp) (PDA.reaches_of_reachesIn hprefix₁)
                (PDA.reaches_of_reachesIn hprefix₂)
                hstep₁ hstep₂ huseful₁ huseful₂
            rcases hinputs with hpreserve | hread
            · have hbad := hpreserve.1
              simp at hbad
            · rcases hread with
                ⟨b, leftTail, rightTail, hleft, hright,
                  hafterLeft, hafterRight⟩
              injection hleft with _ hleftTail
              injection hright with _ hrightTail
              subst leftTail
              subst rightTail
              have hresidual : residual₂ = tail₂ := by
                exact hrightTail.symm
              subst residual₂
              apply PDA.conf.ext
              · exact hstate.symm
              · rfl
              · exact hstack.symm
          · rcases hepsilon₁ with
              ⟨next, replacement, hendpoint₁, htransition₁⟩
            obtain ⟨rfl, rfl, rfl⟩ := PDA.conf.mk.inj hendpoint₁
            have hbeforeEq := ih hprefix₁ hprefix₂
              hbeforeUseful₁ hbeforeUseful₂ hlook
            have hsourceEq : source₂ = source₁ :=
              congrArg PDA.conf.state hbeforeEq
            have hinputEq : input₂ = tail₂ :=
              congrArg PDA.conf.input hbeforeEq
            have hstackEq : stack₂ = Z :: rest :=
              congrArg PDA.conf.stack hbeforeEq
            subst source₂
            subst input₂
            subst stack₂
            obtain ⟨hstate, hstack, hinputs⟩ :=
              emptyStack_globally_useful_step_cross_input M
                hlook (PDA.reaches_of_reachesIn hprefix₁)
                (PDA.reaches_of_reachesIn hprefix₂)
                hstep₁ hstep₂ huseful₁ huseful₂
            rcases hinputs with hpreserve | hread
            · have hresidual : residual₂ = tail₂ := by
                exact hpreserve.2
              subst residual₂
              apply PDA.conf.ext
              · exact hstate.symm
              · rfl
              · exact hstack.symm
            · rcases hread with
                ⟨a, leftTail, rightTail, hleft, hright,
                  hafterLeft, hafterRight⟩
              have hbad : (a :: leftTail).length = leftTail.length := by
                rw [← hleft, ← hafterLeft]
              simp at hbad

/-- Symmetric form: the second run is the one known not to consume into its
tail. -/
public theorem emptyStack_globally_useful_reachesIn_cross_input_symm
    (M : DPDA Q T S)
    {pre tail₁ tail₂ residual₁ : List T} {n : ℕ}
    {q₁ q₂ final₁ final₂ : EState M}
    {gamma₁ gamma₂ : List (EStack M)}
    (h₁ : (emptyStackPDA M).ReachesIn n
      ⟨(emptyStackPDA M).initial_state, pre ++ tail₁,
        [(emptyStackPDA M).start_symbol]⟩
      ⟨q₁, residual₁, gamma₁⟩)
    (h₂ : (emptyStackPDA M).ReachesIn n
      ⟨(emptyStackPDA M).initial_state, pre ++ tail₂,
        [(emptyStackPDA M).start_symbol]⟩
      ⟨q₂, tail₂, gamma₂⟩)
    (huseful₁ : (emptyStackPDA M).Reaches
      ⟨q₁, residual₁, gamma₁⟩ ⟨final₁, [], []⟩)
    (huseful₂ : (emptyStackPDA M).Reaches
      ⟨q₂, tail₂, gamma₂⟩ ⟨final₂, [], []⟩)
    (hlook : tail₁.take 1 = tail₂.take 1) :
    (⟨q₁, residual₁, gamma₁⟩ : PDA.conf (emptyStackPDA M)) =
      ⟨q₂, tail₁, gamma₂⟩ := by
  exact emptyStack_globally_useful_reachesIn_cross_input M
    h₂ h₁ huseful₂ huseful₁ hlook.symm

end

end DPDA_to_LR
