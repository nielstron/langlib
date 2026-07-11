module

public import Langlib.Grammars.Indexed.NormalForm.AhoOverlayBinary
public import Langlib.Grammars.Indexed.NormalForm.AhoOverlayPushCompress
public import Langlib.Grammars.Indexed.NormalForm.AhoOverlayPushFresh
public import Langlib.Grammars.Indexed.NormalForm.AhoOverlayRunner
public import Langlib.Grammars.Indexed.NormalForm.AhoOverlayTerminal

@[expose]
public section

/-!
# Constructor dispatch for copy-on-write overlays

This module is the acyclic assembly point for the individual overlay constructor proofs.  It
exposes the single strong-induction step consumed by the final mutual scheduler.
-/

variable {T : Type}

namespace IndexedGrammar
namespace Aho

/-- Complete overlay-mode constructor dispatch under the mutual strong-induction hypotheses. -/
public theorem overlayScheduleRun_of_smaller
    {g : IndexedGrammar T} [Fintype g.nt]
    {A : g.nt} {stack : List g.flag} {w : List T}
    (parse : NFParse g A stack w)
    (ordinaryIH : ∀ {B : g.nt} {residualStack : List g.flag} {v : List T}
      (q : NFParse g B residualStack v), q.nodeCount < parse.nodeCount →
        OrdinaryScheduleRuns q)
    (overlayIH : ∀ {B : g.nt} {residualStack : List g.flag} {v : List T}
      (q : NFParse g B residualStack v), q.nodeCount < parse.nodeCount →
        OverlayScheduleRun q) :
    OverlayScheduleRun parse := by
  cases parse with
  | @binary A B C stack u v r hr hlhs hc hrhs leftParse rightParse =>
      apply overlayScheduleRun_binary hr hlhs hc hrhs leftParse rightParse
      · apply ordinaryIH leftParse
        simp only [NFParse.nodeCount]
        omega
      · apply ordinaryIH rightParse
        simp only [NFParse.nodeCount]
        omega
  | @pop A B f stack w r hr hlhs hc hrhs rest =>
      apply overlayScheduleRun_atomicPop
        (NFParse.pop hr hlhs hc hrhs rest)
      · intro d hd
        rcases Finset.mem_image.mp hd with ⟨e, _he, hed⟩
        omega
      · intro C residualStack residual hcount
        exact ordinaryIH residual hcount
      · intro C residualStack residual hcount
        exact overlayIH residual hcount
  | @push A B f stack w r hr hlhs hc hrhs rest =>
      let parent : NFParse g A stack w := .push hr hlhs hc hrhs rest
      change OverlayScheduleRun parent
      by_cases hzero : 0 ∈ parent.eventDepths
      · by_cases hone : 1 ∈ rest.eventDepths
        · apply overlayScheduleRun_pushFresh hr hlhs hc hrhs rest hone
          apply overlayIH rest
          simp [parent, NFParse.nodeCount]
        · apply overlayScheduleRun_pushCompress hr hlhs hc hrhs rest hone
          apply overlayIH rest
          simp [parent, NFParse.nodeCount]
      · apply overlayScheduleRun_atomicPop parent
        · intro d hd
          exact Nat.pos_of_ne_zero (fun hd0 => hzero (hd0 ▸ hd))
        · intro C residualStack residual hcount
          exact ordinaryIH residual hcount
        · intro C residualStack residual hcount
          exact overlayIH residual hcount
  | @terminal A stack a r hr hlhs hc hrhs =>
      exact overlayScheduleRun_terminal_false hr hlhs hc hrhs

end Aho
end IndexedGrammar

end
