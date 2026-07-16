module

public import Langlib.Grammars.LR.Equivalence.StackRepresentation
public import Langlib.Grammars.LR.Equivalence.CanonicalSoundness
public import Langlib.Automata.DeterministicPushdown.Basics.Determinism

/-!
# Correctness of the buffered canonical LR machine

The lemmas in this file relate stable parser controls of the concrete marked
DPDA to the grammar-symbol-stack semantics of `CanonicalParser`.
-/

@[expose]
public section

open Language PDA

namespace CF_grammar.LRk.Buffered

open CF_grammar.LRk
open CF_grammar.LRk.CanonicalParser

variable {T : Type} [Fintype T]

noncomputable section

/-- Concrete machine configuration corresponding to a stable canonical
parser configuration. -/
@[expose]
public def stableConfig (G : CF_grammar T) (k : ℕ) (hk : 0 < k)
    (c : CanonicalParser.Config T G) :
    PDA.conf (machine G k hk).toPDA :=
  ⟨Control.parse (scanKernel G k c.stack) (observe k c.input),
    unreadAfter k c.input, stackRep G k c.stack⟩

/-- A successful input transition is one step of the embedded PDA. -/
private theorem input_reachesIn_one {Q A S : Type}
    [Fintype Q] [Fintype A] [Fintype S]
    (M : DPDA Q A S) {q p : Q} {a : A} {input : List A}
    {Z : S} {stack beta : List S}
    (h : M.transition q a Z = some (p, beta)) :
    M.toPDA.ReachesIn 1
      ⟨q, a :: input, Z :: stack⟩
      ⟨p, input, beta ++ stack⟩ := by
  rw [← PDA.reaches₁_iff_reachesIn_one]
  simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, h]

/-- A successful epsilon transition is one step of the embedded PDA. -/
private theorem epsilon_reachesIn_one {Q A S : Type}
    [Fintype Q] [Fintype A] [Fintype S]
    (M : DPDA Q A S) {q p : Q} {input : List A}
    {Z : S} {stack beta : List S}
    (h : M.epsilon_transition q Z = some (p, beta)) :
    M.toPDA.ReachesIn 1
      ⟨q, input, Z :: stack⟩
      ⟨p, input, beta ++ stack⟩ := by
  rw [← PDA.reaches₁_iff_reachesIn_one]
  cases input with
  | nil => simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, h]
  | cons a input =>
      have hinput : M.transition q a Z = none :=
        M.no_mixed q Z (by simp [h]) a
      simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, h, hinput]

/-- Pop a list of non-bottom frames and perform the final nonterminal goto.
The exact count makes the macro usable in the reverse simulation as a
strictly positive deterministic prefix. -/
private theorem pop_frames (G : CF_grammar T) (k : ℕ) (hk : 0 < k)
    (cursor : ReductionCursor G) (buffer : Lookahead T k)
    (input : List (Option T)) (frames : List (StackSymbol G k))
    (Z : StackSymbol G k) (rest : List (StackSymbol G k))
    (hlen : frames.length = cursor.remaining)
    (hframes : ∀ Y ∈ frames, Y ≠ none) :
    (machine G k hk).toPDA.ReachesIn (frames.length + 1)
      ⟨Control.pop cursor buffer, input, frames ++ Z :: rest⟩
      ⟨Control.parse
          (nextKernel G k (kernelOfTop G k Z)
            (symbol.nonterminal (ruleAt G.augment cursor.rule).1)) buffer,
        input,
        some (nextKernel G k (kernelOfTop G k Z)
          (symbol.nonterminal (ruleAt G.augment cursor.rule).1)) :: Z :: rest⟩ := by
  induction frames generalizing cursor with
  | nil =>
      simp only [List.length_nil] at hlen
      have hzero : ¬ 0 < cursor.remaining := by omega
      have hepsilon : (machine G k hk).epsilon_transition
          (Control.pop cursor buffer) Z =
          some (Control.parse
              (nextKernel G k (kernelOfTop G k Z)
                (symbol.nonterminal (ruleAt G.augment cursor.rule).1)) buffer,
            [some (nextKernel G k (kernelOfTop G k Z)
              (symbol.nonterminal (ruleAt G.augment cursor.rule).1)), Z]) := by
        simp [machine, epsilonTransition, hzero]
      simpa using epsilon_reachesIn_one (machine G k hk)
        (input := input) (stack := rest) hepsilon
  | cons Y frames ih =>
      simp only [List.length_cons] at hlen
      have hpos : 0 < cursor.remaining := by omega
      have hY : Y ≠ none := hframes Y (by simp)
      have htail : ∀ X ∈ frames, X ≠ none := by
        intro X hX
        exact hframes X (by simp [hX])
      have hlen' : frames.length = (cursor.pred hpos).remaining := by
        change frames.length = cursor.2.val - 1
        change frames.length + 1 = cursor.2.val at hlen
        omega
      cases Y with
      | none => exact False.elim (hY rfl)
      | some q =>
          have hepsilon : (machine G k hk).epsilon_transition
              (Control.pop cursor buffer) (some q) =
              some (Control.pop (cursor.pred hpos) buffer, []) := by
            simp [machine, epsilonTransition, hpos]
          have hfirst : (machine G k hk).toPDA.ReachesIn 1
              ⟨Control.pop cursor buffer, input,
                some q :: frames ++ Z :: rest⟩
              ⟨Control.pop (cursor.pred hpos) buffer, input,
                frames ++ Z :: rest⟩ := by
            simpa using epsilon_reachesIn_one (machine G k hk)
              (input := input) (stack := frames ++ Z :: rest) hepsilon
          have hrun := ih (cursor.pred hpos) hlen' htail
          have hfull := PDA.reachesIn_of_one_n hfirst hrun
          simpa [ReductionCursor.pred, ReductionCursor.rule] using hfull

/-- Split an exact run after a prescribed number of initial steps. -/
private theorem reachesIn_split_add {Q A S : Type}
    [Fintype Q] [Fintype A] [Fintype S]
    {M : PDA Q A S} {n m : ℕ} {c d : PDA.conf M}
    (h : M.ReachesIn (n + m) c d) :
    ∃ middle, M.ReachesIn n c middle ∧ M.ReachesIn m middle d := by
  induction m generalizing d with
  | zero =>
      exact ⟨d, by simpa using h, PDA.ReachesIn.refl d⟩
  | succ m ih =>
      rw [Nat.add_succ] at h
      obtain ⟨before, hbefore, hlast⟩ :=
        PDA.reachesIn_iff_split_last.mpr h
      obtain ⟨middle, hprefix, hsuffix⟩ := ih hbefore
      exact ⟨middle, hprefix,
        PDA.ReachesIn.step hsuffix
          (PDA.reaches₁_iff_reachesIn_one.mpr hlast)⟩

/-- The accepting control has no outgoing transition. -/
private theorem no_step_from_accept (G : CF_grammar T) (k : ℕ)
    (hk : 0 < k) {input : List (Option T)}
    {stack : List (StackSymbol G k)}
    {d : PDA.conf (machine G k hk).toPDA} :
    ¬ (machine G k hk).toPDA.Reaches₁
      ⟨Control.accept, input, stack⟩ d := by
  cases stack with
  | nil => simp [PDA.Reaches₁, PDA.step]
  | cons Z stack =>
      cases input <;>
        simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, machine,
          inputTransition, epsilonTransition]

/-- The rejecting control has no outgoing transition. -/
private theorem no_step_from_reject (G : CF_grammar T) (k : ℕ)
    (hk : 0 < k) {input : List (Option T)}
    {stack : List (StackSymbol G k)}
    {d : PDA.conf (machine G k hk).toPDA} :
    ¬ (machine G k hk).toPDA.Reaches₁
      ⟨Control.reject, input, stack⟩ d := by
  cases stack with
  | nil => simp [PDA.Reaches₁, PDA.step]
  | cons Z stack =>
      cases input <;>
        simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, machine,
          inputTransition, epsilonTransition]

private theorem reaches_from_accept_eq (G : CF_grammar T) (k : ℕ)
    (hk : 0 < k) {input : List (Option T)}
    {stack : List (StackSymbol G k)}
    {d : PDA.conf (machine G k hk).toPDA}
    (h : (machine G k hk).toPDA.Reaches
      ⟨Control.accept, input, stack⟩ d) :
    d = ⟨Control.accept, input, stack⟩ := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
      subst_vars
      exact False.elim (no_step_from_accept G k hk hstep)

private theorem reaches_from_reject_eq (G : CF_grammar T) (k : ℕ)
    (hk : 0 < k) {input : List (Option T)}
    {stack : List (StackSymbol G k)}
    {d : PDA.conf (machine G k hk).toPDA}
    (h : (machine G k hk).toPDA.Reaches
      ⟨Control.reject, input, stack⟩ d) :
    d = ⟨Control.reject, input, stack⟩ := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
      subst_vars
      exact False.elim (no_step_from_reject G k hk hstep)

/-- If a positive forced prefix has not itself entered the accepting control,
then it can be removed from any accepting deterministic computation, strictly
decreasing the remaining step count. -/
private theorem continue_after_positive_prefix (G : CF_grammar T) (k : ℕ)
    (hk : 0 < k) {c d : PDA.conf (machine G k hk).toPDA}
    {m n : ℕ} {finalStack : List (StackSymbol G k)}
    (hprefix : (machine G k hk).toPDA.ReachesIn m c d)
    (hm : 0 < m) (hd : d.state ≠ Control.accept)
    (haccept : (machine G k hk).toPDA.ReachesIn n c
      ⟨Control.accept, [], finalStack⟩) :
    ∃ n' < n, (machine G k hk).toPDA.ReachesIn n' d
      ⟨Control.accept, [], finalStack⟩ := by
  by_cases hmn : m ≤ n
  · obtain ⟨rest, hn⟩ := Nat.exists_eq_add_of_le hmn
    subst n
    obtain ⟨middle, hfirst, hrest⟩ :=
      reachesIn_split_add haccept
    have hmiddle : middle = d :=
      (machine G k hk).toPDA_reachesIn_deterministic hfirst hprefix
    subst middle
    exact ⟨rest, by omega, hrest⟩
  · have hnm : n ≤ m := by omega
    have hback := (machine G k hk).toPDA_reachesIn_prefix_of_le
      hnm haccept hprefix
    have heq := reaches_from_accept_eq G k hk hback
    exact False.elim (hd (congrArg PDA.conf.state heq))

/-- Positive lookahead distinguishes every nonempty suffix from EOF. -/
private theorem eq_nil_of_observe_eq_eof (k : ℕ) (hk : 0 < k)
    {w : List T} (h : observe k w = eofLookahead T k) : w = [] := by
  cases w with
  | nil => rfl
  | cons a w =>
      have hzero := congrFun h ⟨0, hk⟩
      simp [observe, eofLookahead] at hzero

/-- Once the back of a positive observation is EOF, shifting its head does
not expose another physical input symbol. -/
private theorem unreadAfter_cons_of_last_none (k : ℕ) (hk : 0 < k)
    (a : T) (w : List T)
    (hlast : lastBuffer hk (observe k (a :: w)) = none) :
    unreadAfter k (a :: w) = unreadAfter k w := by
  rw [lastBuffer_observe] at hlast
  have hshort : (a :: w).length < k := by
    by_contra hnot
    have hindex : k - 1 < (a :: w).length := by omega
    rw [List.getElem?_eq_getElem hindex] at hlast
    simp at hlast
  have hwshort : w.length < k := by
    simp only [List.length_cons] at hshort
    omega
  unfold unreadAfter
  rw [if_neg (by omega : ¬ k ≤ (a :: w).length),
    if_neg (by omega : ¬ k ≤ w.length)]

/-- On a positive buffer, a shift action implies that logical input has a
head terminal. -/
private theorem exists_cons_of_tableAction_shift (G : CF_grammar T)
    (k : ℕ) (hk : 0 < k)
    {gamma : List (symbol T G.augment.nt)} {input : List T}
    (haction : tableAction G k (scanKernel G k gamma)
      (observe k input) = .shift) :
    ∃ a w, input = a :: w := by
  cases input with
  | cons a w => exact ⟨a, w, rfl⟩
  | nil =>
      classical
      have haction' : tableAction G k (scanKernel G k gamma)
          (eofLookahead T k) = .shift := by
        simpa [observe, eofLookahead] using haction
      unfold tableAction at haction'
      cases hred : reductionItem? G k (scanKernel G k gamma)
          (eofLookahead T k) with
      | none =>
          rw [hred] at haction'
          simp [lookaheadHead, eofLookahead, hk] at haction'
      | some i =>
          rw [hred] at haction'
          by_cases hi : i.rule = startRuleIndex G <;>
            simp [hi] at haction'

/-- A table accept at a stable positive-lookahead configuration is precisely
canonical-parser acceptance; in particular, all logical input is exhausted. -/
private theorem canonical_accepting_of_action (G : CF_grammar T)
    (k : ℕ) (hk : 0 < k)
    {gamma : List (symbol T G.augment.nt)} {input : List T}
    (haction : tableAction G k (scanKernel G k gamma)
      (observe k input) = .accept) :
    Accepting G k ⟨gamma, input⟩ := by
  obtain ⟨i, hi, hstart⟩ :=
    (tableAction_accept_iff G k (scanKernel G k gamma)
      (observe k input)).mp haction
  have hcand := reductionItem?_reductionCandidate G k hi
  rw [hstart, ruleAt_startRuleIndex] at hcand
  rcases hcand with ⟨_, p, s, hpre, _, hlook⟩
  obtain ⟨rfl, rfl⟩ := fresh_prehandle_eq_root G (by
    simpa [CF_grammar.augmentStartRule] using hpre)
  have hnil : input = [] := by
    apply eq_nil_of_observe_eq_eof k hk
    simpa [eofLookahead, observe] using hlook.symm
  subst input
  exact ⟨rfl, by simpa [eofLookahead, observe] using haction⟩

/-- Every concrete reduce action exposes the suffix equation required by the
trusted canonical reduction step. -/
private theorem canonical_reduce_of_action (G : CF_grammar T) (k : ℕ)
    {gamma : List (symbol T G.augment.nt)} {input : List T}
    {r : RuleIndex G.augment}
    (haction : tableAction G k (scanKernel G k gamma)
      (observe k input) = .reduce r) :
    ∃ p, gamma = p ++ (ruleAt G.augment r).2 ∧
      Step G k ⟨gamma, input⟩
        ⟨p ++ [symbol.nonterminal (ruleAt G.augment r).1], input⟩ := by
  obtain ⟨i, hi, _, hir⟩ :=
    (tableAction_reduce_iff G k (scanKernel G k gamma)
      (observe k input) r).mp haction
  have hcand := reductionItem?_reductionCandidate G k hi
  rcases hcand with ⟨_, p, s, _, hgamma, _⟩
  have hrule : ruleAt G.augment i.rule = ruleAt G.augment r := by rw [hir]
  rw [hrule] at hgamma
  exact ⟨p, hgamma,
    Step.reduce (G := G) (k := k) haction hgamma⟩

/-- One canonical terminal shift is implemented by one epsilon move when EOF
is already buffered, and otherwise by that move followed by one physical
refill. -/
private theorem machine_shift (G : CF_grammar T) (k : ℕ) (hk : 0 < k)
    {gamma : List (symbol T G.augment.nt)} {a : T} {w : List T}
    (haction : tableAction G k (scanKernel G k gamma)
      (observe k (a :: w)) = .shift) :
    ∃ n > 0, (machine G k hk).toPDA.ReachesIn n
      (stableConfig G k hk ⟨gamma, a :: w⟩)
      (stableConfig G k hk
        ⟨gamma ++ [symbol.terminal a], w⟩) := by
  obtain ⟨Z, rest, hstack, htop⟩ := stackRep_top G k gamma
  let next := nextKernel G k (scanKernel G k gamma) (symbol.terminal a)
  have hnext : next = scanKernel G k (gamma ++ [symbol.terminal a]) := by
    simp [next, nextKernel]
  by_cases hlast : lastBuffer hk (observe k (a :: w)) = none
  · have hepsilon : (machine G k hk).epsilon_transition
        (Control.parse (scanKernel G k gamma) (observe k (a :: w))) Z =
        some (Control.parse next
            (shiftBuffer hk (observe k (a :: w)) none),
          [some next, Z]) := by
      simp [machine, epsilonTransition, haction,
        lookaheadHead_observe_cons k hk a w, hlast, next]
    have hstep := epsilon_reachesIn_one (machine G k hk)
      (input := unreadAfter k (a :: w)) (stack := rest) hepsilon
    have hbuffer :=
      shiftBuffer_observe_cons_of_last_none k hk a w hlast
    have hunread := unreadAfter_cons_of_last_none k hk a w hlast
    refine ⟨1, by omega, ?_⟩
    simpa [stableConfig, hstack, hnext, hbuffer, hunread] using hstep
  · obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hlast
    obtain ⟨x, xs, hunread, hxs, hbuffer⟩ :=
      unreadAfter_cons_split k hk a w hb
    have hepsilon : (machine G k hk).epsilon_transition
        (Control.parse (scanKernel G k gamma) (observe k (a :: w))) Z =
        some (Control.refill next (observe k (a :: w)),
          [some next, Z]) := by
      simp [machine, epsilonTransition, haction,
        lookaheadHead_observe_cons k hk a w, hb, next]
    have hfirst : (machine G k hk).toPDA.ReachesIn 1
        (stableConfig G k hk ⟨gamma, a :: w⟩)
        ⟨Control.refill next (observe k (a :: w)), x :: xs,
          some next :: Z :: rest⟩ := by
      have hraw := epsilon_reachesIn_one (machine G k hk)
        (input := x :: xs) (stack := rest) hepsilon
      simpa [stableConfig, hstack, hunread] using hraw
    have htransition : (machine G k hk).transition
        (Control.refill next (observe k (a :: w))) x (some next) =
        some (Control.parse next
            (shiftBuffer hk (observe k (a :: w)) x), [some next]) := by
      simp [machine, inputTransition]
    have hsecond : (machine G k hk).toPDA.ReachesIn 1
        ⟨Control.refill next (observe k (a :: w)), x :: xs,
          some next :: Z :: rest⟩
        (stableConfig G k hk
          ⟨gamma ++ [symbol.terminal a], w⟩) := by
      have hraw := input_reachesIn_one (machine G k hk)
        (input := xs) (stack := Z :: rest) htransition
      simpa [stableConfig, hstack, hnext, hbuffer, hxs] using hraw
    refine ⟨2, by omega, ?_⟩
    simpa using PDA.reachesIn_of_one_n hfirst hsecond

/-- One canonical reduction is implemented by entering pop mode, removing one
saved kernel for every right-hand-side symbol, and pushing the goto kernel for
the production head. -/
private theorem machine_reduce (G : CF_grammar T) (k : ℕ) (hk : 0 < k)
    {gamma p : List (symbol T G.augment.nt)} {input : List T}
    {r : RuleIndex G.augment}
    (haction : tableAction G k (scanKernel G k gamma)
      (observe k input) = .reduce r)
    (hgamma : gamma = p ++ (ruleAt G.augment r).2) :
    (machine G k hk).toPDA.ReachesIn
      ((ruleAt G.augment r).2.length + 2)
      (stableConfig G k hk ⟨gamma, input⟩)
      (stableConfig G k hk
        ⟨p ++ [symbol.nonterminal (ruleAt G.augment r).1], input⟩) := by
  obtain ⟨frames, hframesLen, hframesSome, hframesRep⟩ :=
    stackRep_append_frames G k p (ruleAt G.augment r).2
  obtain ⟨Z, rest, hpStack, hpTop⟩ := stackRep_top G k p
  obtain ⟨Zg, restg, hgammaStack, _⟩ := stackRep_top G k gamma
  have hstack : stackRep G k gamma = frames ++ Z :: rest := by
    rw [hgamma, hframesRep, hpStack]
  have hepsilon : (machine G k hk).epsilon_transition
      (Control.parse (scanKernel G k gamma) (observe k input)) Zg =
      some (Control.pop (fullCursor G r) (observe k input), [Zg]) := by
    simp [machine, epsilonTransition, haction]
  have hfirst : (machine G k hk).toPDA.ReachesIn 1
      (stableConfig G k hk ⟨gamma, input⟩)
      ⟨Control.pop (fullCursor G r) (observe k input),
        unreadAfter k input, stackRep G k gamma⟩ := by
    have hraw := epsilon_reachesIn_one (machine G k hk)
      (input := unreadAfter k input) (stack := restg) hepsilon
    simpa [stableConfig, hgammaStack] using hraw
  have hcursorLen : frames.length = (fullCursor G r).remaining := by
    simpa [fullCursor, ReductionCursor.remaining] using hframesLen
  have hpop := pop_frames G k hk (fullCursor G r) (observe k input)
    (unreadAfter k input) frames Z rest hcursorLen hframesSome
  have hpop' : (machine G k hk).toPDA.ReachesIn
      ((ruleAt G.augment r).2.length + 1)
      ⟨Control.pop (fullCursor G r) (observe k input),
        unreadAfter k input, stackRep G k gamma⟩
      (stableConfig G k hk
        ⟨p ++ [symbol.nonterminal (ruleAt G.augment r).1], input⟩) := by
    have hnext : nextKernel G k (kernelOfTop G k Z)
          (symbol.nonterminal (ruleAt G.augment r).1) =
        scanKernel G k
          (p ++ [symbol.nonterminal (ruleAt G.augment r).1]) := by
      rw [hpTop]
      simp [nextKernel]
    simpa [stableConfig, hstack, hpStack, hframesLen, hnext,
      fullCursor, ReductionCursor.rule] using hpop
  simpa using PDA.reachesIn_of_one_n hfirst hpop'

/-- Every trusted canonical parser step expands to a nonempty finite machine
run between stable controls. -/
private theorem machine_step (G : CF_grammar T) (k : ℕ) (hk : 0 < k)
    {c d : CanonicalParser.Config T G} (h : Step G k c d) :
    ∃ n > 0, (machine G k hk).toPDA.ReachesIn n
      (stableConfig G k hk c) (stableConfig G k hk d) := by
  cases h with
  | shift haction => exact machine_shift G k hk haction
  | @reduce gamma p input r haction hgamma =>
      exact ⟨(ruleAt G.augment r).2.length + 2, by omega,
        machine_reduce G k hk haction hgamma⟩

/-- Canonical reachability is simulated by the concrete DPDA. -/
public theorem machine_reaches_of_canonical (G : CF_grammar T) (k : ℕ)
    (hk : 0 < k) {c d : CanonicalParser.Config T G}
    (h : Reaches G k c d) :
    (machine G k hk).toPDA.Reaches
      (stableConfig G k hk c) (stableConfig G k hk d) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      obtain ⟨n, _, hn⟩ := machine_step G k hk hstep
      exact ih.trans (PDA.reaches_of_reachesIn hn)

/-- A stable canonical accepting configuration enters the final control in
one epsilon move. -/
private theorem machine_accept (G : CF_grammar T) (k : ℕ) (hk : 0 < k)
    {c : CanonicalParser.Config T G} (h : Accepting G k c) :
    (machine G k hk).toPDA.ReachesIn 1
      (stableConfig G k hk c)
      ⟨Control.accept, [], stackRep G k c.stack⟩ := by
  rcases c with ⟨gamma, input⟩
  rcases h with ⟨rfl, haction⟩
  obtain ⟨Z, rest, hstack, _⟩ := stackRep_top G k gamma
  have hepsilon : (machine G k hk).epsilon_transition
      (Control.parse (scanKernel G k gamma) (observe k ([] : List T))) Z =
      some (Control.accept, [Z]) := by
    simp [machine, epsilonTransition, haction, observe, eofLookahead]
  have hraw := epsilon_reachesIn_one (machine G k hk)
    (input := ([] : List (Option T))) (stack := rest) hepsilon
  have hunread : unreadAfter k ([] : List T) = [] := by
    unfold unreadAfter
    simp only [List.length_nil]
    rw [if_neg (by omega : ¬ k ≤ 0)]
  simpa [stableConfig, hstack, hunread] using hraw

/-- Canonical acceptance implies acceptance of the explicitly endmarked word
by the concrete DPDA. -/
public theorem marked_machine_accepts_of_canonical (G : CF_grammar T)
    (k : ℕ) (hk : 0 < k) {w : List T} (h : Accepts G k w) :
    w.map some ++ [none] ∈ (machine G k hk).acceptsByFinalState := by
  rcases h with ⟨c, hreach, haccept⟩
  have hpreload := machine_reaches_preload G k hk w
  have hpreload' : (machine G k hk).toPDA.Reaches
      ⟨(machine G k hk).initial_state, w.map some ++ [none],
        [(machine G k hk).start_symbol]⟩
      (stableConfig G k hk (initialConfig G w)) := by
    simpa [stableConfig, initialConfig, stackRep_nil] using hpreload
  have hparse := machine_reaches_of_canonical G k hk hreach
  have hfinal := PDA.reaches_of_reachesIn (machine_accept G k hk haccept)
  change ∃ q ∈ (machine G k hk).toPDA.final_states,
    ∃ stack, (machine G k hk).toPDA.Reaches
      ⟨(machine G k hk).toPDA.initial_state, w.map some ++ [none],
        [(machine G k hk).toPDA.start_symbol]⟩
      ⟨q, [], stack⟩
  refine ⟨Control.accept, ?_, stackRep G k c.stack,
    hpreload'.trans (hparse.trans hfinal)⟩
  simp [machine, DPDA.toPDA]

/-- Any accepting concrete run starting at a stable parser control projects
to a canonical run ending in a canonical accepting configuration. -/
private theorem canonical_accepts_from_machineIn (G : CF_grammar T)
    (k : ℕ) (hk : 0 < k) {c : CanonicalParser.Config T G}
    {n : ℕ} {finalStack : List (StackSymbol G k)}
    (h : (machine G k hk).toPDA.ReachesIn n
      (stableConfig G k hk c) ⟨Control.accept, [], finalStack⟩) :
    ∃ d, Reaches G k c d ∧ Accepting G k d := by
  induction n using Nat.strong_induction_on generalizing c finalStack with
  | h n ih =>
      rcases c with ⟨gamma, input⟩
      cases haction : tableAction G k (scanKernel G k gamma)
          (observe k input) with
      | accept =>
          exact ⟨⟨gamma, input⟩, Relation.ReflTransGen.refl,
            canonical_accepting_of_action G k hk haction⟩
      | error =>
          obtain ⟨Z, rest, hstack, _⟩ := stackRep_top G k gamma
          have hepsilon : (machine G k hk).epsilon_transition
              (Control.parse (scanKernel G k gamma) (observe k input)) Z =
              some (Control.reject, [Z]) := by
            simp [machine, epsilonTransition, haction]
          have hprefix : (machine G k hk).toPDA.ReachesIn 1
              (stableConfig G k hk ⟨gamma, input⟩)
              ⟨Control.reject, unreadAfter k input, stackRep G k gamma⟩ := by
            have hraw := epsilon_reachesIn_one (machine G k hk)
              (input := unreadAfter k input) (stack := rest) hepsilon
            simpa [stableConfig, hstack] using hraw
          obtain ⟨n', _, hbad⟩ := continue_after_positive_prefix G k hk
            hprefix (by omega) (by simp) h
          have heq := reaches_from_reject_eq G k hk
            (PDA.reaches_of_reachesIn hbad)
          have hstate := congrArg PDA.conf.state heq
          simp at hstate
      | shift =>
          obtain ⟨a, w, rfl⟩ :=
            exists_cons_of_tableAction_shift G k hk haction
          have hstep : Step G k ⟨gamma, a :: w⟩
              ⟨gamma ++ [symbol.terminal a], w⟩ := Step.shift haction
          obtain ⟨m, hm, hprefix⟩ := machine_shift G k hk haction
          obtain ⟨n', hn', hrest⟩ := continue_after_positive_prefix G k hk
            hprefix hm (by simp [stableConfig]) h
          obtain ⟨d, hd, haccept⟩ := ih n' hn' hrest
          exact ⟨d, Relation.ReflTransGen.head hstep hd, haccept⟩
      | reduce r =>
          obtain ⟨p, hgamma, hstep⟩ :=
            canonical_reduce_of_action G k haction
          have hprefix := machine_reduce G k hk haction hgamma
          obtain ⟨n', hn', hrest⟩ := continue_after_positive_prefix G k hk
            hprefix (by omega) (by simp [stableConfig]) h
          obtain ⟨d, hd, haccept⟩ := ih n' hn' hrest
          exact ⟨d, Relation.ReflTransGen.head hstep hd, haccept⟩

/-- Acceptance of a properly endmarked word by the concrete machine yields a
canonical accepting run. -/
public theorem canonical_of_marked_machine_accepts (G : CF_grammar T)
    (k : ℕ) (hk : 0 < k) {w : List T}
    (h : w.map some ++ [none] ∈
      (machine G k hk).acceptsByFinalState) :
    Accepts G k w := by
  change ∃ q ∈ (machine G k hk).toPDA.final_states,
    ∃ stack, (machine G k hk).toPDA.Reaches
      ⟨(machine G k hk).toPDA.initial_state, w.map some ++ [none],
        [(machine G k hk).toPDA.start_symbol]⟩
      ⟨q, [], stack⟩ at h
  rcases h with ⟨q, hq, finalStack, hrun⟩
  have hq' : q = Control.accept := by
    simpa [machine, DPDA.toPDA] using hq
  subst q
  have hpreload := machine_reaches_preload G k hk w
  have hpreload' : (machine G k hk).toPDA.Reaches
      ⟨(machine G k hk).initial_state, w.map some ++ [none],
        [(machine G k hk).start_symbol]⟩
      (stableConfig G k hk (initialConfig G w)) := by
    simpa [stableConfig, initialConfig, stackRep_nil] using hpreload
  have hstable : (machine G k hk).toPDA.Reaches
      (stableConfig G k hk (initialConfig G w))
      ⟨Control.accept, [], finalStack⟩ := by
    rcases (machine G k hk).toPDA_reaches_comparable hpreload' hrun with
      hforward | hback
    · exact hforward
    · have heq := reaches_from_accept_eq G k hk hback
      have hstate := congrArg PDA.conf.state heq
      simp [stableConfig] at hstate
  obtain ⟨n, hn⟩ := PDA.reaches_iff_reachesIn.mp hstable
  obtain ⟨d, hcanonical, haccept⟩ :=
    canonical_accepts_from_machineIn G k hk hn
  exact ⟨d, hcanonical, haccept⟩

/-- On properly endmarked inputs, the concrete machine recognizes exactly the
language of its LR(k) grammar. -/
public theorem marked_machine_correct (G : CF_grammar T) (k : ℕ)
    (hk : 0 < k) (hLR : G.IsLRk k) (w : List T) :
    w.map some ++ [none] ∈ (machine G k hk).acceptsByFinalState ↔
      w ∈ CF_language G := by
  constructor
  · intro h
    exact CanonicalParser.accepts_sound G k
      (canonical_of_marked_machine_accepts G k hk h)
  · intro h
    exact marked_machine_accepts_of_canonical G k hk
      (CanonicalParser.accepts_complete G k hk hLR h)

end

end CF_grammar.LRk.Buffered
