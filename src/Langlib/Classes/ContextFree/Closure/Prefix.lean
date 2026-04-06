import Langlib.Automata.Pushdown.Equivalence.ContextFree
import Langlib.Utilities.LanguageOperations
import Mathlib
import Langlib.Classes.ContextFree.Definition

/-! # Context-Free Closure Under Prefix

Proof that context-free languages are closed under the prefix operation,
via the PDA equivalence (the "all states accept" / verification-mode approach).

## Strategy

Given a CFL `L` accepted by PDA `M` (empty-stack), we build a **prefix PDA** whose
language is exactly `prefixLang L`.  The prefix PDA has two operating modes:

* *Normal mode* (`Sum.inl` states) – follows `M`'s transitions, consuming input.
* *Verification mode* (`Sum.inr` states) – entered nondeterministically from normal
  mode (only when the input has been fully consumed).  In this mode **all** of `M`'s
  transitions (including reads) become ε-transitions, so the PDA can check that the
  remaining stack is "completable", i.e. that there exists some continuation word `v`
  under which `M` would reach empty stack.

## Main declarations

* `PDA.input_splitting` – splitting a computation at a given input boundary
* `PrefixClosure.prefixPDA` – the prefix PDA construction
* `is_PDA_prefixLang` – `is_PDA L → is_PDA (prefixLang L)`
* `Language.IsContextFree.prefixLang` – CFLs are closed under prefix
-/

open PDA Language Set List

variable {T : Type} [Fintype T]

-- ══════════════════════════════════════════════════════════════════
-- § 1  Input splitting lemma
-- ══════════════════════════════════════════════════════════════════

namespace PDA

variable {Q S : Type} [Fintype Q] [Fintype S] {M : PDA Q T S}

/-
PROBLEM
**Input splitting** (counted version).
If `M` processes `w ++ v` starting from `⟨q, w ++ v, α⟩` and reaches `⟨p, [], δ⟩`
in `n` steps, then there is an intermediate configuration `⟨q', [], γ⟩`
such that `M` reaches it from `⟨q, w, α⟩` and then reaches `⟨p, [], δ⟩`
from `⟨q', v, γ⟩`.

PROVIDED SOLUTION
Induction on n.

Case n = 0: reachesIn_zero gives ⟨q, w ++ v, α⟩ = ⟨p, [], δ⟩, so w ++ v = [] (hence w = [] and v = []), α = δ, and q = p. Use q' = q, γ = α, n₁ = 0, n₂ = 0.

Case n + 1: Case split on w.
  Subcase w = []: Use q' = q, γ = α, n₁ = 0, n₂ = n+1. First part is ReachesIn.refl, second part is h itself (since [] ++ v = v).

  Subcase w = a :: w': Use reachesIn_iff_split_first to get ∃ c, ReachesIn 1 ⟨q, a :: (w' ++ v), α⟩ c ∧ ReachesIn n c ⟨p, [], δ⟩.
  Note that a :: (w' ++ v) = List.cons a (w' ++ v).

  The first step (ReachesIn 1) means c ∈ step ⟨q, a :: (w' ++ v), α⟩.
  Case α = []: step from empty stack is ∅, contradiction.
  Case α = Z :: β: The step gives two sub-cases:
    (a) Read transition: c = ⟨q₁, w' ++ v, γ₁ ++ β⟩ for some q₁ γ₁ with (q₁, γ₁) ∈ M.transition_fun q a Z.
        Apply ih to get splitting: ∃ q' γ n₁ n₂, ReachesIn n₁ ⟨q₁, w', γ₁ ++ β⟩ ⟨q', [], γ⟩ ∧ ReachesIn n₂ ⟨q', v, γ⟩ ⟨p, [], δ⟩.
        Now construct: ReachesIn (n₁+1) ⟨q, a :: w', Z :: β⟩ ⟨q', [], γ⟩ using reachesIn_of_one_n with the read step ⟨q, a :: w', Z :: β⟩ → ⟨q₁, w', γ₁ ++ β⟩.
        This read step is valid because (q₁, γ₁) ∈ M.transition_fun q a Z (same membership).
        Use reaches₁_iff_reachesIn_one to convert.
    (b) ε-transition: c = ⟨q₁, a :: (w' ++ v), γ₁ ++ β⟩ for some q₁ γ₁ with (q₁, γ₁) ∈ M.transition_fun' q Z.
        Note: a :: (w' ++ v) = (a :: w') ++ v, so c = ⟨q₁, (a :: w') ++ v, γ₁ ++ β⟩.
        Apply ih to get splitting: ∃ q' γ n₁ n₂, ReachesIn n₁ ⟨q₁, a :: w', γ₁ ++ β⟩ ⟨q', [], γ⟩ ∧ ReachesIn n₂ ⟨q', v, γ⟩ ⟨p, [], δ⟩.
        Now construct: ReachesIn (n₁+1) ⟨q, a :: w', Z :: β⟩ ⟨q', [], γ⟩ using reachesIn_of_one_n with the epsilon step ⟨q, a :: w', Z :: β⟩ → ⟨q₁, a :: w', γ₁ ++ β⟩.
        This ε-step is valid because (q₁, γ₁) ∈ M.transition_fun' q Z (same membership).
        Use reaches₁_iff_reachesIn_one to convert.
-/
theorem input_splitting_reachesIn {n : ℕ} {q p : Q} {w v : List T} {α δ : List S}
    (h : M.ReachesIn n ⟨q, w ++ v, α⟩ ⟨p, [], δ⟩) :
    ∃ q' : Q, ∃ γ : List S, ∃ n₁ n₂ : ℕ,
      M.ReachesIn n₁ ⟨q, w, α⟩ ⟨q', [], γ⟩ ∧
      M.ReachesIn n₂ ⟨q', v, γ⟩ ⟨p, [], δ⟩ := by
  by_cases hw : w = [];
  · use q, α, 0, n
    aesop;
  · induction' n with n ih generalizing q p w v α δ;
    · cases w <;> cases v <;> cases α <;> cases δ <;> cases h <;> tauto;
    · obtain ⟨c, hc⟩ : ∃ c : PDA.conf M, ReachesIn 1 ⟨q, w ++ v, α⟩ c ∧ ReachesIn n c ⟨p, [], δ⟩ := by
        have := h;
        convert this using 1;
        rw [reachesIn_iff_split_first];
      rcases w with ( _ | ⟨ a, w ⟩ ) <;> rcases α with ( _ | ⟨ Z, α ⟩ ) <;> simp_all +decide [ PDA.step ];
      · rcases hc with ⟨ hc₁, hc₂ ⟩;
        obtain ⟨ q', α, hq', rfl ⟩ := hc₁;
        rename_i r₂ hr₁ hr₂;
        obtain ⟨ rfl, rfl, rfl ⟩ := reachesIn_zero hr₁;
        obtain ⟨ c, hc₁, hc₂ ⟩ := hr₂;
      · obtain ⟨q₁, β, hβ, hc⟩ : ∃ q₁ β, (q₁, β) ∈ M.transition_fun q a Z ∧ c = ⟨q₁, w ++ v, β ++ α⟩ ∨ (q₁, β) ∈ M.transition_fun' q Z ∧ c = ⟨q₁, a :: (w ++ v), β ++ α⟩ := by
          have := hc.1;
          rw [reachesIn_one] at this;
          unfold step at this; aesop;
        · by_cases hw : w = [] <;> simp_all +decide [ PDA.ReachesIn ];
          · use q₁, β ++ α;
            exact ⟨ ⟨ 1, by
              constructor;
              constructor;
              constructor;
              exact ⟨ q₁, β, hβ, rfl ⟩ ⟩, ⟨ n, by
              tauto ⟩ ⟩;
          · obtain ⟨ q', γ, ⟨ x, hx ⟩, y, hy ⟩ := ih ( by tauto ) hw;
            use q', γ, ⟨ x + 1, ?_ ⟩, y, hy;
            exact PDA.reachesIn_of_one_n ( by exact PDA.reachesIn_one.mpr <| by exact Set.mem_union_left _ <| Set.mem_setOf.mpr ⟨ q₁, β, hβ, rfl ⟩ ) hx;
        · contrapose! ih;
          use q₁, p, a :: w, v, β ++ α, δ;
          simp_all +decide [ List.append_assoc ];
          intro q' γ x hx y hy; exact ih q' γ ( x + 1 ) ( by
            apply PDA.reachesIn_of_one_n;
            convert PDA.reachesIn_one.mpr _;
            exact ⟨ q₁, a :: w, β ++ α ⟩;
            · exact Or.inr ⟨ q₁, β, by tauto ⟩;
            · exact hx ) y hy;

/-- **Input splitting** (`Reaches` version). -/
theorem input_splitting {q p : Q} {w v : List T} {α δ : List S}
    (h : M.Reaches ⟨q, w ++ v, α⟩ ⟨p, [], δ⟩) :
    ∃ q' : Q, ∃ γ : List S,
      M.Reaches ⟨q, w, α⟩ ⟨q', [], γ⟩ ∧ M.Reaches ⟨q', v, γ⟩ ⟨p, [], δ⟩ := by
  rw [reaches_iff_reachesIn] at h
  obtain ⟨n, h⟩ := h
  obtain ⟨q', γ, n₁, n₂, h₁, h₂⟩ := input_splitting_reachesIn h
  exact ⟨q', γ, reaches_of_reachesIn h₁, reaches_of_reachesIn h₂⟩

end PDA

-- ══════════════════════════════════════════════════════════════════
-- § 2  Prefix PDA construction
-- ══════════════════════════════════════════════════════════════════

namespace PrefixClosure

variable {Q S : Type} [Fintype Q] [Fintype S]

/-- The **prefix PDA**.
States are `Q ⊕ Q` where `Sum.inl q` is *normal mode* and `Sum.inr q`
is *verification mode*. -/
noncomputable def prefixPDA (M : PDA Q T S) : PDA (Q ⊕ Q) T S where
  initial_state := Sum.inl M.initial_state
  start_symbol  := M.start_symbol
  final_states  := ∅
  -- In normal mode, read transitions mirror M.
  -- In verification mode, there are no read transitions.
  transition_fun := fun s a Z =>
    match s with
    | Sum.inl q => (M.transition_fun q a Z).image (Prod.map Sum.inl id)
    | Sum.inr _ => ∅
  -- In normal mode, ε-transitions mirror M plus a switch to verification mode.
  -- In verification mode, ε-transitions include ALL of M's transitions
  -- (both reads and ε), allowing the PDA to simulate M without consuming input.
  transition_fun' := fun s Z =>
    match s with
    | Sum.inl q =>
        (M.transition_fun' q Z).image (Prod.map Sum.inl id) ∪ {(Sum.inr q, [Z])}
    | Sum.inr q =>
        (M.transition_fun' q Z).image (Prod.map Sum.inr id) ∪
        ⋃ a : T, (M.transition_fun q a Z).image (Prod.map Sum.inr id)
  finite := fun s a Z => by
    cases s with
    | inl q => exact (M.finite q a Z).image _
    | inr   => exact Set.finite_empty
  finite' := fun s Z => by
    cases s with
    | inl q => exact ((M.finite' q Z).image _).union (Set.finite_singleton _)
    | inr q =>
        apply Set.Finite.union
        · exact (M.finite' q Z).image _
        · exact Set.finite_iUnion (fun a => (M.finite q a Z).image _)

-- ══════════════════════════════════════════════════════════════════
-- § 3  Forward direction :  prefixLang L ⊆ prefixPDA.acceptsByEmptyStack
-- ══════════════════════════════════════════════════════════════════

section Forward

variable {M : PDA Q T S}

/-
PROBLEM
An `M`-step in normal mode lifts to a `prefixPDA M`-step in `Sum.inl` states.

PROVIDED SOLUTION
Unfold Reaches₁ and step for both the original PDA M and the prefixPDA M. For every case of the step function (read from a::w with Z::α, epsilon from a::w with Z::α, epsilon from [] with Z::α), the prefixPDA M mirrors the transition via image under Prod.map Sum.inl id. So for each case, show that the new config with Sum.inl states is in the step set of prefixPDA M. Need careful case analysis on c₁.input and c₁.stack.
-/
private theorem inl_step_of_M_step (c₁ c₂ : M.conf) (h : M.Reaches₁ c₁ c₂) :
    (prefixPDA M).Reaches₁
      ⟨Sum.inl c₁.state, c₁.input, c₁.stack⟩
      ⟨Sum.inl c₂.state, c₂.input, c₂.stack⟩ := by
  cases c₁ ; cases c₂ ; simp [ Reaches₁, step ] at *;
  rename_i q w α q' w' α' h';
  rcases α with ( _ | ⟨ a, α ⟩ ) <;> rcases q' with ( _ | ⟨ Z, α' ⟩ ) <;> simp_all +decide [ prefixPDA ]

/-
PROBLEM
If `M` reaches `c₂` from `c₁`, then `prefixPDA M` reaches the corresponding
`Sum.inl` configuration.

PROVIDED SOLUTION
By induction on the Reaches relation (which is ReflTransGen of Reaches₁).
Base case: Reaches.refl, so c₁ = c₂, and the prefixPDA trivially reaches from the same config.
Step case: Reaches c₁ c' ∧ Reaches₁ c' c₂. By IH, prefixPDA reaches inl-c' from inl-c₁. By inl_step_of_M_step, prefixPDA reaches inl-c₂ from inl-c'. Compose using Relation.ReflTransGen.tail.
-/
private theorem inl_reaches_of_M_reaches (c₁ c₂ : M.conf) (h : M.Reaches c₁ c₂) :
    (prefixPDA M).Reaches
      ⟨Sum.inl c₁.state, c₁.input, c₁.stack⟩
      ⟨Sum.inl c₂.state, c₂.input, c₂.stack⟩ := by
  induction h <;> simp_all +decide [ Reaches ];
  · rfl;
  · exact Relation.ReflTransGen.tail ‹_› ( by exact? )

/-
PROBLEM
Switching from normal mode to verification mode (ε-step, stack unchanged).

PROVIDED SOLUTION
Unfold Reaches₁ and step for prefixPDA M. From config ⟨Sum.inl q, w, Z :: β⟩, the step function gives:
- If w = []: step matches ⟨Sum.inl q, [], Z :: β⟩, transition_fun' for Sum.inl q includes {(Sum.inr q, [Z])}. So the result ⟨Sum.inr q, [], [Z] ++ β⟩ = ⟨Sum.inr q, [], Z :: β⟩ is in the step set.
- If w = a :: w': step matches ⟨Sum.inl q, a :: w', Z :: β⟩, and the union includes ε-transitions. The transition_fun' for Sum.inl q includes {(Sum.inr q, [Z])}. So ⟨Sum.inr q, a :: w', [Z] ++ β⟩ = ⟨Sum.inr q, a :: w', Z :: β⟩ is in the step set.
In both cases, (Sum.inr q, [Z]) ∈ transition_fun' (Sum.inl q) Z because it's in the union (the singleton part). The result configuration has stack [Z] ++ β = Z :: β, so the stack is unchanged.
-/
private theorem switch_step {q : Q} {w : List T} {Z : S} {β : List S} :
    (prefixPDA M).Reaches₁ ⟨Sum.inl q, w, Z :: β⟩ ⟨Sum.inr q, w, Z :: β⟩ := by
  cases' w with a w' <;> simp +decide [ *, Reaches₁ ];
  · simp +decide [ step ];
    unfold prefixPDA; aesop;
  · simp +decide [ step, M.finite', M.finite ];
    unfold prefixPDA; aesop;

/-
PROBLEM
If `M` reaches `⟨p, [], []⟩` from `⟨q, v, γ⟩`, then in verification mode
the prefix PDA reaches `⟨Sum.inr p, [], []⟩` from `⟨Sum.inr q, [], γ⟩`.

PROVIDED SOLUTION
By induction on the Reaches relation (ReflTransGen).
Base case: h is refl, so q = p and γ = [] and v = []. The prefixPDA trivially reaches from ⟨Sum.inr q, [], []⟩ to itself.
Step case: M.Reaches ⟨q, v, γ⟩ c' ∧ M.Reaches₁ c' ⟨p, [], []⟩.
By IH, (prefixPDA M).Reaches ⟨Sum.inr q, [], γ⟩ ⟨Sum.inr c'.state, [], c'.stack⟩.
Wait, this doesn't quite work because the IH gives us the result for (q, v, γ) to c', but we need the prefixPDA result for (Sum.inr q, [], γ) to something.

Actually, let me use ReachesIn and induction on number of steps instead.

Use reaches_iff_reachesIn to get n steps. Then induction on n.
Base case: 0 steps means ⟨q, v, γ⟩ = ⟨p, [], []⟩, so q = p, v = [], γ = []. Trivially (prefixPDA M).Reaches ⟨Sum.inr q, [], []⟩ ⟨Sum.inr q, [], []⟩.

Inductive case (n+1 steps): Use reachesIn_iff_split_first to get first step: ∃ c, M.Reaches₁ ⟨q, v, γ⟩ c ∧ M.ReachesIn n c ⟨p, [], []⟩.
The first M-step from ⟨q, v, γ⟩ is either a read (consuming first char of v) or ε-transition.

For the prefixPDA in verification mode (Sum.inr), ALL of M's transitions become ε-transitions:
- If M reads 'a' from v: transition_fun q a Z is used. In prefixPDA, transition_fun' (Sum.inr q) Z includes (M.transition_fun q a Z).image (Prod.map Sum.inr id) (via the ⋃ a part). So this becomes an ε-step in prefixPDA.
- If M does ε-transition: transition_fun' q Z is used. In prefixPDA, transition_fun' (Sum.inr q) Z includes (M.transition_fun' q Z).image (Prod.map Sum.inr id). Same ε-step.

So each M-step lifts to a prefixPDA ε-step from ⟨Sum.inr q, [], γ⟩ to ⟨Sum.inr c.state, [], c.stack⟩.

Key: the prefixPDA ε-step doesn't consume input (input stays []), and it produces Sum.inr states.

After this first step, apply IH to the remaining n steps from c to ⟨p, [], []⟩, getting (prefixPDA M).Reaches ⟨Sum.inr c.state, [], c.stack⟩ ⟨Sum.inr p, [], []⟩.

Compose the two Reaches to get the result.
-/
private theorem verify_reaches_of_M_reaches
    {q p : Q} {v : List T} {γ : List S}
    (h : M.Reaches ⟨q, v, γ⟩ ⟨p, [], []⟩) :
    (prefixPDA M).Reaches ⟨Sum.inr q, [], γ⟩ ⟨Sum.inr p, [], []⟩ := by
  have h_ind : ∀ n : ℕ, ∀ (c₁ c₂ : M.conf), M.ReachesIn n c₁ c₂ → (prefixPDA M).Reaches ⟨Sum.inr c₁.state, [], c₁.stack⟩ ⟨Sum.inr c₂.state, [], c₂.stack⟩ := by
    intro n c₁ c₂ h;
    induction' h with c₁ c₂ h ih;
    · constructor;
    · rename_i h₁ h₂ h₃;
      have h_step : ∀ (c₁ c₂ : M.conf), M.Reaches₁ c₁ c₂ → (prefixPDA M).Reaches₁ ⟨Sum.inr c₁.state, [], c₁.stack⟩ ⟨Sum.inr c₂.state, [], c₂.stack⟩ := by
        intros c₁ c₂ h_step
        cases' c₁ with q₁ x₁ Z₁ α₁
        cases' c₂ with q₂ x₂ Z₂ α₂
        simp [Reaches₁] at h_step ⊢
        generalize_proofs at *; (
        cases' x₁ with a₁ x₁ <;> cases' Z₁ with Z₁ α₁ <;> simp_all +decide [ step ];
        · obtain ⟨ β, hβ₁, hβ₂, hβ₃ ⟩ := h_step; use β; simp_all +decide [ prefixPDA ] ;
        · rcases h_step with ( ⟨ β, hβ, rfl, rfl ⟩ | ⟨ β, hβ, rfl, rfl ⟩ ) <;> [ exact ⟨ β, by unfold prefixPDA; aesop ⟩ ; exact ⟨ β, by unfold prefixPDA; aesop ⟩ ] ;);
      exact h₃.trans ( h_step _ _ h₂ |> fun h => Relation.ReflTransGen.single h );
  obtain ⟨ n, hn ⟩ := reaches_iff_reachesIn.mp h; specialize h_ind n ⟨ q, v, γ ⟩ ⟨ p, [], [] ⟩ hn; aesop;

/-
PROBLEM
**Forward direction**: every prefix of a word in `M.acceptsByEmptyStack`
is accepted by the prefix PDA.

PROVIDED SOLUTION
We need to show: if w ∈ prefixLang (M.acceptsByEmptyStack), then w ∈ (prefixPDA M).acceptsByEmptyStack.

Unfold definitions: w ∈ prefixLang means ∃ v, w ++ v ∈ M.acceptsByEmptyStack, which means ∃ v q, M.Reaches ⟨M.initial_state, w ++ v, [M.start_symbol]⟩ ⟨q, [], []⟩.

By input_splitting: ∃ q' γ, M.Reaches ⟨M.initial_state, w, [M.start_symbol]⟩ ⟨q', [], γ⟩ ∧ M.Reaches ⟨q', v, γ⟩ ⟨q, [], []⟩.

For (prefixPDA M).acceptsByEmptyStack, we need: ∃ s, (prefixPDA M).Reaches ⟨Sum.inl M.initial_state, w, [M.start_symbol]⟩ ⟨s, [], []⟩.

Case γ = []:
  By inl_reaches_of_M_reaches: (prefixPDA M).Reaches ⟨Sum.inl M.initial_state, w, [M.start_symbol]⟩ ⟨Sum.inl q', [], []⟩.
  Use s = Sum.inl q'.

Case γ = Z :: β (γ ≠ []):
  Step 1: By inl_reaches_of_M_reaches: (prefixPDA M).Reaches ⟨Sum.inl M.initial_state, w, [M.start_symbol]⟩ ⟨Sum.inl q', [], Z :: β⟩.
  Step 2: By switch_step: (prefixPDA M).Reaches₁ ⟨Sum.inl q', [], Z :: β⟩ ⟨Sum.inr q', [], Z :: β⟩.
  Step 3: By verify_reaches_of_M_reaches applied to M.Reaches ⟨q', v, Z :: β⟩ ⟨q, [], []⟩:
    (prefixPDA M).Reaches ⟨Sum.inr q', [], Z :: β⟩ ⟨Sum.inr q, [], []⟩.
  Compose steps 1, 2, 3. Use s = Sum.inr q.
-/
theorem prefixPDA_supset (M : PDA Q T S) :
    Language.prefixLang M.acceptsByEmptyStack ≤ (prefixPDA M).acceptsByEmptyStack := by
  intro w hw
  obtain ⟨v, hv⟩ := hw;
  obtain ⟨q, hq⟩ : ∃ q : Q, M.Reaches ⟨M.initial_state, w ++ v, [M.start_symbol]⟩ ⟨q, [], []⟩ := by
    exact hv.imp fun q hq => hq;
  obtain ⟨ q', γ, hq', hγ ⟩ := input_splitting hq;
  cases' γ with Z β;
  · use Sum.inl q';
    convert inl_reaches_of_M_reaches _ _ hq' using 1;
  · -- By inl_reaches_of_M_reaches, we have that (prefixPDA M).Reaches ⟨Sum.inl M.initial_state, w, [M.start_symbol]⟩ ⟨Sum.inl q', [], Z :: β⟩.
    have h_inl : (prefixPDA M).Reaches ⟨Sum.inl M.initial_state, w, [M.start_symbol]⟩ ⟨Sum.inl q', [], Z :: β⟩ := by
      convert inl_reaches_of_M_reaches _ _ hq' using 1;
    -- By switch_step, we have that (prefixPDA M).Reaches₁ ⟨Sum.inl q', [], Z :: β⟩ ⟨Sum.inr q', [], Z :: β⟩.
    have h_switch : (prefixPDA M).Reaches₁ ⟨Sum.inl q', [], Z :: β⟩ ⟨Sum.inr q', [], Z :: β⟩ := by
      apply switch_step;
    -- By verify_reaches_of_M_reaches, we have that (prefixPDA M).Reaches ⟨Sum.inr q', [], Z :: β⟩ ⟨Sum.inr q, [], []⟩.
    have h_verify : (prefixPDA M).Reaches ⟨Sum.inr q', [], Z :: β⟩ ⟨Sum.inr q, [], []⟩ := by
      exact?;
    use Sum.inr q;
    exact h_inl.trans ( Relation.ReflTransGen.single h_switch ) |> Relation.ReflTransGen.trans <| h_verify

end Forward

-- ══════════════════════════════════════════════════════════════════
-- § 4  Backward direction :  prefixPDA.acceptsByEmptyStack ⊆ prefixLang L
-- ══════════════════════════════════════════════════════════════════

section Backward

variable {M : PDA Q T S}

/-
PROBLEM
A single step from a `Sum.inr` state in the prefix PDA preserves the input.

PROVIDED SOLUTION
Unfold Reaches₁ as c ∈ step ⟨Sum.inr q, w, γ⟩. Case split on w and γ:
- γ = []: step from empty stack is ∅, contradiction.
- γ = Z :: β, w = []: step only has ε-transitions (transition_fun'). ε-transitions produce ⟨p, [], β' ++ β⟩, so c.input = [].  Since transition_fun for Sum.inr is ∅, only transition_fun' contributes. The result has input [] = w. ✓
- γ = Z :: β, w = a :: w': step has read and ε parts. For Sum.inr, transition_fun is ∅, so the read part is empty. Only ε-transitions remain, producing ⟨p, a :: w', β' ++ β⟩. So c.input = a :: w' = w. ✓
-/
private theorem inr_step_preserves_input {q : Q} {w : List T}
    {γ : List S} {c : (prefixPDA M).conf}
    (h : (prefixPDA M).Reaches₁ ⟨Sum.inr q, w, γ⟩ c) :
    c.input = w := by
  cases γ <;> cases w <;> simp_all +decide [ Reaches₁ ];
  · cases h;
  · cases h;
  · cases h ; aesop;
  · cases h ; aesop;
    grind +revert

/-
PROBLEM
A single step from a `Sum.inr` state stays in `Sum.inr`.

PROVIDED SOLUTION
Same case analysis as inr_step_preserves_input. From ⟨Sum.inr q, w, γ⟩:
- γ = []: step is ∅, contradiction.
- γ = Z :: β: In the step function, for Sum.inr states, transition_fun is ∅ (no read transitions). Only transition_fun' applies. All transitions in transition_fun' for Sum.inr q produce states of the form (Sum.inr p, β') (since they come from images under Prod.map Sum.inr id). So c.state = Sum.inr p for some p.
-/
private theorem inr_step_stays_inr {q : Q} {w : List T}
    {γ : List S} {c : (prefixPDA M).conf}
    (h : (prefixPDA M).Reaches₁ ⟨Sum.inr q, w, γ⟩ c) :
    ∃ q' : Q, c.state = Sum.inr q' := by
  cases γ <;> cases c <;> simp_all +decide [ Reaches₁ ];
  · -- Since the transition function for Sum.inr q with an empty stack is empty, the assumption that the state is in the step function must be false.
    have h_empty : (prefixPDA M).step ⟨Sum.inr q, w, []⟩ = ∅ := by
      unfold step; aesop;
    aesop;
  · cases ‹Q ⊕ Q› <;> simp +decide [ step ] at h ⊢;
    cases w <;> simp_all +decide [ prefixPDA ]

/-
PROBLEM
In verification (`Sum.inr`) mode the input never changes.

PROVIDED SOLUTION
By induction on n.
Base case (n=0): ReachesIn 0 means configs equal by reachesIn_zero, so c.input = w.
Inductive case (n+1): Use reachesIn_iff_split_last to get ∃ c', ReachesIn n ⟨Sum.inr q, w, γ⟩ c' ∧ ReachesIn 1 c' c.
By IH, c'.input = w. Also by inr_step_stays_inr applied repeatedly, c'.state = Sum.inr q' for some q'. Then the last step is Reaches₁ from ⟨Sum.inr q', w, c'.stack⟩ to c. By inr_step_preserves_input, c.input = w.
-/
private theorem inr_input_invariant {n : ℕ} {q : Q} {w : List T}
    {γ : List S} {c : (prefixPDA M).conf}
    (h : (prefixPDA M).ReachesIn n ⟨Sum.inr q, w, γ⟩ c) :
    c.input = w := by
  induction' n with n ih generalizing w γ c;
  · cases h ; aesop;
  · obtain ⟨c', hc₁, hc₂⟩ : ∃ c', ReachesIn n ⟨Sum.inr q, w, γ⟩ c' ∧ ReachesIn 1 c' c := by
      obtain ⟨c', hc'⟩ : ∃ c' : (prefixPDA M).conf, ReachesIn n ⟨Sum.inr q, w, γ⟩ c' ∧ ReachesIn 1 c' c := by
        have := h
        exact?;
      use c';
    obtain ⟨q', hq'⟩ : ∃ q' : Q, c'.state = Sum.inr q' := by
      have h_last_step : ∀ {c : (prefixPDA M).conf}, (prefixPDA M).Reaches ⟨Sum.inr q, w, γ⟩ c → ∃ q' : Q, c.state = Sum.inr q' := by
        intro c hc; induction' hc with c₁ c₂ hc₁ hc₂ ih; aesop;
        obtain ⟨ q', hq' ⟩ := ih; rcases c₁ with ⟨ s₁, w₁, γ₁ ⟩ ; rcases c₂ with ⟨ s₂, w₂, γ₂ ⟩ ; simp_all +decide [ Reaches₁ ] ;
        cases γ₁ <;> simp_all +decide [ step ];
        cases w₁ <;> simp_all +decide [ Reaches₁ ];
        · unfold prefixPDA at hc₂; aesop;
        · unfold prefixPDA at hc₂; aesop;
      apply h_last_step;
      exact?;
    obtain ⟨c'', hc₃, hc₄⟩ : ∃ c'', ReachesIn 1 ⟨Sum.inr q', w, c'.stack⟩ c'' ∧ c'' = c := by
      have h_eq : c'.input = w := by
        exact ih hc₁;
      cases c' ; aesop;
    obtain ⟨c''', hc₅, hc₆⟩ : ∃ c''', Reaches₁ ⟨Sum.inr q', w, c'.stack⟩ c''' ∧ c''' = c'' := by
      obtain ⟨c''', hc₅, hc₆⟩ := hc₃;
      rename_i r₂ hr₂ hr₃;
      cases hr₂ ; aesop;
    have := inr_step_preserves_input hc₅; aesop;

/-
PROBLEM
A single step from a `Sum.inl` configuration in the prefix PDA is either
(a) a lift of an `M`-step staying in `Sum.inl`, or
(b) a switch to `Sum.inr` preserving state, input, and stack.

PROVIDED SOLUTION
Unfold Reaches₁ as c ∈ step ⟨Sum.inl q, w, α⟩. Case split on w and α:
- α = []: step is ∅, contradiction.
- α = Z :: β, w = []: step only has ε-transitions. For Sum.inl q, transition_fun' gives (M.transition_fun' q Z).image (Prod.map Sum.inl id) ∪ {(Sum.inr q, [Z])}.
  Each element is either (Sum.inl p, β') from M's ε-transition (giving case (a) with M.Reaches₁), or (Sum.inr q, [Z]) giving c = ⟨Sum.inr q, [], [Z] ++ β⟩ = ⟨Sum.inr q, [], Z :: β⟩ = ⟨Sum.inr q, w, α⟩ (case (b)).
- α = Z :: β, w = a :: w': step has read and ε.
  Read transitions: (M.transition_fun q a Z).image (Prod.map Sum.inl id). Gives (Sum.inl p, β') pairs, producing ⟨Sum.inl p, w', β' ++ β⟩. This is case (a) with a read M-step.
  ε-transitions: (M.transition_fun' q Z).image (Prod.map Sum.inl id) ∪ {(Sum.inr q, [Z])}. The first part gives (Sum.inl p, β') producing ⟨Sum.inl p, a :: w', β' ++ β⟩ (case (a) with an ε M-step). The singleton {(Sum.inr q, [Z])} gives ⟨Sum.inr q, a :: w', Z :: β⟩ = ⟨Sum.inr q, w, α⟩ (case (b)).
-/
private theorem inl_step_cases {c : (prefixPDA M).conf}
    {q : Q} {w : List T} {α : List S}
    (h : (prefixPDA M).Reaches₁ ⟨Sum.inl q, w, α⟩ c) :
    (∃ q' : Q, ∃ w' : List T, ∃ α' : List S,
      c = ⟨Sum.inl q', w', α'⟩ ∧ M.Reaches₁ ⟨q, w, α⟩ ⟨q', w', α'⟩) ∨
    (c = ⟨Sum.inr q, w, α⟩) := by
  cases w <;> cases α <;> simp_all +decide [ Reaches₁ ];
  · unfold step at h; aesop;
  · unfold step at h;
    unfold prefixPDA at h; simp_all +decide [ Set.mem_union, Set.mem_setOf_eq ] ;
    unfold step; aesop;
  · unfold step at h; aesop;
  · cases h <;> simp_all +decide [ step ];
    · unfold prefixPDA at *; aesop;
    · unfold prefixPDA at *; aesop;

/-
PROBLEM
A single step in verification mode from empty input decomposes into an M-transition.

An ε-transition membership gives an M-step.

PROVIDED SOLUTION
Unfold Reaches₁ and step for ⟨Sum.inr q, [], Z :: β⟩. This matches the case ⟨q', [], Z :: α⟩ in the step function, giving:
c ∈ { r₂ | ∃ p β', (p, β') ∈ (prefixPDA M).transition_fun' (Sum.inr q) Z ∧ r₂ = ⟨p, [], β' ++ β⟩ }
So ∃ p β', (p, β') ∈ (prefixPDA M).transition_fun' (Sum.inr q) Z ∧ c = ⟨p, [], β' ++ β⟩.
Since transition_fun' (Sum.inr q) Z = (M.transition_fun' q Z).image (Prod.map Sum.inr id) ∪ ⋃ a, (M.transition_fun q a Z).image (Prod.map Sum.inr id), we have p = Sum.inr q₁ and δ = β' for some q₁, and either (q₁, δ) ∈ M.transition_fun' q Z or ∃ a, (q₁, δ) ∈ M.transition_fun q a Z.

Unfold Reaches₁ as membership in step. From ⟨q, w, Z :: β⟩, the step function includes ε-transitions:
- If w = []: step = { r₂ | ∃ p β', (p,β') ∈ transition_fun' q Z ∧ r₂ = ⟨p, [], β' ++ β⟩ }. Since (q₁, δ) ∈ transition_fun' q Z, ⟨q₁, [], δ ++ β⟩ is in this set.
- If w = a :: w': step = read_set ∪ eps_set. eps_set = { r₂ | ∃ p β', (p,β') ∈ transition_fun' q Z ∧ r₂ = ⟨p, a :: w', β' ++ β⟩ }. Since (q₁, δ) ∈ transition_fun' q Z, ⟨q₁, a :: w', δ ++ β⟩ is in eps_set.
In both cases, ⟨q₁, w, δ ++ β⟩ ∈ step ⟨q, w, Z :: β⟩.
-/
private theorem M_eps_step {q q₁ : Q} {w : List T} {Z : S} {β δ : List S}
    (h : (q₁, δ) ∈ M.transition_fun' q Z) :
    M.Reaches₁ ⟨q, w, Z :: β⟩ ⟨q₁, w, δ ++ β⟩ := by
  cases w <;> simp_all +decide [ Reaches₁, PDA.step ]

/-
PROBLEM
A read-transition membership gives an M-step.

PROVIDED SOLUTION
Unfold Reaches₁ as membership in step. From ⟨q, a :: w, Z :: β⟩, the step function includes:
read_set = { r₂ | ∃ p β', (p,β') ∈ transition_fun q a Z ∧ r₂ = ⟨p, w, β' ++ β⟩ }.
Since (q₁, δ) ∈ transition_fun q a Z, ⟨q₁, w, δ ++ β⟩ is in read_set ⊆ step.
-/
private theorem M_read_step {q q₁ : Q} {a : T} {w : List T} {Z : S} {β δ : List S}
    (h : (q₁, δ) ∈ M.transition_fun q a Z) :
    M.Reaches₁ ⟨q, a :: w, Z :: β⟩ ⟨q₁, w, δ ++ β⟩ := by
  -- By definition of Reaches₁, we need to show that there exists a next state and stack such that the current state's transition function includes this next state and stack.
  apply Set.mem_union_left; exact (by
  exact ⟨ q₁, δ, h, rfl ⟩)

private theorem verify_step_decompose {q : Q} {Z : S} {β : List S}
    {c : (prefixPDA M).conf}
    (h : (prefixPDA M).Reaches₁ ⟨Sum.inr q, [], Z :: β⟩ c) :
    ∃ q₁ : Q, ∃ δ : List S, c = ⟨Sum.inr q₁, [], δ ++ β⟩ ∧
    (((q₁, δ) ∈ M.transition_fun' q Z) ∨ (∃ a : T, (q₁, δ) ∈ M.transition_fun q a Z)) := by
  obtain ⟨h₁, h₂⟩ := h;
  rcases h₂ with ⟨ δ, hδ, rfl ⟩ ; rcases h₁ with ( _ | _ ) <;> simp_all +decide [ prefixPDA ] ;

/-
PROBLEM
A verification-mode computation reaching empty stack corresponds to
an `M`-computation on some word `v`.

PROVIDED SOLUTION
Induction on n.
Base case (n=0): reachesIn_zero gives q = p and γ = []. Use v = [].

Inductive case (n+1): Use reachesIn_iff_split_first to get ∃ c, ReachesIn 1 ⟨Sum.inr q, [], γ⟩ c ∧ ReachesIn n c ⟨Sum.inr p, [], []⟩.

γ must be nonempty (otherwise step from empty stack is ∅, contradicting the first step). Write γ = Z :: β.

Convert the first step to Reaches₁ and apply verify_step_decompose:
∃ q₁ δ, c = ⟨Sum.inr q₁, [], δ ++ β⟩ ∧ ((q₁, δ) ∈ M.transition_fun' q Z ∨ ∃ a, (q₁, δ) ∈ M.transition_fun q a Z).

Apply IH (with n steps) to get ∃ v₁, M.Reaches ⟨q₁, v₁, δ ++ β⟩ ⟨p, [], []⟩.

Case (q₁, δ) ∈ M.transition_fun' q Z:
  By M_eps_step: M.Reaches₁ ⟨q, v₁, Z :: β⟩ ⟨q₁, v₁, δ ++ β⟩.
  Compose with IH: M.Reaches ⟨q, v₁, Z :: β⟩ ⟨p, [], []⟩. Use v = v₁.

Case ∃ a, (q₁, δ) ∈ M.transition_fun q a Z:
  By M_read_step: M.Reaches₁ ⟨q, a :: v₁, Z :: β⟩ ⟨q₁, v₁, δ ++ β⟩.
  Compose with IH: M.Reaches ⟨q, a :: v₁, Z :: β⟩ ⟨p, [], []⟩. Use v = a :: v₁.
-/
private theorem M_reaches_of_verify_reachesIn {n : ℕ}
    {q p : Q} {γ : List S}
    (h : (prefixPDA M).ReachesIn n ⟨Sum.inr q, [], γ⟩ ⟨Sum.inr p, [], []⟩) :
    ∃ v : List T, M.Reaches ⟨q, v, γ⟩ ⟨p, [], []⟩ := by
  by_contra h_contra;
  have h_ind : ∀ n q p γ, (prefixPDA M).ReachesIn n ⟨Sum.inr q, [], γ⟩ ⟨Sum.inr p, [], []⟩ → (∃ v : List T, M.Reaches ⟨q, v, γ⟩ ⟨p, [], []⟩) := by
    intro n q p γ h
    induction' n with n ih generalizing q p γ;
    · cases h ; aesop;
    · obtain ⟨c, hc⟩ : ∃ c : (prefixPDA M).conf, (prefixPDA M).ReachesIn 1 ⟨Sum.inr q, [], γ⟩ c ∧ (prefixPDA M).ReachesIn n c ⟨Sum.inr p, [], []⟩ := by
        exact?;
      rcases γ with ( _ | ⟨ Z, β ⟩ ) <;> simp_all +decide [ ReachesIn ];
      · rcases hc with ⟨ ⟨ c, hc₁, hc₂ ⟩, hc₃ ⟩;
        rename_i r₂ hr₂ hr₃;
        rcases hr₂ with ⟨ ⟩;
        rcases hr₃ with ⟨ ⟩;
      · obtain ⟨q₁, δ, hc₁, hc₂⟩ : ∃ q₁ : Q, ∃ δ : List S, c = ⟨Sum.inr q₁, [], δ ++ β⟩ ∧ (((q₁, δ) ∈ M.transition_fun' q Z) ∨ (∃ a : T, (q₁, δ) ∈ M.transition_fun q a Z)) := by
          apply verify_step_decompose;
          grind +suggestions;
        obtain ⟨v₁, hv₁⟩ : ∃ v₁ : List T, M.Reaches ⟨q₁, v₁, δ ++ β⟩ ⟨p, [], []⟩ := by
          exact ih q₁ p ( δ ++ β ) ( by simpa only [ hc₁ ] using hc.2 );
        cases' hc₂ with hc₂ hc₂;
        · use v₁;
          have h_eps_step : M.Reaches₁ ⟨q, v₁, Z :: β⟩ ⟨q₁, v₁, δ ++ β⟩ := by
            exact?;
          exact Relation.ReflTransGen.head h_eps_step hv₁;
        · obtain ⟨ a, ha ⟩ := hc₂;
          use a :: v₁;
          have h_step : M.Reaches₁ ⟨q, a :: v₁, Z :: β⟩ ⟨q₁, v₁, δ ++ β⟩ := by
            exact?;
          exact Relation.ReflTransGen.head h_step hv₁;
  exact h_contra <| h_ind n q p γ h

/-
PROBLEM
Once in `Sum.inr` mode, the state stays `Sum.inr` after any number of steps.

PROVIDED SOLUTION
Induction on n. Base: n=0, c = ⟨Sum.inr q, w, γ⟩, so c.state = Sum.inr q. Inductive: split last step. By IH, intermediate config has state Sum.inr q'. Then by inr_step_stays_inr on the last step, c.state = Sum.inr p.
-/
private theorem inr_stays_inr {n : ℕ} {q : Q} {w : List T} {γ : List S}
    {c : (prefixPDA M).conf}
    (h : (prefixPDA M).ReachesIn n ⟨Sum.inr q, w, γ⟩ c) :
    ∃ p : Q, c.state = Sum.inr p := by
  induction' n with n ih generalizing w γ c;
  · cases h ; aesop;
  · obtain ⟨ c', h₁, h₂ ⟩ := h;
    obtain ⟨ p, hp ⟩ := ih ‹_›;
    have := @inr_step_stays_inr T _ Q S _ _ M;
    rename_i r₂ hr₂ hr₂';
    exact this ( show Reaches₁ ⟨ Sum.inr p, r₂.input, r₂.stack ⟩ c from by simpa only [ ← hp ] using hr₂' )

/-
PROBLEM
Key decomposition: any computation of `prefixPDA M` starting in `Sum.inl`
corresponds to an `M`-computation on some extension `w ++ v` of the input.

PROVIDED SOLUTION
Induction on n.

n=0: reachesIn_zero gives s = Sum.inl q, w = [], α = []. Use v = [], q' = q.

n+1: reachesIn_iff_split_first gives ∃ c, ReachesIn 1 ⟨Sum.inl q, w, α⟩ c ∧ ReachesIn n c ⟨s, [], []⟩.
Convert first step to Reaches₁ via reaches₁_iff_reachesIn_one.

By inl_step_cases:

Case (a): c = ⟨Sum.inl q₁, w₁, α₁⟩, M.Reaches₁ ⟨q, w, α⟩ ⟨q₁, w₁, α₁⟩.
  IH on n steps: ∃ v₁ q', M.Reaches ⟨q₁, w₁ ++ v₁, α₁⟩ ⟨q', [], []⟩.
  Lift M-step with unconsumed_input_one v₁: M.Reaches₁ ⟨q, w ++ v₁, α⟩ ⟨q₁, w₁ ++ v₁, α₁⟩.
  Compose: use v = v₁.

Case (b): c = ⟨Sum.inr q, w, α⟩.
  ReachesIn n ⟨Sum.inr q, w, α⟩ ⟨s, [], []⟩.
  By inr_input_invariant: w = [] (since final input is []).
  By inr_stays_inr: s = Sum.inr p for some p.
  By M_reaches_of_verify_reachesIn: ∃ v, M.Reaches ⟨q, v, α⟩ ⟨p, [], []⟩.
  Since w = []: use this v and q' = p.
-/
private theorem inl_computation_to_M {n : ℕ} {q : Q} {w : List T} {α : List S}
    {s : Q ⊕ Q}
    (h : (prefixPDA M).ReachesIn n ⟨Sum.inl q, w, α⟩ ⟨s, [], []⟩) :
    ∃ v : List T, ∃ q' : Q, M.Reaches ⟨q, w ++ v, α⟩ ⟨q', [], []⟩ := by
  induction' n with n ih generalizing q w α s;
  · cases h ; aesop;
  · obtain ⟨c, hc⟩ : ∃ c : (prefixPDA M).conf, ReachesIn 1 ⟨Sum.inl q, w, α⟩ c ∧ ReachesIn n c ⟨s, [], []⟩ := by
      exact?;
    rcases hc with ⟨hc₁, hc₂⟩
    obtain ⟨q', w', α', hc₃⟩ : ∃ q' : Q, ∃ w' : List T, ∃ α' : List S, c = ⟨Sum.inl q', w', α'⟩ ∧ M.Reaches₁ ⟨q, w, α⟩ ⟨q', w', α'⟩ ∨ c = ⟨Sum.inr q, w, α⟩ := by
      obtain ⟨q', w', α', hc₃⟩ : ∃ q' : Q, ∃ w' : List T, ∃ α' : List S, c = ⟨Sum.inl q', w', α'⟩ ∧ M.Reaches₁ ⟨q, w, α⟩ ⟨q', w', α'⟩ ∨ c = ⟨Sum.inr q, w, α⟩ := by
        have := inl_step_cases (by
        exact? : (prefixPDA M).Reaches₁ ⟨Sum.inl q, w, α⟩ c)
        rcases this with ( ⟨ q', w', α', rfl, h ⟩ | rfl ) <;> [ exact ⟨ q', w', α', Or.inl ⟨ rfl, h ⟩ ⟩ ; exact ⟨ q, w, α, Or.inr rfl ⟩ ]
      generalize_proofs at *;
      use q', w', α';
    cases' hc₃ with hc₃ hc₃;
    · obtain ⟨ v, q'', hv ⟩ := ih ( show ReachesIn n ⟨ Sum.inl q', w', α' ⟩ ⟨ s, [], [] ⟩ from by simpa [ hc₃.1 ] using hc₂ );
      have h_lift : M.Reaches ⟨q, w ++ v, α⟩ ⟨q', w' ++ v, α'⟩ := by
        have h_lift : ∀ {r₁ r₂ : M.conf}, M.Reaches₁ r₁ r₂ → ∀ v : List T, M.Reaches₁ (r₁.appendInput v) (r₂.appendInput v) := by
          grind +suggestions;
        exact Relation.ReflTransGen.single ( h_lift hc₃.2 v );
      exact ⟨ v, q'', h_lift.trans hv ⟩;
    · have hw : w = [] := by
        have hw : ∀ {n : ℕ} {q : Q} {w : List T} {γ : List S} {c : (prefixPDA M).conf}, (prefixPDA M).ReachesIn n ⟨Sum.inr q, w, γ⟩ c → c.input = w := by
          exact?
        generalize_proofs at *; (
        specialize @hw n q w α ⟨ s, [], [] ⟩ ; aesop;)
      have hs : ∃ p : Q, s = Sum.inr p := by
        have hs : ∃ p : Q, s = Sum.inr p := by
          have := inr_stays_inr (by
          aesop : (prefixPDA M).ReachesIn n ⟨Sum.inr q, w, α⟩ ⟨s, [], []⟩)
          exact this.imp fun p hp => by simpa using hp;
        generalize_proofs at *;
        exact hs
      obtain ⟨p, rfl⟩ := hs
      have hv : ∃ v : List T, M.Reaches ⟨q, v, α⟩ ⟨p, [], []⟩ := by
        have := M_reaches_of_verify_reachesIn (by
        grind : (prefixPDA M).ReachesIn n ⟨Sum.inr q, [], α⟩ ⟨Sum.inr p, [], []⟩);
        aesop;
      obtain ⟨v, hv⟩ := hv
      use v, p
      aesop

/-
PROBLEM
**Backward direction**: every word accepted by the prefix PDA is a prefix
of some word in `M.acceptsByEmptyStack`.

PROVIDED SOLUTION
Intro w and hw. Unfold acceptsByEmptyStack: obtain ⟨s, hs⟩ from hw where (prefixPDA M).Reaches ⟨Sum.inl M.initial_state, w, [M.start_symbol]⟩ ⟨s, [], []⟩. Convert to ReachesIn: obtain ⟨n, hn⟩. Apply inl_computation_to_M to get ∃ v q', M.Reaches ⟨M.initial_state, w ++ v, [M.start_symbol]⟩ ⟨q', [], []⟩. This gives w ++ v ∈ M.acceptsByEmptyStack (using ⟨q', hv⟩), so w ∈ prefixLang (by ⟨v, ...⟩).
-/
theorem prefixPDA_subset (M : PDA Q T S) :
    (prefixPDA M).acceptsByEmptyStack ≤ Language.prefixLang M.acceptsByEmptyStack := by
  intro w hw
  obtain ⟨s, hs⟩ := hw
  obtain ⟨n, hn⟩ : ∃ n, (prefixPDA M).ReachesIn n ⟨Sum.inl M.initial_state, w, [M.start_symbol]⟩ ⟨s, [], []⟩ := by
    exact?
  obtain ⟨v, q', hv⟩ := inl_computation_to_M hn;
  exact ⟨ v, by tauto ⟩

end Backward

end PrefixClosure

-- ══════════════════════════════════════════════════════════════════
-- § 5  Main theorems
-- ══════════════════════════════════════════════════════════════════

/-- PDA-recognisable languages are closed under prefix. -/
theorem is_PDA_prefixLang {L : Language T} (h : is_PDA L) :
    is_PDA (Language.prefixLang L) := by
  obtain ⟨Q, S, _, _, M, rfl⟩ := h
  exact ⟨Q ⊕ Q, S, inferInstance, inferInstance, PrefixClosure.prefixPDA M,
    le_antisymm (PrefixClosure.prefixPDA_subset M) (PrefixClosure.prefixPDA_supset M)⟩

/-- Context-free languages are closed under the prefix operation
(proved via the PDA equivalence with the "all states accept" construction). -/
theorem Language.IsContextFree.prefixLang {L : Language T}
    (h : L.IsContextFree) :
    (Language.prefixLang L).IsContextFree := by
  rw [← is_PDA_iff_isContextFree] at h ⊢
  exact is_PDA_prefixLang h

/-- Context-free languages are closed under the prefix operation
(project-level `is_CF` formulation). -/
theorem is_CF_prefixLang {L : Language T} (h : is_CF L) :
    is_CF (Language.prefixLang L) := by
  rw [is_CF_iff_isContextFree] at h ⊢
  exact h.prefixLang