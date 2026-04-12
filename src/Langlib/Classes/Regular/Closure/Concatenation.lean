import Mathlib
import Langlib.Utilities.ClosurePredicates

/-! # Regular Closure Under Concatenation

This file proves that the class of regular languages is closed under concatenation
by constructing an ε-NFA from two DFAs.

## Main results

- `Language.IsRegular.mul'` — if `L₁` and `L₂` are regular, then `L₁ * L₂` is regular.
-/

namespace Language

open Classical

variable {α : Type*}

section ConcatεNFA

variable {σ₁ σ₂ : Type*} [Fintype σ₁] [Fintype σ₂]

/-- ε-NFA for the concatenation of two DFAs.

States are `σ₁ ⊕ σ₂`. On the left side we simulate `M₁`; on the right, `M₂`.
Accepting states of `M₁` get an ε-transition to `M₂`'s start state. -/
noncomputable def concatεNFA (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) : εNFA α (σ₁ ⊕ σ₂) where
  step := fun s c =>
    match s, c with
    | Sum.inl q, some a => {Sum.inl (M₁.step q a)}
    | Sum.inl q, none => if q ∈ M₁.accept then {Sum.inr M₂.start} else ∅
    | Sum.inr q, some a => {Sum.inr (M₂.step q a)}
    | Sum.inr _, none => ∅
  start := {Sum.inl M₁.start}
  accept := Sum.inr '' M₂.accept

variable (M₁ : DFA α σ₁) (M₂ : DFA α σ₂)

/-
ε-closure of a right-side singleton: no ε-transitions from `Sum.inr`.
-/
private lemma εClosure_inr (q : σ₂) :
    (concatεNFA M₁ M₂).εClosure {Sum.inr q} = {Sum.inr q} := by
      refine' Set.Subset.antisymm _ _;
      · intro s hs; induction hs; aesop;
        unfold concatεNFA at * ; aesop;
      · exact Set.singleton_subset_iff.mpr ( εNFA.εClosure.base _ ( by simp +decide ) )

/-
Processing a word from a single `Sum.inr` state follows `M₂` exactly.
-/
private lemma evalFrom_inr (q : σ₂) (w : List α) :
    (concatεNFA M₁ M₂).evalFrom {Sum.inr q} w = {Sum.inr (M₂.evalFrom q w)} := by
      induction' w using List.reverseRecOn with w a ih;
      · convert εClosure_inr M₁ M₂ q;
      · simp_all +decide [ List.foldl_append, εNFA.stepSet ];
        convert εClosure_inr M₁ M₂ ( M₂.step ( M₂.evalFrom q w ) a ) using 1

/-
ε-closure of a left-side singleton when the state is NOT accepting in `M₁`.
-/
private lemma εClosure_inl_not_accept (q : σ₁) (hq : q ∉ M₁.accept) :
    (concatεNFA M₁ M₂).εClosure {Sum.inl q} = {Sum.inl q} := by
      -- Since $q \notin M₁.accept$, there are no ε-transitions from $Sum.inl q$ to $Sum.inr M₂.start$.
      have h_no_ε_transitions : ∀ s, s ∈ (concatεNFA M₁ M₂).εClosure {Sum.inl q} → s = Sum.inl q := by
        intro s hs;
        induction hs;
        · aesop;
        · unfold concatεNFA at *; aesop;
      exact Set.eq_singleton_iff_unique_mem.mpr ⟨ by tauto, h_no_ε_transitions ⟩

/-
ε-closure of a left-side singleton when the state IS accepting in `M₁`.
-/
private lemma εClosure_inl_accept (q : σ₁) (hq : q ∈ M₁.accept) :
    (concatεNFA M₁ M₂).εClosure {Sum.inl q} = {Sum.inl q, Sum.inr M₂.start} := by
      refine' le_antisymm _ _;
      · intro x hx;
        induction' hx with x y hxy ih;
        · grind;
        · cases hxy <;> simp_all +decide [ concatεNFA ];
      · intro x hx;
        induction x <;> simp_all +decide [ εNFA.εClosure ];
        · -- Since the ε-closure of a singleton set is the set itself, we have:
          apply εNFA.εClosure.base; simp [hx];
        · apply εNFA.εClosure.step;
          any_goals exact Sum.inl q;
          · unfold concatεNFA; aesop;
          · apply εNFA.εClosure.base;
            simp +decide

/-
The set of states reachable after processing `w` from `Sum.inl q` always
includes `Sum.inl (M₁.evalFrom q w)`. It may also include `Sum.inr` states
from ε-transitions at intermediate accepting states of `M₁`.
-/
private lemma evalFrom_inl_contains (q : σ₁) (w : List α) :
    Sum.inl (M₁.evalFrom q w) ∈ (concatεNFA M₁ M₂).evalFrom {Sum.inl q} w := by
      induction' w using List.reverseRecOn with w ih generalizing q;
      · exact εNFA.εClosure.base _ ( by simp +decide );
      · simp_all +decide [ εNFA.evalFrom ];
        refine' Or.inl ⟨ _, ‹∀ q : σ₁, Sum.inl ( M₁.evalFrom q w ) ∈ List.foldl ( concatεNFA M₁ M₂ ).stepSet ( ( concatεNFA M₁ M₂ ).εClosure { Sum.inl q } ) w› q, _ ⟩;
        exact εNFA.εClosure.base _ ( by simp +decide [ concatεNFA ] )

/-
evalFrom is monotone in the starting set.
-/
private lemma evalFrom_mono (S T : Set (σ₁ ⊕ σ₂)) (w : List α) (h : S ⊆ T) :
    (concatεNFA M₁ M₂).evalFrom S w ⊆ (concatεNFA M₁ M₂).evalFrom T w := by
      grind +suggestions

/-
If `Sum.inl q` is reachable, then `Sum.inr M₂.start` is reachable when `q ∈ M₁.accept`.
-/
private lemma inr_start_reachable_of_inl_accept (q : σ₁) (w : List α)
    (hq : q ∈ M₁.accept)
    (hreach : Sum.inl q ∈ (concatεNFA M₁ M₂).evalFrom {Sum.inl M₁.start} w) :
    Sum.inr M₂.start ∈ (concatεNFA M₁ M₂).evalFrom {Sum.inl M₁.start} w := by
      contrapose! hreach;
      induction' w using List.reverseRecOn with w IH <;> simp_all +decide [ εNFA.evalFrom ];
      · cases eq_or_ne q M₁.start <;> simp_all +decide [ εNFA.εClosure ];
        · exact False.elim ( hreach ( by rw [ εClosure_inl_accept M₁ M₂ M₁.start hq ] ; simp +decide ) );
        · rintro ⟨ s, hs ⟩;
          · aesop;
          · rename_i s hs₁ hs₂;
            cases s <;> simp_all +decide [ concatεNFA ];
      · constructor <;> intro x hx;
        · intro h;
          have h_eps : (concatεNFA M₁ M₂).step (Sum.inl x) (some IH) = {Sum.inl (M₁.step x IH)} := by
            grind +locals;
          by_cases h : M₁.step x IH ∈ M₁.accept <;> simp_all +decide [ εClosure_inl_accept, εClosure_inl_not_accept ];
          have := hreach.1 x hx; simp_all +decide [ εClosure_inl_accept ] ;
        · intro h;
          convert εClosure_inr M₁ M₂ ( M₂.step x IH ) ▸ h using 1;
          simp +decide [ Set.ext_iff ]

/-
evalFrom distributes: `evalFrom S (u ++ v) = evalFrom (evalFrom S u) v`.
-/
private lemma evalFrom_append (S : Set (σ₁ ⊕ σ₂)) (u v : List α) :
    (concatεNFA M₁ M₂).evalFrom S (u ++ v) =
    (concatεNFA M₁ M₂).evalFrom ((concatεNFA M₁ M₂).evalFrom S u) v := by
      simp +decide [ εNFA.evalFrom ];
      -- By definition of ε-closure, we know that if q is in the ε-closure of S, then q is in the ε-closure of any state reachable from S.
      have h_εClosure : ∀ (S : Set (σ₁ ⊕ σ₂)), (concatεNFA M₁ M₂).εClosure S = S ∪ (if ∃ q ∈ M₁.accept, Sum.inl q ∈ S then {Sum.inr M₂.start} else ∅) := by
        intro S;
        refine' le_antisymm _ _;
        · intro q hq;
          induction' hq with q hq ih;
          · exact Or.inl hq;
          · unfold concatεNFA at * ; aesop;
        · intro q hq;
          split_ifs at hq <;> simp_all +decide [ εNFA.εClosure ];
          · rcases hq with ( rfl | hq );
            · grind +suggestions;
            · exact Set.mem_setOf_eq.mpr ( by tauto );
          · exact Set.mem_setOf_eq.mpr ( by tauto );
      induction v using List.reverseRecOn <;> simp_all +decide [ Set.ext_iff ];
      intro b x hx hx' hb; induction u using List.reverseRecOn <;> simp_all +decide [ εNFA.stepSet ] ;
      · exact Or.inr ⟨ x, hx, hx' ⟩;
      · grind

/-
Backward direction: `M₁.accepts * M₂.accepts ⊆ concatεNFA.accepts`.
-/
private lemma concat_backward {w : List α} (hw : w ∈ M₁.accepts * M₂.accepts) :
    w ∈ (concatεNFA M₁ M₂).accepts := by
      obtain ⟨ u, hu, v, hv, rfl ⟩ := Set.mem_image2.mp hw;
      have h_eval_from : Sum.inr (M₂.evalFrom M₂.start v) ∈ (concatεNFA M₁ M₂).evalFrom {Sum.inl M₁.start} (u ++ v) := by
        rw [ evalFrom_append ];
        have h_eval_from : {Sum.inr M₂.start} ⊆ (concatεNFA M₁ M₂).evalFrom {Sum.inl M₁.start} u := by
          apply Set.singleton_subset_iff.mpr;
          apply inr_start_reachable_of_inl_accept;
          exact hu;
          exact?;
        have h_eval_from : (concatεNFA M₁ M₂).evalFrom {Sum.inr M₂.start} v ⊆ (concatεNFA M₁ M₂).evalFrom ((concatεNFA M₁ M₂).evalFrom {Sum.inl M₁.start} u) v := by
          exact?;
        exact h_eval_from ( by rw [ evalFrom_inr ] ; simp +decide );
      exact ⟨ _, Set.mem_image_of_mem _ hv, h_eval_from ⟩

/-
Any `Sum.inr` state reachable from `{Sum.inl q}` comes from a split of the input
where the prefix takes `M₁` to an accepting state.
-/
private lemma inr_reachable_split (q : σ₁) (w : List α) (q₂ : σ₂)
    (h : Sum.inr q₂ ∈ (concatεNFA M₁ M₂).evalFrom {Sum.inl q} w) :
    ∃ u v, w = u ++ v ∧ M₁.evalFrom q u ∈ M₁.accept ∧
      q₂ = M₂.evalFrom M₂.start v := by
        contrapose! h;
        -- By definition of `evalFrom`, we know that `Sum.inr q₂` is reachable from `{Sum.inl q}` if and only if there exists a path from `{Sum.inl q}` to `Sum.inr q₂` in the ε-NFA.
        have h_path : ∀ w, ∀ q₁, Sum.inl q₁ ∈ (concatεNFA M₁ M₂).evalFrom {Sum.inl q} w → q₁ = M₁.evalFrom q w := by
          intro w q₁ hw;
          induction' w using List.reverseRecOn with w a ih generalizing q₁;
          · by_cases hq : q ∈ M₁.accept <;> simp_all +decide [ εClosure_inl_not_accept, εClosure_inl_accept ];
          · simp_all +decide [ εNFA.evalFrom_append_singleton ];
            rcases hw with ( ⟨ q₁, hq₁, hq₂ ⟩ | ⟨ q₂, hq₁, hq₂ ⟩ );
            · have h_step : (concatεNFA M₁ M₂).step (Sum.inl q₁) (some a) = {Sum.inl (M₁.step q₁ a)} := by
                exact?;
              have h_eps_closure : ∀ s : σ₁ ⊕ σ₂, (concatεNFA M₁ M₂).εClosure {s} = if s ∈ Set.range Sum.inl then if s ∈ Set.image Sum.inl M₁.accept then {s, Sum.inr M₂.start} else {s} else if s ∈ Set.range Sum.inr then {s} else ∅ := by
                intro s; rcases s with ( s | s ) <;> simp +decide [ εClosure_inl_not_accept, εClosure_inl_accept, εClosure_inr ] ;
                split_ifs with hs <;> simp +decide [ hs, εClosure_inl_not_accept, εClosure_inl_accept ];
              grind;
            · -- Since the ε-closure of {Sum.inr (M₂.step q₂ a)} is just {Sum.inr (M₂.step q₂ a)}, we have Sum.inl q₁ = Sum.inr (M₂.step q₂ a), which is a contradiction.
              have h_contra : Sum.inl q₁ = Sum.inr (M₂.step q₂ a) := by
                have h_contra : (concatεNFA M₁ M₂).εClosure {Sum.inr (M₂.step q₂ a)} = {Sum.inr (M₂.step q₂ a)} := by
                  exact?;
                exact h_contra.subset hq₂;
              cases h_contra;
        induction' w using List.reverseRecOn with w a ih generalizing q q₂;
        · by_cases hq : q ∈ M₁.accept <;> simp +decide [ hq, εClosure_inl_accept, εClosure_inl_not_accept ] at h ⊢;
          exact h;
        · simp +decide [ εNFA.stepSet ];
          constructor;
          · intro x hx;
            rw [ show ( concatεNFA M₁ M₂ ).step ( Sum.inl x ) ( some a ) = { Sum.inl ( M₁.step x a ) } from ?_ ];
            · rw [ show ( concatεNFA M₁ M₂ ).εClosure { Sum.inl ( M₁.step x a ) } = if M₁.step x a ∈ M₁.accept then { Sum.inl ( M₁.step x a ), Sum.inr M₂.start } else { Sum.inl ( M₁.step x a ) } from ?_ ];
              · split_ifs <;> simp +decide [ h ];
                specialize h ( w ++ [ a ] ) [ ] ; simp_all +decide;
                exact h ( by rw [ ← h_path _ _ hx ] ; assumption );
              · split_ifs with h;
                · exact?;
                · exact εClosure_inl_not_accept M₁ M₂ _ h;
            · grind;
          · intro x hx;
            rw [ show ( concatεNFA M₁ M₂ ).step ( Sum.inr x ) ( some a ) = { Sum.inr ( M₂.step x a ) } by rfl ];
            grind +suggestions

/-
Forward direction: `concatεNFA.accepts ⊆ M₁.accepts * M₂.accepts`.
-/
private lemma concat_forward {w : List α} (hw : w ∈ (concatεNFA M₁ M₂).accepts) :
    w ∈ M₁.accepts * M₂.accepts := by
      obtain ⟨s, hs⟩ := hw;
      obtain ⟨q₂, hq₂⟩ : ∃ q₂, s = Sum.inr q₂ ∧ q₂ ∈ M₂.accept := by
        unfold concatεNFA at hs; aesop;
      have := inr_reachable_split M₁ M₂ M₁.start w q₂ ?_;
      · rcases this with ⟨ u, v, rfl, hu, hv ⟩ ; exact ⟨ u, hu, v, by aesop ⟩ ;
      · aesop

/-- The concatenation ε-NFA accepts exactly the concatenation of the two DFA languages. -/
theorem concatεNFA_correct :
    (concatεNFA M₁ M₂).accepts = M₁.accepts * M₂.accepts :=
  Set.eq_of_subset_of_subset
    (fun _ hw => concat_forward M₁ M₂ hw)
    (fun _ hw => concat_backward M₁ M₂ hw)

end ConcatεNFA

/-- Regular languages are closed under concatenation. -/
theorem IsRegular.mul' {L₁ L₂ : Language α}
    (h₁ : L₁.IsRegular) (h₂ : L₂.IsRegular) :
    (L₁ * L₂).IsRegular := by
  obtain ⟨σ₁, _, M₁, rfl⟩ := h₁
  obtain ⟨σ₂, _, M₂, rfl⟩ := h₂
  rw [← concatεNFA_correct M₁ M₂]
  refine ⟨_, inferInstance, (concatεNFA M₁ M₂).toNFA.toDFA, ?_⟩
  rw [NFA.toDFA_correct, εNFA.toNFA_correct]

end Language

/-- The class of regular languages is closed under concatenation. -/
theorem Regular_closedUnderConcatenation : ClosedUnderConcatenation {L : Language α | L.IsRegular} :=
  fun L₁ L₂ h₁ h₂ => h₁.mul' h₂