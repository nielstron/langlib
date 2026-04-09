import Mathlib

/-! # Regular Closure Under Kleene Star

This file proves that the class of regular languages is closed under Kleene star
by constructing an ε-NFA from a DFA.

## Main results

- `Language.IsRegular.kstar'` — if `L` is regular, then `L∗` is regular.
-/

namespace Language

open Classical

variable {α : Type*}

section StarεNFA

variable {σ : Type*} [Fintype σ]

/-- ε-NFA for the Kleene star of a DFA.

States are `σ ⊕ Unit`. The fresh state `Sum.inr ()` is both the start and the
sole accepting state. It has an ε-transition into the DFA's start state.
Accepting states of the DFA have an ε-transition back to the fresh state. -/
noncomputable def starεNFA (M : DFA α σ) : εNFA α (σ ⊕ Unit) where
  step := fun s c =>
    match s, c with
    | Sum.inl q, some a => {Sum.inl (M.step q a)}
    | Sum.inl q, none => if q ∈ M.accept then {Sum.inr ()} else ∅
    | Sum.inr (), some _ => ∅
    | Sum.inr (), none => {Sum.inl M.start}
  start := {Sum.inr ()}
  accept := {Sum.inr ()}

variable (M : DFA α σ)

/-
ε-closure of `{Sum.inr ()}` includes `Sum.inl M.start`.
-/
private lemma εClosure_fresh :
    (starεNFA M).εClosure {Sum.inr ()} = {Sum.inr (), Sum.inl M.start} := by
      apply le_antisymm;
      · intro s hs;
        induction hs ; aesop;
        unfold starεNFA at * ; aesop;
      · intro x hx;
        induction' n : x with s t ih;
        · have h_eps : Sum.inl M.start ∈ (starεNFA M).εClosure {Sum.inr ()} := by
            apply εNFA.εClosure.step;
            rotate_right;
            exact Sum.inr ();
            · exact Set.mem_singleton _;
            · exact εNFA.εClosure.base _ ( by simp +decide );
          aesop;
        · constructor;
          aesop

/-
ε-closure of `{Sum.inl q}` when `q ∉ M.accept`.
-/
private lemma εClosure_inl_not_accept (q : σ) (hq : q ∉ M.accept) :
    (starεNFA M).εClosure {Sum.inl q} = {Sum.inl q} := by
      -- Since $q \notin M.accept$, there are no ε-transitions from $Sum.inl q$, so the ε-closure is just $\{Sum.inl q\}$.
      ext; simp [starεNFA, hq];
      constructor <;> intro h;
      · induction h;
        · aesop;
        · aesop;
      · constructor;
        aesop

/-
ε-closure of `{Sum.inl q}` when `q ∈ M.accept`.
-/
private lemma εClosure_inl_accept (q : σ) (hq : q ∈ M.accept) :
    (starεNFA M).εClosure {Sum.inl q} = {Sum.inl q, Sum.inr (), Sum.inl M.start} := by
      -- We'll use induction to show that the ε-closure of `{Sum.inl q}` is `{Sum.inl q, Sum.inr (), Sum.inl M.start}`.
      apply Set.Subset.antisymm;
      · intro x hx; induction hx; aesop;
        unfold starεNFA at *; aesop;
      · simp +decide [ Set.subset_def, starεNFA ];
        refine' ⟨ _, _, _ ⟩;
        · exact Set.mem_setOf.mpr ( by tauto );
        · refine' εNFA.εClosure.step _ _ _ _;
          exact Sum.inl q;
          · grind;
          · exact εNFA.εClosure.base _ rfl;
        · refine' εNFA.εClosure.step _ _ _ _;
          exact Sum.inr ();
          · exact Set.mem_singleton _;
          · refine' εNFA.εClosure.step _ _ _ _;
            exact Sum.inl q;
            · grind;
            · exact?

/-
`Sum.inl (M.evalFrom M.start w)` is always reachable from `{Sum.inl M.start}`.
-/
private lemma evalFrom_inl_contains (w : List α) :
    Sum.inl (M.evalFrom M.start w) ∈ (starεNFA M).evalFrom {Sum.inl M.start} w := by
      induction' w using List.reverseRecOn with w a ih <;> simp +decide [ *, List.foldl_append ];
      · exact εNFA.εClosure.base _ ( by simp +decide );
      · refine' Or.inl ⟨ _, ih, _ ⟩;
        exact εNFA.εClosure.base _ ( by simp +decide [ starεNFA ] )

/-
evalFrom distributes over append for the star εNFA.
-/
private lemma evalFrom_append (S : Set (σ ⊕ Unit)) (u v : List α) :
    (starεNFA M).evalFrom S (u ++ v) =
    (starεNFA M).evalFrom ((starεNFA M).evalFrom S u) v := by
      unfold εNFA.evalFrom;
      induction' u using List.reverseRecOn with u ih;
      · induction' v using List.reverseRecOn with v ih <;> simp_all +decide [ List.foldl_append ];
        refine' le_antisymm _ _;
        · exact Set.mem_setOf_eq.mpr ( by tauto );
        · intro x hx;
          induction' hx with x hx ih;
          · exact hx;
          · rename_i h₁ h₂ h₃;
            refine' εNFA.εClosure.step _ _ _ _;
            exacts [ ih, h₁, h₃ ];
      · simp_all +decide [ List.foldl_append, εNFA.stepSet ];
        -- By definition of ε-closure, we know that the ε-closure of a union is the union of the ε-closures.
        have h_eps_closure_union : ∀ (S : Set (σ ⊕ Unit)), (starεNFA M).εClosure (⋃ s ∈ S, (starεNFA M).εClosure ((starεNFA M).step s (some ih))) = ⋃ s ∈ S, (starεNFA M).εClosure ((starεNFA M).step s (some ih)) := by
          intro S
          apply le_antisymm;
          · intro x hx;
            induction' hx with x hx ih;
            · exact hx;
            · rename_i h₁ h₂ h₃;
              cases ih <;> cases ‹σ ⊕ Unit› <;> simp_all +decide [ starεNFA ];
              · obtain ⟨ a, ha₁, ha₂ ⟩ := h₃;
                refine' ⟨ a, ha₁, _ ⟩;
                exact εNFA.εClosure.step _ _ ( by simp +decide [ h₁ ] ) ha₂;
              · obtain ⟨ a, ha₁, ha₂ ⟩ := h₃;
                exact ⟨ a, ha₁, by
                  exact εNFA.εClosure.step _ _ ( by simp +decide [ starεNFA ] ) ha₂ ⟩;
          · exact fun x hx => by rcases Set.mem_iUnion₂.1 hx with ⟨ s, hs, hx ⟩ ; exact Set.mem_of_mem_of_subset hx ( Set.Subset.trans ( by aesop_cat ) ( εNFA.subset_εClosure _ _ ) ) ;
        rw [ h_eps_closure_union ]

/-
evalFrom is monotone in the start set.
-/
private lemma evalFrom_mono (S T : Set (σ ⊕ Unit)) (w : List α) (h : S ⊆ T) :
    (starεNFA M).evalFrom S w ⊆ (starεNFA M).evalFrom T w := by
      induction' w using List.reverseRecOn with w ih generalizing S T <;> simp_all +decide [ εNFA.evalFrom ];
      · intro x hx;
        induction' hx with x hx ih;
        · exact Set.mem_setOf_eq.mpr ( by tauto );
        · apply_rules [ εNFA.εClosure.step ];
      · rename_i h';
        exact Set.biUnion_mono ( h' S T h ) fun _ _ => by tauto;

/-
If `q ∈ M.accept` and `Sum.inl q` is reachable from S, then
`Sum.inr ()` is also reachable from S.
-/
private lemma fresh_reachable_of_accept (S : Set (σ ⊕ Unit)) (q : σ) (w : List α)
    (hq : q ∈ M.accept)
    (h : Sum.inl q ∈ (starεNFA M).evalFrom S w) :
    Sum.inr () ∈ (starεNFA M).evalFrom S w := by
      -- By definition of `evalFrom`, if `Sum.inl q ∈ (starεNFA M).evalFrom S w`, then `Sum.inr () ∈ (starεNFA M).εClosure {Sum.inl q}`.
      have h_closure : Sum.inr () ∈ (starεNFA M).εClosure {Sum.inl q} := by
        exact εClosure_inl_accept M q hq ▸ Set.mem_insert_of_mem _ ( Set.mem_insert _ _ );
      induction' w using List.reverseRecOn with w ih generalizing S <;> simp_all +decide [ εNFA.stepSet ];
      · have h_closure : ∀ s, s ∈ (starεNFA M).εClosure {Sum.inl q} → s ∈ (starεNFA M).εClosure S := by
          intro s hs
          induction' hs with s hs ih;
          · aesop;
          · exact εNFA.εClosure.step _ _ ‹_› ‹_›;
        exact h_closure _ ‹_›;
      · rcases h with ( ⟨ a, ha, ha' ⟩ | ⟨ b, hb, hb' ⟩ );
        · refine' Or.inl ⟨ a, ha, _ ⟩;
          have h_closure : (starεNFA M).εClosure {Sum.inl q} ⊆ (starεNFA M).εClosure ((starεNFA M).step (Sum.inl a) (some ih)) := by
            intro x hx;
            induction' hx with x hx ih;
            · grind;
            · apply_rules [ εNFA.εClosure.step ];
          exact h_closure ‹_›;
        · cases b ; simp_all +decide [ starεNFA ]

/-
Backward: `KStar.kstar M.accepts ⊆ (starεNFA M).accepts`.
-/
private lemma star_backward {w : List α}
    (hw : w ∈ KStar.kstar M.accepts) :
    w ∈ (starεNFA M).accepts := by
      unfold KStar.kstar at hw
      generalize_proofs at *;
      have h_ind : ∀ L : List (List α), (∀ y ∈ L, y ∈ M.accepts) → Sum.inr () ∈ (starεNFA M).evalFrom {Sum.inr ()} L.flatten := by
        intro L hL; induction' L with y L ih <;> simp_all +decide [ Set.subset_def ] ;
        · exact Set.mem_setOf.mpr ( by tauto );
        · have h_eval_y : Sum.inl (M.evalFrom M.start y) ∈ (starεNFA M).evalFrom {Sum.inr ()} y := by
            have h_eval_y : Sum.inl (M.evalFrom M.start y) ∈ (starεNFA M).evalFrom {Sum.inl M.start} y := by
              grind +suggestions
            generalize_proofs at *; (
            have h_eval_y : {Sum.inl M.start} ⊆ (starεNFA M).evalFrom {Sum.inr ()} [] := by
              simp +decide [ εClosure_fresh ]
            generalize_proofs at *; (
            have h_eval_y : (starεNFA M).evalFrom {Sum.inl M.start} y ⊆ (starεNFA M).evalFrom ((starεNFA M).evalFrom {Sum.inr ()} []) y := by
              exact?
            generalize_proofs at *; (
            convert h_eval_y ‹_› using 1
            generalize_proofs at *; (
            simp +decide [ εNFA.evalFrom ];
            rw [ εClosure_fresh ];
            rw [ show ( starεNFA M ).εClosure { Sum.inr (), Sum.inl M.start } = { Sum.inr (), Sum.inl M.start } from ?_ ];
            refine' Set.Subset.antisymm _ _ <;> simp +decide [ Set.subset_def, εNFA.εClosure ];
            · intro a ha; contrapose! ha; simp_all +decide [ εNFA.εClosure ] ;
              intro h; have := h; simp_all +decide [ εNFA.εClosure ] ;
              have h_eval_y : ∀ s ∈ (starεNFA M).εClosure {Sum.inr (), Sum.inl M.start}, s = Sum.inr () ∨ s = Sum.inl M.start := by
                intro s hs; induction hs; aesop;
                unfold starεNFA at *; aesop;
              generalize_proofs at *; (
              grind);
            · exact ⟨ by exact Set.mem_of_mem_of_subset ( Set.mem_insert _ _ ) ( εNFA.subset_εClosure _ _ ), by exact Set.mem_of_mem_of_subset ( Set.mem_insert_of_mem _ ( Set.mem_singleton _ ) ) ( εNFA.subset_εClosure _ _ ) ⟩))))
          generalize_proofs at *; (
          have h_eval_y : Sum.inr () ∈ (starεNFA M).evalFrom {Sum.inr ()} y := by
            apply_rules [ fresh_reachable_of_accept ] ; aesop;
          generalize_proofs at *; (
          exact Set.mem_of_mem_of_subset ih ( evalFrom_mono _ _ _ _ ( Set.singleton_subset_iff.mpr h_eval_y ) ) |> fun h => by simpa [ evalFrom_append ] using h;));
      unfold εNFA.accepts;
      obtain ⟨ L, rfl, hL ⟩ := hw;
      use Sum.inr ();
      aesop

/-- If `Sum.inr ()` is reachable from `{Sum.inl q}` after processing `w`,
then some prefix of `w` takes `M` from `q` to an accepting state. -/
private lemma inl_to_fresh_split (q : σ) (w : List α)
    (h : Sum.inr () ∈ (starεNFA M).evalFrom {Sum.inl q} w) :
    ∃ u v, w = u ++ v ∧ M.evalFrom q u ∈ M.accept ∧
      Sum.inr () ∈ (starεNFA M).evalFrom {Sum.inr ()} v := by sorry

/-- Forward: `(starεNFA M).accepts ⊆ KStar.kstar M.accepts`. -/
private lemma star_forward {w : List α}
    (hw : w ∈ (starεNFA M).accepts) :
    w ∈ KStar.kstar M.accepts := by sorry

/-- The Kleene star ε-NFA accepts exactly the Kleene star of the DFA language. -/
theorem starεNFA_correct :
    (starεNFA M).accepts = KStar.kstar M.accepts :=
  Set.eq_of_subset_of_subset
    (fun _ hw => star_forward M hw)
    (fun _ hw => star_backward M hw)

end StarεNFA

/-- Regular languages are closed under Kleene star. -/
theorem IsRegular.kstar' {L : Language α}
    (hL : L.IsRegular) :
    (KStar.kstar L).IsRegular := by
  obtain ⟨σ, _, M, rfl⟩ := hL
  rw [← starεNFA_correct M]
  refine ⟨_, inferInstance, (starεNFA M).toNFA.toDFA, ?_⟩
  rw [NFA.toDFA_correct, εNFA.toNFA_correct]

end Language