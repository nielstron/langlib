import Mathlib
import Langlib.Utilities.LanguageOperations

/-! # Regular Closure Under Substitution

This file proves that the class of regular languages is closed under substitution
by constructing an ε-NFA from a DFA and a family of DFAs.

## Main results

- `Language.IsRegular.subst'` — if `L` is regular over a finite alphabet and each `f a` is
  regular, then `L.subst f` is regular.
-/

namespace Language

open Classical

variable {α β : Type} [Fintype α]

section SubstεNFA

variable {σ : Type} [Fintype σ]
variable (M : DFA α σ) (τ : α → Type) [inst_fin : ∀ a, Fintype (τ a)]
  (N : (a : α) → DFA β (τ a))

/-- ε-NFA for the substitution of a DFA language by a family of DFA languages. -/
noncomputable def substεNFA : εNFA β (σ ⊕ (σ × (Σ a : α, τ a))) where
  step := fun state c =>
    match state, c with
    | Sum.inl q, none => Set.range fun a => Sum.inr (q, ⟨a, (N a).start⟩)
    | Sum.inl _, some _ => ∅
    | Sum.inr (q, ⟨a, s⟩), some b => {Sum.inr (q, ⟨a, (N a).step s b⟩)}
    | Sum.inr (q, ⟨a, s⟩), none =>
        if s ∈ (N a).accept then {Sum.inl (M.step q a)} else ∅
  start := {Sum.inl M.start}
  accept := Sum.inl '' M.accept

variable {M τ N}

/-! ### General εClosure / evalFrom helpers -/

private lemma εClosure_mono {S T : Set (σ ⊕ (σ × (Σ a : α, τ a)))} (h : S ⊆ T) :
    (substεNFA M τ N).εClosure S ⊆ (substεNFA M τ N).εClosure T := by
  intro x hx; induction hx with
  | base s hs => exact εNFA.εClosure.base _ (h hs)
  | step s t ht _ ih => exact εNFA.εClosure.step _ _ ht ih

private lemma εClosure_idempotent (S : Set (σ ⊕ (σ × (Σ a : α, τ a)))) :
    (substεNFA M τ N).εClosure ((substεNFA M τ N).εClosure S) =
    (substεNFA M τ N).εClosure S := by
  ext x; constructor
  · intro hx; induction hx with
    | base s hs => exact hs
    | step s t ht _ ih => exact εNFA.εClosure.step _ _ ht ih
  · exact fun hx => εNFA.εClosure.base _ hx

private lemma evalFrom_mono {S T : Set (σ ⊕ (σ × (Σ a : α, τ a)))} (w : List β)
    (h : S ⊆ T) :
    (substεNFA M τ N).evalFrom S w ⊆ (substεNFA M τ N).evalFrom T w := by
  induction' w using List.reverseRecOn with w ih generalizing S T <;> simp_all +decide [ εNFA.evalFrom ];
  · exact?;
  · apply_rules [ Set.iUnion₂_subset ];
    grind +suggestions

private lemma evalFrom_εClosure (S : Set (σ ⊕ (σ × (Σ a : α, τ a)))) (w : List β) :
    (substεNFA M τ N).evalFrom ((substεNFA M τ N).εClosure S) w =
    (substεNFA M τ N).evalFrom S w := by
  unfold εNFA.evalFrom; rw [εClosure_idempotent]

private lemma stepSet_εClosed (T : Set (σ ⊕ (σ × (Σ a : α, τ a)))) (a : β) :
    (substεNFA M τ N).εClosure ((substεNFA M τ N).stepSet T a) =
    (substεNFA M τ N).stepSet T a := by
  refine' le_antisymm _ _;
  · intro x hx; induction hx; aesop;
    rename_i s t hs ht ih;
    obtain ⟨ u, hu, hu' ⟩ := Set.mem_iUnion₂.mp ih;
    refine' Set.mem_iUnion₂.mpr ⟨ u, hu, _ ⟩;
    apply_rules [ εNFA.εClosure.step ];
  · exact εNFA.subset_εClosure _ _

private lemma evalFrom_εClosed_set (S : Set (σ ⊕ (σ × (Σ a : α, τ a)))) (w : List β) :
    (substεNFA M τ N).εClosure ((substεNFA M τ N).evalFrom S w) =
    (substεNFA M τ N).evalFrom S w := by
  induction' w using List.reverseRecOn with w' a ih generalizing S;
  · rw [ εNFA.evalFrom_nil, εClosure_idempotent ];
  · rw [ εNFA.evalFrom_append_singleton ];
    exact?

private lemma evalFrom_append (S : Set (σ ⊕ (σ × (Σ a : α, τ a)))) (u v : List β) :
    (substεNFA M τ N).evalFrom S (u ++ v) =
    (substεNFA M τ N).evalFrom ((substεNFA M τ N).evalFrom S u) v := by
  -- By definition of `evalFrom`, we can rewrite the goal using the fold operation and the properties of `εClosure`.
  have h_evalFrom_fold : ∀ (S : Set (σ ⊕ (σ × (Σ a : α, τ a)))) (w : List β), (substεNFA M τ N).evalFrom S w = (w.foldl (fun T c => (substεNFA M τ N).stepSet T c) ((substεNFA M τ N).εClosure S)) := by
    grind;
  rw [ h_evalFrom_fold, h_evalFrom_fold, h_evalFrom_fold, List.foldl_append ];
  convert rfl using 2;
  -- Apply the εClosure_idempotent lemma to conclude the proof.
  apply evalFrom_εClosed_set

private lemma evalFrom_εClosed (S : Set (σ ⊕ (σ × (Σ a : α, τ a)))) (w : List β)
    (x y : σ ⊕ (σ × (Σ a : α, τ a)))
    (hx : x ∈ (substεNFA M τ N).evalFrom S w)
    (hy : y ∈ (substεNFA M τ N).step x none) :
    y ∈ (substεNFA M τ N).evalFrom S w := by
  induction' w using List.reverseRecOn with w ih generalizing x y S;
  · apply_rules [ εNFA.εClosure.step ];
  · simp +zetaDelta at *;
    rcases hx with ( ⟨ a, ha, hx ⟩ | ⟨ a, b, c, ha, hx ⟩ );
    · cases y <;> simp_all +decide [ substεNFA ];
    · refine' Or.inr ⟨ a, b, c, ha, _ ⟩;
      apply_rules [ εNFA.εClosure.step, εNFA.εClosure.base ]

/-! ### evalFrom for Sum.inr states -/

private lemma evalFrom_inr_contains (q : σ) (a : α) (s : τ a) (v : List β) :
    Sum.inr (q, ⟨a, (N a).evalFrom s v⟩) ∈
      (substεNFA M τ N).evalFrom {Sum.inr (q, (⟨a, s⟩ : Σ a, τ a))} v := by
  induction v using List.reverseRecOn generalizing q s <;> simp_all +decide [ DFA.evalFrom ];
  · exact εNFA.εClosure.base _ ( by simp +decide );
  · refine Or.inr ⟨ q, a, List.foldl ( N a ).step s ‹_›, by solve_by_elim, ?_ ⟩;
    apply_rules [ εNFA.εClosure.base ]

/-! ### Backward direction -/

private lemma backward_one_step (q : σ) (a : α) (u : List β)
    (hu : u ∈ (N a).accepts) :
    Sum.inl (M.step q a) ∈ (substεNFA M τ N).evalFrom {Sum.inl q} u := by
  have h_step_inl : Sum.inr (q, ⟨a, (N a).evalFrom (N a).start u⟩) ∈ (substεNFA M τ N).evalFrom {Sum.inl q} u := by
    have h_step : Sum.inr (q, ⟨a, (N a).start⟩) ∈ (substεNFA M τ N).εClosure {Sum.inl q} := by
      apply εNFA.εClosure.step;
      rotate_right;
      exact Sum.inl q;
      · exact Set.mem_range_self a;
      · apply εNFA.εClosure.base; simp +decide [ substεNFA ];
    have h_step : Sum.inr (q, ⟨a, (N a).evalFrom (N a).start u⟩) ∈ (substεNFA M τ N).evalFrom {Sum.inr (q, ⟨a, (N a).start⟩)} u := by
      exact?;
    have h_step : (substεNFA M τ N).evalFrom {Sum.inr (q, ⟨a, (N a).start⟩)} u ⊆ (substεNFA M τ N).evalFrom ((substεNFA M τ N).εClosure {Sum.inl q}) u := by
      apply evalFrom_mono;
      grind;
    convert h_step ‹_› using 1;
    exact?;
  apply_rules [ evalFrom_εClosed ];
  unfold substεNFA; aesop;

private lemma backward_eval (q : σ) (w : List α) (u : List β)
    (hu : u ∈ (w.map (fun a => (N a).accepts)).prod) :
    Sum.inl (M.evalFrom q w) ∈ (substεNFA M τ N).evalFrom {Sum.inl q} u := by
  induction' w with a w ih generalizing q u;
  · cases hu;
    exact Set.mem_setOf.mpr ( by tauto );
  · obtain ⟨ u₁, u₂, rfl, hu₁, hu₂ ⟩ : ∃ u₁ u₂, u = u₁ ++ u₂ ∧ u₁ ∈ (N a).accepts ∧ u₂ ∈ (List.map (fun a => (N a).accepts) w).prod := by
      rw [ mem_list_prod_iff_forall2 ] at hu;
      rcases hu with ⟨ W, rfl, hW ⟩ ; rcases W with ( _ | ⟨ u₁, W ⟩ ) <;> simp_all +decide [ List.forall₂_cons ] ;
      refine' ⟨ u₁, W.flatten, rfl, hW.1, _ ⟩;
      convert mem_list_prod_iff_forall2 _ _ |>.2 ⟨ W, rfl, _ ⟩;
      rw [ List.forall₂_map_right_iff ] ; aesop;
    have h_step : Sum.inl (M.step q a) ∈ (substεNFA M τ N).evalFrom {Sum.inl q} u₁ := by
      exact?;
    grind +suggestions

private lemma subst_backward {u : List β}
    (hu : u ∈ M.accepts.subst (fun a => (N a).accepts)) :
    u ∈ (substεNFA M τ N).accepts := by
  obtain ⟨ w, hw, hw' ⟩ := hu;
  have h_backward : Sum.inl (M.evalFrom M.start w) ∈ (substεNFA M τ N).evalFrom {Sum.inl M.start} u := by
    apply backward_eval; assumption;
  exact ⟨ _, Set.mem_image_of_mem _ hw, h_backward ⟩

/-! ### Forward direction -/

private lemma εClosure_inl_inv (q : σ) (x : σ ⊕ (σ × (Σ a : α, τ a)))
    (hx : x ∈ (substεNFA M τ N).εClosure {Sum.inl q}) :
    (∀ q' : σ, x = Sum.inl q' →
      ∃ w : List α, M.evalFrom q w = q' ∧
        ([] : List β) ∈ (w.map (fun a => (N a).accepts)).prod) ∧
    (∀ (q' : σ) (a : α) (s : τ a), x = Sum.inr (q', (⟨a, s⟩ : Σ a, τ a)) →
      ∃ w : List α, M.evalFrom q w = q' ∧
        ([] : List β) ∈ (w.map (fun a => (N a).accepts)).prod ∧
        s = (N a).start) := by
  induction' hx with x hx ih;
  · simp +zetaDelta at *;
    constructor <;> intros <;> subst_vars <;> simp_all +decide [ DFA.evalFrom ];
    use []
    simp;
  · rename_i h₁ h₂ h₃;
    unfold substεNFA at h₁; simp_all +decide [ Set.mem_range ] ;
    cases ih <;> simp_all +decide [ Set.mem_range ];
    · grind;
    · rcases h₃ _ _ _ rfl with ⟨ w, hw₁, hw₂, hw₃ ⟩ ; use w ++ [ ‹σ × ( a : α ) × τ a›.2.fst ] ; simp_all +decide [ DFA.evalFrom ] ;
      exact ⟨ _, hw₂, _, h₁.1, rfl ⟩

private lemma εClosure_inr_cases (q : σ) (a : α) (t : τ a)
    (x : σ ⊕ (σ × (Σ a : α, τ a)))
    (hx : x ∈ (substεNFA M τ N).εClosure {Sum.inr (q, (⟨a, t⟩ : Σ a, τ a))}) :
    x = Sum.inr (q, ⟨a, t⟩) ∨
    (t ∈ (N a).accept ∧ x ∈ (substεNFA M τ N).εClosure {Sum.inl (M.step q a)}) := by
  induction' hx with x hx ih;
  · aesop;
  · unfold substεNFA at *;
    rename_i h₁ h₂ h₃;
    rcases h₃ with ( rfl | ⟨ ht, h₃ ⟩ );
    · by_cases h : t ∈ ( N a ).accept <;> simp +decide [ h ] at h₁ ⊢;
      exact Or.inr ( by exact Set.mem_setOf.mpr <| by tauto );
    · refine' Or.inr ⟨ ht, _ ⟩;
      apply_rules [ εNFA.εClosure.step ]

/-
Concatenating words from two product languages gives a word in the combined product.
-/
private lemma prod_append_mem (f : α → Language β) (w₁ w₂ : List α) (u₁ u₂ : List β)
    (h₁ : u₁ ∈ (w₁.map f).prod) (h₂ : u₂ ∈ (w₂.map f).prod) :
    u₁ ++ u₂ ∈ ((w₁ ++ w₂).map f).prod := by
  rw [List.map_append, List.prod_append];
  exact ⟨ u₁, h₁, u₂, h₂, rfl ⟩

/-
Helper: a singleton list product is just the language itself.
-/
private lemma singleton_map_prod (f : α → Language β) (a : α) (u : List β) :
    u ∈ ([a].map f).prod ↔ u ∈ f a := by
  grind

/-
Helper: combining products for the step case.
-/
private lemma step_prod_mem (f : α → Language β) (w₀ : List α) (a₀ : α)
    (w_extra : List α) (v₁ v₂b : List β)
    (hv₁ : v₁ ∈ (w₀.map f).prod)
    (hv₂b : v₂b ∈ f a₀)
    (hempty : ([] : List β) ∈ (w_extra.map f).prod) :
    v₁ ++ v₂b ∈ ((w₀ ++ [a₀] ++ w_extra).map f).prod := by
  convert prod_append_mem f ( w₀ ++ [ a₀ ] ) w_extra ( v₁ ++ v₂b ) [] _ _ using 1;
  · grind;
  · exact prod_append_mem f w₀ [ a₀ ] v₁ v₂b hv₁ ( by simpa using hv₂b );
  · assumption

/-
The step case helper: given that s₀ = Sum.inr (q₀, ⟨a₀, t₀⟩) ∈ evalFrom v'
    satisfies the inr invariant, any state x in εClosure (step s₀ (some b))
    satisfies both invariants for v' ++ [b].
-/
private lemma forward_step_analysis (q : σ) (v' : List β) (b : β)
    (q₀ : σ) (a₀ : α) (t₀ : τ a₀)
    (w₀ : List α) (v₁ v₂ : List β)
    (hv_split : v' = v₁ ++ v₂)
    (hq₀ : M.evalFrom q w₀ = q₀)
    (hv₁_prod : v₁ ∈ (w₀.map (fun a => (N a).accepts)).prod)
    (ht₀ : t₀ = (N a₀).evalFrom (N a₀).start v₂)
    (x : σ ⊕ (σ × (Σ a : α, τ a)))
    (hx : x ∈ (substεNFA M τ N).εClosure
      {Sum.inr (q₀, (⟨a₀, (N a₀).step t₀ b⟩ : Σ a, τ a))}) :
    (∀ q' : σ, x = Sum.inl q' →
      ∃ w : List α, M.evalFrom q w = q' ∧
        v' ++ [b] ∈ (w.map (fun a => (N a).accepts)).prod) ∧
    (∀ (q' : σ) (a : α) (s : τ a), x = Sum.inr (q', (⟨a, s⟩ : Σ a, τ a)) →
      ∃ (w : List α) (v₁' v₂' : List β), v' ++ [b] = v₁' ++ v₂' ∧ M.evalFrom q w = q' ∧
        v₁' ∈ (w.map (fun a => (N a).accepts)).prod ∧
        s = (N a).evalFrom (N a).start v₂') := by
  constructor <;> intros;
  · rename_i q' hq';
    -- Apply εClosure_inr_cases to hx.
    obtain ⟨ht', hx'⟩ : (N a₀).step t₀ b ∈ (N a₀).accept ∧ x ∈ (substεNFA M τ N).εClosure {Sum.inl (M.step q₀ a₀)} := by
      have := εClosure_inr_cases ( M := M ) ( N := N ) ( q := q₀ ) ( a := a₀ ) ( t := ( N a₀ ).step t₀ b ) x hx; aesop;
    -- Apply εClosure_inl_inv to x ∈ εClosure {Sum.inl (M.step q₀ a₀)}.
    obtain ⟨w_extra, hw_extra⟩ : ∃ w_extra : List α, M.evalFrom (M.step q₀ a₀) w_extra = q' ∧ [] ∈ (w_extra.map (fun a => (N a).accepts)).prod := by
      have := εClosure_inl_inv ( M.step q₀ a₀ ) x hx'; aesop;
    refine' ⟨ w₀ ++ [ a₀ ] ++ w_extra, _, _ ⟩ <;> simp_all +decide [ DFA.evalFrom ];
    refine' ⟨ v₁, _, v₂ ++ [ b ], _, _ ⟩ <;> simp_all +decide [ Language.mul_def ];
    refine' ⟨ v₂ ++ [ b ], _, [ ], _, _ ⟩ <;> simp_all +decide [ DFA.accepts ];
    convert ht' using 1;
    simp +decide [ DFA.acceptsFrom, DFA.evalFrom ];
  · rename_i q' a s hs;
    have hεClosure_cases : x = Sum.inr (q₀, ⟨a₀, (N a₀).step t₀ b⟩) ∨ ( (N a₀).step t₀ b ∈ (N a₀).accept ∧ x ∈ (substεNFA M τ N).εClosure {Sum.inl (M.step q₀ a₀)} ) := by
      apply εClosure_inr_cases; assumption;
    rcases hεClosure_cases with ( rfl | ⟨ h₁, h₂ ⟩ ) <;> simp_all +decide [];
    · grind +suggestions;
    · have := εClosure_inl_inv ( M.step q₀ a₀ ) ( Sum.inr ( q', ⟨ a, s ⟩ ) ) h₂; simp_all +decide [] ;
      obtain ⟨ w, hw₁, hw₂, hw₃ ⟩ := this q' a s rfl rfl ( by tauto ) ; use w₀ ++ [ a₀ ] ++ w, v₁ ++ v₂ ++ [ b ], [ ] ; simp_all +decide [ List.map_append ] ;
      constructor;
      · simp_all +decide [ DFA.evalFrom ];
      · have h_prod : v₁ ++ (v₂ ++ [b]) ∈ ((w₀ ++ [a₀] ++ w).map (fun a => (N a).accepts)).prod := by
          apply step_prod_mem;
          · assumption;
          · simp_all +decide [ DFA.mem_accepts ];
            convert h₁ using 1;
          · exact hw₂;
        grind

private lemma forward_inv (q : σ) (v : List β) :
    (∀ q' : σ, Sum.inl q' ∈ (substεNFA M τ N).evalFrom {Sum.inl q} v →
      ∃ w : List α, M.evalFrom q w = q' ∧
        v ∈ (w.map (fun a => (N a).accepts)).prod) ∧
    (∀ (q' : σ) (a : α) (s : τ a),
      Sum.inr (q', (⟨a, s⟩ : Σ a, τ a)) ∈ (substεNFA M τ N).evalFrom {Sum.inl q} v →
      ∃ (w : List α) (v₁ v₂ : List β), v = v₁ ++ v₂ ∧ M.evalFrom q w = q' ∧
        v₁ ∈ (w.map (fun a => (N a).accepts)).prod ∧
        s = (N a).evalFrom (N a).start v₂) := by
  induction v using List.reverseRecOn with
  | nil =>
    rw [εNFA.evalFrom_nil]
    exact ⟨fun q' hq' => (εClosure_inl_inv q _ hq').1 q' rfl,
      fun q' a s hq' => by
        obtain ⟨w, hw1, hw2, hw3⟩ := (εClosure_inl_inv q _ hq').2 q' a s rfl
        exact ⟨w, [], [], rfl, hw1, hw2, by simp [DFA.evalFrom, hw3]⟩⟩
  | append_singleton v' b ih =>
    obtain ⟨ih_inl, ih_inr⟩ := ih
    rw [εNFA.evalFrom_append_singleton]
    -- Helper: extract source state from stepSet membership
    have extract_source : ∀ (x : σ ⊕ (σ × (Σ a : α, τ a))),
        x ∈ (substεNFA M τ N).stepSet ((substεNFA M τ N).evalFrom {Sum.inl q} v') b →
        ∃ (q₀ : σ) (a₀ : α) (t₀ : τ a₀),
          Sum.inr (q₀, (⟨a₀, t₀⟩ : Σ a, τ a)) ∈
            (substεNFA M τ N).evalFrom {Sum.inl q} v' ∧
          x ∈ (substεNFA M τ N).εClosure
            {Sum.inr (q₀, (⟨a₀, (N a₀).step t₀ b⟩ : Σ a, τ a))} := by
      intro x hx
      simp only [εNFA.stepSet] at hx
      obtain ⟨s₀, hs₀_mem, hs₀_cl⟩ := Set.mem_iUnion₂.mp hx
      rcases s₀ with q₀ | ⟨q₀, a₀, t₀⟩
      · simp [substεNFA] at hs₀_cl
      · exact ⟨q₀, a₀, t₀, hs₀_mem, by simpa [substεNFA] using hs₀_cl⟩
    constructor
    · -- Sum.inl case
      intro q' hq'
      obtain ⟨q₀, a₀, t₀, hs₀_mem, hx_cl⟩ := extract_source _ hq'
      obtain ⟨w₀, v₁, v₂, hv_split, hq₀, hv₁_prod, ht₀⟩ := ih_inr q₀ a₀ t₀ hs₀_mem
      exact (forward_step_analysis q v' b q₀ a₀ t₀ w₀ v₁ v₂
        hv_split hq₀ hv₁_prod ht₀ _ hx_cl).1 q' rfl
    · -- Sum.inr case
      intro q' a s hq'
      obtain ⟨q₀, a₀, t₀, hs₀_mem, hx_cl⟩ := extract_source _ hq'
      obtain ⟨w₀, v₁, v₂, hv_split, hq₀, hv₁_prod, ht₀⟩ := ih_inr q₀ a₀ t₀ hs₀_mem
      exact (forward_step_analysis q v' b q₀ a₀ t₀ w₀ v₁ v₂
        hv_split hq₀ hv₁_prod ht₀ _ hx_cl).2 q' a s rfl

private lemma subst_forward {u : List β}
    (hu : u ∈ (substεNFA M τ N).accepts) :
    u ∈ M.accepts.subst (fun a => (N a).accepts) := by
  obtain ⟨q', hq'⟩ : ∃ q', Sum.inl q' ∈ (substεNFA M τ N).evalFrom {Sum.inl M.start} u ∧ q' ∈ M.accept := by
    obtain ⟨ q', hq' ⟩ := hu;
    unfold Language.substεNFA at *; aesop;
  have := forward_inv ( M := M ) ( τ := τ ) ( N := N ) M.start u;
  exact Exists.elim ( this.1 q' hq'.1 ) fun w hw => ⟨ w, by aesop ⟩

/-- The substitution ε-NFA accepts exactly the substitution of the DFA language. -/
theorem substεNFA_correct :
    (substεNFA M τ N).accepts = M.accepts.subst (fun a => (N a).accepts) :=
  Set.eq_of_subset_of_subset
    (fun _ hw => subst_forward hw)
    (fun _ hw => subst_backward hw)

end SubstεNFA

/-- Regular languages are closed under substitution (requires finite source alphabet). -/
theorem IsRegular.subst' {L : Language α} {f : α → Language β}
    (hL : L.IsRegular) (hf : ∀ a, (f a).IsRegular) :
    (L.subst f).IsRegular := by
  obtain ⟨σ, _, M, rfl⟩ := hL
  choose τ_type τ_fin N_dfa hN using hf
  haveI := τ_fin
  rw [show f = fun a => (N_dfa a).accepts from funext (fun a => (hN a).symm)]
  rw [← substεNFA_correct (M := M) (τ := τ_type) (N := N_dfa)]
  exact ⟨_, inferInstance, (substεNFA M τ_type N_dfa).toNFA.toDFA,
    by rw [NFA.toDFA_correct, εNFA.toNFA_correct]⟩

end Language