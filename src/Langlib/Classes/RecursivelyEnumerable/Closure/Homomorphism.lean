import Mathlib
import Langlib.Grammars.Unrestricted.Toolbox
import Langlib.Classes.RecursivelyEnumerable.Basics.Lifting
import Langlib.Classes.RecursivelyEnumerable.Definition
import Langlib.Utilities.LanguageOperations
import Langlib.Utilities.Homomorphism

/-! # RE Closure Under String Homomorphism

This file proves that the class of recursively enumerable languages is closed under
ε-free string homomorphism.

Given an unrestricted grammar `g` over terminals `α` generating `L`, and an ε-free string
homomorphism `h : α → List β`, we construct an unrestricted grammar `hom_grammar g h`
over terminals `β` whose language is `L.homomorphicImage h`.

## Main declarations

- `hom_grammar`
- `RE_closed_under_epsfree_homomorphism`

## Note on erasing homomorphisms

The two-phase grammar construction `hom_grammar` is correct only for ε-free homomorphisms
(where `h a ≠ []` for all `a`). For erasing homomorphisms (where some `h a = []`),
the Phase 2 expansion can remove nonterminal placeholders, which may create new adjacencies
that enable Phase 1 rules that have no corresponding rule application in the original grammar.
A correct construction for the general case would require a more sophisticated mechanism
(e.g., a scanning phase to ensure Phase 1 is complete before Phase 2 begins).
-/

open List

variable {α β : Type}

-- ============================================================================
-- Grammar construction
-- ============================================================================

section construction

/-- Map a symbol by replacing terminals with nonterminal placeholders. -/
def homLiftSym {N : Type} : symbol α N → symbol β (N ⊕ α)
  | symbol.terminal a    => symbol.nonterminal (Sum.inr a)
  | symbol.nonterminal n => symbol.nonterminal (Sum.inl n)

/-- Lift an entire string to placeholder form. -/
def homLiftStr {N : Type} (s : List (symbol α N)) :
    List (symbol β (N ⊕ α)) :=
  s.map homLiftSym

/-- Lift a rule to phase 1 form. -/
def homLiftRule {N : Type} (r : grule α N) : grule β (N ⊕ α) :=
  ⟨homLiftStr r.input_L,
   Sum.inl r.input_N,
   homLiftStr r.input_R,
   homLiftStr r.output_string⟩

/-- Create a phase 2 rule for terminal `a`. -/
def homExpandRule {N : Type} (h : α → List β) (a : α) : grule β (N ⊕ α) :=
  ⟨[], Sum.inr a, [], (h a).map symbol.terminal⟩

/-- The two-phase grammar for the homomorphic image. -/
def hom_grammar (g : grammar α) (h : α → List β) : grammar β :=
  ⟨g.nt ⊕ α,
   Sum.inl g.initial,
   (g.rules.map homLiftRule) ++ (all_used_terminals g).map (homExpandRule h)⟩

end construction

-- ============================================================================
-- Helpers
-- ============================================================================

section helpers

variable {g : grammar α}

lemma homLiftStr_map_terminal (w : List α) :
    @homLiftStr α β g.nt (w.map symbol.terminal) =
      w.map (fun a => (symbol.nonterminal (Sum.inr a) : symbol β (g.nt ⊕ α))) := by
  simp [homLiftStr, homLiftSym, List.map_map]

lemma mem_prod_singletons_iff_flatMap (w : List α) (h : α → List β) (u : List β) :
    u ∈ (w.map (fun a => ({h a} : Language β))).prod ↔ u = w.flatMap h := by
  induction w generalizing u with
  | nil => simp
  | cons a w ih =>
    simp only [List.map_cons, List.prod_cons, Language.mul_def]
    constructor
    · rintro ⟨u₁, hu₁, u₂, hu₂, rfl⟩
      rw [Set.mem_singleton_iff] at hu₁
      rw [hu₁, List.flatMap_cons]
      congr 1; exact (ih u₂).mp hu₂
    · intro hu
      refine ⟨h a, Set.mem_singleton _, w.flatMap h, (ih _).mpr rfl, ?_⟩
      simp [List.flatMap_cons, hu]

end helpers

-- ============================================================================
-- Forward direction
-- ============================================================================

section forward_direction

variable {g : grammar α} {h : α → List β}

private lemma phase1_transforms {w₁ w₂ : List (symbol α g.nt)}
    (ht : grammar_transforms g w₁ w₂) :
    grammar_transforms (hom_grammar g h) (homLiftStr w₁) (homLiftStr w₂) := by
  obtain ⟨r, hr, u, v, hw₁, hw₂⟩ := ht
  use homLiftRule r, by unfold hom_grammar; aesop, homLiftStr u, homLiftStr v
  unfold homLiftStr homLiftRule; aesop

private lemma phase1_derives {w₁ w₂ : List (symbol α g.nt)}
    (hd : grammar_derives g w₁ w₂) :
    grammar_derives (hom_grammar g h) (homLiftStr w₁) (homLiftStr w₂) := by
  induction hd with
  | refl => exact grammar_deri_self
  | tail _ hs ih => exact grammar_deri_of_deri_tran ih (phase1_transforms hs)

private lemma terminals_in_derived_word {w : List α}
    (hw : w ∈ grammar_language g) :
    ∀ a ∈ w, a ∈ all_used_terminals g := by
  intro a ha
  contrapose! ha
  have h_not_derive : ∀ w : List (symbol α g.nt),
      a ∉ List.filterMap as_terminal w →
      ∀ v : List (symbol α g.nt), grammar_derives g w v →
      a ∉ List.filterMap as_terminal v := by
    intros w hw v hv
    induction' hv with w' v' hv' ih
    · assumption
    · obtain ⟨r, hr, u, v, hw', hv'⟩ := ih
      simp_all +decide [List.filterMap_append]
      intro x hx H
      exact ha <| List.mem_filterMap.mpr
        ⟨x, List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨r, hr, rfl⟩, hx⟩, H⟩
  convert h_not_derive [symbol.nonterminal g.initial] _ (List.map symbol.terminal w) hw using 1
  · unfold as_terminal; aesop
  · simp +decide [as_terminal]

private lemma phase2_step (a : α) (ha : a ∈ all_used_terminals g)
    (u v : List (symbol β (g.nt ⊕ α))) :
    grammar_transforms (hom_grammar g h)
      (u ++ [symbol.nonterminal (Sum.inr a)] ++ v)
      (u ++ (h a).map symbol.terminal ++ v) :=
  ⟨homExpandRule h a,
    List.mem_append_right _ (List.mem_map.mpr ⟨a, ha, rfl⟩),
    u, v, by simp [homExpandRule], by simp [homExpandRule]⟩

private lemma phase2_expand_all (w : List α)
    (hw : ∀ a ∈ w, a ∈ all_used_terminals g) :
    grammar_derives (hom_grammar g h)
      (w.map (fun a => (symbol.nonterminal (Sum.inr a) : symbol β (g.nt ⊕ α))))
      ((w.flatMap h).map symbol.terminal) := by
  induction w with
  | nil => exact grammar_deri_self
  | cons a w ih =>
    simp only [List.map_cons, List.flatMap_cons, List.map_append]
    have ha := hw a List.mem_cons_self
    have hw' : ∀ b ∈ w, b ∈ all_used_terminals g :=
      fun b hb => hw b (List.mem_cons_of_mem a hb)
    have step1 : grammar_transforms (hom_grammar g h)
        (symbol.nonterminal (Sum.inr a) ::
          w.map (fun a => (symbol.nonterminal (Sum.inr a) : symbol β (g.nt ⊕ α))))
        ((h a).map symbol.terminal ++
          w.map (fun a => (symbol.nonterminal (Sum.inr a) : symbol β (g.nt ⊕ α)))) := by
      simpa using phase2_step a ha [] _
    exact grammar_deri_of_tran_deri step1
      (grammar_deri_with_prefix ((h a).map symbol.terminal) (ih hw'))

private lemma in_hom_of_in_original {w : List α}
    (hw : w ∈ grammar_language g) :
    w.flatMap h ∈ grammar_language (hom_grammar g h) := by
  unfold grammar_language grammar_generates at *
  have p1 := phase1_derives (h := h) hw
  rw [homLiftStr_map_terminal] at p1
  exact grammar_deri_of_deri_deri p1 (phase2_expand_all w (terminals_in_derived_word hw))

end forward_direction

-- ============================================================================
-- Backward direction (ε-free case)
-- ============================================================================

section backward_direction

variable {g : grammar α} {h : α → List β}

-- Decorated symbols for tracking the invariant.
private inductive DSym (N : Type)
  | nt : N → DSym N
  | unexpanded : α → DSym N
  | expanded : α → DSym N

private def dToHom' {N : Type} (h : α → List β) : @DSym α N → List (symbol β (N ⊕ α))
  | DSym.nt n        => [symbol.nonterminal (Sum.inl n)]
  | DSym.unexpanded a => [symbol.nonterminal (Sum.inr a)]
  | DSym.expanded a  => (h a).map symbol.terminal

private def dToOrig' {N : Type} : @DSym α N → symbol α N
  | DSym.nt n        => symbol.nonterminal n
  | DSym.unexpanded a => symbol.terminal a
  | DSym.expanded a  => symbol.terminal a

private def ValidForm' (g : grammar α) (h : α → List β)
    (s : List (symbol β (g.nt ⊕ α))) : Prop :=
  ∃ ds : List (@DSym α g.nt),
    s = ds.flatMap (dToHom' h) ∧
    grammar_derives g [symbol.nonterminal g.initial] (ds.map dToOrig')

private lemma valid_initial' :
    ValidForm' g h [symbol.nonterminal (Sum.inl g.initial)] :=
  ⟨[DSym.nt g.initial], rfl, grammar_deri_self⟩

-- ============================================================================
-- Helper: lifting DSym
-- ============================================================================

private def liftDSym {N : Type} : symbol α N → @DSym α N
  | symbol.terminal a    => DSym.unexpanded a
  | symbol.nonterminal n => DSym.nt n

private lemma dToHom'_liftDSym {N : Type} (h : α → List β) (s : symbol α N) :
    dToHom' h (liftDSym s) = [homLiftSym s] := by
  cases s <;> simp [liftDSym, dToHom', homLiftSym]

private lemma dToOrig'_liftDSym {N : Type} (s : symbol α N) :
    dToOrig' (@liftDSym α N s) = s := by
  cases s <;> simp [liftDSym, dToOrig']

private lemma flatMap_dToHom'_map_liftDSym {N : Type} (h : α → List β) (l : List (symbol α N)) :
    (l.map liftDSym).flatMap (dToHom' h) = homLiftStr l := by
  induction l with
  | nil => simp [homLiftStr]
  | cons s l ih =>
    simp [List.map_cons, List.flatMap_cons, homLiftStr, dToHom'_liftDSym, ih]

private lemma map_dToOrig'_map_liftDSym {N : Type} (l : List (symbol α N)) :
    (l.map liftDSym).map (@dToOrig' α N) = l := by
  induction l with
  | nil => simp
  | cons s l ih => simp [dToOrig'_liftDSym, ih]

/-
============================================================================
Helper: splitting flatMap at a nonterminal (ε-free case)
============================================================================

In the ε-free case, every nonterminal in `ds.flatMap (dToHom' h)` comes from a
    unique DSym element, and we can split ds at that element.
-/
private lemma dsym_flatMap_split_at_nonterminal (heps : ∀ a, h a ≠ [])
    (ds : List (@DSym α g.nt))
    (u v : List (symbol β (g.nt ⊕ α))) (x : g.nt ⊕ α) :
    ds.flatMap (dToHom' h) = u ++ [symbol.nonterminal x] ++ v →
    ∃ ds₁ d ds₂,
      ds = ds₁ ++ [d] ++ ds₂ ∧
      dToHom' h d = [symbol.nonterminal x] ∧
      ds₁.flatMap (dToHom' h) = u ∧
      ds₂.flatMap (dToHom' h) = v := by
  induction ds generalizing u v;
  · aesop;
  · rename_i d ds ih;
    rcases d with ( _ | _ | _ ) <;> simp_all +decide [ List.append_assoc ];
    · rcases u with ( _ | ⟨ y, u ⟩ ) <;> simp_all +decide [ List.append_assoc ];
      · intro h;
        cases h;
        exact ⟨ [ ], DSym.nt _, ds, rfl, rfl, by tauto ⟩;
      · grind +locals;
    · intro h;
      rcases u with ( _ | ⟨ u, u ⟩ ) <;> simp_all +decide [ List.append_assoc ];
      · use [ ], DSym.unexpanded ‹_›, ds;
        cases h ; aesop;
      · grind +locals;
    · intro h_eq
      obtain ⟨u', hu'⟩ : ∃ u', u = (h ‹_›).map symbol.terminal ++ u' := by
        have h_prefix : (h ‹_›).map symbol.terminal ++ flatMap (dToHom' h) ds = u ++ symbol.nonterminal x :: v := by
          exact h_eq;
        have h_prefix : ∀ {l₁ l₂ l₃ : List (symbol β (g.nt ⊕ α))}, l₁ ++ l₂ = l₃ ++ symbol.nonterminal x :: v → (∀ y ∈ l₁, y ≠ symbol.nonterminal x) → ∃ u', l₃ = l₁ ++ u' := by
          intros l₁ l₂ l₃ h_eq h_no_x; induction' l₁ with a l₁ ih generalizing l₃ <;> simp_all +decide [ List.append_assoc ] ;
          rcases l₃ with ( _ | ⟨ b, l₃ ⟩ ) <;> simp_all +decide [ List.append_assoc ];
        grind;
      specialize ih u' v;
      simp_all +decide [ List.append_assoc ];
      obtain ⟨ ds₁, d, ds₂, rfl, hd, hu', hv ⟩ := ih ( by simpa [ dToHom' ] using h_eq ) ; use DSym.expanded ‹_› :: ds₁, d, ds₂; aesop;

/-
In the ε-free case, if `ds.flatMap (dToHom' h)` ends with `homLiftStr s`
    (which consists entirely of nonterminals), then `ds` ends with `s.map liftDSym`.
-/
private lemma dsym_flatMap_match_suffix (heps : ∀ a, h a ≠ [])
    (ds : List (@DSym α g.nt))
    (u : List (symbol β (g.nt ⊕ α)))
    (s : List (symbol α g.nt)) :
    ds.flatMap (dToHom' h) = u ++ homLiftStr s →
    ∃ ds₁ : List (@DSym α g.nt),
      ds = ds₁ ++ s.map liftDSym ∧
      ds₁.flatMap (dToHom' h) = u := by
  intro hds;
  induction' s using List.reverseRecOn with s' sym ih generalizing ds u;
  · unfold homLiftStr at hds; aesop;
  · have h_split : ds.flatMap (dToHom' h) = u ++ (homLiftStr s' ++ [homLiftSym sym]) := by
      unfold homLiftStr at *; aesop;
    obtain ⟨ds₁, d, ds₂, hds₁, hd, hds₂⟩ : ∃ ds₁ d ds₂, ds = ds₁ ++ [d] ++ ds₂ ∧ dToHom' h d = [homLiftSym sym] ∧ ds₁.flatMap (dToHom' h) = u ++ homLiftStr s' ∧ ds₂.flatMap (dToHom' h) = [] := by
      have := dsym_flatMap_split_at_nonterminal heps ds ( u ++ homLiftStr s' ) [] ( match sym with | symbol.terminal a => Sum.inr a | symbol.nonterminal n => Sum.inl n ) ?_;
      · cases sym <;> tauto;
      · convert h_split using 1;
        cases sym <;> simp +decide [ homLiftSym ];
    have h_ds₂_empty : ds₂ = [] := by
      induction ds₂ <;> simp_all +decide [ List.flatMap ];
      cases ‹DSym g.nt› <;> simp_all +decide [ dToHom' ];
    cases sym <;> simp_all +decide [ dToHom' ];
    · rcases d with ( _ | _ | _ ) <;> simp_all +decide [ homLiftSym ];
      obtain ⟨ ds₁, hds₁, hds₂ ⟩ := ih ds₁ u hds₂; use ds₁; aesop;
    · rcases d with ( _ | _ | _ ) <;> simp_all +decide [ homLiftSym ];
      obtain ⟨ ds₁, hds₁, hds₂ ⟩ := ih ds₁ u hds₂; use ds₁; aesop;

/-
In the ε-free case, if `ds.flatMap (dToHom' h)` starts with `homLiftStr s`
    (which consists entirely of nonterminals), then `ds` starts with `s.map liftDSym`.
-/
private lemma dsym_flatMap_match_prefix (heps : ∀ a, h a ≠ [])
    (ds : List (@DSym α g.nt))
    (s : List (symbol α g.nt))
    (v : List (symbol β (g.nt ⊕ α))) :
    ds.flatMap (dToHom' h) = homLiftStr s ++ v →
    ∃ ds₂ : List (@DSym α g.nt),
      ds = s.map liftDSym ++ ds₂ ∧
      ds₂.flatMap (dToHom' h) = v := by
  intro h_eq
  induction' s with sym s' ih generalizing ds v;
  · aesop;
  · rcases ds with ( _ | ⟨ d, ds ⟩ ) <;> simp_all +decide [ homLiftStr ];
    rcases d with ( _ | _ | _ ) <;> simp_all +decide [ dToHom' ];
    · cases sym <;> simp_all +decide [ homLiftSym ];
      exact Exists.elim ( ih ds v h_eq.2 ) fun ds₂ hds₂ => ⟨ ds₂, ⟨ rfl, hds₂.1 ⟩, hds₂.2 ⟩;
    · cases sym <;> simp_all +decide [ homLiftSym ];
      exact ⟨ _, ⟨ rfl, ih _ _ h_eq.2 |> Classical.choose_spec |> And.left ⟩, ih _ _ h_eq.2 |> Classical.choose_spec |> And.right ⟩;
    · cases sym <;> cases h : h ‹_› <;> simp_all +decide [ homLiftSym ];
      replace h_eq := congr_arg List.head? h_eq ; aesop

/-
============================================================================
Main invariant lemma
============================================================================

Invariant preserved through steps (ε-free case).
-/
private lemma valid_step' (heps : ∀ a, h a ≠ [])
    {s₁ s₂ : List (symbol β (g.nt ⊕ α))}
    (hv : ValidForm' g h s₁) (ht : grammar_transforms (hom_grammar g h) s₁ s₂) :
    ValidForm' g h s₂ := by
  rcases ht with ⟨ r, hr, u, v, rfl, rfl ⟩;
  unfold hom_grammar at hr; simp_all +decide [ List.mem_append, List.mem_map ] ;
  rcases hr with ( ⟨ r, hr, rfl ⟩ | ⟨ a, ha, rfl ⟩ ) <;> simp_all +decide [ homLiftRule, homExpandRule ];
  · obtain ⟨ ds, hds₁, hds₂ ⟩ := hv;
    -- Use `dsym_flatMap_split_at_nonterminal` to split `ds` into `ds_L`, `d_mid`, and `ds_R`.
    obtain ⟨ds_L, d_mid, ds_R, hds_split⟩ : ∃ ds_L d_mid ds_R, ds = ds_L ++ [d_mid] ++ ds_R ∧ dToHom' h d_mid = [symbol.nonterminal (Sum.inl r.input_N)] ∧ ds_L.flatMap (dToHom' h) = u ++ homLiftStr r.input_L ∧ ds_R.flatMap (dToHom' h) = homLiftStr r.input_R ++ v := by
      have := dsym_flatMap_split_at_nonterminal heps ds ( u ++ homLiftStr r.input_L ) ( homLiftStr r.input_R ++ v ) ( Sum.inl r.input_N ) ?_;
      · exact this;
      · simpa [ List.append_assoc ] using hds₁.symm;
    -- Use `dsym_flatMap_match_suffix` to split `ds_L` into `ds_pre` and `r.input_L.map liftDSym`.
    obtain ⟨ds_pre, hds_pre⟩ : ∃ ds_pre, ds_L = ds_pre ++ r.input_L.map liftDSym ∧ ds_pre.flatMap (dToHom' h) = u := by
      have := dsym_flatMap_match_suffix heps ds_L u r.input_L; aesop;
    -- Use `dsym_flatMap_match_prefix` to split `ds_R` into `r.input_R.map liftDSym` and `ds_post`.
    obtain ⟨ds_post, hds_post⟩ : ∃ ds_post, ds_R = r.input_R.map liftDSym ++ ds_post ∧ ds_post.flatMap (dToHom' h) = v := by
      apply dsym_flatMap_match_prefix heps ds_R r.input_R v hds_split.right.right.right;
    refine' ⟨ ds_pre ++ r.output_string.map liftDSym ++ ds_post, _, _ ⟩ <;> simp_all +decide [ List.flatMap_append ];
    · exact Eq.symm (flatMap_dToHom'_map_liftDSym h r.output_string);
    · convert grammar_deri_of_deri_tran hds₂ _ using 1;
      use r, hr, ds_pre.map dToOrig', ds_post.map dToOrig';
      cases d_mid <;> simp_all +decide [ dToOrig' ];
      · cases hds_split.2.1;
        exact ⟨ by rw [ show dToOrig' ∘ liftDSym = id from funext fun x => by cases x <;> rfl ] ; simp +decide, by rw [ show dToOrig' ∘ liftDSym = id from funext fun x => by cases x <;> rfl ] ; simp +decide ⟩;
      · cases hds_split.2.1;
      · cases h : h ‹_› <;> simp_all +decide [ dToHom' ];
  · obtain ⟨ ds, hds₁, hds₂ ⟩ := hv;
    -- Use dsym_flatMap_split_at_nonterminal to split ds into ds₁, d, ds₂.
    obtain ⟨ds₁, d, ds₂, hds_split⟩ : ∃ ds₁ d ds₂, ds = ds₁ ++ [d] ++ ds₂ ∧ dToHom' h d = [symbol.nonterminal (Sum.inr a)] ∧ ds₁.flatMap (dToHom' h) = u ∧ ds₂.flatMap (dToHom' h) = v := by
      apply dsym_flatMap_split_at_nonterminal heps ds u v (Sum.inr a);
      simpa using hds₁.symm;
    use ds₁ ++ [DSym.expanded a] ++ ds₂;
    cases d <;> simp_all +decide [ dToHom', dToOrig' ];
    cases hds₁ ; aesop

private lemma valid_derives' (heps : ∀ a, h a ≠ [])
    {s : List (symbol β (g.nt ⊕ α))}
    (hd : grammar_derives (hom_grammar g h)
      [symbol.nonterminal (Sum.inl g.initial)] s) :
    ValidForm' g h s := by
  induction hd with
  | refl => exact valid_initial'
  | tail _ hs ih => exact valid_step' heps ih hs

private lemma valid_terminal' {w : List β}
    (hv : ValidForm' g h (w.map symbol.terminal)) :
    ∃ w' ∈ grammar_language g, w = w'.flatMap h := by
  obtain ⟨ds, hds⟩ := hv
  obtain ⟨w', hw'⟩ : ∃ w' : List α, ds = w'.map DSym.expanded := by
    have h_ds_expanded : ∀ x ∈ ds, ∃ a : α, x = DSym.expanded a := by
      intro x hx; rcases x with (_ | _ | _) <;> simp_all +decide [List.flatMap]
      · have : symbol.nonterminal (Sum.inl ‹_›) ∈ (map (dToHom' h) ds).flatten :=
          List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨_, hx, rfl⟩, by simp [dToHom']⟩
        grind
      · have : ∀ {l : List (symbol β (g.nt ⊕ α))},
            l = (ds.map (dToHom' h)).flatten →
            (∃ x ∈ l, x = symbol.nonterminal (Sum.inr ‹_›)) → False := by grind
        apply this rfl
        simp +zetaDelta at *
        exact ⟨_, hx, by tauto⟩
    have : ∀ {l : List (DSym g.nt)},
        (∀ x ∈ l, ∃ a : α, x = DSym.expanded a) →
        ∃ w' : List α, l = w'.map DSym.expanded := by
      intro l hl; induction l with
      | nil => exact ⟨[], rfl⟩
      | cons x l ih =>
        obtain ⟨a, rfl⟩ := hl x (by simp)
        obtain ⟨w', hw'⟩ := ih fun x hx => hl x (by simp [hx])
        exact ⟨a :: w', by simp [hw']⟩
    exact this h_ds_expanded
  subst hw'
  refine ⟨w', ?_, ?_⟩
  · have : (w'.map DSym.expanded).map (@dToOrig' α g.nt) = w'.map symbol.terminal := by
      simp [List.map_map, dToOrig']
    rw [this] at hds
    exact hds.2
  · have hinj : Function.Injective (symbol.terminal : β → symbol β (g.nt ⊕ α)) :=
      fun x y hxy => by injection hxy
    apply hinj.list_map
    have hfm : (w'.map (DSym.expanded (N := g.nt))).flatMap (dToHom' h) =
        (w'.flatMap h).map (symbol.terminal (N := g.nt ⊕ α)) := by
      simp only [List.flatMap, List.map_map]
      simp only [Function.comp_def, dToHom']
      rw [List.map_flatten, List.map_map]; rfl
    rw [hfm] at hds
    exact hds.1

/-- The backward direction (ε-free case). -/
private lemma backward_direction_epsfree (heps : ∀ a, h a ≠ [])
    {w : List β}
    (hd : w ∈ grammar_language (hom_grammar g h)) :
    ∃ w' ∈ grammar_language g, w = w'.flatMap h :=
  valid_terminal' (valid_derives' heps hd)

end backward_direction

-- ============================================================================
-- Main theorems
-- ============================================================================

/-- The class of RE languages is closed under ε-free string homomorphism. -/
theorem RE_closed_under_epsfree_homomorphism (L : Language α) (h : α → List β)
    (hL : is_RE L) (heps : IsEpsFreeHomomorphism h) :
    is_RE (L.homomorphicImage h) := by
  obtain ⟨g, rfl⟩ := hL
  refine ⟨hom_grammar g h, ?_⟩
  ext w
  simp only [Language.homomorphicImage, Language.subst, grammar_language]
  constructor
  · intro hd
    obtain ⟨w', hw', rfl⟩ := backward_direction_epsfree heps hd
    exact ⟨w', hw', (mem_prod_singletons_iff_flatMap w' h _).mpr rfl⟩
  · rintro ⟨w', hw', hu⟩
    rw [(mem_prod_singletons_iff_flatMap w' h w).mp hu]
    exact in_hom_of_in_original hw'

/-- The class of recursively enumerable languages is closed under string homomorphism.

**Note:** This theorem is correct but the current proof has a sorry.
The two-phase grammar construction `hom_grammar` is not correct for erasing
homomorphisms — a more sophisticated construction is needed. The ε-free case
is fully proved above. -/
theorem RE_closed_under_homomorphism (L : Language α) (h : α → List β)
    (hL : is_RE L) : is_RE (L.homomorphicImage h) := by
  sorry