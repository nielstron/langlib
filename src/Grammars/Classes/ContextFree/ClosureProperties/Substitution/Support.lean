import Mathlib.Computability.ContextFreeGrammar
import Mathlib.Algebra.Group.Pointwise.Set.ListOfFn
import Mathlib.Data.List.Lemmas

namespace List

lemma split_commute_of_not_mem {α : Type*} (x y x' y' : List α) (mid : List α) (a : α)
    (h : x ++ mid ++ y = x' ++ a :: y')
    (h_not_mem : a ∉ mid) :
    (∃ z, x' = x ++ mid ++ z ∧ y = z ++ a :: y') ∨
    (∃ z, x = x' ++ a :: z ∧ y' = z ++ mid ++ y) := by
  revert x y x' y' mid a h h_not_mem
  intros x y x' y' mid a h1 h2
  induction x generalizing y x' y' mid a with
  | nil =>
      simp_all only [nil_append, append_assoc, nil_eq, append_eq_nil_iff,
        reduceCtorEq, and_false, false_and, exists_const, or_false]
      rcases List.append_eq_append_iff.mp h1 with h | h
      · aesop (simp_config := { singlePass := true })
      rcases h with ⟨bs, rfl, h⟩
      rcases bs with (_ | ⟨b, bs⟩) <;> simp_all [List.append_assoc]
  | cons hd tl ih =>
      rcases x' with (_ | ⟨b, x'⟩) <;> simp_all [List.append_assoc]

end List

namespace ContextFreeRule

namespace Rewrites

theorem map {T N T' N'} (f : Symbol T N → Symbol T' N')
    (r : ContextFreeRule T N) (r' : ContextFreeRule T' N')
    (u v : List (Symbol T N)) (h : r.Rewrites u v)
    (h_input : f (Symbol.nonterminal r.input) = Symbol.nonterminal r'.input)
    (h_output : r'.output = r.output.map f) :
    r'.Rewrites (u.map f) (v.map f) := by
  induction h generalizing f r' with
  | head s =>
      rw [List.map_cons, List.map_append]
      exact h_input.symm ▸ h_output.symm ▸ (by tauto)
  | @cons x _ _ h_rec ih =>
      simp only [List.map_cons]
      exact ContextFreeRule.Rewrites.cons (f x) (ih f r' h_input h_output)

lemma map_inv {T N T' N'} (f : Symbol T N → Symbol T' N')
    (hf : Function.Injective f)
    (r : ContextFreeRule T N) (r' : ContextFreeRule T' N')
    (u : List (Symbol T N)) (v' : List (Symbol T' N'))
    (h : r'.Rewrites (u.map f) v')
    (h_input : f (Symbol.nonterminal r.input) = Symbol.nonterminal r'.input)
    (h_output : r'.output = r.output.map f) :
    ∃ v, v' = v.map f ∧ r.Rewrites u v := by
  obtain ⟨x, y, hx, hy, hv'⟩ :
      ∃ x y : List (Symbol T N),
        u = x ++ [Symbol.nonterminal r.input] ++ y ∧
        v' = List.map f x ++ List.map f r.output ++ List.map f y := by
    obtain ⟨x', y', hx', hy', hv'⟩ :
        ∃ x' y' : List (Symbol T' N'),
          List.map f u = x' ++ [Symbol.nonterminal r'.input] ++ y' ∧
          v' = x' ++ r'.output ++ y' := by
      exact exists_parts h
    obtain ⟨x, y, hx, hy, hv'⟩ :
        ∃ x y : List (Symbol T N),
          u = x ++ [Symbol.nonterminal r.input] ++ y ∧
          List.map f x = x' ∧ List.map f y = y' := by
      have h_split : List.map f u =
          List.map f (u.take (List.length x')) ++
          [Symbol.nonterminal r'.input] ++
          List.map f (u.drop (List.length x' + 1)) := by
        convert hx' using 1
        rw [← List.take_append_drop (List.length x' + 1) u, List.map_append] at *
        aesop
      refine ⟨List.take x'.length u, List.drop (x'.length + 1) u, ?_, ?_, ?_⟩
      · apply List.map_injective_iff.mpr hf
        rw [List.map_append, List.map_append, List.map_singleton, h_input]
        exact h_split
      ·
        have : List.take (List.length x') (List.map f u) =
            List.map f (List.take x'.length u) := by rw [List.map_take]
        rw [← this, hx', List.take_append_of_le_length] <;> simp
      ·
        replace h_split := congr_arg (fun z => z.drop (x'.length + 1)) h_split
        simp_all [List.drop_append]
    aesop
  use x ++ r.output ++ y
  exact ⟨by simp, by rw [hx]; exact rewrites_of_exists_parts r x y⟩

lemma mem_terminal_of_mem_target {T N : Type} (r : ContextFreeRule T N)
    (u v : List (Symbol T N)) (h : r.Rewrites u v) (a : T) (ha : Symbol.terminal a ∈ v) :
    Symbol.terminal a ∈ u ∨ Symbol.terminal a ∈ r.output := by
  have h_rewrite : ∃ x y : List (Symbol T N),
      u = x ++ [Symbol.nonterminal r.input] ++ y ∧ v = x ++ r.output ++ y := by
    exact exists_parts h
  grind +ring

lemma commute_of_not_mem_output {T N : Type}
    (r1 r2 : ContextFreeRule T N)
    (u v w : List (Symbol T N))
    (h1 : r1.Rewrites u v)
    (h2 : r2.Rewrites v w)
    (h_disjoint : Symbol.nonterminal r2.input ∉ r1.output) :
    ∃ v', r2.Rewrites u v' ∧ r1.Rewrites v' w := by
  revert h1 h2 h_disjoint
  intro h1 h2 h3
  rw [ContextFreeRule.rewrites_iff] at *
  obtain ⟨p1, q1, hp1, hv1⟩ := h1
  obtain ⟨p2, q2, hp2, hw2⟩ := h2
  have h_split :
      ∃ z, p2 = p1 ++ r1.output ++ z ∧ q1 = z ++ [Symbol.nonterminal r2.input] ++ q2 ∨
           p1 = p2 ++ [Symbol.nonterminal r2.input] ++ z ∧ q2 = z ++ r1.output ++ q1 := by
    have h_split : p1 ++ r1.output ++ q1 = p2 ++ Symbol.nonterminal r2.input :: q2 := by
      simpa [List.cons_append] using (show p1 ++ r1.output ++ q1 =
          p2 ++ [Symbol.nonterminal r2.input] ++ q2 by rw [← hv1, hp2])
    have := List.split_commute_of_not_mem p1 q1 p2 q2 r1.output
      (Symbol.nonterminal r2.input) h_split h3
    aesop
  rcases h_split with ⟨z, h | h⟩ <;> simp_all only [List.append_assoc, List.cons_append,
    List.nil_append, rewrites_iff, ↓existsAndEq, and_true]
  · grind
  ·
    exact ⟨p2, z ++ Symbol.nonterminal r1.input :: q1, rfl,
      p2 ++ r2.output ++ z, q1,
      by simp [List.append_assoc], by simp [List.append_assoc]⟩

lemma split_append {T N : Type} (r : ContextFreeRule T N)
    (u v w : List (Symbol T N))
    (h : r.Rewrites (u ++ v) w) :
    (∃ u', r.Rewrites u u' ∧ w = u' ++ v) ∨ (∃ v', r.Rewrites v v' ∧ w = u ++ v') := by
  obtain ⟨s, t, hs, ht⟩ :
      ∃ s t : List (Symbol T N),
        u ++ v = s ++ [Symbol.nonterminal r.input] ++ t ∧ w = s ++ r.output ++ t := by
    exact exists_parts h
  rcases Classical.em (s.length < u.length) with h_cases | h_cases
  ·
    obtain ⟨u', hu'⟩ :
        ∃ u' : List (Symbol T N), u = s ++ [Symbol.nonterminal r.input] ++ u' := by
      rw [List.append_eq_append_iff] at hs
      rcases hs with (⟨as, hs, ht⟩ | ⟨bs, rfl, ht⟩)
      ·
        simp_all only [List.append_assoc]
        replace hs := congr_arg List.length hs
        simp_all +arith
        cases as <;> simp_all +arith
      · exact ⟨bs, rfl⟩
    exact Or.inl ⟨s ++ r.output ++ u', by
      rw [ContextFreeRule.rewrites_iff]
      exact ⟨s, u', hu', rfl⟩, by aesop⟩
  ·
    obtain ⟨s', hs'⟩ : ∃ s', s = u ++ s' := by
      simp only [List.append_assoc, List.singleton_append, not_lt] at hs h_cases
      rw [List.append_eq_append_iff] at hs
      rcases hs with ⟨as, rfl, _⟩ | ⟨bs, rfl, _⟩
      · exact ⟨as, rfl⟩
      ·
        simp only [List.length_append] at h_cases
        have : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
        exact ⟨[], by simp [this]⟩
    simp_all only [List.append_assoc, List.cons_append, List.nil_append,
      List.append_cancel_left_eq, exists_eq_right']
    exact Or.inr <| by
      rw [ContextFreeRule.rewrites_iff]
      aesop

end Rewrites

end ContextFreeRule

namespace ContextFreeGrammar

theorem Derives.distrib_prod {T : Type} {g : ContextFreeGrammar T}
    (S : List (Symbol T g.NT)) (W : List (List (Symbol T g.NT)))
    (h : List.Forall₂ (fun s w => g.Derives [s] w) S W) :
    g.Derives S W.flatten := by
  induction h with
  | nil => constructor
  | @cons s w S W h_sw h_rest ih =>
      have h_trans₁ : g.Derives (s :: S) (w ++ S) := by
        have h_append :
            ∀ {u v : List (Symbol T g.NT)}, g.Derives u v →
            ∀ {S : List (Symbol T g.NT)}, g.Derives (u ++ S) (v ++ S) := by
          intro u v h S
          induction h with
          | refl => exact Relation.ReflTransGen.refl
          | tail _ h_step' ih_inner => exact ih_inner.tail (Produces.append_right h_step' S)
        exact h_append h_sw
      have h_trans₂ : g.Derives (w ++ S) (w ++ W.flatten) := by
        exact append_left ih w
      exact trans h_trans₁ h_trans₂

lemma Produces.split_append {T : Type} {g : ContextFreeGrammar T}
    (u v w : List (Symbol T g.NT))
    (h : g.Produces (u ++ v) w) :
    (∃ u', g.Produces u u' ∧ w = u' ++ v) ∨ (∃ v', g.Produces v v' ∧ w = u ++ v') := by
  obtain ⟨r, hr, h⟩ := h
  have h_split :
      (∃ u', r.Rewrites u u' ∧ w = u' ++ v) ∨
      (∃ v', r.Rewrites v v' ∧ w = u ++ v') := by
    have h_split :
        ∀ r : ContextFreeRule T g.NT, ∀ u v w : List (Symbol T g.NT),
          r.Rewrites (u ++ v) w →
          (∃ u', r.Rewrites u u' ∧ w = u' ++ v) ∨
          (∃ v', r.Rewrites v v' ∧ w = u ++ v') := by
      intros r u v w h
      induction u generalizing v w with
      | nil => aesop
      | cons hd tl ih =>
          cases h with
          | head s => exact Or.inl ⟨r.output ++ tl, by tauto, by simp [List.append_assoc]⟩
          | @cons x _ s₂ h_rec =>
              have ih := ih v s₂ h_rec
              cases ih with
              | inl h_ih =>
                  simp_all only [List.cons_append, List.cons.injEq, true_and]
                  obtain ⟨u', hu', rfl⟩ := h_ih
                  exact Or.inl ⟨hd :: u', by exact ContextFreeRule.Rewrites.cons hd hu', by simp⟩
              | inr h_ih => simp_all
    exact h_split r u v w h
  exact Or.imp
    (fun ⟨u', hu', hw⟩ => ⟨u', ⟨r, hr, hu'⟩, hw⟩)
    (fun ⟨v', hv', hw⟩ => ⟨v', ⟨r, hr, hv'⟩, hw⟩)
    h_split

lemma Derives.split_append {T : Type} {g : ContextFreeGrammar T}
    (u v w : List (Symbol T g.NT))
    (h : g.Derives (u ++ v) w) :
    ∃ u' v', g.Derives u u' ∧ g.Derives v v' ∧ w = u' ++ v' := by
  revert h w u v
  intro u v w h_deriv
  induction h_deriv with
  | refl => exact ⟨u, v, by constructor, by constructor, rfl⟩
  | tail _ h_step ih =>
      obtain ⟨u', v', hu', hv', rfl⟩ := ih
      rcases ContextFreeGrammar.Produces.split_append u' v' _ h_step
        with ⟨u'', hu'', rfl⟩ | ⟨v'', hv'', rfl⟩
      · exact ⟨u'', v', hu'.trans (Relation.ReflTransGen.single hu''), hv', rfl⟩
      · exact ⟨u', v'', hu', hv'.trans (Relation.ReflTransGen.single hv''), rfl⟩

lemma no_rewrites_of_all_terminal {T N : Type} (r : ContextFreeRule T N)
    (w : List T) (v : List (Symbol T N)) :
    ¬ r.Rewrites (w.map Symbol.terminal) v := by
  intro h
  rw [ContextFreeRule.rewrites_iff] at h
  obtain ⟨p, q, hp, _⟩ := h
  have : Symbol.nonterminal r.input ∈ w.map Symbol.terminal := by
    rw [hp]
    simp
  simp at this

lemma no_produces_of_all_terminal {T : Type} (g : ContextFreeGrammar T)
    (w : List T) (v : List (Symbol T g.NT)) :
    ¬ g.Produces (w.map Symbol.terminal) v := by
  rintro ⟨r, _, hr⟩
  exact no_rewrites_of_all_terminal r w v hr

lemma derives_of_all_terminal {T : Type} (g : ContextFreeGrammar T)
    (w : List T) (v : List (Symbol T g.NT)) :
    g.Derives (w.map Symbol.terminal) v → v = w.map Symbol.terminal := by
  intro h
  induction h with
  | refl => rfl
  | tail _ h2 ih =>
      subst ih
      exact absurd h2 (no_produces_of_all_terminal g w _)

private lemma produces_commute_derives_of_not_mem_output {T N : Type}
    {R₁ R₂ : Finset (ContextFreeRule T N)}
    (h : ∀ r₁ ∈ R₁, ∀ r₂ ∈ R₂, Symbol.nonterminal r₂.input ∉ r₁.output)
    (r₁ : ContextFreeRule T N) (hr₁ : r₁ ∈ R₁)
    {u v : List (Symbol T N)} (hrew₁ : r₁.Rewrites u v)
    {w : List (Symbol T N)}
    (h₂ : Relation.ReflTransGen (fun u v => ∃ r ∈ R₂, r.Rewrites u v) v w) :
    ∃ v', Relation.ReflTransGen (fun u v => ∃ r ∈ R₂, r.Rewrites u v) u v' ∧
          ∃ r ∈ R₁, r.Rewrites v' w := by
  induction h₂ with
  | refl => exact ⟨u, Relation.ReflTransGen.refl, r₁, hr₁, hrew₁⟩
  | tail _ hstep ih =>
      obtain ⟨v'', hv''₁, r₁', hr₁', hrew₁'⟩ := ih
      obtain ⟨r₂, hr₂, hrew₂⟩ := hstep
      obtain ⟨x, hrew₂', hrew₁''⟩ :=
        ContextFreeRule.Rewrites.commute_of_not_mem_output r₁' r₂ v'' _ _ hrew₁' hrew₂
          (h r₁' hr₁' r₂ hr₂)
      exact ⟨x, hv''₁.tail ⟨r₂, hr₂, hrew₂'⟩, r₁', hr₁', hrew₁''⟩

theorem derives_commute_of_not_mem_output {T N : Type}
    {R₁ R₂ : Finset (ContextFreeRule T N)}
    (h : ∀ r₁ ∈ R₁, ∀ r₂ ∈ R₂, Symbol.nonterminal r₂.input ∉ r₁.output)
    {u v w : List (Symbol T N)}
    (h₁ : Relation.ReflTransGen (fun u v => ∃ r ∈ R₁, r.Rewrites u v) u v)
    (h₂ : Relation.ReflTransGen (fun u v => ∃ r ∈ R₂, r.Rewrites u v) v w) :
    ∃ v',
      Relation.ReflTransGen (fun u v => ∃ r ∈ R₂, r.Rewrites u v) u v' ∧
      Relation.ReflTransGen (fun u v => ∃ r ∈ R₁, r.Rewrites u v) v' w := by
  induction h₁ generalizing w with
  | refl => exact ⟨w, h₂, Relation.ReflTransGen.refl⟩
  | tail _ hstep ih =>
      obtain ⟨r_step, hr_step, hrew_step⟩ := hstep
      obtain ⟨v', hv'₁, r', hr', hrew'⟩ :=
        produces_commute_derives_of_not_mem_output h r_step hr_step hrew_step h₂
      obtain ⟨x, hx₁, hx₂⟩ := ih hv'₁
      exact ⟨x, hx₁, hx₂.tail ⟨r', hr', hrew'⟩⟩

end ContextFreeGrammar

namespace Language

theorem mem_list_prod_iff_forall2 (S : List (Language α)) (w : List α) :
    w ∈ S.prod ↔ ∃ W : List (List α), w = W.flatten ∧ List.Forall₂ (fun w s => w ∈ s) W S := by
  induction S generalizing w with
  | nil => simp
  | cons s S ih =>
      constructor
      ·
        rintro ⟨u, hu, v, hv, rfl⟩
        obtain ⟨W, rfl, hW⟩ := (ih v).mp hv
        use u :: W
        aesop
      ·
        rintro ⟨_ | ⟨w, W⟩, rfl, h⟩
        · simp at h
        ·
          rw [List.forall₂_cons] at h
          exact ⟨w, h.1, W.flatten, (ih _).mpr ⟨W, rfl, h.2⟩, rfl⟩

def subst {α β : Type} (L : Language α) (f : α → Language β) : Language β :=
  {u | ∃ w ∈ L, u ∈ (w.map f).prod}

theorem subst_pair_eq_mul {β : Type} (f : Bool → Language β) :
    ({[false, true]} : Language Bool).subst f = f false * f true := by
  apply Set.ext
  intro u
  simp only [subst, Set.mem_setOf_eq, Language.mul_def, Set.mem_image2]
  simp only [List.prod]
  constructor
  ·
    simp [Language.mul_def, Language.one_def] at *
    grind
  ·
    intro h
    obtain ⟨a, ha, b, hb, hab⟩ := h
    use [false, true]
    constructor
    · exact rfl
    ·
      simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, mul_one]
      exact ⟨a, ha, b, hb, hab⟩

theorem subst_singletons_eq_add {β : Type}
    (f : Bool → Language β) :
    ({[false], [true]} : Language Bool).subst f = f false + f true := by
  ext u
  constructor
  ·
    rintro ⟨w, hw, hu⟩
    simp only [mem_add]
    rcases hw with (rfl | rfl) <;> simp_all
  ·
    intro hu
    rcases hu with hu_false | hu_true
    ·
      refine ⟨[false], by tauto, ?_⟩
      simpa [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    ·
      refine ⟨[true], by tauto, ?_⟩
      simpa [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]

theorem subst_univ_unit_eq_kstar {β : Type} (f : Unit → Language β) :
    Language.subst (Set.univ : Language Unit) f = KStar.kstar (f ()) := by
  ext u
  constructor
  ·
    rintro ⟨w, hw, hu⟩
    induction w generalizing u with
    | nil => exact ⟨[], by simpa using hu⟩
    | cons _ _ ih =>
        rcases hu with ⟨u₁, hu₁, u₂, hu₂, rfl⟩
        obtain ⟨L, hL₁, hL₂⟩ := ih u₂ (Set.mem_univ _) hu₂
        exact ⟨[u₁] ++ L, by aesop⟩
  ·
    rintro ⟨L, rfl, hL⟩
    use List.replicate L.length ()
    induction L with
    | nil => trivial
    | cons _ tail ih =>
        have ih' := ih (List.forall_mem_cons.mp hL).2
        refine ⟨Set.mem_univ _, ?_⟩
        simpa [List.replicate_succ, List.prod_cons, List.prod_nil, mul_one] using
          (Set.mem_image2_of_mem (List.forall_mem_cons.mp hL).1 ih'.2)

end Language
