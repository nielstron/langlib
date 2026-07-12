module

public import Langlib.Grammars.Indexed.Definition
import Mathlib.Tactic

@[expose]
public section

/-!
# Counted derivations for indexed normal form

Exact-step derivations, append splitting, terminal-source rigidity, and the four normal-form
rule cases used to turn derivations into data-carrying parse certificates.
-/

variable {T : Type}

namespace IndexedGrammar

/-! ## Minimal sentential counting support -/

private def ISym.isIndexed {g : IndexedGrammar T} : g.ISym → Bool
  | ISym.terminal _ => false
  | ISym.indexed _ _ => true

private def sententialNonterminalCount {g : IndexedGrammar T} (w : List g.ISym) : ℕ :=
  w.countP ISym.isIndexed

@[simp] private theorem ISym.isIndexed_terminal {g : IndexedGrammar T} (a : T) :
    ISym.isIndexed (g := g) (ISym.terminal a) = false := rfl

@[simp] private theorem ISym.isIndexed_indexed {g : IndexedGrammar T} (A : g.nt)
    (σ : List g.flag) :
    ISym.isIndexed (g := g) (ISym.indexed A σ) = true := rfl

@[simp] private theorem sententialNonterminalCount_append {g : IndexedGrammar T}
    (u v : List g.ISym) :
    sententialNonterminalCount (u ++ v) =
      sententialNonterminalCount u + sententialNonterminalCount v := by
  simp [sententialNonterminalCount, List.countP_append]

@[simp] private theorem sententialNonterminalCount_cons_indexed {g : IndexedGrammar T}
    (A : g.nt) (σ : List g.flag) (w : List g.ISym) :
    sententialNonterminalCount (ISym.indexed A σ :: w) =
      sententialNonterminalCount w + 1 := by
  simp [sententialNonterminalCount]

/-! ## Counted derivations -/

/-- `DerivesIn g n w₁ w₂` means that `w₁` derives `w₂` in exactly `n` indexed-grammar
steps. This is a counted counterpart to `Derives`, useful when extracting minimal accepting
derivations. -/
def DerivesIn (g : IndexedGrammar T) : ℕ → List g.ISym → List g.ISym → Prop
  | 0, w₁, w₂ => w₁ = w₂
  | n + 1, w₁, w₂ => ∃ w, DerivesIn g n w₁ w ∧ g.Transforms w w₂

@[simp] theorem derivesIn_zero {g : IndexedGrammar T} {w₁ w₂ : List g.ISym} :
    g.DerivesIn 0 w₁ w₂ ↔ w₁ = w₂ :=
  Iff.rfl

@[simp] theorem derivesIn_succ {g : IndexedGrammar T} {n : ℕ}
    {w₁ w₂ : List g.ISym} :
    g.DerivesIn (n + 1) w₁ w₂ ↔
      ∃ w, g.DerivesIn n w₁ w ∧ g.Transforms w w₂ :=
  Iff.rfl

theorem derivesIn_one_of_transforms {g : IndexedGrammar T}
    {w₁ w₂ : List g.ISym} (h : g.Transforms w₁ w₂) :
    g.DerivesIn 1 w₁ w₂ :=
  ⟨w₁, rfl, h⟩

theorem derives_of_derivesIn {g : IndexedGrammar T} {n : ℕ}
    {w₁ w₂ : List g.ISym} (h : g.DerivesIn n w₁ w₂) :
    g.Derives w₁ w₂ := by
  induction n generalizing w₂ with
  | zero =>
      have hw : w₁ = w₂ := by simpa using h
      subst w₂
      exact g.deri_self w₁
  | succ n ih =>
      rcases h with ⟨w, hprev, hstep⟩
      exact (ih hprev).tail hstep

theorem exists_derivesIn_of_derives {g : IndexedGrammar T}
    {w₁ w₂ : List g.ISym} (h : g.Derives w₁ w₂) :
    ∃ n, g.DerivesIn n w₁ w₂ := by
  induction h with
  | refl =>
      exact ⟨0, rfl⟩
  | tail _ hstep ih =>
      rcases ih with ⟨n, hn⟩
      exact ⟨n + 1, ⟨_, hn, hstep⟩⟩

theorem derives_iff_exists_derivesIn {g : IndexedGrammar T}
    {w₁ w₂ : List g.ISym} :
    g.Derives w₁ w₂ ↔ ∃ n, g.DerivesIn n w₁ w₂ := by
  constructor
  · exact exists_derivesIn_of_derives
  · rintro ⟨n, h⟩
    exact derives_of_derivesIn h

theorem derivesIn_trans {g : IndexedGrammar T} {m n : ℕ}
    {w₁ w₂ w₃ : List g.ISym}
    (h₁ : g.DerivesIn m w₁ w₂) (h₂ : g.DerivesIn n w₂ w₃) :
    g.DerivesIn (m + n) w₁ w₃ := by
  induction n generalizing w₃ with
  | zero =>
      have hw : w₂ = w₃ := by simpa using h₂
      subst w₃
      simpa using h₁
  | succ n ih =>
      rcases h₂ with ⟨w, hprev, hstep⟩
      exact ⟨w, by simpa [Nat.add_assoc] using ih hprev, hstep⟩

/-- Split a counted derivation after `m` steps. -/
theorem derivesIn_split {g : IndexedGrammar T} {m n : ℕ}
    {w₁ w₃ : List g.ISym}
    (h : g.DerivesIn (m + n) w₁ w₃) :
    ∃ w₂, g.DerivesIn m w₁ w₂ ∧ g.DerivesIn n w₂ w₃ := by
  induction n generalizing w₃ with
  | zero =>
      exact ⟨w₃, by simpa using h, rfl⟩
  | succ n ih =>
      rcases (show g.DerivesIn ((m + n) + 1) w₁ w₃ by
        simpa [Nat.add_assoc] using h) with ⟨w, hprev, hstep⟩
      rcases ih hprev with ⟨w₂, hm, hn⟩
      exact ⟨w₂, hm, ⟨w, hn, hstep⟩⟩

/-- Split a counted derivation at any index `i ≤ n`. -/
theorem generates_iff_exists_derivesIn (g : IndexedGrammar T) (w : List T) :
    g.Generates w ↔
      ∃ n, g.DerivesIn n [ISym.indexed g.initial []] (w.map ISym.terminal) := by
  rw [Generates, derives_iff_exists_derivesIn]

/-! ## Append splitting -/

/-- A one-step indexed rewrite remains valid after appending an unchanged right context. -/
theorem transforms_append_left {g : IndexedGrammar T} {u u' : List g.ISym}
    (h : g.Transforms u u') (v : List g.ISym) :
    g.Transforms (u ++ v) (u' ++ v) := by
  rcases h with ⟨r, p, q, σ, hr, hw₁, hw₂⟩
  refine ⟨r, p, q ++ v, σ, hr, ?_, ?_⟩
  · cases hc : r.consume with
    | none =>
        rw [hc] at hw₁
        simp [hw₁, List.append_assoc]
    | some f =>
        rw [hc] at hw₁
        simp [hw₁, List.append_assoc]
  · rw [hw₂]
    simp [List.append_assoc]

/-- A one-step indexed rewrite remains valid after prepending an unchanged left context. -/
theorem transforms_append_right {g : IndexedGrammar T} {v v' : List g.ISym}
    (h : g.Transforms v v') (u : List g.ISym) :
    g.Transforms (u ++ v) (u ++ v') := by
  rcases h with ⟨r, p, q, σ, hr, hw₁, hw₂⟩
  refine ⟨r, u ++ p, q, σ, hr, ?_, ?_⟩
  · cases hc : r.consume with
    | none =>
        rw [hc] at hw₁
        simp [hw₁, List.append_assoc]
    | some f =>
        rw [hc] at hw₁
        simp [hw₁, List.append_assoc]
  · rw [hw₂]
    simp [List.append_assoc]

/-- Counted indexed derivations are closed under appending an unchanged right context. -/
theorem derivesIn_append_left {g : IndexedGrammar T} {n : ℕ}
    {u u' : List g.ISym}
    (h : g.DerivesIn n u u') (v : List g.ISym) :
    g.DerivesIn n (u ++ v) (u' ++ v) := by
  induction n generalizing u' with
  | zero =>
      have hu : u = u' := by simpa using h
      subst u'
      rfl
  | succ n ih =>
      rcases h with ⟨w, hprev, hstep⟩
      exact ⟨w ++ v, ih hprev, transforms_append_left hstep v⟩

/-- Counted indexed derivations are closed under prepending an unchanged left context. -/
theorem derivesIn_append_right {g : IndexedGrammar T} {n : ℕ}
    {v v' : List g.ISym}
    (h : g.DerivesIn n v v') (u : List g.ISym) :
    g.DerivesIn n (u ++ v) (u ++ v') := by
  induction n generalizing v' with
  | zero =>
      have hv : v = v' := by simpa using h
      subst v'
      rfl
  | succ n ih =>
      rcases h with ⟨w, hprev, hstep⟩
      exact ⟨u ++ w, ih hprev, transforms_append_right hstep u⟩

/-- Independent counted indexed derivations compose over append. -/
theorem derivesIn_append {g : IndexedGrammar T} {m n : ℕ}
    {u u' v v' : List g.ISym}
    (hu : g.DerivesIn m u u') (hv : g.DerivesIn n v v') :
    g.DerivesIn (m + n) (u ++ v) (u' ++ v') :=
  derivesIn_trans (derivesIn_append_left hu v) (derivesIn_append_right hv u')

/-- Counted terminal-word composition over append. -/
theorem derivesIn_append_to_terminals_of_derivesIn {g : IndexedGrammar T}
    {m n : ℕ} {u v : List g.ISym} {wu wv : List T}
    (hu : g.DerivesIn m u (wu.map fun a => (ISym.terminal a : g.ISym)))
    (hv : g.DerivesIn n v (wv.map fun a => (ISym.terminal a : g.ISym))) :
    g.DerivesIn (m + n) (u ++ v)
      ((wu ++ wv).map fun a => (ISym.terminal a : g.ISym)) := by
  simpa [List.map_append] using derivesIn_append hu hv

/-- There is no indexed-grammar rewrite step whose source sentential form is empty. -/
theorem not_transforms_nil {g : IndexedGrammar T} {w : List g.ISym} :
    ¬ g.Transforms ([] : List g.ISym) w := by
  rintro ⟨r, u, v, σ, _hr, hsource, _htarget⟩
  cases hc : r.consume with
  | none =>
      rw [hc] at hsource
      simp at hsource
  | some f =>
      rw [hc] at hsource
      simp at hsource

/-- A counted derivation starting from the empty sentential form is necessarily the
zero-step derivation to the empty sentential form. -/
theorem derivesIn_nil_left_eq {g : IndexedGrammar T} {n : ℕ} {w : List g.ISym}
    (h : g.DerivesIn n ([] : List g.ISym) w) : n = 0 ∧ w = [] := by
  induction n generalizing w with
  | zero =>
      have hw : ([] : List g.ISym) = w := by
        simpa using h
      exact ⟨rfl, hw.symm⟩
  | succ n ih =>
      rcases h with ⟨x, hprev, hstep⟩
      obtain ⟨_hn, hx⟩ := ih hprev
      rw [hx] at hstep
      exact False.elim (not_transforms_nil (g := g) hstep)

theorem derivesIn_pair_to_terminals_of_derivesIn {g : IndexedGrammar T}
    {m n : ℕ} {A B : g.nt} {σ τ : List g.flag} {u v : List T}
    (hleft : g.DerivesIn m [ISym.indexed A σ]
      (u.map fun a => (ISym.terminal a : g.ISym)))
    (hright : g.DerivesIn n [ISym.indexed B τ]
      (v.map fun a => (ISym.terminal a : g.ISym))) :
    g.DerivesIn (m + n) [ISym.indexed A σ, ISym.indexed B τ]
      ((u ++ v).map fun a => (ISym.terminal a : g.ISym)) := by
  simpa using
    derivesIn_append_to_terminals_of_derivesIn (g := g)
      (u := [ISym.indexed A σ]) (v := [ISym.indexed B τ])
      hleft hright

/-- A one-step indexed rewrite of an appended sentential form rewrites either the left side
or the right side of the append. -/
theorem transforms_append_cases_of_append {g : IndexedGrammar T} {u v w : List g.ISym}
    (hstep : g.Transforms (u ++ v) w) :
    (∃ u', g.Transforms u u' ∧ w = u' ++ v) ∨
      (∃ v', g.Transforms v v' ∧ w = u ++ v') := by
  rcases hstep with ⟨r, p, q, σ, hr, hw₁, hw₂⟩
  subst w
  cases hc : r.consume with
  | none =>
      rw [hc] at hw₁
      have hsplit : u ++ v = p ++ ([ISym.indexed r.lhs σ] ++ q) := by
        simpa [List.append_assoc] using hw₁
      rw [List.append_eq_append_iff] at hsplit
      rcases hsplit with ⟨as, hp, hv⟩ | ⟨bs, hu, htail⟩
      · right
        refine ⟨as ++ g.expandRhs r.rhs σ ++ q, ?_, ?_⟩
        · refine ⟨r, as, q, σ, hr, ?_, rfl⟩
          rw [hc]
          simpa [List.append_assoc] using hv
        · rw [hp]
          simp [List.append_assoc]
      · cases bs with
        | nil =>
            right
            refine ⟨g.expandRhs r.rhs σ ++ q, ?_, ?_⟩
            · refine ⟨r, [], q, σ, hr, ?_, rfl⟩
              rw [hc]
              simpa using htail.symm
            · rw [hu]
              simp [List.append_assoc]
        | cons b bs =>
            simp at htail
            rcases htail with ⟨rfl, hq⟩
            left
            refine ⟨p ++ g.expandRhs r.rhs σ ++ bs, ?_, ?_⟩
            · refine ⟨r, p, bs, σ, hr, ?_, rfl⟩
              rw [hc]
              rw [hu]
              simp [List.append_assoc]
            · rw [hq]
              simp [List.append_assoc]
  | some f =>
      rw [hc] at hw₁
      have hsplit : u ++ v = p ++ ([ISym.indexed r.lhs (f :: σ)] ++ q) := by
        simpa [List.append_assoc] using hw₁
      rw [List.append_eq_append_iff] at hsplit
      rcases hsplit with ⟨as, hp, hv⟩ | ⟨bs, hu, htail⟩
      · right
        refine ⟨as ++ g.expandRhs r.rhs σ ++ q, ?_, ?_⟩
        · refine ⟨r, as, q, σ, hr, ?_, rfl⟩
          rw [hc]
          simpa [List.append_assoc] using hv
        · rw [hp]
          simp [List.append_assoc]
      · cases bs with
        | nil =>
            right
            refine ⟨g.expandRhs r.rhs σ ++ q, ?_, ?_⟩
            · refine ⟨r, [], q, σ, hr, ?_, rfl⟩
              rw [hc]
              simpa using htail.symm
            · rw [hu]
              simp [List.append_assoc]
        | cons b bs =>
            simp at htail
            rcases htail with ⟨rfl, hq⟩
            left
            refine ⟨p ++ g.expandRhs r.rhs σ ++ bs, ?_, ?_⟩
            · refine ⟨r, p, bs, σ, hr, ?_, rfl⟩
              rw [hc]
              rw [hu]
              simp [List.append_assoc]
            · rw [hq]
              simp [List.append_assoc]

/-- A counted derivation from an appended sentential form can be factored into counted
derivations from the two sides of the append. The two side budgets add up to the original
budget. -/
theorem derivesIn_append_split {g : IndexedGrammar T} {n : ℕ}
    {u v x : List g.ISym}
    (hder : g.DerivesIn n (u ++ v) x) :
    ∃ m k : ℕ, ∃ u' v' : List g.ISym,
      m + k = n ∧
        x = u' ++ v' ∧
        g.DerivesIn m u u' ∧
        g.DerivesIn k v v' := by
  induction n generalizing x with
  | zero =>
      have hx : u ++ v = x := by simpa using hder
      subst x
      exact ⟨0, 0, u, v, rfl, rfl, rfl, rfl⟩
  | succ n ih =>
      rcases hder with ⟨y, hprev, hstep⟩
      rcases ih hprev with ⟨m, k, u', v', hmk, hy, hu, hv⟩
      subst y
      rcases transforms_append_cases_of_append hstep with hleft | hright
      · rcases hleft with ⟨u'', hstepLeft, hx⟩
        refine ⟨m + 1, k, u'', v', ?_, hx, ?_, hv⟩
        · omega
        · exact ⟨u', hu, hstepLeft⟩
      · rcases hright with ⟨v'', hstepRight, hx⟩
        refine ⟨m, k + 1, u', v'', ?_, hx, hu, ?_⟩
        · omega
        · exact ⟨v', hv, hstepRight⟩

theorem append_eq_map_terminal_split {g : IndexedGrammar T}
    {u v : List g.ISym} {w : List T}
    (h : u ++ v = (w.map fun a => (ISym.terminal a : g.ISym))) :
    ∃ wu wv : List T,
      w = wu ++ wv ∧
        u = (wu.map fun a => (ISym.terminal a : g.ISym)) ∧
        v = (wv.map fun a => (ISym.terminal a : g.ISym)) := by
  induction u generalizing w with
  | nil =>
      refine ⟨[], w, by simp, rfl, ?_⟩
      simpa using h
  | cons s u ih =>
      cases w with
      | nil =>
          simp at h
      | cons a w =>
          simp only [List.map_cons, List.cons_append, List.cons.injEq] at h
          rcases h with ⟨hs, htail⟩
          subst s
          rcases ih htail with ⟨wu, wv, hw, hu, hv⟩
          refine ⟨a :: wu, wv, ?_, ?_, hv⟩
          · simp [hw]
          · simp [hu]

theorem derives_append_to_terminals_split {g : IndexedGrammar T}
    {u v : List g.ISym} {w : List T}
    (hder : g.Derives (u ++ v) (w.map fun a => (ISym.terminal a : g.ISym))) :
    ∃ wu wv : List T,
      w = wu ++ wv ∧
        g.Derives u (wu.map fun a => (ISym.terminal a : g.ISym)) ∧
        g.Derives v (wv.map fun a => (ISym.terminal a : g.ISym)) := by
  have haux :
      ∀ {x : List g.ISym},
        g.Derives x (w.map fun a => (ISym.terminal a : g.ISym)) →
        ∀ {u v : List g.ISym}, x = u ++ v →
          ∃ wu wv : List T,
            w = wu ++ wv ∧
              g.Derives u (wu.map fun a => (ISym.terminal a : g.ISym)) ∧
              g.Derives v (wv.map fun a => (ISym.terminal a : g.ISym)) := by
    intro x h
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl =>
        intro u v hx
        rcases append_eq_map_terminal_split (g := g) hx.symm with ⟨wu, wv, hw, hu, hv⟩
        subst u
        subst v
        exact ⟨wu, wv, hw, g.deri_self _, g.deri_self _⟩
    | @head a c hstep hrest ih =>
        intro u v hx
        subst a
        rcases transforms_append_cases_of_append hstep with hleft | hright
        · rcases hleft with ⟨u', hu', hc⟩
          rcases ih hc with ⟨wu, wv, hw, huder, hvder⟩
          exact ⟨wu, wv, hw, (deri_of_tran hu').trans huder, hvder⟩
        · rcases hright with ⟨v', hv', hc⟩
          rcases ih hc with ⟨wu, wv, hw, huder, hvder⟩
          exact ⟨wu, wv, hw, huder, (deri_of_tran hv').trans hvder⟩
  exact haux hder rfl

/-- Counted split of an appended terminal derivation. -/
theorem derivesIn_append_to_terminals_split {g : IndexedGrammar T} {n : ℕ}
    {u v : List g.ISym} {w : List T}
    (hder : g.DerivesIn n (u ++ v)
      (w.map fun a => (ISym.terminal a : g.ISym))) :
    ∃ m k : ℕ, ∃ wu wv : List T,
      m + k = n ∧
        w = wu ++ wv ∧
        g.DerivesIn m u (wu.map fun a => (ISym.terminal a : g.ISym)) ∧
        g.DerivesIn k v (wv.map fun a => (ISym.terminal a : g.ISym)) := by
  rcases derivesIn_append_split (g := g) hder with ⟨m, k, u', v', hmk, hx, hu, hv⟩
  rcases append_eq_map_terminal_split (g := g) hx.symm with
    ⟨wu, wv, hw, hu', hv'⟩
  subst u'
  subst v'
  exact ⟨m, k, wu, wv, hmk, hw, hu, hv⟩

/-- Counted split for the pair produced by a normal-form binary branch. -/
theorem derivesIn_pair_to_terminals_split {g : IndexedGrammar T} {n : ℕ}
    {A B : g.nt} {σ τ : List g.flag} {w : List T}
    (hder : g.DerivesIn n [ISym.indexed A σ, ISym.indexed B τ]
      (w.map fun a => (ISym.terminal a : g.ISym))) :
    ∃ m k : ℕ, ∃ u v : List T,
      m + k = n ∧
        w = u ++ v ∧
        g.DerivesIn m [ISym.indexed A σ]
          (u.map fun a => (ISym.terminal a : g.ISym)) ∧
        g.DerivesIn k [ISym.indexed B τ]
          (v.map fun a => (ISym.terminal a : g.ISym)) := by
  simpa using
    derivesIn_append_to_terminals_split (g := g)
      (u := [ISym.indexed A σ]) (v := [ISym.indexed B τ]) (w := w) hder

theorem not_transforms_from_terminals {g : IndexedGrammar T}
    {w : List T} {x : List g.ISym} :
    ¬ g.Transforms (w.map fun a => (ISym.terminal a : g.ISym)) x := by
  intro h
  rcases h with ⟨r, u, v, σ, _hr, hw₁, _hw₂⟩
  have hcount :
      sententialNonterminalCount (w.map fun a => (ISym.terminal a : g.ISym)) = 0 := by
    simp [sententialNonterminalCount]
  cases hc : r.consume with
  | none =>
      rw [hc] at hw₁
      rw [hw₁] at hcount
      simp [List.append_assoc] at hcount
  | some f =>
      rw [hc] at hw₁
      rw [hw₁] at hcount
      simp [List.append_assoc] at hcount

theorem derives_from_terminals_eq {g : IndexedGrammar T}
    {u : List T} {w : List g.ISym}
    (hder : g.Derives (u.map fun a => (ISym.terminal a : g.ISym)) w) :
    w = u.map fun a => (ISym.terminal a : g.ISym) := by
  induction hder with
  | refl =>
      rfl
  | tail _ hstep ih =>
      rw [ih] at hstep
      exact False.elim (not_transforms_from_terminals hstep)

theorem derives_terminals_inj {g : IndexedGrammar T}
    {u w : List T}
    (hder : g.Derives (u.map fun a => (ISym.terminal a : g.ISym))
      (w.map fun a => (ISym.terminal a : g.ISym))) :
    w = u := by
  have h := derives_from_terminals_eq (g := g) hder
  have hmap : w.map (fun a => (ISym.terminal a : g.ISym)) =
      u.map fun a => (ISym.terminal a : g.ISym) := h
  exact (Function.Injective.list_map (fun a b hab => by simpa using hab)) hmap

theorem derives_terminal_singleton_eq {g : IndexedGrammar T}
    {a : T} {w : List T}
    (hder : g.Derives [ISym.terminal a]
      (w.map fun b => (ISym.terminal b : g.ISym))) :
    w = [a] := by
  simpa using
    derives_terminals_inj (g := g) (u := [a]) (w := w) hder

theorem derivesIn_from_terminals_eq {g : IndexedGrammar T}
    {n : ℕ} {u : List T} {w : List g.ISym}
    (hder : g.DerivesIn n
      (u.map fun a => (ISym.terminal a : g.ISym)) w) :
    w = u.map fun a => (ISym.terminal a : g.ISym) :=
  derives_from_terminals_eq (g := g) (derives_of_derivesIn hder)

theorem not_derivesIn_succ_from_terminals {g : IndexedGrammar T}
    {n : ℕ} {u : List T} {w : List g.ISym} :
    ¬ g.DerivesIn (n + 1)
      (u.map fun a => (ISym.terminal a : g.ISym)) w := by
  intro hder
  rcases hder with ⟨x, hprev, hstep⟩
  have hx := derivesIn_from_terminals_eq (g := g) hprev
  subst x
  exact not_transforms_from_terminals hstep

theorem derivesIn_terminal_singleton_eq {g : IndexedGrammar T}
    {n : ℕ} {a : T} {w : List T}
    (hder : g.DerivesIn n [ISym.terminal a]
      (w.map fun b => (ISym.terminal b : g.ISym))) :
    w = [a] := by
  exact derives_terminal_singleton_eq (g := g) (derives_of_derivesIn hder)

theorem derivesIn_terminal_singleton_steps_eq_zero {g : IndexedGrammar T}
    {n : ℕ} {a : T} {w : List T}
    (hder : g.DerivesIn n [ISym.terminal a]
      (w.map fun b => (ISym.terminal b : g.ISym))) :
    n = 0 := by
  cases n with
  | zero => rfl
  | succ n =>
      exact False.elim
        (not_derivesIn_succ_from_terminals (g := g) (n := n) (u := [a]) hder)


/-! ## Normal-form rule decomposition -/

def TransformIsBinaryStep (g : IndexedGrammar T)
    (w₁ w₂ : List g.ISym) : Prop :=
  ∃ A B C : g.nt, ∃ u v : List g.ISym, ∃ σ : List g.flag,
    B ≠ g.initial ∧ C ≠ g.initial ∧
      w₁ = u ++ [ISym.indexed A σ] ++ v ∧
      w₂ = u ++ [ISym.indexed B σ, ISym.indexed C σ] ++ v

/-- A normal-form flag-pop step `A[f :: σ] ↦ B[σ]`. -/
def TransformIsPopStep (g : IndexedGrammar T)
    (w₁ w₂ : List g.ISym) : Prop :=
  ∃ A B : g.nt, ∃ f : g.flag, ∃ u v : List g.ISym, ∃ σ : List g.flag,
    B ≠ g.initial ∧
      w₁ = u ++ [ISym.indexed A (f :: σ)] ++ v ∧
      w₂ = u ++ [ISym.indexed B σ] ++ v

/-- A normal-form flag-push step `A[σ] ↦ B[f :: σ]`. -/
def TransformIsPushStep (g : IndexedGrammar T)
    (w₁ w₂ : List g.ISym) : Prop :=
  ∃ A B : g.nt, ∃ f : g.flag, ∃ u v : List g.ISym, ∃ σ : List g.flag,
    B ≠ g.initial ∧
      w₁ = u ++ [ISym.indexed A σ] ++ v ∧
      w₂ = u ++ [ISym.indexed B (f :: σ)] ++ v

/-- A normal-form terminal-emission step `A[σ] ↦ a`. -/
def TransformIsTerminalStep (g : IndexedGrammar T)
    (w₁ w₂ : List g.ISym) : Prop :=
  ∃ A : g.nt, ∃ a : T, ∃ u v : List g.ISym, ∃ σ : List g.flag,
    w₁ = u ++ [ISym.indexed A σ] ++ v ∧
      w₂ = u ++ [ISym.terminal a] ++ v

/-- A one-step rewrite in normal form has exactly one of the four indexed-normal-form
shapes: binary split, flag pop, flag push, or terminal emission. -/
theorem transforms_cases_of_isNormalForm {g : IndexedGrammar T}
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {w₁ w₂ : List g.ISym} (h : g.Transforms w₁ w₂) :
    (∃ A B C : g.nt, ∃ u v : List g.ISym, ∃ σ : List g.flag,
      B ≠ g.initial ∧ C ≠ g.initial ∧
      w₁ = u ++ [ISym.indexed A σ] ++ v ∧
      w₂ = u ++ [ISym.indexed B σ, ISym.indexed C σ] ++ v) ∨
    (∃ A B : g.nt, ∃ f : g.flag, ∃ u v : List g.ISym, ∃ σ : List g.flag,
      B ≠ g.initial ∧
      w₁ = u ++ [ISym.indexed A (f :: σ)] ++ v ∧
      w₂ = u ++ [ISym.indexed B σ] ++ v) ∨
    (∃ A B : g.nt, ∃ f : g.flag, ∃ u v : List g.ISym, ∃ σ : List g.flag,
      B ≠ g.initial ∧
      w₁ = u ++ [ISym.indexed A σ] ++ v ∧
      w₂ = u ++ [ISym.indexed B (f :: σ)] ++ v) ∨
    (∃ A : g.nt, ∃ a : T, ∃ u v : List g.ISym, ∃ σ : List g.flag,
      w₁ = u ++ [ISym.indexed A σ] ++ v ∧
      w₂ = u ++ [ISym.terminal a] ++ v) := by
  rcases h with ⟨r, u, v, σ, hr, hw₁, hw₂⟩
  rcases hNF r hr with hbin | hpop | hpush | hterm
  · rcases hbin with ⟨hc, B, C, hrhs, hB, hC⟩
    left
    refine ⟨r.lhs, B, C, u, v, σ, hB, hC, ?_, ?_⟩
    · simpa [hc] using hw₁
    · rw [hw₂, hrhs]
      simp [expandRhs]
  · rcases hpop with ⟨f, hc, B, hrhs, hB⟩
    right
    left
    refine ⟨r.lhs, B, f, u, v, σ, hB, ?_, ?_⟩
    · simpa [hc] using hw₁
    · rw [hw₂, hrhs]
      simp [expandRhs]
  · rcases hpush with ⟨hc, B, f, hrhs, hB⟩
    right
    right
    left
    refine ⟨r.lhs, B, f, u, v, σ, hB, ?_, ?_⟩
    · simpa [hc] using hw₁
    · rw [hw₂, hrhs]
      simp [expandRhs]
  · rcases hterm with ⟨hc, a, hrhs⟩
    right
    right
    right
    refine ⟨r.lhs, a, u, v, σ, ?_, ?_⟩
    · simpa [hc] using hw₁
    · rw [hw₂, hrhs]
      simp [expandRhs]

theorem transforms_kind_cases_of_isNormalForm {g : IndexedGrammar T}
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {w₁ w₂ : List g.ISym} (h : g.Transforms w₁ w₂) :
    TransformIsBinaryStep g w₁ w₂ ∨
      TransformIsPopStep g w₁ w₂ ∨
      TransformIsPushStep g w₁ w₂ ∨
      TransformIsTerminalStep g w₁ w₂ := by
  simpa [TransformIsBinaryStep, TransformIsPopStep, TransformIsPushStep,
    TransformIsTerminalStep] using transforms_cases_of_isNormalForm hNF h

/-- A singleton indexed symbol can only match a one-rule redex with empty context. -/
private theorem singleton_indexed_eq_context_bounds {g : IndexedGrammar T}
    {A B : g.nt} {σ τ : List g.flag} {u v : List g.ISym}
    (h : [ISym.indexed A σ] = u ++ [ISym.indexed B τ] ++ v) :
    u = [] ∧ v = [] ∧ A = B ∧ σ = τ := by
  have hu : u = [] := by
    cases u with
    | nil => rfl
    | cons x xs =>
        have hlen := congrArg List.length h
        simp at hlen
  subst u
  have h' : [ISym.indexed A σ] = ISym.indexed B τ :: v := by
    simpa using h
  simp at h'
  rcases h' with ⟨⟨hA, hσ⟩, hv⟩
  exact ⟨rfl, hv, hA, hσ⟩

theorem transforms_singleton_binary_iff_rule_of_isNormalForm {g : IndexedGrammar T}
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {A B C : g.nt} {σ : List g.flag} :
    g.Transforms [ISym.indexed A σ] [ISym.indexed B σ, ISym.indexed C σ] ↔
      ∃ r ∈ g.rules,
        r.lhs = A ∧ r.consume = none ∧
          r.rhs = [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none] := by
  constructor
  · intro hstep
    rcases hstep with ⟨r, u, v, τ, hr, hw₁, hw₂⟩
    rcases hNF r hr with hbin | hpop | hpush | hterm
    · rcases hbin with ⟨hc, B₀, C₀, hrhs, _hB₀, _hC₀⟩
      rw [hc] at hw₁
      rcases singleton_indexed_eq_context_bounds hw₁ with ⟨hu, hv, hA, hτ⟩
      subst u
      subst v
      subst τ
      rw [hrhs] at hw₂
      simp [expandRhs] at hw₂
      rcases hw₂ with ⟨hB, hC⟩
      subst B₀
      subst C₀
      exact ⟨r, hr, hA.symm, hc, hrhs⟩
    · rcases hpop with ⟨f, hc, B₀, hrhs, _hB₀⟩
      rw [hc] at hw₁
      rcases singleton_indexed_eq_context_bounds hw₁ with ⟨hu, hv, _hA, _hτ⟩
      subst u
      subst v
      rw [hrhs] at hw₂
      simp [expandRhs] at hw₂
    · rcases hpush with ⟨hc, B₀, f, hrhs, _hB₀⟩
      rw [hc] at hw₁
      rcases singleton_indexed_eq_context_bounds hw₁ with ⟨hu, hv, _hA, _hτ⟩
      subst u
      subst v
      rw [hrhs] at hw₂
      simp [expandRhs] at hw₂
    · rcases hterm with ⟨hc, a, hrhs⟩
      rw [hc] at hw₁
      rcases singleton_indexed_eq_context_bounds hw₁ with ⟨hu, hv, _hA, _hτ⟩
      subst u
      subst v
      rw [hrhs] at hw₂
      simp [expandRhs] at hw₂
  · rintro ⟨r, hr, hlhs, hc, hrhs⟩
    refine ⟨r, [], [], σ, hr, ?_, ?_⟩
    · rw [hc, hlhs]
      rfl
    · rw [hrhs]
      simp [expandRhs]

theorem transforms_singleton_pop_iff_rule_of_isNormalForm {g : IndexedGrammar T}
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {A B : g.nt} {f : g.flag} {ρ : List g.flag} :
    g.Transforms [ISym.indexed A (f :: ρ)] [ISym.indexed B ρ] ↔
      ∃ r ∈ g.rules,
        r.lhs = A ∧ r.consume = some f ∧
          r.rhs = [IRhsSymbol.nonterminal B none] := by
  constructor
  · intro hstep
    rcases hstep with ⟨r, u, v, τ, hr, hw₁, hw₂⟩
    rcases hNF r hr with hbin | hpop | hpush | hterm
    · rcases hbin with ⟨hc, B₀, C₀, hrhs, _hB₀, _hC₀⟩
      rw [hc] at hw₁
      rcases singleton_indexed_eq_context_bounds hw₁ with ⟨hu, hv, _hA, _hτ⟩
      subst u
      subst v
      rw [hrhs] at hw₂
      simp [expandRhs] at hw₂
    · rcases hpop with ⟨f₀, hc, B₀, hrhs, _hB₀⟩
      rw [hc] at hw₁
      rcases singleton_indexed_eq_context_bounds hw₁ with ⟨hu, hv, hA, hstack⟩
      subst u
      subst v
      simp at hstack
      rcases hstack with ⟨hf, hτ⟩
      subst f₀
      subst τ
      rw [hrhs] at hw₂
      simp [expandRhs] at hw₂
      subst B₀
      exact ⟨r, hr, hA.symm, hc, hrhs⟩
    · rcases hpush with ⟨hc, B₀, f₀, hrhs, _hB₀⟩
      rw [hc] at hw₁
      rcases singleton_indexed_eq_context_bounds hw₁ with ⟨hu, hv, _hA, hτ⟩
      subst u
      subst v
      rw [hrhs] at hw₂
      simp [expandRhs] at hw₂
      rcases hw₂ with ⟨_, hout⟩
      subst τ
      have hlen := congrArg List.length hout
      simp at hlen
      omega
    · rcases hterm with ⟨hc, a, hrhs⟩
      rw [hc] at hw₁
      rcases singleton_indexed_eq_context_bounds hw₁ with ⟨hu, hv, _hA, _hτ⟩
      subst u
      subst v
      rw [hrhs] at hw₂
      simp [expandRhs] at hw₂
  · rintro ⟨r, hr, hlhs, hc, hrhs⟩
    refine ⟨r, [], [], ρ, hr, ?_, ?_⟩
    · rw [hc, hlhs]
      rfl
    · rw [hrhs]
      simp [expandRhs]

theorem transforms_singleton_push_iff_rule_of_isNormalForm {g : IndexedGrammar T}
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {A B : g.nt} {f : g.flag} {σ : List g.flag} :
    g.Transforms [ISym.indexed A σ] [ISym.indexed B (f :: σ)] ↔
      ∃ r ∈ g.rules,
        r.lhs = A ∧ r.consume = none ∧
          r.rhs = [IRhsSymbol.nonterminal B (some f)] := by
  constructor
  · intro hstep
    rcases hstep with ⟨r, u, v, τ, hr, hw₁, hw₂⟩
    rcases hNF r hr with hbin | hpop | hpush | hterm
    · rcases hbin with ⟨hc, B₀, C₀, hrhs, _hB₀, _hC₀⟩
      rw [hc] at hw₁
      rcases singleton_indexed_eq_context_bounds hw₁ with ⟨hu, hv, _hA, _hτ⟩
      subst u
      subst v
      rw [hrhs] at hw₂
      simp [expandRhs] at hw₂
    · rcases hpop with ⟨f₀, hc, B₀, hrhs, _hB₀⟩
      rw [hc] at hw₁
      rcases singleton_indexed_eq_context_bounds hw₁ with ⟨hu, hv, _hA, hτ⟩
      subst u
      subst v
      rw [hrhs] at hw₂
      simp [expandRhs] at hw₂
      rcases hw₂ with ⟨_, hout⟩
      subst σ
      have hlen := congrArg List.length hout
      simp at hlen
      omega
    · rcases hpush with ⟨hc, B₀, f₀, hrhs, _hB₀⟩
      rw [hc] at hw₁
      rcases singleton_indexed_eq_context_bounds hw₁ with ⟨hu, hv, hA, hτ⟩
      subst u
      subst v
      subst τ
      rw [hrhs] at hw₂
      simp [expandRhs] at hw₂
      rcases hw₂ with ⟨hB, hf⟩
      subst B₀
      subst f₀
      exact ⟨r, hr, hA.symm, hc, hrhs⟩
    · rcases hterm with ⟨hc, a, hrhs⟩
      rw [hc] at hw₁
      rcases singleton_indexed_eq_context_bounds hw₁ with ⟨hu, hv, _hA, _hτ⟩
      subst u
      subst v
      rw [hrhs] at hw₂
      simp [expandRhs] at hw₂
  · rintro ⟨r, hr, hlhs, hc, hrhs⟩
    refine ⟨r, [], [], σ, hr, ?_, ?_⟩
    · rw [hc, hlhs]
      rfl
    · rw [hrhs]
      simp [expandRhs]

theorem transforms_singleton_terminal_iff_rule_of_isNormalForm {g : IndexedGrammar T}
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {A : g.nt} {σ : List g.flag} {a : T} :
    g.Transforms [ISym.indexed A σ] [ISym.terminal a] ↔
      ∃ r ∈ g.rules,
        r.lhs = A ∧ r.consume = none ∧ r.rhs = [IRhsSymbol.terminal a] := by
  constructor
  · intro hstep
    rcases hstep with ⟨r, u, v, τ, hr, hw₁, hw₂⟩
    rcases hNF r hr with hbin | hpop | hpush | hterm
    · rcases hbin with ⟨hc, B₀, C₀, hrhs, _hB₀, _hC₀⟩
      rw [hc] at hw₁
      rcases singleton_indexed_eq_context_bounds hw₁ with ⟨hu, hv, _hA, _hτ⟩
      subst u
      subst v
      rw [hrhs] at hw₂
      simp [expandRhs] at hw₂
    · rcases hpop with ⟨f, hc, B₀, hrhs, _hB₀⟩
      rw [hc] at hw₁
      rcases singleton_indexed_eq_context_bounds hw₁ with ⟨hu, hv, _hA, _hτ⟩
      subst u
      subst v
      rw [hrhs] at hw₂
      simp [expandRhs] at hw₂
    · rcases hpush with ⟨hc, B₀, f, hrhs, _hB₀⟩
      rw [hc] at hw₁
      rcases singleton_indexed_eq_context_bounds hw₁ with ⟨hu, hv, _hA, _hτ⟩
      subst u
      subst v
      rw [hrhs] at hw₂
      simp [expandRhs] at hw₂
    · rcases hterm with ⟨hc, a₀, hrhs⟩
      rw [hc] at hw₁
      rcases singleton_indexed_eq_context_bounds hw₁ with ⟨hu, hv, hA, hτ⟩
      subst u
      subst v
      subst τ
      rw [hrhs] at hw₂
      simp [expandRhs] at hw₂
      subst a₀
      exact ⟨r, hr, hA.symm, hc, hrhs⟩
  · rintro ⟨r, hr, hlhs, hc, hrhs⟩
    refine ⟨r, [], [], σ, hr, ?_, ?_⟩
    · rw [hc, hlhs]
      rfl
    · rw [hrhs]
      simp [expandRhs]

/-- Counted first-step analysis for a terminal derivation from one indexed nonterminal in
normal form. The binary case splits both the terminal word and the remaining step budget. -/
theorem derivesIn_singleton_to_terminals_cases_of_isNormalForm {g : IndexedGrammar T}
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {n : ℕ} {A : g.nt} {σ : List g.flag} {w : List T}
    (hder : g.DerivesIn (n + 1) [ISym.indexed A σ]
      (w.map fun a => (ISym.terminal a : g.ISym))) :
    (∃ B C : g.nt, ∃ m k : ℕ, ∃ u v : List T,
      m + k = n ∧
        w = u ++ v ∧
        g.Transforms [ISym.indexed A σ] [ISym.indexed B σ, ISym.indexed C σ] ∧
        g.DerivesIn m [ISym.indexed B σ]
          (u.map fun a => (ISym.terminal a : g.ISym)) ∧
        g.DerivesIn k [ISym.indexed C σ]
          (v.map fun a => (ISym.terminal a : g.ISym))) ∨
    (∃ f : g.flag, ∃ ρ : List g.flag, ∃ B : g.nt,
      σ = f :: ρ ∧
        g.Transforms [ISym.indexed A σ] [ISym.indexed B ρ] ∧
        g.DerivesIn n [ISym.indexed B ρ]
          (w.map fun a => (ISym.terminal a : g.ISym))) ∨
    (∃ B : g.nt, ∃ f : g.flag,
      g.Transforms [ISym.indexed A σ] [ISym.indexed B (f :: σ)] ∧
        g.DerivesIn n [ISym.indexed B (f :: σ)]
          (w.map fun a => (ISym.terminal a : g.ISym))) ∨
    (∃ a : T,
      g.Transforms [ISym.indexed A σ] [ISym.terminal a] ∧ w = [a] ∧ n = 0) := by
  have hsplitInput :
      g.DerivesIn (1 + n) [ISym.indexed A σ]
        (w.map fun a => (ISym.terminal a : g.ISym)) := by
    simpa [Nat.add_comm] using hder
  rcases derivesIn_split (g := g) (m := 1) (n := n) hsplitInput with
    ⟨mid, hfirst, hrest⟩
  rcases hfirst with ⟨pre, hpre, hstep⟩
  have hpre' : [ISym.indexed A σ] = pre := by simpa using hpre
  subst pre
  rcases transforms_kind_cases_of_isNormalForm hNF hstep with hbin | hpop | hpush | hterm
  · rcases hbin with ⟨A₀, B, C, p, q, τ, _hB, _hC, hw₁, hw₂⟩
    rcases singleton_indexed_eq_context_bounds hw₁ with ⟨hp, hq, hA, hτ⟩
    subst p
    subst q
    subst A₀
    subst τ
    have hmid : mid = [ISym.indexed B σ, ISym.indexed C σ] := by
      simpa using hw₂
    subst mid
    rcases derivesIn_pair_to_terminals_split (g := g) hrest with
      ⟨m, k, u, v, hmk, hw, hleft, hright⟩
    left
    exact ⟨B, C, m, k, u, v, hmk, hw, hstep, hleft, hright⟩
  · rcases hpop with ⟨A₀, B, f, p, q, ρ, _hB, hw₁, hw₂⟩
    rcases singleton_indexed_eq_context_bounds hw₁ with ⟨hp, hq, hA, hσ⟩
    subst p
    subst q
    subst A₀
    have hmid : mid = [ISym.indexed B ρ] := by
      simpa using hw₂
    subst mid
    right
    left
    exact ⟨f, ρ, B, hσ, hstep, hrest⟩
  · rcases hpush with ⟨A₀, B, f, p, q, τ, _hB, hw₁, hw₂⟩
    rcases singleton_indexed_eq_context_bounds hw₁ with ⟨hp, hq, hA, hτ⟩
    subst p
    subst q
    subst A₀
    subst τ
    have hmid : mid = [ISym.indexed B (f :: σ)] := by
      simpa using hw₂
    subst mid
    right
    right
    left
    exact ⟨B, f, hstep, hrest⟩
  · rcases hterm with ⟨A₀, a, p, q, τ, hw₁, hw₂⟩
    rcases singleton_indexed_eq_context_bounds hw₁ with ⟨hp, hq, hA, hτ⟩
    subst p
    subst q
    subst A₀
    subst τ
    have hmid : mid = [ISym.terminal a] := by
      simpa using hw₂
    subst mid
    right
    right
    right
    exact ⟨a, hstep, derivesIn_terminal_singleton_eq (g := g) hrest,
      derivesIn_terminal_singleton_steps_eq_zero (g := g) hrest⟩

/-- Exact counted recursive characterization of terminal derivations from one indexed
nonterminal in normal form. -/
theorem derivesIn_singleton_to_terminals_iff_of_isNormalForm {g : IndexedGrammar T}
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {n : ℕ} {A : g.nt} {σ : List g.flag} {w : List T} :
    g.DerivesIn (n + 1) [ISym.indexed A σ]
        (w.map fun a => (ISym.terminal a : g.ISym)) ↔
      (∃ B C : g.nt, ∃ m k : ℕ, ∃ u v : List T,
        m + k = n ∧
          w = u ++ v ∧
          g.Transforms [ISym.indexed A σ] [ISym.indexed B σ, ISym.indexed C σ] ∧
          g.DerivesIn m [ISym.indexed B σ]
            (u.map fun a => (ISym.terminal a : g.ISym)) ∧
          g.DerivesIn k [ISym.indexed C σ]
            (v.map fun a => (ISym.terminal a : g.ISym))) ∨
      (∃ f : g.flag, ∃ ρ : List g.flag, ∃ B : g.nt,
        σ = f :: ρ ∧
          g.Transforms [ISym.indexed A σ] [ISym.indexed B ρ] ∧
          g.DerivesIn n [ISym.indexed B ρ]
            (w.map fun a => (ISym.terminal a : g.ISym))) ∨
      (∃ B : g.nt, ∃ f : g.flag,
        g.Transforms [ISym.indexed A σ] [ISym.indexed B (f :: σ)] ∧
          g.DerivesIn n [ISym.indexed B (f :: σ)]
            (w.map fun a => (ISym.terminal a : g.ISym))) ∨
      (∃ a : T,
        g.Transforms [ISym.indexed A σ] [ISym.terminal a] ∧ w = [a] ∧ n = 0) := by
  constructor
  · exact derivesIn_singleton_to_terminals_cases_of_isNormalForm hNF
  · intro h
    rcases h with hbin | hpop | hpush | hterm
    · rcases hbin with ⟨B, C, m, k, u, v, hmk, hw, hstep, hleft, hright⟩
      subst w
      have hpair :=
        derivesIn_pair_to_terminals_of_derivesIn (g := g) hleft hright
      have hpairn :
          g.DerivesIn n [ISym.indexed B σ, ISym.indexed C σ]
            ((u ++ v).map fun a => (ISym.terminal a : g.ISym)) := by
        simpa [hmk] using hpair
      have htotal := derivesIn_trans (derivesIn_one_of_transforms hstep) hpairn
      simpa [Nat.add_comm] using htotal
    · rcases hpop with ⟨f, ρ, B, _hσ, hstep, hrest⟩
      have htotal := derivesIn_trans (derivesIn_one_of_transforms hstep) hrest
      simpa [Nat.add_comm] using htotal
    · rcases hpush with ⟨B, f, hstep, hrest⟩
      have htotal := derivesIn_trans (derivesIn_one_of_transforms hstep) hrest
      simpa [Nat.add_comm] using htotal
    · rcases hterm with ⟨a, hstep, hw, hn⟩
      subst w
      subst n
      simpa using derivesIn_one_of_transforms hstep

/-- Counted recursive characterization using concrete normal-form rules from `g.rules`.
This is the finite-search-facing form of singleton terminal derivability. -/
theorem derivesIn_singleton_to_terminals_rule_iff_of_isNormalForm {g : IndexedGrammar T}
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {n : ℕ} {A : g.nt} {σ : List g.flag} {w : List T} :
    g.DerivesIn (n + 1) [ISym.indexed A σ]
        (w.map fun a => (ISym.terminal a : g.ISym)) ↔
      (∃ B C : g.nt, ∃ m k : ℕ, ∃ u v : List T,
        ∃ r ∈ g.rules,
          r.lhs = A ∧ r.consume = none ∧
          r.rhs = [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none] ∧
          m + k = n ∧
          w = u ++ v ∧
          g.DerivesIn m [ISym.indexed B σ]
            (u.map fun a => (ISym.terminal a : g.ISym)) ∧
          g.DerivesIn k [ISym.indexed C σ]
            (v.map fun a => (ISym.terminal a : g.ISym))) ∨
      (∃ f : g.flag, ∃ ρ : List g.flag, ∃ B : g.nt,
        ∃ r ∈ g.rules,
          σ = f :: ρ ∧
          r.lhs = A ∧ r.consume = some f ∧
          r.rhs = [IRhsSymbol.nonterminal B none] ∧
          g.DerivesIn n [ISym.indexed B ρ]
            (w.map fun a => (ISym.terminal a : g.ISym))) ∨
      (∃ B : g.nt, ∃ f : g.flag, ∃ r ∈ g.rules,
        r.lhs = A ∧ r.consume = none ∧
        r.rhs = [IRhsSymbol.nonterminal B (some f)] ∧
        g.DerivesIn n [ISym.indexed B (f :: σ)]
          (w.map fun a => (ISym.terminal a : g.ISym))) ∨
      (∃ a : T, ∃ r ∈ g.rules,
        r.lhs = A ∧ r.consume = none ∧ r.rhs = [IRhsSymbol.terminal a] ∧
          w = [a] ∧ n = 0) := by
  constructor
  · intro hder
    have hcases :=
      (derivesIn_singleton_to_terminals_iff_of_isNormalForm
        (g := g) hNF (n := n) (A := A) (σ := σ) (w := w)).mp hder
    rcases hcases with hbin | hpop | hpush | hterm
    · rcases hbin with ⟨B, C, m, k, u, v, hmk, hw, hstep, hleft, hright⟩
      rcases (transforms_singleton_binary_iff_rule_of_isNormalForm
          (g := g) hNF (A := A) (B := B) (C := C) (σ := σ)).mp hstep with
        ⟨r, hr, hlhs, hc, hrhs⟩
      left
      exact ⟨B, C, m, k, u, v, r, hr, hlhs, hc, hrhs, hmk, hw, hleft, hright⟩
    · rcases hpop with ⟨f, ρ, B, hσ, hstep, hrest⟩
      rcases (transforms_singleton_pop_iff_rule_of_isNormalForm
          (g := g) hNF (A := A) (B := B) (f := f) (ρ := ρ)).mp
          (by simpa [hσ] using hstep) with
        ⟨r, hr, hlhs, hc, hrhs⟩
      right
      left
      exact ⟨f, ρ, B, r, hr, hσ, hlhs, hc, hrhs, hrest⟩
    · rcases hpush with ⟨B, f, hstep, hrest⟩
      rcases (transforms_singleton_push_iff_rule_of_isNormalForm
          (g := g) hNF (A := A) (B := B) (f := f) (σ := σ)).mp hstep with
        ⟨r, hr, hlhs, hc, hrhs⟩
      right
      right
      left
      exact ⟨B, f, r, hr, hlhs, hc, hrhs, hrest⟩
    · rcases hterm with ⟨a, hstep, hw, hn⟩
      rcases (transforms_singleton_terminal_iff_rule_of_isNormalForm
          (g := g) hNF (A := A) (σ := σ) (a := a)).mp hstep with
        ⟨r, hr, hlhs, hc, hrhs⟩
      right
      right
      right
      exact ⟨a, r, hr, hlhs, hc, hrhs, hw, hn⟩
  · intro h
    apply (derivesIn_singleton_to_terminals_iff_of_isNormalForm
      (g := g) hNF (n := n) (A := A) (σ := σ) (w := w)).mpr
    rcases h with hbin | hpop | hpush | hterm
    · rcases hbin with
        ⟨B, C, m, k, u, v, r, hr, hlhs, hc, hrhs, hmk, hw, hleft, hright⟩
      have hstep :
          g.Transforms [ISym.indexed A σ] [ISym.indexed B σ, ISym.indexed C σ] :=
        (transforms_singleton_binary_iff_rule_of_isNormalForm
          (g := g) hNF (A := A) (B := B) (C := C) (σ := σ)).mpr
          ⟨r, hr, hlhs, hc, hrhs⟩
      left
      exact ⟨B, C, m, k, u, v, hmk, hw, hstep, hleft, hright⟩
    · rcases hpop with ⟨f, ρ, B, r, hr, hσ, hlhs, hc, hrhs, hrest⟩
      have hstep :
          g.Transforms [ISym.indexed A (f :: ρ)] [ISym.indexed B ρ] :=
        (transforms_singleton_pop_iff_rule_of_isNormalForm
          (g := g) hNF (A := A) (B := B) (f := f) (ρ := ρ)).mpr
          ⟨r, hr, hlhs, hc, hrhs⟩
      right
      left
      exact ⟨f, ρ, B, hσ, by simpa [hσ] using hstep, hrest⟩
    · rcases hpush with ⟨B, f, r, hr, hlhs, hc, hrhs, hrest⟩
      have hstep :
          g.Transforms [ISym.indexed A σ] [ISym.indexed B (f :: σ)] :=
        (transforms_singleton_push_iff_rule_of_isNormalForm
          (g := g) hNF (A := A) (B := B) (f := f) (σ := σ)).mpr
          ⟨r, hr, hlhs, hc, hrhs⟩
      right
      right
      left
      exact ⟨B, f, hstep, hrest⟩
    · rcases hterm with ⟨a, r, hr, hlhs, hc, hrhs, hw, hn⟩
      have hstep :
          g.Transforms [ISym.indexed A σ] [ISym.terminal a] :=
        (transforms_singleton_terminal_iff_rule_of_isNormalForm
          (g := g) hNF (A := A) (σ := σ) (a := a)).mpr
          ⟨r, hr, hlhs, hc, hrhs⟩
      right
      right
      right
      exact ⟨a, hstep, hw, hn⟩

theorem derives_singleton_to_terminals_length_pos_of_noEpsilon {g : IndexedGrammar T}
    (hne : g.NoEpsilon') {A : g.nt} {σ : List g.flag} {w : List T}
    (hder : g.Derives [ISym.indexed A σ]
      (w.map fun a => (ISym.terminal a : g.ISym))) :
    0 < w.length := by
  have hlen := derives_length_le_of_noEpsilon hne hder
  simp at hlen
  omega

theorem binary_subderivations_lengths_pos_of_noEpsilon {g : IndexedGrammar T}
    (hne : g.NoEpsilon') {B C : g.nt} {σ : List g.flag} {u v : List T}
    (hleft : g.Derives [ISym.indexed B σ]
      (u.map fun a => (ISym.terminal a : g.ISym)))
    (hright : g.Derives [ISym.indexed C σ]
      (v.map fun a => (ISym.terminal a : g.ISym))) :
    0 < u.length ∧ 0 < v.length :=
  ⟨derives_singleton_to_terminals_length_pos_of_noEpsilon hne hleft,
    derives_singleton_to_terminals_length_pos_of_noEpsilon hne hright⟩

theorem binary_subderivations_lengths_lt_parent_of_noEpsilon {g : IndexedGrammar T}
    (hne : g.NoEpsilon') {B C : g.nt} {σ : List g.flag} {w u v : List T}
    (hw : w = u ++ v)
    (hleft : g.Derives [ISym.indexed B σ]
      (u.map fun a => (ISym.terminal a : g.ISym)))
    (hright : g.Derives [ISym.indexed C σ]
      (v.map fun a => (ISym.terminal a : g.ISym))) :
    u.length < w.length ∧ v.length < w.length := by
  have hpos := binary_subderivations_lengths_pos_of_noEpsilon hne hleft hright
  have hlen := congrArg List.length hw
  simp [List.length_append] at hlen
  omega

theorem binary_subderivations_lengths_lt_parent_of_isNormalForm {g : IndexedGrammar T}
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {B C : g.nt} {σ : List g.flag} {w u v : List T}
    (hw : w = u ++ v)
    (hleft : g.Derives [ISym.indexed B σ]
      (u.map fun a => (ISym.terminal a : g.ISym)))
    (hright : g.Derives [ISym.indexed C σ]
      (v.map fun a => (ISym.terminal a : g.ISym))) :
    u.length < w.length ∧ v.length < w.length :=
  binary_subderivations_lengths_lt_parent_of_noEpsilon
    (g.noEpsilon_of_isNormalForm hNF) hw hleft hright

/-- The two words generated by a binary branch are sublists of the parent word. -/
theorem binary_subderivation_words_sublist_parent {w u v : List T}
    (hw : w = u ++ v) :
    u.Sublist w ∧ v.Sublist w := by
  subst w
  exact ⟨List.sublist_append_left u v, List.sublist_append_right u v⟩

/-- Binary branch words remain inside any target word containing the parent as a sublist. -/
theorem binary_subderivation_words_sublist_target {w u v target : List T}
    (hw : w = u ++ v) (hwt : w.Sublist target) :
    u.Sublist target ∧ v.Sublist target := by
  have hparent := binary_subderivation_words_sublist_parent (T := T) hw
  exact ⟨hparent.1.trans hwt, hparent.2.trans hwt⟩

/-- Counted forward rule-level singleton decomposition with explicit decreasing sub-budgets and
target-compatible child yields. This is the finite-search form of the first-step analysis: every
recursive premise has a strictly smaller counted budget, and binary premises also have nonempty,
strictly smaller terminal yields contained in the ambient target. -/
theorem derivesIn_singleton_to_terminals_rule_cases_with_target_bounds_of_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {n : ℕ} {A : g.nt} {σ : List g.flag} {w target : List T}
    (hwt : w.Sublist target)
    (hder : g.DerivesIn (n + 1) [ISym.indexed A σ]
      (w.map fun a => (ISym.terminal a : g.ISym))) :
      (∃ B C : g.nt, ∃ m k : ℕ, ∃ u v : List T,
        ∃ r ∈ g.rules,
          r.lhs = A ∧ r.consume = none ∧
          r.rhs = [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none] ∧
          m + k = n ∧
          m < n + 1 ∧ k < n + 1 ∧
          w = u ++ v ∧
          0 < u.length ∧ 0 < v.length ∧
          u.length < w.length ∧ v.length < w.length ∧
          u.Sublist target ∧ v.Sublist target ∧
          g.DerivesIn m [ISym.indexed B σ]
            (u.map fun a => (ISym.terminal a : g.ISym)) ∧
          g.DerivesIn k [ISym.indexed C σ]
            (v.map fun a => (ISym.terminal a : g.ISym))) ∨
      (∃ f : g.flag, ∃ ρ : List g.flag, ∃ B : g.nt,
        ∃ r ∈ g.rules,
          σ = f :: ρ ∧
          r.lhs = A ∧ r.consume = some f ∧
          r.rhs = [IRhsSymbol.nonterminal B none] ∧
          n < n + 1 ∧
          g.DerivesIn n [ISym.indexed B ρ]
            (w.map fun a => (ISym.terminal a : g.ISym))) ∨
      (∃ B : g.nt, ∃ f : g.flag, ∃ r ∈ g.rules,
        r.lhs = A ∧ r.consume = none ∧
        r.rhs = [IRhsSymbol.nonterminal B (some f)] ∧
        n < n + 1 ∧
        g.DerivesIn n [ISym.indexed B (f :: σ)]
          (w.map fun a => (ISym.terminal a : g.ISym))) ∨
      (∃ a : T, ∃ r ∈ g.rules,
        r.lhs = A ∧ r.consume = none ∧ r.rhs = [IRhsSymbol.terminal a] ∧
          w = [a] ∧ n = 0) := by
  have hcases :=
    (derivesIn_singleton_to_terminals_rule_iff_of_isNormalForm
      (g := g) hNF (n := n) (A := A) (σ := σ) (w := w)).mp hder
  rcases hcases with hbin | hpop | hpush | hterm
  · rcases hbin with
      ⟨B, C, m, k, u, v, r, hr, hlhs, hc, hrhs, hmk, hw, hleft, hright⟩
    have hleftD := derives_of_derivesIn (g := g) hleft
    have hrightD := derives_of_derivesIn (g := g) hright
    have hpos :=
      binary_subderivations_lengths_pos_of_noEpsilon
        (g.noEpsilon_of_isNormalForm hNF) hleftD hrightD
    have hlt :=
      binary_subderivations_lengths_lt_parent_of_isNormalForm
        hNF hw hleftD hrightD
    have hsub := binary_subderivation_words_sublist_target (T := T) hw hwt
    have hm_lt : m < n + 1 := by omega
    have hk_lt : k < n + 1 := by omega
    left
    exact ⟨B, C, m, k, u, v, r, hr, hlhs, hc, hrhs, hmk, hm_lt, hk_lt, hw,
      hpos.1, hpos.2, hlt.1, hlt.2, hsub.1, hsub.2, hleft, hright⟩
  · rcases hpop with ⟨f, ρ, B, r, hr, hσ, hlhs, hc, hrhs, hrest⟩
    right
    left
    exact ⟨f, ρ, B, r, hr, hσ, hlhs, hc, hrhs, Nat.lt_succ_self n, hrest⟩
  · rcases hpush with ⟨B, f, r, hr, hlhs, hc, hrhs, hrest⟩
    right
    right
    left
    exact ⟨B, f, r, hr, hlhs, hc, hrhs, Nat.lt_succ_self n, hrest⟩
  · right
    right
    right
    exact hterm


end IndexedGrammar
