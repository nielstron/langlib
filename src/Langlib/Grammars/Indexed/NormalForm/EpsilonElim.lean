module

public import Mathlib
public import Langlib.Grammars.Indexed.Definition
public import Langlib.Grammars.Indexed.NormalForm.Bounds
@[expose]
public section

/-! # ε-Free Indexed Grammars

This file develops the stack-sensitive nullability infrastructure used by the
normal-form pipeline.  Nullability for indexed grammars depends on the current
stack, so ε-elimination is organized around right-hand-side sublists whose
deleted symbols are nullable at the stack they receive during expansion.

## References

* A. V. Aho, "Indexed grammars — an extension of context-free grammars", *JACM* 15(4), 1968.
-/

open List Relation

variable {T : Type}

namespace IndexedGrammar

section EpsilonElim

/-- A nonterminal `A` with stack `σ` is *nullable* if `g` can derive `[]` from
    `[indexed A σ]`. -/
def IsNullable (g : IndexedGrammar T) (A : g.nt) (σ : List g.flag) : Prop :=
  g.Derives [ISym.indexed A σ] []

/-- Generating the empty word is exactly nullability of the initial nonterminal with the
empty stack. -/
theorem generates_nil_iff_initial_nullable (g : IndexedGrammar T) :
    g.Generates [] ↔ g.IsNullable g.initial [] := by
  rfl

theorem isNullable_appendStackSuffix {g : IndexedGrammar T}
    {A : g.nt} {σ : List g.flag} (h : g.IsNullable A σ)
    (suffix : List g.flag) :
    g.IsNullable A (σ ++ suffix) := by
  simpa [IsNullable] using derives_appendStackSuffix_indexed (g := g) h suffix

/-- In a no-ε indexed grammar, no single stacked nonterminal can derive the empty sentential
form. -/
theorem not_isNullable_of_noEpsilon {g : IndexedGrammar T}
    (hne : g.NoEpsilon') (A : g.nt) (σ : List g.flag) :
    ¬ g.IsNullable A σ := by
  intro hnullable
  have hlen := derives_length_le_of_noEpsilon hne hnullable
  simp at hlen

/-- A nullable stacked nonterminal can be erased in any sentential context. -/
theorem derives_erase_nullable {g : IndexedGrammar T} {A : g.nt} {σ : List g.flag}
    (hnullable : g.IsNullable A σ) (u v : List g.ISym) :
    g.Derives (u ++ [ISym.indexed A σ] ++ v) (u ++ v) := by
  have hctx := deri_with_suffix (g := g) v (deri_with_prefix u hnullable)
  simpa [List.append_assoc] using hctx

/-- A one-step indexed rewrite of an appended sentential form rewrites either the left side
or the right side of the append. -/
theorem transforms_append_cases {g : IndexedGrammar T} {u v w : List g.ISym}
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

/-- If an appended sentential form derives `[]`, then its left component also derives `[]`. -/
theorem derives_nil_of_append_left {g : IndexedGrammar T} {u v : List g.ISym}
    (hder : g.Derives (u ++ v) []) :
    g.Derives u [] := by
  have haux :
      ∀ {w : List g.ISym}, g.Derives w [] →
        ∀ {u v : List g.ISym}, w = u ++ v → g.Derives u [] := by
    intro w h
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl =>
        intro u v hw
        rw [List.nil_eq_append_iff] at hw
        rw [hw.1]
        exact g.deri_self []
    | @head a c hstep hrest ih =>
        intro u v hw
        have hstep' : g.Transforms (u ++ v) c := by
          simpa [hw] using hstep
        rcases transforms_append_cases hstep' with hleft | hright
        · rcases hleft with ⟨u', hu', hw'⟩
          exact (deri_of_tran hu').trans (ih hw')
        · rcases hright with ⟨v', _hv', hw'⟩
          exact ih hw'
  exact haux hder rfl

/-- If an appended sentential form derives `[]`, then its right component also derives `[]`. -/
theorem derives_nil_of_append_right {g : IndexedGrammar T} {u v : List g.ISym}
    (hder : g.Derives (u ++ v) []) :
    g.Derives v [] := by
  have haux :
      ∀ {w : List g.ISym}, g.Derives w [] →
        ∀ {u v : List g.ISym}, w = u ++ v → g.Derives v [] := by
    intro w h
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl =>
        intro u v hw
        rw [List.nil_eq_append_iff] at hw
        rw [hw.2]
        exact g.deri_self []
    | @head a c hstep hrest ih =>
        intro u v hw
        have hstep' : g.Transforms (u ++ v) c := by
          simpa [hw] using hstep
        rcases transforms_append_cases hstep' with hleft | hright
        · rcases hleft with ⟨u', _hu', hw'⟩
          exact ih hw'
        · rcases hright with ⟨v', hv', hw'⟩
          exact (deri_of_tran hv').trans (ih hw')
  exact haux hder rfl

/-- If `u ++ v ++ w` derives `[]`, then the middle component derives `[]`. -/
theorem derives_nil_of_append {g : IndexedGrammar T} {u v w : List g.ISym}
    (hder : g.Derives (u ++ v ++ w) []) :
    g.Derives v [] := by
  have hleft : g.Derives (u ++ v) [] :=
    derives_nil_of_append_left (u := u ++ v) (v := w) (by
      simpa [List.append_assoc] using hder)
  exact derives_nil_of_append_right (u := u) (v := v) hleft

/-- Counted form: if `u ++ v` derives `[]`, then `u` derives `[]` within the
original budget. -/
theorem derivesIn_nil_of_append_left {g : IndexedGrammar T} {n : ℕ}
    {u v : List g.ISym} (hder : g.DerivesIn n (u ++ v) []) :
    ∃ m : ℕ, m ≤ n ∧ g.DerivesIn m u [] := by
  rcases derivesIn_append_split (g := g) hder with ⟨m, k, u', v', hmk, hx, hu, _hv⟩
  have hxnil := hx
  rw [List.nil_eq_append_iff] at hxnil
  rcases hxnil with ⟨hu', _hv'⟩
  subst u'
  refine ⟨m, ?_, by simpa using hu⟩
  omega

/-- Counted form: if `u ++ v` derives `[]`, then `v` derives `[]` within the
original budget. -/
theorem derivesIn_nil_of_append_right {g : IndexedGrammar T} {n : ℕ}
    {u v : List g.ISym} (hder : g.DerivesIn n (u ++ v) []) :
    ∃ m : ℕ, m ≤ n ∧ g.DerivesIn m v [] := by
  rcases derivesIn_append_split (g := g) hder with ⟨m, k, u', v', hmk, hx, _hu, hv⟩
  have hxnil := hx
  rw [List.nil_eq_append_iff] at hxnil
  rcases hxnil with ⟨_hu', hv'⟩
  subst v'
  refine ⟨k, ?_, by simpa using hv⟩
  omega

/-- Counted form: every symbol in a sentential form deriving `[]` derives `[]` within
the original budget. -/
theorem derivesIn_nil_of_mem {g : IndexedGrammar T} {n : ℕ}
    {w : List g.ISym} {s : g.ISym} (hder : g.DerivesIn n w []) (hs : s ∈ w) :
    ∃ m : ℕ, m ≤ n ∧ g.DerivesIn m [s] [] := by
  rcases (List.mem_iff_append.mp hs) with ⟨u, v, rfl⟩
  obtain ⟨m₁, hm₁n, hleft⟩ :=
    derivesIn_nil_of_append_left (g := g) (u := u ++ [s]) (v := v)
      (by simpa [List.append_assoc] using hder)
  obtain ⟨m₂, hm₂m₁, hsingle⟩ :=
    derivesIn_nil_of_append_right (g := g) (u := u) (v := [s]) hleft
  exact ⟨m₂, le_trans hm₂m₁ hm₁n, hsingle⟩

/-- Every symbol occurring in a sentential form that derives `[]` is nullable as a singleton
sentential form. -/
theorem derives_nil_of_mem {g : IndexedGrammar T} {w : List g.ISym} {s : g.ISym}
    (hder : g.Derives w []) (hs : s ∈ w) :
    g.Derives [s] [] := by
  rcases (List.mem_iff_append.mp hs) with ⟨u, v, rfl⟩
  exact derives_nil_of_append (u := u) (v := [s]) (w := v) (by simpa using hder)

/-- A terminal already present in a sentential form is still present after one indexed-grammar
rewrite step. Indexed rules rewrite only one indexed nonterminal in its context. -/
theorem terminal_mem_of_transforms {g : IndexedGrammar T} {w₁ w₂ : List g.ISym} {t : T}
    (hstep : g.Transforms w₁ w₂) :
    (ISym.terminal t : g.ISym) ∈ w₁ → (ISym.terminal t : g.ISym) ∈ w₂ := by
  rcases hstep with ⟨r, u, v, σ, _hr, hw₁, hw₂⟩
  subst w₂
  cases hc : r.consume with
  | none =>
      rw [hc] at hw₁
      subst w₁
      intro ht
      rw [List.mem_append] at ht ⊢
      rcases ht with hleft | hv
      · left
        rw [List.mem_append] at hleft ⊢
        rcases hleft with hu | hmid
        · exact Or.inl hu
        · simp at hmid
      · exact Or.inr hv
  | some f =>
      rw [hc] at hw₁
      subst w₁
      intro ht
      rw [List.mem_append] at ht ⊢
      rcases ht with hleft | hv
      · left
        rw [List.mem_append] at hleft ⊢
        rcases hleft with hu | hmid
        · exact Or.inl hu
        · simp at hmid
      · exact Or.inr hv

/-- A terminal already present in a sentential form is preserved by any indexed derivation. -/
theorem terminal_mem_of_derives {g : IndexedGrammar T} {w₁ w₂ : List g.ISym} {t : T}
    (hder : g.Derives w₁ w₂) :
    (ISym.terminal t : g.ISym) ∈ w₁ → (ISym.terminal t : g.ISym) ∈ w₂ := by
  induction hder with
  | refl =>
      intro ht
      exact ht
  | tail _ hstep ih =>
      intro ht
      exact terminal_mem_of_transforms hstep (ih ht)

/-- A sentential form containing a terminal cannot derive the empty sentential form. -/
theorem not_derives_nil_of_terminal_mem {g : IndexedGrammar T} {w : List g.ISym} {t : T}
    (ht : (ISym.terminal t : g.ISym) ∈ w) :
    ¬ g.Derives w [] := by
  intro hder
  have hmem := terminal_mem_of_derives hder ht
  simp at hmem

/-- If a sentential form derives `[]`, it contains no terminal. -/
theorem no_terminal_mem_of_derives_nil {g : IndexedGrammar T} {w : List g.ISym}
    (hder : g.Derives w []) (t : T) :
    (ISym.terminal t : g.ISym) ∉ w := by
  intro ht
  exact not_derives_nil_of_terminal_mem ht hder

/-- A terminal RHS symbol appears as the corresponding terminal in any expansion. -/
theorem terminal_mem_expandRhs_of_mem {g : IndexedGrammar T}
    {rhs : List (IRhsSymbol T g.nt g.flag)} {σ : List g.flag} {t : T}
    (ht : IRhsSymbol.terminal t ∈ rhs) :
    (ISym.terminal t : g.ISym) ∈ g.expandRhs rhs σ := by
  unfold expandRhs
  exact List.mem_map.mpr ⟨IRhsSymbol.terminal t, ht, rfl⟩

/-- Terminals in an expanded RHS come exactly from terminal RHS symbols. -/
theorem terminal_mem_rhs_of_mem_expandRhs {g : IndexedGrammar T}
    {rhs : List (IRhsSymbol T g.nt g.flag)} {σ : List g.flag} {t : T}
    (ht : (ISym.terminal t : g.ISym) ∈ g.expandRhs rhs σ) :
    IRhsSymbol.terminal t ∈ rhs := by
  unfold expandRhs at ht
  rw [List.mem_map] at ht
  rcases ht with ⟨s, hs, hs_eq⟩
  cases s with
  | terminal t₀ =>
      simp at hs_eq
      subst t₀
      exact hs
  | nonterminal n push =>
      cases push <;> simp at hs_eq

/-- If an expanded RHS can derive `[]`, the original RHS contains no terminal symbols. -/
theorem no_terminal_mem_rhs_of_expandRhs_derives_nil {g : IndexedGrammar T}
    {rhs : List (IRhsSymbol T g.nt g.flag)} {σ : List g.flag}
    (hder : g.Derives (g.expandRhs rhs σ) []) (t : T) :
    IRhsSymbol.terminal t ∉ rhs := by
  intro ht
  exact not_derives_nil_of_terminal_mem
    (terminal_mem_expandRhs_of_mem (g := g) (σ := σ) ht) hder

/-- A sentential form whose every symbol is a nullable indexed nonterminal derives the empty
sentential form. -/
theorem derives_nil_of_all_nullable_indexed {g : IndexedGrammar T} {w : List g.ISym}
    (hnullable :
      ∀ s ∈ w, ∃ A : g.nt, ∃ σ : List g.flag, s = ISym.indexed A σ ∧ g.IsNullable A σ) :
    g.Derives w [] := by
  induction w with
  | nil =>
      exact g.deri_self []
  | cons s rest ih =>
      rcases hnullable s (by simp) with ⟨A, σ, rfl, hA⟩
      have hhead : g.Derives ([ISym.indexed A σ] ++ rest) ([] ++ rest) :=
        deri_with_suffix rest hA
      have hrest : g.Derives rest [] := by
        apply ih
        intro x hx
        exact hnullable x (by simp [hx])
      exact
        (show g.Derives (ISym.indexed A σ :: rest) rest from by
          simpa using hhead).trans hrest

/-- If a sentential form derives `[]`, every symbol in it is a nullable indexed nonterminal. -/
theorem all_nullable_indexed_of_derives_nil {g : IndexedGrammar T} {w : List g.ISym}
    (hder : g.Derives w []) :
    ∀ s ∈ w, ∃ A : g.nt, ∃ σ : List g.flag, s = ISym.indexed A σ ∧ g.IsNullable A σ := by
  intro s hs
  cases s with
  | terminal t =>
      have hsingle : g.Derives [ISym.terminal t] [] :=
        derives_nil_of_mem hder hs
      exact False.elim
        (not_derives_nil_of_terminal_mem (g := g) (w := [ISym.terminal t])
          (t := t) (by simp) hsingle)
  | indexed A σ =>
      exact ⟨A, σ, rfl, derives_nil_of_mem hder hs⟩

/-- A sentential form derives `[]` exactly when all of its symbols are nullable indexed
nonterminals. -/
theorem derives_nil_iff_all_nullable_indexed {g : IndexedGrammar T} {w : List g.ISym} :
    g.Derives w [] ↔
      ∀ s ∈ w, ∃ A : g.nt, ∃ σ : List g.flag, s = ISym.indexed A σ ∧ g.IsNullable A σ :=
  ⟨all_nullable_indexed_of_derives_nil, derives_nil_of_all_nullable_indexed⟩

/-- An expanded RHS derives `[]` exactly when every RHS symbol is a nonterminal nullable at
the stack it receives from the expansion. -/
theorem expandRhs_derives_nil_iff_all_nullable_rhs {g : IndexedGrammar T}
    {rhs : List (IRhsSymbol T g.nt g.flag)} {σ : List g.flag} :
    g.Derives (g.expandRhs rhs σ) [] ↔
      ∀ s ∈ rhs, ∃ A : g.nt, ∃ push : Option g.flag,
        s = IRhsSymbol.nonterminal A push ∧
          g.IsNullable A (match push with | none => σ | some f => f :: σ) := by
  constructor
  · intro hder s hs
    cases s with
    | terminal t =>
        exact False.elim (no_terminal_mem_rhs_of_expandRhs_derives_nil hder t hs)
    | nonterminal A push =>
        cases push with
        | none =>
            refine ⟨A, none, rfl, ?_⟩
            have hmem : (ISym.indexed A σ : g.ISym) ∈ g.expandRhs rhs σ := by
              unfold expandRhs
              exact List.mem_map.mpr ⟨IRhsSymbol.nonterminal A none, hs, rfl⟩
            exact derives_nil_of_mem hder hmem
        | some f =>
            refine ⟨A, some f, rfl, ?_⟩
            have hmem : (ISym.indexed A (f :: σ) : g.ISym) ∈ g.expandRhs rhs σ := by
              unfold expandRhs
              exact List.mem_map.mpr ⟨IRhsSymbol.nonterminal A (some f), hs, rfl⟩
            exact derives_nil_of_mem hder hmem
  · intro hnullable
    apply derives_nil_of_all_nullable_indexed
    intro s hs
    unfold expandRhs at hs
    rw [List.mem_map] at hs
    rcases hs with ⟨rhsSym, hrhsSym, hs_eq⟩
    cases rhsSym with
    | terminal t =>
        rcases hnullable (IRhsSymbol.terminal t) hrhsSym with ⟨A, push, hterm, _⟩
        cases hterm
    | nonterminal A push =>
        subst s
        rcases hnullable (IRhsSymbol.nonterminal A push) hrhsSym with
          ⟨B, push', heq, hnull⟩
        cases heq
        cases push with
        | none =>
            exact ⟨A, σ, rfl, hnull⟩
        | some f =>
            exact ⟨A, f :: σ, rfl, hnull⟩

/-- Counted extraction for one nonterminal occurrence in an expanded RHS deriving `[]`. -/
theorem derivesIn_nil_of_expandRhs_nonterminal_mem {g : IndexedGrammar T}
    {n : ℕ} {rhs : List (IRhsSymbol T g.nt g.flag)} {σ : List g.flag}
    {B : g.nt} {push : Option g.flag}
    (hder : g.DerivesIn n (g.expandRhs rhs σ) [])
    (hs : IRhsSymbol.nonterminal B push ∈ rhs) :
    ∃ m : ℕ, m ≤ n ∧
      g.DerivesIn m
        [ISym.indexed B (match push with | none => σ | some f => f :: σ)] [] := by
  cases push with
  | none =>
      have hmem : (ISym.indexed B σ : g.ISym) ∈ g.expandRhs rhs σ := by
        unfold expandRhs
        exact List.mem_map.mpr ⟨IRhsSymbol.nonterminal B none, hs, rfl⟩
      simpa using derivesIn_nil_of_mem (g := g) hder hmem
  | some f =>
      have hmem : (ISym.indexed B (f :: σ) : g.ISym) ∈ g.expandRhs rhs σ := by
        unfold expandRhs
        exact List.mem_map.mpr ⟨IRhsSymbol.nonterminal B (some f), hs, rfl⟩
      simpa using derivesIn_nil_of_mem (g := g) hder hmem

/-- `kept` is obtained from `rhs` by deleting only RHS nonterminals that are nullable at
the stack they receive during expansion. -/
inductive NullableRhsSublist (g : IndexedGrammar T) (σ : List g.flag) :
    List (IRhsSymbol T g.nt g.flag) → List (IRhsSymbol T g.nt g.flag) → Prop
  | nil : NullableRhsSublist g σ [] []
  | keep (s : IRhsSymbol T g.nt g.flag) {rhs kept}
      (h : NullableRhsSublist g σ rhs kept) :
      NullableRhsSublist g σ (s :: rhs) (s :: kept)
  | drop_none {A : g.nt} {rhs kept}
      (hnullable : g.IsNullable A σ)
      (h : NullableRhsSublist g σ rhs kept) :
      NullableRhsSublist g σ (IRhsSymbol.nonterminal A none :: rhs) kept
  | drop_some {A : g.nt} {f : g.flag} {rhs kept}
      (hnullable : g.IsNullable A (f :: σ))
      (h : NullableRhsSublist g σ rhs kept) :
      NullableRhsSublist g σ (IRhsSymbol.nonterminal A (some f) :: rhs) kept

theorem nullableRhsSublist_self (g : IndexedGrammar T) (σ : List g.flag)
    (rhs : List (IRhsSymbol T g.nt g.flag)) :
    NullableRhsSublist g σ rhs rhs := by
  induction rhs with
  | nil => exact NullableRhsSublist.nil
  | cons s rhs ih => exact NullableRhsSublist.keep s ih

theorem NullableRhsSublist.sublist {g : IndexedGrammar T} {σ : List g.flag}
    {rhs kept : List (IRhsSymbol T g.nt g.flag)}
    (h : NullableRhsSublist g σ rhs kept) :
    kept.Sublist rhs := by
  induction h with
  | nil => exact List.Sublist.refl []
  | keep s h ih => exact ih.cons₂ s
  | drop_none hnullable h ih =>
      rename_i A rhs kept
      exact List.Sublist.cons (IRhsSymbol.nonterminal A none) ih
  | drop_some hnullable h ih =>
      rename_i A f rhs kept
      exact List.Sublist.cons (IRhsSymbol.nonterminal A (some f)) ih

theorem derives_expandRhs_of_nullableRhsSublist {g : IndexedGrammar T}
    {σ : List g.flag} {rhs kept : List (IRhsSymbol T g.nt g.flag)}
    (h : NullableRhsSublist g σ rhs kept) :
    g.Derives (g.expandRhs rhs σ) (g.expandRhs kept σ) := by
  induction h with
  | nil =>
      exact g.deri_self []
  | keep s h ih =>
      cases s with
      | terminal t =>
          simpa [expandRhs] using deri_with_prefix (g := g) [ISym.terminal t] ih
      | nonterminal A push =>
          cases push with
          | none =>
              simpa [expandRhs] using
                deri_with_prefix (g := g) [ISym.indexed A σ] ih
          | some f =>
              simpa [expandRhs] using
                deri_with_prefix (g := g) [ISym.indexed A (f :: σ)] ih
  | drop_none hnullable h ih =>
      rename_i A rhs kept
      have hdrop :
          g.Derives (ISym.indexed A σ :: g.expandRhs rhs σ)
            (g.expandRhs rhs σ) := by
        simpa using derives_erase_nullable (g := g) hnullable [] (g.expandRhs rhs σ)
      exact hdrop.trans ih
  | drop_some hnullable h ih =>
      rename_i A f rhs kept
      have hdrop :
          g.Derives (ISym.indexed A (f :: σ) :: g.expandRhs rhs σ)
            (g.expandRhs rhs σ) := by
        simpa using derives_erase_nullable (g := g) hnullable [] (g.expandRhs rhs σ)
      exact hdrop.trans ih

theorem derives_context_expandRhs_of_nullableRhsSublist {g : IndexedGrammar T}
    {σ : List g.flag} {rhs kept : List (IRhsSymbol T g.nt g.flag)}
    (h : NullableRhsSublist g σ rhs kept) (u v : List g.ISym) :
    g.Derives (u ++ g.expandRhs rhs σ ++ v)
      (u ++ g.expandRhs kept σ ++ v) := by
  simpa [List.append_assoc] using
    deri_with_suffix (g := g) v
      (deri_with_prefix (g := g) u (derives_expandRhs_of_nullableRhsSublist h))

theorem derives_nil_of_nullableRhsSublist_nil {g : IndexedGrammar T}
    {σ : List g.flag} {rhs : List (IRhsSymbol T g.nt g.flag)}
    (h : NullableRhsSublist g σ rhs []) :
    g.Derives (g.expandRhs rhs σ) [] := by
  simpa [expandRhs] using derives_expandRhs_of_nullableRhsSublist h

theorem NullableRhsSublist.kept_ne_nil_of_not_derives_nil {g : IndexedGrammar T}
    {σ : List g.flag} {rhs kept : List (IRhsSymbol T g.nt g.flag)}
    (h : NullableRhsSublist g σ rhs kept)
    (hnot : ¬ g.Derives (g.expandRhs rhs σ) []) :
    kept ≠ [] := by
  intro hkept
  subst kept
  exact hnot (derives_nil_of_nullableRhsSublist_nil h)

theorem exists_nonempty_nullableRhsSublist_of_not_derives_nil {g : IndexedGrammar T}
    {rhs : List (IRhsSymbol T g.nt g.flag)} {σ : List g.flag}
    (hnot : ¬ g.Derives (g.expandRhs rhs σ) []) :
    ∃ kept : List (IRhsSymbol T g.nt g.flag),
      NullableRhsSublist g σ rhs kept ∧ kept ≠ [] := by
  refine ⟨rhs, nullableRhsSublist_self g σ rhs, ?_⟩
  intro hrhs
  subst rhs
  exact hnot (by simpa [expandRhs] using g.deri_self [])

theorem derives_rule_nullableRhsSublist_none {g : IndexedGrammar T}
    {r : IRule T g.nt g.flag} {σ : List g.flag}
    {kept : List (IRhsSymbol T g.nt g.flag)}
    (hr : r ∈ g.rules) (hconsume : r.consume = none)
    (hsub : NullableRhsSublist g σ r.rhs kept) (u v : List g.ISym) :
    g.Derives (u ++ [ISym.indexed r.lhs σ] ++ v)
      (u ++ g.expandRhs kept σ ++ v) := by
  have hstep :
      g.Transforms (u ++ [ISym.indexed r.lhs σ] ++ v)
        (u ++ g.expandRhs r.rhs σ ++ v) := by
    refine ⟨r, u, v, σ, hr, ?_, rfl⟩
    rw [hconsume]
  exact
    (deri_of_tran hstep).trans
      (derives_context_expandRhs_of_nullableRhsSublist hsub u v)

theorem derives_rule_nullableRhsSublist_some {g : IndexedGrammar T}
    {r : IRule T g.nt g.flag} {f : g.flag} {σ : List g.flag}
    {kept : List (IRhsSymbol T g.nt g.flag)}
    (hr : r ∈ g.rules) (hconsume : r.consume = some f)
    (hsub : NullableRhsSublist g σ r.rhs kept) (u v : List g.ISym) :
    g.Derives (u ++ [ISym.indexed r.lhs (f :: σ)] ++ v)
      (u ++ g.expandRhs kept σ ++ v) := by
  have hstep :
      g.Transforms (u ++ [ISym.indexed r.lhs (f :: σ)] ++ v)
        (u ++ g.expandRhs r.rhs σ ++ v) := by
    refine ⟨r, u, v, σ, hr, ?_, rfl⟩
    rw [hconsume]
  exact
    (deri_of_tran hstep).trans
      (derives_context_expandRhs_of_nullableRhsSublist hsub u v)

theorem derives_rule_nullableRhsSublist {g : IndexedGrammar T}
    {r : IRule T g.nt g.flag} {σ : List g.flag}
    {kept : List (IRhsSymbol T g.nt g.flag)}
    (hr : r ∈ g.rules) (hsub : NullableRhsSublist g σ r.rhs kept)
    (u v : List g.ISym) :
    g.Derives
      (match r.consume with
       | none => u ++ [ISym.indexed r.lhs σ] ++ v
       | some f => u ++ [ISym.indexed r.lhs (f :: σ)] ++ v)
      (u ++ g.expandRhs kept σ ++ v) := by
  cases hconsume : r.consume with
  | none =>
      simpa [hconsume] using
        derives_rule_nullableRhsSublist_none
          (g := g) (r := r) (σ := σ) (kept := kept) hr hconsume hsub u v
  | some f =>
      simpa [hconsume] using
        derives_rule_nullableRhsSublist_some
          (g := g) (r := r) (f := f) (σ := σ) (kept := kept) hr hconsume hsub u v

/-- A derivation whose source sentential form is empty can only end at the empty sentential
form. -/
theorem derives_empty_left_eq {g : IndexedGrammar T} {w : List g.ISym}
    (h : g.Derives ([] : List g.ISym) w) :
    w = [] := by
  obtain ⟨n, hn⟩ := exists_derivesIn_of_derives (g := g) h
  exact (derivesIn_nil_left_eq (g := g) hn).2

/-- If an expanded RHS derives a terminal word, then the same word is derived by some
sublist obtained by deleting only nullable RHS nonterminals.  Nonempty terminal output keeps
at least one RHS symbol. -/
theorem exists_nullableRhsSublist_derives_to_terminals {g : IndexedGrammar T}
    {rhs : List (IRhsSymbol T g.nt g.flag)} {σ : List g.flag} {w : List T}
    (hder : g.Derives (g.expandRhs rhs σ)
      (w.map fun a => (ISym.terminal a : g.ISym))) :
    ∃ kept : List (IRhsSymbol T g.nt g.flag),
      NullableRhsSublist g σ rhs kept ∧
        g.Derives (g.expandRhs kept σ)
          (w.map fun a => (ISym.terminal a : g.ISym)) ∧
        (w ≠ [] → kept ≠ []) := by
  induction rhs generalizing w with
  | nil =>
      have htarget :
          (w.map fun a => (ISym.terminal a : g.ISym)) = [] :=
        derives_empty_left_eq (g := g) (by simpa [expandRhs] using hder)
      have hw : w = [] := by
        simpa using htarget
      subst w
      refine ⟨[], NullableRhsSublist.nil, ?_, ?_⟩
      · exact g.deri_self []
      · intro hne
        exact False.elim (hne rfl)
  | cons s rhs ih =>
      have hsource :
          g.Derives (g.expandRhs [s] σ ++ g.expandRhs rhs σ)
            (w.map fun a => (ISym.terminal a : g.ISym)) := by
        simpa [expandRhs] using hder
      rcases derives_append_to_terminals_split
          (g := g) (u := g.expandRhs [s] σ) (v := g.expandRhs rhs σ)
          hsource with
        ⟨wh, wt, hw, hhead, htail⟩
      subst w
      rcases ih htail with ⟨kept, hsub, hkept_der, hkept_nonempty⟩
      have hkeep :
          ∃ kept' : List (IRhsSymbol T g.nt g.flag),
            NullableRhsSublist g σ (s :: rhs) kept' ∧
              g.Derives (g.expandRhs kept' σ)
                ((wh ++ wt).map fun a => (ISym.terminal a : g.ISym)) ∧
              ((wh ++ wt) ≠ [] → kept' ≠ []) := by
        refine ⟨s :: kept, NullableRhsSublist.keep s hsub, ?_, ?_⟩
        · have hleft :
              g.Derives (g.expandRhs [s] σ ++ g.expandRhs kept σ)
                ((wh.map fun a => (ISym.terminal a : g.ISym)) ++
                  g.expandRhs kept σ) :=
            deri_with_suffix (g := g) (g.expandRhs kept σ) hhead
          have hright :
              g.Derives
                ((wh.map fun a => (ISym.terminal a : g.ISym)) ++
                  g.expandRhs kept σ)
                ((wh.map fun a => (ISym.terminal a : g.ISym)) ++
                  (wt.map fun a => (ISym.terminal a : g.ISym))) :=
            deri_with_prefix (g := g)
              (wh.map fun a => (ISym.terminal a : g.ISym)) hkept_der
          have hcomp := hleft.trans hright
          simpa [expandRhs, List.map_append] using hcomp
        · intro _ hnil
          cases hnil
      cases s with
      | terminal t =>
          exact hkeep
      | nonterminal A push =>
          cases push with
          | none =>
              cases wh with
              | nil =>
                  have hnullable : g.IsNullable A σ := by
                    simpa [IsNullable, expandRhs] using hhead
                  refine ⟨kept, NullableRhsSublist.drop_none hnullable hsub, ?_, ?_⟩
                  · simpa using hkept_der
                  · simpa using hkept_nonempty
              | cons a wh =>
                  exact hkeep
          | some f =>
              cases wh with
              | nil =>
                  have hnullable : g.IsNullable A (f :: σ) := by
                    simpa [IsNullable, expandRhs] using hhead
                  refine ⟨kept, NullableRhsSublist.drop_some hnullable hsub, ?_, ?_⟩
                  · simpa using hkept_der
                  · simpa using hkept_nonempty
              | cons a wh =>
                  exact hkeep

/-- Branch-wise strengthening of `exists_nullableRhsSublist_derives_to_terminals`: every
kept RHS symbol is assigned a nonempty terminal yield derived from that symbol. -/
theorem exists_nullableRhsSublist_derives_to_terminals_parts {g : IndexedGrammar T}
    {rhs : List (IRhsSymbol T g.nt g.flag)} {σ : List g.flag} {w : List T}
    (hder : g.Derives (g.expandRhs rhs σ)
      (w.map fun a => (ISym.terminal a : g.ISym))) :
    ∃ kept : List (IRhsSymbol T g.nt g.flag), ∃ parts : List (List T),
      NullableRhsSublist g σ rhs kept ∧
        w = parts.flatten ∧
        List.Forall₂
          (fun s part =>
            part ≠ [] ∧
              g.Derives (g.expandRhs [s] σ)
                (part.map fun a => (ISym.terminal a : g.ISym)))
          kept parts := by
  induction rhs generalizing w with
  | nil =>
      have htarget :
          (w.map fun a => (ISym.terminal a : g.ISym)) = [] :=
        derives_empty_left_eq (g := g) (by simpa [expandRhs] using hder)
      have hw : w = [] := by
        simpa using htarget
      subst w
      exact ⟨[], [], NullableRhsSublist.nil, rfl, List.Forall₂.nil⟩
  | cons s rhs ih =>
      have hsource :
          g.Derives (g.expandRhs [s] σ ++ g.expandRhs rhs σ)
            (w.map fun a => (ISym.terminal a : g.ISym)) := by
        simpa [expandRhs] using hder
      rcases derives_append_to_terminals_split
          (g := g) (u := g.expandRhs [s] σ) (v := g.expandRhs rhs σ)
          hsource with
        ⟨wh, wt, hw, hhead, htail⟩
      subst w
      rcases ih htail with ⟨kept, parts, hsub, hwt, hparts⟩
      have hkeep (hwh : wh ≠ []) :
          ∃ kept' : List (IRhsSymbol T g.nt g.flag), ∃ parts' : List (List T),
            NullableRhsSublist g σ (s :: rhs) kept' ∧
              wh ++ wt = parts'.flatten ∧
              List.Forall₂
                (fun s part =>
                  part ≠ [] ∧
                    g.Derives (g.expandRhs [s] σ)
                      (part.map fun a => (ISym.terminal a : g.ISym)))
                kept' parts' := by
        refine ⟨s :: kept, wh :: parts, NullableRhsSublist.keep s hsub, ?_, ?_⟩
        · simp [hwt]
        · exact List.Forall₂.cons ⟨hwh, hhead⟩ hparts
      cases s with
      | terminal t =>
          have hwh : wh ≠ [] := by
            intro hnil_wh
            subst wh
            have hnil : g.Derives ([ISym.terminal t] : List g.ISym) [] := by
              simpa [expandRhs] using hhead
            exact not_derives_nil_of_terminal_mem (g := g) (t := t) (by simp) hnil
          exact hkeep hwh
      | nonterminal A push =>
          cases push with
          | none =>
              cases wh with
              | nil =>
                  have hnullable : g.IsNullable A σ := by
                    simpa [IsNullable, expandRhs] using hhead
                  exact ⟨kept, parts, NullableRhsSublist.drop_none hnullable hsub, by simp [hwt],
                    hparts⟩
              | cons a wh =>
                  exact hkeep (by simp)
          | some f =>
              cases wh with
              | nil =>
                  have hnullable : g.IsNullable A (f :: σ) := by
                    simpa [IsNullable, expandRhs] using hhead
                  exact ⟨kept, parts, NullableRhsSublist.drop_some hnullable hsub, by simp [hwt],
                    hparts⟩
              | cons a wh =>
                  exact hkeep (by simp)

/-- Counted branch-wise RHS pruning.  Besides deleting nullable RHS nonterminals, this
records a counted terminal yield for every kept symbol, and the kept budgets together do not
exceed the original derivation budget. -/
theorem exists_nullableRhsSublist_derivesIn_to_terminals_parts {g : IndexedGrammar T}
    {n : ℕ} {rhs : List (IRhsSymbol T g.nt g.flag)} {σ : List g.flag} {w : List T}
    (hder : g.DerivesIn n (g.expandRhs rhs σ)
      (w.map fun a => (ISym.terminal a : g.ISym))) :
    ∃ kept : List (IRhsSymbol T g.nt g.flag), ∃ parts : List (ℕ × List T),
      NullableRhsSublist g σ rhs kept ∧
        w = parts.flatMap (fun p => p.2) ∧
        (parts.map fun p => p.1).sum ≤ n ∧
        List.Forall₂
          (fun s p =>
            p.2 ≠ [] ∧
              g.DerivesIn p.1 (g.expandRhs [s] σ)
                (p.2.map fun a => (ISym.terminal a : g.ISym)))
          kept parts := by
  induction rhs generalizing n w with
  | nil =>
      obtain ⟨_hn, htarget⟩ :=
        derivesIn_nil_left_eq (g := g) (by simpa [expandRhs] using hder)
      have hw : w = [] := by
        simpa using htarget
      subst w
      exact ⟨[], [], NullableRhsSublist.nil, rfl, by simp, List.Forall₂.nil⟩
  | cons s rhs ih =>
      have hsource :
          g.DerivesIn n (g.expandRhs [s] σ ++ g.expandRhs rhs σ)
            (w.map fun a => (ISym.terminal a : g.ISym)) := by
        simpa [expandRhs] using hder
      rcases derivesIn_append_to_terminals_split
          (g := g) (u := g.expandRhs [s] σ) (v := g.expandRhs rhs σ)
          hsource with
        ⟨nh, nt, wh, wt, hbudget, hw, hhead, htail⟩
      subst w
      rcases ih htail with ⟨kept, parts, hsub, hwt, hparts_budget, hparts⟩
      have hkeep (hwh : wh ≠ []) :
          ∃ kept' : List (IRhsSymbol T g.nt g.flag), ∃ parts' : List (ℕ × List T),
            NullableRhsSublist g σ (s :: rhs) kept' ∧
              wh ++ wt = parts'.flatMap (fun p => p.2) ∧
              (parts'.map fun p => p.1).sum ≤ n ∧
              List.Forall₂
                (fun s p =>
                  p.2 ≠ [] ∧
                    g.DerivesIn p.1 (g.expandRhs [s] σ)
                      (p.2.map fun a => (ISym.terminal a : g.ISym)))
                kept' parts' := by
        refine ⟨s :: kept, (nh, wh) :: parts, NullableRhsSublist.keep s hsub, ?_, ?_, ?_⟩
        · simp [hwt]
        · simp
          omega
        · exact List.Forall₂.cons ⟨hwh, hhead⟩ hparts
      cases s with
      | terminal t =>
          have hwh : wh ≠ [] := by
            intro hnil_wh
            subst wh
            have hnil : g.Derives ([ISym.terminal t] : List g.ISym) [] :=
              derives_of_derivesIn (g := g) (by simpa [expandRhs] using hhead)
            exact not_derives_nil_of_terminal_mem (g := g) (t := t) (by simp) hnil
          exact hkeep hwh
      | nonterminal A push =>
          cases push with
          | none =>
              cases wh with
              | nil =>
                  have hnullable : g.IsNullable A σ := by
                    simpa [IsNullable, expandRhs] using
                      derives_of_derivesIn (g := g) hhead
                  refine ⟨kept, parts, NullableRhsSublist.drop_none hnullable hsub,
                    by simp [hwt], ?_, hparts⟩
                  omega
              | cons a wh =>
                  exact hkeep (by simp)
          | some f =>
              cases wh with
              | nil =>
                  have hnullable : g.IsNullable A (f :: σ) := by
                    simpa [IsNullable, expandRhs] using
                      derives_of_derivesIn (g := g) hhead
                  refine ⟨kept, parts, NullableRhsSublist.drop_some hnullable hsub,
                    by simp [hwt], ?_, hparts⟩
                  omega
              | cons a wh =>
                  exact hkeep (by simp)

theorem exists_nonempty_nullableRhsSublist_derivesIn_to_terminals_parts
    {g : IndexedGrammar T}
    {n : ℕ} {rhs : List (IRhsSymbol T g.nt g.flag)} {σ : List g.flag} {w : List T}
    (hder : g.DerivesIn n (g.expandRhs rhs σ)
      (w.map fun a => (ISym.terminal a : g.ISym))) (hw : w ≠ []) :
    ∃ kept : List (IRhsSymbol T g.nt g.flag), ∃ parts : List (ℕ × List T),
      NullableRhsSublist g σ rhs kept ∧
        kept ≠ [] ∧
        w = parts.flatMap (fun p => p.2) ∧
        (parts.map fun p => p.1).sum ≤ n ∧
        List.Forall₂
          (fun s p =>
            p.2 ≠ [] ∧
              g.DerivesIn p.1 (g.expandRhs [s] σ)
                (p.2.map fun a => (ISym.terminal a : g.ISym)))
          kept parts := by
  obtain ⟨kept, parts, hsub, hflat, hbudget, hparts⟩ :=
    exists_nullableRhsSublist_derivesIn_to_terminals_parts
      (g := g) (n := n) (rhs := rhs) (σ := σ) (w := w) hder
  refine ⟨kept, parts, hsub, ?_, hflat, hbudget, hparts⟩
  intro hkept
  subst kept
  cases hparts
  exact hw (by simpa using hflat)

/-- One epsilon-pruned step: apply an original rule, but keep only a nonempty RHS sublist
whose deleted nonterminals are nullable at the stack used by the rule application. -/
def PrunedTransforms (g : IndexedGrammar T) (w₁ w₂ : List g.ISym) : Prop :=
  ∃ r : IRule T g.nt g.flag, ∃ u v : List g.ISym, ∃ σ : List g.flag,
    ∃ kept : List (IRhsSymbol T g.nt g.flag),
      r ∈ g.rules ∧
        kept ≠ [] ∧
        NullableRhsSublist g σ r.rhs kept ∧
        (match r.consume with
         | none => w₁ = u ++ [ISym.indexed r.lhs σ] ++ v
         | some f => w₁ = u ++ [ISym.indexed r.lhs (f :: σ)] ++ v) ∧
        w₂ = u ++ g.expandRhs kept σ ++ v

/-- Reflexive-transitive closure of epsilon-pruned indexed steps. -/
def PrunedDerives (g : IndexedGrammar T) : List g.ISym → List g.ISym → Prop :=
  ReflTransGen g.PrunedTransforms

theorem prunedTransforms_length_le {g : IndexedGrammar T} {w₁ w₂ : List g.ISym}
    (hstep : g.PrunedTransforms w₁ w₂) :
    w₁.length ≤ w₂.length := by
  rcases hstep with ⟨r, u, v, σ, kept, _hr, hkept, _hsub, hw₁, hw₂⟩
  have hlen : 1 ≤ (g.expandRhs kept σ).length := by
    simp [expandRhs]
    exact Nat.succ_le_of_lt (List.length_pos_of_ne_nil hkept)
  subst w₂
  cases hc : r.consume with
  | none =>
      rw [hc] at hw₁
      subst w₁
      simp [List.length_append]
      omega
  | some f =>
      rw [hc] at hw₁
      subst w₁
      simp [List.length_append]
      omega

theorem prunedDerives_length_le {g : IndexedGrammar T} {w₁ w₂ : List g.ISym}
    (hder : g.PrunedDerives w₁ w₂) :
    w₁.length ≤ w₂.length := by
  induction hder with
  | refl => exact le_rfl
  | tail _ hstep ih =>
      exact le_trans ih (prunedTransforms_length_le hstep)

theorem derives_of_prunedTransforms {g : IndexedGrammar T} {w₁ w₂ : List g.ISym}
    (hstep : g.PrunedTransforms w₁ w₂) :
    g.Derives w₁ w₂ := by
  rcases hstep with ⟨r, u, v, σ, kept, hr, _hkept, hsub, hw₁, hw₂⟩
  subst w₂
  cases hc : r.consume with
  | none =>
      rw [hc] at hw₁
      have hfull :
          g.Transforms w₁ (u ++ g.expandRhs r.rhs σ ++ v) := by
        refine ⟨r, u, v, σ, hr, ?_, rfl⟩
        simpa [hc] using hw₁
      exact
        (deri_of_tran hfull).trans
          (derives_context_expandRhs_of_nullableRhsSublist hsub u v)
  | some f =>
      rw [hc] at hw₁
      have hfull :
          g.Transforms w₁ (u ++ g.expandRhs r.rhs σ ++ v) := by
        refine ⟨r, u, v, σ, hr, ?_, rfl⟩
        simpa [hc] using hw₁
      exact
        (deri_of_tran hfull).trans
          (derives_context_expandRhs_of_nullableRhsSublist hsub u v)

theorem derives_of_prunedDerives {g : IndexedGrammar T} {w₁ w₂ : List g.ISym}
    (hder : g.PrunedDerives w₁ w₂) :
    g.Derives w₁ w₂ := by
  induction hder with
  | refl => exact g.deri_self w₁
  | tail _ hstep ih =>
      exact ih.trans (derives_of_prunedTransforms hstep)

theorem prunedTransforms_with_prefix {g : IndexedGrammar T}
    {w₁ w₂ : List g.ISym} (u : List g.ISym)
    (hstep : g.PrunedTransforms w₁ w₂) :
    g.PrunedTransforms (u ++ w₁) (u ++ w₂) := by
  rcases hstep with ⟨r, p, q, σ, kept, hr, hkept, hsub, hw₁, hw₂⟩
  refine ⟨r, u ++ p, q, σ, kept, hr, hkept, hsub, ?_, ?_⟩
  · cases hc : r.consume with
    | none =>
        have hw₁' : w₁ = p ++ [ISym.indexed r.lhs σ] ++ q := by
          simpa [hc] using hw₁
        simp [hw₁', List.append_assoc]
    | some f =>
        have hw₁' : w₁ = p ++ [ISym.indexed r.lhs (f :: σ)] ++ q := by
          simpa [hc] using hw₁
        simp [hw₁', List.append_assoc]
  · simp [hw₂, List.append_assoc]

theorem prunedTransforms_with_suffix {g : IndexedGrammar T}
    {w₁ w₂ : List g.ISym} (v : List g.ISym)
    (hstep : g.PrunedTransforms w₁ w₂) :
    g.PrunedTransforms (w₁ ++ v) (w₂ ++ v) := by
  rcases hstep with ⟨r, p, q, σ, kept, hr, hkept, hsub, hw₁, hw₂⟩
  refine ⟨r, p, q ++ v, σ, kept, hr, hkept, hsub, ?_, ?_⟩
  · cases hc : r.consume with
    | none =>
        have hw₁' : w₁ = p ++ [ISym.indexed r.lhs σ] ++ q := by
          simpa [hc] using hw₁
        simp [hw₁', List.append_assoc]
    | some f =>
        have hw₁' : w₁ = p ++ [ISym.indexed r.lhs (f :: σ)] ++ q := by
          simpa [hc] using hw₁
        simp [hw₁', List.append_assoc]
  · simp [hw₂, List.append_assoc]

theorem prunedDerives_with_prefix {g : IndexedGrammar T}
    {w₁ w₂ : List g.ISym} (u : List g.ISym)
    (hder : g.PrunedDerives w₁ w₂) :
    g.PrunedDerives (u ++ w₁) (u ++ w₂) := by
  induction hder with
  | refl => exact ReflTransGen.refl
  | tail _ hstep ih =>
      exact ih.tail (prunedTransforms_with_prefix u hstep)

theorem prunedDerives_with_suffix {g : IndexedGrammar T}
    {w₁ w₂ : List g.ISym} (v : List g.ISym)
    (hder : g.PrunedDerives w₁ w₂) :
    g.PrunedDerives (w₁ ++ v) (w₂ ++ v) := by
  induction hder with
  | refl => exact ReflTransGen.refl
  | tail _ hstep ih =>
      exact ih.tail (prunedTransforms_with_suffix v hstep)

theorem prunedDerives_append {g : IndexedGrammar T}
    {u₁ u₂ v₁ v₂ : List g.ISym}
    (hu : g.PrunedDerives u₁ u₂) (hv : g.PrunedDerives v₁ v₂) :
    g.PrunedDerives (u₁ ++ v₁) (u₂ ++ v₂) :=
  (prunedDerives_with_suffix v₁ hu).trans
    (prunedDerives_with_prefix u₂ hv)

theorem part_fst_le_sum_of_mem (parts : List (ℕ × List T)) {p : ℕ × List T}
    (hp : p ∈ parts) :
    p.1 ≤ (parts.map fun q => q.1).sum := by
  induction parts with
  | nil =>
      simp at hp
  | cons =>
      rename_i hd parts ih
      simp only [List.mem_cons] at hp
      simp only [List.map_cons, List.sum_cons]
      rcases hp with hp | hp
      · subst p
        omega
      · have htail := ih hp
        omega

theorem prunedDerives_expandRhs_to_terminals_of_forall₂_derivesIn
    {g : IndexedGrammar T} {N : ℕ}
    (hrec : ∀ {m : ℕ} {A : g.nt} {σ : List g.flag} {w : List T},
      m < N →
        g.DerivesIn m [ISym.indexed A σ]
          (w.map fun a => (ISym.terminal a : g.ISym)) →
        w ≠ [] →
        g.PrunedDerives [ISym.indexed A σ]
          (w.map fun a => (ISym.terminal a : g.ISym)))
    {σ : List g.flag} {kept : List (IRhsSymbol T g.nt g.flag)}
    {parts : List (ℕ × List T)}
    (hparts : List.Forall₂
      (fun s p =>
        p.2 ≠ [] ∧
          g.DerivesIn p.1 (g.expandRhs [s] σ)
            (p.2.map fun a => (ISym.terminal a : g.ISym)))
      kept parts)
    (hlt : ∀ p ∈ parts, p.1 < N) :
    g.PrunedDerives (g.expandRhs kept σ)
      ((parts.flatMap fun p => p.2).map fun a => (ISym.terminal a : g.ISym)) := by
  induction hparts with
  | nil =>
      exact ReflTransGen.refl
  | cons hhead _htail ih =>
      rename_i s part kept parts
      rcases part with ⟨m, y⟩
      rcases hhead with ⟨hyne, hder⟩
      have hheadPruned :
          g.PrunedDerives (g.expandRhs [s] σ)
            (y.map fun a => (ISym.terminal a : g.ISym)) := by
        cases s with
        | terminal t =>
            have hy : y = [t] := by
              simpa [expandRhs] using
                derivesIn_terminal_singleton_eq (g := g) hder
            subst y
            simpa [expandRhs] using
              (ReflTransGen.refl :
                g.PrunedDerives ([ISym.terminal t] : List g.ISym) [ISym.terminal t])
        | nonterminal A push =>
            cases push with
            | none =>
                exact hrec (A := A) (σ := σ) (w := y)
                  (hlt (m, y) (by simp)) (by simpa [expandRhs] using hder) hyne
            | some f =>
                exact hrec (A := A) (σ := f :: σ) (w := y)
                  (hlt (m, y) (by simp)) (by simpa [expandRhs] using hder) hyne
      have htailPruned :
          g.PrunedDerives (g.expandRhs kept σ)
            ((parts.flatMap fun p => p.2).map fun a => (ISym.terminal a : g.ISym)) := by
        apply ih
        intro p hp
        exact hlt p (by simp [hp])
      have hcat := prunedDerives_append hheadPruned htailPruned
      simpa [expandRhs, List.map_append] using hcat

theorem nullableRhsSublist_nil_of_expandRhs_derives_nil {g : IndexedGrammar T}
    {rhs : List (IRhsSymbol T g.nt g.flag)} {σ : List g.flag}
    (hder : g.Derives (g.expandRhs rhs σ) []) :
    NullableRhsSublist g σ rhs [] := by
  induction rhs with
  | nil =>
      exact NullableRhsSublist.nil
  | cons s rhs ih =>
      have hall :=
        (expandRhs_derives_nil_iff_all_nullable_rhs (g := g)
          (rhs := s :: rhs) (σ := σ)).mp hder
      have htail_all :
          ∀ x ∈ rhs, ∃ A : g.nt, ∃ push : Option g.flag,
            x = IRhsSymbol.nonterminal A push ∧
              g.IsNullable A (match push with | none => σ | some f => f :: σ) := by
        intro x hx
        exact hall x (by simp [hx])
      have htail_der : g.Derives (g.expandRhs rhs σ) [] :=
        (expandRhs_derives_nil_iff_all_nullable_rhs (g := g)
          (rhs := rhs) (σ := σ)).mpr htail_all
      have htail := ih htail_der
      cases s with
      | terminal t =>
          rcases hall (IRhsSymbol.terminal t) (by simp) with ⟨A, push, hs, _⟩
          cases hs
      | nonterminal A push =>
          rcases hall (IRhsSymbol.nonterminal A push) (by simp) with
            ⟨B, push', hs, hnullable⟩
          cases hs
          cases push with
          | none =>
              exact NullableRhsSublist.drop_none hnullable htail
          | some f =>
              exact NullableRhsSublist.drop_some hnullable htail

/-- A singleton indexed symbol can only be a one-rule redex with empty context. -/
private theorem singleton_indexed_eq_context {g : IndexedGrammar T}
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

/-- Every nonempty generated word has a first start-rule expansion whose nullable
deletions leave a nonempty RHS deriving the same word. -/
theorem exists_initial_rule_nullableRhsSublist_of_generates_nonempty
    {g : IndexedGrammar T} {w : List T}
    (hgen : g.Generates w) (hw : w ≠ []) :
    ∃ r : IRule T g.nt g.flag,
      ∃ kept : List (IRhsSymbol T g.nt g.flag),
        r ∈ g.rules ∧
          r.lhs = g.initial ∧
          r.consume = none ∧
          NullableRhsSublist g [] r.rhs kept ∧
          kept ≠ [] ∧
          g.Derives (g.expandRhs kept [])
            (w.map fun a => (ISym.terminal a : g.ISym)) := by
  rcases Relation.ReflTransGen.cases_head hgen with hrefl | ⟨mid, hstep, hrest⟩
  · cases w with
    | nil =>
        exact False.elim (hw rfl)
    | cons a w =>
        simp at hrefl
  · rcases hstep with ⟨r, u, v, σ, hr, hsource, htarget⟩
    cases hc : r.consume with
    | none =>
        rw [hc] at hsource
        rcases singleton_indexed_eq_context hsource with ⟨hu, hv, hlhs, hσ⟩
        subst u
        subst v
        subst σ
        have hmid : mid = g.expandRhs r.rhs [] := by
          simpa using htarget
        subst mid
        have hrest' :
            g.Derives (g.expandRhs r.rhs [])
              (w.map fun a => (ISym.terminal a : g.ISym)) := by
          simpa using hrest
        rcases exists_nullableRhsSublist_derives_to_terminals
            (g := g) (rhs := r.rhs) (σ := []) (w := w) hrest' with
          ⟨kept, hsub, hkept_der, hkept_nonempty⟩
        exact ⟨r, kept, hr, hlhs.symm, hc, hsub, hkept_nonempty hw, hkept_der⟩
    | some f =>
        rw [hc] at hsource
        rcases singleton_indexed_eq_context hsource with ⟨_hu, _hv, _hlhs, hσ⟩
        simp at hσ

theorem exists_prunedTransforms_initial_of_generates_nonempty
    {g : IndexedGrammar T} {w : List T}
    (hgen : g.Generates w) (hw : w ≠ []) :
    ∃ sent : List g.ISym,
      g.PrunedTransforms [ISym.indexed g.initial []] sent ∧
        g.Derives sent (w.map fun a => (ISym.terminal a : g.ISym)) := by
  rcases exists_initial_rule_nullableRhsSublist_of_generates_nonempty
      (g := g) hgen hw with
    ⟨r, kept, hr, hlhs, hconsume, hsub, hkept, hder⟩
  refine ⟨g.expandRhs kept [], ?_, hder⟩
  refine ⟨r, [], [], [], kept, hr, hkept, hsub, ?_, ?_⟩
  · simp [hconsume, hlhs]
  · simp

theorem prunedDerives_indexed_to_terminals_of_derivesIn_nonempty
    {g : IndexedGrammar T} {n : ℕ} {A : g.nt} {σ : List g.flag} {w : List T}
    (hder : g.DerivesIn n [ISym.indexed A σ]
      (w.map fun a => (ISym.terminal a : g.ISym)))
    (hw : w ≠ []) :
    g.PrunedDerives [ISym.indexed A σ]
      (w.map fun a => (ISym.terminal a : g.ISym)) := by
  have hmain :
      ∀ n : ℕ, ∀ (A : g.nt) (σ : List g.flag) (w : List T),
        g.DerivesIn n [ISym.indexed A σ]
          (w.map fun a => (ISym.terminal a : g.ISym)) →
        w ≠ [] →
        g.PrunedDerives [ISym.indexed A σ]
          (w.map fun a => (ISym.terminal a : g.ISym)) := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih A σ w hder hw
    cases n with
    | zero =>
        have hEq : ([ISym.indexed A σ] : List g.ISym) =
            (w.map fun a => (ISym.terminal a : g.ISym)) := by
          simpa using hder
        have hmem : (ISym.indexed A σ : g.ISym) ∈
            (w.map fun a => (ISym.terminal a : g.ISym)) := by
          rw [← hEq]
          simp
        rcases List.mem_map.mp hmem with ⟨t, _ht, ht⟩
        cases ht
    | succ n =>
        have hsplitInput :
            g.DerivesIn (1 + n) [ISym.indexed A σ]
              (w.map fun a => (ISym.terminal a : g.ISym)) := by
          simpa [Nat.add_comm] using hder
        rcases derivesIn_split (g := g) (m := 1) (n := n) hsplitInput with
          ⟨mid, hfirst, hrest⟩
        rcases hfirst with ⟨x, hx0, hstep⟩
        have hx : x = [ISym.indexed A σ] := by
          simpa using hx0.symm
        subst x
        rcases hstep with ⟨r, u, v, ρ, hr, hsource, htarget⟩
        cases hc : r.consume with
        | none =>
            rw [hc] at hsource
            rcases singleton_indexed_eq_context hsource with ⟨hu, hv, hA, hσ⟩
            subst u
            subst v
            subst A
            subst σ
            have hmid : mid = g.expandRhs r.rhs ρ := by
              simpa using htarget
            subst mid
            have hrest' :
                g.DerivesIn n (g.expandRhs r.rhs ρ)
                  (w.map fun a => (ISym.terminal a : g.ISym)) := by
              simpa using hrest
            obtain ⟨kept, parts, hsub, hkept, hflat, hbudget, hparts⟩ :=
              exists_nonempty_nullableRhsSublist_derivesIn_to_terminals_parts
                (g := g) (n := n) (rhs := r.rhs) (σ := ρ) (w := w) hrest' hw
            have hprunedStep :
                g.PrunedTransforms [ISym.indexed r.lhs ρ] (g.expandRhs kept ρ) := by
              refine ⟨r, [], [], ρ, kept, hr, hkept, hsub, ?_, ?_⟩
              · simp [hc]
              · simp
            have hlt : ∀ p ∈ parts, p.1 < n + 1 := by
              intro p hp
              have hple : p.1 ≤ (parts.map fun q => q.1).sum :=
                part_fst_le_sum_of_mem (T := T) parts hp
              have hpn : p.1 ≤ n := le_trans hple hbudget
              omega
            have htail :
                g.PrunedDerives (g.expandRhs kept ρ)
                  ((parts.flatMap fun p => p.2).map fun a =>
                    (ISym.terminal a : g.ISym)) :=
              prunedDerives_expandRhs_to_terminals_of_forall₂_derivesIn
                (g := g) (N := n + 1)
                (hrec := fun {m A σ w} hm hderm hwm => ih m hm A σ w hderm hwm)
                (σ := ρ) hparts hlt
            have htailW :
                g.PrunedDerives (g.expandRhs kept ρ)
                  (w.map fun a => (ISym.terminal a : g.ISym)) := by
              simpa [hflat] using htail
            exact (ReflTransGen.single hprunedStep).trans htailW
        | some f =>
            rw [hc] at hsource
            rcases singleton_indexed_eq_context hsource with ⟨hu, hv, hA, hσ⟩
            subst u
            subst v
            subst A
            subst σ
            have hmid : mid = g.expandRhs r.rhs ρ := by
              simpa using htarget
            subst mid
            have hrest' :
                g.DerivesIn n (g.expandRhs r.rhs ρ)
                  (w.map fun a => (ISym.terminal a : g.ISym)) := by
              simpa using hrest
            obtain ⟨kept, parts, hsub, hkept, hflat, hbudget, hparts⟩ :=
              exists_nonempty_nullableRhsSublist_derivesIn_to_terminals_parts
                (g := g) (n := n) (rhs := r.rhs) (σ := ρ) (w := w) hrest' hw
            have hprunedStep :
                g.PrunedTransforms [ISym.indexed r.lhs (f :: ρ)] (g.expandRhs kept ρ) := by
              refine ⟨r, [], [], ρ, kept, hr, hkept, hsub, ?_, ?_⟩
              · simp [hc]
              · simp
            have hlt : ∀ p ∈ parts, p.1 < n + 1 := by
              intro p hp
              have hple : p.1 ≤ (parts.map fun q => q.1).sum :=
                part_fst_le_sum_of_mem (T := T) parts hp
              have hpn : p.1 ≤ n := le_trans hple hbudget
              omega
            have htail :
                g.PrunedDerives (g.expandRhs kept ρ)
                  ((parts.flatMap fun p => p.2).map fun a =>
                    (ISym.terminal a : g.ISym)) :=
              prunedDerives_expandRhs_to_terminals_of_forall₂_derivesIn
                (g := g) (N := n + 1)
                (hrec := fun {m A σ w} hm hderm hwm => ih m hm A σ w hderm hwm)
                (σ := ρ) hparts hlt
            have htailW :
                g.PrunedDerives (g.expandRhs kept ρ)
                  (w.map fun a => (ISym.terminal a : g.ISym)) := by
              simpa [hflat] using htail
            exact (ReflTransGen.single hprunedStep).trans htailW
  exact hmain n A σ w hder hw

/-- Every nonempty generated word has a complete derivation using only ε-pruned steps. -/
theorem prunedDerives_initial_of_generates_nonempty
    {g : IndexedGrammar T} {w : List T}
    (hgen : g.Generates w) (hw : w ≠ []) :
    g.PrunedDerives [ISym.indexed g.initial []]
      (w.map fun a => (ISym.terminal a : g.ISym)) := by
  obtain ⟨n, hder⟩ := exists_derivesIn_of_derives (g := g) hgen
  exact prunedDerives_indexed_to_terminals_of_derivesIn_nonempty
    (g := g) (n := n) (A := g.initial) (σ := []) (w := w) hder hw

/-- A pruned derivation from the start symbol can only end in a nonempty terminal word. -/
theorem ne_nil_of_prunedDerives_initial_to_terminals
    {g : IndexedGrammar T} {w : List T}
    (hder : g.PrunedDerives [ISym.indexed g.initial []]
      (w.map fun a => (ISym.terminal a : g.ISym))) :
    w ≠ [] := by
  have hlen : 1 ≤ w.length := by
    simpa using prunedDerives_length_le (g := g) hder
  intro hw
  subst w
  simp at hlen

/-- Semantic ε-elimination: pruned derivations from the start generate exactly the nonempty
part of the original language. -/
theorem prunedDerives_initial_to_terminals_iff_generates_nonempty
    {g : IndexedGrammar T} {w : List T} :
    g.PrunedDerives [ISym.indexed g.initial []]
      (w.map fun a => (ISym.terminal a : g.ISym)) ↔
      g.Generates w ∧ w ≠ [] := by
  constructor
  · intro hder
    exact ⟨by simpa [Generates] using derives_of_prunedDerives hder,
      ne_nil_of_prunedDerives_initial_to_terminals hder⟩
  · rintro ⟨hgen, hw⟩
    exact prunedDerives_initial_of_generates_nonempty hgen hw

/-- First-step analysis for a nullable stacked nonterminal. Nullability is witnessed by a
matching grammar rule whose expansion is nullable. -/
theorem isNullable_cases_rule {g : IndexedGrammar T} {A : g.nt} {σ : List g.flag}
    (hnullable : g.IsNullable A σ) :
    (∃ r : IRule T g.nt g.flag,
      r ∈ g.rules ∧ r.lhs = A ∧ r.consume = none ∧
        g.Derives (g.expandRhs r.rhs σ) []) ∨
    (∃ f : g.flag, ∃ ρ : List g.flag, ∃ r : IRule T g.nt g.flag,
      σ = f :: ρ ∧ r ∈ g.rules ∧ r.lhs = A ∧ r.consume = some f ∧
        g.Derives (g.expandRhs r.rhs ρ) []) := by
  rcases Relation.ReflTransGen.cases_head hnullable with hnil | ⟨mid, hstep, hrest⟩
  · cases hnil
  · rcases hstep with ⟨r, u, v, ρ, hr, hw₁, hw₂⟩
    cases hc : r.consume with
    | none =>
        rw [hc] at hw₁
        rcases singleton_indexed_eq_context hw₁ with ⟨hu, hv, hA, hσ⟩
        subst u
        subst v
        have hmid : mid = g.expandRhs r.rhs ρ := by
          simpa using hw₂
        subst mid
        left
        exact ⟨r, hr, hA.symm, hc, by simpa [hσ] using hrest⟩
    | some f =>
        rw [hc] at hw₁
        rcases singleton_indexed_eq_context hw₁ with ⟨hu, hv, hA, hσ⟩
        subst u
        subst v
        have hmid : mid = g.expandRhs r.rhs ρ := by
          simpa using hw₂
        subst mid
        right
        exact ⟨f, ρ, r, hσ, hr, hA.symm, hc, by simpa using hrest⟩

/-- Nullability propagates backwards along a derivation. -/
theorem isNullable_of_derives_nullable {g : IndexedGrammar T}
    {A B : g.nt} {σ τ : List g.flag}
    (hder : g.Derives [ISym.indexed A σ] [ISym.indexed B τ])
    (hnullable : g.IsNullable B τ) :
    g.IsNullable A σ :=
  hder.trans hnullable

/-- If a non-consuming rule expands to a nullable sentential form, then its left-hand side is
nullable at the same stack. -/
theorem isNullable_of_rule_derives_empty_none {g : IndexedGrammar T}
    {r : IRule T g.nt g.flag} {A : g.nt} {σ : List g.flag}
    (hr : r ∈ g.rules) (hlhs : r.lhs = A) (hconsume : r.consume = none)
    (hder : g.Derives (g.expandRhs r.rhs σ) []) :
    g.IsNullable A σ := by
  apply deri_of_deri_deri (deri_of_tran ?_) hder
  refine ⟨r, [], [], σ, hr, ?_, ?_⟩
  · rw [hconsume, hlhs]
    simp
  · simp

/-- If a flag-consuming rule expands to a nullable sentential form, then its left-hand side is
nullable when that flag is on top of the stack. -/
theorem isNullable_of_rule_derives_empty_some {g : IndexedGrammar T}
    {r : IRule T g.nt g.flag} {A : g.nt} {f : g.flag} {σ : List g.flag}
    (hr : r ∈ g.rules) (hlhs : r.lhs = A) (hconsume : r.consume = some f)
    (hder : g.Derives (g.expandRhs r.rhs σ) []) :
    g.IsNullable A (f :: σ) := by
  apply deri_of_deri_deri (deri_of_tran ?_) hder
  refine ⟨r, [], [], σ, hr, ?_, ?_⟩
  · rw [hconsume, hlhs]
    simp
  · simp

/-- Rule-level characterization of nullable stacked nonterminals. -/
theorem isNullable_iff_rule_derives_empty {g : IndexedGrammar T}
    {A : g.nt} {σ : List g.flag} :
    g.IsNullable A σ ↔
      (∃ r : IRule T g.nt g.flag,
        r ∈ g.rules ∧ r.lhs = A ∧ r.consume = none ∧
          g.Derives (g.expandRhs r.rhs σ) []) ∨
      (∃ f : g.flag, ∃ ρ : List g.flag, ∃ r : IRule T g.nt g.flag,
        σ = f :: ρ ∧ r ∈ g.rules ∧ r.lhs = A ∧ r.consume = some f ∧
          g.Derives (g.expandRhs r.rhs ρ) []) := by
  constructor
  · exact isNullable_cases_rule
  · intro h
    rcases h with hnone | hsome
    · rcases hnone with ⟨r, hr, hlhs, hconsume, hder⟩
      exact isNullable_of_rule_derives_empty_none hr hlhs hconsume hder
    · rcases hsome with ⟨f, ρ, r, hσ, hr, hlhs, hconsume, hder⟩
      rw [hσ]
      exact isNullable_of_rule_derives_empty_some hr hlhs hconsume hder

/-- In a flag-separated grammar, nullability has three concrete sources:
an explicit ε-rule, a non-consuming rule whose whole RHS is nullable at the inherited stack,
or a pop rule whose single child is nullable after the pop. -/
theorem isNullable_cases_flagsSeparated {g : IndexedGrammar T}
    (hfs : g.FlagsSeparated) {A : g.nt} {σ : List g.flag}
    (hnullable : g.IsNullable A σ) :
    (∃ r : IRule T g.nt g.flag,
      r ∈ g.rules ∧ r.lhs = A ∧ r.consume = none ∧ r.rhs = []) ∨
    (∃ r : IRule T g.nt g.flag,
      r ∈ g.rules ∧ r.lhs = A ∧ r.consume = none ∧ r.rhs ≠ [] ∧
        ∀ s ∈ r.rhs, ∃ B : g.nt, ∃ push : Option g.flag,
          s = IRhsSymbol.nonterminal B push ∧
            g.IsNullable B (match push with | none => σ | some f => f :: σ)) ∨
    (∃ f : g.flag, ∃ ρ : List g.flag, ∃ r : IRule T g.nt g.flag, ∃ B : g.nt,
      σ = f :: ρ ∧ r ∈ g.rules ∧ r.lhs = A ∧ r.consume = some f ∧
        r.rhs = [IRhsSymbol.nonterminal B none] ∧ g.IsNullable B ρ) := by
  rcases isNullable_cases_rule (g := g) hnullable with hnone | hsome
  · rcases hnone with ⟨r, hr, hlhs, hconsume, hder⟩
    by_cases hrhs : r.rhs = []
    · exact Or.inl ⟨r, hr, hlhs, hconsume, hrhs⟩
    · exact Or.inr (Or.inl ⟨r, hr, hlhs, hconsume, hrhs,
        (expandRhs_derives_nil_iff_all_nullable_rhs (g := g)
          (rhs := r.rhs) (σ := σ)).mp hder⟩)
  · rcases hsome with ⟨f, ρ, r, hσ, hr, hlhs, hconsume, hder⟩
    have hsomeFlag : r.consume.isSome := by
      simp [hconsume]
    rcases (hfs r hr).1 hsomeFlag with ⟨B, hrhs⟩
    have hB : g.IsNullable B ρ := by
      have hall :=
        (expandRhs_derives_nil_iff_all_nullable_rhs (g := g)
          (rhs := r.rhs) (σ := ρ)).mp hder
      have hmem : IRhsSymbol.nonterminal B none ∈ r.rhs := by
        rw [hrhs]
        simp
      rcases hall (IRhsSymbol.nonterminal B none) hmem with
        ⟨C, push, hsym, hnull⟩
      cases hsym
      exact hnull
    exact Or.inr (Or.inr ⟨f, ρ, r, B, hσ, hr, hlhs, hconsume, hrhs, hB⟩)

/-- A non-consuming rule whose expanded RHS is entirely nullable makes its LHS nullable. -/
theorem isNullable_of_rule_all_nullable_none {g : IndexedGrammar T}
    {r : IRule T g.nt g.flag} {A : g.nt} {σ : List g.flag}
    (hr : r ∈ g.rules) (hlhs : r.lhs = A) (hconsume : r.consume = none)
    (hall : ∀ s ∈ r.rhs, ∃ B : g.nt, ∃ push : Option g.flag,
      s = IRhsSymbol.nonterminal B push ∧
        g.IsNullable B (match push with | none => σ | some f => f :: σ)) :
    g.IsNullable A σ := by
  exact isNullable_of_rule_derives_empty_none (g := g) (r := r) (A := A)
    (σ := σ) hr hlhs hconsume
    ((expandRhs_derives_nil_iff_all_nullable_rhs (g := g)
      (rhs := r.rhs) (σ := σ)).mpr hall)

/-- A pop rule whose unique child is nullable after the pop makes its LHS nullable with
the consumed flag on top of the stack. -/
theorem isNullable_of_pop_rule_nullable_child {g : IndexedGrammar T}
    {r : IRule T g.nt g.flag} {A B : g.nt} {f : g.flag} {σ : List g.flag}
    (hr : r ∈ g.rules) (hlhs : r.lhs = A) (hconsume : r.consume = some f)
    (hrhs : r.rhs = [IRhsSymbol.nonterminal B none]) (hB : g.IsNullable B σ) :
    g.IsNullable A (f :: σ) := by
  apply isNullable_of_rule_derives_empty_some (g := g) (r := r) (A := A)
    (f := f) (σ := σ) hr hlhs hconsume
  rw [hrhs]
  simpa [expandRhs, IsNullable] using hB

/-- In a flag-separated grammar, nullability is exactly generated by explicit ε-rules,
non-consuming all-nullable RHSs, and pop rules whose child is nullable after the pop. -/
theorem isNullable_flagsSeparated_iff {g : IndexedGrammar T}
    (hfs : g.FlagsSeparated) {A : g.nt} {σ : List g.flag} :
    g.IsNullable A σ ↔
      (∃ r : IRule T g.nt g.flag,
        r ∈ g.rules ∧ r.lhs = A ∧ r.consume = none ∧ r.rhs = []) ∨
      (∃ r : IRule T g.nt g.flag,
        r ∈ g.rules ∧ r.lhs = A ∧ r.consume = none ∧ r.rhs ≠ [] ∧
          ∀ s ∈ r.rhs, ∃ B : g.nt, ∃ push : Option g.flag,
            s = IRhsSymbol.nonterminal B push ∧
              g.IsNullable B (match push with | none => σ | some f => f :: σ)) ∨
      (∃ f : g.flag, ∃ ρ : List g.flag, ∃ r : IRule T g.nt g.flag, ∃ B : g.nt,
        σ = f :: ρ ∧ r ∈ g.rules ∧ r.lhs = A ∧ r.consume = some f ∧
          r.rhs = [IRhsSymbol.nonterminal B none] ∧ g.IsNullable B ρ) := by
  constructor
  · exact isNullable_cases_flagsSeparated hfs
  · intro h
    rcases h with hnone_empty | hnone_nonempty | hsome
    · rcases hnone_empty with ⟨r, hr, hlhs, hconsume, hrhs⟩
      apply isNullable_of_rule_derives_empty_none (g := g) (r := r) (A := A)
        (σ := σ) hr hlhs hconsume
      rw [hrhs]
      exact g.deri_self []
    · rcases hnone_nonempty with ⟨r, hr, hlhs, hconsume, _hrhs_ne, hall⟩
      exact isNullable_of_rule_all_nullable_none hr hlhs hconsume hall
    · rcases hsome with ⟨f, ρ, r, B, hσ, hr, hlhs, hconsume, hrhs, hB⟩
      rw [hσ]
      exact isNullable_of_pop_rule_nullable_child hr hlhs hconsume hrhs hB

/-- Empty-stack specialization of the flag-separated nullability equations. -/
theorem isNullable_nil_iff_flagsSeparated {g : IndexedGrammar T}
    (hfs : g.FlagsSeparated) {A : g.nt} :
    g.IsNullable A [] ↔
      (∃ r : IRule T g.nt g.flag,
        r ∈ g.rules ∧ r.lhs = A ∧ r.consume = none ∧ r.rhs = []) ∨
      (∃ r : IRule T g.nt g.flag,
        r ∈ g.rules ∧ r.lhs = A ∧ r.consume = none ∧ r.rhs ≠ [] ∧
          ∀ s ∈ r.rhs, ∃ B : g.nt, ∃ push : Option g.flag,
            s = IRhsSymbol.nonterminal B push ∧
              g.IsNullable B (match push with | none => [] | some f => [f])) := by
  rw [isNullable_flagsSeparated_iff (g := g) hfs]
  constructor
  · intro h
    rcases h with hnone_empty | hnone_nonempty | hsome
    · exact Or.inl hnone_empty
    · exact Or.inr hnone_nonempty
    · rcases hsome with ⟨f, ρ, r, B, hnil, _hr, _hlhs, _hconsume, _hrhs, _hB⟩
      cases hnil
  · intro h
    rcases h with hnone_empty | hnone_nonempty
    · exact Or.inl hnone_empty
    · exact Or.inr (Or.inl hnone_nonempty)

/-- Nonempty-stack specialization of the flag-separated nullability equations. -/
theorem isNullable_cons_iff_flagsSeparated {g : IndexedGrammar T}
    (hfs : g.FlagsSeparated) {A : g.nt} {f : g.flag} {ρ : List g.flag} :
    g.IsNullable A (f :: ρ) ↔
      (∃ r : IRule T g.nt g.flag,
        r ∈ g.rules ∧ r.lhs = A ∧ r.consume = none ∧ r.rhs = []) ∨
      (∃ r : IRule T g.nt g.flag,
        r ∈ g.rules ∧ r.lhs = A ∧ r.consume = none ∧ r.rhs ≠ [] ∧
          ∀ s ∈ r.rhs, ∃ B : g.nt, ∃ push : Option g.flag,
            s = IRhsSymbol.nonterminal B push ∧
              g.IsNullable B
                (match push with | none => f :: ρ | some f' => f' :: f :: ρ)) ∨
      (∃ r : IRule T g.nt g.flag, ∃ B : g.nt,
        r ∈ g.rules ∧ r.lhs = A ∧ r.consume = some f ∧
          r.rhs = [IRhsSymbol.nonterminal B none] ∧ g.IsNullable B ρ) := by
  rw [isNullable_flagsSeparated_iff (g := g) hfs]
  constructor
  · intro h
    rcases h with hnone_empty | hnone_nonempty | hsome
    · exact Or.inl hnone_empty
    · exact Or.inr (Or.inl hnone_nonempty)
    · rcases hsome with ⟨f', ρ', r, B, hstack, hr, hlhs, hconsume, hrhs, hB⟩
      cases hstack
      exact Or.inr (Or.inr ⟨r, B, hr, hlhs, hconsume, hrhs, hB⟩)
  · intro h
    rcases h with hnone_empty | hnone_nonempty | hsome
    · exact Or.inl hnone_empty
    · exact Or.inr (Or.inl hnone_nonempty)
    · rcases hsome with ⟨r, B, hr, hlhs, hconsume, hrhs, hB⟩
      exact Or.inr (Or.inr ⟨f, ρ, r, B, rfl, hr, hlhs, hconsume, hrhs, hB⟩)

/-- An explicit rule `A → ε` makes `A` nullable at every stack. -/
theorem isNullable_of_empty_rule_none {g : IndexedGrammar T}
    {r : IRule T g.nt g.flag} {A : g.nt} (hr : r ∈ g.rules)
    (hlhs : r.lhs = A) (hconsume : r.consume = none) (hrhs : r.rhs = [])
    (σ : List g.flag) :
    g.IsNullable A σ := by
  apply deri_of_tran
  refine ⟨r, [], [], σ, hr, ?_, ?_⟩
  · rw [hconsume, hlhs]
    simp
  · rw [hrhs]
    simp [expandRhs]

/-- An explicit rule `Af → ε` makes `A` nullable at every stack whose top flag is `f`. -/
theorem isNullable_of_empty_rule_some {g : IndexedGrammar T}
    {r : IRule T g.nt g.flag} {A : g.nt} {f : g.flag} (hr : r ∈ g.rules)
    (hlhs : r.lhs = A) (hconsume : r.consume = some f) (hrhs : r.rhs = [])
    (σ : List g.flag) :
    g.IsNullable A (f :: σ) := by
  apply deri_of_tran
  refine ⟨r, [], [], σ, hr, ?_, ?_⟩
  · rw [hconsume, hlhs]
    simp
  · rw [hrhs]
    simp [expandRhs]

/-- The semantic set of nullable stacked nonterminals. -/
def NullableSet (g : IndexedGrammar T) : Set (g.nt × List g.flag) :=
  {p | g.IsNullable p.1 p.2}

/-- One algebraic unfolding of stack-sensitive nullability for flag-separated grammars. -/
def NullableStep (g : IndexedGrammar T) (X : Set (g.nt × List g.flag)) :
    Set (g.nt × List g.flag) :=
  {p |
    (∃ r : IRule T g.nt g.flag,
      r ∈ g.rules ∧ r.lhs = p.1 ∧ r.consume = none ∧ r.rhs = []) ∨
    (∃ r : IRule T g.nt g.flag,
      r ∈ g.rules ∧ r.lhs = p.1 ∧ r.consume = none ∧ r.rhs ≠ [] ∧
        ∀ s ∈ r.rhs, ∃ B : g.nt, ∃ push : Option g.flag,
          s = IRhsSymbol.nonterminal B push ∧
            (B, match push with | none => p.2 | some f => f :: p.2) ∈ X) ∨
    (∃ f : g.flag, ∃ ρ : List g.flag, ∃ r : IRule T g.nt g.flag, ∃ B : g.nt,
      p.2 = f :: ρ ∧ r ∈ g.rules ∧ r.lhs = p.1 ∧ r.consume = some f ∧
        r.rhs = [IRhsSymbol.nonterminal B none] ∧ (B, ρ) ∈ X)}

theorem nullableStep_mono {g : IndexedGrammar T}
    {X Y : Set (g.nt × List g.flag)} (hXY : X ⊆ Y) :
    g.NullableStep X ⊆ g.NullableStep Y := by
  intro p hp
  rcases hp with hnone_empty | hnone_nonempty | hsome
  · exact Or.inl hnone_empty
  · rcases hnone_nonempty with ⟨r, hr, hlhs, hconsume, hrhs_ne, hall⟩
    exact Or.inr (Or.inl ⟨r, hr, hlhs, hconsume, hrhs_ne, fun s hs => by
      rcases hall s hs with ⟨B, push, hsym, hmem⟩
      exact ⟨B, push, hsym, hXY hmem⟩⟩)
  · rcases hsome with ⟨f, ρ, r, B, hstack, hr, hlhs, hconsume, hrhs, hmem⟩
    exact Or.inr (Or.inr ⟨f, ρ, r, B, hstack, hr, hlhs, hconsume, hrhs, hXY hmem⟩)

theorem nullableStep_sound {g : IndexedGrammar T}
    {X : Set (g.nt × List g.flag)}
    (hX : ∀ A : g.nt, ∀ σ : List g.flag, (A, σ) ∈ X → g.IsNullable A σ) :
    g.NullableStep X ⊆ g.NullableSet := by
  intro p hp
  rcases p with ⟨A, σ⟩
  change
    (∃ r : IRule T g.nt g.flag,
      r ∈ g.rules ∧ r.lhs = A ∧ r.consume = none ∧ r.rhs = []) ∨
    (∃ r : IRule T g.nt g.flag,
      r ∈ g.rules ∧ r.lhs = A ∧ r.consume = none ∧ r.rhs ≠ [] ∧
        ∀ s ∈ r.rhs, ∃ B : g.nt, ∃ push : Option g.flag,
          s = IRhsSymbol.nonterminal B push ∧
            (B, match push with | none => σ | some f => f :: σ) ∈ X) ∨
    (∃ f : g.flag, ∃ ρ : List g.flag, ∃ r : IRule T g.nt g.flag, ∃ B : g.nt,
      σ = f :: ρ ∧ r ∈ g.rules ∧ r.lhs = A ∧ r.consume = some f ∧
        r.rhs = [IRhsSymbol.nonterminal B none] ∧ (B, ρ) ∈ X) at hp
  change g.IsNullable A σ
  rcases hp with hnone_empty | hnone_nonempty | hsome
  · rcases hnone_empty with ⟨r, hr, hlhs, hconsume, hrhs⟩
    exact isNullable_of_empty_rule_none hr hlhs hconsume hrhs σ
  · rcases hnone_nonempty with ⟨r, hr, hlhs, hconsume, _hrhs_ne, hall⟩
    apply isNullable_of_rule_all_nullable_none hr hlhs hconsume
    intro s hs
    rcases hall s hs with ⟨B, push, hsym, hmem⟩
    cases push with
    | none =>
        exact ⟨B, none, hsym, hX B σ hmem⟩
    | some f =>
        exact ⟨B, some f, hsym, hX B (f :: σ) hmem⟩
  · rcases hsome with ⟨f, ρ, r, B, hstack, hr, hlhs, hconsume, hrhs, hmem⟩
    rw [hstack]
    exact isNullable_of_pop_rule_nullable_child hr hlhs hconsume hrhs (hX B ρ hmem)

theorem nullableSet_subset_step_flagsSeparated {g : IndexedGrammar T}
    (hfs : g.FlagsSeparated) :
    g.NullableSet ⊆ g.NullableStep g.NullableSet := by
  intro p hp
  rcases p with ⟨A, σ⟩
  change g.IsNullable A σ at hp
  have hcases := (isNullable_flagsSeparated_iff (g := g) hfs (A := A) (σ := σ)).mp hp
  simpa [NullableStep, NullableSet] using hcases

theorem nullableStep_subset_nullableSet {g : IndexedGrammar T} :
    g.NullableStep g.NullableSet ⊆ g.NullableSet := by
  exact nullableStep_sound (g := g) (X := g.NullableSet) (fun A σ h => h)

theorem nullableSet_fixedPoint_flagsSeparated {g : IndexedGrammar T}
    (hfs : g.FlagsSeparated) :
    g.NullableStep g.NullableSet = g.NullableSet := by
  apply Set.Subset.antisymm
  · exact nullableStep_subset_nullableSet (g := g)
  · exact nullableSet_subset_step_flagsSeparated hfs

/-- Finite unfoldings of the nullability equations, starting from no nullable states. -/
def NullableApprox (g : IndexedGrammar T) : ℕ → Set (g.nt × List g.flag)
  | 0 => ∅
  | n + 1 => g.NullableStep (g.NullableApprox n)

theorem nullableApprox_sound (g : IndexedGrammar T) :
    ∀ n : ℕ, g.NullableApprox n ⊆ g.NullableSet := by
  intro n
  induction n with
  | zero =>
      intro p hp
      simp [NullableApprox] at hp
  | succ n ih =>
      exact nullableStep_sound (g := g) (X := g.NullableApprox n)
        (fun A σ h => ih h)

theorem nullableApprox_mono_succ (g : IndexedGrammar T) :
    ∀ n : ℕ, g.NullableApprox n ⊆ g.NullableApprox (n + 1) := by
  intro n
  induction n with
  | zero =>
      intro p hp
      simp [NullableApprox] at hp
  | succ n ih =>
      exact nullableStep_mono (g := g) ih

theorem nullableApprox_mono (g : IndexedGrammar T) {m n : ℕ} (hmn : m ≤ n) :
    g.NullableApprox m ⊆ g.NullableApprox n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  induction k with
  | zero =>
      intro p hp
      simpa using hp
  | succ k ih =>
      intro p hp
      have hsucc :
          g.NullableApprox (m + k) ⊆ g.NullableApprox (m + (k + 1)) := by
        simpa [Nat.add_assoc] using nullableApprox_mono_succ g (m + k)
      exact hsucc (ih (by omega) hp)

theorem nullableApprox_complete_of_derivesIn_flagsSeparated {g : IndexedGrammar T}
    (hfs : g.FlagsSeparated) :
    ∀ n : ℕ, ∀ A : g.nt, ∀ σ : List g.flag,
      g.DerivesIn n [ISym.indexed A σ] [] →
        (A, σ) ∈ g.NullableApprox (n + 1) := by
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih A σ hder
  cases n with
  | zero =>
      simp at hder
  | succ n =>
      have hsplitInput :
          g.DerivesIn (1 + n) [ISym.indexed A σ] [] := by
        simpa [Nat.add_comm] using hder
      rcases derivesIn_split (g := g) (m := 1) (n := n) hsplitInput with
        ⟨mid, hfirst, hrest⟩
      rcases hfirst with ⟨x, hx0, hstep⟩
      have hx : x = [ISym.indexed A σ] := by
        simpa using hx0.symm
      subst x
      rcases hstep with ⟨r, u, v, ρ, hr, hsource, htarget⟩
      cases hc : r.consume with
      | none =>
          rw [hc] at hsource
          rcases singleton_indexed_eq_context hsource with ⟨hu, hv, hA, hσ⟩
          subst u
          subst v
          subst A
          subst σ
          have hmid : mid = g.expandRhs r.rhs ρ := by
            simpa using htarget
          subst mid
          have hrest' : g.DerivesIn n (g.expandRhs r.rhs ρ) [] := by
            simpa using hrest
          change (r.lhs, ρ) ∈ g.NullableStep (g.NullableApprox (n + 1))
          by_cases hrhs : r.rhs = []
          · exact Or.inl ⟨r, hr, rfl, hc, hrhs⟩
          · refine Or.inr (Or.inl ⟨r, hr, rfl, hc, hrhs, ?_⟩)
            intro s hs
            cases s with
            | terminal t =>
                have hmem : (ISym.terminal t : g.ISym) ∈ g.expandRhs r.rhs ρ :=
                  terminal_mem_expandRhs_of_mem (g := g) (σ := ρ) hs
                obtain ⟨m, _hmn, hsingle⟩ :=
                  derivesIn_nil_of_mem (g := g) hrest' hmem
                exact False.elim
                  (not_derives_nil_of_terminal_mem (g := g)
                    (w := [ISym.terminal t]) (t := t) (by simp)
                    (derives_of_derivesIn (g := g) hsingle))
            | nonterminal B push =>
                refine ⟨B, push, rfl, ?_⟩
                obtain ⟨m, hmn, hchild⟩ :=
                  derivesIn_nil_of_expandRhs_nonterminal_mem
                    (g := g) (n := n) (rhs := r.rhs) (σ := ρ) hrest' hs
                cases push with
                | none =>
                    have hchildApprox :
                        (B, ρ) ∈ g.NullableApprox (m + 1) :=
                      ih m (by omega) B ρ (by simpa using hchild)
                    exact nullableApprox_mono g (by omega) hchildApprox
                | some f =>
                    have hchildApprox :
                        (B, f :: ρ) ∈ g.NullableApprox (m + 1) :=
                      ih m (by omega) B (f :: ρ) (by simpa using hchild)
                    exact nullableApprox_mono g (by omega) hchildApprox
      | some f =>
          rw [hc] at hsource
          rcases singleton_indexed_eq_context hsource with ⟨hu, hv, hA, hσ⟩
          subst u
          subst v
          subst A
          subst σ
          have hmid : mid = g.expandRhs r.rhs ρ := by
            simpa using htarget
          subst mid
          have hrest' : g.DerivesIn n (g.expandRhs r.rhs ρ) [] := by
            simpa using hrest
          have hsomeFlag : r.consume.isSome := by
            simp [hc]
          rcases (hfs r hr).1 hsomeFlag with ⟨B, hrhs⟩
          have hchild : g.DerivesIn n [ISym.indexed B ρ] [] := by
            simpa [hrhs, expandRhs] using hrest'
          have hchildApprox : (B, ρ) ∈ g.NullableApprox (n + 1) :=
            ih n (by omega) B ρ hchild
          change (r.lhs, f :: ρ) ∈ g.NullableStep (g.NullableApprox (n + 1))
          exact Or.inr (Or.inr ⟨f, ρ, r, B, rfl, hr, rfl, hc, hrhs, hchildApprox⟩)

theorem nullableSet_subset_iUnion_nullableApprox_flagsSeparated {g : IndexedGrammar T}
    (hfs : g.FlagsSeparated) :
    g.NullableSet ⊆ {p : g.nt × List g.flag | ∃ n : ℕ, p ∈ g.NullableApprox n} := by
  intro p hp
  rcases p with ⟨A, σ⟩
  change g.IsNullable A σ at hp
  obtain ⟨n, hder⟩ := exists_derivesIn_of_derives (g := g) hp
  exact ⟨n + 1, nullableApprox_complete_of_derivesIn_flagsSeparated
    (g := g) hfs n A σ hder⟩

theorem nullableSet_eq_iUnion_nullableApprox_flagsSeparated {g : IndexedGrammar T}
    (hfs : g.FlagsSeparated) :
    g.NullableSet = {p : g.nt × List g.flag | ∃ n : ℕ, p ∈ g.NullableApprox n} := by
  apply Set.Subset.antisymm
  · exact nullableSet_subset_iUnion_nullableApprox_flagsSeparated hfs
  · intro p hp
    rcases hp with ⟨n, hn⟩
    exact nullableApprox_sound g n hn

/-- A grammar is ε-free exactly when no stacked nonterminal is nullable. -/
theorem noEpsilon_iff_no_isNullable {g : IndexedGrammar T} :
    g.NoEpsilon' ↔ ∀ A : g.nt, ∀ σ : List g.flag, ¬ g.IsNullable A σ := by
  constructor
  · intro hne A σ
    exact not_isNullable_of_noEpsilon hne A σ
  · intro hno r hr hrhs
    cases hc : r.consume with
    | none =>
        exact hno r.lhs []
          (isNullable_of_empty_rule_none hr rfl hc hrhs [])
    | some f =>
        exact hno r.lhs (f :: [])
          (isNullable_of_empty_rule_some hr rfl hc hrhs [])

/-- If a grammar is already ε-free, it is an ε-free equivalent of itself. -/
theorem exists_noEpsilon_all (g : IndexedGrammar T) (hne : g.NoEpsilon') :
    ∃ g' : IndexedGrammar T,
      g'.NoEpsilon' ∧
      (g.StartNotOnRhs' → g'.StartNotOnRhs') ∧
      ∀ w : List T, (g'.Generates w ↔ g.Generates w) := by
  exact ⟨g, hne, fun h => h, fun _ => Iff.rfl⟩

theorem exists_noEpsilon (g : IndexedGrammar T) (hne : g.NoEpsilon') :
    ∃ g' : IndexedGrammar T,
      g'.NoEpsilon' ∧
      (g.StartNotOnRhs' → g'.StartNotOnRhs') ∧
      ∀ w : List T, w ≠ [] → (g'.Generates w ↔ g.Generates w) := by
  obtain ⟨g', hne', hfresh, hlang⟩ := g.exists_noEpsilon_all hne
  exact ⟨g', hne', hfresh, fun w _ => hlang w⟩

end EpsilonElim

end IndexedGrammar
