import Mathlib
import Langlib.Grammars.Indexed.Definition

/-! # Fresh Start Symbol for Indexed Grammars

This file proves that every indexed grammar can be transformed into one whose
start symbol does not appear on the right-hand side of any production rule,
while preserving the generated language.

This is Step 1 of Aho's Normal Form theorem for indexed grammars.

## References

* A. V. Aho, "Indexed grammars — an extension of context-free grammars", *JACM* 15(4), 1968.
-/

open List Relation

variable {T : Type}

namespace IndexedGrammar

section FreshStart

variable (g : IndexedGrammar T)

/-! ### Lifting functions -/

/-- Lift an RHS symbol to the `Option` nonterminal type. -/
def liftRhsSym : IRhsSymbol T g.nt g.flag → IRhsSymbol T (Option g.nt) g.flag
  | .terminal t => .terminal t
  | .nonterminal n f => .nonterminal (some n) f

/-- Lift a production rule to the `Option` nonterminal type. -/
def liftRule (r : IRule T g.nt g.flag) : IRule T (Option g.nt) g.flag where
  lhs := some r.lhs
  consume := r.consume
  rhs := r.rhs.map g.liftRhsSym

/-- The grammar with a fresh start symbol `none : Option g.nt`. Has one start rule
    `S' → S` (where `S' = none`, `S = some g.initial`) and all original rules lifted. -/
def freshStart : IndexedGrammar T where
  nt := Option g.nt
  flag := g.flag
  initial := none
  rules :=
    ⟨none, none, [.nonterminal (some g.initial) none]⟩ :: g.rules.map g.liftRule


/-- Lift a sentential-form symbol from `g` to `freshStart g`. -/
def liftISym : g.ISym → (g.freshStart).ISym
  | .terminal t => .terminal t
  | .indexed n σ => .indexed (some n) σ

/-! ### Key helper: expandRhs commutes with lifting -/

theorem expandRhs_liftRhsSym (rhs : List (IRhsSymbol T g.nt g.flag)) (σ : List g.flag) :
    (expandRhs g rhs σ).map g.liftISym =
    expandRhs g.freshStart (rhs.map g.liftRhsSym) σ := by
  unfold expandRhs;
  unfold IndexedGrammar.liftRhsSym; aesop;

theorem map_liftISym_terminal (w : List T) :
    w.map (ISym.terminal (g := g.freshStart)) =
    (w.map (ISym.terminal (g := g))).map g.liftISym := by
  induction w <;> aesop

/-! ### Forward direction: g.Language ⊆ (freshStart g).Language -/

/-
Lifting preserves one-step transforms.
-/
theorem freshStart_lift_transforms {w₁ w₂ : List g.ISym}
    (h : g.Transforms w₁ w₂) :
    (g.freshStart).Transforms (w₁.map g.liftISym) (w₂.map g.liftISym) := by
  obtain ⟨ r, u, v, σ, hr, hw₁, hw₂ ⟩ := h;
  use ⟨some r.lhs, r.consume, r.rhs.map g.liftRhsSym⟩;
  refine' ⟨ map g.liftISym u, map g.liftISym v, σ, _, _, _ ⟩;
  · exact List.mem_cons_of_mem _ ( List.mem_map.mpr ⟨ r, hr, rfl ⟩ );
  · grind +locals;
  · rw [ hw₂, List.map_append, List.map_append, expandRhs_liftRhsSym ]

/-
Lifting preserves multi-step derivations.
-/
theorem freshStart_lift_derives {w₁ w₂ : List g.ISym}
    (h : g.Derives w₁ w₂) :
    (g.freshStart).Derives (w₁.map g.liftISym) (w₂.map g.liftISym) := by
  induction h;
  · constructor;
  · exact deri_of_deri_tran ‹_› ( freshStart_lift_transforms _ ‹_› )

/-
Forward language inclusion.
-/
theorem freshStart_language_forward {w : List T}
    (h : w ∈ g.Language) : w ∈ (g.freshStart).Language := by
  -- Apply the start rule to get [indexed (some g.initial) []].
  have h_start : (g.freshStart).Transforms [ISym.indexed none []] [ISym.indexed (some g.initial) []] := by
    use ⟨none, none, [.nonterminal (some g.initial) none]⟩;
    exact ⟨ [ ], [ ], [ ], by unfold IndexedGrammar.freshStart; aesop ⟩;
  -- Apply the deri_of_tran_deri theorem to combine the derivations.
  apply deri_of_tran_deri h_start;
  convert freshStart_lift_derives g h;
  rw [map_liftISym_terminal]

/-! ### Backward direction: (freshStart g).Language ⊆ g.Language -/

/-- A sentential form of `freshStart g` is "proper" if it contains no occurrence of the
    fresh start symbol `none`. -/
def Proper (w : List (g.freshStart).ISym) : Prop :=
  ∀ s ∈ w, ∀ σ, s ≠ ISym.indexed none σ

/-
After lifting, a sentential form is proper.
-/
theorem proper_of_map_liftISym (w : List g.ISym) :
    g.Proper (w.map g.liftISym) := by
  intro s hs σ h;
  rw [ List.mem_map ] at hs;
  rcases hs with ⟨ a, ha, rfl ⟩ ; cases a <;> cases h

/-
Proper sentential forms remain proper after a transform step.
-/
theorem proper_of_proper_transforms {w₁ w₂ : List (g.freshStart).ISym}
    (hp : g.Proper w₁) (ht : (g.freshStart).Transforms w₁ w₂) :
    g.Proper w₂ := by
  contrapose! hp;
  obtain ⟨ r, u, v, σ, hr, hw₁, hw₂ ⟩ := ht;
  rcases r with ⟨ lhs, consume, rhs ⟩;
  rcases lhs with ( _ | lhs ) <;> simp_all +decide [ IndexedGrammar.freshStart ];
  · rcases consume with ( _ | consume ) <;> simp_all +decide [ IndexedGrammar.Proper ];
    · exact ⟨ σ, Or.inr <| Or.inl rfl ⟩;
    · exact ⟨ _, Or.inr <| Or.inl rfl ⟩;
  · rcases consume with ( _ | f ) <;> simp_all +decide [ IndexedGrammar.Proper ];
    · obtain ⟨ x, hx ⟩ := hp;
      rcases hx with ( hx | hx | hx );
      · exact ⟨ x, Or.inl hx ⟩;
      · unfold IndexedGrammar.expandRhs at hx; simp_all +decide [ IndexedGrammar.liftRule ] ;
        obtain ⟨ a, ha, ha' ⟩ := hx; rcases a with ( _ | ⟨ n, _ | f ⟩ ) <;> simp_all +decide ;
        · obtain ⟨ a, ha₁, ha₂, ha₃, rfl ⟩ := hr; simp_all +decide [ IndexedGrammar.liftRhsSym ] ;
          obtain ⟨ s, hs₁, hs₂ ⟩ := ha; rcases s with ( _ | ⟨ n, _ | f ⟩ ) <;> simp_all +decide ;
        · rcases hr with ⟨ r, hr₁, hr₂, hr₃, rfl ⟩ ; simp_all +decide [ IndexedGrammar.liftRhsSym ] ;
          rcases ha with ⟨ a, ha₁, ha₂ ⟩ ; rcases a with ( _ | ⟨ n, _ | f ⟩ ) <;> simp_all +decide ;
      · exact ⟨ x, Or.inr hx ⟩;
    · obtain ⟨ x, hx ⟩ := hp;
      unfold IndexedGrammar.expandRhs at hx; simp_all +decide [ List.mem_map ] ;
      rcases hx with ( hx | hx | hx );
      · exact ⟨ x, Or.inl hx ⟩;
      · rcases hx with ⟨ a, ha, hx ⟩ ; rcases a with ( _ | ⟨ n, _ | f ⟩ ) <;> simp_all +decide [ IndexedGrammar.liftRule ] ;
        · rcases hr with ⟨ r, hr₁, hr₂, hr₃, rfl ⟩ ; simp_all +decide [ IndexedGrammar.liftRhsSym ] ;
          rcases ha with ⟨ a, ha₁, ha₂ ⟩ ; rcases a with ( _ | ⟨ n, _ | f ⟩ ) <;> simp_all +decide [ IndexedGrammar.liftRhsSym ] ;
        · rcases hr with ⟨ r, hr₁, hr₂, hr₃, rfl ⟩ ; simp_all +decide [ IndexedGrammar.liftRhsSym ] ;
          rcases ha with ⟨ a, ha₁, ha₂ ⟩ ; rcases a with ( _ | ⟨ n, _ | f ⟩ ) <;> simp_all +decide [ IndexedGrammar.liftRhsSym ] ;
      · exact ⟨ x, Or.inr hx ⟩

/-
Proper sentential forms remain proper after any number of derivation steps.
-/
theorem proper_of_proper_derives {w₁ w₂ : List (g.freshStart).ISym}
    (hp : g.Proper w₁) (hd : (g.freshStart).Derives w₁ w₂) :
    g.Proper w₂ := by
  induction hd;
  · assumption;
  · exact proper_of_proper_transforms g ‹_› ‹_›

/-- Unlift a sentential-form symbol. For proper forms, this is the inverse of `liftISym`. -/
noncomputable def unliftISym [Inhabited T] : (g.freshStart).ISym → g.ISym
  | .terminal t => .terminal t
  | .indexed (some n) σ => .indexed n σ
  | .indexed none _ => .terminal default  -- junk; never used on proper forms

/-- Unlift a proper sentential form. -/
noncomputable def unliftSF [Inhabited T] (w : List (g.freshStart).ISym) : List g.ISym :=
  w.map g.unliftISym

/-
Roundtrip: unlift ∘ lift = id.
-/
theorem unlift_lift [Inhabited T] (s : g.ISym) : g.unliftISym (g.liftISym s) = s := by
  cases s <;> aesop

/-
Roundtrip on lists: unliftSF ∘ map liftISym = id.
-/
theorem unliftSF_map_liftISym [Inhabited T] (w : List g.ISym) :
    g.unliftSF (w.map g.liftISym) = w := by
  unfold unliftSF;
  rw [ List.map_map ];
  exact List.map_congr_left ( fun x hx => unlift_lift g x ) ▸ by simp +decide ;

/-
For a proper transform, the corresponding unlift is a transform in the original grammar.
-/
theorem freshStart_unlift_transforms [Inhabited T] {w₁ w₂ : List (g.freshStart).ISym}
    (hp : g.Proper w₁)
    (ht : (g.freshStart).Transforms w₁ w₂) :
    g.Transforms (g.unliftSF w₁) (g.unliftSF w₂) := by
  obtain ⟨ r, u, v, σ, hr, hw₁, hw₂ ⟩ := ht;
  -- Since r is a rule in the freshStart grammar, and w₁ is proper, r cannot be the start rule.
  have hr_not_start : r ≠ ⟨none, none, [.nonterminal (some g.initial) none]⟩ := by
    intro h; simp_all +decide [ IndexedGrammar.freshStart ] ;
    exact hp _ ( List.mem_append_right _ ( List.mem_cons_self ) ) _ rfl;
  -- Since r is not the start rule, it must be a lifted rule from the original grammar.
  obtain ⟨r', hr'⟩ : ∃ r' ∈ g.rules, r = g.liftRule r' := by
    unfold IndexedGrammar.freshStart at hr; aesop;
  -- Since u and v are lists of symbols in the freshStart grammar, we can write them as u = u'.map liftISym and v = v'.map liftISym for some u', v' in the original grammar.
  obtain ⟨u', v', hu', hv'⟩ : ∃ u' v' : List g.ISym, u = u'.map g.liftISym ∧ v = v'.map g.liftISym := by
    have h_lift : ∀ s ∈ u ++ v, ∃ s' : g.ISym, s = g.liftISym s' := by
      have h_lift : ∀ s ∈ w₁, ∃ s' : g.ISym, s = g.liftISym s' := by
        intro s hs; specialize hp s hs; rcases s with ( _ | _ | s ) <;> simp_all +decide ;
        · exact ⟨ ISym.terminal _, rfl ⟩;
        · exact ⟨ ISym.indexed s _, rfl ⟩;
      cases r ; aesop;
    have h_lift : ∀ l : List (g.freshStart).ISym, (∀ s ∈ l, ∃ s' : g.ISym, s = g.liftISym s') → ∃ l' : List g.ISym, l = l'.map g.liftISym := by
      intro l hl; induction' l with s l ih <;> simp_all +decide ;
      rcases hl.1 with ⟨ s', rfl ⟩ ; rcases ih with ⟨ l', rfl ⟩ ; exact ⟨ s' :: l', by simp +decide ⟩ ;
    exact Exists.elim ( h_lift u fun s hs => by solve_by_elim [ List.mem_append_left ] ) fun u' hu' => Exists.elim ( h_lift v fun s hs => by solve_by_elim [ List.mem_append_right ] ) fun v' hv' => ⟨ u', v', hu', hv' ⟩;
  use r', u', v', σ;
  rcases r' with ⟨ lhs, consume, rhs ⟩ ; simp_all +decide [ IndexedGrammar.liftRule ] ;
  cases consume <;> simp_all +decide [ IndexedGrammar.unliftSF ];
  · rw [ ← expandRhs_liftRhsSym ];
    simp +decide [ Function.comp, unlift_lift ];
    rw [ show g.unliftISym ∘ g.liftISym = id from funext fun x => unlift_lift g x ] ; aesop;
  · rw [ ← expandRhs_liftRhsSym ];
    simp +decide [ Function.comp_def, unlift_lift ];
    rfl

/-
For a proper derivation, the corresponding unlift is a derivation in the original grammar.
-/
theorem freshStart_unlift_derives [Inhabited T] {w₁ w₂ : List (g.freshStart).ISym}
    (hp : g.Proper w₁)
    (hd : (g.freshStart).Derives w₁ w₂) :
    g.Derives (g.unliftSF w₁) (g.unliftSF w₂) := by
  induction hd;
  · exact deri_self g (g.unliftSF w₁)
  · rename_i h₁ h₂ h₃;
    apply deri_of_deri_tran h₃;
    apply freshStart_unlift_transforms;
    · exact proper_of_proper_derives g hp h₁
    · assumption

/-
The first step from `[indexed none []]` must produce `[indexed (some g.initial) []]`.
-/
theorem freshStart_first_step {w : List (g.freshStart).ISym}
    (ht : (g.freshStart).Transforms [.indexed none []] w) :
    w = [.indexed (some g.initial) []] := by
  obtain ⟨ r, u, v, σ, hr, hu, hv ⟩ := ht; rcases r with ⟨ lhs, consume, rhs ⟩ ;
  cases u <;> cases v <;> cases consume <;> simp_all +decide;
  unfold IndexedGrammar.freshStart at hr; simp_all +decide [ List.mem_cons ] ;
  unfold IndexedGrammar.liftRule at hr; aesop;

/-
Terminal forms unlift correctly.
-/
theorem unliftSF_terminal [Inhabited T] (w : List T) :
    g.unliftSF (w.map (ISym.terminal (g := g.freshStart))) =
    w.map (ISym.terminal (g := g)) := by
  unfold unliftSF;
  simp +zetaDelta at *;
  exact?

/-
Backward language inclusion.
-/
theorem freshStart_language_backward [Inhabited T] {w : List T}
    (h : w ∈ (g.freshStart).Language) : w ∈ g.Language := by
  obtain ⟨hw₁, hw₂⟩ : ∃ w₁, (g.freshStart).Derives [.indexed none []] w₁ ∧ w₁ = w.map (ISym.terminal (g := g.freshStart)) := by
    exact ⟨ _, h, rfl ⟩;
  obtain ⟨hw₁, hw₂⟩ := hw₂.left.cases_head;
  · cases w <;> aesop;
  · rename_i h;
    obtain ⟨ c, hc₁, hc₂ ⟩ := h;
    have hc₃ : c = [.indexed (some g.initial) []] := by
      grind +suggestions;
    have hc₄ : g.Proper c := by
      simp [hc₃, Proper];
    have hc₅ : g.Derives (g.unliftSF c) (g.unliftSF hw₁) := by
      exact freshStart_unlift_derives g hc₄ hc₂
    unfold IndexedGrammar.unliftSF at *; aesop;

/-! ### Main result -/

/-- The fresh-start grammar generates the same language as the original. -/
theorem freshStart_language [Inhabited T] : (g.freshStart).Language = g.Language := by
  ext w
  exact ⟨freshStart_language_backward g, freshStart_language_forward g⟩

/-
The fresh start symbol does not appear on any right-hand side.
-/
theorem freshStart_startNotOnRhs : (g.freshStart).StartNotOnRhs' := by
  unfold IndexedGrammar.StartNotOnRhs';
  simp [ IndexedGrammar.freshStart, IndexedGrammar.liftRule ];
  intro r hr s hs; cases s <;> simp +decide [ IndexedGrammar.liftRhsSym ] ;

end FreshStart

end IndexedGrammar