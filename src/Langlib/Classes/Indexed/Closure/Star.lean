module

public import Langlib.Classes.Indexed.Definition
public import Langlib.Grammars.Indexed.NormalForm.Derivation
public import Langlib.Utilities.ClosurePredicates
import Mathlib.Tactic

@[expose]
public section

/-!
# Indexed Languages Are Closed Under Kleene Star

Given an indexed grammar `g`, the star grammar adds a fresh start nonterminal with rules
`S⋆ → S S⋆` and `S⋆ → ε`, and otherwise contains a lifted copy of every rule of `g`.
-/

open List

variable {T : Type}

private inductive StarNT (N : Type) where
  | start : StarNT N
  | original : N → StarNT N

private def starLiftRhs {N F : Type} :
    IRhsSymbol T N F → IRhsSymbol T (StarNT N) F
  | .terminal t => .terminal t
  | .nonterminal n push => .nonterminal (StarNT.original n) push

private def starLiftRule {N F : Type} (r : IRule T N F) :
    IRule T (StarNT N) F :=
  { lhs := StarNT.original r.lhs
    consume := r.consume
    rhs := r.rhs.map starLiftRhs }

private def starLoopRule (g : IndexedGrammar T) : IRule T (StarNT g.nt) g.flag :=
  { lhs := StarNT.start
    consume := none
    rhs :=
      [ .nonterminal (StarNT.original g.initial) none
      , .nonterminal StarNT.start none ] }

private def starStopRule (g : IndexedGrammar T) : IRule T (StarNT g.nt) g.flag :=
  { lhs := StarNT.start, consume := none, rhs := [] }

private def indexedStar (g : IndexedGrammar T) : IndexedGrammar T where
  nt := StarNT g.nt
  flag := g.flag
  initial := StarNT.start
  rules := [starLoopRule g, starStopRule g] ++ g.rules.map starLiftRule

private def starLiftISym (g : IndexedGrammar T) :
    g.ISym → (indexedStar g).ISym
  | .terminal t => .terminal t
  | .indexed n σ => .indexed (StarNT.original n) σ

private lemma starLiftISym_injective (g : IndexedGrammar T) :
    Function.Injective (starLiftISym g) := by
  intro x y h
  cases x with
  | terminal x =>
      cases y with
      | terminal y => simpa [starLiftISym] using h
      | indexed y τ => simp [starLiftISym] at h
  | indexed x σ =>
      cases y with
      | terminal y => simp [starLiftISym] at h
      | indexed y τ =>
          simp [starLiftISym] at h ⊢
          exact ⟨by injection h.1, h.2⟩

private lemma star_lift_expandRhs (g : IndexedGrammar T)
    (rhs : List (IRhsSymbol T g.nt g.flag)) (σ : List g.flag) :
    (g.expandRhs rhs σ).map (starLiftISym g) =
      (indexedStar g).expandRhs (rhs.map starLiftRhs) σ := by
  unfold IndexedGrammar.expandRhs
  rw [List.map_map, List.map_map]
  congr! 2
  funext s
  cases s with
  | terminal t => rfl
  | nonterminal n push => cases push <;> rfl

private lemma star_lift_tran (g : IndexedGrammar T) {w₁ w₂ : List g.ISym}
    (h : g.Transforms w₁ w₂) :
    (indexedStar g).Transforms
      (w₁.map (starLiftISym g)) (w₂.map (starLiftISym g)) := by
  obtain ⟨r, u, v, σ, hr, hw₁, hw₂⟩ := h
  refine ⟨starLiftRule r, u.map (starLiftISym g), v.map (starLiftISym g), σ,
    ?_, ?_, ?_⟩
  · simp [indexedStar]
    exact Or.inr (Or.inr ⟨r, hr, rfl⟩)
  · cases hc : r.consume with
    | none =>
        rw [hc] at hw₁
        simpa [starLiftRule, starLiftISym, hc, List.map_append] using
          congrArg (List.map (starLiftISym g)) hw₁
    | some f =>
        rw [hc] at hw₁
        simpa [starLiftRule, starLiftISym, hc, List.map_append] using
          congrArg (List.map (starLiftISym g)) hw₁
  · rw [hw₂]
    simp [starLiftRule, star_lift_expandRhs, List.map_append]

private lemma star_lift_deri (g : IndexedGrammar T) {w₁ w₂ : List g.ISym}
    (h : g.Derives w₁ w₂) :
    (indexedStar g).Derives
      (w₁.map (starLiftISym g)) (w₂.map (starLiftISym g)) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ ht ih => exact ih.tail (star_lift_tran g ht)

private lemma star_loop_tran (g : IndexedGrammar T) :
    (indexedStar g).Transforms
      [.indexed StarNT.start []]
      [.indexed (StarNT.original g.initial) [], .indexed StarNT.start []] := by
  refine ⟨starLoopRule g, [], [], [], ?_, ?_, ?_⟩
  · simp [indexedStar]
  · simp [starLoopRule]
  · simp [starLoopRule, IndexedGrammar.expandRhs]

private lemma star_stop_tran (g : IndexedGrammar T) :
    (indexedStar g).Transforms [.indexed StarNT.start []] [] := by
  refine ⟨starStopRule g, [], [], [], ?_, ?_, ?_⟩
  · simp [indexedStar]
  · simp [starStopRule]
  · simp [starStopRule, IndexedGrammar.expandRhs]

private lemma indexedStar_generates_flatten (g : IndexedGrammar T)
    (words : List (List T)) (hwords : ∀ w ∈ words, g.Generates w) :
    (indexedStar g).Generates words.flatten := by
  induction words with
  | nil =>
      unfold IndexedGrammar.Generates
      simpa using IndexedGrammar.deri_of_tran (star_stop_tran g)
  | cons w words ih =>
      have hw : g.Generates w := hwords w (by simp)
      have htail : ∀ x ∈ words, g.Generates x := by
        intro x hx
        exact hwords x (by simp [hx])
      unfold IndexedGrammar.Generates at hw ⊢
      have hstart := IndexedGrammar.deri_of_tran (star_loop_tran g)
      have hword := IndexedGrammar.deri_with_suffix
        ([IndexedGrammar.ISym.indexed StarNT.start []] : List (indexedStar g).ISym)
        (star_lift_deri g hw)
      have hrest := IndexedGrammar.deri_with_prefix
        (w.map (IndexedGrammar.ISym.terminal (g := indexedStar g))) (ih htail)
      exact hstart.trans (hword.trans (by
        simpa [starLiftISym, List.map_map, List.map_append] using hrest))

private lemma map_eq_append_singleton_of_injective {α β : Type} {f : α → β}
    (hf : Function.Injective f) {xs : List α} {x : α} {u v : List β}
    (h : xs.map f = u ++ [f x] ++ v) :
    ∃ xs₁ xs₂ : List α,
      xs = xs₁ ++ [x] ++ xs₂ ∧ u = xs₁.map f ∧ v = xs₂.map f := by
  have h' : xs.map f = u ++ f x :: v := by simpa using h
  obtain ⟨xs₁, rest, hxs, hu, hrest⟩ := List.map_eq_append_iff.mp h'
  cases rest with
  | nil => simp at hrest
  | cons y xs₂ =>
      simp only [List.map_cons, List.cons.injEq] at hrest
      obtain ⟨hy, hv⟩ := hrest
      have hyx : y = x := hf hy
      subst y
      exact ⟨xs₁, xs₂, by simpa [List.singleton_append] using hxs, hu.symm, hv.symm⟩

private lemma star_unlift_tran (g : IndexedGrammar T) {w₁ : List g.ISym}
    {w₂ : List (indexedStar g).ISym}
    (h : (indexedStar g).Transforms (w₁.map (starLiftISym g)) w₂) :
    ∃ w₂g : List g.ISym,
      w₂ = w₂g.map (starLiftISym g) ∧ g.Transforms w₁ w₂g := by
  obtain ⟨r, u, v, σ, hr, hw₁, hw₂⟩ := h
  simp [indexedStar] at hr
  rcases hr with hloop | hstop | hlift
  · subst r
    have hmem : (IndexedGrammar.ISym.indexed StarNT.start σ : (indexedStar g).ISym) ∈
        w₁.map (starLiftISym g) := by
      cases starLoopRule g |>.consume <;> simp_all [starLoopRule]
    obtain ⟨s, _, hs⟩ := List.mem_map.mp hmem
    cases s <;> simp [starLiftISym] at hs
  · subst r
    have hmem : (IndexedGrammar.ISym.indexed StarNT.start σ : (indexedStar g).ISym) ∈
        w₁.map (starLiftISym g) := by
      cases starStopRule g |>.consume <;> simp_all [starStopRule]
    obtain ⟨s, _, hs⟩ := List.mem_map.mp hmem
    cases s <;> simp [starLiftISym] at hs
  · obtain ⟨rg, hrg, rfl⟩ := hlift
    cases hc : rg.consume with
    | none =>
        simp [starLiftRule, hc] at hw₁ hw₂
        obtain ⟨xs₁, xs₂, hxs, hu, hv⟩ :=
          map_eq_append_singleton_of_injective (starLiftISym_injective g)
            (xs := w₁) (x := IndexedGrammar.ISym.indexed rg.lhs σ)
            (by simpa [starLiftISym, List.singleton_append] using hw₁)
        refine ⟨xs₁ ++ g.expandRhs rg.rhs σ ++ xs₂, ?_, ?_⟩
        · rw [hw₂, hu, hv]
          simp [star_lift_expandRhs, List.map_append, List.append_assoc]
        · refine ⟨rg, xs₁, xs₂, σ, hrg, ?_, rfl⟩
          simp [hc, hxs]
    | some f =>
        simp [starLiftRule, hc] at hw₁ hw₂
        obtain ⟨xs₁, xs₂, hxs, hu, hv⟩ :=
          map_eq_append_singleton_of_injective (starLiftISym_injective g)
            (xs := w₁) (x := IndexedGrammar.ISym.indexed rg.lhs (f :: σ))
            (by simpa [starLiftISym, List.singleton_append] using hw₁)
        refine ⟨xs₁ ++ g.expandRhs rg.rhs σ ++ xs₂, ?_, ?_⟩
        · rw [hw₂, hu, hv]
          simp [star_lift_expandRhs, List.map_append, List.append_assoc]
        · refine ⟨rg, xs₁, xs₂, σ, hrg, ?_, rfl⟩
          simp [hc, hxs]

private lemma star_unlift_derivesIn (g : IndexedGrammar T) {n : ℕ}
    {w₁ : List g.ISym} {w₂ : List (indexedStar g).ISym}
    (h : (indexedStar g).DerivesIn n (w₁.map (starLiftISym g)) w₂) :
    ∃ w₂g : List g.ISym,
      w₂ = w₂g.map (starLiftISym g) ∧ g.DerivesIn n w₁ w₂g := by
  induction n generalizing w₂ with
  | zero =>
      have hw := h
      simp only [IndexedGrammar.derivesIn_zero] at hw
      exact ⟨w₁, hw.symm, rfl⟩
  | succ n ih =>
      rcases h with ⟨mid, hprev, hstep⟩
      obtain ⟨midg, rfl, hprevg⟩ := ih hprev
      obtain ⟨w₂g, hw₂, hstepg⟩ := star_unlift_tran g hstep
      exact ⟨w₂g, hw₂, ⟨midg, hprevg, hstepg⟩⟩

private lemma starLiftISym_terminal_inv (g : IndexedGrammar T)
    {wg : List g.ISym} {w : List T}
    (h : wg.map (starLiftISym g) =
      w.map (IndexedGrammar.ISym.terminal (g := indexedStar g))) :
    wg = w.map (IndexedGrammar.ISym.terminal (g := g)) := by
  induction wg generalizing w with
  | nil => cases w <;> simp_all
  | cons s wg ih =>
      cases w with
      | nil => simp at h
      | cons a w =>
          cases s <;> simp [starLiftISym] at h ⊢
          exact ⟨h.1, ih h.2⟩

private lemma star_first_step (g : IndexedGrammar T)
    {b : List (indexedStar g).ISym}
    (h : (indexedStar g).Transforms [.indexed StarNT.start []] b) :
    b = [.indexed (StarNT.original g.initial) [], .indexed StarNT.start []] ∨ b = [] := by
  obtain ⟨r, u, v, σ, hr, hw₁, hw₂⟩ := h
  rcases r with ⟨lhs, consume, rhs⟩
  cases consume with
  | none =>
      cases u with
      | nil =>
          cases v with
          | nil =>
              simp at hw₁
              obtain ⟨rfl, rfl⟩ := hw₁
              simp [indexedStar] at hr
              rcases hr with hloop | hstop | hlift
              · left
                rw [hloop] at hw₂
                simpa [IndexedGrammar.expandRhs] using hw₂
              · right
                rw [hstop] at hw₂
                simpa [IndexedGrammar.expandRhs] using hw₂
              · obtain ⟨a, _ha, hbad, _hconsume, _hrhs⟩ := hlift
          | cons vh vt => simp at hw₁
      | cons uh ut => simp at hw₁
  | some f =>
      cases u <;> cases v <;> simp at hw₁

private abbrev indexedStarTarget (g : IndexedGrammar T) : Language T :=
  KStar.kstar g.Language

private theorem indexedStar_language_subset (g : IndexedGrammar T) :
    Set.Subset (indexedStar g).Language (indexedStarTarget g) := by
  intro w hw
  change (indexedStar g).Generates w at hw
  rw [IndexedGrammar.generates_iff_exists_derivesIn] at hw
  obtain ⟨n, hn⟩ := hw
  induction n using Nat.strong_induction_on generalizing w with
  | h n ih =>
      cases n with
      | zero =>
          simp only [IndexedGrammar.derivesIn_zero] at hn
          cases w <;> simp [indexedStar] at hn
      | succ n =>
          have hn' : (indexedStar g).DerivesIn (1 + n)
              [IndexedGrammar.ISym.indexed (indexedStar g).initial []]
              (w.map IndexedGrammar.ISym.terminal) := by
            rw [Nat.one_add]
            exact hn
          obtain ⟨b, hfirst, hrest⟩ := IndexedGrammar.derivesIn_split hn'
          rcases hfirst with ⟨mid, hzero, hstep⟩
          have hmid : mid =
              ([IndexedGrammar.ISym.indexed StarNT.start []] : List (indexedStar g).ISym) := by
            simpa using hzero.symm
          subst mid
          rcases star_first_step g hstep with hloop | hstop
          · subst b
            obtain ⟨m, k, w₁, w₂, hmk, hw, hleft, hright⟩ :=
              IndexedGrammar.derivesIn_append_to_terminals_split
                (g := indexedStar g)
                (u := [IndexedGrammar.ISym.indexed (StarNT.original g.initial) []])
                (v := [IndexedGrammar.ISym.indexed StarNT.start []])
                (w := w) hrest
            have hk : k < n + 1 := by omega
            have hw₂star : w₂ ∈ KStar.kstar g.Language := ih k hk hright
            have hleft' : (indexedStar g).DerivesIn m
                (([IndexedGrammar.ISym.indexed g.initial []] : List g.ISym).map
                  (starLiftISym g))
                (w₁.map (IndexedGrammar.ISym.terminal (g := indexedStar g))) := by
              simpa [starLiftISym] using hleft
            obtain ⟨endg, hend, hleftg⟩ := star_unlift_derivesIn g hleft'
            have hendg : endg =
                w₁.map (IndexedGrammar.ISym.terminal (g := g)) :=
              starLiftISym_terminal_inv g hend.symm
            have hw₁g : w₁ ∈ g.Language := by
              change g.Generates w₁
              rw [IndexedGrammar.generates_iff_exists_derivesIn]
              exact ⟨m, by simpa [hendg] using hleftg⟩
            rw [Language.mem_kstar] at hw₂star ⊢
            obtain ⟨words, hw₂, hwords⟩ := hw₂star
            refine ⟨w₁ :: words, ?_, ?_⟩
            · simp [hw, hw₂]
            · intro x hx
              simp only [List.mem_cons] at hx
              rcases hx with rfl | hx
              · exact hw₁g
              · exact hwords x hx
          · subst b
            have hnil := IndexedGrammar.derivesIn_nil_left_eq
              (g := indexedStar g) hrest
            have hterm :
                w.map (IndexedGrammar.ISym.terminal (g := indexedStar g)) = [] := hnil.2
            have hw_nil : w = [] := by simpa using hterm
            subst w
            exact Language.nil_mem_kstar g.Language

private theorem indexedStar_language (g : IndexedGrammar T) :
    (indexedStar g).Language = KStar.kstar g.Language := by
  apply Set.Subset.antisymm
  · exact indexedStar_language_subset g
  · intro w hw
    rw [Language.mem_kstar] at hw
    obtain ⟨words, rfl, hwords⟩ := hw
    exact indexedStar_generates_flatten g words hwords

/-- Indexed languages are closed under Kleene star. -/
public theorem Indexed_closedUnderKleeneStar :
    ClosedUnderKleeneStar (α := T) is_Indexed := by
  intro L hL
  obtain ⟨g, rfl⟩ := hL
  exact ⟨indexedStar g, indexedStar_language g⟩

end
