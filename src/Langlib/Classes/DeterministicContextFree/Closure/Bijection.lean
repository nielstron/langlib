module

public import Langlib.Classes.DeterministicContextFree.Definition
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Height.Basic
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
@[expose]
public section



/-! # DCF Closure Under Injective Terminal Maps -/

open PDA

variable {T₁ T₂ : Type}

namespace DPDA

variable {Q S : Type} [Fintype Q] [Fintype T₁] [Fintype T₂] [Fintype S]

/-- Pull input symbols back along an alphabet map. -/
public def comapInput (M : DPDA Q T₂ S) (f : T₁ → T₂) : DPDA Q T₁ S where
  initial_state := M.initial_state
  start_symbol := M.start_symbol
  final_states := M.final_states
  transition q a Z := M.transition q (f a) Z
  epsilon_transition := M.epsilon_transition
  no_mixed := by
    intro q Z hε a
    exact M.no_mixed q Z hε (f a)

private def comapConf (M : DPDA Q T₂ S) (f : T₁ → T₂) :
    PDA.conf (M.comapInput f).toPDA → PDA.conf M.toPDA
  | ⟨q, w, γ⟩ => ⟨q, w.map f, γ⟩

private lemma comap_reaches₁_sound (M : DPDA Q T₂ S) (f : T₁ → T₂)
    {c c' : PDA.conf (M.comapInput f).toPDA} :
    PDA.Reaches₁ c c' → PDA.Reaches₁ (comapConf M f c) (comapConf M f c') := by
  intro h
  rcases c with ⟨q, w, γ⟩
  rcases c' with ⟨q', w', γ'⟩
  cases γ with
  | nil =>
      simp [PDA.Reaches₁, PDA.step] at h
  | cons Z γ =>
      cases w with
      | nil =>
          simp [PDA.Reaches₁, PDA.step, comapConf, DPDA.comapInput, DPDA.toPDA] at h ⊢
          exact h
      | cons a w =>
          simp [PDA.Reaches₁, PDA.step, comapConf, DPDA.comapInput, DPDA.toPDA] at h ⊢
          rcases h with h | h
          · rcases h with ⟨β, hp, hw, hγ⟩
            left
            exact ⟨β, hp, by simp [hw], hγ⟩
          · rcases h with ⟨β, hp, hw, hγ⟩
            right
            exact ⟨β, hp, by simp [hw], hγ⟩

private lemma comap_reaches_sound (M : DPDA Q T₂ S) (f : T₁ → T₂)
    {c c' : PDA.conf (M.comapInput f).toPDA} :
    PDA.Reaches c c' → PDA.Reaches (comapConf M f c) (comapConf M f c') := by
  intro h
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
      exact Relation.ReflTransGen.tail ih (comap_reaches₁_sound M f hstep)

private lemma comap_reaches₁_complete (M : DPDA Q T₂ S) (f : T₁ → T₂)
    {c : PDA.conf (M.comapInput f).toPDA} {d' : PDA.conf M.toPDA} :
    PDA.Reaches₁ (comapConf M f c) d' →
      ∃ c' : PDA.conf (M.comapInput f).toPDA,
        PDA.Reaches₁ c c' ∧ comapConf M f c' = d' := by
  intro h
  rcases c with ⟨q, w, γ⟩
  rcases d' with ⟨q', w', γ'⟩
  cases γ with
  | nil =>
      simp [PDA.Reaches₁, PDA.step, comapConf] at h
  | cons Z γ =>
      cases w with
      | nil =>
          simp [PDA.Reaches₁, PDA.step, comapConf, DPDA.toPDA] at h
          rcases h with ⟨β, hp, hw, hγ⟩
          subst hw
          subst hγ
          exact ⟨⟨q', [], β ++ γ⟩, by
            simp [PDA.Reaches₁, PDA.step, DPDA.comapInput, DPDA.toPDA, hp], rfl⟩
      | cons a w =>
          simp [PDA.Reaches₁, PDA.step, comapConf, DPDA.toPDA] at h
          rcases h with h | h
          · rcases h with ⟨β, hp, hw, hγ⟩
            subst hw
            subst hγ
            exact ⟨⟨q', w, β ++ γ⟩, by
              simp [PDA.Reaches₁, PDA.step, DPDA.comapInput, DPDA.toPDA, hp], rfl⟩
          · rcases h with ⟨β, hp, hw, hγ⟩
            subst hw
            subst hγ
            exact ⟨⟨q', a :: w, β ++ γ⟩, by
              simp [PDA.Reaches₁, PDA.step, DPDA.comapInput, DPDA.toPDA, hp], rfl⟩

private lemma comap_reaches_complete_aux (M : DPDA Q T₂ S) (f : T₁ → T₂)
    {d d' : PDA.conf M.toPDA} (h : PDA.Reaches d d') :
    ∀ c : PDA.conf (M.comapInput f).toPDA,
      comapConf M f c = d →
        ∃ c' : PDA.conf (M.comapInput f).toPDA,
          PDA.Reaches c c' ∧ comapConf M f c' = d' := by
  induction h with
  | refl =>
      intro c hc
      exact ⟨c, Relation.ReflTransGen.refl, hc⟩
  | tail dmid hstep ih =>
      intro c hc
      rcases ih c hc with ⟨cmid, hcmid, hmap⟩
      rcases comap_reaches₁_complete M f (c := cmid) (by simpa [hmap] using hstep)
        with ⟨c', hstep', hmap'⟩
      exact ⟨c', Relation.ReflTransGen.tail hcmid hstep', hmap'⟩

private lemma comap_reaches_complete (M : DPDA Q T₂ S) (f : T₁ → T₂)
    {c : PDA.conf (M.comapInput f).toPDA} {d' : PDA.conf M.toPDA} :
    PDA.Reaches (comapConf M f c) d' →
      ∃ c' : PDA.conf (M.comapInput f).toPDA,
        PDA.Reaches c c' ∧ comapConf M f c' = d' :=
  fun h => comap_reaches_complete_aux M f h c rfl

public theorem comap_acceptsByFinalState (M : DPDA Q T₂ S) (f : T₁ → T₂) :
    (M.comapInput f).acceptsByFinalState = {w : List T₁ | w.map f ∈ M.acceptsByFinalState} := by
  ext w
  constructor
  · rintro ⟨q, hq, γ, hreach⟩
    exact ⟨q, hq, γ, comap_reaches_sound M f hreach⟩
  · rintro ⟨q, hq, γ, hreach⟩
    rcases comap_reaches_complete M f
        (c := ⟨(M.comapInput f).initial_state, w, [(M.comapInput f).start_symbol]⟩)
        (d' := ⟨q, [], γ⟩) hreach with ⟨c, hc, hmap⟩
    rcases c with ⟨q', input, stack⟩
    simp [comapConf] at hmap
    rcases hmap with ⟨rfl, hinput, rfl⟩
    have hnil : input = [] := by
      cases input <;> simp at hinput ⊢
    subst input
    exact ⟨q', hq, stack, hc⟩

/-- Rename the input alphabet of a DPDA along `f`, decoding symbols in the image using `g`.
Symbols outside the image of `f` have no transition. -/
@[expose]
public noncomputable def mapInput (M : DPDA Q T₁ S) (f : T₁ → T₂) (g : T₂ → T₁) : DPDA Q T₂ S where
  initial_state := M.initial_state
  start_symbol := M.start_symbol
  final_states := M.final_states
  transition q b Z := by
    classical
    exact if h : ∃ a, f a = b then M.transition q (g b) Z else none
  epsilon_transition := M.epsilon_transition
  no_mixed := by
    intro q Z hε b
    classical
    by_cases h : ∃ a, f a = b
    · simpa [h] using M.no_mixed q Z hε (g b)
    · simp [h]

private def mapConf {f : T₁ → T₂} {g : T₂ → T₁} (M : DPDA Q T₁ S) :
    PDA.conf M.toPDA → PDA.conf (M.mapInput f g).toPDA
  | ⟨q, w, γ⟩ => ⟨q, List.map f w, γ⟩

private lemma reaches₁_map {f : T₁ → T₂} {g : T₂ → T₁} (M : DPDA Q T₁ S)
    (hfg : Function.LeftInverse g f) {c c' : PDA.conf M.toPDA} :
    PDA.Reaches₁ c c' →
      @PDA.Reaches₁ Q T₂ S _ _ _ (M.mapInput f g).toPDA
        (mapConf (f := f) (g := g) M c)
        (mapConf (f := f) (g := g) M c') := by
  intro h
  rcases c with ⟨q, w, γ⟩
  rcases c' with ⟨q', w', γ'⟩
  cases γ with
  | nil =>
      have h' : @PDA.ReachesIn Q T₁ S _ _ _ M.toPDA 1 ⟨q, w, []⟩ ⟨q', w', γ'⟩ :=
        (PDA.reaches₁_iff_reachesIn_one).mp h
      exact False.elim (PDA.reachesIn_one_on_empty_stack h')
  | cons Z γ =>
      cases w with
      | nil =>
          simpa [PDA.Reaches₁, PDA.step, mapConf, DPDA.mapInput] using h
      | cons a w =>
          unfold PDA.Reaches₁ PDA.step at h ⊢
          rcases h with h | h
          · rcases h with ⟨p, β, hp, hcfg⟩
            left
            refine ⟨p, β, ?_, ?_⟩
            · simpa [DPDA.toPDA, DPDA.mapInput, hfg a] using hp
            · simpa [mapConf] using congrArg (mapConf (f := f) (g := g) M) hcfg
          · rcases h with ⟨p, β, hp, hcfg⟩
            right
            refine ⟨p, β, ?_, ?_⟩
            · simpa [DPDA.toPDA, DPDA.mapInput] using hp
            · simpa [mapConf] using congrArg (mapConf (f := f) (g := g) M) hcfg

private lemma reaches_map {f : T₁ → T₂} {g : T₂ → T₁} (M : DPDA Q T₁ S)
    (hfg : Function.LeftInverse g f) {c c' : PDA.conf M.toPDA} :
    PDA.Reaches c c' →
      @PDA.Reaches Q T₂ S _ _ _ (M.mapInput f g).toPDA
        (mapConf (f := f) (g := g) M c)
        (mapConf (f := f) (g := g) M c') := by
  intro h
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
      exact Relation.ReflTransGen.tail ih (reaches₁_map M hfg hstep)

private lemma reaches₁_map_rev {f : T₁ → T₂} {g : T₂ → T₁} (M : DPDA Q T₁ S)
    (hfg : Function.LeftInverse g f) {c : PDA.conf M.toPDA}
    {d : PDA.conf (M.mapInput f g).toPDA} :
    @PDA.Reaches₁ Q T₂ S _ _ _ (M.mapInput f g).toPDA
      (mapConf (f := f) (g := g) M c) d →
      ∃ c' : PDA.conf M.toPDA,
        d = mapConf (f := f) (g := g) M c' ∧
        PDA.Reaches₁ c c' := by
  intro h
  rcases c with ⟨q, w, γ⟩
  rcases d with ⟨q', w', γ'⟩
  cases γ with
  | nil =>
      have h' : @PDA.ReachesIn Q T₂ S _ _ _ (M.mapInput f g).toPDA 1
          (mapConf (f := f) (g := g) M ⟨q, w, []⟩) ⟨q', w', γ'⟩ :=
        (PDA.reaches₁_iff_reachesIn_one).mp h
      exact False.elim (PDA.reachesIn_one_on_empty_stack h')
  | cons Z γ =>
      cases w with
      | nil =>
          unfold PDA.Reaches₁ PDA.step at h
          rcases h with ⟨p, β, hp, hcfg⟩
          refine ⟨⟨p, [], β ++ γ⟩, hcfg, ?_⟩
          exact ⟨p, β, hp, rfl⟩
      | cons a w =>
          unfold PDA.Reaches₁ PDA.step at h
          rcases h with h | h
          · rcases h with ⟨p, β, hp, hcfg⟩
            refine ⟨⟨p, w, β ++ γ⟩, hcfg, ?_⟩
            left
            refine ⟨p, β, ?_, rfl⟩
            simpa [DPDA.toPDA, DPDA.mapInput, hfg a] using hp
          · rcases h with ⟨p, β, hp, hcfg⟩
            refine ⟨⟨p, a :: w, β ++ γ⟩, hcfg, ?_⟩
            right
            refine ⟨p, β, ?_, rfl⟩
            simpa [DPDA.toPDA, DPDA.mapInput] using hp

private lemma reaches_map_rev {f : T₁ → T₂} {g : T₂ → T₁} (M : DPDA Q T₁ S)
    (hfg : Function.LeftInverse g f) {c : PDA.conf M.toPDA}
    {d : PDA.conf (M.mapInput f g).toPDA} :
    @PDA.Reaches Q T₂ S _ _ _ (M.mapInput f g).toPDA
      (mapConf (f := f) (g := g) M c) d →
      ∃ c' : PDA.conf M.toPDA,
        d = mapConf (f := f) (g := g) M c' ∧
        PDA.Reaches c c' := by
  intro h
  induction h with
  | refl =>
      exact ⟨c, rfl, PDA.Reaches.refl _⟩
  | tail _ hstep ih =>
      rcases ih with ⟨c', rfl, hreach'⟩
      rcases reaches₁_map_rev M hfg hstep with ⟨c'', rfl, hstep'⟩
      exact ⟨c'', rfl, Relation.ReflTransGen.tail hreach' hstep'⟩

private lemma reaches₁_consumed_prefix {f : T₁ → T₂} {g : T₂ → T₁}
    (M : DPDA Q T₁ S) {c c' : PDA.conf (M.mapInput f g).toPDA} :
    @PDA.Reaches₁ Q T₂ S _ _ _ (M.mapInput f g).toPDA c c' →
      ∃ x : List T₂, c.input = x ++ c'.input ∧ ∀ a ∈ x, ∃ b, f b = a := by
  intro h
  rcases c with ⟨q, w, γ⟩
  rcases c' with ⟨q', w', γ'⟩
  cases γ with
  | nil =>
      have h' : @PDA.ReachesIn Q T₂ S _ _ _ (M.mapInput f g).toPDA 1 ⟨q, w, []⟩ ⟨q', w', γ'⟩ :=
        (PDA.reaches₁_iff_reachesIn_one).mp h
      exact False.elim (PDA.reachesIn_one_on_empty_stack h')
  | cons Z γ =>
      cases w with
      | nil =>
          unfold PDA.Reaches₁ PDA.step at h
          rcases h with ⟨p, β, hp, hcfg⟩
          cases hcfg
          refine ⟨[], by simp, by simp⟩
      | cons a w =>
          unfold PDA.Reaches₁ PDA.step at h
          rcases h with h | h
          · rcases h with ⟨p, β, hp, hcfg⟩
            cases hcfg
            refine ⟨[a], by simp, ?_⟩
            intro y hy
            simp at hy
            cases hy
            classical
            have himg : ∃ b, f b = a := by
              by_cases h' : ∃ b, f b = a
              · exact h'
              · simp [DPDA.toPDA, DPDA.mapInput, h'] at hp
            exact himg
          · rcases h with ⟨p, β, hp, hcfg⟩
            cases hcfg
            refine ⟨[], by simp, by simp⟩

private lemma reaches_consumed_prefix {f : T₁ → T₂} {g : T₂ → T₁}
    (M : DPDA Q T₁ S) {c c' : PDA.conf (M.mapInput f g).toPDA} :
    @PDA.Reaches Q T₂ S _ _ _ (M.mapInput f g).toPDA c c' →
      ∃ x : List T₂, c.input = x ++ c'.input ∧ ∀ a ∈ x, ∃ b, f b = a := by
  intro h
  induction h with
  | refl =>
      exact ⟨[], by simp, by simp⟩
  | tail _ hstep ih =>
      rcases ih with ⟨x, hx, himg⟩
      rcases reaches₁_consumed_prefix M hstep with ⟨y, hy, himg'⟩
      refine ⟨x ++ y, by simp [hx, hy, List.append_assoc], ?_⟩
      intro a ha
      rw [List.mem_append] at ha
      exact ha.elim (himg a) (himg' a)

/-- Injective terminal renaming preserves final-state acceptance of DPDAs. -/
public theorem map_acceptsByFinalState_of_injective [Nonempty T₁] {f : T₁ → T₂}
    (hf : Function.Injective f) (M : DPDA Q T₁ S) :
    (M.mapInput f (Function.invFun f)).acceptsByFinalState = Language.map f M.acceptsByFinalState := by
  classical
  let g := Function.invFun f
  have hfg : Function.LeftInverse g f := Function.leftInverse_invFun hf
  have hmap_eq :
      ∀ v : List T₂, (∀ a ∈ v, ∃ b, f b = a) → List.map f (List.map g v) = v := by
    intro v
    induction v with
    | nil =>
        intro _
        rfl
    | cons a v ih =>
        intro hv
        rcases hv a (by simp) with ⟨b, rfl⟩
        have hv' : ∀ a ∈ v, ∃ b, f b = a := by
          intro a ha
          exact hv a (by simp [ha])
        simpa [hfg b] using ih hv'
  ext w
  constructor
  · rintro ⟨q, hq, γ, hreach⟩
    rcases reaches_consumed_prefix M hreach with ⟨x, hx, himg⟩
    have hw : w = x := by simpa using hx
    subst w
    let u := List.map g x
    have huw : List.map f u = x := hmap_eq x himg
    have hreach' :
        @PDA.Reaches Q T₂ S _ _ _ (M.mapInput f g).toPDA
          (mapConf (f := f) (g := g) M
            (⟨M.initial_state, u, [M.start_symbol]⟩ : PDA.conf M.toPDA))
          ⟨q, [], γ⟩ := by
      simpa [mapConf, u, huw] using hreach
    rcases reaches_map_rev M hfg hreach' with ⟨c, hc, hreach₀⟩
    rcases c with ⟨q', w', γ'⟩
    simp [mapConf] at hc
    rcases hc with ⟨rfl, hw', rfl⟩
    have : w' = [] := by simpa using hw'.symm
    subst w'
    exact ⟨u, ⟨q, hq, γ, hreach₀⟩, huw⟩
  · rintro ⟨u, ⟨q, hq, γ, hreach⟩, rfl⟩
    exact ⟨q, hq, γ, reaches_map M hfg hreach⟩

end DPDA

/-- Deterministic context-free languages are preserved under injective terminal maps. -/
public theorem DCF_of_map_injective_DCF [Nonempty T₁] [Fintype T₁] [Fintype T₂]
    {f : T₁ → T₂} (hf : Function.Injective f) (L : Language T₁) :
    is_DCF L → is_DCF (Language.map f L) := by
  intro hL
  obtain ⟨Q, S, hQ, hS, M, hM⟩ := hL
  refine ⟨Q, S, hQ, hS, DPDA.mapInput M f (Function.invFun f), ?_⟩
  rw [DPDA.map_acceptsByFinalState_of_injective hf M, hM]

private theorem preimage_map_injective_eq {f : T₁ → T₂} (hf : Function.Injective f)
    (L : Language T₁) :
    ({w : List T₁ | w.map f ∈ Language.map f L} : Language T₁) = L := by
  ext w
  constructor
  · rintro ⟨v, hv, hmap⟩
    have : v = w := by
      exact (List.map_injective_iff.mpr hf) hmap
    simpa [this] using hv
  · intro hw
    exact ⟨w, hw, rfl⟩

public theorem DCF_of_map_injective_DCF_rev [Fintype T₁] [Fintype T₂]
    {f : T₁ → T₂} (hf : Function.Injective f) (L : Language T₁) :
    is_DCF (Language.map f L) → is_DCF L := by
  intro hmap
  obtain ⟨Q, S, hQ, hS, M, hM⟩ := hmap
  refine ⟨Q, S, hQ, hS, DPDA.comapInput M f, ?_⟩
  rw [DPDA.comap_acceptsByFinalState M f, hM, preimage_map_injective_eq hf L]
