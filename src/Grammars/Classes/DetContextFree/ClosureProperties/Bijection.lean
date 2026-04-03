import Grammars.Classes.DetContextFree.Basics.DCFL

/-! # DCFL Closure Under Injective Terminal Maps -/

open PDA

variable {T₁ T₂ : Type}

namespace DPDA

variable {Q S : Type} [Fintype Q] [Fintype T₁] [Fintype T₂] [Fintype S]

/-- Rename the input alphabet of a DPDA along `f`, decoding symbols in the image using `g`.
Symbols outside the image of `f` have no transition. -/
noncomputable def mapInput (M : DPDA Q T₁ S) (f : T₁ → T₂) (g : T₂ → T₁) : DPDA Q T₂ S where
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
theorem map_acceptsByFinalState_of_injective [Nonempty T₁] {f : T₁ → T₂}
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
theorem DCFL_of_map_injective_DCFL [Nonempty T₁] [Fintype T₁] [Fintype T₂]
    {f : T₁ → T₂} (hf : Function.Injective f) (L : Language T₁) :
    is_DCFL L → is_DCFL (Language.map f L) := by
  intro hL
  obtain ⟨Q, S, hQ, hS, M, hM⟩ := hL
  refine ⟨Q, S, hQ, hS, DPDA.mapInput M f (Function.invFun f), ?_⟩
  rw [DPDA.map_acceptsByFinalState_of_injective hf M, hM]
