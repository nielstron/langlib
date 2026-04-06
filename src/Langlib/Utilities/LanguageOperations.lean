import Mathlib.Computability.Language
import Mathlib.Computability.MyhillNerode
import Mathlib.Algebra.Group.Pointwise.Set.ListOfFn

/-! # Language Operations

This file defines basic operations on languages used throughout the closure-property proofs.

## Main declarations

- `bijemapLang`
- `permuteLang`
-/

open scoped Classical

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

private lemma mem_prod_singletons_iff {α β : Type} (f : α → β) :
    ∀ w : List α, ∀ u : List β,
      u ∈ (w.map fun x => ({[f x]} : Language β)).prod ↔ u = List.map f w
  | [], u => by
      change u ∈ ({[]} : Language β) ↔ u = []
      rfl
  | x :: xs, u => by
      constructor
      · intro hu
        rw [show (List.map (fun x => ({[f x]} : Language β)) (x :: xs)).prod =
            ({[f x]} : Language β) * (List.map (fun x => ({[f x]} : Language β)) xs).prod by rfl] at hu
        rw [Language.mul_def] at hu
        rcases hu with ⟨u₁, hu₁, u₂, hu₂, rfl⟩
        have hu₂' := (mem_prod_singletons_iff f xs u₂).1 hu₂
        have hu₁' : u₁ = [f x] := by simpa using hu₁
        simp [hu₁', hu₂']
      · intro hu
        subst hu
        rw [show (List.map (fun x => ({[f x]} : Language β)) (x :: xs)).prod =
            ({[f x]} : Language β) * (List.map (fun x => ({[f x]} : Language β)) xs).prod by rfl]
        rw [Language.mul_def]
        refine ⟨[f x], Set.mem_singleton _, List.map f xs, ?_, rfl⟩
        exact (mem_prod_singletons_iff f xs (List.map f xs)).2 rfl

/-- Substituting each symbol `x` with the singleton language `{[f x]}` is the same as
mapping the whole language along `f`. -/
theorem subst_singletons_eq_map {α β : Type} (L : Language α) (f : α → β) :
    L.subst (fun x => ({[f x]} : Language β)) = Language.map f L := by
  ext u
  constructor
  · rintro ⟨w, hw, hu⟩
    exact ⟨w, hw, (mem_prod_singletons_iff f w u).1 hu ▸ rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, hw, (mem_prod_singletons_iff f w _).2 rfl⟩

/-- The prefix language of `L` consists of all words that can be extended on the right to a word
in `L`. -/
def prefixLang (L : Language α) : Language α :=
  { w | ∃ v : List α, w ++ v ∈ L }

@[simp] theorem mem_prefixLang {L : Language α} {w : List α} :
    w ∈ prefixLang L ↔ ∃ v : List α, w ++ v ∈ L :=
  Iff.rfl

theorem subset_prefixLang (L : Language α) : L ≤ prefixLang L := by
  intro w hw
  exact ⟨[], by simpa⟩

theorem nil_mem_prefixLang {L : Language α} (h : ∃ w, w ∈ L) :
    [] ∈ prefixLang L := by
  obtain ⟨w, hw⟩ := h
  exact ⟨w, by simpa⟩

theorem prefixLang_mono {L₁ L₂ : Language α} (h : L₁ ≤ L₂) :
    prefixLang L₁ ≤ prefixLang L₂ := by
  intro w hw
  rcases hw with ⟨v, hv⟩
  exact ⟨v, h hv⟩

@[simp] theorem prefixLang_zero : prefixLang (0 : Language α) = 0 := by
  ext w
  constructor
  · rintro ⟨v, hv⟩
    simp at hv
  · intro hw
    simp at hw

@[simp] theorem prefixLang_add (L₁ L₂ : Language α) :
    prefixLang (L₁ + L₂) = prefixLang L₁ + prefixLang L₂ := by
  ext w
  constructor
  · rintro ⟨v, hv | hv⟩
    · exact Or.inl ⟨v, hv⟩
    · exact Or.inr ⟨v, hv⟩
  · rintro (⟨v, hv⟩ | ⟨v, hv⟩)
    · exact ⟨v, Or.inl hv⟩
    · exact ⟨v, Or.inr hv⟩

theorem prefixLang_prefixLang (L : Language α) :
    prefixLang (prefixLang L) = prefixLang L := by
  ext w
  constructor
  · rintro ⟨v, u, hu⟩
    exact ⟨v ++ u, by simpa [List.append_assoc] using hu⟩
  · rintro ⟨v, hv⟩
    exact ⟨[], v, by simpa using hv⟩

/-- The suffix language of `L` consists of all words that can be extended on the left to a word in
`L`. -/
def suffixLang (L : Language α) : Language α :=
  { w | ∃ v : List α, v ++ w ∈ L }

@[simp] theorem mem_suffixLang {L : Language α} {w : List α} :
    w ∈ suffixLang L ↔ ∃ v : List α, v ++ w ∈ L :=
  Iff.rfl

theorem subset_suffixLang (L : Language α) : L ≤ suffixLang L := by
  intro w hw
  exact ⟨[], by simpa⟩

theorem suffixLang_mono {L₁ L₂ : Language α} (h : L₁ ≤ L₂) :
    suffixLang L₁ ≤ suffixLang L₂ := by
  intro w hw
  rcases hw with ⟨v, hv⟩
  exact ⟨v, h hv⟩

@[simp] theorem suffixLang_zero : suffixLang (0 : Language α) = 0 := by
  ext w
  constructor
  · rintro ⟨v, hv⟩
    simp at hv
  · intro hw
    simp at hw

@[simp] theorem suffixLang_add (L₁ L₂ : Language α) :
    suffixLang (L₁ + L₂) = suffixLang L₁ + suffixLang L₂ := by
  ext w
  constructor
  · rintro ⟨v, hv | hv⟩
    · exact Or.inl ⟨v, hv⟩
    · exact Or.inr ⟨v, hv⟩
  · rintro (⟨v, hv⟩ | ⟨v, hv⟩)
    · exact ⟨v, Or.inl hv⟩
    · exact ⟨v, Or.inr hv⟩

variable {T : Type _}

def bijemapLang {T' : Type _} (L : Language T) (π : T ≃ T') : Language T' :=
  fun w : List T' => List.map π.symm w ∈ L

def permuteLang (L : Language T) (π : Equiv.Perm T) : Language T :=
  bijemapLang L π

@[simp] theorem bijemapLang_symm_bijemapLang (L : Language T) (π : T ≃ T') :
    bijemapLang (bijemapLang L π) π.symm = L := by
  ext w
  change List.map π.symm (List.map π w) ∈ L ↔ w ∈ L
  simp [List.map_map]

theorem suffixLang_eq_reverse_prefixLang_reverse (L : Language T) :
    suffixLang L = (prefixLang L.reverse).reverse := by
  ext w
  constructor
  · rintro ⟨v, hv⟩
    change ∃ u, (w.reverse ++ u).reverse ∈ L
    exact ⟨v.reverse, by simpa [List.reverse_append] using hv⟩
  · change w.reverse ∈ prefixLang L.reverse → w ∈ suffixLang L
    rintro ⟨v, hv⟩
    change (w.reverse ++ v).reverse ∈ L at hv
    change ∃ u, u ++ w ∈ L
    exact ⟨v.reverse, by simpa [List.reverse_append] using hv⟩

theorem prefixLang_eq_reverse_suffixLang_reverse (L : Language T) :
    prefixLang L = (suffixLang L.reverse).reverse := by
  ext w
  constructor
  · rintro ⟨v, hv⟩
    change ∃ u, (u ++ w.reverse).reverse ∈ L
    exact ⟨v.reverse, by simpa [List.reverse_append] using hv⟩
  · change w.reverse ∈ suffixLang L.reverse → w ∈ prefixLang L
    rintro ⟨v, hv⟩
    change (v ++ w.reverse).reverse ∈ L at hv
    change ∃ u, w ++ u ∈ L
    exact ⟨v.reverse, by simpa [List.reverse_append] using hv⟩

/-- The right quotient of `L` by `R`: the set of words `w` such that `w ++ v ∈ L` for some
`v ∈ R`. This generalises `prefixLang` (which is `rightQuotient L Set.univ`). -/
def rightQuotient (L : Language α) (R : Language α) : Language α :=
  { w | ∃ v ∈ R, w ++ v ∈ L }

instance : HDiv (Language α) (Language α) (Language α) where
  hDiv := rightQuotient

infixl:70 " \\\\ " => fun x L => Language.leftQuotient L x

@[simp] theorem mem_rightQuotient {L R : Language α} {w : List α} :
    w ∈ rightQuotient L R ↔ ∃ v ∈ R, w ++ v ∈ L :=
  Iff.rfl

theorem prefixLang_eq_rightQuotient_univ (L : Language α) :
    prefixLang L = rightQuotient L Set.univ := by
  ext w; constructor
  · rintro ⟨v, hv⟩; exact ⟨v, Set.mem_univ _, hv⟩
  · rintro ⟨v, _, hv⟩; exact ⟨v, hv⟩

theorem reverse_leftQuotient_eq_rightQuotient_reverse_singleton
    (L : Language α) (x : List α) :
    (x \\ L).reverse = L.reverse / {x.reverse} := by
  ext w
  constructor
  · intro h
    change x ++ w.reverse ∈ L at h
    change ∃ v ∈ ({x.reverse} : Language α), w ++ v ∈ L.reverse
    refine ⟨x.reverse, Set.mem_singleton _, ?_⟩
    change (w ++ x.reverse).reverse ∈ L
    simpa [List.reverse_append] using h
  · rintro ⟨v, hv, hvw⟩
    rw [Set.mem_singleton_iff] at hv
    subst hv
    change x ++ w.reverse ∈ L
    change (w ++ x.reverse).reverse ∈ L at hvw
    simpa [List.reverse_append] using hvw

theorem leftQuotient_eq_reverse_rightQuotient_reverse_singleton
    (L : Language α) (x : List α) :
    x \\ L = (L.reverse / {x.reverse}).reverse := by
  ext w
  constructor
  · intro h
    change w.reverse ∈ L.reverse / ({x.reverse} : Language α)
    refine ⟨x.reverse, Set.mem_singleton _, ?_⟩
    change (w.reverse ++ x.reverse).reverse ∈ L
    simpa [List.reverse_append] using h
  · intro h
    change ∃ v ∈ ({x.reverse} : Language α), w.reverse ++ v ∈ L.reverse at h
    rcases h with ⟨v, hv, hvw⟩
    rw [Set.mem_singleton_iff] at hv
    subst hv
    change x ++ w ∈ L
    change (w.reverse ++ x.reverse).reverse ∈ L at hvw
    simpa [List.reverse_append] using hvw

theorem rightQuotient_mono_left {L₁ L₂ R : Language α} (h : L₁ ≤ L₂) :
    L₁ / R ≤ L₂ / R := by
  intro w ⟨v, hv, hwv⟩
  exact ⟨v, hv, h hwv⟩

theorem rightQuotient_mono_right {L R₁ R₂ : Language α} (h : R₁ ≤ R₂) :
    L / R₁ ≤ L / R₂ := by
  intro w ⟨v, hv, hwv⟩
  exact ⟨v, h hv, hwv⟩

@[simp] theorem rightQuotient_add_right (L R₁ R₂ : Language α) :
    L / (R₁ + R₂) = L / R₁ + L / R₂ := by
  ext w
  constructor
  · rintro ⟨v, hv | hv, hwv⟩
    · exact Or.inl ⟨v, hv, hwv⟩
    · exact Or.inr ⟨v, hv, hwv⟩
  · rintro (⟨v, hv, hwv⟩ | ⟨v, hv, hwv⟩)
    · exact ⟨v, Or.inl hv, hwv⟩
    · exact ⟨v, Or.inr hv, hwv⟩

@[simp] theorem rightQuotient_zero_left (R : Language α) :
    0 / R = 0 := by
  ext w; constructor
  · rintro ⟨v, _, hv⟩; exact hv
  · tauto

@[simp] theorem rightQuotient_zero_right (L : Language α) :
    L / 0 = 0 := by
  ext w; constructor
  · rintro ⟨v, hv, _⟩; exact hv.elim
  · tauto

@[simp] theorem rightQuotient_add_left (L₁ L₂ R : Language α) :
    (L₁ + L₂) / R = L₁ / R + L₂ / R := by
  ext w
  constructor
  · rintro ⟨v, hv, hwv | hwv⟩
    · exact Or.inl ⟨v, hv, hwv⟩
    · exact Or.inr ⟨v, hv, hwv⟩
  · rintro (⟨v, hv, hwv⟩ | ⟨v, hv, hwv⟩)
    · exact ⟨v, hv, Or.inl hwv⟩
    · exact ⟨v, hv, Or.inr hwv⟩

theorem subset_rightQuotient_univ (L : Language α) :
    L ≤ rightQuotient L Set.univ := by
  rw [← prefixLang_eq_rightQuotient_univ]
  exact subset_prefixLang L

theorem leftQuotient_mono {L₁ L₂ : Language α} (h : L₁ ≤ L₂) (x : List α) :
    x \\ L₁ ≤ x \\ L₂ := by
  intro w hw
  exact h hw

@[simp] theorem leftQuotient_zero (x : List α) :
    x \\ (0 : Language α) = 0 := by
  ext w
  simp [mem_leftQuotient]

@[simp] theorem nil_leftQuotient (L : Language α) :
    ([] : List α) \\ L = L := by
  simpa using Language.leftQuotient_nil L

@[simp] theorem cons_leftQuotient (a : α) (x : List α) (L : Language α) :
    (a :: x) \\ L = x \\ ([a] \\ L) := by
  simpa using (Language.leftQuotient_append L [a] x)

@[simp] theorem append_leftQuotient (x y : List α) (L : Language α) :
    (x ++ y) \\ L = y \\ (x \\ L) := by
  simpa using (Language.leftQuotient_append L x y)

@[simp] theorem leftQuotient_add (x : List α) (L₁ L₂ : Language α) :
    x \\ (L₁ + L₂) = x \\ L₁ + x \\ L₂ := by
  ext w
  constructor
  · intro h
    exact h
  · intro h
    exact h

end Language
