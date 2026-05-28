module

public import Langlib.Utilities.ClosurePredicates
public import Langlib.Classes.RecursivelyEnumerable.Definition
import Langlib.Classes.RecursivelyEnumerable.Closure.Concatenation
import Langlib.Classes.RecursivelyEnumerable.Closure.Homomorphism
import Langlib.Classes.RecursivelyEnumerable.Closure.Intersection
import Langlib.Classes.RecursivelyEnumerable.Closure.InverseHomomorphism
import Langlib.Classes.RecursivelyEnumerable.Closure.Star
import Langlib.Classes.RecursivelyEnumerable.Closure.Union
import Langlib.Classes.Regular.Closure.Homomorphism
import Langlib.Classes.Regular.Examples.TopBot
import Langlib.Classes.Regular.Inclusion.RecursivelyEnumerable
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
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

@[expose] public section

/-! # RE Closure Under Substitution

This file proves that recursively enumerable languages over finite alphabets are
closed under finite-alphabet substitution.  The key result is
`RE_closedUnderSubstitution`: encode each substituted symbol as a block
`inl a :: map inr u`, take the Kleene star of the RE block language, restrict
the projected source word to the original RE language by inverse homomorphism
and intersection, then erase the source-symbol markers by homomorphism.

## Main declarations

- `RE_of_subst_RE`
- `RE_closedUnderSubstitution`
-/

open scoped Classical

variable {α β ι : Type}

/-- RE languages are closed under finite indexed union. -/
theorem RE_of_finite_iUnion [Fintype α] [Fintype ι] (L : ι → Language α)
    (hL : ∀ i, is_RE (L i)) :
    is_RE ((⋃ i, L i) : Language α) := by
  classical
  have hfin : ∀ s : Finset ι, is_RE ((⋃ i ∈ s, L i) : Language α) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        simpa using is_RE_of_isRegular (Language.isRegular_bot : (⊥ : Language α).IsRegular)
    | insert a s has ih =>
        let U : Language α := (⋃ i ∈ s, L i)
        have hEq : ((⋃ i ∈ insert a s, L i) : Language α) =
            ((L a : Language α) + U : Language α) := by
          ext w
          have hU_mp : w ∈ U → ∃ i, ∃ _ : i ∈ s, w ∈ L i := by
            intro hw
            change w ∈ (⋃ i ∈ s, L i : Set (List α)) at hw
            simpa only [Set.mem_iUnion] using hw
          have hU_mpr : (∃ i, ∃ _ : i ∈ s, w ∈ L i) → w ∈ U := by
            intro hw
            change w ∈ (⋃ i ∈ s, L i : Set (List α))
            simpa only [Set.mem_iUnion] using hw
          rw [Language.mem_add]
          constructor
          · intro hw
            simp only [Set.mem_iUnion, Finset.mem_insert] at hw
            rcases hw with ⟨i, hi, hwi⟩
            rcases hi with rfl | his
            · exact Or.inl hwi
            · exact Or.inr (hU_mpr ⟨i, his, hwi⟩)
          · intro hw
            simp only [Set.mem_iUnion, Finset.mem_insert]
            rcases hw with hwa | hU
            · exact ⟨a, Or.inl rfl, hwa⟩
            · obtain ⟨i, his, hwi⟩ := hU_mp hU
              exact ⟨i, Or.inr his, hwi⟩
        rw [hEq]
        exact RE_of_RE_u_RE (L a : Language α) U ⟨hL a, ih⟩
  simpa using hfin Finset.univ

namespace Language

/-- Projection from encoded substitution blocks to the source alphabet. -/
def substProj (x : α ⊕ β) : List α :=
  match x with
  | Sum.inl a => [a]
  | Sum.inr _ => []

/-- Erasure from encoded substitution blocks to the target alphabet. -/
def substErase (x : α ⊕ β) : List β :=
  match x with
  | Sum.inl _ => []
  | Sum.inr b => [b]

@[simp] theorem substProj_map_inr (u : List β) :
    (u.map Sum.inr).flatMap (@substProj α β) = [] := by
  induction u <;> simp [substProj, *]

@[simp] theorem substErase_map_inr (u : List β) :
    (u.map Sum.inr).flatMap (@substErase α β) = u := by
  induction u <;> simp [substErase, *]

/-- The language of one encoded substitution block. -/
def substBlock (f : α → Language β) : Language (α ⊕ β) :=
  ⋃ a, ({[Sum.inl a]} : Language (α ⊕ β)) *
    ((f a).homomorphicImage fun b => [Sum.inr b])

@[simp] theorem substProj_block (a : α) (u : List β) :
    (Sum.inl a :: u.map Sum.inr).flatMap (@substProj α β) = [a] := by
  simp [substProj]

@[simp] theorem substErase_block (a : α) (u : List β) :
    (Sum.inl a :: u.map Sum.inr).flatMap (@substErase α β) = u := by
  simp [substErase]

theorem mem_homomorphicImage_iff_flatMap (L : Language α) (h : α → List β) (w : List β) :
    w ∈ L.homomorphicImage h ↔ ∃ x ∈ L, x.flatMap h = w := by
  simp only [homomorphicImage, subst]
  constructor
  · rintro ⟨x, hx, hw⟩
    exact ⟨x, hx, ((mem_prod_singletons_iff_flatMap x h w).mp hw).symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, (mem_prod_singletons_iff_flatMap x h _).mpr rfl⟩

theorem mem_substBlock_iff (f : α → Language β) (z : List (α ⊕ β)) :
    z ∈ substBlock f ↔ ∃ a u, u ∈ f a ∧ z = Sum.inl a :: u.map Sum.inr := by
  constructor
  · intro hz
    change z ∈ (⋃ a, ({[Sum.inl a]} : Language (α ⊕ β)) *
      ((f a).homomorphicImage fun b => [Sum.inr b])) at hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨a, x, hx, y, hy, rfl⟩ := hz
    subst x
    obtain ⟨u, hu, hflat⟩ :=
      (mem_homomorphicImage_iff_flatMap (f a) (fun b => [Sum.inr b]) y).mp hy
    have hy_eq : y = u.map Sum.inr := by
      rw [← hflat]
      simpa [Function.comp_def] using
        (List.flatMap_pure_eq_map (fun b : β => Sum.inr b) u)
    exact ⟨a, u, hu, by simp [hy_eq]⟩
  · rintro ⟨a, u, hu, rfl⟩
    change Sum.inl a :: List.map Sum.inr u ∈
      (⋃ a, ({[Sum.inl a]} : Language (α ⊕ β)) *
        ((f a).homomorphicImage fun b => [Sum.inr b]))
    simp only [Set.mem_iUnion]
    refine ⟨a, ?_⟩
    refine ⟨[Sum.inl a], Set.mem_singleton _, u.map Sum.inr, ?_, rfl⟩
    exact (mem_homomorphicImage_iff_flatMap (f a) (fun b => [Sum.inr b]) _).mpr
      ⟨u, hu, by
        simpa [Function.comp_def] using
          (List.flatMap_pure_eq_map (fun b : β => Sum.inr b) u)⟩

private theorem forall₂_mem_map {f : α → Language β} :
    ∀ {W : List (List β)} {x : List α},
      List.Forall₂ (fun u a => u ∈ f a) W x →
      List.Forall₂ (fun u L => u ∈ L) W (x.map f)
  | [], [], _ => by simp
  | _ :: _, [], h => by cases h
  | [], _ :: _, h => by cases h
  | u :: W, a :: x, h => by
      cases h with
      | cons hu hrest =>
          exact List.Forall₂.cons hu (forall₂_mem_map hrest)

private theorem encode_subst_witness (f : α → Language β) :
    ∀ {W : List (List β)} {x : List α},
      List.Forall₂ (fun u a => u ∈ f a) W x →
      ∃ ys : List (List (α ⊕ β)),
        ys.flatten.flatMap (@substProj α β) = x ∧
        ys.flatten.flatMap (@substErase α β) = W.flatten ∧
        ∀ y ∈ ys, y ∈ substBlock f
  | [], [], _ => by
      refine ⟨[], by simp, by simp, by simp⟩
  | _ :: _, [], h => by cases h
  | [], _ :: _, h => by cases h
  | u :: W, a :: x, h => by
      rw [List.forall₂_cons] at h
      obtain ⟨ys, hproj, herase, hys⟩ := encode_subst_witness f h.2
      refine ⟨(Sum.inl a :: u.map Sum.inr) :: ys, ?_, ?_, ?_⟩
      · simp [substProj, hproj, List.flatMap_append]
      · simp [substErase, herase, List.flatMap_append]
      · intro y hy
        rcases (List.mem_cons.mp hy) with hyHead | hyTail
        · rw [hyHead]
          exact (mem_substBlock_iff f _).mpr ⟨a, u, h.1, rfl⟩
        · exact hys y hyTail

private theorem decode_subst_blocks (f : α → Language β) :
    ∀ Y : List (List (α ⊕ β)),
      (∀ y ∈ Y, y ∈ substBlock f) →
      ∃ x W,
        List.Forall₂ (fun u a => u ∈ f a) W x ∧
        Y.flatten.flatMap (@substProj α β) = x ∧
        Y.flatten.flatMap (@substErase α β) = W.flatten
  | [], _ => by
      exact ⟨[], [], by simp, by simp, by simp⟩
  | y :: Y, hY => by
      have hy : y ∈ substBlock f := hY y (by simp)
      obtain ⟨a, u, hu, rfl⟩ := (mem_substBlock_iff f y).mp hy
      obtain ⟨x, W, hW, hproj, herase⟩ := decode_subst_blocks f Y
        (fun z hz => hY z (List.mem_cons_of_mem _ hz))
      refine ⟨a :: x, u :: W, ?_, ?_, ?_⟩
      · rw [List.forall₂_cons]
        exact ⟨hu, hW⟩
      · simp [substProj, hproj, List.flatMap_append]
      · simp [substErase, herase, List.flatMap_append]

theorem subst_coding_eq_subst (L : Language α) (f : α → Language β) :
    (((KStar.kstar (substBlock f)) ⊓
        ({ y : List (α ⊕ β) | y.flatMap (@substProj α β) ∈ L } : Language (α ⊕ β)))
      ).homomorphicImage (@substErase α β) = L.subst f := by
  ext w
  rw [mem_homomorphicImage_iff_flatMap]
  constructor
  · rintro ⟨y, hy, herase⟩
    rcases hy with ⟨hyStar, hyProj⟩
    obtain ⟨Y, rfl, hY⟩ := Language.mem_kstar.mp hyStar
    obtain ⟨x, W, hW, hproj, hflatten⟩ := decode_subst_blocks f Y hY
    refine ⟨x, ?_, ?_⟩
    ·
      change Y.flatten.flatMap (@substProj α β) ∈ L at hyProj
      rwa [hproj] at hyProj
    · rw [← herase, hflatten]
      exact (Language.mem_list_prod_iff_forall2 (x.map f) W.flatten).mpr
        ⟨W, rfl, forall₂_mem_map hW⟩
  · intro hw
    simp only [subst] at hw
    obtain ⟨x, hxL, hwprod⟩ := hw
    obtain ⟨W, hWflat, hW⟩ := (Language.mem_list_prod_iff_forall2 (x.map f) w).mp hwprod
    have hW' : List.Forall₂ (fun u a => u ∈ f a) W x := by
      clear hWflat hxL hwprod
      induction x generalizing W with
      | nil =>
          cases W <;> simp_all
      | cons a x ih =>
          cases W with
          | nil => cases hW
          | cons u W =>
              cases hW with
              | cons hu hrest =>
                  exact List.Forall₂.cons hu (ih W hrest)
    obtain ⟨Y, hproj, herase, hY⟩ := encode_subst_witness f hW'
    refine ⟨Y.flatten, ⟨?_, ?_⟩, ?_⟩
    · exact Language.join_mem_kstar hY
    ·
      change Y.flatten.flatMap (@substProj α β) ∈ L
      rwa [hproj]
    · rw [herase, ← hWflat]

end Language

variable [Fintype α] [Fintype β]

/-- The encoded single-block language for an RE substitution family is RE. -/
theorem RE_of_substBlock_RE (f : α → Language β) (hf : ∀ a, is_RE (f a)) :
    is_RE (Language.substBlock f) := by
  classical
  apply (RE_of_finite_iUnion (α := α ⊕ β) (ι := α)
    (fun a => ({[Sum.inl a]} : Language (α ⊕ β)) *
      ((f a).homomorphicImage fun b => [Sum.inr b])))
  intro a
  have hmarker : is_RE ({[Sum.inl a]} : Language (α ⊕ β)) :=
    is_RE_of_isRegular (Language.isRegular_singleton_word [Sum.inl a])
  have hchunk : is_RE ((f a).homomorphicImage fun b => [Sum.inr b]) :=
    RE_closed_under_homomorphism (α := β) (β := α ⊕ β)
      (f a) (fun b => [Sum.inr b]) (hf a)
  exact RE_of_RE_c_RE ({[Sum.inl a]} : Language (α ⊕ β))
    ((f a).homomorphicImage fun b => [Sum.inr b]) ⟨hmarker, hchunk⟩

/-- RE languages over finite alphabets are closed under substitution. -/
theorem RE_of_subst_RE (L : Language α) (f : α → Language β)
    (hL : is_RE L) (hf : ∀ a, is_RE (f a)) :
    is_RE (L.subst f) := by
  classical
  have hBlock : is_RE (Language.substBlock f) := RE_of_substBlock_RE f hf
  have hStar : is_RE (KStar.kstar (Language.substBlock f)) :=
    RE_of_star_RE (Language.substBlock f) hBlock
  have hInv : is_RE ({ y : List (α ⊕ β) | y.flatMap (@Language.substProj α β) ∈ L } :
      Language (α ⊕ β)) :=
    RE_of_inverseHomomorphism_RE L (@Language.substProj α β) hL
  have hCoded : is_RE ((KStar.kstar (Language.substBlock f)) ⊓
      ({ y : List (α ⊕ β) | y.flatMap (@Language.substProj α β) ∈ L } :
        Language (α ⊕ β))) :=
    RE_of_RE_i_RE (KStar.kstar (Language.substBlock f))
      ({ y : List (α ⊕ β) | y.flatMap (@Language.substProj α β) ∈ L } :
        Language (α ⊕ β)) ⟨hStar, hInv⟩
  have hImage : is_RE ((((KStar.kstar (Language.substBlock f)) ⊓
        ({ y : List (α ⊕ β) | y.flatMap (@Language.substProj α β) ∈ L } :
          Language (α ⊕ β))).homomorphicImage (@Language.substErase α β))) :=
    RE_closed_under_homomorphism
      ((KStar.kstar (Language.substBlock f)) ⊓
        ({ y : List (α ⊕ β) | y.flatMap (@Language.substProj α β) ∈ L } :
          Language (α ⊕ β)))
      (@Language.substErase α β) hCoded
  rwa [Language.subst_coding_eq_subst] at hImage

/-- The class of recursively enumerable languages is closed under substitution. -/
theorem RE_closedUnderSubstitution : ClosedUnderSubstitution is_RE :=
  fun L f hL hf => RE_of_subst_RE L f hL hf
