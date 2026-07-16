module

public import Langlib.Classes.DeterministicContextFree.Closure.Bijection
public import Langlib.Classes.DeterministicContextFree.Closure.IntersectionRegular
public import Langlib.Classes.DeterministicContextFree.Closure.QuotientRegular
public import Langlib.Classes.Regular.Closure.Homomorphism
public import Langlib.Classes.Regular.Closure.Concatenation
public import Langlib.Classes.Regular.Examples.SingletonWord
public import Langlib.Classes.Regular.Examples.TopBot
public import Mathlib.Data.Fintype.Option

@[expose]
public section

/-!
# Removing an explicit endmarker

An LR parser can read a fresh marker to make end-of-input observable.  This
file packages the language-level step which removes that implementation
device: quotient by the singleton marker, then pull the result back along the
injective `Option.some` embedding.
-/

open Language

variable {T : Type}

/-- Append a fresh `none` endmarker after embedding every original terminal
with `some`. -/
@[expose]
public def endmarked (L : Language T) : Language (Option T) :=
  {v | ∃ w ∈ L, v = w.map some ++ [none]}

/-- The regular shape language consisting of any number of embedded terminals
followed by exactly one endmarker. -/
@[expose]
public def endmarkedShape : Language (Option T) :=
  endmarked (⊤ : Language T)

public theorem endmarkedShape_eq :
    endmarkedShape (T := T) =
      Language.map some (⊤ : Language T) *
        ({[none]} : Language (Option T)) := by
  ext v
  constructor
  · rintro ⟨w, _, rfl⟩
    exact ⟨w.map some, ⟨w, trivial, rfl⟩, [none], rfl, rfl⟩
  · rintro ⟨u, ⟨w, _, rfl⟩, marker, hmarker, rfl⟩
    have hmarker' : marker = [none] := by simpa using hmarker
    subst marker
    exact ⟨w, trivial, rfl⟩

/-- Properly endmarked words form a regular language. -/
public theorem endmarkedShape_isRegular :
    (endmarkedShape (T := T)).IsRegular := by
  rw [endmarkedShape_eq]
  exact (Language.isRegular_top.map some).mul'
    (singletonWordLanguage_isRegular ([none] : List (Option T)))

/-- It suffices for a DPDA implementation to be correct on properly marked
inputs.  Intersecting its language with the regular marker-shape language
removes any behavior it may have on malformed encodings. -/
public theorem is_DCF_endmarked_of_marked_machine [Fintype T]
    (L : Language T) (K : Language (Option T))
    (hK : is_DCF K)
    (hcorrect : ∀ w : List T,
      w.map some ++ [none] ∈ K ↔ w ∈ L) :
    is_DCF (endmarked L) := by
  have heq : endmarked L = K ⊓ endmarkedShape := by
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨(hcorrect w).2 hw, ⟨w, trivial, rfl⟩⟩
    · rintro ⟨hvK, w, _, rfl⟩
      exact ⟨w, (hcorrect w).1 hvK, rfl⟩
  rw [heq]
  exact DCF_inter_regular K endmarkedShape hK endmarkedShape_isRegular

/-- Removing the final marker from an endmarked language leaves exactly the
letterwise `some` image of the original language. -/
public theorem endmarked_rightQuotient_marker (L : Language T) :
    endmarked L / ({[none]} : Language (Option T)) =
      Language.map some L := by
  ext v
  constructor
  · rintro ⟨marker, hmarker, hv⟩
    have hmarker' : marker = [none] := by simpa using hmarker
    subst marker
    rcases hv with ⟨w, hw, heq⟩
    have hvmap : v = w.map some := by
      exact List.append_cancel_right heq
    exact ⟨w, hw, hvmap.symm⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨[none], rfl, w, hw, rfl⟩

/-- If the explicitly endmarked language is deterministic context-free, then
so is the original language. -/
public theorem is_DCF_of_is_DCF_endmarked [Fintype T] (L : Language T)
    (hL : is_DCF (endmarked L)) : is_DCF L := by
  have hquot : is_DCF
      (endmarked L / ({[none]} : Language (Option T))) :=
    is_DCF_rightQuotient_regular hL
      (singletonWordLanguage_isRegular ([none] : List (Option T)))
  rw [endmarked_rightQuotient_marker] at hquot
  exact DCF_of_map_injective_DCF_rev (Option.some_injective T) L hquot

end
