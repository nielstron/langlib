module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.DPDAToFirstOrder

@[expose]
public section

/-!
# Injectivity of the fresh-endmarker language encoding

Pair normalization embeds a source word as `word.map some ++ [none]`.
The fresh final marker makes this word map injective, and therefore equality of
the normalized languages is exactly equality of the source languages.
-/

namespace DCFEquivalence

namespace DPDANormalization

/-- Append one fresh endmarker after lifting every source symbol. -/
@[expose] public def endmarkedWord {Action : Type}
    (word : List Action) : List (Option Action) :=
  word.map some ++ [none]

/-- Image of a language under the fresh-endmarker word encoding. -/
@[expose] public def endmarkedLanguage {Action : Type}
    (language : Language Action) : Language (Option Action) :=
  {word | ∃ sourceWord ∈ language,
    word = endmarkedWord sourceWord}

public theorem endmarkedWord_injective {Action : Type} :
    Function.Injective (endmarkedWord (Action := Action)) := by
  intro left right hequal
  have hmaps : left.map some = right.map some := by
    exact List.append_cancel_right hequal
  exact (List.map_injective_iff.mpr (Option.some_injective Action)) hmaps

/-- Fresh-endmarker language encoding is injective on arbitrary languages. -/
public theorem endmarkedLanguage_injective {Action : Type} :
    Function.Injective (endmarkedLanguage (Action := Action)) := by
  intro left right hequal
  apply Set.ext
  intro word
  constructor
  · intro hleft
    have hencoded : endmarkedWord word ∈ endmarkedLanguage left :=
      ⟨word, hleft, rfl⟩
    rw [hequal] at hencoded
    obtain ⟨sourceWord, hright, hword⟩ := hencoded
    have : word = sourceWord :=
      endmarkedWord_injective hword
    simpa [this] using hright
  · intro hright
    have hencoded : endmarkedWord word ∈ endmarkedLanguage right :=
      ⟨word, hright, rfl⟩
    rw [← hequal] at hencoded
    obtain ⟨sourceWord, hleft, hword⟩ := hencoded
    have : word = sourceWord :=
      endmarkedWord_injective hword
    simpa [this] using hleft

public theorem endmarkedLanguage_eq_iff {Action : Type}
    {left right : Language Action} :
    endmarkedLanguage left = endmarkedLanguage right ↔ left = right := by
  constructor
  · intro hequal
    exact endmarkedLanguage_injective hequal
  · exact congrArg endmarkedLanguage

end DPDANormalization

end DCFEquivalence
