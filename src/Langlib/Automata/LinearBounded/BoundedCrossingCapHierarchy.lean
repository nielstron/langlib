module

public import Langlib.Automata.LinearBounded.BoundedCrossingZero
public import Langlib.Automata.LinearBounded.HeadTurnCrossing
public import Langlib.Classes.Regular.Examples.EmptyWord
public import Langlib.Classes.Regular.Examples.TopBot
import Mathlib.Tactic

@[expose]
public section

/-!
# Sharp bounded-crossing cap hierarchy

For every finite terminal alphabet, all positive fixed crossing caps, the existential uniform
crossing class, every fixed selected-accepting head-turn cap, DFA languages, NFA languages, and
Mathlib-regular languages are the same class.  The pairwise equalities below state this directly,
without requiring clients to choose an intermediate presentation class.

Crossing cap zero is different: it contains exactly the empty and universal languages.  It is a
subclass of every positive crossing slice over every terminal type, and the inclusion is strict
exactly when the terminal type is nonempty.  The singleton empty-word language is the strictness
witness, so one terminal symbol is both necessary and sufficient.  Over an empty terminal type,
`List T` is a singleton and every language is empty or universal; cap zero therefore already
contains every language.
-/

open LBA.BoundedCrossing

variable {T : Type}

/-! ## Direct equalities throughout the regular part of the hierarchy -/

/-- DFA recognizability and Mathlib regularity define the same language class. -/
public theorem DFA_eq_isRegular :
    (DFA.Class : Set (Language T)) = {language | language.IsRegular} := by
  ext language
  exact Language.isRegular_iff.symm

/-- NFA recognizability and Mathlib regularity define the same language class. -/
public theorem NFA_eq_isRegular :
    (NFA.Class : Set (Language T)) = {language | language.IsRegular} := by
  rw [NFA_eq_DFA, DFA_eq_isRegular]

/-- Every positive fixed crossing slice is directly equal to the Mathlib-regular class. -/
public theorem BoundedCrossingSlice_eq_isRegular
    [Fintype T] {bound : Nat} (hbound : 1 ≤ bound) :
    (BoundedCrossingSlice bound : Set (Language T)) =
      {language | language.IsRegular} := by
  rw [BoundedCrossingSlice_eq_DFA hbound, DFA_eq_isRegular]

/-- The existential uniform selected-accepting crossing class is directly equal to the
Mathlib-regular class. -/
public theorem UniformBoundedCrossingLBA_eq_isRegular [Fintype T] :
    (UniformBoundedCrossingLBA : Set (Language T)) =
      {language | language.IsRegular} := by
  rw [UniformBoundedCrossingLBA_eq_DFA, DFA_eq_isRegular]

/-- Any two positive fixed crossing caps define the same language class. -/
public theorem BoundedCrossingSlice_eq_BoundedCrossingSlice
    [Fintype T] {left right : Nat} (hleft : 1 ≤ left) (hright : 1 ≤ right) :
    (BoundedCrossingSlice left : Set (Language T)) =
      BoundedCrossingSlice right := by
  rw [BoundedCrossingSlice_eq_DFA hleft,
    BoundedCrossingSlice_eq_DFA hright]

/-- Every positive fixed crossing slice is directly equal to the existential uniform crossing
class. -/
public theorem BoundedCrossingSlice_eq_UniformBoundedCrossingLBA
    [Fintype T] {bound : Nat} (hbound : 1 ≤ bound) :
    (BoundedCrossingSlice bound : Set (Language T)) =
      UniformBoundedCrossingLBA := by
  rw [BoundedCrossingSlice_eq_DFA hbound,
    UniformBoundedCrossingLBA_eq_DFA]

/-- Every positive fixed crossing slice is directly equal to every fixed selected-accepting
head-turn class. -/
public theorem BoundedCrossingSlice_eq_HeadTurnBoundedLBA
    [Fintype T] {crossingBound : Nat} (hcrossingBound : 1 ≤ crossingBound)
    (turnBound : Nat) :
    (BoundedCrossingSlice crossingBound : Set (Language T)) =
      HeadTurnBoundedLBA turnBound := by
  rw [BoundedCrossingSlice_eq_DFA hcrossingBound,
    HeadTurnBoundedLBA_eq_DFA]

/-- The existential uniform crossing class is directly equal to every fixed selected-accepting
head-turn class. -/
public theorem UniformBoundedCrossingLBA_eq_HeadTurnBoundedLBA
    [Fintype T] (turnBound : Nat) :
    (UniformBoundedCrossingLBA : Set (Language T)) =
      HeadTurnBoundedLBA turnBound := by
  rw [UniformBoundedCrossingLBA_eq_DFA,
    HeadTurnBoundedLBA_eq_DFA]

/-- All fixed selected-accepting head-turn caps define the same language class, including cap
zero. -/
public theorem HeadTurnBoundedLBA_eq_HeadTurnBoundedLBA
    [Fintype T] (left right : Nat) :
    (HeadTurnBoundedLBA left : Set (Language T)) =
      HeadTurnBoundedLBA right := by
  rw [HeadTurnBoundedLBA_eq_DFA, HeadTurnBoundedLBA_eq_DFA]

/-! ## Cap zero versus positive crossing caps -/

/-- The singleton empty-word language is DFA-recognizable over every terminal type. -/
private theorem emptyWordLanguage_is_DFA :
    is_DFA (emptyWordLanguage T) :=
  Language.isRegular_iff.mp emptyWordLanguage_isRegular

/-- The cap-zero crossing slice is contained directly in the DFA class over every terminal
type. -/
public theorem BoundedCrossingSlice_zero_subset_DFA :
    (BoundedCrossingSlice 0 : Set (Language T)) ⊆ DFA.Class := by
  intro language hlanguage
  rcases (is_BoundedCrossingSlice_zero_iff_eq_empty_or_univ.mp hlanguage) with
    rfl | rfl
  · exact Language.isRegular_iff.mp Language.isRegular_bot
  · exact Language.isRegular_iff.mp Language.isRegular_top

/-- The cap-zero crossing slice is contained directly in the NFA class over every terminal
type. -/
public theorem BoundedCrossingSlice_zero_subset_NFA :
    (BoundedCrossingSlice 0 : Set (Language T)) ⊆ NFA.Class := by
  rw [NFA_eq_DFA]
  exact BoundedCrossingSlice_zero_subset_DFA

/-- The cap-zero crossing slice is contained directly in the Mathlib-regular class over every
terminal type. -/
public theorem BoundedCrossingSlice_zero_subset_isRegular :
    (BoundedCrossingSlice 0 : Set (Language T)) ⊆
      {language | language.IsRegular} := by
  rw [← DFA_eq_isRegular]
  exact BoundedCrossingSlice_zero_subset_DFA

/-- The cap-zero crossing slice is contained directly in the existential uniform crossing
class over every terminal type. -/
public theorem BoundedCrossingSlice_zero_subset_UniformBoundedCrossingLBA :
    (BoundedCrossingSlice 0 : Set (Language T)) ⊆
      UniformBoundedCrossingLBA := by
  intro language hlanguage
  exact is_UniformBoundedCrossingLBA_of_is_DFA
    (BoundedCrossingSlice_zero_subset_DFA hlanguage)

/-- The cap-zero crossing slice is contained directly in every selected-accepting head-turn
class over every terminal type. -/
public theorem BoundedCrossingSlice_zero_subset_HeadTurnBoundedLBA
    (turnBound : Nat) :
    (BoundedCrossingSlice 0 : Set (Language T)) ⊆
      HeadTurnBoundedLBA turnBound := by
  intro language hlanguage
  exact is_HeadTurnBoundedLBA_of_is_DFA turnBound
    (BoundedCrossingSlice_zero_subset_DFA hlanguage)

/-- Any class containing cap zero and the singleton empty-word language strictly contains cap
zero over a nonempty terminal type. -/
private theorem BoundedCrossingSlice_zero_strict_subset_of_mem_emptyWord
    [Nonempty T] {languages : Set (Language T)}
    (hsubset : (BoundedCrossingSlice 0 : Set (Language T)) ⊆ languages)
    (hemptyWord : emptyWordLanguage T ∈ languages) :
    (BoundedCrossingSlice 0 : Set (Language T)) ⊂ languages := by
  refine ssubset_iff_subset_ne.mpr ⟨hsubset, ?_⟩
  intro heq
  have hzero :
      emptyWordLanguage T ∈ (BoundedCrossingSlice 0 : Set (Language T)) := by
    rw [heq]
    exact hemptyWord
  rcases (is_BoundedCrossingSlice_zero_iff_eq_empty_or_univ.mp hzero) with
    hempty | huniv
  · have hnil : ([] : List T) ∈ emptyWordLanguage T := Set.mem_singleton []
    rw [hempty] at hnil
    change False at hnil
    exact hnil
  · obtain ⟨symbol⟩ := (inferInstance : Nonempty T)
    have hsingleton : [symbol] ∈ emptyWordLanguage T := by
      rw [huniv]
      trivial
    exact (List.cons_ne_nil symbol []) (Set.mem_singleton_iff.mp hsingleton)

/-- The cap-zero crossing slice is contained in every positive fixed-cap crossing slice.  This
does not require the terminal type to be finite or inhabited. -/
public theorem BoundedCrossingSlice_zero_subset
    {bound : Nat} (hbound : 1 ≤ bound) :
    (BoundedCrossingSlice 0 : Set (Language T)) ⊆
      BoundedCrossingSlice bound := by
  intro language hlanguage
  rcases (is_BoundedCrossingSlice_zero_iff_eq_empty_or_univ.mp hlanguage) with
    rfl | rfl
  · apply is_BoundedCrossingSlice_of_is_DFA hbound
    exact Language.isRegular_iff.mp Language.isRegular_bot
  · apply is_BoundedCrossingSlice_of_is_DFA hbound
    exact Language.isRegular_iff.mp Language.isRegular_top

/-- Over every nonempty terminal type, cap zero is strictly contained in every positive crossing
slice.  The singleton empty-word language is the witness, so no second alphabet symbol is
needed. -/
public theorem BoundedCrossingSlice_zero_strict_subset
    [Nonempty T] {bound : Nat} (hbound : 1 ≤ bound) :
    (BoundedCrossingSlice 0 : Set (Language T)) ⊂
      BoundedCrossingSlice bound := by
  apply BoundedCrossingSlice_zero_strict_subset_of_mem_emptyWord
    (BoundedCrossingSlice_zero_subset hbound)
  exact is_BoundedCrossingSlice_of_is_DFA hbound emptyWordLanguage_is_DFA

/-- Over every nonempty terminal type, cap zero is strictly contained directly in the DFA
class. -/
public theorem BoundedCrossingSlice_zero_strict_subset_DFA [Nonempty T] :
    (BoundedCrossingSlice 0 : Set (Language T)) ⊂ DFA.Class := by
  exact BoundedCrossingSlice_zero_strict_subset_of_mem_emptyWord
    BoundedCrossingSlice_zero_subset_DFA emptyWordLanguage_is_DFA

/-- Over every nonempty terminal type, cap zero is strictly contained directly in the NFA
class. -/
public theorem BoundedCrossingSlice_zero_strict_subset_NFA [Nonempty T] :
    (BoundedCrossingSlice 0 : Set (Language T)) ⊂ NFA.Class := by
  apply BoundedCrossingSlice_zero_strict_subset_of_mem_emptyWord
    BoundedCrossingSlice_zero_subset_NFA
  exact is_NFA_iff_is_DFA.mpr emptyWordLanguage_is_DFA

/-- Over every nonempty terminal type, cap zero is strictly contained directly in the
Mathlib-regular class. -/
public theorem BoundedCrossingSlice_zero_strict_subset_isRegular [Nonempty T] :
    (BoundedCrossingSlice 0 : Set (Language T)) ⊂
      {language | language.IsRegular} := by
  exact BoundedCrossingSlice_zero_strict_subset_of_mem_emptyWord
    BoundedCrossingSlice_zero_subset_isRegular emptyWordLanguage_isRegular

/-- Over every nonempty terminal type, cap zero is strictly contained directly in the
existential uniform crossing class. -/
public theorem BoundedCrossingSlice_zero_strict_subset_UniformBoundedCrossingLBA
    [Nonempty T] :
    (BoundedCrossingSlice 0 : Set (Language T)) ⊂
      UniformBoundedCrossingLBA := by
  apply BoundedCrossingSlice_zero_strict_subset_of_mem_emptyWord
    BoundedCrossingSlice_zero_subset_UniformBoundedCrossingLBA
  exact is_UniformBoundedCrossingLBA_of_is_DFA emptyWordLanguage_is_DFA

/-- Over every nonempty terminal type, cap zero is strictly contained directly in every
selected-accepting head-turn class. -/
public theorem BoundedCrossingSlice_zero_strict_subset_HeadTurnBoundedLBA
    [Nonempty T] (turnBound : Nat) :
    (BoundedCrossingSlice 0 : Set (Language T)) ⊂
      HeadTurnBoundedLBA turnBound := by
  apply BoundedCrossingSlice_zero_strict_subset_of_mem_emptyWord
    (BoundedCrossingSlice_zero_subset_HeadTurnBoundedLBA turnBound)
  exact is_HeadTurnBoundedLBA_of_is_DFA turnBound emptyWordLanguage_is_DFA

/-- Cardinality form of strictness: one terminal symbol is sufficient for every positive cap. -/
public theorem BoundedCrossingSlice_zero_strict_subset_of_card
    [Fintype T] {bound : Nat} (hbound : 1 ≤ bound)
    (hT : 1 ≤ Fintype.card T) :
    (BoundedCrossingSlice 0 : Set (Language T)) ⊂
      BoundedCrossingSlice bound := by
  letI : Nonempty T := Fintype.card_pos_iff.mp (by omega)
  exact BoundedCrossingSlice_zero_strict_subset hbound

/-- Cardinality form of direct cap-zero strictness below the DFA class. -/
public theorem BoundedCrossingSlice_zero_strict_subset_DFA_of_card
    [Fintype T] (hT : 1 ≤ Fintype.card T) :
    (BoundedCrossingSlice 0 : Set (Language T)) ⊂ DFA.Class := by
  letI : Nonempty T := Fintype.card_pos_iff.mp (by omega)
  exact BoundedCrossingSlice_zero_strict_subset_DFA

/-- Cardinality form of direct cap-zero strictness below the NFA class. -/
public theorem BoundedCrossingSlice_zero_strict_subset_NFA_of_card
    [Fintype T] (hT : 1 ≤ Fintype.card T) :
    (BoundedCrossingSlice 0 : Set (Language T)) ⊂ NFA.Class := by
  letI : Nonempty T := Fintype.card_pos_iff.mp (by omega)
  exact BoundedCrossingSlice_zero_strict_subset_NFA

/-- Cardinality form of direct cap-zero strictness below the Mathlib-regular class. -/
public theorem BoundedCrossingSlice_zero_strict_subset_isRegular_of_card
    [Fintype T] (hT : 1 ≤ Fintype.card T) :
    (BoundedCrossingSlice 0 : Set (Language T)) ⊂
      {language | language.IsRegular} := by
  letI : Nonempty T := Fintype.card_pos_iff.mp (by omega)
  exact BoundedCrossingSlice_zero_strict_subset_isRegular

/-- Cardinality form of direct cap-zero strictness below the uniform crossing class. -/
public theorem BoundedCrossingSlice_zero_strict_subset_UniformBoundedCrossingLBA_of_card
    [Fintype T] (hT : 1 ≤ Fintype.card T) :
    (BoundedCrossingSlice 0 : Set (Language T)) ⊂
      UniformBoundedCrossingLBA := by
  letI : Nonempty T := Fintype.card_pos_iff.mp (by omega)
  exact BoundedCrossingSlice_zero_strict_subset_UniformBoundedCrossingLBA

/-- Cardinality form of direct cap-zero strictness below every head-turn class. -/
public theorem BoundedCrossingSlice_zero_strict_subset_HeadTurnBoundedLBA_of_card
    [Fintype T] (turnBound : Nat) (hT : 1 ≤ Fintype.card T) :
    (BoundedCrossingSlice 0 : Set (Language T)) ⊂
      HeadTurnBoundedLBA turnBound := by
  letI : Nonempty T := Fintype.card_pos_iff.mp (by omega)
  exact BoundedCrossingSlice_zero_strict_subset_HeadTurnBoundedLBA turnBound

/-! ## The empty terminal type -/

/-- If the terminal type is empty, every word is the empty word. -/
private theorem list_eq_nil_of_isEmpty [IsEmpty T] (word : List T) :
    word = [] := by
  cases word with
  | nil => rfl
  | cons symbol _ => exact isEmptyElim symbol

/-- Over an empty terminal type, every language is either empty or universal. -/
public theorem language_eq_empty_or_univ_of_isEmpty
    [IsEmpty T] (language : Language T) :
    language = (∅ : Set (List T)) ∨
      language = (Set.univ : Set (List T)) := by
  by_cases hnil : ([] : List T) ∈ language
  · right
    ext word
    rw [list_eq_nil_of_isEmpty word]
    exact iff_true_intro hnil
  · left
    ext word
    rw [list_eq_nil_of_isEmpty word]
    exact iff_false_intro hnil

/-- Over an empty terminal type, cap zero already contains every language. -/
public theorem BoundedCrossingSlice_zero_eq_univ_of_isEmpty [IsEmpty T] :
    (BoundedCrossingSlice 0 : Set (Language T)) = Set.univ := by
  ext language
  constructor
  · intro _
    trivial
  · intro _
    exact is_BoundedCrossingSlice_zero_iff_eq_empty_or_univ.mpr
      (language_eq_empty_or_univ_of_isEmpty language)

/-- Over an empty terminal type, cap zero and every positive crossing cap coincide. -/
public theorem BoundedCrossingSlice_zero_eq_positive_of_isEmpty
    [IsEmpty T] {bound : Nat} (hbound : 1 ≤ bound) :
    (BoundedCrossingSlice 0 : Set (Language T)) =
      BoundedCrossingSlice bound := by
  apply Set.Subset.antisymm (BoundedCrossingSlice_zero_subset hbound)
  rw [BoundedCrossingSlice_zero_eq_univ_of_isEmpty]
  exact Set.subset_univ _

/-- Over an empty terminal type, every language is DFA-recognizable. -/
public theorem DFA_eq_univ_of_isEmpty [IsEmpty T] :
    (DFA.Class : Set (Language T)) = Set.univ := by
  ext language
  constructor
  · intro _
    trivial
  · intro _
    rcases language_eq_empty_or_univ_of_isEmpty language with rfl | rfl
    · exact Language.isRegular_iff.mp Language.isRegular_bot
    · exact Language.isRegular_iff.mp Language.isRegular_top

/-- Over an empty terminal type, every language is NFA-recognizable. -/
public theorem NFA_eq_univ_of_isEmpty [IsEmpty T] :
    (NFA.Class : Set (Language T)) = Set.univ := by
  rw [NFA_eq_DFA, DFA_eq_univ_of_isEmpty]

/-- Over an empty terminal type, every language is Mathlib-regular. -/
public theorem isRegular_languages_eq_univ_of_isEmpty [IsEmpty T] :
    ({language : Language T | language.IsRegular} : Set (Language T)) =
      Set.univ := by
  rw [← DFA_eq_isRegular, DFA_eq_univ_of_isEmpty]

/-- Empty-terminal cap zero is directly equal to the regular-language class. -/
public theorem BoundedCrossingSlice_zero_eq_isRegular_of_isEmpty [IsEmpty T] :
    (BoundedCrossingSlice 0 : Set (Language T)) =
      {language | language.IsRegular} := by
  rw [BoundedCrossingSlice_zero_eq_univ_of_isEmpty,
    isRegular_languages_eq_univ_of_isEmpty]

/-- Empty-terminal cap zero is directly equal to the DFA class. -/
public theorem BoundedCrossingSlice_zero_eq_DFA_of_isEmpty [IsEmpty T] :
    (BoundedCrossingSlice 0 : Set (Language T)) = DFA.Class := by
  rw [BoundedCrossingSlice_zero_eq_univ_of_isEmpty,
    DFA_eq_univ_of_isEmpty]

/-- Empty-terminal cap zero is directly equal to the NFA class. -/
public theorem BoundedCrossingSlice_zero_eq_NFA_of_isEmpty [IsEmpty T] :
    (BoundedCrossingSlice 0 : Set (Language T)) = NFA.Class := by
  rw [BoundedCrossingSlice_zero_eq_univ_of_isEmpty,
    NFA_eq_univ_of_isEmpty]

/-- Empty-terminal cap zero is directly equal to the existential uniform crossing class. -/
public theorem BoundedCrossingSlice_zero_eq_UniformBoundedCrossingLBA_of_isEmpty
    [IsEmpty T] :
    (BoundedCrossingSlice 0 : Set (Language T)) =
      UniformBoundedCrossingLBA := by
  apply Set.Subset.antisymm
    BoundedCrossingSlice_zero_subset_UniformBoundedCrossingLBA
  rw [BoundedCrossingSlice_zero_eq_univ_of_isEmpty]
  exact Set.subset_univ _

/-- Empty-terminal cap zero is directly equal to every selected-accepting head-turn class. -/
public theorem BoundedCrossingSlice_zero_eq_HeadTurnBoundedLBA_of_isEmpty
    [IsEmpty T] (turnBound : Nat) :
    (BoundedCrossingSlice 0 : Set (Language T)) =
      HeadTurnBoundedLBA turnBound := by
  apply Set.Subset.antisymm
    (BoundedCrossingSlice_zero_subset_HeadTurnBoundedLBA turnBound)
  rw [BoundedCrossingSlice_zero_eq_univ_of_isEmpty]
  exact Set.subset_univ _

/-! ## Exact strictness criterion -/

/-- Cap zero is strictly below a positive crossing cap exactly when the terminal type is
nonempty. -/
public theorem BoundedCrossingSlice_zero_strict_subset_iff_nonempty
    {bound : Nat} (hbound : 1 ≤ bound) :
    (BoundedCrossingSlice 0 : Set (Language T)) ⊂
        BoundedCrossingSlice bound ↔
      Nonempty T := by
  constructor
  · intro hstrict
    by_contra hempty
    letI : IsEmpty T := ⟨fun symbol ↦ hempty ⟨symbol⟩⟩
    exact hstrict.ne (BoundedCrossingSlice_zero_eq_positive_of_isEmpty hbound)
  · intro hnonempty
    letI : Nonempty T := hnonempty
    exact BoundedCrossingSlice_zero_strict_subset hbound

/-- Cap zero is strictly below the DFA class exactly when the terminal type is nonempty. -/
public theorem BoundedCrossingSlice_zero_strict_subset_DFA_iff_nonempty :
    (BoundedCrossingSlice 0 : Set (Language T)) ⊂ DFA.Class ↔
      Nonempty T := by
  constructor
  · intro hstrict
    by_contra hempty
    letI : IsEmpty T := ⟨fun symbol ↦ hempty ⟨symbol⟩⟩
    exact hstrict.ne BoundedCrossingSlice_zero_eq_DFA_of_isEmpty
  · intro hnonempty
    letI : Nonempty T := hnonempty
    exact BoundedCrossingSlice_zero_strict_subset_DFA

/-- Cap zero is strictly below the NFA class exactly when the terminal type is nonempty. -/
public theorem BoundedCrossingSlice_zero_strict_subset_NFA_iff_nonempty :
    (BoundedCrossingSlice 0 : Set (Language T)) ⊂ NFA.Class ↔
      Nonempty T := by
  rw [NFA_eq_DFA]
  exact BoundedCrossingSlice_zero_strict_subset_DFA_iff_nonempty

/-- Cap zero is strictly below the Mathlib-regular class exactly when the terminal type is
nonempty. -/
public theorem BoundedCrossingSlice_zero_strict_subset_isRegular_iff_nonempty :
    (BoundedCrossingSlice 0 : Set (Language T)) ⊂
        {language | language.IsRegular} ↔
      Nonempty T := by
  rw [← DFA_eq_isRegular]
  exact BoundedCrossingSlice_zero_strict_subset_DFA_iff_nonempty

/-- Cap zero is strictly below the existential uniform crossing class exactly when the terminal
type is nonempty. -/
public theorem
    BoundedCrossingSlice_zero_strict_subset_UniformBoundedCrossingLBA_iff_nonempty :
    (BoundedCrossingSlice 0 : Set (Language T)) ⊂
        UniformBoundedCrossingLBA ↔
      Nonempty T := by
  constructor
  · intro hstrict
    by_contra hempty
    letI : IsEmpty T := ⟨fun symbol ↦ hempty ⟨symbol⟩⟩
    exact hstrict.ne
      BoundedCrossingSlice_zero_eq_UniformBoundedCrossingLBA_of_isEmpty
  · intro hnonempty
    letI : Nonempty T := hnonempty
    exact BoundedCrossingSlice_zero_strict_subset_UniformBoundedCrossingLBA

/-- Cap zero is strictly below every selected-accepting head-turn class exactly when the
terminal type is nonempty. -/
public theorem BoundedCrossingSlice_zero_strict_subset_HeadTurnBoundedLBA_iff_nonempty
    (turnBound : Nat) :
    (BoundedCrossingSlice 0 : Set (Language T)) ⊂
        HeadTurnBoundedLBA turnBound ↔
      Nonempty T := by
  constructor
  · intro hstrict
    by_contra hempty
    letI : IsEmpty T := ⟨fun symbol ↦ hempty ⟨symbol⟩⟩
    exact hstrict.ne
      (BoundedCrossingSlice_zero_eq_HeadTurnBoundedLBA_of_isEmpty turnBound)
  · intro hnonempty
    letI : Nonempty T := hnonempty
    exact BoundedCrossingSlice_zero_strict_subset_HeadTurnBoundedLBA turnBound

/-- Finite-cardinality form of the exact strictness criterion. -/
public theorem BoundedCrossingSlice_zero_strict_subset_iff_one_le_card
    [Fintype T] {bound : Nat} (hbound : 1 ≤ bound) :
    ((BoundedCrossingSlice 0 : Set (Language T)) ⊂
        BoundedCrossingSlice bound) ↔
      1 ≤ Fintype.card T := by
  rw [BoundedCrossingSlice_zero_strict_subset_iff_nonempty hbound,
    ← Fintype.card_pos_iff]
  omega

end
