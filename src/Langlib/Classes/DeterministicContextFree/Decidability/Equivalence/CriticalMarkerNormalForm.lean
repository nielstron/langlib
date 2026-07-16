module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.CriticalMarkerExposure
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.GrammarNormalForm

@[expose]
public section

/-!
# Exposing normal form under critical-marker extension

Fresh critical markers are nullary, so they add no formal successor
positions.  Every successor position of the extended grammar therefore comes
from the original grammar, and its exposing word can be lifted pointwise
through the left action injection.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

omit [DecidableEq Action] in
public theorem withCriticalMarkers_rank_originalSymbol
    (g : EncodedFirstOrderGrammar Action) (count : ℕ)
    (X : Fin g.ranks.length) :
    (g.withCriticalMarkers count).ranks.get
        ⟨X.val, by
          simpa [withCriticalMarkers_ranks] using
            (lt_of_lt_of_le X.isLt (Nat.le_add_right _ _))⟩ =
      g.ranks.get X := by
  have hextended :
      (g.withCriticalMarkers count).ranks[X.val]? =
        some ((g.withCriticalMarkers count).ranks.get
          ⟨X.val, by
            simpa [withCriticalMarkers_ranks] using
              (lt_of_lt_of_le X.isLt (Nat.le_add_right _ _))⟩) := by
    rw [List.getElem?_eq_some_iff]
    exact ⟨by
      simpa [withCriticalMarkers_ranks] using
        (lt_of_lt_of_le X.isLt (Nat.le_add_right _ _)), rfl⟩
  have horiginal :
      g.ranks[X.val]? = some (g.ranks.get X) := by
    simp
  have hlookup :
      (g.withCriticalMarkers count).ranks[X.val]? = g.ranks[X.val]? := by
    change (g.ranks ++ List.replicate count 0)[X.val]? = g.ranks[X.val]?
    exact List.getElem?_append_left X.isLt
  exact Option.some.inj (hextended.symm.trans (hlookup.trans horiginal))

/-- The same formal successor position in a critical-marker extension.
Fresh markers are nullary, so all successor positions arise this way. -/
@[expose] public def liftSuccessorPosition
    (g : EncodedFirstOrderGrammar Action) (count : ℕ)
    (position : g.SuccessorPosition) :
    (g.withCriticalMarkers count).SuccessorPosition := by
  let X : Fin (g.withCriticalMarkers count).ranks.length :=
    ⟨position.1.val, by
      simpa [withCriticalMarkers_ranks] using
        (lt_of_lt_of_le position.1.isLt (Nat.le_add_right _ _))⟩
  have hrank :
      (g.withCriticalMarkers count).ranks.get X =
        g.ranks.get position.1 := by
    exact withCriticalMarkers_rank_originalSymbol g count position.1
  exact ⟨X, ⟨position.2.val, by
    simpa only [hrank] using position.2.isLt⟩⟩

/-- An ordinary word exposing an original successor still exposes the lifted
successor after adding critical markers. -/
public theorem ExposesSuccessor.withCriticalMarkers
    {g : EncodedFirstOrderGrammar Action}
    {position : g.SuccessorPosition} {word : List Action}
    (hexposes : g.ExposesSuccessor position word) (count : ℕ) :
    (g.withCriticalMarkers count).ExposesSuccessor
      (g.liftSuccessorPosition count position) (word.map Sum.inl) := by
  obtain ⟨target, hrun, hequivalent⟩ := hexposes
  have hrank :
      (g.withCriticalMarkers count).ranks.get
          (g.liftSuccessorPosition count position).1 =
        g.ranks.get position.1 := by
    exact withCriticalMarkers_rank_originalSymbol g count position.1
  have htemplate :
      RegularTerm.symbolTemplate
          (g.liftSuccessorPosition count position).1
          ((g.withCriticalMarkers count).ranks.get
            (g.liftSuccessorPosition count position).1) =
        RegularTerm.symbolTemplate position.1
          (g.ranks.get position.1) := by
    calc
      _ = RegularTerm.symbolTemplate
          (g.liftSuccessorPosition count position).1
          (g.ranks.get position.1) :=
        congrArg
          (RegularTerm.symbolTemplate
            (g.liftSuccessorPosition count position).1)
          hrank
      _ = _ := by rfl
  refine ⟨target, ?_, ?_⟩
  · rw [g.withCriticalMarkers_runActions?_lift count, htemplate]
    exact hrun
  · simpa [liftSuccessorPosition] using hequivalent

omit [DecidableEq Action] in
private theorem originalSymbol_of_extendedSuccessor
    (g : EncodedFirstOrderGrammar Action) (count : ℕ)
    (position : (g.withCriticalMarkers count).SuccessorPosition) :
    position.1.val < g.ranks.length := by
  by_contra hnot
  have hge : g.ranks.length ≤ position.1.val := Nat.le_of_not_gt hnot
  have hpositionBound :
      position.1.val < g.ranks.length + count := by
    simpa [withCriticalMarkers_ranks] using position.1.isLt
  have hoffset : position.1.val - g.ranks.length < count := by
    omega
  have hlookup :
      (g.withCriticalMarkers count).ranks[position.1.val]? = some 0 := by
    change (g.ranks ++ List.replicate count 0)[position.1.val]? = some 0
    rw [List.getElem?_append_right hge]
    simp [hoffset]
  have hget :
      (g.withCriticalMarkers count).ranks[position.1.val]? =
        some ((g.withCriticalMarkers count).ranks.get position.1) := by
    simp
  have hrank :
      (g.withCriticalMarkers count).ranks.get position.1 = 0 :=
    Option.some.inj (hget.symm.trans hlookup)
  have hchild := position.2.isLt
  omega

omit [DecidableEq Action] in
private theorem extendedRank_eq_originalRank
    (g : EncodedFirstOrderGrammar Action) (count : ℕ)
    (position : (g.withCriticalMarkers count).SuccessorPosition)
    (hX : position.1.val < g.ranks.length) :
    (g.withCriticalMarkers count).ranks.get position.1 =
      g.ranks.get ⟨position.1.val, hX⟩ := by
  have hextended :
      (g.withCriticalMarkers count).ranks[position.1.val]? =
        some ((g.withCriticalMarkers count).ranks.get position.1) := by
    simp
  have horiginal :
      g.ranks[position.1.val]? =
        some (g.ranks.get ⟨position.1.val, hX⟩) := by
    simp
  have hlookup :
      (g.withCriticalMarkers count).ranks[position.1.val]? =
        g.ranks[position.1.val]? := by
    change (g.ranks ++ List.replicate count 0)[position.1.val]? =
      g.ranks[position.1.val]?
    exact List.getElem?_append_left hX
  exact Option.some.inj (hextended.symm.trans (hlookup.trans horiginal))

/-- Adding finitely many fresh nullary critical markers preserves exposing
normal form.  Original exposing words are lifted through the left summand of
the enlarged ordinary-action alphabet. -/
public theorem withCriticalMarkers_exposingNormalForm
    {g : EncodedFirstOrderGrammar Action}
    (hnormal : g.ExposingNormalForm) (count : ℕ) :
    (g.withCriticalMarkers count).ExposingNormalForm := by
  intro position
  have hX := originalSymbol_of_extendedSuccessor g count position
  have hrank := extendedRank_eq_originalRank g count position hX
  let originalX : Fin g.ranks.length := ⟨position.1.val, hX⟩
  let originalChild : Fin (g.ranks.get originalX) :=
    ⟨position.2.val, by
      rw [← hrank]
      exact position.2.isLt⟩
  let originalPosition : g.SuccessorPosition :=
    ⟨originalX, originalChild⟩
  obtain ⟨word, target, hrun, hequivalent⟩ :=
    hnormal originalPosition
  have htemplate :
      RegularTerm.symbolTemplate position.1
          ((g.withCriticalMarkers count).ranks.get position.1) =
        RegularTerm.symbolTemplate originalPosition.1
          (g.ranks.get originalPosition.1) := by
    calc
      _ = RegularTerm.symbolTemplate position.1
          (g.ranks.get originalX) :=
        congrArg (RegularTerm.symbolTemplate position.1) hrank
      _ = _ := by rfl
  refine ⟨word.map Sum.inl, target, ?_, ?_⟩
  · rw [g.withCriticalMarkers_runActions?_lift count]
    rw [htemplate]
    exact hrun
  · simpa [originalPosition, originalChild] using hequivalent

omit [DecidableEq Action] in
private theorem exists_originalActions_of_lifted_action_labels
    {extendedActions : List (Action ⊕ ℕ)}
    {originalWord : List (Label Action)}
    (hword :
      extendedActions.map Sum.inl =
        originalWord.map liftCriticalLabel) :
    ∃ originalActions : List Action,
      extendedActions = originalActions.map Sum.inl := by
  induction extendedActions generalizing originalWord with
  | nil =>
      exact ⟨[], rfl⟩
  | cons extendedAction extendedActions ih =>
      cases originalWord with
      | nil =>
          simp at hword
      | cons originalLabel originalWord =>
          simp only [List.map_cons, List.cons.injEq] at hword
          obtain ⟨hhead, htail⟩ := hword
          cases extendedAction with
          | inl action =>
              cases originalLabel with
              | inl originalAction =>
                  simp only [liftCriticalLabel,
                    Sum.inl.injEq] at hhead
                  subst originalAction
                  obtain ⟨actions, hactions⟩ := ih htail
                  exact ⟨action :: actions, by simp [hactions]⟩
              | inr x =>
                  simp [liftCriticalLabel] at hhead
          | inr marker =>
              cases originalLabel <;>
                simp [liftCriticalLabel] at hhead

/-- Every successful successor-exposing word in a critical-marker extension
uses only injected original actions.  Fresh markers have rank zero and hence
no successor positions, while the formal source template contains only its
original root symbol and variables. -/
public theorem withCriticalMarkers_exposesSuccessor_exists_originalActions
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {count : ℕ} {word : List (Action ⊕ ℕ)}
    (position :
      (g.withCriticalMarkers count).SuccessorPosition)
    (hexposes :
      (g.withCriticalMarkers count).ExposesSuccessor position word) :
    ∃ originalActions : List Action,
      word = originalActions.map Sum.inl := by
  let extended := g.withCriticalMarkers count
  obtain ⟨target, hrun, _hequivalent⟩ :=
    hexposes
  have hX := originalSymbol_of_extendedSuccessor g count position
  have hrankEq :=
    extendedRank_eq_originalRank g count position hX
  have hrank :
      g.ranks[position.1.val]? =
        some (extended.ranks.get position.1) := by
    have horiginal :
        g.ranks[position.1.val]? =
          some (g.ranks.get ⟨position.1.val, hX⟩) := by
      simp
    calc
      g.ranks[position.1.val]? =
          some (g.ranks.get ⟨position.1.val, hX⟩) := horiginal
      _ = some (extended.ranks.get position.1) := by
        exact congrArg some hrankEq.symm
  have htemplate :
      (RegularTerm.symbolTemplate position.1
        (extended.ranks.get position.1)).WellFormed
          g.ranks (extended.ranks.get position.1) := by
    simpa using RegularTerm.symbolTemplate_wellFormed hrank
  have hrunLabels :
      extended.run? (word.map Sum.inl)
        (RegularTerm.symbolTemplate position.1
          (extended.ranks.get position.1)) = some target := by
    simpa [runActions?] using hrun
  obtain ⟨originalWord, hword, _horiginalRun⟩ :=
    (withCriticalMarkers_run?_some_iff_original
      g hg count
      (RegularTerm.usesOriginalSymbols_of_wellFormed
        htemplate)).mp hrunLabels
  obtain ⟨originalActions, hactions⟩ :=
    exists_originalActions_of_lifted_action_labels hword
  exact ⟨originalActions, hactions⟩

/-- In particular, every canonical exposing word selected by normal form in
a critical-marker extension consists only of injected original actions. -/
public theorem withCriticalMarkers_exposingWord_exists_originalActions
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {count : ℕ}
    (hnormal : (g.withCriticalMarkers count).ExposingNormalForm)
    (position :
      (g.withCriticalMarkers count).SuccessorPosition) :
    ∃ originalActions : List Action,
      (g.withCriticalMarkers count).exposingWord hnormal position =
        originalActions.map Sum.inl :=
  g.withCriticalMarkers_exposesSuccessor_exists_originalActions
    hg position
      ((g.withCriticalMarkers count).exposingWord_exposes
        hnormal position)

private theorem foldr_max_map_le
    {α : Type} (xs : List α) (f : α → ℕ) (bound : ℕ)
    (hbound : ∀ x ∈ xs, f x ≤ bound) :
    (xs.map f).foldr max 0 ≤ bound := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.foldr_cons]
      apply max_le
      · exact hbound x (by simp)
      · exact ih (fun y hy => hbound y (by simp [hy]))

/-- Adding fresh nullary critical markers does not increase the canonical
exposure bound.  The statement is uniform in the number of markers: every
extended successor is an original successor, and its lifted original
shortest exposing word is still available. -/
public theorem withCriticalMarkers_exposureBound_le
    {g : EncodedFirstOrderGrammar Action}
    (hnormal : g.ExposingNormalForm) (count : ℕ) :
    (g.withCriticalMarkers count).exposureBound
        (g.withCriticalMarkers_exposingNormalForm hnormal count) ≤
      g.exposureBound hnormal := by
  unfold exposureBound
  apply Nat.add_le_add_left
  apply foldr_max_map_le
  intro position _
  have hX := originalSymbol_of_extendedSuccessor g count position
  have hrank := extendedRank_eq_originalRank g count position hX
  let originalX : Fin g.ranks.length := ⟨position.1.val, hX⟩
  let originalChild : Fin (g.ranks.get originalX) :=
    ⟨position.2.val, by
      rw [← hrank]
      exact position.2.isLt⟩
  let originalPosition : g.SuccessorPosition :=
    ⟨originalX, originalChild⟩
  have hposition :
      g.liftSuccessorPosition count originalPosition = position := by
    have hfirst :
        (g.liftSuccessorPosition count originalPosition).1 = position.1 := by
      apply Fin.ext
      rfl
    apply Sigma.ext hfirst
    cases hfirst
    apply heq_of_eq
    apply Fin.ext
    rfl
  have hexposes :
      (g.withCriticalMarkers count).ExposesSuccessor position
        ((g.exposingWord hnormal originalPosition).map Sum.inl) := by
    rw [← hposition]
    exact (g.exposingWord_exposes hnormal originalPosition).withCriticalMarkers count
  have hlength :
      ((g.withCriticalMarkers count).exposingWord
          (g.withCriticalMarkers_exposingNormalForm hnormal count)
          position).length ≤
        (g.exposingWord hnormal originalPosition).length := by
    calc
      _ = (g.withCriticalMarkers count).exposingLength
          (g.withCriticalMarkers_exposingNormalForm hnormal count)
          position := exposingWord_length _ _
      _ ≤ ((g.exposingWord hnormal originalPosition).map Sum.inl).length :=
        exposingLength_le _ _ hexposes
      _ = (g.exposingWord hnormal originalPosition).length := by simp
  exact hlength.trans (List.le_max_of_le
    (List.mem_map.mpr ⟨originalPosition,
      g.mem_successorPositions originalPosition, rfl⟩)
    (le_refl _))

end EncodedFirstOrderGrammar

end DCFEquivalence
