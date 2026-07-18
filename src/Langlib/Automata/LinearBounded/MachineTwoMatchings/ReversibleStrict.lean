module

public import Langlib.Automata.LinearBounded.MachineTwoMatchings.FirstSymbol
public import Langlib.Automata.LinearBounded.MachineTwoMatchings.ReversibleTriviality

@[expose]
public section

/-!
# Configuration-reversible LBAs are strictly weaker than exact two-matching LBAs

The globally configuration-biunique class contains only the empty and universal languages,
whereas the exact-two-matching first-symbol machine recognizes a nonconstant language over every
inhabited finite alphabet.
-/

/-- Over every inhabited finite alphabet, globally configuration-reversible LBA languages form
a strict subclass of exact-two-matching LBA languages. -/
public theorem reversibleLBA_strict_subset_twoMatchingLBA
    {T : Type} [Fintype T] [DecidableEq T] [Nonempty T] :
    (ReversibleLBA : Set (Language T)) ⊂
      (TwoMatchingLBA : Set (Language T)) := by
  refine ssubset_iff_subset_ne.mpr
    ⟨reversibleLBA_subset_twoMatchingLBA, ?_⟩
  intro heq
  obtain ⟨L, htwo, hnil, word, hword⟩ :=
    exists_nonconstant_twoMatchingLBA T
  have hreversible : is_ReversibleLBA L := by
    have hmembership : L ∈ (ReversibleLBA : Set (Language T)) := by
      rw [heq]
      exact htwo
    exact hmembership
  rcases is_ReversibleLBA_iff_eq_empty_or_univ.mp hreversible with hempty | huniv
  · have : word ∈ (∅ : Set (List T)) := by
      rw [← hempty]
      exact hword
    exact this
  · apply hnil
    rw [huniv]
    trivial

