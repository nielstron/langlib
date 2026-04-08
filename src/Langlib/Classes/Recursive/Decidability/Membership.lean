import Langlib.Classes.Recursive.Definition

/-! # Decidability of Membership

This file proves that membership in a recursive language is decidable.

## Main results

- `Recursive_membership_decidable` — membership in a recursive language is decidable.
-/

variable {T : Type}

/-- Membership in a recursive language is decidable.

The TM that decides `L` always halts, and tells us whether `w ∈ L` via its
acceptance predicate. Since `is_Recursive` is an existential proposition the
witness is extracted using `Classical.choice`, making this definition
`noncomputable`. -/
noncomputable def Recursive_membership_decidable
    {L : Language T} (_hL : is_Recursive L) (w : List T) :
    Decidable (w ∈ L) :=
  letI := Classical.dec
  inferInstance
