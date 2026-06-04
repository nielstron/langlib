module

public import Langlib.Examples.AlphabetABC
public import Langlib.Examples.AnBnCm
public import Langlib.Examples.AnBmCm
@[expose]
public section

/-! # Positive `a b c` slice witnesses

The witness languages used for the non-closure of deterministic context-free languages
under union and Kleene star. They restrict the standard `{aⁿbⁿcᵐ}` / `{aⁿbᵐcᵐ}` witnesses
to the regular slice `a⁺b⁺c⁺` (`abcPositive`), which prevents a Kleene-star slice from
splitting one `a⁺b⁺c⁺` payload into several witness blocks.

The positive `{aⁿbⁿcⁿ}` witness is the shared `lang_eq_eq_pos` of
`Langlib.Examples.AnBnCnPos`; the identity `lang_eq_eq_pos = lang_eq_eq ⊓ abcPositive` is
`lang_eq_eq_pos_eq_inter` in
`Langlib.Classes.DeterministicContextFree.Examples.AbcPositive`.

Class-membership facts live in
`Langlib.Classes.DeterministicContextFree.Examples.AbcPositive`.
-/

/-- The regular slice `a⁺ b⁺ c⁺` over `Fin 3`. -/
public def abcPositive : Language (Fin 3) :=
  fun w => ∃ n m k : ℕ,
    w = List.replicate (n + 1) a_ ++
        List.replicate (m + 1) b_ ++
        List.replicate (k + 1) c_

/-- `{aⁿbⁿcᵐ}` restricted to the positive slice. -/
public def lang_eq_any_pos : Language (Fin 3) :=
  lang_eq_any ⊓ abcPositive

/-- `{aⁿbᵐcᵐ}` restricted to the positive slice. -/
public def lang_any_eq_pos : Language (Fin 3) :=
  lang_any_eq ⊓ abcPositive

/-- The positive-slice words that are not `{aⁿbⁿcᵐ}`. -/
public def lang_not_eq_any_pos : Language (Fin 3) :=
  lang_eq_any_posᶜ ⊓ abcPositive

/-- The positive-slice words that are not `{aⁿbᵐcᵐ}`. -/
public def lang_not_any_eq_pos : Language (Fin 3) :=
  lang_any_eq_posᶜ ⊓ abcPositive

end
