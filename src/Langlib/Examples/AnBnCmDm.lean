module

public import Langlib.Examples.AnBn
@[expose]
public section

/-! # The language `{0ⁿ1ⁿ2ᵐ3ᵐ}` over `Fin 4`

The witness language used for `Linear ⊊ CF` and the non-closure of linear languages
under concatenation. It is the concatenation of two relabelled copies of `{aⁿbⁿ}`
(`anbn`): one mapped onto `0`/`1` and one onto `2`/`3`.

Class-membership facts live in `Langlib.Classes.ContextFree.Examples.AnBnCmDm`
(`anbncmdm_is_CF`) and `Langlib.Classes.Linear.Examples.AnBnCmDm`
(`anbncmdm_not_is_Linear`).
-/

/-- Inject `aⁿbⁿ`'s alphabet to `0`/`1`. -/
public def f4 : Bool → Fin 4 := fun b => if b then 1 else 0
/-- Inject `aⁿbⁿ`'s alphabet to `2`/`3`. -/
public def g4 : Bool → Fin 4 := fun b => if b then 3 else 2

/-- The witness language `{0ⁿ1ⁿ2ᵐ3ᵐ}` over `Fin 4`. -/
public def anbncmdm : Language (Fin 4) := Language.map f4 anbn * Language.map g4 anbn

end
