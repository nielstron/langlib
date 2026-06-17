module

public import Langlib.Utilities.ClosurePredicates
public import Langlib.Classes.RecursivelyEnumerable.Definition
public import Langlib.Classes.RecursivelyEnumerable.Examples.Halting
public import Langlib.Classes.RecursivelyEnumerable.Examples.NonHalting
import Langlib.Classes.RecursivelyEnumerable.Closure.Bijection
import Langlib.Classes.RecursivelyEnumerable.Closure.InverseHomomorphism
@[expose]
public section



/-! # RE Non-Closure Under Complement

Key results: `haltingUnary_complement_not_RE` gives a concrete RE language whose complement
is not RE, and `RE_notClosedUnderComplement` packages this as failure of complement closure.

The concrete witnesses come from `Langlib.Classes.RecursivelyEnumerable.Examples.Halting`
(`haltingUnaryLanguage` is RE) and
`Langlib.Classes.RecursivelyEnumerable.Examples.NonHalting`
(its complement is not RE); this file only assembles them into the closure statements.
-/

/-- Recursively enumerable languages over the unary alphabet are not closed under complement. -/
public theorem RE_notClosedUnderComplement :
    ¬ ClosedUnderComplement (α := Unit) is_RE := by
  intro hclosed
  exact haltingUnary_complement_not_RE
    (hclosed haltingUnaryLanguage haltingUnaryLanguage_RE)

/-- RE languages over any nonempty finite alphabet are not closed under complement. -/
public theorem RE_notClosedUnderComplement_of_nonempty {T : Type} [Fintype T] [Nonempty T] :
    ¬ ClosedUnderComplement (α := T) is_RE := by
  intro hclosed
  let a : T := Classical.choice inferInstance
  let f : Unit → T := fun _ => a
  have hf : Function.Injective f := by
    intro x y _
    cases x
    cases y
    rfl
  have hmap : is_RE (Language.map f haltingUnaryLanguage) :=
    RE_of_map_injective_RE hf haltingUnaryLanguage haltingUnaryLanguage_RE
  have hcomp : is_RE (Language.map f haltingUnaryLanguage)ᶜ :=
    hclosed _ hmap
  let h : Unit → List T := fun _ => [a]
  have hpre : is_RE ({w : List Unit | w.flatMap h ∈ (Language.map f haltingUnaryLanguage)ᶜ}) :=
    RE_of_inverseHomomorphism_RE (Language.map f haltingUnaryLanguage)ᶜ h hcomp
  have heq :
      ({w : List Unit | w.flatMap h ∈ (Language.map f haltingUnaryLanguage)ᶜ} :
        Language Unit) = haltingUnaryLanguageᶜ := by
    ext w
    change (w.flatMap h ∈ (Language.map f haltingUnaryLanguage)ᶜ) ↔
      w ∈ haltingUnaryLanguageᶜ
    rw [Set.mem_compl_iff, Set.mem_compl_iff]
    have hflat : w.flatMap h = w.map f := by
      simpa [h, f, Function.comp_def] using (List.flatMap_pure_eq_map f w)
    rw [hflat]
    constructor
    · intro hnot hw
      exact hnot ⟨w, hw, rfl⟩
    · rintro hnot ⟨u, hu, humap⟩
      have huw : u = w := by
        apply List.map_injective_iff.mpr hf
        simpa using humap
      exact hnot (by simpa [huw] using hu)
  exact haltingUnary_complement_not_RE (by simpa [heq] using hpre)

end
