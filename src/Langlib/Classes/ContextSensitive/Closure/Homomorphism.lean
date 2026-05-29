module

public import Langlib.Utilities.ClosurePredicates
public import Langlib.Classes.ContextSensitive.Closure.Quotient

/-!
# Context-Sensitive Non-Closure Under String Homomorphism

The current non-contracting context-sensitive class does not contain any language with the empty
word.  An erasing homomorphism maps the one-letter singleton language to `{[]}`, so this class is
not closed under arbitrary string homomorphisms.
-/

private theorem homomorphicImage_singleton_erasing :
    Language.homomorphicImage ({[()]} : Language Unit) (fun _ : Unit => ([] : List Unit)) =
      ({[]} : Language Unit) := by
  ext w
  constructor
  · rintro ⟨v, hv, hw⟩
    rw [Set.mem_singleton_iff] at hv
    subst v
    change w ∈ ([({[]} : Language Unit)] : List (Language Unit)).prod at hw
    simpa using hw
  · intro hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    refine ⟨[()], Set.mem_singleton [()], ?_⟩
    simp [List.prod_cons, List.prod_nil]
    exact Set.mem_singleton []

/-- Context-sensitive languages are not closed under arbitrary string homomorphisms. -/
public theorem CS_notClosedUnderHomomorphism :
    ¬ ClosedUnderHomomorphism is_CS := by
  intro hclosed
  have himage := hclosed ({[()]} : Language Unit) (fun _ : Unit => ([] : List Unit))
    (CS_singleton_letter ())
  rw [homomorphicImage_singleton_erasing] at himage
  exact not_CS_epsilon himage
