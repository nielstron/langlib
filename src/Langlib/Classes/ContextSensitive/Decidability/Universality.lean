module

public import Langlib.Classes.ContextFree.Decidability.Universality
public import Langlib.Classes.ContextSensitive.Decidability.Characterization

@[expose]
public section

/-!
# Undecidability of universality for encoded context-sensitive grammars

An epsilon-free encoded CFG can be read literally as a noncontracting grammar.
After adjoining one isolated fresh-start epsilon rule, it is therefore a valid
context-sensitive code with exactly the same language.  The generic reduction
lemma below packages this last step: any primitive-recursive family of
epsilon-free CFG cores whose fresh-start languages characterize nonhalting
rules out a universality procedure for the repository's concrete `CSCode`
presentation.
-/

open ContextFree.EncodedCFG

namespace ContextSensitiveUniversality

variable {T : Type} [DecidableEq T] [Primcodable T]

private theorem addEpsilonStart_completeAlphabet_eq_univ_iff
    {A B : Type} [Fintype A] [Fintype B] [DecidableEq A]
    [DecidableEq B] (G : EncodedCFG A) {f : A → B} {g : B → A}
    (hgf : Function.LeftInverse g f) :
    contextFreeLanguageOf (addEpsilonStart (completeAlphabet f G)) =
        Set.univ ↔
      contextFreeLanguageOf (addEpsilonStart G) = Set.univ := by
  have hlanguages :
      contextFreeLanguageOf (addEpsilonStart (completeAlphabet f G)) =
        contextFreeLanguageOf (completeAlphabet f (addEpsilonStart G)) := by
    rw [contextFreeLanguageOf_addEpsilonStart,
      contextFreeLanguageOf_completeAlphabet_of_leftInverse G hgf,
      contextFreeLanguageOf_completeAlphabet_of_leftInverse
        (addEpsilonStart G) hgf,
      contextFreeLanguageOf_addEpsilonStart]
    ext w
    simp only [Language.mem_add]
    constructor
    · rintro (rfl | hmap | hout)
      · exact Or.inl ⟨[], Or.inl (Set.mem_singleton []), rfl⟩
      · exact Or.inl (by
          change w ∈ Set.image (List.map f)
            (({[]} : Language A) + contextFreeLanguageOf G)
          obtain ⟨u, hu, rfl⟩ := hmap
          exact ⟨u, Or.inr hu, rfl⟩)
      · exact Or.inr hout
    · rintro (hmap | hout)
      · change w ∈ Set.image (List.map f)
          (({[]} : Language A) + contextFreeLanguageOf G) at hmap
        obtain ⟨u, hu, rfl⟩ := hmap
        rcases hu with rfl | hu
        · exact Or.inl rfl
        · exact Or.inr (Or.inl ⟨u, hu, rfl⟩)
      · exact Or.inr (Or.inr hout)
  rw [hlanguages,
    contextFreeLanguageOf_completeAlphabet_eq_univ_iff
      (addEpsilonStart G) hgf]

/-- A primitive-recursive epsilon-free CFG reduction to nonhalting also gives
a reduction to universality of concrete context-sensitive grammar codes. -/
theorem not_computableUniversality_of_cfg_reduction
    (core : Nat.Partrec.Code → EncodedCFG T)
    (hcore : Primrec core)
    (hfree : ∀ c, NoEmptyRHS (core c))
    (hspec : ∀ c,
      contextFreeLanguageOf (addEpsilonStart (core c)) = Set.univ ↔
        ¬ (c.eval 0).Dom) :
    ¬ ComputableUniversality (CS : Set (Language T))
      (ContextSensitive.contextSensitiveLanguageOf' :
        ContextSensitive.CSCode T → Language T) := by
  intro hUniversal
  let compile : Nat.Partrec.Code → ContextSensitive.CSCode T :=
    fun c ↦ addEpsilonStartCSCode (core c) (hfree c)
  have hcompilePrimrec : Primrec compile := by
    exact addEpsilonStartCSCode_primrec core hcore hfree
  apply hUniversal.2.2.not_of_computable_nonhalting_reduction
    compile hcompilePrimrec.to_comp (fun _ ↦ trivial) 0
  intro c
  rw [show ContextSensitive.contextSensitiveLanguageOf' (compile c) =
      contextFreeLanguageOf (addEpsilonStart (core c)) by
    exact contextSensitiveLanguageOf_addEpsilonStartCSCode
      (core c) (hfree c)]
  exact hspec c

/-- Context-sensitive universality is undecidable over every effectively
encoded finite alphabet large enough to contain the one fixed history
alphabet.  The bound is independent of the target alphabet. -/
theorem contextSensitive_computableUniversality_undecidable_of_encoding :
    ∃ n : Nat, ∀ (T : Type) [Fintype T] [DecidableEq T]
      [Primcodable T], n ≤ Fintype.card T →
        ¬ ComputableUniversality (CS : Set (Language T))
          (ContextSensitive.contextSensitiveLanguageOf' :
            ContextSensitive.CSCode T → Language T) := by
  obtain ⟨A, hA, hneA, hdA, hpA, core, hcore, hfree, hspec⟩ :=
    ContextFreeUniversality.exists_nativeHistoryCompiler
  refine ⟨Fintype.card A, ?_⟩
  intro B hB hdB hpB hcard
  letI : Fintype A := hA
  letI : Nonempty A := hneA
  letI : DecidableEq A := hdA
  letI : Primcodable A := hpA
  let e : A ↪ B := Classical.choice
    (Function.Embedding.nonempty_of_card_le hcard)
  let f : A → B := e
  let g : B → A := Function.invFun f
  have hgf : Function.LeftInverse g f :=
    Function.leftInverse_invFun e.injective
  let liftedCore : PartrecCode → EncodedCFG B :=
    fun c ↦ completeAlphabet f (core c)
  apply not_computableUniversality_of_cfg_reduction liftedCore
  · exact (completeAlphabet_primrec
      (Primrec.dom_finite f)).comp hcore
  · intro c
    exact completeAlphabet_noEmptyRHS (hfree c)
  · intro c
    rw [addEpsilonStart_completeAlphabet_eq_univ_iff
      (core c) hgf]
    exact hspec c

/-- **Universality of encoded context-sensitive grammars is not computable
over any sufficiently large finite terminal alphabet.**  Every finite target
type receives its canonical finite code, so no additional alphabet encoding
assumption appears in the headline statement. -/
theorem contextSensitive_computableUniversality_undecidable :
    ∃ n : Nat, ∀ (T : Type) (_ : Fintype T),
      n ≤ Fintype.card T →
      letI : DecidableEq T := Classical.decEq T
      letI : Primcodable T :=
        Primcodable.ofEquiv (Fin (Fintype.card T))
          (Fintype.truncEquivFin T).out
      ¬ ComputableUniversality (CS : Set (Language T))
        (ContextSensitive.contextSensitiveLanguageOf' :
          ContextSensitive.CSCode T → Language T) := by
  obtain ⟨n, hundecidable⟩ :=
    contextSensitive_computableUniversality_undecidable_of_encoding
  refine ⟨n, ?_⟩
  intro T hT hcard
  letI : Fintype T := hT
  letI : DecidableEq T := Classical.decEq T
  letI : Primcodable T :=
    Primcodable.ofEquiv (Fin (Fintype.card T))
      (Fintype.truncEquivFin T).out
  exact hundecidable T hcard

end ContextSensitiveUniversality
