module

public import Langlib.Classes.ContextFree.Decidability.MalformedHistories.InitialErrorCompiler

@[expose]
public section

/-!
# Undecidability of context-free universality

The reduction compiles the complement of one accepting-history language.  Its
only source-dependent component is a finite-state check of the first row
against the marked unary encoding of the source program.  All other malformed
history components are fixed context-free grammar codes.
-/

open ContextFree.EncodedCFG
open ContextFree.MalformedHistories
open ContextFree.MalformedHistories.InitialErrorCompiler

namespace ContextFreeUniversality

variable {Γ Λ : Type} [DecidableEq Γ] [DecidableEq Λ]

/-- The five malformed-history components, kept epsilon-free.  The four fixed
codes denote syntax, final-row, and the two alternating step errors; the
initial component is compiled uniformly from `n`. -/
noncomputable def historyErrorCore [Fintype Γ] [Fintype Λ]
    (blocksCode malformedCode finalCode evenCode oddCode :
      EncodedCFG (HistoryAlphabet Γ Λ)) (n : Nat) :
    EncodedCFG (HistoryAlphabet Γ Λ) :=
  union malformedCode
    (union (initialErrorCFG blocksCode n)
      (union finalCode (union evenCode oddCode)))

theorem historyErrorCore_primrec [Fintype Γ] [Fintype Λ]
    [Primcodable (CellAlphabet Γ Λ)]
    [Primcodable (HistoryAlphabet Γ Λ)]
    (blocksCode malformedCode finalCode evenCode oddCode :
      EncodedCFG (HistoryAlphabet Γ Λ)) :
    Primrec (historyErrorCore blocksCode malformedCode finalCode
      evenCode oddCode) := by
  have hinitial := initialErrorCFG_primrec
    (Γ := Γ) (Λ := Λ) blocksCode
  have hodd : Primrec (fun _ : Nat => oddCode) := Primrec.const oddCode
  have hevenOdd : Primrec (fun _ : Nat => union evenCode oddCode) :=
    union_primrec.comp
      (Primrec.pair (Primrec.const evenCode) hodd)
  have hfinal : Primrec (fun _ : Nat =>
      union finalCode (union evenCode oddCode)) :=
    union_primrec.comp
      (Primrec.pair (Primrec.const finalCode) hevenOdd)
  have hrest : Primrec (fun n : Nat =>
      union (initialErrorCFG blocksCode n)
        (union finalCode (union evenCode oddCode))) :=
    union_primrec.comp (Primrec.pair hinitial hfinal)
  exact union_primrec.comp
    (Primrec.pair (Primrec.const malformedCode) hrest)

theorem historyErrorCore_noEmptyRHS [Fintype Γ] [Fintype Λ]
    {blocksCode malformedCode finalCode evenCode oddCode :
      EncodedCFG (HistoryAlphabet Γ Λ)}
    (hblocks : NoEmptyRHS blocksCode)
    (hmalformed : NoEmptyRHS malformedCode)
    (hfinal : NoEmptyRHS finalCode)
    (heven : NoEmptyRHS evenCode) (hodd : NoEmptyRHS oddCode)
    (n : Nat) :
    NoEmptyRHS (historyErrorCore blocksCode malformedCode finalCode
      evenCode oddCode n) := by
  exact noEmptyRHS_union hmalformed
    (noEmptyRHS_union (initialErrorCFG_noEmptyRHS hblocks n)
      (noEmptyRHS_union hfinal (noEmptyRHS_union heven hodd)))

/-- The native compiler core denotes exactly the complement of valid
histories with the empty word removed. -/
theorem contextFreeLanguageOf_historyErrorCore
    [Fintype Γ] [Fintype Λ] {Q F : Type}
    (S : CertifiedRowSystem (Option Bool) (RowAlphabet Γ Λ)
      LBA.RowCert Q F)
    (blocksCode malformedCode finalCode evenCode oddCode :
      EncodedCFG (HistoryAlphabet Γ Λ))
    (hblocks : contextFreeLanguageOf blocksCode =
      blocksLanguage \ ({[]} : Set (List (HistoryAlphabet Γ Λ))))
    (hmalformed : contextFreeLanguageOf malformedCode =
      malformedLanguage \ ({[]} : Set (List (HistoryAlphabet Γ Λ))))
    (hfinal : contextFreeLanguageOf finalCode =
      relaxedBadFinalLanguage (BundledFinal (systemFinalVerifier S)) \
        ({[]} : Set (List (HistoryAlphabet Γ Λ))))
    (heven : contextFreeLanguageOf evenCode =
      relaxedBadStepLanguage 0 (BundledStep S) \
        ({[]} : Set (List (HistoryAlphabet Γ Λ))))
    (hodd : contextFreeLanguageOf oddCode =
      relaxedBadStepLanguage 1 (BundledStep S) \
        ({[]} : Set (List (HistoryAlphabet Γ Λ))))
    (n : Nat) :
    contextFreeLanguageOf (historyErrorCore blocksCode malformedCode
        finalCode evenCode oddCode n) =
      (validLanguage (initialRowVerifier (Γ := Γ) (Λ := Λ) n).Accepts
        (BundledFinal (systemFinalVerifier S)) (BundledStep S))ᶜ \
          ({[]} : Set (List (HistoryAlphabet Γ Λ))) := by
  letI : DecidableEq (CellAlphabet Γ Λ) := inferInstance
  rw [historyErrorCore, contextFreeLanguageOf_union,
    contextFreeLanguageOf_union, contextFreeLanguageOf_union,
    contextFreeLanguageOf_union,
    contextFreeLanguageOf_initialErrorCFG blocksCode hblocks,
    hmalformed, hfinal, heven, hodd,
    compl_validLanguage_relaxed]
  ext w
  simp only [Language.mem_add]
  have hinitialNe :
      w ∈ relaxedBadInitialLanguage
          (initialRowVerifier (Γ := Γ) (Λ := Λ) n).Accepts →
        w ≠ [] := by
    rintro ⟨h, hraw, -⟩ rfl
    simp [RawRepresents, encode] at hraw
  constructor
  · rintro (⟨hm, hne⟩ | hi | ⟨hf, hne⟩ |
      ⟨he, hne⟩ | ⟨ho, hne⟩)
    · exact ⟨Or.inl hm, hne⟩
    · exact ⟨Or.inr (Or.inl hi), hinitialNe hi⟩
    · exact ⟨Or.inr (Or.inr (Or.inl hf)), hne⟩
    · exact ⟨Or.inr (Or.inr (Or.inr (Or.inl he))), hne⟩
    · exact ⟨Or.inr (Or.inr (Or.inr (Or.inr ho))), hne⟩
  · rintro ⟨hm | hi | hf | he | ho, hne⟩
    · exact Or.inl ⟨hm, hne⟩
    · exact Or.inr (Or.inl hi)
    · exact Or.inr (Or.inr (Or.inl ⟨hf, hne⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨he, hne⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨ho, hne⟩)))

/-- Add the unique epsilon start production to the positive malformed-history
core. -/
noncomputable def historyComplementCompiler [Fintype Γ] [Fintype Λ]
    (blocksCode malformedCode finalCode evenCode oddCode :
      EncodedCFG (HistoryAlphabet Γ Λ)) (n : Nat) :
    EncodedCFG (HistoryAlphabet Γ Λ) :=
  addEpsilonStart (historyErrorCore blocksCode malformedCode finalCode
    evenCode oddCode n)

theorem historyComplementCompiler_primrec [Fintype Γ] [Fintype Λ]
    [Primcodable (CellAlphabet Γ Λ)]
    [Primcodable (HistoryAlphabet Γ Λ)]
    (blocksCode malformedCode finalCode evenCode oddCode :
      EncodedCFG (HistoryAlphabet Γ Λ)) :
    Primrec (historyComplementCompiler blocksCode malformedCode finalCode
      evenCode oddCode) :=
  addEpsilonStart_primrec.comp
    (historyErrorCore_primrec blocksCode malformedCode finalCode
      evenCode oddCode)

private theorem nil_not_mem_validLanguage
    {A : Type} (Initial Final : List A → Prop)
    (Step : List A → List A → Prop) :
    [] ∉ validLanguage Initial Final Step := by
  rintro ⟨h, hrep, -⟩
  simp [Represents, encode] at hrep

/-- Adding the isolated epsilon production turns the core into the exact
complement of the valid-history language. -/
theorem contextFreeLanguageOf_historyComplementCompiler
    [Fintype Γ] [Fintype Λ] {Q F : Type}
    (S : CertifiedRowSystem (Option Bool) (RowAlphabet Γ Λ)
      LBA.RowCert Q F)
    (blocksCode malformedCode finalCode evenCode oddCode :
      EncodedCFG (HistoryAlphabet Γ Λ))
    (hblocks : contextFreeLanguageOf blocksCode =
      blocksLanguage \ ({[]} : Set (List (HistoryAlphabet Γ Λ))))
    (hmalformed : contextFreeLanguageOf malformedCode =
      malformedLanguage \ ({[]} : Set (List (HistoryAlphabet Γ Λ))))
    (hfinal : contextFreeLanguageOf finalCode =
      relaxedBadFinalLanguage (BundledFinal (systemFinalVerifier S)) \
        ({[]} : Set (List (HistoryAlphabet Γ Λ))))
    (heven : contextFreeLanguageOf evenCode =
      relaxedBadStepLanguage 0 (BundledStep S) \
        ({[]} : Set (List (HistoryAlphabet Γ Λ))))
    (hodd : contextFreeLanguageOf oddCode =
      relaxedBadStepLanguage 1 (BundledStep S) \
        ({[]} : Set (List (HistoryAlphabet Γ Λ))))
    (n : Nat) :
    contextFreeLanguageOf (historyComplementCompiler blocksCode malformedCode
        finalCode evenCode oddCode n) =
      (validLanguage (initialRowVerifier (Γ := Γ) (Λ := Λ) n).Accepts
        (BundledFinal (systemFinalVerifier S)) (BundledStep S))ᶜ := by
  rw [historyComplementCompiler, contextFreeLanguageOf_addEpsilonStart,
    contextFreeLanguageOf_historyErrorCore S blocksCode malformedCode
      finalCode evenCode oddCode hblocks hmalformed hfinal heven hodd n]
  ext w
  simp only [Language.mem_add]
  constructor
  · rintro (rfl | ⟨hw, -⟩)
    · exact nil_not_mem_validLanguage _ _ _
    · exact hw
  · intro hw
    by_cases hnil : w = []
    · exact Or.inl hnil
    · exact Or.inr ⟨hw, hnil⟩

/-- There is one fixed finite native history alphabet and one primitive
recursive epsilon-free compiler whose epsilon-completion is universal exactly
for nonhalting source programs.  This package is also reusable by reductions
to other grammar formalisms before any ambient-alphabet completion. -/
theorem exists_nativeHistoryCompiler :
    ∃ (A : Type) (_ : Fintype A) (_ : Nonempty A) (_ : DecidableEq A)
      (_ : Primcodable A) (core : PartrecCode → EncodedCFG A),
      Primrec core ∧ (∀ c, NoEmptyRHS (core c)) ∧
        ∀ c, contextFreeLanguageOf (addEpsilonStart (core c)) = Set.univ ↔
          ¬ (c.eval 0).Dom := by
  obtain ⟨Γ, Λ, hΓ, hΛ, hdΓ, hdΛ, M, hM⟩ :=
    FixedSystem.exists_fixedSystem
  letI : Fintype Γ := hΓ
  letI : Fintype Λ := hΛ
  letI : DecidableEq Γ := hdΓ
  letI : DecidableEq Λ := hdΛ
  letI : Fintype (CellAlphabet Γ Λ) := inferInstance
  letI : DecidableEq (CellAlphabet Γ Λ) := inferInstance
  letI : Fintype (HistoryAlphabet Γ Λ) := inferInstance
  letI : DecidableEq (HistoryAlphabet Γ Λ) := inferInstance
  letI : Nonempty (HistoryAlphabet Γ Λ) := ⟨Symbol.separator⟩
  letI : Primcodable (CellAlphabet Γ Λ) :=
    Primcodable.ofEquiv (Fin (Fintype.card (CellAlphabet Γ Λ)))
      (Fintype.truncEquivFin (CellAlphabet Γ Λ)).out
  letI : Primcodable (HistoryAlphabet Γ Λ) :=
    Primcodable.ofEquiv (Fin (Fintype.card (HistoryAlphabet Γ Λ)))
      (Fintype.truncEquivFin (HistoryAlphabet Γ Λ)).out
  let S := FixedSystem.coverSystem M
  have hblocksCF : is_CF
      (blocksLanguage : Language (HistoryAlphabet Γ Λ)) :=
    is_CF_of_is_RG (is_RG_of_isRegular blocksLanguage_isRegular)
  have hmalformedCF : is_CF
      (malformedLanguage : Language (HistoryAlphabet Γ Λ)) :=
    malformedLanguage_is_CF
  have hfinalCF : is_CF
      (relaxedBadFinalLanguage
        (BundledFinal (systemFinalVerifier S)) :
          Language (HistoryAlphabet Γ Λ)) :=
    (systemFinalVerifier S).relaxedBundledBadFinalLanguage_is_CF
  have hevenCF : is_CF
      (relaxedBadStepLanguage 0 (BundledStep S) :
        Language (HistoryAlphabet Γ Λ)) :=
    relaxedBadStepLanguage_zero_is_CF S
  have hoddCF : is_CF
      (relaxedBadStepLanguage 1 (BundledStep S) :
        Language (HistoryAlphabet Γ Λ)) :=
    relaxedBadStepLanguage_one_is_CF S
  obtain ⟨blocksCode, hblocksFree, hblocksLang⟩ :=
    exists_noEmptyRHS_code hblocksCF
  obtain ⟨malformedCode, hmalformedFree, hmalformedLang⟩ :=
    exists_noEmptyRHS_code hmalformedCF
  obtain ⟨finalCode, hfinalFree, hfinalLang⟩ :=
    exists_noEmptyRHS_code hfinalCF
  obtain ⟨evenCode, hevenFree, hevenLang⟩ :=
    exists_noEmptyRHS_code hevenCF
  obtain ⟨oddCode, hoddFree, hoddLang⟩ :=
    exists_noEmptyRHS_code hoddCF
  let core : PartrecCode → EncodedCFG (HistoryAlphabet Γ Λ) := fun c =>
    historyErrorCore blocksCode malformedCode finalCode evenCode oddCode
      (Encodable.encode c)
  have hcorePrim : Primrec core :=
    (historyErrorCore_primrec blocksCode malformedCode finalCode
      evenCode oddCode).comp Primrec.encode
  have hcoreFree : ∀ c, NoEmptyRHS (core c) := by
    intro c
    exact historyErrorCore_noEmptyRHS hblocksFree hmalformedFree
      hfinalFree hevenFree hoddFree (Encodable.encode c)
  have hmarked (c : PartrecCode) :
      FixedSystem.markedCodeWord c =
        true :: List.replicate (Encodable.encode c) false := by
    simp [FixedSystem.markedCodeWord, codeUnaryWord]
  have hvalid (c : PartrecCode) :
      validLanguage
          (initialRowVerifier (Γ := Γ) (Λ := Λ)
            (Encodable.encode c)).Accepts
          (BundledFinal (systemFinalVerifier S)) (BundledStep S) =
        bundledValidLanguageWith S
          (FixedSystem.InitialRow (Γ := Γ) (Λ := Λ)
            (FixedSystem.markedCodeWord c)) := by
    have hinitial (row : List (CellAlphabet Γ Λ)) :
        (initialRowVerifier (Γ := Γ) (Λ := Λ)
            (Encodable.encode c)).Accepts row ↔
          IsFirstBundledRow row ∧
            FixedSystem.InitialRow (Γ := Γ) (Λ := Λ)
              (FixedSystem.markedCodeWord c) (underlyingRow row) := by
      rw [initialRowVerifier_accepts_iff,
        foldl_rowProgress_zero_iff_initialRow, hmarked]
    ext w
    simp only [validLanguage, bundledValidLanguageWith]
    constructor
    · rintro ⟨h, hrep, hinit, hfinal, hstep⟩
      exact ⟨h, hrep, (hinitial h.first).mp hinit, hfinal, hstep⟩
    · rintro ⟨h, hrep, hinit, hfinal, hstep⟩
      exact ⟨h, hrep, (hinitial h.first).mpr hinit, hfinal, hstep⟩
  have hcompiler (c : PartrecCode) :
      contextFreeLanguageOf (addEpsilonStart (core c)) =
        (bundledValidLanguageWith S
          (FixedSystem.InitialRow (Γ := Γ) (Λ := Λ)
            (FixedSystem.markedCodeWord c)))ᶜ := by
    rw [show addEpsilonStart (core c) =
        historyComplementCompiler blocksCode malformedCode finalCode
          evenCode oddCode (Encodable.encode c) by rfl,
      contextFreeLanguageOf_historyComplementCompiler S blocksCode
        malformedCode finalCode evenCode oddCode hblocksLang
        hmalformedLang hfinalLang hevenLang hoddLang,
      hvalid]
  refine ⟨HistoryAlphabet Γ Λ, inferInstance, inferInstance, inferInstance,
    inferInstance, core, hcorePrim, hcoreFree, ?_⟩
  intro c
  rw [hcompiler]
  constructor
  · intro huniv hdom
    obtain ⟨w, hw⟩ := (hM c).mpr hdom
    have hwc : w ∈
        (bundledValidLanguageWith S
          (FixedSystem.InitialRow (Γ := Γ) (Λ := Λ)
            (FixedSystem.markedCodeWord c)))ᶜ := by
      rw [huniv]
      exact Set.mem_univ w
    exact hwc hw
  · intro hnonhalting
    apply Set.eq_univ_of_forall
    intro w
    change w ∉ bundledValidLanguageWith S
      (FixedSystem.InitialRow (Γ := Γ) (Λ := Λ)
        (FixedSystem.markedCodeWord c))
    intro hw
    exact hnonhalting ((hM c).mp ⟨w, hw⟩)

/-- **Universality of encoded context-free grammars is not computable over
any sufficiently large finite terminal alphabet.**  The bound is the size of
the one fixed native history alphabet; larger alphabets are handled by an
injective relabelling together with a fixed grammar accepting every word that
leaves the embedded alphabet. -/
theorem contextFree_computableUniversality_undecidable :
    ∃ n : Nat, ∀ (T : Type) (_ : Fintype T),
      n ≤ Fintype.card T →
      letI : DecidableEq T := Classical.decEq T
      letI : Primcodable T :=
        Primcodable.ofEquiv (Fin (Fintype.card T))
          (Fintype.truncEquivFin T).out
      ¬ ComputableUniversality (CF : Set (Language T))
        (contextFreeLanguageOf : EncodedCFG T → Language T) := by
  obtain ⟨A, hA, hnA, hdA, hpA, core, hcorePrim, -, hcoreSpec⟩ :=
    exists_nativeHistoryCompiler
  letI : Fintype A := hA
  letI : Nonempty A := hnA
  letI : DecidableEq A := hdA
  letI : Primcodable A := hpA
  refine ⟨Fintype.card A, ?_⟩
  intro T hT hcard
  letI : Fintype T := hT
  letI : DecidableEq T := Classical.decEq T
  letI : Primcodable T :=
    Primcodable.ofEquiv (Fin (Fintype.card T))
      (Fintype.truncEquivFin T).out
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  let compile : PartrecCode → EncodedCFG T := fun c =>
    completeAlphabet e (addEpsilonStart (core c))
  have hePrim : Primrec (e : A → T) := Primrec.dom_finite e
  have hcompilePrim : Primrec compile :=
    (completeAlphabet_primrec hePrim).comp
      (addEpsilonStart_primrec.comp hcorePrim)
  have hcompile : Computable compile := hcompilePrim.to_comp
  have hcompileSpec (c : PartrecCode) :
      contextFreeLanguageOf (compile c) = Set.univ ↔
        ¬ (c.eval 0).Dom := by
    change contextFreeLanguageOf
        (completeAlphabet e (addEpsilonStart (core c))) = Set.univ ↔ _
    rw [contextFreeLanguageOf_completeAlphabet_eq_univ_iff
        (addEpsilonStart (core c))
        (Function.leftInverse_invFun e.injective),
      hcoreSpec]
  intro huniversality
  exact (ComputablePredOnPromise.not_of_computable_nonhalting_reduction
    compile hcompile (fun _ => trivial) 0 hcompileSpec)
      huniversality.2.2

end ContextFreeUniversality
