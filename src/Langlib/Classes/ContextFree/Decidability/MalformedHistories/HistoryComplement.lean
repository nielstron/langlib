module

public import Langlib.Classes.ContextFree.Decidability.MalformedHistories.FinalPredicates
public import Langlib.Classes.ContextFree.Decidability.MalformedHistories.SyntaxErrors

@[expose]
public section

/-!
# Context-free complements of finite certified history languages

This file packages the five exact error components: malformed syntax, rejected
initial row, rejected final row, and failed adjacent steps of either parity.
-/

namespace ContextFree.MalformedHistories

variable {I A C Q F IState FinalState : Type}

/-- The row verifier already carried by a certified row system. -/
def systemFinalVerifier (S : CertifiedRowSystem I A C Q F) :
    RowVerifier A F where
  start := S.finalStart
  step := S.finalCell
  done := S.finalDone

theorem systemFinalVerifier_accepts_iff
    (S : CertifiedRowSystem I A C Q F) (row : List A) :
    (systemFinalVerifier S).Accepts row ↔ S.Final row := by
  rfl

/-- Valid alternating histories for bundled rows. -/
def bundledValidLanguage
    (S : CertifiedRowSystem I A C Q F)
    (InitialVerifier : RowVerifier A IState)
    (FinalVerifier : RowVerifier A FinalState) :
    Language (Symbol (BundledCell A C)) :=
  validLanguage (BundledInitial InitialVerifier)
    (BundledFinal FinalVerifier) (BundledStep S)

section Finite

variable [Fintype A] [DecidableEq A] [Fintype C] [DecidableEq C]
  [Fintype Q] [DecidableEq Q] [Fintype IState] [Fintype FinalState]

/-- The complement of every finite certified bundled-history language is
context-free.  The statement is uniform over the finite row verifiers; an
effective undecidability reduction additionally needs explicit encoded grammar
compilers for these components. -/
theorem compl_bundledValidLanguage_is_CF
    (S : CertifiedRowSystem I A C Q F)
    (InitialVerifier : RowVerifier A IState)
    (FinalVerifier : RowVerifier A FinalState) :
    is_CF ((bundledValidLanguage S InitialVerifier FinalVerifier)ᶜ) := by
  rw [bundledValidLanguage, compl_validLanguage_relaxed]
  apply CF_of_CF_u_CF
  refine ⟨malformedLanguage_is_CF, ?_⟩
  apply CF_of_CF_u_CF
  refine ⟨InitialVerifier.relaxedBundledBadInitialLanguage_is_CF, ?_⟩
  apply CF_of_CF_u_CF
  refine ⟨FinalVerifier.relaxedBundledBadFinalLanguage_is_CF, ?_⟩
  apply CF_of_CF_u_CF
  exact ⟨relaxedBadStepLanguage_zero_is_CF S,
    relaxedBadStepLanguage_one_is_CF S⟩

end Finite

section SystemFinal

variable [Fintype A] [DecidableEq A] [Fintype C] [DecidableEq C]
  [Fintype Q] [DecidableEq Q] [Fintype F] [Fintype IState]

theorem compl_bundledValidLanguage_systemFinal_is_CF
    (S : CertifiedRowSystem I A C Q F)
    (InitialVerifier : RowVerifier A IState) :
    is_CF ((bundledValidLanguage S InitialVerifier
      (systemFinalVerifier S))ᶜ) :=
  compl_bundledValidLanguage_is_CF S InitialVerifier
    (systemFinalVerifier S)

end SystemFinal

end ContextFree.MalformedHistories
