module

public import Langlib.Automata.LinearBounded.CertifiedRowSystem.Complement.Definition
public import Langlib.Automata.LinearBounded.CertifiedRowSystem.Complement.Construction
public import Langlib.Automata.LinearBounded.CertifiedRowSystem.Complement.Correctness
public import Langlib.Automata.LinearBounded.CertifiedRowSystem.Complement.EndToEnd

@[expose]
public section

/-!
# Complementing certified row systems

The protocol representation and semantic finite graph are defined in
`Complement/Definition.lean`; its synchronous certified-row construction is in
`Complement/Construction.lean`, and its correctness development is in
`Complement/Correctness.lean`.
-/

namespace CertifiedRowSystem

/-- The nonempty complement of the row language of any finite certified row system
is recognized by an input-sized nondeterministic LBA. -/
public theorem is_LBA_pos_complement_rowReachLanguage
    {I A C Q F : Type}
    [Fintype I] [DecidableEq I]
    [Fintype A] [Nonempty A]
    [Fintype C] [Fintype Q] [Fintype F]
    (S : CertifiedRowSystem I A C Q F) :
    is_LBA_pos (S.rowReachLanguageᶜ \ ({[]} : Set (List I))) := by
  classical
  rw [← rowReachLanguage_complementSystem S]
  exact is_LBA_pos_rowReachLanguage (Complement.complementSystem S)

end CertifiedRowSystem
