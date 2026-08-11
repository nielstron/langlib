module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.FiniteHeadPrefixes
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.CriticalWorstInstance

@[expose]
public section

/-!
# Open-sound finite bases

Ground-instance soundness in the original grammar is not stable under adding
fresh critical markers.  The sufficient-basis construction therefore selects
the stronger rows whose two open schemas already have equal trace languages
with the private variable labels.  Critical worst-instance semantics then
makes every such row sound for arbitrary ground substitutions in every large
enough marker extension.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- Structural validity together with trace equivalence of the open schemas
themselves. -/
@[expose] public def OpenSoundBasisPair
    (g : EncodedFirstOrderGrammar Action) (pair : BasisPair) : Prop :=
  g.basisPairWellFormedCode pair = true ∧
    g.TraceEquivalent pair.left pair.right

/-- All open-sound schemas under one arity/presentation bound. -/
noncomputable def boundedOpenSoundBasis
    (g : EncodedFirstOrderGrammar Action) (bound : ℕ) : List BasisPair := by
  classical
  exact (g.basisPairsUpTo bound).filter g.OpenSoundBasisPair

public theorem mem_boundedOpenSoundBasis_iff
    (g : EncodedFirstOrderGrammar Action) (bound : ℕ)
    (pair : BasisPair) :
    pair ∈ g.boundedOpenSoundBasis bound ↔
      pair.arity ≤ bound ∧
      pair.left.nodes.length ≤ bound ∧
      pair.right.nodes.length ≤ bound ∧
      g.OpenSoundBasisPair pair := by
  classical
  simp only [boundedOpenSoundBasis, List.mem_filter, decide_eq_true_eq,
    mem_basisPairsUpTo_iff]
  unfold OpenSoundBasisPair
  tauto

omit [DecidableEq Action] in
private theorem groundArguments_of_code
    {g : EncodedFirstOrderGrammar Action}
    {arguments : List RegularTerm}
    (harguments : g.groundArgumentsCode arguments = true) :
    ∀ argument ∈ arguments, argument.Ground g.ranks := by
  unfold groundArgumentsCode at harguments
  have hall := List.all_eq_true.mp harguments
  intro argument hargument
  exact (RegularTerm.groundCode_eq_true_iff g.ranks argument).mp
    (hall argument hargument)

/-- An original open-sound row is an ordinary sound basis row in every marker
extension containing at least its arity-many critical symbols. -/
public theorem OpenSoundBasisPair.sound_in_criticalExtension
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {pair : BasisPair} (hopen : g.OpenSoundBasisPair pair)
    {count : ℕ} (hcount : pair.arity ≤ count) :
    (g.withCriticalMarkers count).SoundBasisPair pair := by
  unfold OpenSoundBasisPair at hopen
  have hpairWellFormed := hopen.1
  unfold basisPairWellFormedCode at hpairWellFormed
  rw [Bool.and_eq_true] at hpairWellFormed
  let family := criticalInstanceFamily_of_originalBasis g hg [pair] count
    (by
      intro schema hschema
      have hschemaEq : schema = pair := by simpa using hschema
      subst schema
      exact hpairWellFormed)
    (by
      intro schema hschema
      have hschemaEq : schema = pair := by simpa using hschema
      subst schema
      exact hcount)
  constructor
  · exact family.schema_wellformed pair (by simp)
  · intro arguments hlength hargumentsCode
    apply openTraceEquivalent_instantiation_in_criticalExtension
      hg hcount hpairWellFormed.1 hpairWellFormed.2 hopen.2 hlength
    exact groundArguments_of_code hargumentsCode

end EncodedFirstOrderGrammar

end DCFEquivalence
