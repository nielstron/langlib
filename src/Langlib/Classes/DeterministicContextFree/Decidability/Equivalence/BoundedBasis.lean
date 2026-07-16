module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.GuardedContextOperational

@[expose]
public section

/-!
# Finite bounded bases for deterministic first-order grammars

The completeness argument for deterministic first-order grammars first obtains
a grammar-dependent bound on the finite graph presentations of the sound term
schemas that are needed.  This file turns such a semantic bound into an actual
finite `List BasisPair` suitable for the executable certificate checker.

Nothing semantic is hidden in the term enumeration: `regularTermsUpTo` is a
fully explicit enumeration of every well-formed pointed graph with at most the
given number of nodes.  The final selection of sound pairs is deliberately
noncomputable; the equivalence semidecider will enumerate arbitrary proposed
bases and verify their finite certificates, rather than evaluate that
selection.
-/

namespace DCFEquivalence

/-! ## Enumerating finite lists over a finite alphabet -/

/-- All lists of exactly `length` whose entries are drawn from `alphabet`.
Duplicates in `alphabet` are harmless. -/
@[expose] public def listsOfLength (alphabet : List α) : ℕ → List (List α)
  | 0 => [[]]
  | length + 1 =>
      alphabet.flatMap fun head =>
        (listsOfLength alphabet length).map (head :: ·)

public theorem mem_listsOfLength_iff {alphabet : List α}
    (length : ℕ) (values : List α) :
    values ∈ listsOfLength alphabet length ↔
      values.length = length ∧ ∀ value ∈ values, value ∈ alphabet := by
  induction length generalizing values with
  | zero =>
      constructor
      · intro h
        simp [listsOfLength] at h
        subst values
        simp
      · rintro ⟨hlength, _⟩
        have : values = [] := List.length_eq_zero_iff.mp hlength
        subst values
        simp [listsOfLength]
  | succ length ih =>
      constructor
      · intro h
        simp only [listsOfLength, List.mem_flatMap, List.mem_map] at h
        obtain ⟨head, hhead, tail, htail, rfl⟩ := h
        have htailSpec := (ih tail).mp htail
        refine ⟨by simp [htailSpec.1], ?_⟩
        intro value hvalue
        simp only [List.mem_cons] at hvalue
        rcases hvalue with rfl | hvalue
        · exact hhead
        · exact htailSpec.2 value hvalue
      · rintro ⟨hlength, hvalues⟩
        cases values with
        | nil => simp at hlength
        | cons head tail =>
            simp only [List.length_cons, Nat.succ.injEq] at hlength
            simp only [listsOfLength, List.mem_flatMap, List.mem_map]
            refine ⟨head, hvalues head (by simp), tail, ?_, rfl⟩
            apply (ih tail).mpr
            refine ⟨hlength, ?_⟩
            intro value hvalue
            exact hvalues value (by simp [hvalue])

/-! ## Enumerating bounded regular-term graphs -/

namespace RegularTerm

/-- Every raw node that can occur in a well-formed graph of `nodeCount`
nodes with the supplied rank table and variable bound. -/
@[expose] public def rawNodesFor (ranks : List ℕ)
    (variableBound nodeCount : ℕ) : List RawNode :=
  (List.range variableBound).map Sum.inl ++
    (List.range ranks.length).flatMap fun symbol =>
      match ranks[symbol]? with
      | none => []
      | some rank =>
          (listsOfLength (List.range nodeCount) rank).map fun children =>
            .inr (symbol, children)

public theorem mem_rawNodesFor_of_nodeWellFormedCode
    {ranks : List ℕ} {variableBound nodeCount : ℕ} {node : RawNode}
    (hnode : nodeWellFormedCode ranks variableBound nodeCount node = true) :
    node ∈ rawNodesFor ranks variableBound nodeCount := by
  cases node with
  | inl x =>
      apply List.mem_append_left
      apply List.mem_map.mpr
      refine ⟨x, List.mem_range.mpr ?_, rfl⟩
      simpa [nodeWellFormedCode] using of_decide_eq_true hnode
  | inr application =>
      rcases application with ⟨symbol, children⟩
      change (match ranks[symbol]? with
        | none => false
        | some rank =>
            decide (children.length = rank) &&
              children.all fun child => decide (child < nodeCount)) = true
        at hnode
      cases hrank : ranks[symbol]? with
      | none => simp [hrank] at hnode
      | some rank =>
          rw [hrank, Bool.and_eq_true] at hnode
          apply List.mem_append_right
          simp only [List.mem_flatMap]
          have hsymbol : symbol < ranks.length :=
            (List.getElem?_eq_some_iff.mp hrank).1
          refine ⟨symbol, List.mem_range.mpr hsymbol, ?_⟩
          simp only [hrank, List.mem_map]
          refine ⟨children, ?_, rfl⟩
          apply (mem_listsOfLength_iff rank children).mpr
          refine ⟨of_decide_eq_true hnode.1, ?_⟩
          intro child hchild
          exact List.mem_range.mpr
            (of_decide_eq_true ((List.all_eq_true.mp hnode.2) child hchild))

/-- All pointed raw graphs with exactly `nodeCount` nodes over the finite raw
node alphabet appropriate to that size. -/
@[expose] public def regularTermsOfSize (ranks : List ℕ)
    (variableBound nodeCount : ℕ) : List RegularTerm :=
  (listsOfLength (rawNodesFor ranks variableBound nodeCount) nodeCount).flatMap
    fun nodes => (List.range nodeCount).map fun root => (nodes, root)

/-- All well-formed pointed graphs with at most `nodeBound` nodes.  The raw
enumeration may contain malformed terms; the final Boolean filter makes the
public membership theorem exact. -/
@[expose] public def regularTermsUpTo (ranks : List ℕ)
    (variableBound nodeBound : ℕ) : List RegularTerm :=
  (List.range (nodeBound + 1)).flatMap fun nodeCount =>
    (regularTermsOfSize ranks variableBound nodeCount).filter fun term =>
      term.wellFormedCode ranks variableBound

public theorem mem_regularTermsOfSize_of_wellFormedCode
    {ranks : List ℕ} {variableBound : ℕ} {term : RegularTerm}
    (hterm : term.wellFormedCode ranks variableBound = true) :
    term ∈ regularTermsOfSize ranks variableBound term.nodes.length := by
  unfold wellFormedCode at hterm
  rw [Bool.and_eq_true] at hterm
  unfold regularTermsOfSize
  simp only [List.mem_flatMap, List.mem_map]
  refine ⟨term.nodes, ?_, term.root, ?_, ?_⟩
  · apply (mem_listsOfLength_iff term.nodes.length term.nodes).mpr
    refine ⟨rfl, ?_⟩
    intro node hnode
    exact mem_rawNodesFor_of_nodeWellFormedCode
      ((List.all_eq_true.mp hterm.2) node hnode)
  · exact List.mem_range.mpr (of_decide_eq_true hterm.1)
  · cases term
    rfl

public theorem mem_regularTermsUpTo_iff
    (ranks : List ℕ) (variableBound nodeBound : ℕ) (term : RegularTerm) :
    term ∈ regularTermsUpTo ranks variableBound nodeBound ↔
      term.nodes.length ≤ nodeBound ∧
        term.wellFormedCode ranks variableBound = true := by
  constructor
  · intro h
    unfold regularTermsUpTo at h
    simp only [List.mem_flatMap, List.mem_range, List.mem_filter] at h
    obtain ⟨nodeCount, hcount, hterm, hwellFormed⟩ := h
    unfold regularTermsOfSize at hterm
    simp only [List.mem_flatMap, List.mem_map] at hterm
    obtain ⟨nodes, hnodes, root, _hroot, hterm⟩ := hterm
    subst term
    have hlength := (mem_listsOfLength_iff nodeCount nodes).mp hnodes
    refine ⟨?_, hwellFormed⟩
    change nodes.length ≤ nodeBound
    rw [hlength.1]
    omega
  · rintro ⟨hbound, hwellFormed⟩
    unfold regularTermsUpTo
    simp only [List.mem_flatMap, List.mem_range, List.mem_filter]
    refine ⟨term.nodes.length, by omega, ?_, hwellFormed⟩
    exact mem_regularTermsOfSize_of_wellFormedCode hwellFormed

end RegularTerm

/-! ## The finite list of bounded sound schemas -/

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- A basis schema is semantically sound when all structurally valid ground
instances of its two sides have equal trace languages. -/
@[expose] public def SoundBasisPair
    (g : EncodedFirstOrderGrammar Action) (pair : BasisPair) : Prop :=
  g.basisPairWellFormedCode pair = true ∧
    ∀ arguments : List RegularTerm,
      arguments.length = pair.arity →
      g.groundArgumentsCode arguments = true →
      g.TraceEquivalent
        (pair.left.instantiate arguments)
        (pair.right.instantiate arguments)

/-- Enumerate every pair of schemas whose arity and two finite graph sizes are
bounded by `bound`. -/
@[expose] public def basisPairsUpTo
    (g : EncodedFirstOrderGrammar Action) (bound : ℕ) : List BasisPair :=
  (List.range (bound + 1)).flatMap fun arity =>
    (RegularTerm.regularTermsUpTo g.ranks arity bound).flatMap fun left =>
      (RegularTerm.regularTermsUpTo g.ranks arity bound).map fun right =>
        (arity, left, right)

omit [DecidableEq Action] in
public theorem mem_basisPairsUpTo_iff
    (g : EncodedFirstOrderGrammar Action) (bound : ℕ) (pair : BasisPair) :
    pair ∈ g.basisPairsUpTo bound ↔
      pair.arity ≤ bound ∧
      pair.left.nodes.length ≤ bound ∧
      pair.right.nodes.length ≤ bound ∧
      g.basisPairWellFormedCode pair = true := by
  rcases pair with ⟨arity, left, right⟩
  simp only [basisPairsUpTo, List.mem_flatMap, List.mem_range, List.mem_map]
  simp only [RegularTerm.mem_regularTermsUpTo_iff]
  unfold BasisPair.arity BasisPair.left BasisPair.right
  unfold basisPairWellFormedCode
  simp only [Bool.and_eq_true]
  constructor
  · rintro ⟨candidateArity, harity, candidateLeft, hleft,
        candidateRight, hright, hpair⟩
    cases hpair
    exact ⟨by omega, hleft.1, hright.1, hleft.2, hright.2⟩
  · rintro ⟨harity, hleftSize, hrightSize, hleftWellFormed,
        hrightWellFormed⟩
    refine ⟨arity, by omega, left, ⟨hleftSize, hleftWellFormed⟩,
      right, ⟨hrightSize, hrightWellFormed⟩, rfl⟩

/-- The mathematically selected finite basis of all sound schemas up to a
fixed presentation bound.  It is used only as an existence witness. -/
noncomputable def boundedSoundBasis
    (g : EncodedFirstOrderGrammar Action) (bound : ℕ) : List BasisPair := by
  classical
  exact (g.basisPairsUpTo bound).filter g.SoundBasisPair

public theorem mem_boundedSoundBasis_iff
    (g : EncodedFirstOrderGrammar Action) (bound : ℕ) (pair : BasisPair) :
    pair ∈ g.boundedSoundBasis bound ↔
      pair.arity ≤ bound ∧
      pair.left.nodes.length ≤ bound ∧
      pair.right.nodes.length ≤ bound ∧
      g.SoundBasisPair pair := by
  classical
  simp only [boundedSoundBasis, List.mem_filter, decide_eq_true_eq,
    mem_basisPairsUpTo_iff]
  unfold SoundBasisPair
  tauto

/-- Every row selected into the bounded basis is structurally valid and sound
for every ground substitution. -/
public theorem soundBasisPair_of_mem_boundedSoundBasis
    (g : EncodedFirstOrderGrammar Action) (bound : ℕ)
    {pair : BasisPair} (hpair : pair ∈ g.boundedSoundBasis bound) :
    g.SoundBasisPair pair :=
  (g.mem_boundedSoundBasis_iff bound pair).mp hpair |>.2.2.2

/-- A derived nonempty pair which is an instance of a bounded sound schema can
be discharged by one basis rule in the concrete finite basis. -/
public theorem CertificateDerivable.nop_of_boundedSoundInstance
    (g : EncodedFirstOrderGrammar Action) (bound : ℕ)
    {initialLeft initialRight left right : RegularTerm}
    {word : List (Label Action)} {schema : BasisPair}
    {arguments : List RegularTerm}
    (hpair : CertificateDerivable g initialLeft initialRight
      (g.boundedSoundBasis bound) (.pair word left right))
    (hnonempty : word ≠ [])
    (hsound : g.SoundBasisPair schema)
    (harityBound : schema.arity ≤ bound)
    (hleftBound : schema.left.nodes.length ≤ bound)
    (hrightBound : schema.right.nodes.length ≤ bound)
    (hargumentCount : arguments.length = schema.arity)
    (harguments : g.groundArgumentsCode arguments = true)
    (hleft : RegularTerm.unfoldingEquivalentCode left
      (schema.left.instantiate arguments) = true)
    (hright : RegularTerm.unfoldingEquivalentCode right
      (schema.right.instantiate arguments) = true) :
    CertificateDerivable g initialLeft initialRight
      (g.boundedSoundBasis bound) (.nop word) := by
  have hmem : schema ∈ g.boundedSoundBasis bound :=
    (g.mem_boundedSoundBasis_iff bound schema).mpr
      ⟨harityBound, hleftBound, hrightBound, hsound⟩
  obtain ⟨basisRef, hbasisRef, hschema⟩ := List.mem_iff_getElem.mp hmem
  apply CertificateDerivable.basis hpair
    (pairRef := basisRef) (schema := schema) (arguments := arguments)
  · exact List.getElem?_eq_some_iff.mpr ⟨hbasisRef, hschema⟩
  · exact hnonempty
  · exact hsound.1
  · exact hargumentCount
  · exact harguments
  · exact hleft
  · exact hright

end EncodedFirstOrderGrammar

end DCFEquivalence
