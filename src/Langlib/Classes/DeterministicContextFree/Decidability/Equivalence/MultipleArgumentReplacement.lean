module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.ArgumentReplacementCertificate

@[expose]
public section

/-!
# Replacing a prefix of schema arguments

A balancing result replaces every immediate active successor by the pivot
residual reached by its fixed exposing word.  The one-slot certificate rule is
iterated here in argument order.  After `k` steps, the first `k` arguments are
the selected replacements and the untouched suffix is inherited from the
original tuple.
-/

namespace DCFEquivalence

namespace RegularTerm

/-- Replace the initial segment of `arguments` by `replacements`, retaining
the untouched suffix of `arguments`. -/
@[expose] public def replaceArgumentPrefix
    (arguments replacements : List RegularTerm) : List RegularTerm :=
  replacements ++ arguments.drop replacements.length

@[simp] public theorem replaceArgumentPrefix_nil
    (arguments : List RegularTerm) :
    replaceArgumentPrefix arguments [] = arguments := by
  simp [replaceArgumentPrefix]

public theorem replaceArgumentPrefix_length
    {arguments replacements : List RegularTerm}
    (hlength : replacements.length ≤ arguments.length) :
    (replaceArgumentPrefix arguments replacements).length =
      arguments.length := by
  simp [replaceArgumentPrefix, List.length_drop]
  omega

/-- Before appending the next replacement, the boundary slot is still the
corresponding original argument. -/
public theorem replaceArgumentPrefix_getElem?_boundary
    {arguments replacements : List RegularTerm}
    (hlength : replacements.length < arguments.length) :
    (replaceArgumentPrefix arguments replacements)[replacements.length]? =
      arguments[replacements.length]? := by
  rw [replaceArgumentPrefix,
    List.getElem?_append_right (Nat.le_refl replacements.length)]
  simp [List.getElem?_drop, hlength]

/-- Appending one replacement to the replacement prefix is the same operation
as replacing the current boundary slot. -/
public theorem replaceArgumentPrefix_append
    {arguments replacements : List RegularTerm}
    (replacement : RegularTerm)
    (hlength : replacements.length < arguments.length) :
    replaceArgumentPrefix arguments (replacements ++ [replacement]) =
      replaceArgument
        (replaceArgumentPrefix arguments replacements)
        replacements.length replacement := by
  unfold replaceArgumentPrefix replaceArgument
  rw [List.set_append_right replacements.length replacement
      (Nat.le_refl replacements.length),
    List.drop_eq_getElem_cons hlength]
  simp only [Nat.sub_self, List.set_cons_zero, List.append_assoc,
    List.singleton_append, List.length_append, List.length_singleton]

/-- Prefix replacement preserves groundness when both the source tuple and
the selected replacement prefix are ground. -/
public theorem replaceArgumentPrefix_ground
    {ranks : List ℕ} {arguments replacements : List RegularTerm}
    (harguments : ∀ argument ∈ arguments, argument.Ground ranks)
    (hreplacements : ∀ replacement ∈ replacements,
      replacement.Ground ranks) :
    ∀ argument ∈ replaceArgumentPrefix arguments replacements,
      argument.Ground ranks := by
  intro argument hargument
  simp only [replaceArgumentPrefix, List.mem_append] at hargument
  rcases hargument with hreplacement | hargument
  · exact hreplacements argument hreplacement
  · exact harguments argument (List.mem_of_mem_drop hargument)

end RegularTerm

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- Repeatedly apply the positional subterm-replacement rule to an initial
prefix of a schema's arguments.  Each shorter pair is indexed by the slot it
replaces and is measured against the unchanged outer word. -/
public theorem CertificateDerivable.replaceArgumentPrefix
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm} {basis : List BasisPair}
    {word : List (Label Action)}
    {outerLeft outerRight schema : RegularTerm}
    {arguments replacements : List RegularTerm}
    (houter : CertificateDerivable g initialLeft initialRight basis
      (.pair word outerLeft outerRight))
    (hschema : schema.WellFormed g.ranks arguments.length)
    (harguments : ∀ argument ∈ arguments,
      argument.Ground g.ranks)
    (hreplacements : ∀ replacement ∈ replacements,
      replacement.Ground g.ranks)
    (hreplacementLength : replacements.length ≤ arguments.length)
    (houterLeft : outerLeft.UnfoldingEquivalent
      (schema.instantiate arguments))
    (shorterWord : ℕ → List (Label Action))
    (shorterLeft shorterRight : ℕ → RegularTerm)
    (hshorter : ∀ i, i < replacements.length →
      CertificateDerivable g initialLeft initialRight basis
        (.pair (shorterWord i) (shorterLeft i) (shorterRight i)))
    (hshorterLength : ∀ i, i < replacements.length →
      (shorterWord i).length < word.length)
    (hshorterLeft : ∀ i, (hi : i < replacements.length) →
      (shorterLeft i).UnfoldingEquivalent arguments[i])
    (hshorterRight : ∀ i, (hi : i < replacements.length) →
      (shorterRight i).UnfoldingEquivalent replacements[i]) :
    ∃ result,
      CertificateDerivable g initialLeft initialRight basis
        (.pair word result outerRight) ∧
      result.UnfoldingEquivalent
        (schema.instantiate
          (RegularTerm.replaceArgumentPrefix arguments replacements)) := by
  induction replacements using List.reverseRecOn with
  | nil =>
      exact ⟨outerLeft, houter, by
        simpa using houterLeft⟩
  | append_singleton replacements replacement ih =>
      have hprefixLength : replacements.length ≤ arguments.length := by
        have hlength := hreplacementLength
        simp only [List.length_append, List.length_singleton] at hlength
        omega
      have hboundary : replacements.length < arguments.length := by
        have hlength := hreplacementLength
        simp only [List.length_append, List.length_singleton] at hlength
        omega
      have hprefixGround :
          ∀ argument ∈
              RegularTerm.replaceArgumentPrefix arguments replacements,
            argument.Ground g.ranks := by
        apply RegularTerm.replaceArgumentPrefix_ground harguments
        intro candidate hcandidate
        exact hreplacements candidate (by
          simp only [List.mem_append, List.mem_singleton]
          exact Or.inl hcandidate)
      obtain ⟨prefixResult, hprefixDerivation, hprefixMatch⟩ :=
        ih
          (by
            intro candidate hcandidate
            exact hreplacements candidate (by
              simp only [List.mem_append, List.mem_singleton]
              exact Or.inl hcandidate))
          hprefixLength
          (fun i hi => hshorter i (by
            simp only [List.length_append, List.length_singleton]
            omega))
          (fun i hi => hshorterLength i (by
            simp only [List.length_append, List.length_singleton]
            omega))
          (fun i hi => hshorterLeft i (by
            simp only [List.length_append, List.length_singleton]
            omega))
          (fun i hi => by
            have hfull : i < (replacements ++ [replacement]).length := by
              simp only [List.length_append, List.length_singleton]
              omega
            simpa [List.getElem_append_left hi] using
              hshorterRight i hfull)
      have hcurrentLength :
          (RegularTerm.replaceArgumentPrefix arguments replacements).length =
            arguments.length :=
        RegularTerm.replaceArgumentPrefix_length hprefixLength
      have hschemaCurrent :
          schema.WellFormed g.ranks
            (RegularTerm.replaceArgumentPrefix arguments replacements).length := by
        simpa [hcurrentLength] using hschema
      have hreplacementGround : replacement.Ground g.ranks :=
        hreplacements replacement (by simp)
      have hcurrentBoundary :
          replacements.length <
            (RegularTerm.replaceArgumentPrefix arguments replacements).length := by
        rw [hcurrentLength]
        exact hboundary
      have hboundarySlot :
          (RegularTerm.replaceArgumentPrefix arguments replacements)[
              replacements.length] =
            arguments[replacements.length] := by
        have hleftGet :=
          List.getElem?_eq_getElem hcurrentBoundary
        have hrightGet :=
          List.getElem?_eq_getElem hboundary
        exact Option.some.inj
          (hleftGet.symm.trans
            ((RegularTerm.replaceArgumentPrefix_getElem?_boundary
              hboundary).trans hrightGet))
      obtain ⟨result, hresult, hresultMatch⟩ :=
        hprefixDerivation.replaceArgument
          (hshorter replacements.length (by simp))
          hschemaCurrent hprefixGround
          (by simpa [hcurrentLength] using hboundary)
          hreplacementGround
          (hshorterLength replacements.length (by simp))
          hprefixMatch
          (by
            rw [hboundarySlot]
            exact hshorterLeft replacements.length (by simp))
          (by
            simpa using hshorterRight replacements.length (by simp))
      refine ⟨result, hresult, ?_⟩
      simpa [RegularTerm.replaceArgumentPrefix_append replacement hboundary]
        using hresultMatch

/-- Finite-indexed interface to prefix replacement.  This is convenient when
the shorter rows are selected as one dependent family over the replacement
tuple. -/
public theorem CertificateDerivable.replaceArgumentPrefixFin
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm} {basis : List BasisPair}
    {word : List (Label Action)}
    {outerLeft outerRight schema : RegularTerm}
    {arguments replacements : List RegularTerm}
    (houter : CertificateDerivable g initialLeft initialRight basis
      (.pair word outerLeft outerRight))
    (hschema : schema.WellFormed g.ranks arguments.length)
    (harguments : ∀ argument ∈ arguments,
      argument.Ground g.ranks)
    (hreplacements : ∀ replacement ∈ replacements,
      replacement.Ground g.ranks)
    (hreplacementLength : replacements.length ≤ arguments.length)
    (houterLeft : outerLeft.UnfoldingEquivalent
      (schema.instantiate arguments))
    (shorterWord : Fin replacements.length → List (Label Action))
    (shorterLeft shorterRight : Fin replacements.length → RegularTerm)
    (hshorter : ∀ i,
      CertificateDerivable g initialLeft initialRight basis
        (.pair (shorterWord i) (shorterLeft i) (shorterRight i)))
    (hshorterLength : ∀ i,
      (shorterWord i).length < word.length)
    (hshorterLeft : ∀ i,
      (shorterLeft i).UnfoldingEquivalent arguments[i.val])
    (hshorterRight : ∀ i,
      (shorterRight i).UnfoldingEquivalent replacements[i.val]) :
    ∃ result,
      CertificateDerivable g initialLeft initialRight basis
        (.pair word result outerRight) ∧
      result.UnfoldingEquivalent
        (schema.instantiate
          (RegularTerm.replaceArgumentPrefix arguments replacements)) := by
  let wordAt : ℕ → List (Label Action) := fun i =>
    if hi : i < replacements.length then shorterWord ⟨i, hi⟩ else []
  let leftAt : ℕ → RegularTerm := fun i =>
    if hi : i < replacements.length then shorterLeft ⟨i, hi⟩
    else RegularTerm.variableTerm 0
  let rightAt : ℕ → RegularTerm := fun i =>
    if hi : i < replacements.length then shorterRight ⟨i, hi⟩
    else RegularTerm.variableTerm 0
  apply houter.replaceArgumentPrefix hschema harguments hreplacements
    hreplacementLength houterLeft wordAt leftAt rightAt
  · intro i hi
    simpa [wordAt, leftAt, rightAt, hi] using hshorter ⟨i, hi⟩
  · intro i hi
    simpa [wordAt, hi] using hshorterLength ⟨i, hi⟩
  · intro i hi
    simpa [leftAt, hi] using hshorterLeft ⟨i, hi⟩
  · intro i hi
    simpa [rightAt, hi] using hshorterRight ⟨i, hi⟩

end EncodedFirstOrderGrammar

end DCFEquivalence
