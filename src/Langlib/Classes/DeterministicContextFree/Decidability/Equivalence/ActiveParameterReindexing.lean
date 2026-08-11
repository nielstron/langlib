module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.RegularStairBases

@[expose]
public section

/-!
# Reindexing active schema parameters

Tail elimination is simplest when the parameter being removed is the final
active one.  This file implements the bounded preprocessing step: swap any
chosen active position `x` with `width - 1`, simultaneously in the open schema
and in its fixed argument tuple.

The schema transformation is itself an ordinary substitution by variable
terms.  The argument transformation uses the same involutive transposition, so
the represented instance is unchanged up to unfolding equivalence.
-/

namespace DCFEquivalence

namespace RegularTerm

private theorem swapIndex_lt
    {bound x y i : ℕ}
    (hx : x < bound) (hy : y < bound) (hi : i < bound) :
    Equiv.swap x y i < bound := by
  rw [Equiv.swap_apply_def]
  split
  · exact hy
  · split
    · exact hx
    · exact hi

/-- Reorder a finite argument tuple by swapping positions `x` and `y`.
Out-of-range swaps are totalized by the harmless variable-zero fallback; all
semantic lemmas below assume both swapped indices are in range, so the fallback
is never selected. -/
@[expose] public def swapArguments
    (arguments : List RegularTerm) (x y : ℕ) : List RegularTerm :=
  (List.range arguments.length).map fun i =>
    (arguments[Equiv.swap x y i]?).getD (variableTerm 0)

@[simp] public theorem swapArguments_length
    (arguments : List RegularTerm) (x y : ℕ) :
    (swapArguments arguments x y).length = arguments.length := by
  simp [swapArguments]

public theorem swapArguments_getElem?
    {arguments : List RegularTerm} {x y i : ℕ}
    (hx : x < arguments.length) (hy : y < arguments.length)
    (hi : i < arguments.length) :
    (swapArguments arguments x y)[i]? =
      arguments[Equiv.swap x y i]? := by
  have hswap := swapIndex_lt hx hy hi
  simp [swapArguments, hi, hswap]

public theorem swapArguments_getElem?_left
    {arguments : List RegularTerm} {x y : ℕ}
    (hx : x < arguments.length) (hy : y < arguments.length) :
    (swapArguments arguments x y)[x]? = arguments[y]? := by
  simpa using
    (swapArguments_getElem? (arguments := arguments)
      hx hy hx).trans (by simp)

public theorem swapArguments_getElem?_right
    {arguments : List RegularTerm} {x y : ℕ}
    (hx : x < arguments.length) (hy : y < arguments.length) :
    (swapArguments arguments x y)[y]? = arguments[x]? := by
  simpa using
    (swapArguments_getElem? (arguments := arguments)
      hx hy hy).trans (by simp)

/-- Swapping the same two positions twice restores the raw argument list. -/
public theorem swapArguments_swap
    {arguments : List RegularTerm} {x y : ℕ}
    (hx : x < arguments.length) (hy : y < arguments.length) :
    swapArguments (swapArguments arguments x y) x y = arguments := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < arguments.length
  · have houterX : x < (swapArguments arguments x y).length := by
      simpa using hx
    have houterY : y < (swapArguments arguments x y).length := by
      simpa using hy
    have houterI : i < (swapArguments arguments x y).length := by
      simpa using hi
    rw [swapArguments_getElem? houterX houterY houterI]
    have hswap := swapIndex_lt hx hy hi
    rw [swapArguments_getElem? hx hy hswap]
    simp
  · have hleft : ¬i < (swapArguments
        (swapArguments arguments x y) x y).length := by
      simpa using hi
    rw [List.getElem?_eq_none (Nat.le_of_not_gt hleft),
      List.getElem?_eq_none (Nat.le_of_not_gt hi)]

/-- The swap preserves any property held by every input argument. -/
public theorem swapArguments_forall_mem
    {arguments : List RegularTerm} {x y : ℕ}
    (hx : x < arguments.length) (hy : y < arguments.length)
    {P : RegularTerm → Prop}
    (hP : ∀ argument ∈ arguments, P argument) :
    ∀ argument ∈ swapArguments arguments x y, P argument := by
  intro argument hargument
  obtain ⟨i, hiRange, hvalue⟩ := List.mem_map.mp hargument
  have hi : i < arguments.length := List.mem_range.mp hiRange
  have hswap := swapIndex_lt hx hy hi
  have hget := List.getElem?_eq_getElem
    (l := arguments) hswap
  rw [hget] at hvalue
  simp only [Option.getD_some] at hvalue
  subst argument
  exact hP _ (List.getElem_mem hswap)

/-- One-node variable terms are reference closed. -/
public theorem variableTerm_referenceClosed (x : ℕ) :
    (variableTerm x).ReferenceClosed := by
  apply identityArguments_referenceClosed (x + 1)
  exact List.mem_of_getElem?
    (identityArguments_getElem? (by omega))

/-- One-node variable terms are well formed at every arity containing their
index. -/
public theorem variableTerm_wellFormed
    {ranks : List ℕ} {arity x : ℕ} (hx : x < arity) :
    (variableTerm x).WellFormed ranks arity := by
  unfold variableTerm WellFormed wellFormedCode nodes root
  simp [nodeWellFormedCode, hx]

/-- The positional variable substitution implementing the transposition. -/
@[expose] public def swapIdentityArguments
    (arity x y : ℕ) : List RegularTerm :=
  swapArguments (identityArguments arity) x y

@[simp] public theorem swapIdentityArguments_length
    (arity x y : ℕ) :
    (swapIdentityArguments arity x y).length = arity := by
  simp [swapIdentityArguments]

public theorem swapIdentityArguments_getElem?
    {arity x y i : ℕ}
    (hx : x < arity) (hy : y < arity) (hi : i < arity) :
    (swapIdentityArguments arity x y)[i]? =
      some (variableTerm (Equiv.swap x y i)) := by
  unfold swapIdentityArguments
  rw [swapArguments_getElem? (by simpa) (by simpa) (by simpa)]
  exact identityArguments_getElem? (swapIndex_lt hx hy hi)

private theorem swapIdentityArguments_eq_map
    {arity x y : ℕ} (hx : x < arity) (hy : y < arity) :
    swapIdentityArguments arity x y =
      (List.range arity).map fun i =>
        variableTerm (Equiv.swap x y i) := by
  unfold swapIdentityArguments swapArguments
  rw [identityArguments_length]
  apply List.map_congr_left
  intro i hi
  have hiBound : i < arity := List.mem_range.mp hi
  have hswap := swapIndex_lt hx hy hiBound
  rw [identityArguments_getElem? hswap]
  rfl

public theorem swapIdentityArguments_referenceClosed
    {arity x y : ℕ} (hx : x < arity) (hy : y < arity) :
    ∀ argument ∈ swapIdentityArguments arity x y,
      argument.ReferenceClosed := by
  unfold swapIdentityArguments
  apply swapArguments_forall_mem
    (arguments := identityArguments arity)
    (P := fun argument => argument.ReferenceClosed)
    (by simpa) (by simpa)
  exact identityArguments_referenceClosed arity

private theorem swapIdentityArguments_wellFormed
    {ranks : List ℕ} {arity x y : ℕ}
    (hx : x < arity) (hy : y < arity) :
    ∀ argument ∈ swapIdentityArguments arity x y,
      argument.WellFormed ranks arity := by
  intro argument hargument
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hargument
  have hiBound : i < arity := by
    have := (List.getElem?_eq_some_iff.mp hi).choose
    simpa using this
  rw [swapIdentityArguments_getElem? hx hy hiBound] at hi
  cases Option.some.inj hi
  exact variableTerm_wellFormed
    (swapIndex_lt hx hy hiBound)

/-- Reindex an open schema by the transposition of `x` and `y`. -/
@[expose] public def swapParameters
    (schema : RegularTerm) (arity x y : ℕ) : RegularTerm :=
  schema.instantiate (swapIdentityArguments arity x y)

/-- Parameter swapping preserves the schema's ranked arity. -/
public theorem swapParameters_wellFormed
    {ranks : List ℕ} {schema : RegularTerm} {arity x y : ℕ}
    (hschema : schema.WellFormed ranks arity)
    (hx : x < arity) (hy : y < arity) :
    (swapParameters schema arity x y).WellFormed ranks arity := by
  have hresult := instantiate_wellFormed_max
    (arguments := swapIdentityArguments arity x y)
    (by simpa using hschema)
    (swapIdentityArguments_wellFormed hx hy)
  simpa [swapParameters] using hresult

private theorem forall₂_map_same_local
    {A B C : Type} {R : B → C → Prop}
    (left : A → B) (right : A → C) (values : List A)
    (h : ∀ value ∈ values, R (left value) (right value)) :
    List.Forall₂ R (values.map left) (values.map right) := by
  induction values with
  | nil => exact .nil
  | cons value values ih =>
      exact .cons (h value (by simp))
        (ih fun tail htail => h tail (by simp [htail]))

private theorem composedSwapIdentity_forall₂
    {arity x y : ℕ} {arguments : List RegularTerm}
    (hargumentsLength : arguments.length = arity)
    (hx : x < arity) (hy : y < arity)
    (hargumentsClosed :
      ∀ argument ∈ arguments, argument.ReferenceClosed) :
    List.Forall₂ UnfoldingEquivalent
      (composedContexts (swapIdentityArguments arity x y) arguments)
      (swapArguments arguments x y) := by
  rw [swapIdentityArguments_eq_map hx hy]
  unfold composedContexts swapArguments
  rw [hargumentsLength]
  rw [List.map_map]
  apply forall₂_map_same_local
  intro i hiRange
  have hi : i < arity := List.mem_range.mp hiRange
  have hswap : Equiv.swap x y i < arguments.length := by
    rw [hargumentsLength]
    exact swapIndex_lt hx hy hi
  let argument := arguments[Equiv.swap x y i]
  have hargument :
      arguments[Equiv.swap x y i]? = some argument :=
    List.getElem?_eq_getElem hswap
  have hroot :
      (variableTerm (Equiv.swap x y i)).nodeAt?
          (variableTerm (Equiv.swap x y i)).root =
        some (.inl (Equiv.swap x y i)) := by
    simpa [rootNode?] using
      variableTerm_rootNode? (Equiv.swap x y i)
  have hequivalent :=
    instantiate_unfoldingEquivalent_argument hroot hargument
      (hargumentsClosed argument
        (List.getElem_mem hswap))
  simpa [hargument] using hequivalent

private theorem composedSwapIdentity_referenceClosed
    {arity x y : ℕ} {arguments : List RegularTerm}
    (hx : x < arity) (hy : y < arity)
    (hargumentsClosed :
      ∀ argument ∈ arguments, argument.ReferenceClosed) :
    ∀ context ∈
        composedContexts (swapIdentityArguments arity x y) arguments,
      context.ReferenceClosed := by
  intro context hcontext
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hcontext
  exact instantiate_referenceClosed
    (swapIdentityArguments_referenceClosed hx hy source hsource)
    hargumentsClosed

/-- Reindexing a schema and then instantiating it by `arguments` is equivalent
to instantiating the original schema by the correspondingly swapped tuple. -/
public theorem swapParameters_instantiate_unfoldingEquivalent
    {ranks : List ℕ} {schema : RegularTerm}
    {arity x y : ℕ} {arguments : List RegularTerm}
    (hschema : schema.WellFormed ranks arity)
    (hx : x < arity) (hy : y < arity)
    (hargumentsLength : arguments.length = arity)
    (hargumentsClosed :
      ∀ argument ∈ arguments, argument.ReferenceClosed) :
    RegularTerm.UnfoldingEquivalent
      ((swapParameters schema arity x y).instantiate arguments)
      (schema.instantiate (swapArguments arguments x y)) := by
  have hcomposition := instantiate_comp_unfoldingEquivalent
    (outer := schema)
    (contexts := swapIdentityArguments arity x y)
    (arguments := arguments)
    (by simpa using hschema)
    (swapIdentityArguments_referenceClosed hx hy)
    hargumentsClosed
  have hxArguments : x < arguments.length := by
    simpa [hargumentsLength] using hx
  have hyArguments : y < arguments.length := by
    simpa [hargumentsLength] using hy
  have hswappedClosed :
      ∀ argument ∈ swapArguments arguments x y,
        argument.ReferenceClosed :=
    swapArguments_forall_mem hxArguments hyArguments
      hargumentsClosed
  have hcongruence := instantiate_unfoldingEquivalent
    (referenceClosed_of_wellFormed hschema)
    (composedSwapIdentity_forall₂
      hargumentsLength hx hy hargumentsClosed)
    (composedSwapIdentity_referenceClosed
      hx hy hargumentsClosed)
    hswappedClosed
  have hcomposition' :
      RegularTerm.UnfoldingEquivalent
        ((swapParameters schema arity x y).instantiate arguments)
        (schema.instantiate
          (composedContexts
            (swapIdentityArguments arity x y) arguments)) := by
    simpa [swapParameters] using hcomposition
  exact hcomposition'.trans hcongruence

/-- Swapping both the schema and its fixed argument tuple preserves the
represented regular tree. -/
public theorem swapParameters_fixedInstance_unfoldingEquivalent
    {ranks : List ℕ} {schema : RegularTerm}
    {arity x y : ℕ} {arguments : List RegularTerm}
    (hschema : schema.WellFormed ranks arity)
    (hx : x < arity) (hy : y < arity)
    (hargumentsLength : arguments.length = arity)
    (hargumentsClosed :
      ∀ argument ∈ arguments, argument.ReferenceClosed) :
    ((swapParameters schema arity x y).instantiate
        (swapArguments arguments x y)).UnfoldingEquivalent
      (schema.instantiate arguments) := by
  have hxArguments : x < arguments.length := by
    simpa [hargumentsLength] using hx
  have hyArguments : y < arguments.length := by
    simpa [hargumentsLength] using hy
  have hswappedClosed :
      ∀ argument ∈ swapArguments arguments x y,
        argument.ReferenceClosed :=
    swapArguments_forall_mem hxArguments hyArguments
      hargumentsClosed
  have hresult := swapParameters_instantiate_unfoldingEquivalent
    (arguments := swapArguments arguments x y)
    hschema hx hy (swapArguments_length arguments x y |>.trans
      hargumentsLength) hswappedClosed
  rw [swapArguments_swap hxArguments hyArguments] at hresult
  exact hresult

/-- The graph-size overhead of parameter reindexing is exactly one copied
variable node per schema parameter. -/
public theorem swapParameters_nodes_length
    {schema : RegularTerm} {arity x y : ℕ}
    (hx : x < arity) (hy : y < arity) :
    (swapParameters schema arity x y).nodes.length =
      schema.nodes.length + arity := by
  unfold RegularTerm.swapParameters
  rw [instantiate_nodes_length,
    swapIdentityArguments_eq_map hx hy]
  simp [Function.comp_def, variableTerm, nodes]

/-- Swapping positions inside the active prefix preserves pointwise semantic
agreement through that prefix. -/
public theorem ArgumentsEquivalentThrough.swapArguments
    {width x y : ℕ} {left right : List RegularTerm}
    (harguments : ArgumentsEquivalentThrough width left right)
    (hx : x < width) (hy : y < width)
    (hleftWidth : width ≤ left.length)
    (hrightWidth : width ≤ right.length) :
    ArgumentsEquivalentThrough width
      (swapArguments left x y) (swapArguments right x y) := by
  intro i hi
  have hswapWidth : Equiv.swap x y i < width :=
    swapIndex_lt hx hy hi
  obtain ⟨leftArgument, rightArgument,
      hleft, hright, hequivalent⟩ :=
    harguments (Equiv.swap x y i) hswapWidth
  have hxLeft : x < left.length := hx.trans_le hleftWidth
  have hyLeft : y < left.length := hy.trans_le hleftWidth
  have hiLeft : i < left.length := hi.trans_le hleftWidth
  have hxRight : x < right.length := hx.trans_le hrightWidth
  have hyRight : y < right.length := hy.trans_le hrightWidth
  have hiRight : i < right.length := hi.trans_le hrightWidth
  refine ⟨leftArgument, rightArgument, ?_, ?_, hequivalent⟩
  · rw [swapArguments_getElem? hxLeft hyLeft hiLeft]
    exact hleft
  · rw [swapArguments_getElem? hxRight hyRight hiRight]
    exact hright

/-- A transposition wholly inside the active prefix transports the support
invariant to the reindexed schema. -/
public theorem SupportedByPrefix.swapParameters
    {ranks : List ℕ} {schema : RegularTerm}
    {arity width x y : ℕ}
    (hsupported : SupportedByPrefix ranks arity width schema)
    (hx : x < width) (hy : y < width) :
    SupportedByPrefix ranks arity width
      (swapParameters schema arity x y) := by
  have hxArity : x < arity := hx.trans_le hsupported.2.1
  have hyArity : y < arity := hy.trans_le hsupported.2.1
  refine ⟨swapParameters_wellFormed hsupported.1
      hxArity hyArity, hsupported.2.1, ?_⟩
  intro leftArguments rightArguments
    hleftLength hrightLength hleftClosed hrightClosed harguments
  have hxLeft : x < leftArguments.length := by
    simpa [hleftLength] using hxArity
  have hyLeft : y < leftArguments.length := by
    simpa [hleftLength] using hyArity
  have hxRight : x < rightArguments.length := by
    simpa [hrightLength] using hxArity
  have hyRight : y < rightArguments.length := by
    simpa [hrightLength] using hyArity
  have hleftSwappedClosed :
      ∀ argument ∈ swapArguments leftArguments x y,
        argument.ReferenceClosed :=
    swapArguments_forall_mem hxLeft hyLeft hleftClosed
  have hrightSwappedClosed :
      ∀ argument ∈ swapArguments rightArguments x y,
        argument.ReferenceClosed :=
    swapArguments_forall_mem hxRight hyRight hrightClosed
  have hswappedArguments :
      ArgumentsEquivalentThrough width
        (swapArguments leftArguments x y)
        (swapArguments rightArguments x y) :=
    harguments.swapArguments hx hy
      (by simpa [hleftLength] using hsupported.2.1)
      (by simpa [hrightLength] using hsupported.2.1)
  have hmiddle := hsupported.2.2
    (swapArguments leftArguments x y)
    (swapArguments rightArguments x y)
    (swapArguments_length leftArguments x y |>.trans hleftLength)
    (swapArguments_length rightArguments x y |>.trans hrightLength)
    hleftSwappedClosed hrightSwappedClosed hswappedArguments
  have hleftReindex :=
    swapParameters_instantiate_unfoldingEquivalent
      hsupported.1 hxArity hyArity hleftLength hleftClosed
  have hrightReindex :=
    swapParameters_instantiate_unfoldingEquivalent
      hsupported.1 hxArity hyArity hrightLength hrightClosed
  exact hleftReindex.trans (hmiddle.trans hrightReindex.symm)

/-- Move one chosen active parameter to the final active position. -/
@[expose] public def moveParameterToActiveLast
    (schema : RegularTerm) (arity width x : ℕ) : RegularTerm :=
  swapParameters schema arity x (width - 1)

/-- Apply the matching transposition to a fixed argument tuple. -/
@[expose] public def moveArgumentToActiveLast
    (arguments : List RegularTerm) (width x : ℕ) : List RegularTerm :=
  swapArguments arguments x (width - 1)

/-- After the move, the final active argument is the originally selected one. -/
public theorem moveArgumentToActiveLast_getElem?
    {arguments : List RegularTerm} {width x : ℕ}
    (hwidth : 0 < width) (hx : x < width)
    (hwidthArguments : width ≤ arguments.length) :
    (moveArgumentToActiveLast arguments width x)[width - 1]? =
      arguments[x]? := by
  unfold moveArgumentToActiveLast
  apply swapArguments_getElem?_right
  · exact hx.trans_le hwidthArguments
  · omega

/-- Moving an active parameter to the last active position preserves prefix
support. -/
public theorem SupportedByPrefix.moveParameterToActiveLast
    {ranks : List ℕ} {schema : RegularTerm}
    {arity width x : ℕ}
    (hsupported : SupportedByPrefix ranks arity width schema)
    (hwidth : 0 < width) (hx : x < width) :
    SupportedByPrefix ranks arity width
      (moveParameterToActiveLast schema arity width x) := by
  change SupportedByPrefix ranks arity width
    (RegularTerm.swapParameters schema arity x (width - 1))
  exact SupportedByPrefix.swapParameters hsupported hx (by omega)

/-- Moving both a supported schema and its fixed tuple to put `x` last
preserves the represented instance. -/
public theorem moveParameterToActiveLast_fixedInstance
    {ranks : List ℕ} {schema : RegularTerm}
    {arity width x : ℕ} {arguments : List RegularTerm}
    (hsupported : SupportedByPrefix ranks arity width schema)
    (hwidth : 0 < width) (hx : x < width)
    (hargumentsLength : arguments.length = arity)
    (hargumentsClosed :
      ∀ argument ∈ arguments, argument.ReferenceClosed) :
    RegularTerm.UnfoldingEquivalent
      ((moveParameterToActiveLast schema arity width x).instantiate
        (moveArgumentToActiveLast arguments width x))
      (schema.instantiate arguments) := by
  have hxArity : x < arity := hx.trans_le hsupported.2.1
  have hlastArity : width - 1 < arity := by
    have hlastWidth : width - 1 < width := by omega
    exact hlastWidth.trans_le hsupported.2.1
  simpa [RegularTerm.moveParameterToActiveLast,
    RegularTerm.moveArgumentToActiveLast] using
      (swapParameters_fixedInstance_unfoldingEquivalent
        hsupported.1 hxArity hlastArity
          hargumentsLength hargumentsClosed)

end RegularTerm

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

omit [DecidableEq Action] in
public theorem groundArgumentsCode_swapArguments
    {g : EncodedFirstOrderGrammar Action}
    {arguments : List RegularTerm} {x y : ℕ}
    (hground : g.groundArgumentsCode arguments = true)
    (hx : x < arguments.length) (hy : y < arguments.length) :
    g.groundArgumentsCode
      (RegularTerm.swapArguments arguments x y) = true := by
  unfold groundArgumentsCode at hground ⊢
  apply List.all_eq_true.mpr
  apply RegularTerm.swapArguments_forall_mem
    (P := fun argument =>
      RegularTerm.groundCode g.ranks argument = true)
    hx hy
  exact List.all_eq_true.mp hground

namespace ActiveSchemaCoverage

public theorem reindexed_arguments_referenceClosed
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm} {width word}
    (coverage : ActiveSchemaCoverage g initialLeft initialRight width word) :
    ∀ argument ∈ coverage.arguments,
      argument.ReferenceClosed := by
  have harguments := coverage.arguments_ground
  unfold groundArgumentsCode at harguments
  have hall := List.all_eq_true.mp harguments
  intro argument hargument
  exact RegularTerm.referenceClosed_of_ground
    ((RegularTerm.groundCode_eq_true_iff g.ranks argument).mp
      (hall argument hargument))

/-- Reindex an active-schema presentation so the chosen active argument is in
the final active slot.  The residual pair and its derivation are unchanged;
only the two open schemas and their common fixed argument tuple are
transposed. -/
public def moveParameterToActiveLast
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm} {width word}
    (coverage : ActiveSchemaCoverage g initialLeft initialRight width word)
    (hwidth : 0 < width) (x : ℕ) (hx : x < width) :
    ActiveSchemaCoverage g initialLeft initialRight width word := by
  let leftSchema := RegularTerm.moveParameterToActiveLast
    coverage.schema.left coverage.schema.arity width x
  let rightSchema := RegularTerm.moveParameterToActiveLast
    coverage.schema.right coverage.schema.arity width x
  let arguments := RegularTerm.moveArgumentToActiveLast
    coverage.arguments width x
  let schema : BasisPair :=
    (coverage.schema.arity, leftSchema, rightSchema)
  have hleftSupported :=
    coverage.left_supported.moveParameterToActiveLast hwidth hx
  have hrightSupported :=
    coverage.right_supported.moveParameterToActiveLast hwidth hx
  have hargumentsClosed := reindexed_arguments_referenceClosed coverage
  have hxArguments : x < coverage.arguments.length := by
    rw [coverage.argument_count]
    exact hx.trans_le coverage.left_supported.2.1
  have hlastArguments :
      width - 1 < coverage.arguments.length := by
    rw [coverage.argument_count]
    have hlastWidth : width - 1 < width := by omega
    exact hlastWidth.trans_le coverage.left_supported.2.1
  have hleftFixed :=
    RegularTerm.moveParameterToActiveLast_fixedInstance
      coverage.left_supported hwidth hx coverage.argument_count
        hargumentsClosed
  have hrightFixed :=
    RegularTerm.moveParameterToActiveLast_fixedInstance
      coverage.right_supported hwidth hx coverage.argument_count
        hargumentsClosed
  have hleftMatch :=
    (RegularTerm.unfoldingEquivalentCode_eq_true_iff _ _).mp
      coverage.left_matches
  have hrightMatch :=
    (RegularTerm.unfoldingEquivalentCode_eq_true_iff _ _).mp
      coverage.right_matches
  refine
    { left := coverage.left
      right := coverage.right
      derivation := coverage.derivation
      schema := schema
      arguments := arguments
      word_nonempty := coverage.word_nonempty
      schema_wellFormed := ?_
      rank_padding := coverage.rank_padding
      left_supported := ?_
      right_supported := ?_
      argument_count := ?_
      arguments_ground := ?_
      left_matches := ?_
      right_matches := ?_ }
  · unfold schema basisPairWellFormedCode BasisPair.left BasisPair.right
    rw [Bool.and_eq_true]
    exact ⟨hleftSupported.1, hrightSupported.1⟩
  · change RegularTerm.SupportedByPrefix g.ranks
      coverage.schema.arity width leftSchema
    exact hleftSupported
  · change RegularTerm.SupportedByPrefix g.ranks
      coverage.schema.arity width rightSchema
    exact hrightSupported
  · change arguments.length = coverage.schema.arity
    simp [arguments, RegularTerm.moveArgumentToActiveLast,
      coverage.argument_count]
  · unfold arguments RegularTerm.moveArgumentToActiveLast
    exact groundArgumentsCode_swapArguments coverage.arguments_ground
      hxArguments hlastArguments
  · apply (RegularTerm.unfoldingEquivalentCode_eq_true_iff _ _).mpr
    simpa [schema, leftSchema, arguments] using
      hleftMatch.trans hleftFixed.symm
  · apply (RegularTerm.unfoldingEquivalentCode_eq_true_iff _ _).mpr
    simpa [schema, rightSchema, arguments] using
      hrightMatch.trans hrightFixed.symm

end ActiveSchemaCoverage

namespace BoundedActiveSchemaCoverage

/-- The bounded presentation-level transposition.  Reindexing copies one
one-node variable graph per parameter, so doubling the old bound uniformly
absorbs both the old schema size and its arity. -/
public def moveParameterToActiveLast
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {bound width : ℕ} {arguments : List RegularTerm} {word}
    (coverage : BoundedActiveSchemaCoverage g initialLeft initialRight
      bound width arguments word)
    (hwidth : 0 < width) (x : ℕ) (hx : x < width) :
    BoundedActiveSchemaCoverage g initialLeft initialRight
      (bound + bound) width
      (RegularTerm.moveArgumentToActiveLast arguments width x) word := by
  let moved := coverage.coverage.moveParameterToActiveLast
    hwidth x hx
  have hxArity : x < coverage.coverage.schema.arity :=
    hx.trans_le coverage.coverage.left_supported.2.1
  have hlastArity :
      width - 1 < coverage.coverage.schema.arity := by
    have hlastWidth : width - 1 < width := by omega
    exact hlastWidth.trans_le
      coverage.coverage.left_supported.2.1
  refine
    { coverage := moved
      arguments_eq := ?_
      arity_le := ?_
      left_size_le := ?_
      right_size_le := ?_ }
  · change RegularTerm.moveArgumentToActiveLast
      coverage.coverage.arguments width x =
        RegularTerm.moveArgumentToActiveLast arguments width x
    exact congrArg
      (fun tuple =>
        RegularTerm.moveArgumentToActiveLast tuple width x)
      coverage.arguments_eq
  · change coverage.coverage.schema.arity ≤ bound + bound
    exact coverage.arity_le.trans (by omega)
  · change
      (RegularTerm.moveParameterToActiveLast
        coverage.coverage.schema.left
        coverage.coverage.schema.arity width x).nodes.length ≤
          bound + bound
    rw [RegularTerm.moveParameterToActiveLast,
      RegularTerm.swapParameters_nodes_length hxArity hlastArity]
    exact Nat.add_le_add coverage.left_size_le coverage.arity_le
  · change
      (RegularTerm.moveParameterToActiveLast
        coverage.coverage.schema.right
        coverage.coverage.schema.arity width x).nodes.length ≤
          bound + bound
    rw [RegularTerm.moveParameterToActiveLast,
      RegularTerm.swapParameters_nodes_length hxArity hlastArity]
    exact Nat.add_le_add coverage.right_size_le coverage.arity_le

end BoundedActiveSchemaCoverage

namespace RegularActiveStairSequence

/-- Reindex every level of a regular active stair by one common active
transposition.  The path levels are unchanged and the exact `+ arity` schema
overhead is absorbed by doubling the old growth bound pointwise. -/
public def moveParameterToActiveLast
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {width : ℕ} {growth : ℕ → ℕ}
    {path : TracePath g initialLeft initialRight}
    (sequence : RegularActiveStairSequence g initialLeft initialRight
      width growth path)
    (hwidth : 0 < width) (x : ℕ) (hx : x < width) :
    RegularActiveStairSequence g initialLeft initialRight width
      (fun j => growth j + growth j) path :=
  { arguments := RegularTerm.moveArgumentToActiveLast
      sequence.arguments width x
    levels := sequence.levels
    levels_strictMono := sequence.levels_strictMono
    covered := by
      intro j
      obtain ⟨coverage⟩ := sequence.covered j
      exact ⟨coverage.moveParameterToActiveLast hwidth x hx⟩ }

end RegularActiveStairSequence

end EncodedFirstOrderGrammar

end DCFEquivalence
