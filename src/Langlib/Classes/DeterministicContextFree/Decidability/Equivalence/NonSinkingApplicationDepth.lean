module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.FixedTailPivotSubsequence

@[expose]
public section

/-!
# Protected application depth along non-sinking symbolic runs

The depth-`d` prefix schema of a ground term initially has
`ApplicationDepth d`.  A root rewrite can lower that depth only by selecting
an immediate argument of its current source; operationally, that one-letter
step sinks.  Consequently a symbolic run whose every local step is
non-sinking preserves the full application depth, independently of its
length.

For the Proposition-49 pivot suffix, the paper states non-sinking relative to
one fixed base term.  Turning that global statement into local non-sinking of
each symbolic residual needs an additional operational reflection invariant:
any local symbolic sink must induce a sinking prefix from the fixed base.
That invariant is named explicitly below.  This separates the structural
depth theorem proved here from the still-specific pivot-path argument which
must establish the reflection premise.
-/

namespace DCFEquivalence

namespace RegularTerm

private theorem withRoot_wellFormed_of_lt
    {ranks : List ℕ} {arity : ℕ} {term : RegularTerm}
    (hterm : term.WellFormed ranks arity)
    {i : ℕ} (hi : i < term.nodes.length) :
    (term.withRoot i).WellFormed ranks arity := by
  unfold WellFormed wellFormedCode at hterm ⊢
  rw [Bool.and_eq_true] at hterm ⊢
  refine ⟨?_, ?_⟩
  · simpa [withRoot, root, nodes] using decide_eq_true hi
  · simpa [withRoot, nodes] using hterm.2

private theorem variable_lt_of_wellFormed
    {ranks : List ℕ} {arity : ℕ} {term : RegularTerm}
    (hterm : term.WellFormed ranks arity)
    {i x : ℕ} (hnode : term.nodeAt? i = some (.inl x)) :
    x < arity := by
  unfold WellFormed wellFormedCode at hterm
  rw [Bool.and_eq_true] at hterm
  have hmem : (.inl x : RawNode) ∈ term.nodes :=
    List.mem_of_getElem? hnode
  have hwell := (List.all_eq_true.mp hterm.2) _ hmem
  simpa [nodeWellFormedCode] using of_decide_eq_true hwell

end RegularTerm

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- A non-sinking ordinary rewrite preserves the complete protected
application depth of its symbolic source. -/
public theorem stepAction_preserves_applicationDepth_of_not_sinks
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {source target : RegularTerm} {action : Action} {depth : ℕ}
    (hsource : ∃ arity, source.WellFormed g.ranks arity)
    (hdepth : source.ApplicationDepth depth)
    (hstep : g.step? (.inl action) source = some target)
    (hnotSinks : ¬g.SinksBy source [.inl action]) :
    target.ApplicationDepth depth := by
  cases depth with
  | zero => trivial
  | succ depth =>
      obtain ⟨sourceArity, hsourceWellFormed⟩ := hsource
      obtain ⟨X, children, hsourceRoot, hchildrenDepth⟩ := hdepth
      have hstepOriginal := hstep
      change g.rootRewrite? action source = some target at hstep
      unfold rootRewrite? at hstep
      rw [hsourceRoot] at hstep
      obtain ⟨rhs, hrule, rfl⟩ :=
        Option.map_eq_some_iff.mp hstep
      obtain ⟨rank, hrank, hrhsWellFormed⟩ :=
        selected_rhs_wellFormed hg hrule
      have hsourceRootNode :=
        RegularTerm.nodeAt?_root_of_rootApplication? hsourceRoot
      have hsourceNodeWellFormed := hsourceWellFormed
      unfold RegularTerm.WellFormed
        RegularTerm.wellFormedCode at hsourceNodeWellFormed
      rw [Bool.and_eq_true] at hsourceNodeWellFormed
      have hsourceRootMem :
          (.inr (X, children) : RawNode) ∈ source.nodes :=
        List.mem_of_getElem? hsourceRootNode
      have hsourceRootWell :=
        (List.all_eq_true.mp hsourceNodeWellFormed.2) _
          hsourceRootMem
      unfold RegularTerm.nodeWellFormedCode at hsourceRootWell
      cases hsourceRank : g.ranks[X]? with
      | none => simp [hsourceRank] at hsourceRootWell
      | some sourceRank =>
          simp only [hsourceRank, Bool.and_eq_true,
            decide_eq_true_eq] at hsourceRootWell
          have hrankEq : rank = sourceRank :=
            Option.some.inj (hrank.symm.trans hsourceRank)
          have hrhsChildren :
              rhs.WellFormed g.ranks children.length := by
            rw [hsourceRootWell.1, ← hrankEq]
            exact hrhsWellFormed
          let arguments := children.map source.withRoot
          have hargumentsDepth :
              ∀ argument ∈ arguments,
                argument.ApplicationDepth depth := by
            intro argument hargument
            obtain ⟨child, hchild, rfl⟩ :=
              List.mem_map.mp hargument
            exact hchildrenDepth child hchild
          have hsourceClosed :=
            RegularTerm.referenceClosed_of_wellFormed
              hsourceWellFormed
          have hargumentsClosed :
              ∀ argument ∈ arguments,
                argument.ReferenceClosed := by
            intro argument hargument
            obtain ⟨child, hchild, rfl⟩ :=
              List.mem_map.mp hargument
            exact RegularTerm.withRoot_referenceClosed
              hsourceClosed
              (hsourceClosed.2 source.root X children
                hsourceRootNode child hchild)
          have hrhsClosed :=
            RegularTerm.referenceClosed_of_wellFormed
              hrhsChildren
          cases hrhsRoot : rhs.rootNode? with
          | none =>
              have := hrhsClosed.1
              unfold RegularTerm.rootNode?
                RegularTerm.nodeAt? at hrhsRoot
              rw [List.getElem?_eq_none_iff] at hrhsRoot
              omega
          | some node =>
              cases node with
              | inl x =>
                  have hvariableNode :
                      rhs.nodeAt? rhs.root = some (.inl x) := by
                    simpa [RegularTerm.rootNode?] using hrhsRoot
                  have hxChildren : x < children.length := by
                    exact RegularTerm.variable_lt_of_wellFormed
                      hrhsChildren hvariableNode
                  have hxArguments : x < arguments.length := by
                    simpa [arguments] using hxChildren
                  let child := children[x]
                  let argument := arguments[x]
                  have hargumentGet :
                      arguments[x]? = some argument :=
                    List.getElem?_eq_getElem hxArguments
                  have hargumentEq :
                      argument = source.withRoot child := by
                    simp [argument, child, arguments]
                  have hinstance :
                      (rhs.instantiate arguments)
                        |>.UnfoldingEquivalent argument :=
                    RegularTerm.instantiate_unfoldingEquivalent_argument
                      hvariableNode hargumentGet
                      (hargumentsClosed argument
                        (List.mem_of_getElem? hargumentGet))
                  exfalso
                  apply hnotSinks
                  refine ⟨[.inl action], [], by simp, by simp, ?_⟩
                  refine ⟨source.withRoot child,
                    rhs.instantiate arguments, ?_, ?_, ?_⟩
                  · exact ⟨child,
                      .child .root hsourceRootNode
                        (List.getElem_mem hxChildren),
                      rfl⟩
                  · simpa using hstepOriginal
                  · simpa [hargumentEq] using hinstance
              | inr application =>
                  rcases application with ⟨Y, rhsChildren⟩
                  have hrhsApplication :
                      rhs.rootApplication? =
                        some (Y, rhsChildren) := by
                    simp [RegularTerm.rootApplication?, hrhsRoot]
                  have htargetRoot :=
                    RegularTerm.instantiate_rootApplication?
                      (arguments := arguments)
                      hrhsClosed hrhsApplication
                  refine ⟨Y,
                    rhsChildren.map (rhs.resolveRHSRef arguments),
                    htargetRoot, ?_⟩
                  intro resolvedChild hresolvedChild
                  obtain ⟨rhsChild, hrhsChild, rfl⟩ :=
                    List.mem_map.mp hresolvedChild
                  rw [RegularTerm.instantiate_withRoot]
                  apply RegularTerm.instantiate_applicationDepth
                    (ranks := g.ranks)
                  · have hrhsChildLt :=
                      hrhsClosed.2 rhs.root Y rhsChildren
                      (by simpa [RegularTerm.rootNode?] using
                        hrhsRoot)
                      rhsChild hrhsChild
                    simpa [arguments] using
                      (RegularTerm.withRoot_wellFormed_of_lt
                        hrhsChildren hrhsChildLt)
                  · exact hargumentsDepth
                  · exact hargumentsClosed

/-- Every executed one-letter step of `word` is locally non-sinking at the
symbolic residual reached immediately before it. -/
@[expose] public def NoLocalSinkingAlong
    (g : EncodedFirstOrderGrammar Action)
    (source : RegularTerm) (word : List Action) : Prop :=
  ∀ stem action suffix current,
    word = stem ++ action :: suffix →
      g.runActions? stem source = some current →
      ¬g.SinksBy current [.inl action]

/-- A locally non-sinking symbolic run preserves its initial protected
application depth, regardless of the run length. -/
public theorem runActions?_preserves_applicationDepth_of_noLocalSinking
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {source target : RegularTerm} {word : List Action} {depth : ℕ}
    (hsource : ∃ arity, source.WellFormed g.ranks arity)
    (hdepth : source.ApplicationDepth depth)
    (hrun : g.runActions? word source = some target)
    (hnoSinking : g.NoLocalSinkingAlong source word) :
    target.ApplicationDepth depth := by
  induction word generalizing source with
  | nil =>
      simp [runActions?] at hrun
      subst target
      exact hdepth
  | cons action word ih =>
      cases hstep : g.step? (.inl action) source with
      | none => simp [runActions?, hstep] at hrun
      | some next =>
          have htail :
              g.runActions? word next = some target := by
            simpa [runActions?, hstep] using hrun
          have hnotFirst : ¬g.SinksBy source [.inl action] := by
            apply hnoSinking [] action word source
            · simp
            · simp [runActions?]
          have hnextDepth :
              next.ApplicationDepth depth :=
            stepAction_preserves_applicationDepth_of_not_sinks
              hg hsource hdepth hstep hnotFirst
          have hnextWellFormed :=
            stepAction_some_wellFormed hg hsource hstep
          have hnoTail : g.NoLocalSinkingAlong next word := by
            intro stem nextAction suffix current
              hword hstemRun
            apply hnoSinking (action :: stem) nextAction
              suffix current
            · simp [hword, List.cons_append]
            · simpa [runActions?, hstep] using hstemRun
          exact ih hnextWellFormed hnextDepth htail hnoTail

/-- No prefix of the ordinary word sinks from one fixed concrete base.  The
empty prefix is harmless, and allowing an empty suffix includes the complete
word among the checked prefixes. -/
@[expose] public def NeverSinksFromBase
    (g : EncodedFirstOrderGrammar Action)
    (base : RegularTerm) (word : List Action) : Prop :=
  ∀ stem suffix,
    word = stem ++ suffix →
      ¬g.SinksBy base (stem.map Sum.inl)

/-- The operational reflection premise missing from the bare global
non-sinking statement: every local symbolic sink would be visible as a
sinking prefix from the fixed concrete base. -/
@[expose] public def LocalSinkingReflectsToBase
    (g : EncodedFirstOrderGrammar Action)
    (base schema : RegularTerm) (word : List Action) : Prop :=
  ∀ stem action suffix current,
    word = stem ++ action :: suffix →
      g.runActions? stem schema = some current →
      g.SinksBy current [.inl action] →
      g.SinksBy base ((stem ++ [action]).map Sum.inl)

/-- Global non-sinking plus local-to-base reflection yields the exact local
non-sinking invariant required by symbolic depth preservation. -/
public theorem noLocalSinkingAlong_of_neverSinksFromBase
    {g : EncodedFirstOrderGrammar Action}
    {base schema : RegularTerm} {word : List Action}
    (hnever : g.NeverSinksFromBase base word)
    (hreflects : g.LocalSinkingReflectsToBase base schema word) :
    g.NoLocalSinkingAlong schema word := by
  intro stem action suffix current hword hstemRun hsinks
  apply hnever (stem ++ [action]) suffix
  · simpa [List.append_assoc] using hword
  · exact hreflects stem action suffix current
      hword hstemRun hsinks

/-- A fixed-tail residual carrying the protected application depth inherited
from its depth-prefix source. -/
public structure ProtectedFixedTailResidual
    (g : EncodedFirstOrderGrammar Action)
    (term filler : RegularTerm) (depth : ℕ)
    (word : List Action) (target : RegularTerm) where
  fixedTail : FixedTailResidual g term filler depth word target
  applicationDepth : fixedTail.residual.ApplicationDepth depth

/-- A reflected fixed-tail residual is protected whenever its symbolic run
is locally non-sinking. -/
public theorem FixedTailResidual.applicationDepth_of_noLocalSinking
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {term filler target : RegularTerm}
    {depth : ℕ} {word : List Action}
    (hterm : term.Ground g.ranks)
    (residual : FixedTailResidual g term filler depth word target)
    (hnoSinking :
      g.NoLocalSinkingAlong
        (term.depthPrefix depth).head.toRegularTerm word) :
    residual.residual.ApplicationDepth depth := by
  let decomposition := term.depthPrefix depth
  have hschemaWellFormed :
      decomposition.head.toRegularTerm.WellFormed g.ranks
        (decomposition.schemaArity g.ranks) :=
    decomposition.head_wellFormed_schemaArity
      (RegularTerm.depthPrefix_valid term depth)
      (RegularTerm.depthPrefix_head_rankedBy hterm depth)
  apply runActions?_preserves_applicationDepth_of_noLocalSinking
    hg ⟨_, hschemaWellFormed⟩
  · exact FiniteHead.depthPrefix_schema_applicationDepth hterm depth
  · simpa [decomposition] using residual.symbolic_run
  · simpa [decomposition] using hnoSinking

/-- Concrete fixed-base non-sinking produces a protected fixed-tail residual
once the local-to-base operational reflection invariant is supplied. -/
public theorem exists_protectedFixedTailResidual_of_neverSinksFromBase
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {term filler target : RegularTerm}
    (hterm : term.Ground g.ranks)
    (hfiller : filler.Ground g.ranks)
    (depth : ℕ) {word : List Action}
    (hrun : g.runActions? word term = some target)
    (hnoExposure : g.NoDepthExposureBefore term depth word)
    (hnever : g.NeverSinksFromBase term word)
    (hreflects :
      g.LocalSinkingReflectsToBase term
        (term.depthPrefix depth).head.toRegularTerm word) :
    Nonempty
      (ProtectedFixedTailResidual
        g term filler depth word target) := by
  obtain ⟨residual⟩ :=
    exists_fixedTailResidual hg hterm hfiller
      depth hrun hnoExposure
  have hnoLocal :
      g.NoLocalSinkingAlong
        (term.depthPrefix depth).head.toRegularTerm word :=
    noLocalSinkingAlong_of_neverSinksFromBase
      hnever hreflects
  exact ⟨
    { fixedTail := residual
      applicationDepth :=
        residual.applicationDepth_of_noLocalSinking
          hg hterm hnoLocal }⟩

namespace FixedTailPivotPresentation

/-- Pointwise local non-sinking of the fixed-prefix symbolic runs protects
the full cutoff depth in every pivot schema. -/
public theorem schemas_applicationDepth_of_noLocalSinking
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {base filler : RegularTerm}
    {labels : ℕ → List (Label Action)}
    {pivots : ℕ → RegularTerm}
    (presentation :
      FixedTailPivotPresentation g base filler labels pivots)
    (hnoSinking : ∀ j,
      g.NoLocalSinkingAlong
        (base.depthPrefix presentation.depth).head.toRegularTerm
        (presentation.actions j)) :
    ∀ j, (presentation.schema j).ApplicationDepth
      presentation.depth := by
  intro j
  exact (presentation.residual j)
    |>.applicationDepth_of_noLocalSinking
      hg presentation.base_ground (hnoSinking j)

/-- Paper-shaped family form: if every concrete pivot prefix never sinks
from the fixed base and every local symbolic sink reflects to such a base
prefix, then every pivot schema protects the cutoff depth. -/
public theorem schemas_applicationDepth_of_neverSinksFromBase
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {base filler : RegularTerm}
    {labels : ℕ → List (Label Action)}
    {pivots : ℕ → RegularTerm}
    (presentation :
      FixedTailPivotPresentation g base filler labels pivots)
    (hnever : ∀ j,
      g.NeverSinksFromBase base (presentation.actions j))
    (hreflects : ∀ j,
      g.LocalSinkingReflectsToBase base
        ((base.depthPrefix presentation.depth)
          |>.head.toRegularTerm)
        (presentation.actions j)) :
    ∀ j, (presentation.schema j).ApplicationDepth
      presentation.depth := by
  apply presentation.schemas_applicationDepth_of_noLocalSinking hg
  intro j
  exact noLocalSinkingAlong_of_neverSinksFromBase
    (hnever j) (hreflects j)

end FixedTailPivotPresentation

end EncodedFirstOrderGrammar

end DCFEquivalence
