module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.CriticalMarkerPrefixAbstraction

@[expose]
public section

/-!
# Protected depth with fresh-marker boundary exceptions

The marker-aware depth prefix cuts a fresh nullary marker as soon as it is
encountered.  Its variable can therefore occur above the requested cutoff
depth.  Such a variable is nevertheless operationally harmless for an
original-action continuation: its concrete argument is a fresh marker, at
which every original action is disabled.

`GuardedApplicationDepth guard d` records exactly this hybrid invariant.
Every node above depth `d` is either an application or a variable accepted by
`guard`.  For a critical prefix, the accepted indices are precisely those
whose boundary tail has a fresh-marker root.
-/

namespace DCFEquivalence

namespace RegularTerm

/-- Every node strictly above `depth` is an application, except that a
variable satisfying `guard` may stop the prefix early. -/
@[expose] public def GuardedApplicationDepth
    (guard : ℕ → Prop) : RegularTerm → ℕ → Prop
  | _, 0 => True
  | term, depth + 1 =>
      (∃ x, term.rootNode? = some (.inl x) ∧ guard x) ∨
        ∃ X children,
          term.rootApplication? = some (X, children) ∧
            ∀ child ∈ children,
              (term.withRoot child).GuardedApplicationDepth guard depth

public theorem GuardedApplicationDepth.mono
    {guard : ℕ → Prop} {term : RegularTerm} {small large : ℕ}
    (hdepth : term.GuardedApplicationDepth guard large)
    (hle : small ≤ large) :
    term.GuardedApplicationDepth guard small := by
  induction small generalizing term large with
  | zero =>
      trivial
  | succ small ih =>
      cases large with
      | zero =>
          omega
      | succ large =>
          rcases hdepth with hvariable | happlication
          · exact Or.inl hvariable
          · obtain ⟨X, children, hroot, hchildren⟩ :=
              happlication
            exact Or.inr ⟨X, children, hroot, by
              intro child hchild
              exact ih (hchildren child hchild) (by omega)⟩

public theorem UnfoldingEquivalent.guardedApplicationDepth
    {guard : ℕ → Prop} {left right : RegularTerm}
    (hequivalent : left.UnfoldingEquivalent right)
    {depth : ℕ}
    (hleft : left.GuardedApplicationDepth guard depth) :
    right.GuardedApplicationDepth guard depth := by
  induction depth generalizing left right with
  | zero =>
      trivial
  | succ depth ih =>
      rcases hleft with hvariable | happlication
      · obtain ⟨x, hleftRoot, hx⟩ := hvariable
        exact Or.inl ⟨x,
          EncodedFirstOrderGrammar.rootNode?_variable_of_unfoldingEquivalent
            hequivalent hleftRoot,
          hx⟩
      · obtain ⟨X, leftChildren, hleftRoot, hleftChildren⟩ :=
          happlication
        obtain ⟨rightChildren, hrightRoot, hchildrenEquivalent⟩ :=
          rootApplication?_of_unfoldingEquivalent
            hequivalent hleftRoot
        refine Or.inr ⟨X, rightChildren, hrightRoot, ?_⟩
        intro rightChild hrightChild
        obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hrightChild
        have hlength := List.Forall₂.length_eq hchildrenEquivalent
        have hiRight : i < rightChildren.length :=
          (List.getElem?_eq_some_iff.mp hi).1
        have hiLeft : i < leftChildren.length := by
          omega
        let leftChild := leftChildren[i]
        have hleftChildMem : leftChild ∈ leftChildren :=
          List.getElem_mem hiLeft
        have hrightGet :
            rightChildren.get ⟨i, hiRight⟩ = rightChild := by
          exact Option.some.inj
            ((List.getElem?_eq_getElem hiRight).symm.trans hi)
        have hchildrenGet :=
          (List.forall₂_iff_get.mp hchildrenEquivalent).2
            i hiLeft hiRight
        rw [hrightGet] at hchildrenGet
        have hpointed :
            (left.withRoot leftChild).UnfoldingEquivalent
              (right.withRoot rightChild) :=
          (withRoot_unfoldingEquivalent_iff_bisimilarAt
            left right leftChild rightChild).2 hchildrenGet
        exact ih hpointed
          (hleftChildren leftChild hleftChildMem)

public theorem UnfoldingEquivalent.guardedApplicationDepth_iff
    {guard : ℕ → Prop} {left right : RegularTerm}
    (hequivalent : left.UnfoldingEquivalent right)
    (depth : ℕ) :
    left.GuardedApplicationDepth guard depth ↔
      right.GuardedApplicationDepth guard depth :=
  ⟨hequivalent.guardedApplicationDepth,
    hequivalent.symm.guardedApplicationDepth⟩

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

private theorem withRoot_wellFormed
    {ranks : List ℕ} {arity : ℕ} {term : RegularTerm}
    (hterm : term.WellFormed ranks arity)
    {i : ℕ} (hi : i < term.nodes.length) :
    (term.withRoot i).WellFormed ranks arity := by
  unfold WellFormed wellFormedCode at hterm ⊢
  rw [Bool.and_eq_true] at hterm ⊢
  exact ⟨by simpa [withRoot, root, nodes] using decide_eq_true hi,
    by simpa [withRoot, nodes] using hterm.2⟩

/-- Substitution by guarded schemas preserves guarded depth. -/
public theorem instantiate_guardedApplicationDepth
    {ranks : List ℕ} {schema : RegularTerm}
    {arguments : List RegularTerm} {guard : ℕ → Prop} {depth : ℕ}
    (hschema : schema.WellFormed ranks arguments.length)
    (harguments : ∀ argument ∈ arguments,
      argument.GuardedApplicationDepth guard depth)
    (hargumentsClosed : ∀ argument ∈ arguments,
      argument.ReferenceClosed) :
    (schema.instantiate arguments).GuardedApplicationDepth guard depth := by
  induction depth generalizing schema with
  | zero =>
      trivial
  | succ depth ih =>
      have hschemaClosed := referenceClosed_of_wellFormed hschema
      cases hroot : schema.rootNode? with
      | none =>
          have hrootLt := hschemaClosed.1
          unfold rootNode? nodeAt? at hroot
          rw [List.getElem?_eq_none_iff] at hroot
          omega
      | some node =>
          cases node with
          | inl x =>
              have hx : x < arguments.length :=
                variable_lt_of_wellFormed hschema
                  (by simpa [rootNode?] using hroot)
              let argument := arguments[x]
              have hargument : arguments[x]? = some argument :=
                List.getElem?_eq_getElem hx
              have hinstance :=
                instantiate_unfoldingEquivalent_argument
                  (by simpa [rootNode?] using hroot)
                  hargument
                  (hargumentsClosed argument
                    (List.mem_of_getElem? hargument))
              exact hinstance.symm.guardedApplicationDepth
                (harguments argument
                  (List.mem_of_getElem? hargument))
          | inr application =>
              rcases application with ⟨X, children⟩
              have hrootApplication :
                  schema.rootApplication? = some (X, children) := by
                simp [rootApplication?, hroot]
              have hinstRoot := instantiate_rootApplication?
                (arguments := arguments) hschemaClosed
                hrootApplication
              refine Or.inr ⟨X,
                children.map (schema.resolveRHSRef arguments),
                hinstRoot, ?_⟩
              intro resolvedChild hresolvedChild
              obtain ⟨child, hchild, rfl⟩ :=
                List.mem_map.mp hresolvedChild
              rw [instantiate_withRoot]
              apply ih
              · exact withRoot_wellFormed hschema
                  (hschemaClosed.2 schema.root X children
                    (by simpa [rootNode?] using hroot)
                    child hchild)
              · intro argument hargument
                exact (harguments argument hargument).mono
                  (Nat.le_succ depth)

/-- A reachable-prefix witness is enough to transfer guarded depth through
instantiation; unreachable graph garbage and its variables are irrelevant. -/
public theorem HasPrefixWitness.instantiate_guardedApplicationDepth
    {schema : RegularTerm} {arguments : List RegularTerm}
    {guard : ℕ → Prop} {width depth : ℕ}
    (hwitness : schema.HasPrefixWitness width)
    (hclosed : schema.ReferenceClosed)
    (hwidth : width ≤ arguments.length)
    (hargumentsDepth : ∀ argument ∈ arguments,
      argument.GuardedApplicationDepth guard depth)
    (hargumentsClosed : ∀ argument ∈ arguments,
      argument.ReferenceClosed) :
    (schema.instantiate arguments).GuardedApplicationDepth guard depth := by
  induction depth generalizing schema width with
  | zero =>
      trivial
  | succ depth ih =>
      obtain ⟨support, hsupport⟩ := hwitness
      rcases hsupport.2 schema.root hsupport.1 with
        hvariable | happlication
      · obtain ⟨x, hnode, hx⟩ := hvariable
        have hxArguments : x < arguments.length :=
          hx.trans_le hwidth
        let argument := arguments[x]
        have hargument : arguments[x]? = some argument :=
          List.getElem?_eq_getElem hxArguments
        have hinstance :
            (schema.instantiate arguments).UnfoldingEquivalent
              argument :=
          instantiate_unfoldingEquivalent_argument
            hnode hargument
            (hargumentsClosed argument
              (List.mem_of_getElem? hargument))
        exact hinstance.symm.guardedApplicationDepth
          (hargumentsDepth argument
            (List.mem_of_getElem? hargument))
      · obtain ⟨X, children, hnode, hchildren⟩ :=
          happlication
        have hroot :
            schema.rootApplication? = some (X, children) := by
          unfold rootApplication? rootNode?
          rw [hnode]
        have hinstanceRoot :=
          instantiate_rootApplication?
            (arguments := arguments) hclosed hroot
        refine Or.inr ⟨X,
          children.map (schema.resolveRHSRef arguments),
          hinstanceRoot, ?_⟩
        intro resolvedChild hresolvedChild
        obtain ⟨child, hchild, rfl⟩ :=
          List.mem_map.mp hresolvedChild
        have hchildBound :=
          hclosed.2 schema.root X children hnode child hchild
        have hchildWitness :
            (schema.withRoot child).HasPrefixWitness width := by
          refine ⟨support, ?_⟩
          constructor
          · exact hchildren child hchild
          · intro i hi
            simpa [withRoot, nodeAt?, nodes] using
              hsupport.2 i hi
        rw [instantiate_withRoot]
        apply ih hchildWitness
          (withRoot_referenceClosed hclosed hchildBound)
          hwidth
        intro argument hargument
        exact (hargumentsDepth argument hargument).mono
          (Nat.le_succ depth)

/-- An application-rooted witnessed schema contributes one protected layer
above guarded arguments. -/
public theorem HasPrefixWitness.instantiate_guardedApplicationDepth_succ
    {schema : RegularTerm} {arguments : List RegularTerm}
    {guard : ℕ → Prop} {width depth : ℕ}
    (hwitness : schema.HasPrefixWitness width)
    (hclosed : schema.ReferenceClosed)
    (hwidth : width ≤ arguments.length)
    {X : ℕ} {children : List ℕ}
    (hroot : schema.rootApplication? = some (X, children))
    (hargumentsDepth : ∀ argument ∈ arguments,
      argument.GuardedApplicationDepth guard depth)
    (hargumentsClosed : ∀ argument ∈ arguments,
      argument.ReferenceClosed) :
    (schema.instantiate arguments)
      |>.GuardedApplicationDepth guard (depth + 1) := by
  have hrootNode := nodeAt?_root_of_rootApplication? hroot
  have hinstanceRoot :=
    instantiate_rootApplication?
      (arguments := arguments) hclosed hroot
  refine Or.inr ⟨X,
    children.map (schema.resolveRHSRef arguments),
    hinstanceRoot, ?_⟩
  obtain ⟨support, hsupport⟩ := hwitness
  intro resolvedChild hresolvedChild
  obtain ⟨child, hchild, rfl⟩ :=
    List.mem_map.mp hresolvedChild
  have hchildMem : child ∈ support := by
    rcases hsupport.2 schema.root hsupport.1 with
      hvariable | happlication
    · obtain ⟨x, hnode, _hx⟩ := hvariable
      rw [hrootNode] at hnode
      simp at hnode
    · obtain ⟨Y, witnessChildren, hnode,
          hwitnessChildren⟩ := happlication
      rw [hrootNode] at hnode
      simp only [Option.some.injEq, Sum.inr.injEq,
        Prod.mk.injEq] at hnode
      rcases hnode with ⟨rfl, rfl⟩
      exact hwitnessChildren child hchild
  have hchildBound :=
    hclosed.2 schema.root X children hrootNode child hchild
  have hchildWitness :
      (schema.withRoot child).HasPrefixWitness width := by
    refine ⟨support, ?_⟩
    constructor
    · exact hchildMem
    · intro i hi
      simpa [withRoot, nodeAt?, nodes] using
        hsupport.2 i hi
  rw [instantiate_withRoot]
  exact hchildWitness.instantiate_guardedApplicationDepth
    (withRoot_referenceClosed hclosed hchildBound)
    hwidth hargumentsDepth hargumentsClosed

end RegularTerm

namespace FiniteHead

/-- Finite-head form of guarded application depth. -/
@[expose] public def GuardedDepth
    (guard : ℕ → Prop) : FiniteHead → ℕ → Prop
  | _, 0 => True
  | .var x, _ + 1 => guard x
  | .app _ children, depth + 1 =>
      ∀ child ∈ children, child.GuardedDepth guard depth

public theorem GuardedDepth.mono
    {guard : ℕ → Prop} {head : FiniteHead} {small large : ℕ}
    (hdepth : head.GuardedDepth guard large)
    (hle : small ≤ large) :
    head.GuardedDepth guard small := by
  induction small generalizing head large with
  | zero =>
      trivial
  | succ small ih =>
      cases large with
      | zero =>
          omega
      | succ large =>
          cases head with
          | var x =>
              exact hdepth
          | app X children =>
              intro child hchild
              exact ih (hdepth child hchild) (by omega)

/-- Extending a rank table preserves finite-head ranking. -/
public theorem RankedBy.appendRanks
    {head : FiniteHead} {ranks extra : List ℕ}
    (hranked : head.RankedBy ranks) :
    head.RankedBy (ranks ++ extra) := by
  induction head using FiniteHead.rec
    (motive_2 := fun heads =>
      (∀ head ∈ heads, head.RankedBy ranks) →
        ∀ head ∈ heads, head.RankedBy (ranks ++ extra)) with
  | var x =>
      simp [RankedBy]
  | app X children ih =>
      simp only [RankedBy] at hranked ⊢
      have hX : X < ranks.length :=
        (List.getElem?_eq_some_iff.mp hranked.1).1
      constructor
      · rw [List.getElem?_append_left hX]
        exact hranked.1
      · exact ih hranked.2
  | nil =>
      aesop
  | cons head heads ihHead ihHeads =>
      aesop

public theorem GuardedDepth.shiftVariables
    {guard guard' : ℕ → Prop} {head : FiniteHead}
    {depth offset : ℕ}
    (hguard : ∀ x, guard x → guard' (offset + x))
    (hdepth : head.GuardedDepth guard depth) :
    (head.shiftVariables offset).GuardedDepth guard' depth := by
  induction depth generalizing head with
  | zero =>
      trivial
  | succ depth ih =>
      cases head with
      | var x =>
          simpa [FiniteHead.shiftVariables, GuardedDepth] using
            hguard x hdepth
      | app X children =>
          simp only [FiniteHead.shiftVariables, GuardedDepth]
          intro shiftedChild hshiftedChild
          obtain ⟨child, hchild, rfl⟩ :=
            List.mem_map.mp hshiftedChild
          apply ih (hdepth child hchild)

/-- Compiling a guarded finite head preserves guarded application depth. -/
public theorem toRegularTerm_guardedApplicationDepth
    {guard : ℕ → Prop} {head : FiniteHead} {depth : ℕ}
    (hdepth : head.GuardedDepth guard depth) :
    head.toRegularTerm.GuardedApplicationDepth guard depth := by
  induction depth generalizing head with
  | zero =>
      trivial
  | succ depth ih =>
      cases head with
      | var x =>
          exact Or.inl ⟨x, by
            simpa [toRegularTerm] using
              RegularTerm.variableTerm_rootNode? x,
            hdepth⟩
      | app X children =>
          rw [toRegularTerm]
          have hroot :=
            RegularTerm.instantiate_rootApplication?
              (arguments := children.map toRegularTerm)
              (RegularTerm.symbolTemplate_referenceClosed
                X children.length)
              (RegularTerm.symbolTemplate_rootApplication?
                X children.length)
          refine Or.inr ⟨X, _,
            by simpa using hroot, ?_⟩
          intro resolvedChild hresolvedChild
          obtain ⟨i, hi, rfl⟩ :=
            List.mem_map.mp hresolvedChild
          have hiChildren : i < children.length := by
            simpa using hi
          let child := children[i]
          have hargument :
              (children.map toRegularTerm)[i]? =
                some child.toRegularTerm := by
            simp [child, hiChildren]
          have hvariable :
              ((RegularTerm.symbolTemplate X children.length)
                |>.withRoot (i + 1)).nodeAt?
                  ((RegularTerm.symbolTemplate X children.length)
                    |>.withRoot (i + 1)).root =
                some (.inl i) := by
            simpa using
              RegularTerm.symbolTemplate_variableNode
                X children.length i hiChildren
          have hinstance :
              (((RegularTerm.symbolTemplate X children.length)
                |>.withRoot (i + 1)).instantiate
                  (children.map toRegularTerm))
                |>.UnfoldingEquivalent child.toRegularTerm :=
            RegularTerm.instantiate_unfoldingEquivalent_argument
              hvariable hargument
              (toRegularTerm_referenceClosed child)
          change (((RegularTerm.symbolTemplate X children.length)
            |>.instantiate (children.map toRegularTerm)).withRoot
              ((RegularTerm.symbolTemplate X children.length)
                |>.resolveRHSRef
                  (children.map toRegularTerm) (i + 1)))
            |>.GuardedApplicationDepth guard depth
          rw [RegularTerm.instantiate_withRoot]
          exact hinstance.symm.guardedApplicationDepth
            (ih (hdepth child (List.getElem_mem hiChildren)))

end FiniteHead

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

private theorem HasPrefixWitness.runActions_of_someWellFormed
    {A : Type} [DecidableEq A]
    {grammar : EncodedFirstOrderGrammar A}
    (hgrammar : grammar.WellFormed)
    {schema residual : RegularTerm} {width : ℕ}
    (hwitness : schema.HasPrefixWitness width)
    (hschema : ∃ arity, schema.WellFormed grammar.ranks arity)
    {word : List A}
    (hrun : grammar.runActions? word schema = some residual) :
    residual.HasPrefixWitness width := by
  induction word generalizing schema with
  | nil =>
      simp [runActions?] at hrun
      subst residual
      exact hwitness
  | cons action word ih =>
      cases hstep : grammar.step? (.inl action) schema with
      | none =>
          simp [runActions?, hstep] at hrun
      | some next =>
          have htail :
              grammar.runActions? word next = some residual := by
            simpa [runActions?, hstep] using hrun
          have hnextWitness :=
            hwitness.stepAction hgrammar
              (Classical.choose_spec hschema) hstep
          exact ih hnextWitness
            (stepAction_some_wellFormed hgrammar hschema hstep)
            htail

/-- A critical-prefix variable is guarded when its genuine boundary tail has
a fresh marker at the root. -/
@[expose] public def CriticalBoundaryGuard
    (g : EncodedFirstOrderGrammar Action) (count : ℕ)
    (decomposition : DepthPrefix) (x : ℕ) : Prop :=
  ∃ tail,
    decomposition.tails[x]? = some tail ∧
      g.FreshCriticalMarkerRoot count tail

private theorem getElem?_append_offset
    {A : Type} (leading middle trailing : List A)
    {x : ℕ} {value : A}
    (hget : middle[x]? = some value) :
    (leading ++ middle ++ trailing)[leading.length + x]? =
      some value := by
  have hx : x < middle.length :=
    (List.getElem?_eq_some_iff.mp hget).1
  rw [List.getElem?_append_left (by simp; omega)]
  rw [List.getElem?_append_right (by omega)]
  simpa using hget

private theorem collectHeads_guardedDepth
    (g : EncodedFirstOrderGrammar Action) (count : ℕ)
    (children : List DepthPrefix) (leading : List RegularTerm)
    (depth : ℕ)
    (hchildren : ∀ child ∈ children,
      child.head.GuardedDepth
        (g.CriticalBoundaryGuard count child) depth) :
    ∀ head ∈ DepthPrefix.collectHeads children leading.length,
      head.GuardedDepth
        (g.CriticalBoundaryGuard count
          { head := .var 0
            tails := leading ++ DepthPrefix.collectTails children })
        depth := by
  induction children generalizing leading with
  | nil =>
      simp [DepthPrefix.collectHeads]
  | cons child children ih =>
      intro head hhead
      simp only [DepthPrefix.collectHeads, List.mem_cons] at hhead
      rcases hhead with rfl | hhead
      · apply (hchildren child (by simp)).shiftVariables
        intro x hx
        obtain ⟨tail, htail, hfresh⟩ := hx
        refine ⟨tail, ?_, hfresh⟩
        simpa [CriticalBoundaryGuard, DepthPrefix.collectTails,
          List.append_assoc] using
          getElem?_append_offset leading child.tails
            (DepthPrefix.collectTails children) htail
      · have htailResult :=
          ih (leading ++ child.tails)
            (fun item hitem =>
              hchildren item (by simp [hitem]))
            head (by
              simpa [List.length_append, Nat.add_comm,
                Nat.add_left_comm, Nat.add_assoc] using hhead)
        simpa [CriticalBoundaryGuard, DepthPrefix.collectTails,
          List.append_assoc] using htailResult

/-- The marker-aware finite head protects the requested depth except at
variables whose own boundary tail is a fresh marker. -/
public theorem criticalDepthPrefix_head_guardedDepth
    {g : EncodedFirstOrderGrammar Action} {count : ℕ}
    {term : RegularTerm}
    (hground : term.Ground (g.withCriticalMarkers count).ranks)
    (depth : ℕ) :
    (g.criticalDepthPrefix depth term).head.GuardedDepth
      (g.CriticalBoundaryGuard count
        (g.criticalDepthPrefix depth term))
      depth := by
  induction depth generalizing term with
  | zero =>
      trivial
  | succ depth ih =>
      obtain ⟨symbol, children, hroot⟩ :=
        hground.exists_rootApplication
      by_cases hsymbol : symbol < g.ranks.length
      · rw [g.criticalDepthPrefix_succ_of_originalRoot
          hroot hsymbol]
        unfold DepthPrefix.assemble
        simp only [FiniteHead.GuardedDepth]
        have hrootNode :=
          RegularTerm.nodeAt?_root_of_rootApplication? hroot
        apply collectHeads_guardedDepth g count
          (children.map fun child =>
            g.criticalDepthPrefix depth (term.withRoot child))
          [] depth
        intro childPrefix hchildPrefix
        obtain ⟨child, hchild, rfl⟩ :=
          List.mem_map.mp hchildPrefix
        exact ih
          (hground.withRoot_descendant
            (.child .root hrootNode hchild))
      · rw [g.criticalDepthPrefix_succ_of_freshRoot
          hroot hsymbol]
        simp only [FiniteHead.GuardedDepth]
        refine ⟨term, by simp, ?_⟩
        exact g.freshCriticalMarkerRoot_of_ground_root_not_original
          hground hroot hsymbol

/-- The compiled critical prefix has the same guarded depth invariant. -/
public theorem criticalDepthPrefix_schema_guardedApplicationDepth
    {g : EncodedFirstOrderGrammar Action} {count : ℕ}
    {term : RegularTerm}
    (hground : term.Ground (g.withCriticalMarkers count).ranks)
    (depth : ℕ) :
    (g.criticalDepthPrefix depth term).head.toRegularTerm
      |>.GuardedApplicationDepth
        (g.CriticalBoundaryGuard count
          (g.criticalDepthPrefix depth term))
        depth :=
  FiniteHead.toRegularTerm_guardedApplicationDepth
    (g.criticalDepthPrefix_head_guardedDepth hground depth)

/-- Fixed-base non-sinking preserves the full guarded depth of a
marker-aware prefix residual, independently of the length of the rebased
word. -/
public theorem
    criticalDepthPrefix_residual_guardedApplicationDepth_of_neverSinksFromBase
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {count : ℕ} {base residual : RegularTerm}
    (hbase : base.Ground (g.withCriticalMarkers count).ranks)
    (depth : ℕ) {word : List (Action ⊕ ℕ)}
    (hrun :
      (g.withCriticalMarkers count).runActions? word
        (g.criticalDepthPrefix depth base).head.toRegularTerm =
          some residual)
    (hnever :
      (g.withCriticalMarkers count).NeverSinksFromBase base word) :
    residual.GuardedApplicationDepth
      (g.CriticalBoundaryGuard count
        (g.criticalDepthPrefix depth base))
      depth := by
  let extended := g.withCriticalMarkers count
  have hgExtended : extended.WellFormed :=
    g.withCriticalMarkers_wellFormed hg count
  cases depth with
  | zero =>
      trivial
  | succ depth =>
      obtain ⟨X, children, hroot⟩ :=
        hbase.exists_rootApplication
      by_cases hX : X < g.ranks.length
      · let childPrefixes :=
          children.map fun child =>
            g.criticalDepthPrefix depth (base.withRoot child)
        let heads := DepthPrefix.collectHeads childPrefixes 0
        let arguments := heads.map FiniteHead.toRegularTerm
        let outer := RegularTerm.symbolTemplate X children.length
        have hrootNode :=
          RegularTerm.nodeAt?_root_of_rootApplication? hroot
        have hchildrenGround :
            ∀ child ∈ children,
              (base.withRoot child).Ground extended.ranks := by
          intro child hchild
          exact hbase.withRoot_descendant
            (.child .root hrootNode hchild)
        have hheadsDepth :
            ∀ head ∈ heads,
              head.GuardedDepth
                (g.CriticalBoundaryGuard count
                  (g.criticalDepthPrefix (depth + 1) base))
                depth := by
          intro head hhead
          have hcollected :=
            collectHeads_guardedDepth g count childPrefixes []
              depth
              (by
                intro childPrefix hchildPrefix
                obtain ⟨child, hchild, rfl⟩ :=
                  List.mem_map.mp hchildPrefix
                exact g.criticalDepthPrefix_head_guardedDepth
                  (hchildrenGround child hchild) depth)
              head (by simpa [heads] using hhead)
          simpa [CriticalBoundaryGuard,
            childPrefixes,
            g.criticalDepthPrefix_succ_of_originalRoot
              hroot hX,
            DepthPrefix.assemble_tails] using hcollected
        have hargumentsDepth :
            ∀ argument ∈ arguments,
              argument.GuardedApplicationDepth
                (g.CriticalBoundaryGuard count
                  (g.criticalDepthPrefix (depth + 1) base))
                depth := by
          intro argument hargument
          obtain ⟨head, hhead, rfl⟩ :=
            List.mem_map.mp hargument
          exact FiniteHead.toRegularTerm_guardedApplicationDepth
            (hheadsDepth head hhead)
        have hargumentsClosed :
            ∀ argument ∈ arguments,
              argument.ReferenceClosed := by
          intro argument hargument
          obtain ⟨head, _hhead, rfl⟩ :=
            List.mem_map.mp hargument
          exact FiniteHead.toRegularTerm_referenceClosed head
        have hargumentsLength :
            arguments.length = children.length := by
          simp [arguments, heads, childPrefixes]
        have hrank :
            extended.ranks[X]? = some children.length :=
          hbase.root_rank_arity hroot
        have houterWellFormed :
            outer.WellFormed extended.ranks arguments.length := by
          rw [hargumentsLength]
          simpa [outer] using
            RegularTerm.symbolTemplate_wellFormed hrank
        have houterWitness :
            outer.HasPrefixWitness arguments.length := by
          rw [hargumentsLength]
          simpa [outer] using
            RegularTerm.symbolTemplate_hasPrefixWitness
              X children.length
        have hsymbolicRun :
            extended.runActions? word
              (outer.instantiate arguments) =
                some residual := by
          rw [g.criticalDepthPrefix_succ_of_originalRoot
            hroot hX] at hrun
          simpa [DepthPrefix.assemble, childPrefixes, heads,
            arguments, outer, FiniteHead.toRegularTerm] using hrun
        have hnoVariable :
            extended.NoVariableAlong outer word := by
          simpa [outer] using
            symbolTemplate_noVariableAlong_of_neverSinksFromBase
              hgExtended hbase hroot hnever
        obtain ⟨outerResidual, houterRun, houterInstance⟩ :=
          runActions?_reflects_instantiation_of_noVariableBefore
            hgExtended word ⟨_, houterWellFormed⟩
            hargumentsClosed hsymbolicRun
            hnoVariable.noVariableBefore
        have houterResidualWitness :=
          HasPrefixWitness.runActions_of_someWellFormed
            hgExtended houterWitness
            ⟨_, houterWellFormed⟩ houterRun
        have houterResidualClosed :
            outerResidual.ReferenceClosed :=
          extended.runActions?_preserves_referenceClosed
            hgExtended word
            (RegularTerm.referenceClosed_of_wellFormed
              houterWellFormed)
            houterRun
        have houterResidualRoot :
            ∃ Y outerChildren,
              outerResidual.rootApplication? =
                some (Y, outerChildren) := by
          obtain ⟨support, hsupport⟩ := houterResidualWitness
          rcases hsupport.2 outerResidual.root hsupport.1 with
            hvariable | happlication
          · obtain ⟨x, hnode, _hx⟩ := hvariable
            have hrootVariable :
                outerResidual.rootNode? = some (.inl x) := by
              simpa [RegularTerm.rootNode?] using hnode
            have hequivalent :=
              unfoldingEquivalent_variableTerm_of_rootNode?
                hrootVariable
            exact False.elim
              ((hnoVariable word [] (by simp)
                outerResidual x houterRun) hequivalent)
          · obtain ⟨Y, outerChildren, hnode, _hchildren⟩ :=
              happlication
            exact ⟨Y, outerChildren, by
              unfold RegularTerm.rootApplication?
                RegularTerm.rootNode?
              rw [hnode]⟩
        obtain ⟨Y, outerChildren, houterRoot⟩ :=
          houterResidualRoot
        have houterDepth :
            (outerResidual.instantiate arguments)
              |>.GuardedApplicationDepth
                (g.CriticalBoundaryGuard count
                  (g.criticalDepthPrefix (depth + 1) base))
                (depth + 1) :=
          houterResidualWitness
            |>.instantiate_guardedApplicationDepth_succ
              houterResidualClosed (by omega) houterRoot
              hargumentsDepth hargumentsClosed
        exact houterInstance.guardedApplicationDepth houterDepth
      · rw [g.criticalDepthPrefix_succ_of_freshRoot
          hroot hX] at hrun ⊢
        cases word with
        | nil =>
            simp [runActions?] at hrun
            subst residual
            exact Or.inl ⟨0, by
              simp [FiniteHead.toRegularTerm,
                RegularTerm.variableTerm_rootNode?], by
              refine ⟨base, by simp, ?_⟩
              exact
                g.freshCriticalMarkerRoot_of_ground_root_not_original
                  hbase hroot hX⟩
        | cons action word =>
            have hstep :
                extended.step? (.inl action)
                  (RegularTerm.variableTerm 0) = none := by
              change extended.rootRewrite? action
                (RegularTerm.variableTerm 0) = none
              simp [rootRewrite?, RegularTerm.rootApplication?,
                RegularTerm.rootNode?, RegularTerm.variableTerm,
                RegularTerm.nodeAt?, RegularTerm.nodes,
                RegularTerm.root]
            have hstep' :
                (g.withCriticalMarkers count).step? (.inl action)
                  (RegularTerm.variableTerm 0) = none := by
              simpa [extended] using hstep
            have hrun' :
                (g.withCriticalMarkers count).runActions?
                  (action :: word) (RegularTerm.variableTerm 0) =
                    some residual := by
              simpa [FiniteHead.toRegularTerm] using hrun
            simp [runActions?, hstep'] at hrun'

/-- One successful ordinary rewrite consumes at most one guarded layer. -/
public theorem stepAction_preserves_guardedApplicationDepth
    {A : Type} [DecidableEq A]
    {grammar : EncodedFirstOrderGrammar A}
    (hgrammar : grammar.WellFormed)
    {source target : RegularTerm} {action : A}
    {guard : ℕ → Prop} {depth : ℕ}
    (hsourceWellFormed :
      ∃ arity, source.WellFormed grammar.ranks arity)
    (hdepth :
      source.GuardedApplicationDepth guard (depth + 1))
    (hstep : grammar.step? (.inl action) source = some target) :
    target.GuardedApplicationDepth guard depth := by
  rcases hdepth with hvariable | happlication
  · obtain ⟨x, hroot, _hx⟩ := hvariable
    have hrootApplication : source.rootApplication? = none := by
      unfold RegularTerm.rootApplication?
      rw [hroot]
    change grammar.rootRewrite? action source = some target at hstep
    unfold rootRewrite? at hstep
    rw [hrootApplication] at hstep
    contradiction
  · obtain ⟨X, children, hroot, hchildrenDepth⟩ :=
      happlication
    obtain ⟨sourceArity, hsourceWellFormed⟩ :=
      hsourceWellFormed
    change grammar.rootRewrite? action source = some target at hstep
    unfold rootRewrite? at hstep
    rw [hroot] at hstep
    obtain ⟨rhs, hrule, rfl⟩ :=
      Option.map_eq_some_iff.mp hstep
    obtain ⟨rank, hrank, hrhsWellFormed⟩ :=
      selected_rhs_wellFormed hgrammar hrule
    have hrootNode :=
      RegularTerm.nodeAt?_root_of_rootApplication? hroot
    have hsourceNodeWellFormed := hsourceWellFormed
    unfold RegularTerm.WellFormed
      RegularTerm.wellFormedCode at hsourceNodeWellFormed
    rw [Bool.and_eq_true] at hsourceNodeWellFormed
    have hrootMem :
        (.inr (X, children) : RawNode) ∈ source.nodes :=
      List.mem_of_getElem? hrootNode
    have hrootWell :=
      (List.all_eq_true.mp hsourceNodeWellFormed.2) _ hrootMem
    unfold RegularTerm.nodeWellFormedCode at hrootWell
    cases hsourceRank : grammar.ranks[X]? with
    | none =>
        simp [hsourceRank] at hrootWell
    | some sourceRank =>
        simp only [hsourceRank, Bool.and_eq_true,
          decide_eq_true_eq] at hrootWell
        have hrankEq : rank = sourceRank :=
          Option.some.inj (hrank.symm.trans hsourceRank)
        have hrhsChildren :
            rhs.WellFormed grammar.ranks children.length := by
          rw [hrootWell.1, ← hrankEq]
          exact hrhsWellFormed
        apply RegularTerm.instantiate_guardedApplicationDepth
          (arguments := children.map source.withRoot)
          (by simpa using hrhsChildren)
        · intro argument hargument
          obtain ⟨child, hchild, rfl⟩ :=
            List.mem_map.mp hargument
          exact hchildrenDepth child hchild
        · intro argument hargument
          obtain ⟨child, hchild, rfl⟩ :=
            List.mem_map.mp hargument
          exact RegularTerm.withRoot_referenceClosed
            (RegularTerm.referenceClosed_of_wellFormed
              hsourceWellFormed)
            ((RegularTerm.referenceClosed_of_wellFormed
              hsourceWellFormed).2 source.root X children
                hrootNode child hchild)

/-- A finite ordinary run consumes at most its length from guarded depth. -/
public theorem runActions?_preserves_guardedApplicationDepth
    {A : Type} [DecidableEq A]
    {grammar : EncodedFirstOrderGrammar A}
    (hgrammar : grammar.WellFormed)
    {source target : RegularTerm} {word : List A}
    {guard : ℕ → Prop} {depth : ℕ}
    (hsource : ∃ arity,
      source.WellFormed grammar.ranks arity)
    (hdepth :
      source.GuardedApplicationDepth guard
        (word.length + depth))
    (hrun : grammar.runActions? word source = some target) :
    target.GuardedApplicationDepth guard depth := by
  induction word generalizing source with
  | nil =>
      simp [runActions?] at hrun
      subst target
      simpa using hdepth
  | cons action word ih =>
      cases hstep : grammar.step? (.inl action) source with
      | none =>
          simp [runActions?, hstep] at hrun
      | some next =>
          have htail :
              grammar.runActions? word next = some target := by
            simpa [runActions?, hstep] using hrun
          have hnextDepth :
              next.GuardedApplicationDepth guard
                (word.length + depth) := by
            apply stepAction_preserves_guardedApplicationDepth
              hgrammar hsource
              (depth := word.length + depth)
            · simpa [Nat.add_assoc, Nat.add_comm,
                Nat.add_left_comm] using hdepth
            · exact hstep
          exact ih
            (stepAction_some_wellFormed hgrammar hsource hstep)
            hnextDepth htail

/-- At positive guarded depth, a residual equivalent to variable `x` forces
`x` to satisfy the guard. -/
public theorem RegularTerm.GuardedApplicationDepth.guard_of_variable
    {guard : ℕ → Prop} {term : RegularTerm} {x : ℕ}
    (hdepth : term.GuardedApplicationDepth guard 1)
    (hvariable :
      term.UnfoldingEquivalent (RegularTerm.variableTerm x)) :
    guard x := by
  have hroot :
      term.rootNode? = some (.inl x) :=
    rootNode?_variable_of_unfoldingEquivalent
      hvariable.symm
      (RegularTerm.variableTerm_rootNode? x)
  rcases hdepth with hguarded | happlication
  · obtain ⟨y, hy, hguard⟩ := hguarded
    have hxy : y = x := by
      exact Sum.inl.inj (Option.some.inj (hy.symm.trans hroot))
    simpa [hxy] using hguard
  · obtain ⟨Y, children, happlication, _hchildren⟩ :=
      happlication
    have happlicationRoot :
        term.rootNode? = some (.inr (Y, children)) := by
      simpa [RegularTerm.rootNode?] using
        RegularTerm.nodeAt?_root_of_rootApplication?
          happlication
    rw [hroot] at happlicationRoot
    simp at happlicationRoot

/-- Guarded depth plus concrete stuckness of every guarded argument gives
the exact no-variable premise needed for symbolic reflection of a short
continuation. -/
public theorem noVariableBefore_of_guardedApplicationDepth
    {A : Type} [DecidableEq A]
    {grammar : EncodedFirstOrderGrammar A}
    (hgrammar : grammar.WellFormed)
    {schema concrete target : RegularTerm}
    {arguments : List RegularTerm} {arity depth : ℕ}
    {guard : ℕ → Prop} {word : List A}
    (hschema : schema.WellFormed grammar.ranks arity)
    (hguarded :
      schema.GuardedApplicationDepth guard depth)
    (hlength : word.length ≤ depth)
    (hargumentsClosed : ∀ argument ∈ arguments,
      argument.ReferenceClosed)
    (hguardedArgument : ∀ x, guard x →
      ∀ stem suffix, word = stem ++ suffix → suffix ≠ [] →
        ∃ argument,
          arguments[x]? = some argument ∧
            grammar.runActions? suffix argument = none)
    (hinstance :
      (schema.instantiate arguments).UnfoldingEquivalent concrete)
    (hconcreteClosed : concrete.ReferenceClosed)
    (hrun : grammar.runActions? word concrete = some target) :
    grammar.NoVariableBefore schema word := by
  have hschemaClosed :=
    RegularTerm.referenceClosed_of_wellFormed hschema
  have hinstanceClosed :
      (schema.instantiate arguments).ReferenceClosed :=
    RegularTerm.instantiate_referenceClosed
      hschemaClosed hargumentsClosed
  intro stem suffix hword hsuffix residual x
    hstemRun hresidualVariable
  have hstemLength : stem.length + 1 ≤ depth := by
    have hsuffixPositive : 0 < suffix.length :=
      List.length_pos_iff.mpr hsuffix
    rw [hword, List.length_append] at hlength
    omega
  have hstemGuarded :
      residual.GuardedApplicationDepth guard 1 := by
    exact runActions?_preserves_guardedApplicationDepth
      hgrammar ⟨arity, hschema⟩
      (hguarded.mono hstemLength) hstemRun
  have hxGuard : guard x :=
    RegularTerm.GuardedApplicationDepth.guard_of_variable
      hstemGuarded hresidualVariable
  obtain ⟨argument, hargument, hstuck⟩ :=
    hguardedArgument x hxGuard stem suffix hword hsuffix
  have hresidualNode :
      residual.nodeAt? residual.root = some (.inl x) := by
    have hroot :
        residual.rootNode? = some (.inl x) :=
      rootNode?_variable_of_unfoldingEquivalent
        hresidualVariable.symm
        (RegularTerm.variableTerm_rootNode? x)
    simpa [RegularTerm.rootNode?] using hroot
  have hresidualInstanceArgument :
      (residual.instantiate arguments).UnfoldingEquivalent
        argument :=
    RegularTerm.instantiate_unfoldingEquivalent_argument
      hresidualNode hargument
      (hargumentsClosed argument
        (List.mem_of_getElem? hargument))
  obtain ⟨instantiatedStem, hinstantiatedStemRun,
      hresidualInstantiation⟩ :=
    grammar.runActions?_instantiate hgrammar stem hschema
      hargumentsClosed hstemRun
  obtain ⟨concreteStem, hconcreteStemRun,
      hconcreteStemEquivalent⟩ :=
    exists_runActions_of_unfoldingEquivalent hgrammar
      hinstance.symm hconcreteClosed hinstanceClosed
      hinstantiatedStemRun
  have hconcreteStemArgument :
      concreteStem.UnfoldingEquivalent argument :=
    hconcreteStemEquivalent.trans
      (hresidualInstantiation.symm.trans
        hresidualInstanceArgument)
  have hsuffixRun :
      grammar.runActions? suffix concreteStem = some target := by
    unfold runActions? at hrun hconcreteStemRun ⊢
    rw [hword, List.map_append, grammar.run?_append,
      hconcreteStemRun] at hrun
    exact hrun
  have hconcreteStemClosed :
      concreteStem.ReferenceClosed :=
    grammar.runActions?_preserves_referenceClosed
      hgrammar stem hconcreteClosed hconcreteStemRun
  obtain ⟨argumentTarget, hargumentRun, _htargetEquivalent⟩ :=
    exists_runActions_of_unfoldingEquivalent hgrammar
      hconcreteStemArgument.symm
      (hargumentsClosed argument
        (List.mem_of_getElem? hargument))
      hconcreteStemClosed hsuffixRun
  rw [hstuck] at hargumentRun
  contradiction

private theorem exists_map_inl_suffix_of_append_eq_map_inl
    {A B : Type}
    {stem suffix : List (A ⊕ B)} {original : List A}
    (hword : stem ++ suffix = original.map Sum.inl) :
    ∃ originalSuffix : List A,
      suffix = originalSuffix.map Sum.inl := by
  induction stem generalizing original with
  | nil =>
      exact ⟨original, by simpa using hword⟩
  | cons action stem ih =>
      cases original with
      | nil =>
          simp at hword
      | cons originalAction original =>
          simp only [List.cons_append, List.map_cons,
            List.cons.injEq] at hword
          obtain ⟨_haction, htail⟩ := hword
          exact ih htail

/-- A nonempty word of injected original actions is disabled at a fresh
marker root in the critical extension. -/
public theorem FreshCriticalMarkerRoot.withCriticalMarkers_runActions?_eq_none
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {count : ℕ} {term : RegularTerm}
    (hfresh : g.FreshCriticalMarkerRoot count term)
    {word : List Action} (hword : word ≠ []) :
    (g.withCriticalMarkers count).runActions?
      (word.map Sum.inl) term = none := by
  have horiginal :
      g.runActions? word term = none :=
    hfresh.runActions?_eq_none_of_ne_nil hg hword
  unfold runActions? at horiginal ⊢
  rw [← g.withCriticalMarkers_run?_lift count
    (word.map Sum.inl) term] at horiginal
  simpa [List.map_map, Function.comp_def, liftCriticalLabel] using
    horiginal

/-- A guarded residual over the marker-aware fixed tuple can reflect every
short successful continuation consisting only of injected original actions. -/
public theorem criticalNoVariableBefore_of_guardedApplicationDepth
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {count : ℕ} {base filler schema concrete target : RegularTerm}
    {depth arity : ℕ} {word : List (Action ⊕ ℕ)}
    (hbase : base.Ground (g.withCriticalMarkers count).ranks)
    (hfiller : filler.Ground (g.withCriticalMarkers count).ranks)
    (hschema :
      schema.WellFormed (g.withCriticalMarkers count).ranks arity)
    (hguarded :
      schema.GuardedApplicationDepth
        (g.CriticalBoundaryGuard count
          (g.criticalDepthPrefix depth base))
        depth)
    (hlength : word.length ≤ depth)
    (originalActions : List Action)
    (hword : word = originalActions.map Sum.inl)
    (hinstance :
      (schema.instantiate
        ((g.criticalDepthPrefix depth base)
          |>.paddedArguments g.ranks filler))
        |>.UnfoldingEquivalent concrete)
    (hconcreteClosed : concrete.ReferenceClosed)
    (hrun :
      (g.withCriticalMarkers count).runActions? word concrete =
        some target) :
    (g.withCriticalMarkers count).NoVariableBefore schema word := by
  let decomposition := g.criticalDepthPrefix depth base
  let arguments :=
    decomposition.paddedArguments g.ranks filler
  have hargumentsGround :
      ∀ argument ∈ arguments,
        argument.Ground (g.withCriticalMarkers count).ranks :=
    g.criticalDepthPrefix_paddedArguments_ground
      hbase hfiller depth
  have hargumentsClosed :
      ∀ argument ∈ arguments,
        argument.ReferenceClosed := by
    intro argument hargument
    exact RegularTerm.referenceClosed_of_ground
      (hargumentsGround argument hargument)
  apply noVariableBefore_of_guardedApplicationDepth
    (g.withCriticalMarkers_wellFormed hg count)
    hschema hguarded hlength hargumentsClosed
  · intro x hx stem suffix hsplit hsuffix
    obtain ⟨tail, htail, hfresh⟩ := hx
    have hxTails : x < decomposition.tails.length :=
      (List.getElem?_eq_some_iff.mp htail).1
    have hargument : arguments[x]? = some tail := by
      unfold arguments DepthPrefix.paddedArguments
      rw [List.getElem?_append_left hxTails]
      exact htail
    obtain ⟨originalSuffix, hsuffixOriginal⟩ :=
      exists_map_inl_suffix_of_append_eq_map_inl
        (stem := stem) (suffix := suffix)
        (original := originalActions)
        (by rw [← hword]; exact hsplit.symm)
    have horiginalSuffix : originalSuffix ≠ [] := by
      intro hnil
      subst originalSuffix
      apply hsuffix
      simpa using hsuffixOriginal
    refine ⟨tail, hargument, ?_⟩
    rw [hsuffixOriginal]
    exact hfresh.withCriticalMarkers_runActions?_eq_none
      hg horiginalSuffix
  · simpa [arguments, decomposition] using hinstance
  · exact hconcreteClosed
  · exact hrun

/-- An arbitrarily long injected-original run which never sinks from its
fixed base reflects through the marker-aware prefix.  Non-sinking preserves
the full guarded depth at every symbolic prefix; a variable residual is
therefore a fresh-marker boundary and cannot execute the nonempty suffix. -/
public theorem
    criticalDepthPrefix_noVariableBefore_of_neverSinksFromBase
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {count : ℕ} {base filler target : RegularTerm}
    (hbase : base.Ground (g.withCriticalMarkers count).ranks)
    (hfiller : filler.Ground (g.withCriticalMarkers count).ranks)
    (depth : ℕ) (hdepth : 0 < depth)
    {word : List (Action ⊕ ℕ)}
    (originalActions : List Action)
    (hword : word = originalActions.map Sum.inl)
    (hrun :
      (g.withCriticalMarkers count).runActions? word base =
        some target)
    (hnever :
      (g.withCriticalMarkers count).NeverSinksFromBase base word) :
    (g.withCriticalMarkers count).NoVariableBefore
      (g.criticalDepthPrefix depth base).head.toRegularTerm word := by
  let extended := g.withCriticalMarkers count
  let decomposition := g.criticalDepthPrefix depth base
  let schema := decomposition.head.toRegularTerm
  let arguments :=
    decomposition.paddedArguments g.ranks filler
  have hgExtended : extended.WellFormed :=
    g.withCriticalMarkers_wellFormed hg count
  have hvalid : decomposition.Valid :=
    g.criticalDepthPrefix_valid base depth
  have hrankedOriginal : decomposition.head.RankedBy g.ranks :=
    g.criticalDepthPrefix_head_rankedBy_original hbase depth
  have hrankedExtended :
      decomposition.head.RankedBy extended.ranks := by
    simpa [extended, withCriticalMarkers_ranks] using
      hrankedOriginal.appendRanks
  have hschemaSupported :
      RegularTerm.SupportedByPrefix extended.ranks
        (decomposition.schemaArity g.ranks)
        decomposition.tails.length schema := by
    have hsource :=
      FiniteHead.toRegularTerm_supportedByPrefix
        hvalid hrankedExtended
    have hrankMax :
        extended.ranks.foldr max 0 =
          g.ranks.foldr max 0 := by
      simpa [extended] using
        g.withCriticalMarkers_rankMax count
    rw [hrankMax] at hsource
    simpa [schema, DepthPrefix.schemaArity] using hsource
  have hpadding :
      extended.ranks.foldr max 0 ≤
        decomposition.schemaArity g.ranks := by
    rw [withCriticalMarkers_rankMax]
    simp [DepthPrefix.schemaArity]
  have hargumentsGround :
      ∀ argument ∈ arguments,
        argument.Ground extended.ranks :=
    g.criticalDepthPrefix_paddedArguments_ground
      hbase hfiller depth
  have hargumentsClosed :
      ∀ argument ∈ arguments,
        argument.ReferenceClosed := by
    intro argument hargument
    exact RegularTerm.referenceClosed_of_ground
      (hargumentsGround argument hargument)
  have hinstanceEquivalent :
      (schema.instantiate arguments).UnfoldingEquivalent base :=
    g.criticalDepthPrefix_compiled_unfoldingEquivalent
      hbase hfiller depth
  have hinstanceClosed :
      (schema.instantiate arguments).ReferenceClosed :=
    RegularTerm.instantiate_referenceClosed
      (RegularTerm.referenceClosed_of_wellFormed
        hschemaSupported.1)
      hargumentsClosed
  intro stem suffix hsplit hsuffix residual x
    hstemRun hresidualVariable
  have hneverStem :
      extended.NeverSinksFromBase base stem := by
    intro initialSegment remainder hstem hsinks
    apply hnever initialSegment (remainder ++ suffix)
    · calc
        word = stem ++ suffix := hsplit
        _ = (initialSegment ++ remainder) ++ suffix := by
          rw [hstem]
        _ = initialSegment ++ (remainder ++ suffix) := by
          rw [List.append_assoc]
    · exact hsinks
  have hresidualGuarded :
      residual.GuardedApplicationDepth
        (g.CriticalBoundaryGuard count decomposition) depth := by
    simpa [schema, decomposition, extended] using
      g.criticalDepthPrefix_residual_guardedApplicationDepth_of_neverSinksFromBase
        hg hbase depth hstemRun hneverStem
  have hxGuard :
      g.CriticalBoundaryGuard count decomposition x := by
    apply RegularTerm.GuardedApplicationDepth.guard_of_variable
      (hresidualGuarded.mono hdepth)
    exact hresidualVariable
  obtain ⟨tail, htail, hfresh⟩ := hxGuard
  have hxTails : x < decomposition.tails.length :=
    (List.getElem?_eq_some_iff.mp htail).1
  have hargument : arguments[x]? = some tail := by
    unfold arguments DepthPrefix.paddedArguments
    rw [List.getElem?_append_left hxTails]
    exact htail
  obtain ⟨originalSuffix, hsuffixOriginal⟩ :=
    exists_map_inl_suffix_of_append_eq_map_inl
      (stem := stem) (suffix := suffix)
      (original := originalActions)
      (by rw [← hword]; exact hsplit.symm)
  have horiginalSuffix : originalSuffix ≠ [] := by
    intro hnil
    subst originalSuffix
    apply hsuffix
    simpa using hsuffixOriginal
  have hresidualRoot :
      residual.rootNode? = some (.inl x) :=
    rootNode?_variable_of_unfoldingEquivalent
      hresidualVariable.symm
      (RegularTerm.variableTerm_rootNode? x)
  have hresidualNode :
      residual.nodeAt? residual.root = some (.inl x) := by
    simpa [RegularTerm.rootNode?] using hresidualRoot
  have hresidualInstanceTail :
      (residual.instantiate arguments).UnfoldingEquivalent tail :=
    RegularTerm.instantiate_unfoldingEquivalent_argument
      hresidualNode hargument
      (hargumentsClosed tail
        (List.mem_of_getElem? hargument))
  obtain ⟨instantiatedStem, hinstantiatedStemRun,
      hresidualInstantiation⟩ :=
    extended.runActions?_instantiate hgExtended stem
      hschemaSupported.1 hargumentsClosed hstemRun
  obtain ⟨baseStem, hbaseStemRun, hbaseStemEquivalent⟩ :=
    exists_runActions_of_unfoldingEquivalent hgExtended
      hinstanceEquivalent.symm
      (RegularTerm.referenceClosed_of_ground hbase)
      hinstanceClosed hinstantiatedStemRun
  have hbaseStemTail :
      baseStem.UnfoldingEquivalent tail :=
    hbaseStemEquivalent.trans
      (hresidualInstantiation.symm.trans
        hresidualInstanceTail)
  have hsuffixRun :
      extended.runActions? suffix baseStem = some target := by
    unfold runActions? at hrun hbaseStemRun ⊢
    rw [hsplit, List.map_append, extended.run?_append,
      hbaseStemRun] at hrun
    exact hrun
  have hbaseStemClosed :
      baseStem.ReferenceClosed :=
    extended.runActions?_preserves_referenceClosed
      hgExtended stem
      (RegularTerm.referenceClosed_of_ground hbase)
      hbaseStemRun
  have htailClosed : tail.ReferenceClosed :=
    RegularTerm.referenceClosed_of_ground
      (hargumentsGround tail
        (List.mem_of_getElem? hargument))
  obtain ⟨tailTarget, htailRun, _htargetEquivalent⟩ :=
    exists_runActions_of_unfoldingEquivalent hgExtended
      hbaseStemTail.symm htailClosed hbaseStemClosed
      hsuffixRun
  rw [hsuffixOriginal,
    hfresh.withCriticalMarkers_runActions?_eq_none
      hg horiginalSuffix] at htailRun
  contradiction

end EncodedFirstOrderGrammar

end DCFEquivalence
