module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.CriticalMarkerStructuredPivotInvariants

@[expose]
public section

/-!
# Prefix abstraction at critical markers

An ordinary fixed-depth prefix descends through fresh critical markers when
the cutoff depth is larger than the marker's occurrence depth.  That leaves a
fresh symbol in the compiled schema, so the schema is not well formed over the
original rank table.

The marker-aware prefix below stops early at every non-original application
root.  For a ground critical-marker extension such a root is necessarily one
of the fresh nullary markers.  The resulting finite head therefore uses only
original symbols, while both ordinary depth boundaries and early marker
boundaries are recorded in one fixed argument tuple.
-/

namespace DCFEquivalence

namespace DepthPrefix

/-- Renumbering collected child heads preserves ranking. -/
public theorem collectHeads_rankedBy_of_forall
    (children : List DepthPrefix) (offset : ℕ) (ranks : List ℕ)
    (hranked : ∀ child ∈ children, child.head.RankedBy ranks) :
    ∀ head ∈ collectHeads children offset,
      head.RankedBy ranks := by
  induction children generalizing offset with
  | nil =>
      simp [collectHeads]
  | cons child children ih =>
      intro head hhead
      simp only [collectHeads, List.mem_cons] at hhead
      rcases hhead with rfl | hhead
      · exact FiniteHead.rankedBy_shiftVariables
          (hranked child (by simp))
      · exact ih (offset + child.tails.length)
          (fun item hitem => hranked item (by simp [hitem]))
          head hhead

/-- Renumbering collected child heads preserves a common depth bound. -/
public theorem collectHeads_depth_le_of_forall
    (children : List DepthPrefix) (offset bound : ℕ)
    (hdepth : ∀ child ∈ children, child.head.depth ≤ bound) :
    ∀ head ∈ collectHeads children offset,
      head.depth ≤ bound := by
  induction children generalizing offset with
  | nil =>
      simp [collectHeads]
  | cons child children ih =>
      intro head hhead
      simp only [collectHeads, List.mem_cons] at hhead
      rcases hhead with rfl | hhead
      · simpa using hdepth child (by simp)
      · exact ih (offset + child.tails.length)
          (fun item hitem => hdepth item (by simp [hitem]))
          head hhead

end DepthPrefix

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- A pointed ground term has one of the fresh nullary marker symbols at its
root. -/
@[expose] public def FreshCriticalMarkerRoot
    (g : EncodedFirstOrderGrammar Action) (count : ℕ)
    (term : RegularTerm) : Prop :=
  ∃ marker, marker < count ∧
    term.rootApplication? =
      some (g.criticalMarkerSymbol marker, [])

/-- A boundary emitted by a marker-aware prefix is either at the requested
depth or is an earlier fresh-marker root. -/
@[expose] public def CriticalPrefixBoundary
    (g : EncodedFirstOrderGrammar Action) (count : ℕ)
    (term : RegularTerm) (depth : ℕ) (tail : RegularTerm) : Prop :=
  term.SubtermAtDepth depth tail ∨
    g.FreshCriticalMarkerRoot count tail

/-- Unfold to the requested depth, except that every non-original application
root is cut immediately and retained as a boundary argument. -/
@[expose] public def criticalDepthPrefix
    (g : EncodedFirstOrderGrammar Action) :
    ℕ → RegularTerm → DepthPrefix
  | 0, term =>
      { head := .var 0
        tails := [term] }
  | depth + 1, term =>
      match term.rootApplication? with
      | none =>
          { head := .var 0
            tails := [term] }
      | some (symbol, children) =>
          if symbol < g.ranks.length then
            DepthPrefix.assemble symbol
              (children.map fun child =>
                g.criticalDepthPrefix depth (term.withRoot child))
          else
            { head := .var 0
              tails := [term] }

@[simp] public theorem criticalDepthPrefix_zero
    (g : EncodedFirstOrderGrammar Action) (term : RegularTerm) :
    g.criticalDepthPrefix 0 term =
      { head := .var 0, tails := [term] } := rfl

public theorem criticalDepthPrefix_succ_of_originalRoot
    (g : EncodedFirstOrderGrammar Action)
    {term : RegularTerm} {symbol : ℕ} {children : List ℕ}
    (hroot : term.rootApplication? = some (symbol, children))
    (hsymbol : symbol < g.ranks.length) (depth : ℕ) :
    g.criticalDepthPrefix (depth + 1) term =
      DepthPrefix.assemble symbol
        (children.map fun child =>
          g.criticalDepthPrefix depth (term.withRoot child)) := by
  simp [criticalDepthPrefix, hroot, hsymbol]

public theorem criticalDepthPrefix_succ_of_freshRoot
    (g : EncodedFirstOrderGrammar Action)
    {term : RegularTerm} {symbol : ℕ} {children : List ℕ}
    (hroot : term.rootApplication? = some (symbol, children))
    (hsymbol : ¬symbol < g.ranks.length) (depth : ℕ) :
    g.criticalDepthPrefix (depth + 1) term =
      { head := .var 0, tails := [term] } := by
  simp [criticalDepthPrefix, hroot, hsymbol]

/-- Marker-aware prefixes retain exact boundary numbering. -/
public theorem criticalDepthPrefix_valid
    (g : EncodedFirstOrderGrammar Action)
    (term : RegularTerm) (depth : ℕ) :
    (g.criticalDepthPrefix depth term).Valid := by
  induction depth generalizing term with
  | zero =>
      simp [criticalDepthPrefix, DepthPrefix.Valid,
        FiniteHead.VariablesBelow]
  | succ depth ih =>
      cases hroot : term.rootApplication? with
      | none =>
          simp [criticalDepthPrefix, hroot, DepthPrefix.Valid,
            FiniteHead.VariablesBelow]
      | some application =>
          rcases application with ⟨symbol, children⟩
          by_cases hsymbol : symbol < g.ranks.length
          · rw [g.criticalDepthPrefix_succ_of_originalRoot
              hroot hsymbol]
            apply DepthPrefix.assemble_valid
            intro childPrefix hchildPrefix
            obtain ⟨child, _hchild, rfl⟩ :=
              List.mem_map.mp hchildPrefix
            exact ih (term.withRoot child)
          · rw [g.criticalDepthPrefix_succ_of_freshRoot
              hroot hsymbol]
            simp [DepthPrefix.Valid, FiniteHead.VariablesBelow]

/-- An out-of-original-range root of an extended-ground term is exactly one
of the installed fresh nullary marker roots. -/
public theorem freshCriticalMarkerRoot_of_ground_root_not_original
    {g : EncodedFirstOrderGrammar Action} {count : ℕ}
    {term : RegularTerm} {symbol : ℕ} {children : List ℕ}
    (hground : term.Ground (g.withCriticalMarkers count).ranks)
    (hroot : term.rootApplication? = some (symbol, children))
    (hsymbol : ¬symbol < g.ranks.length) :
    g.FreshCriticalMarkerRoot count term := by
  have hrank := hground.root_rank_arity hroot
  have hsymbolExtended :
      symbol < (g.withCriticalMarkers count).ranks.length :=
    (List.getElem?_eq_some_iff.mp hrank).1
  have hlength :
      (g.withCriticalMarkers count).ranks.length =
        g.ranks.length + count := by
    simp [withCriticalMarkers_ranks]
  rw [hlength] at hsymbolExtended
  let marker := symbol - g.ranks.length
  have hmarker : marker < count := by
    dsimp [marker]
    omega
  have hsymbolEq :
      symbol = g.criticalMarkerSymbol marker := by
    unfold criticalMarkerSymbol
    dsimp [marker]
    omega
  have hmarkerRank :
      (g.withCriticalMarkers count).ranks[symbol]? = some 0 := by
    rw [hsymbolEq]
    change (g.ranks ++ List.replicate count 0)[
      g.ranks.length + marker]? = some 0
    rw [List.getElem?_append_right (by omega)]
    simp [hmarker]
  have hchildren : children = [] := by
    rw [hmarkerRank] at hrank
    have := Option.some.inj hrank
    apply List.length_eq_zero_iff.mp
    omega
  exact ⟨marker, hmarker, by simpa [hsymbolEq, hchildren] using hroot⟩

/-- Every marker-aware boundary has the advertised semantic origin. -/
public theorem criticalDepthPrefix_tails_boundary
    {g : EncodedFirstOrderGrammar Action} {count : ℕ}
    {term : RegularTerm}
    (hground : term.Ground (g.withCriticalMarkers count).ranks)
    (depth : ℕ) :
    ∀ tail ∈ (g.criticalDepthPrefix depth term).tails,
      g.CriticalPrefixBoundary count term depth tail := by
  induction depth generalizing term with
  | zero =>
      intro tail htail
      simp only [criticalDepthPrefix_zero,
        List.mem_singleton] at htail
      subst tail
      exact Or.inl
        ((RegularTerm.subtermAtDepth_zero_iff term term).mpr rfl)
  | succ depth ih =>
      obtain ⟨symbol, children, hroot⟩ :=
        hground.exists_rootApplication
      by_cases hsymbol : symbol < g.ranks.length
      · rw [g.criticalDepthPrefix_succ_of_originalRoot
          hroot hsymbol]
        simp only [DepthPrefix.assemble_tails,
          List.mem_flatMap, List.mem_map]
        rintro tail ⟨childPrefix, ⟨child, hchild, rfl⟩, htail⟩
        have hrootNode :=
          RegularTerm.nodeAt?_root_of_rootApplication? hroot
        have hchildGround :
            (term.withRoot child).Ground
              (g.withCriticalMarkers count).ranks :=
          hground.withRoot_descendant
            (.child .root hrootNode hchild)
        rcases ih hchildGround tail htail with
            hdepth | hmarker
        · exact Or.inl
            (by
              simpa [Nat.add_comm] using
                RegularTerm.SubtermAtDepth.of_child
                  hroot hchild hdepth)
        · exact Or.inr hmarker
      · rw [g.criticalDepthPrefix_succ_of_freshRoot
          hroot hsymbol]
        intro tail htail
        simp only [List.mem_singleton] at htail
        subst tail
        exact Or.inr
          (freshCriticalMarkerRoot_of_ground_root_not_original
            hground hroot hsymbol)

/-- Every marker-aware boundary remains ground in the extension. -/
public theorem criticalDepthPrefix_tails_ground
    {g : EncodedFirstOrderGrammar Action} {count : ℕ}
    {term : RegularTerm}
    (hground : term.Ground (g.withCriticalMarkers count).ranks)
    (depth : ℕ) :
    ∀ tail ∈ (g.criticalDepthPrefix depth term).tails,
      tail.Ground (g.withCriticalMarkers count).ranks := by
  induction depth generalizing term with
  | zero =>
      intro tail htail
      simp only [criticalDepthPrefix_zero,
        List.mem_singleton] at htail
      simpa [htail] using hground
  | succ depth ih =>
      obtain ⟨symbol, children, hroot⟩ :=
        hground.exists_rootApplication
      by_cases hsymbol : symbol < g.ranks.length
      · rw [g.criticalDepthPrefix_succ_of_originalRoot
          hroot hsymbol]
        simp only [DepthPrefix.assemble_tails,
          List.mem_flatMap, List.mem_map]
        rintro tail ⟨childPrefix, ⟨child, hchild, rfl⟩, htail⟩
        have hrootNode :=
          RegularTerm.nodeAt?_root_of_rootApplication? hroot
        exact ih
          (hground.withRoot_descendant
            (.child .root hrootNode hchild))
          tail htail
      · rw [g.criticalDepthPrefix_succ_of_freshRoot
          hroot hsymbol]
        intro tail htail
        simp only [List.mem_singleton] at htail
        simpa [htail] using hground

/-- The marker-aware finite head is ranked entirely by the original table. -/
public theorem criticalDepthPrefix_head_rankedBy_original
    {g : EncodedFirstOrderGrammar Action} {count : ℕ}
    {term : RegularTerm}
    (hground : term.Ground (g.withCriticalMarkers count).ranks)
    (depth : ℕ) :
    (g.criticalDepthPrefix depth term).head.RankedBy g.ranks := by
  induction depth generalizing term with
  | zero =>
      simp [criticalDepthPrefix, FiniteHead.RankedBy]
  | succ depth ih =>
      obtain ⟨symbol, children, hroot⟩ :=
        hground.exists_rootApplication
      by_cases hsymbol : symbol < g.ranks.length
      · rw [g.criticalDepthPrefix_succ_of_originalRoot
          hroot hsymbol]
        unfold DepthPrefix.assemble
        simp only [FiniteHead.RankedBy,
          DepthPrefix.collectHeads_length, List.length_map]
        constructor
        · have hextendedRank := hground.root_rank_arity hroot
          change (g.ranks ++ List.replicate count 0)[symbol]? =
            some children.length at hextendedRank
          rw [List.getElem?_append_left hsymbol] at hextendedRank
          exact hextendedRank
        · apply DepthPrefix.collectHeads_rankedBy_of_forall
          intro childPrefix hchildPrefix
          obtain ⟨child, hchild, rfl⟩ :=
            List.mem_map.mp hchildPrefix
          have hrootNode :=
            RegularTerm.nodeAt?_root_of_rootApplication? hroot
          exact ih
            (hground.withRoot_descendant
              (.child .root hrootNode hchild))
      · rw [g.criticalDepthPrefix_succ_of_freshRoot
          hroot hsymbol]
        simp [FiniteHead.RankedBy]

/-- The marker-aware head never exceeds the requested cutoff depth. -/
public theorem criticalDepthPrefix_head_depth_le
    (g : EncodedFirstOrderGrammar Action)
    (term : RegularTerm) (depth : ℕ) :
    (g.criticalDepthPrefix depth term).head.depth ≤ depth := by
  induction depth generalizing term with
  | zero =>
      simp [criticalDepthPrefix, FiniteHead.depth]
  | succ depth ih =>
      cases hroot : term.rootApplication? with
      | none =>
          simp [criticalDepthPrefix, hroot, FiniteHead.depth]
      | some application =>
          rcases application with ⟨symbol, children⟩
          by_cases hsymbol : symbol < g.ranks.length
          · rw [g.criticalDepthPrefix_succ_of_originalRoot
              hroot hsymbol]
            unfold DepthPrefix.assemble
            simp only [FiniteHead.depth]
            have hmax :
                ((DepthPrefix.collectHeads
                  (children.map fun child =>
                    g.criticalDepthPrefix depth
                      (term.withRoot child)) 0).map
                  FiniteHead.depth).foldr max 0 ≤ depth := by
              apply List.max_le_of_forall_le
              intro value hvalue
              obtain ⟨head, hhead, rfl⟩ :=
                List.mem_map.mp hvalue
              apply DepthPrefix.collectHeads_depth_le_of_forall
                (children.map fun child =>
                  g.criticalDepthPrefix depth
                    (term.withRoot child)) 0 depth
              · intro childPrefix hchildPrefix
                obtain ⟨child, _hchild, rfl⟩ :=
                  List.mem_map.mp hchildPrefix
                exact ih (term.withRoot child)
              · exact hhead
            omega
          · rw [g.criticalDepthPrefix_succ_of_freshRoot
              hroot hsymbol]
            simp [FiniteHead.depth]

/-- Count-independent boundary-width envelope for marker-aware prefixes. -/
@[expose] public def criticalDepthPrefixTailBound
    (g : EncodedFirstOrderGrammar Action) : ℕ → ℕ
  | 0 => 1
  | depth + 1 =>
      max 1
        ((g.ranks.foldr max 0) *
          g.criticalDepthPrefixTailBound depth)

private theorem sum_map_le_length_mul
    {A : Type} (values : List A) (weight : A → ℕ) (bound : ℕ)
    (hbound : ∀ value ∈ values, weight value ≤ bound) :
    (values.map weight).sum ≤ values.length * bound := by
  induction values with
  | nil =>
      simp
  | cons value values ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons,
        Nat.succ_mul]
      have hhead := hbound value (by simp)
      have htail := ih
        (fun item hitem => hbound item (by simp [hitem]))
      omega

/-- The number of ordinary depth and early-marker boundaries is uniformly
bounded by the original maximum rank and the cutoff depth. -/
public theorem criticalDepthPrefix_tails_length_le
    {g : EncodedFirstOrderGrammar Action} {count : ℕ}
    {term : RegularTerm}
    (hground : term.Ground (g.withCriticalMarkers count).ranks)
    (depth : ℕ) :
    (g.criticalDepthPrefix depth term).tails.length ≤
      g.criticalDepthPrefixTailBound depth := by
  induction depth generalizing term with
  | zero =>
      simp [criticalDepthPrefix, criticalDepthPrefixTailBound]
  | succ depth ih =>
      obtain ⟨symbol, children, hroot⟩ :=
        hground.exists_rootApplication
      by_cases hsymbol : symbol < g.ranks.length
      · rw [g.criticalDepthPrefix_succ_of_originalRoot
          hroot hsymbol]
        simp only [DepthPrefix.assemble_tails,
          List.length_flatMap, List.map_map, Function.comp_def,
          criticalDepthPrefixTailBound]
        have hrootNode :=
          RegularTerm.nodeAt?_root_of_rootApplication? hroot
        have hchildren : ∀ child ∈ children,
            (g.criticalDepthPrefix depth
              (term.withRoot child)).tails.length ≤
              g.criticalDepthPrefixTailBound depth := by
          intro child hchild
          exact ih
            (hground.withRoot_descendant
              (.child .root hrootNode hchild))
        apply le_trans
          (sum_map_le_length_mul children
            (fun child =>
              (g.criticalDepthPrefix depth
                (term.withRoot child)).tails.length)
            (g.criticalDepthPrefixTailBound depth)
            hchildren)
        apply le_trans
          (Nat.mul_le_mul_right
            (g.criticalDepthPrefixTailBound depth)
            (List.le_max_of_le
              (List.mem_of_getElem? (by
                have hextendedRank :=
                  hground.root_rank_arity hroot
                change (g.ranks ++ List.replicate count 0)[symbol]? =
                  some children.length at hextendedRank
                rw [List.getElem?_append_left hsymbol] at hextendedRank
                exact hextendedRank))
              (le_refl _)))
        exact Nat.le_max_right _ _
      · rw [g.criticalDepthPrefix_succ_of_freshRoot
          hroot hsymbol]
        simp [criticalDepthPrefixTailBound]

/-- Uniform padded arity bound for marker-aware schemas. -/
public theorem criticalDepthPrefix_schemaArity_le
    {g : EncodedFirstOrderGrammar Action} {count : ℕ}
    {term : RegularTerm}
    (hground : term.Ground (g.withCriticalMarkers count).ranks)
    (depth : ℕ) :
    (g.criticalDepthPrefix depth term).schemaArity g.ranks ≤
      max (g.criticalDepthPrefixTailBound depth)
        (g.ranks.foldr max 0) := by
  unfold DepthPrefix.schemaArity
  exact max_le_max_right _
    (g.criticalDepthPrefix_tails_length_le hground depth)

/-- Uniform compiled graph-size bound for marker-aware heads. -/
public theorem criticalDepthPrefix_schema_nodes_length_le
    {g : EncodedFirstOrderGrammar Action} {count : ℕ}
    {term : RegularTerm}
    (hground : term.Ground (g.withCriticalMarkers count).ranks)
    (depth : ℕ) :
    (g.criticalDepthPrefix depth term).head.toRegularTerm.nodes.length ≤
      FiniteHead.compiledDepthBound
        (g.ranks.foldr max 0) depth := by
  rw [FiniteHead.toRegularTerm_nodes_length]
  exact FiniteHead.compiledNodeCount_le_depthBound
    (g.criticalDepthPrefix_head_rankedBy_original hground depth)
    (g.criticalDepthPrefix_head_depth_le term depth)

/-- Evaluating the marker-aware head over its genuine boundary tuple
reconstructs the original extended-ground term. -/
public theorem criticalDepthPrefix_evaluate_unfoldingEquivalent
    {g : EncodedFirstOrderGrammar Action} {count : ℕ}
    {term : RegularTerm}
    (hground : term.Ground (g.withCriticalMarkers count).ranks)
    (depth : ℕ) :
    ((g.criticalDepthPrefix depth term).head.evaluate
      (g.criticalDepthPrefix depth term).tails)
        |>.UnfoldingEquivalent term := by
  induction depth generalizing term with
  | zero =>
      simpa [criticalDepthPrefix, FiniteHead.evaluate] using
        RegularTerm.unfoldingEquivalent_refl term
  | succ depth ih =>
      obtain ⟨symbol, children, hroot⟩ :=
        hground.exists_rootApplication
      by_cases hsymbol : symbol < g.ranks.length
      · rw [g.criticalDepthPrefix_succ_of_originalRoot
          hroot hsymbol]
        let childPrefixes := children.map fun child =>
          g.criticalDepthPrefix depth (term.withRoot child)
        have hclosed :=
          RegularTerm.referenceClosed_of_ground hground
        have hchildBound :=
          RegularTerm.rootApplication_children_lt hclosed hroot
        have hrootNode :
            term.nodeAt? term.root =
              some (.inr (symbol, children)) :=
          RegularTerm.nodeAt?_root_of_rootApplication? hroot
        have hchildGround : ∀ child ∈ children,
            (term.withRoot child).Ground
              (g.withCriticalMarkers count).ranks := by
          intro child hchild
          exact hground.withRoot_descendant
            (.child .root hrootNode hchild)
        have hvalid : ∀ childPrefix ∈ childPrefixes,
            childPrefix.Valid := by
          intro childPrefix hchildPrefix
          obtain ⟨child, _hchild, rfl⟩ :=
            List.mem_map.mp hchildPrefix
          exact g.criticalDepthPrefix_valid
            (term.withRoot child) depth
        rw [DepthPrefix.evaluate_assemble
          symbol childPrefixes hvalid]
        have hchildrenEquivalent :
            List.Forall₂ RegularTerm.UnfoldingEquivalent
              (children.map fun child =>
                (g.criticalDepthPrefix depth
                    (term.withRoot child)).head.evaluate
                  (g.criticalDepthPrefix depth
                    (term.withRoot child)).tails)
              (children.map term.withRoot) := by
          rw [List.forall₂_iff_get]
          constructor
          · simp
          · intro i hleft hright
            have hi : i < children.length := by
              simpa using hright
            simpa using ih
              (hchildGround children[i]
                (List.get_mem children ⟨i, hi⟩))
        have hleftClosed : ∀ argument ∈
            (children.map fun child =>
              (g.criticalDepthPrefix depth
                  (term.withRoot child)).head.evaluate
                (g.criticalDepthPrefix depth
                  (term.withRoot child)).tails),
            argument.ReferenceClosed := by
          intro argument hargument
          obtain ⟨child, hchild, rfl⟩ :=
            List.mem_map.mp hargument
          apply FiniteHead.evaluate_referenceClosed
          intro tail htail
          apply RegularTerm.referenceClosed_of_ground
          exact g.criticalDepthPrefix_tails_ground
            (hchildGround child hchild) depth tail htail
        have hrightClosed :
            ∀ argument ∈ children.map term.withRoot,
              argument.ReferenceClosed := by
          intro argument hargument
          obtain ⟨child, hchild, rfl⟩ :=
            List.mem_map.mp hargument
          exact RegularTerm.withRoot_referenceClosed hclosed
            (hchildBound child hchild)
        have hresult :=
          (RegularTerm.instantiate_unfoldingEquivalent
            (RegularTerm.symbolTemplate_referenceClosed
              symbol children.length)
            hchildrenEquivalent hleftClosed hrightClosed).trans
              (RegularTerm.symbolTemplate_instantiate_unfoldingEquivalent
                hclosed hroot)
        simpa [childPrefixes] using hresult
      · rw [g.criticalDepthPrefix_succ_of_freshRoot
          hroot hsymbol]
        simpa [FiniteHead.evaluate] using
          RegularTerm.unfoldingEquivalent_refl term

/-- The compiled and padded marker-aware schema denotes the original ground
term, even though its boundary arguments need only be ground in the marker
extension. -/
public theorem criticalDepthPrefix_compiled_unfoldingEquivalent
    {g : EncodedFirstOrderGrammar Action} {count : ℕ}
    {term filler : RegularTerm}
    (hground : term.Ground (g.withCriticalMarkers count).ranks)
    (hfiller : filler.Ground (g.withCriticalMarkers count).ranks)
    (depth : ℕ) :
    ((g.criticalDepthPrefix depth term).head.toRegularTerm.instantiate
      ((g.criticalDepthPrefix depth term)
        |>.paddedArguments g.ranks filler))
      |>.UnfoldingEquivalent term := by
  let decomposition := g.criticalDepthPrefix depth term
  have hcompiled :=
    DepthPrefix.compiled_unfoldingEquivalent_evaluate
      (g.criticalDepthPrefix_valid term depth)
      (g.criticalDepthPrefix_head_rankedBy_original
        hground depth)
      (filler := filler)
      (fun tail htail =>
        RegularTerm.referenceClosed_of_ground
          (g.criticalDepthPrefix_tails_ground
            hground depth tail htail))
      (RegularTerm.referenceClosed_of_ground hfiller)
  exact hcompiled.trans
    (g.criticalDepthPrefix_evaluate_unfoldingEquivalent
      hground depth)

/-- The padded tuple of ordinary depth boundaries and early marker boundaries
is ground in the marker extension. -/
public theorem criticalDepthPrefix_paddedArguments_ground
    {g : EncodedFirstOrderGrammar Action} {count : ℕ}
    {term filler : RegularTerm}
    (hground : term.Ground (g.withCriticalMarkers count).ranks)
    (hfiller : filler.Ground (g.withCriticalMarkers count).ranks)
    (depth : ℕ) :
    ∀ argument ∈
      (g.criticalDepthPrefix depth term)
        |>.paddedArguments g.ranks filler,
      argument.Ground (g.withCriticalMarkers count).ranks := by
  intro argument hargument
  simp only [DepthPrefix.paddedArguments, List.mem_append,
    List.mem_replicate] at hargument
  rcases hargument with htail | ⟨_hcount, rfl⟩
  · exact g.criticalDepthPrefix_tails_ground
      hground depth argument htail
  · exact hfiller

/-- The marker-aware compiled head is well formed over the original ranks at
its padded arity. -/
public theorem criticalDepthPrefix_head_wellFormed_original
    {g : EncodedFirstOrderGrammar Action} {count : ℕ}
    {term : RegularTerm}
    (hground : term.Ground (g.withCriticalMarkers count).ranks)
    (depth : ℕ) :
    (g.criticalDepthPrefix depth term).head.toRegularTerm.WellFormed
      g.ranks
      ((g.criticalDepthPrefix depth term).schemaArity g.ranks) := by
  exact DepthPrefix.head_wellFormed_schemaArity
    (g.criticalDepthPrefix_valid term depth)
    (g.criticalDepthPrefix_head_rankedBy_original hground depth)

/-- No nonempty original-action run starts at a fresh marker root. -/
public theorem FreshCriticalMarkerRoot.runActions?_eq_none_of_ne_nil
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {count : ℕ} {term : RegularTerm}
    (hfresh : g.FreshCriticalMarkerRoot count term)
    {word : List Action} (hword : word ≠ []) :
    g.runActions? word term = none := by
  obtain ⟨marker, _hmarker, hroot⟩ := hfresh
  obtain ⟨action, suffix, rfl⟩ :=
    List.exists_cons_of_ne_nil hword
  have hlookup :
      g.ruleLookup (g.criticalMarkerSymbol marker) action = none := by
    cases hrule :
        g.ruleLookup (g.criticalMarkerSymbol marker) action with
    | none =>
        rfl
    | some rhs =>
        obtain ⟨rank, hrank, _hrhs⟩ :=
          selected_rhs_wellFormed hg hrule
        have hsymbol :
            g.criticalMarkerSymbol marker < g.ranks.length :=
          (List.getElem?_eq_some_iff.mp hrank).1
        unfold criticalMarkerSymbol at hsymbol
        omega
  have hstep :
      g.step? (.inl action) term = none := by
    change g.rootRewrite? action term = none
    unfold rootRewrite?
    rw [hroot]
    simp [hlookup]
  simp [runActions?, hstep]

/-- For one executable original word, cutting fresh marker roots early is as
safe as cutting only at the requested depth: a proper symbolic prefix cannot
reach any boundary variable.  Ordinary depth boundaries contradict the
no-exposure hypothesis, while a marker boundary cannot execute the nonempty
remaining original suffix. -/
public theorem criticalDepthPrefix_noVariableBefore
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {count : ℕ} {term filler target : RegularTerm}
    (hterm : term.Ground (g.withCriticalMarkers count).ranks)
    (hfiller : filler.Ground (g.withCriticalMarkers count).ranks)
    (depth : ℕ) {word : List Action}
    (hrun : g.runActions? word term = some target)
    (hnoExposure : g.NoDepthExposureBefore term depth word) :
    g.NoVariableBefore
      (g.criticalDepthPrefix depth term).head.toRegularTerm word := by
  let decomposition := g.criticalDepthPrefix depth term
  let schema := decomposition.head.toRegularTerm
  let arguments := decomposition.paddedArguments g.ranks filler
  have hvalid : decomposition.Valid :=
    g.criticalDepthPrefix_valid term depth
  have hranked : decomposition.head.RankedBy g.ranks :=
    g.criticalDepthPrefix_head_rankedBy_original hterm depth
  have hschemaSupported :
      RegularTerm.SupportedByPrefix g.ranks
        (decomposition.schemaArity g.ranks)
        decomposition.tails.length schema :=
    FiniteHead.toRegularTerm_supportedByPrefix hvalid hranked
  have hpadding :
      g.ranks.foldr max 0 ≤
        decomposition.schemaArity g.ranks := by
    simp [DepthPrefix.schemaArity]
  have hargumentsGround :
      ∀ argument ∈ arguments,
        argument.Ground (g.withCriticalMarkers count).ranks :=
    g.criticalDepthPrefix_paddedArguments_ground
      hterm hfiller depth
  have hargumentsClosed :
      ∀ argument ∈ arguments,
        argument.ReferenceClosed := by
    intro argument hargument
    exact RegularTerm.referenceClosed_of_ground
      (hargumentsGround argument hargument)
  have hinstanceEquivalent :
      (schema.instantiate arguments).UnfoldingEquivalent term :=
    g.criticalDepthPrefix_compiled_unfoldingEquivalent
      hterm hfiller depth
  have hinstanceClosed :
      (schema.instantiate arguments).ReferenceClosed :=
    RegularTerm.instantiate_referenceClosed
      (RegularTerm.referenceClosed_of_wellFormed
        hschemaSupported.1)
      hargumentsClosed
  intro stem suffix hword hsuffix residual x
    hstemRun hresidualVariable
  have hresidualSupported :=
    hschemaSupported.residual hg hpadding hstemRun
  have hresidualRoot :
      residual.rootNode? = some (.inl x) :=
    rootNode?_variable_of_unfoldingEquivalent
      hresidualVariable.symm
      (RegularTerm.variableTerm_rootNode? x)
  have hxTails : x < decomposition.tails.length :=
    hresidualSupported.variableIndex_lt_width_of_root
      hresidualRoot
  let tail := decomposition.tails[x]
  have htailGet : decomposition.tails[x]? = some tail :=
    List.getElem?_eq_getElem hxTails
  have hargumentGet : arguments[x]? = some tail := by
    unfold arguments DepthPrefix.paddedArguments
    rw [List.getElem?_append_left hxTails]
    exact htailGet
  have hresidualNode :
      residual.nodeAt? residual.root = some (.inl x) := by
    simpa [RegularTerm.rootNode?] using hresidualRoot
  have hresidualInstanceTail :
      (residual.instantiate arguments).UnfoldingEquivalent tail :=
    RegularTerm.instantiate_unfoldingEquivalent_argument
      hresidualNode hargumentGet
      (RegularTerm.referenceClosed_of_ground
        (hargumentsGround tail
          (List.mem_of_getElem? hargumentGet)))
  obtain ⟨instantiatedStem, hinstantiatedStemRun,
      hresidualInstantiation⟩ :=
    g.runActions?_instantiate hg stem hschemaSupported.1
      hargumentsClosed hstemRun
  obtain ⟨termStem, htermStemRun, htermStemEquivalent⟩ :=
    exists_runActions_of_unfoldingEquivalent hg
      hinstanceEquivalent.symm
      (RegularTerm.referenceClosed_of_ground hterm)
      hinstanceClosed hinstantiatedStemRun
  have htermStemTail :
      termStem.UnfoldingEquivalent tail :=
    htermStemEquivalent.trans
      (hresidualInstantiation.symm.trans
        hresidualInstanceTail)
  rcases g.criticalDepthPrefix_tails_boundary
      hterm depth tail (List.getElem_mem hxTails) with
      htailDepth | htailMarker
  · apply hnoExposure stem suffix hword hsuffix
    exact ⟨tail, termStem, htailDepth,
      by simpa [runActions?] using htermStemRun,
      htermStemTail⟩
  · have htermStemClosed : termStem.ReferenceClosed :=
      g.runActions?_preserves_referenceClosed hg stem
        (RegularTerm.referenceClosed_of_ground hterm)
        htermStemRun
    have htailClosed : tail.ReferenceClosed :=
      RegularTerm.referenceClosed_of_ground
        (g.criticalDepthPrefix_tails_ground
          hterm depth tail (List.getElem_mem hxTails))
    have hsuffixRun :
        g.runActions? suffix termStem = some target := by
      unfold runActions? at hrun htermStemRun ⊢
      rw [hword, List.map_append, g.run?_append,
        htermStemRun] at hrun
      exact hrun
    obtain ⟨tailTarget, htailRun, _htarget⟩ :=
      exists_runActions_of_unfoldingEquivalent hg
        htermStemTail.symm htailClosed htermStemClosed
        hsuffixRun
    rw [htailMarker.runActions?_eq_none_of_ne_nil
      hg hsuffix] at htailRun
    contradiction

end EncodedFirstOrderGrammar

end DCFEquivalence
