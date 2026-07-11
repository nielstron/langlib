module

public import Langlib.Grammars.Indexed.NormalForm.AhoControlDenotation

@[expose]
public section

/-!
# Soundness of Aho's compressed-index machine

This file proves the grammar-facing direction of Aho's construction.  The invariant uses the
mark-aware block denotation from `AhoBlockDenotation`: compressed tokens denote visible stack
blocks, while gaps skipped by a plain push remain existentially hidden between those blocks.
-/

open List Relation

variable {T : Type}

namespace IndexedGrammar
namespace Aho
namespace BlockDenotation

/-! ## Elementary segment and layout operations -/

/-- A represented segment contains no frame delimiter. -/
public theorem SegmentRep.dollarFree
    {g : IndexedGrammar T} [Fintype g.nt]
    {inherited before : VisibleStack g} {xs : List (WorkSym g)}
    {form : List g.ISym} (h : SegmentRep g inherited xs before form) :
    DollarFree xs := by
  induction h with
  | nil => simp [DollarFree]
  | terminal a tail ih => simpa [DollarFree] using ih
  | plain A actual decorates tail ih => simpa [DollarFree] using ih
  | live A actual decorates tail ih => simpa [DollarFree] using ih
  | index d flags denotes tail ih => simpa [DollarFree] using ih

/-- Change the mark of a compressed token at the right edge of a segment. -/
public theorem SegmentRep.changeLastIndex
    {g : IndexedGrammar T} [Fintype g.nt]
    {inherited before : VisibleStack g} {beta : List (WorkSym g)}
    {form : List g.ISym} {R : CFlag g} {d e : IndexMark}
    (hlater : d.later = e.later)
    (h : SegmentRep g inherited (beta ++ [WorkSym.index R d]) before form) :
    SegmentRep g inherited (beta ++ [WorkSym.index R e]) before form := by
  rcases (segmentRep_append_iff beta [WorkSym.index R d]).mp h with
    ⟨middle, leftForm, rightForm, hright, hleft, rfl⟩
  exact (segmentRep_append_iff beta [WorkSym.index R e]).mpr
    ⟨middle, leftForm, rightForm,
      hright.changeIndexMark hlater, hleft, rfl⟩

/-- Invert a compressed token at the head of a represented segment. -/
public theorem SegmentRep.unconsIndex
    {g : IndexedGrammar T} [Fintype g.nt]
    {inherited before : VisibleStack g} {xs : List (WorkSym g)}
    {form : List g.ISym} {R : CFlag g} {d : IndexMark}
    (h : SegmentRep g inherited (WorkSym.index R d :: xs) before form) :
    ∃ stack flags,
      before = ⟨flags, d.later⟩ :: stack ∧
        CFlag.Denotes g flags R ∧ SegmentRep g inherited xs stack form := by
  cases h with
  | index _ flags denotes tail =>
      exact ⟨_, flags, rfl, denotes, tail⟩

/-- The part of `frameLeft` before its final active-frame delimiter. -/
public def framePrefix (g : IndexedGrammar T) :
    List (FrameBoundary g) → List (WorkSym g)
  | [] => []
  | (pending, _) :: frames =>
      WorkSym.dollar :: pending ++ framePrefix g frames

@[simp] public theorem frameLeft_eq_prefix (g : IndexedGrammar T)
    (frames : List (FrameBoundary g)) :
    frameLeft g frames = framePrefix g frames ++ [WorkSym.dollar] := by
  induction frames with
  | nil => simp [frameLeft, framePrefix]
  | cons frame frames ih =>
      rcases frame with ⟨pending, suffix⟩
      simp [frameLeft, framePrefix, ih, List.append_assoc]

@[simp] public theorem framePrefix_append_boundary (g : IndexedGrammar T)
    (frames : List (FrameBoundary g)) (pending suffix : List (WorkSym g)) :
    framePrefix g (frames ++ [(pending, suffix)]) =
      frameLeft g frames ++ pending := by
  induction frames with
  | nil => simp [framePrefix, frameLeft]
  | cons frame frames ih =>
      rcases frame with ⟨outerPending, outerSuffix⟩
      simp [framePrefix, frameLeft, ih, List.append_assoc]

@[simp] public theorem frameLeft_append_boundary (g : IndexedGrammar T)
    (frames : List (FrameBoundary g)) (pending suffix : List (WorkSym g)) :
    frameLeft g (frames ++ [(pending, suffix)]) =
      frameLeft g frames ++ pending ++ [WorkSym.dollar] := by
  rw [frameLeft_eq_prefix, framePrefix_append_boundary]

@[simp] public theorem frameTail_append_boundary (g : IndexedGrammar T)
    (frames : List (FrameBoundary g)) (pending suffix : List (WorkSym g)) :
    frameTail g (frames ++ [(pending, suffix)]) =
      WorkSym.close :: suffix ++ frameTail g frames := by
  simp [frameTail, List.reverse_append, List.append_assoc]

/-- A layout focused on an ordinary work symbol exposes the head of the active segment. -/
public theorem CursorLayout.of_current_cons
    {g : IndexedGrammar T} {frames : List (FrameBoundary g)}
    {x : WorkSym g} {xs : List (WorkSym g)} {cursor : WorkCursor g}
    (h : CursorLayout g frames (x :: xs) cursor) :
    cursor.left = frameLeft g frames ∧ cursor.focus = x ∧
      cursor.right = xs ++ frameTail g frames := by
  rcases h with ⟨z, zs, hword, hleft, hfocus, hright⟩
  simp only [List.cons_append, List.cons.injEq] at hword
  rcases hword with ⟨rfl, rfl⟩
  exact ⟨hleft, hfocus, hright⟩

/-- Conversely, the canonical zipper for a nonempty active segment has the expected layout. -/
public theorem CursorLayout.cons
    {g : IndexedGrammar T} (frames : List (FrameBoundary g))
    (x : WorkSym g) (xs : List (WorkSym g)) :
    CursorLayout g frames (x :: xs)
      ⟨frameLeft g frames, x, xs ++ frameTail g frames⟩ := by
  exact ⟨x, xs ++ frameTail g frames, by simp, rfl, rfl, rfl⟩

/-- A layout with an empty active segment is focused on the head of its frame tail. -/
public theorem CursorLayout.of_current_nil
    {g : IndexedGrammar T} {frames : List (FrameBoundary g)}
    {cursor : WorkCursor g} (h : CursorLayout g frames [] cursor) :
    ∃ z zs, frameTail g frames = z :: zs ∧
      cursor.left = frameLeft g frames ∧ cursor.focus = z ∧ cursor.right = zs := by
  rcases h with ⟨z, zs, htail, hleft, hfocus, hright⟩
  exact ⟨z, zs, by simpa using htail, hleft, hfocus, hright⟩

/-- Prefix/suffix contextual closure for indexed derivations. -/
public theorem derives_in_context {g : IndexedGrammar T}
    (pref suffix : List g.ISym) {u v : List g.ISym}
    (h : g.Derives u v) :
    g.Derives (pref ++ u ++ suffix) (pref ++ v ++ suffix) := by
  simpa [List.append_assoc] using
    deri_with_prefix pref (deri_with_suffix suffix h)

/-! ## Changing the active innermost segment -/

/-- A transformation of the active segment lifts through all suspended frames. -/
public theorem NestedRep.mapCurrent
    {g : IndexedGrammar T} [Fintype g.nt]
    {inherited : VisibleStack g} {frames : List (FrameBoundary g)}
    {current current' : List (WorkSym g)} {form : List g.ISym}
    (h : NestedRep g inherited frames current form)
    (base : ∀ {baseStack before : VisibleStack g} {baseForm : List g.ISym},
      SegmentRep g baseStack current before baseForm →
        ∃ before' form',
          SegmentRep g baseStack current' before' form' ∧
            g.Derives baseForm form') :
    ∃ form', NestedRep g inherited frames current' form' ∧
      g.Derives form form' := by
  induction h with
  | current segment =>
      rcases base segment with ⟨before', form', segment', hderiv⟩
      exact ⟨form', NestedRep.current segment', hderiv⟩
  | @frame inherited tailStack pendingStack pending suffix current frames
      suffixForm pendingForm innerForm suffixRep pendingRep pendingEndsIndex innerRep ih =>
      rcases ih base with ⟨innerForm', innerRep', hderiv⟩
      refine ⟨innerForm' ++ pendingForm ++ suffixForm,
        NestedRep.frame suffixRep pendingRep pendingEndsIndex innerRep', ?_⟩
      simpa [List.append_assoc] using
        derives_in_context [] (pendingForm ++ suffixForm) hderiv

/-- A form-preserving active-segment edit lifts through all suspended frames. -/
public theorem NestedRep.mapCurrentSame
    {g : IndexedGrammar T} [Fintype g.nt]
    {inherited : VisibleStack g} {frames : List (FrameBoundary g)}
    {current current' : List (WorkSym g)} {form : List g.ISym}
    (h : NestedRep g inherited frames current form)
    (base : ∀ {baseStack before : VisibleStack g} {baseForm : List g.ISym},
      SegmentRep g baseStack current before baseForm →
        ∃ before', SegmentRep g baseStack current' before' baseForm) :
    NestedRep g inherited frames current' form := by
  rcases h.mapCurrent (fun hseg => by
    rcases base hseg with ⟨before', hseg'⟩
    exact ⟨before', _, hseg', deri_self g _⟩) with
    ⟨form', hrep, hderiv⟩
  -- `mapCurrent` may choose a propositionally equal form through a reflexive derivation;
  -- use the direct structural induction below to retain definitional equality.
  clear form' hrep hderiv
  induction h with
  | current segment =>
      rcases base segment with ⟨before', segment'⟩
      exact NestedRep.current segment'
  | frame suffixRep pendingRep pendingEndsIndex innerRep ih =>
      exact NestedRep.frame suffixRep pendingRep pendingEndsIndex (ih base)

/-! ## Productive marking of the innermost suspended index -/

/-- Mark the index at the end of the innermost pending frame, if there is one. -/
public def markInnermostFrames {g : IndexedGrammar T} :
    List (FrameBoundary g) → List (FrameBoundary g)
  | [] => []
  | [(pending, suffix)] => [(markProductivePrefix pending, suffix)]
  | boundary :: next :: frames =>
      boundary :: markInnermostFrames (next :: frames)

/-- Productive marking distributes over a prefix when the marked suffix ends in an index. -/
public theorem markProductivePrefix_append_of_endsIndex
    {g : IndexedGrammar T} (pref suffix : List (WorkSym g))
    (hends : ∃ beta R d, suffix = beta ++ [WorkSym.index R d]) :
    markProductivePrefix (pref ++ suffix) =
      pref ++ markProductivePrefix suffix := by
  rcases hends with ⟨beta, R, d, rfl⟩
  simp only [← List.append_assoc, markProductivePrefix_append_index]

/-- Every nonempty frame prefix represented by `NestedRep` ends in its consumed compressed
index. -/
public theorem NestedRep.framePrefix_endsIndex
    {g : IndexedGrammar T} [Fintype g.nt]
    {inherited : VisibleStack g} {frames : List (FrameBoundary g)}
    {current : List (WorkSym g)} {form : List g.ISym}
    (h : NestedRep g inherited frames current form) (hne : frames ≠ []) :
    ∃ beta R d, framePrefix g frames = beta ++ [WorkSym.index R d] := by
  induction h with
  | current segment => exact False.elim (hne rfl)
  | @frame inherited tailStack pendingStack pending suffix current frames
      suffixForm pendingForm innerForm suffixRep pendingRep pendingEnds innerRep ih =>
      cases frames with
      | nil =>
          rcases pendingEnds with ⟨beta, R, d, rfl⟩
          exact ⟨WorkSym.dollar :: beta, R, d, by
            simp [framePrefix, List.append_assoc]⟩
      | cons next rest =>
          rcases ih (by simp) with ⟨beta, R, d, hprefix⟩
          refine ⟨WorkSym.dollar :: pending ++ beta, R, d, ?_⟩
          change WorkSym.dollar :: pending ++ framePrefix g (next :: rest) = _
          rw [hprefix]
          simp [List.append_assoc]

/-- Marking pending lists cannot affect the closing half of the frame layout. -/
@[simp] public theorem frameTail_markInnermostFrames
    {g : IndexedGrammar T} (frames : List (FrameBoundary g)) :
    frameTail g (markInnermostFrames frames) = frameTail g frames := by
  induction frames with
  | nil => simp [markInnermostFrames]
  | cons boundary frames ih =>
      cases frames with
      | nil =>
          rcases boundary with ⟨pending, suffix⟩
          simp [markInnermostFrames, frameTail]
      | cons next rest =>
          unfold frameTail at ih ⊢
          have ihcore := List.append_cancel_right ih
          simp only [markInnermostFrames, List.reverse_cons,
            List.flatMap_append, List.flatMap_singleton]
          rw [ihcore]
          simp [List.reverse_cons, List.flatMap_append, List.append_assoc]

/-- Productive marking changes only operational marks in the innermost suspended boundary. -/
public theorem NestedRep.markInnermostUsed
    {g : IndexedGrammar T} [Fintype g.nt]
    {inherited : VisibleStack g} {frames : List (FrameBoundary g)}
    {current : List (WorkSym g)} {form : List g.ISym}
    (h : NestedRep g inherited frames current form) :
    NestedRep g inherited (markInnermostFrames frames) current form ∧
      framePrefix g (markInnermostFrames frames) =
        markProductivePrefix (framePrefix g frames) ∧
      frameTail g (markInnermostFrames frames) = frameTail g frames := by
  induction h with
  | current segment =>
      exact ⟨NestedRep.current segment, by simp [markInnermostFrames, framePrefix],
        by simp [markInnermostFrames]⟩
  | @frame inherited tailStack pendingStack pending suffix current frames
      suffixForm pendingForm innerForm suffixRep pendingRep pendingEnds innerRep ih =>
      cases frames with
      | nil =>
          rcases pendingEnds with ⟨beta, R, d, hpending⟩
          subst pending
          have pendingRep' := pendingRep.changeLastIndex
            (IndexMark.later_markUsed d).symm
          refine ⟨NestedRep.frame suffixRep (by simpa using pendingRep') ?_ innerRep,
            ?_, frameTail_markInnermostFrames _⟩
          · exact ⟨beta, R, d.markUsed, by simp⟩
          · have hmark := markProductivePrefix_append_of_endsIndex
              [WorkSym.dollar] (beta ++ [WorkSym.index R d])
              ⟨beta, R, d, rfl⟩
            simpa [markInnermostFrames, framePrefix, List.append_assoc] using hmark.symm
      | cons next rest =>
          rcases ih with ⟨innerRep', hprefix, htail⟩
          have hends := innerRep.framePrefix_endsIndex (by simp)
          refine ⟨NestedRep.frame suffixRep pendingRep pendingEnds innerRep', ?_,
            frameTail_markInnermostFrames _⟩
          · simp only [markInnermostFrames, framePrefix]
            rw [hprefix]
            simpa [List.append_assoc] using
              (markProductivePrefix_append_of_endsIndex
                (WorkSym.dollar :: pending) (framePrefix g (next :: rest)) hends).symm

/-! ## Grammar-producing edits of an active segment -/

public theorem NestedRep.plainBinary
    {g : IndexedGrammar T} [Fintype g.nt]
    {inherited : VisibleStack g} {frames : List (FrameBoundary g)}
    {xs : List (WorkSym g)} {form : List g.ISym} {A B C : g.nt}
    (haug : AugBinary g A B C)
    (h : NestedRep g inherited frames (WorkSym.plain A :: xs) form) :
    ∃ form',
      NestedRep g inherited frames (WorkSym.plain B :: WorkSym.plain C :: xs) form' ∧
        g.Derives form form' := by
  apply h.mapCurrent
  intro baseStack before baseForm hseg
  cases hseg with
  | @plain _ _ tailForm _ actual decorates tail =>
      refine ⟨before, _, SegmentRep.plain B actual decorates
        (SegmentRep.plain C actual decorates tail), ?_⟩
      simpa using deri_with_suffix tailForm
        (augBinary_derives haug actual)

public theorem NestedRep.plainTerminal
    {g : IndexedGrammar T} [Fintype g.nt]
    {inherited : VisibleStack g} {frames : List (FrameBoundary g)}
    {xs : List (WorkSym g)} {form : List g.ISym} {A : g.nt} {a : T}
    (haug : AugTerminal g A a)
    (h : NestedRep g inherited frames (WorkSym.plain A :: xs) form) :
    ∃ form', NestedRep g inherited frames (WorkSym.terminal a :: xs) form' ∧
      g.Derives form form' := by
  apply h.mapCurrent
  intro baseStack before baseForm hseg
  cases hseg with
  | @plain _ _ tailForm _ actual decorates tail =>
      refine ⟨before, _, SegmentRep.terminal a tail, ?_⟩
      simpa using deri_with_suffix tailForm
        (augTerminal_derives haug actual)

public theorem NestedRep.plainPushSkip
    {g : IndexedGrammar T} [Fintype g.nt]
    {inherited : VisibleStack g} {frames : List (FrameBoundary g)}
    {xs : List (WorkSym g)} {form : List g.ISym} {A B : g.nt} {f : g.flag}
    (haug : AugPush g A B f)
    (h : NestedRep g inherited frames (WorkSym.plain A :: xs) form) :
    ∃ form', NestedRep g inherited frames (WorkSym.plain B :: xs) form' ∧
      g.Derives form form' := by
  apply h.mapCurrent
  intro baseStack before baseForm hseg
  cases hseg with
  | @plain _ _ tailForm _ actual decorates tail =>
      refine ⟨before, _, SegmentRep.plain B (f :: actual)
        (decorates.pushHidden f) tail, ?_⟩
      simpa using deri_with_suffix tailForm
        (augPush_derives haug actual)

public theorem NestedRep.plainPushUse
    {g : IndexedGrammar T} [Fintype g.nt]
    {inherited : VisibleStack g} {frames : List (FrameBoundary g)}
    {xs : List (WorkSym g)} {form : List g.ISym} {A B : g.nt} {f : g.flag}
    (haug : AugPush g A B f)
    (h : NestedRep g inherited frames (WorkSym.plain A :: xs) form) :
    ∃ form', NestedRep g inherited frames
        (WorkSym.live B :: WorkSym.index (cflagBase g f) .firstPending :: xs) form' ∧
      g.Derives form form' := by
  apply h.mapCurrent
  intro baseStack before baseForm hseg
  cases hseg with
  | @plain _ _ tailForm _ actual decorates tail =>
      refine ⟨⟨[f], false⟩ :: before, _,
        SegmentRep.live B (f :: actual) (decorates.pushFirst f)
          (SegmentRep.index .firstPending [f] (CFlag.Denotes.base f) tail), ?_⟩
      simpa using deri_with_suffix tailForm
        (augPush_derives haug actual)

public theorem NestedRep.liveBinaryBoth
    {g : IndexedGrammar T} [Fintype g.nt]
    {inherited : VisibleStack g} {frames : List (FrameBoundary g)}
    {xs : List (WorkSym g)} {form : List g.ISym} {A B C : g.nt}
    (haug : AugBinary g A B C)
    (h : NestedRep g inherited frames (WorkSym.live A :: xs) form) :
    ∃ form', NestedRep g inherited frames
        (WorkSym.live B :: WorkSym.live C :: xs) form' ∧
      g.Derives form form' := by
  apply h.mapCurrent
  intro baseStack before baseForm hseg
  cases hseg with
  | @live _ _ tailForm _ actual decorates tail =>
      refine ⟨before, _, SegmentRep.live B actual decorates
        (SegmentRep.live C actual decorates tail), ?_⟩
      simpa using deri_with_suffix tailForm
        (augBinary_derives haug actual)

public theorem NestedRep.liveBinaryLeft
    {g : IndexedGrammar T} [Fintype g.nt]
    {inherited : VisibleStack g} {frames : List (FrameBoundary g)}
    {xs : List (WorkSym g)} {form : List g.ISym} {A B C : g.nt}
    (haug : AugBinary g A B C)
    (h : NestedRep g inherited frames (WorkSym.live A :: xs) form) :
    ∃ form', NestedRep g inherited frames
        (WorkSym.live B :: WorkSym.plain C :: xs) form' ∧
      g.Derives form form' := by
  apply h.mapCurrent
  intro baseStack before baseForm hseg
  cases hseg with
  | @live _ _ tailForm _ actual decorates tail =>
      refine ⟨before, _, SegmentRep.live B actual decorates
        (SegmentRep.plain C actual decorates.toDecorates tail), ?_⟩
      simpa using deri_with_suffix tailForm
        (augBinary_derives haug actual)

public theorem NestedRep.liveBinaryRight
    {g : IndexedGrammar T} [Fintype g.nt]
    {inherited : VisibleStack g} {frames : List (FrameBoundary g)}
    {xs : List (WorkSym g)} {form : List g.ISym} {A B C : g.nt}
    (haug : AugBinary g A B C)
    (h : NestedRep g inherited frames (WorkSym.live A :: xs) form) :
    ∃ form', NestedRep g inherited frames
        (WorkSym.plain B :: WorkSym.live C :: xs) form' ∧
      g.Derives form form' := by
  apply h.mapCurrent
  intro baseStack before baseForm hseg
  cases hseg with
  | @live _ _ tailForm _ actual decorates tail =>
      refine ⟨before, _, SegmentRep.plain B actual decorates.toDecorates
        (SegmentRep.live C actual decorates tail), ?_⟩
      simpa using deri_with_suffix tailForm
        (augBinary_derives haug actual)

public theorem NestedRep.livePushFresh
    {g : IndexedGrammar T} [Fintype g.nt]
    {inherited : VisibleStack g} {frames : List (FrameBoundary g)}
    {xs : List (WorkSym g)} {form : List g.ISym} {A B : g.nt} {f : g.flag}
    (haug : AugPush g A B f)
    (h : NestedRep g inherited frames (WorkSym.live A :: xs) form) :
    ∃ form', NestedRep g inherited frames
        (WorkSym.live B :: WorkSym.index (cflagBase g f) .laterPending :: xs) form' ∧
      g.Derives form form' := by
  apply h.mapCurrent
  intro baseStack before baseForm hseg
  cases hseg with
  | @live _ _ tailForm _ actual decorates tail =>
      refine ⟨⟨[f], true⟩ :: before, _,
        SegmentRep.live B (f :: actual) (decorates.pushLater f)
          (SegmentRep.index .laterPending [f] (CFlag.Denotes.base f) tail), ?_⟩
      simpa using deri_with_suffix tailForm
        (augPush_derives haug actual)

public theorem NestedRep.livePushCompress
    {g : IndexedGrammar T} [Fintype g.nt]
    {inherited : VisibleStack g} {frames : List (FrameBoundary g)}
    {xs : List (WorkSym g)} {form : List g.ISym} {A B : g.nt} {f : g.flag}
    {R : CFlag g} {d : IndexMark}
    (haug : AugPush g A B f)
    (h : NestedRep g inherited frames
      (WorkSym.live A :: WorkSym.index R d :: xs) form) :
    ∃ form', NestedRep g inherited frames
        (WorkSym.live B ::
          WorkSym.index (cflagComp g (cflagBase g f) R) d :: xs) form' ∧
      g.Derives form form' := by
  apply h.mapCurrent
  intro baseStack before baseForm hseg
  cases hseg with
  | @live _ _ tailForm _ actual decorates tail =>
      cases tail with
      | index _ flags denotes rest =>
          have denotes' : CFlag.Denotes g (f :: flags)
              (cflagComp g (cflagBase g f) R) := by
            simpa using CFlag.Denotes.comp (CFlag.Denotes.base f) denotes
          refine ⟨⟨f :: flags, d.later⟩ :: _, _,
            SegmentRep.live B (f :: actual) (decorates.pushCompress f)
              (SegmentRep.index d (f :: flags) denotes' rest), ?_⟩
          simpa using deri_with_suffix tailForm
            (augPush_derives haug actual)

/-! ## Opening a pop frame -/

/-- The local, delimiter-free content of a pop-to-plain move. -/
public theorem SegmentRep.openPopPlain
    {g : IndexedGrammar T} [Fintype g.nt]
    {baseStack before : VisibleStack g} {beta gamma : List (WorkSym g)}
    {form : List g.ISym} {R : CFlag g} {d : IndexMark} {A B : g.nt}
    (hfree : IndexFree beta) (hedge : R A B = true)
    (h : SegmentRep g baseStack
      (WorkSym.live A :: beta ++ WorkSym.index R d :: gamma) before form) :
    ∃ form', NestedRep g baseStack
        [((beta ++ [WorkSym.index R d]), gamma)] [WorkSym.plain B] form' ∧
      g.Derives form form' := by
  cases h with
  | @live _ _ tailForm _ actual decorates tail =>
      rcases (segmentRep_append_iff beta (WorkSym.index R d :: gamma)).mp tail with
        ⟨middle, betaForm, gammaForm, hright, hbeta, hform⟩
      rcases hright.unconsIndex with
        ⟨tailStack, flags, hmiddle, denotes, suffixRep⟩
      subst middle
      have hstack : before = ⟨flags, d.later⟩ :: tailStack :=
        hbeta.stack_eq_of_indexFree hfree
      subst before
      rcases decorates.popPlain with ⟨rest, hactual, restDecorates⟩
      subst actual
      have pendingRep : SegmentRep g tailStack
          (beta ++ [WorkSym.index R d])
          (⟨flags, d.later⟩ :: tailStack) betaForm :=
        (segmentRep_append_iff beta [WorkSym.index R d]).mpr
          ⟨⟨flags, d.later⟩ :: tailStack, betaForm, [],
            SegmentRep.index d flags denotes (SegmentRep.nil tailStack),
            hbeta, by simp⟩
      have innerRep : NestedRep g tailStack [] [WorkSym.plain B]
          [ISym.indexed B rest] :=
        NestedRep.current
          (SegmentRep.plain B rest restDecorates (SegmentRep.nil tailStack))
      refine ⟨[ISym.indexed B rest] ++ betaForm ++ gammaForm,
        NestedRep.frame suffixRep pendingRep ⟨beta, R, d, rfl⟩ innerRep, ?_⟩
      rw [hform]
      simpa [List.append_assoc] using
        deri_with_suffix (betaForm ++ gammaForm)
          (denotes.edge_derives hedge rest)

/-- The local, delimiter-free content of a pop-to-live move. -/
public theorem SegmentRep.openPopLive
    {g : IndexedGrammar T} [Fintype g.nt]
    {baseStack before : VisibleStack g} {beta gamma : List (WorkSym g)}
    {form : List g.ISym} {R : CFlag g} {d : IndexMark} {A B : g.nt}
    (hfree : IndexFree beta) (hedge : R A B = true) (hlater : d.later = true)
    (h : SegmentRep g baseStack
      (WorkSym.live A :: beta ++ WorkSym.index R d :: gamma) before form) :
    ∃ form', NestedRep g baseStack
        [((beta ++ [WorkSym.index R d]), gamma)] [WorkSym.live B] form' ∧
      g.Derives form form' := by
  cases h with
  | @live _ _ tailForm _ actual decorates tail =>
      rcases (segmentRep_append_iff beta (WorkSym.index R d :: gamma)).mp tail with
        ⟨middle, betaForm, gammaForm, hright, hbeta, hform⟩
      rcases hright.unconsIndex with
        ⟨tailStack, flags, hmiddle, denotes, suffixRep⟩
      subst middle
      have hstack : before = ⟨flags, d.later⟩ :: tailStack :=
        hbeta.stack_eq_of_indexFree hfree
      subst before
      rcases decorates.popLive hlater with ⟨rest, hactual, restDecorates⟩
      subst actual
      have pendingRep : SegmentRep g tailStack
          (beta ++ [WorkSym.index R d])
          (⟨flags, d.later⟩ :: tailStack) betaForm :=
        (segmentRep_append_iff beta [WorkSym.index R d]).mpr
          ⟨⟨flags, d.later⟩ :: tailStack, betaForm, [],
            SegmentRep.index d flags denotes (SegmentRep.nil tailStack),
            hbeta, by simp⟩
      have innerRep : NestedRep g tailStack [] [WorkSym.live B]
          [ISym.indexed B rest] :=
        NestedRep.current
          (SegmentRep.live B rest restDecorates (SegmentRep.nil tailStack))
      refine ⟨[ISym.indexed B rest] ++ betaForm ++ gammaForm,
        NestedRep.frame suffixRep pendingRep ⟨beta, R, d, rfl⟩ innerRep, ?_⟩
      rw [hform]
      simpa [List.append_assoc] using
        deri_with_suffix (betaForm ++ gammaForm)
          (denotes.edge_derives hedge rest)

/-- Opening a new innermost pop frame lifts through every already suspended outer frame. -/
public theorem NestedRep.appendInnermost
    {g : IndexedGrammar T} [Fintype g.nt]
    {inherited : VisibleStack g} {frames : List (FrameBoundary g)}
    {current current' : List (WorkSym g)} {form : List g.ISym}
    (boundary : FrameBoundary g)
    (h : NestedRep g inherited frames current form)
    (base : ∀ {baseStack before : VisibleStack g} {baseForm : List g.ISym},
      SegmentRep g baseStack current before baseForm →
        ∃ form', NestedRep g baseStack [boundary] current' form' ∧
          g.Derives baseForm form') :
    ∃ form', NestedRep g inherited (frames ++ [boundary]) current' form' ∧
      g.Derives form form' := by
  induction h with
  | current segment =>
      simpa using base segment
  | @frame inherited tailStack pendingStack pending suffix current frames
      suffixForm pendingForm innerForm suffixRep pendingRep pendingEnds innerRep ih =>
      rcases ih base with ⟨innerForm', innerRep', hderiv⟩
      refine ⟨innerForm' ++ pendingForm ++ suffixForm, ?_, ?_⟩
      · simpa [List.append_assoc] using
          NestedRep.frame suffixRep pendingRep pendingEnds innerRep'
      · simpa [List.append_assoc] using
          derives_in_context [] (pendingForm ++ suffixForm) hderiv

public theorem NestedRep.openPopPlain
    {g : IndexedGrammar T} [Fintype g.nt]
    {inherited : VisibleStack g} {frames : List (FrameBoundary g)}
    {beta gamma : List (WorkSym g)} {form : List g.ISym}
    {R : CFlag g} {d : IndexMark} {A B : g.nt}
    (hfree : IndexFree beta) (hedge : R A B = true)
    (h : NestedRep g inherited frames
      (WorkSym.live A :: beta ++ WorkSym.index R d :: gamma) form) :
    ∃ form', NestedRep g inherited
        (frames ++ [((beta ++ [WorkSym.index R d]), gamma)])
        [WorkSym.plain B] form' ∧ g.Derives form form' := by
  apply h.appendInnermost ((beta ++ [WorkSym.index R d]), gamma)
  intro baseStack before baseForm segment
  exact segment.openPopPlain hfree hedge

public theorem NestedRep.openPopLive
    {g : IndexedGrammar T} [Fintype g.nt]
    {inherited : VisibleStack g} {frames : List (FrameBoundary g)}
    {beta gamma : List (WorkSym g)} {form : List g.ISym}
    {R : CFlag g} {d : IndexMark} {A B : g.nt}
    (hfree : IndexFree beta) (hedge : R A B = true) (hlater : d.later = true)
    (h : NestedRep g inherited frames
      (WorkSym.live A :: beta ++ WorkSym.index R d :: gamma) form) :
    ∃ form', NestedRep g inherited
        (frames ++ [((beta ++ [WorkSym.index R d]), gamma)])
        [WorkSym.live B] form' ∧ g.Derives form form' := by
  apply h.appendInnermost ((beta ++ [WorkSym.index R d]), gamma)
  intro baseStack before baseForm segment
  exact segment.openPopLive hfree hedge hlater

/-! ## Form-preserving structural moves -/

/-- If the active segment loses a represented leading symbol, the same leading form symbol is
exposed through every enclosing frame. -/
public theorem NestedRep.unconsForm
    {g : IndexedGrammar T} [Fintype g.nt]
    {inherited : VisibleStack g} {frames : List (FrameBoundary g)}
    {current current' : List (WorkSym g)} {form : List g.ISym} {s : g.ISym}
    (h : NestedRep g inherited frames current form)
    (base : ∀ {baseStack before : VisibleStack g} {baseForm : List g.ISym},
      SegmentRep g baseStack current before baseForm →
        ∃ before' restForm,
          SegmentRep g baseStack current' before' restForm ∧
            baseForm = s :: restForm) :
    ∃ restForm, NestedRep g inherited frames current' restForm ∧
      form = s :: restForm := by
  induction h with
  | current segment =>
      rcases base segment with ⟨before', restForm, segment', hform⟩
      exact ⟨restForm, NestedRep.current segment', hform⟩
  | @frame inherited tailStack pendingStack pending suffix current frames
      suffixForm pendingForm innerForm suffixRep pendingRep pendingEnds innerRep ih =>
      rcases ih base with ⟨innerRest, innerRep', hinner⟩
      refine ⟨innerRest ++ pendingForm ++ suffixForm,
        NestedRep.frame suffixRep pendingRep pendingEnds innerRep', ?_⟩
      simp [hinner, List.append_assoc]

/-- Removing a matched terminal from the active segment removes exactly that leading terminal
from the represented sentential form. -/
public theorem NestedRep.matchTerminal
    {g : IndexedGrammar T} [Fintype g.nt]
    {inherited : VisibleStack g} {frames : List (FrameBoundary g)}
    {xs : List (WorkSym g)} {form : List g.ISym} {a : T}
    (h : NestedRep g inherited frames (WorkSym.terminal a :: xs) form) :
    ∃ restForm, NestedRep g inherited frames xs restForm ∧
      form = ISym.terminal a :: restForm := by
  apply h.unconsForm
  intro baseStack before baseForm segment
  cases segment with
  | terminal _ tail =>
      exact ⟨before, _, tail, rfl⟩

/-- An index token has no sentential-form symbol of its own, so erasing an allowed token leaves
the represented form unchanged. -/
public theorem NestedRep.eraseIndex
    {g : IndexedGrammar T} [Fintype g.nt]
    {inherited : VisibleStack g} {frames : List (FrameBoundary g)}
    {xs : List (WorkSym g)} {form : List g.ISym} {R : CFlag g} {d : IndexMark}
    (h : NestedRep g inherited frames (WorkSym.index R d :: xs) form) :
    NestedRep g inherited frames xs form := by
  apply h.mapCurrentSame
  intro baseStack before baseForm segment
  rcases segment.unconsIndex with ⟨stack, flags, rfl, denotes, tail⟩
  exact ⟨stack, tail⟩

/-- Collapse the innermost completed frame back into the active segment. -/
public theorem NestedRep.closeInnermost
    {g : IndexedGrammar T} [Fintype g.nt]
    {inherited : VisibleStack g} {frames : List (FrameBoundary g)}
    {current : List (WorkSym g)} {form : List g.ISym}
    (h : NestedRep g inherited frames current form)
    (hcurrent : current = []) (hne : frames ≠ []) :
    ∃ outer pending suffix,
      frames = outer ++ [(pending, suffix)] ∧
        NestedRep g inherited outer (pending ++ suffix) form := by
  induction h with
  | current segment => exact False.elim (hne rfl)
  | @frame inherited tailStack pendingStack pending suffix current frames
      suffixForm pendingForm innerForm suffixRep pendingRep pendingEnds innerRep ih =>
      cases frames with
      | nil =>
          subst current
          cases innerRep with
          | current innerSegment =>
              rcases (segmentRep_nil_iff g).mp innerSegment with
                ⟨hbefore, hinnerForm⟩
              subst innerForm
              have combined : SegmentRep g inherited (pending ++ suffix)
                  pendingStack (pendingForm ++ suffixForm) :=
                (segmentRep_append_iff pending suffix).mpr
                  ⟨tailStack, pendingForm, suffixForm,
                    suffixRep, pendingRep, rfl⟩
              exact ⟨[], pending, suffix, rfl, by
                simpa using NestedRep.current combined⟩
      | cons next rest =>
          rcases ih hcurrent (by simp) with
            ⟨outer, lastPending, lastSuffix, hframes, collapsed⟩
          refine ⟨(pending, suffix) :: outer, lastPending, lastSuffix, ?_, ?_⟩
          · rw [hframes]
            simp
          · exact NestedRep.frame suffixRep pendingRep pendingEnds collapsed

/-- Read a delimiter-free suffix split uniquely from the right. -/
public theorem append_delimiter_unique
    {α : Type} [DecidableEq α] {delimiter : α}
    {left₁ left₂ right₁ right₂ : List α}
    (hfree₁ : delimiter ∉ right₁) (hfree₂ : delimiter ∉ right₂)
    (heq : left₁ ++ delimiter :: right₁ = left₂ ++ delimiter :: right₂) :
    left₁ = left₂ ∧ right₁ = right₂ := by
  have hrev : right₁.reverse ++ delimiter :: left₁.reverse =
      right₂.reverse ++ delimiter :: left₂.reverse := by
    simpa [List.reverse_append] using congrArg List.reverse heq
  have first_unique : ∀ {xs ys p q : List α},
      delimiter ∉ xs → delimiter ∉ ys →
      xs ++ delimiter :: p = ys ++ delimiter :: q → xs = ys ∧ p = q := by
    intro xs
    induction xs with
    | nil =>
        intro ys p q hxs hys heq
        cases ys with
        | nil => simpa using heq
        | cons y ys =>
            simp only [List.nil_append, List.cons_append, List.cons.injEq] at heq
            exact False.elim (hys (by simp [heq.1]))
    | cons x xs ih =>
        intro ys p q hxs hys heq
        cases ys with
        | nil =>
            simp only [List.cons_append, List.nil_append, List.cons.injEq] at heq
            exact False.elim (hxs (by simp [heq.1]))
        | cons y ys =>
            simp only [List.cons_append, List.cons.injEq] at heq
            have hxs' : delimiter ∉ xs :=
              fun hm => hxs (List.mem_cons_of_mem x hm)
            have hys' : delimiter ∉ ys :=
              fun hm => hys (List.mem_cons_of_mem y hm)
            rcases ih hxs' hys' heq.2 with
              ⟨hxy, hpq⟩
            exact ⟨by simp [heq.1, hxy], hpq⟩
  rcases first_unique (by simpa using hfree₁) (by simpa using hfree₂) hrev with
    ⟨hright, hleft⟩
  exact ⟨by simpa using congrArg List.reverse hleft,
    by simpa using congrArg List.reverse hright⟩

/-! ## Inverting represented cursors -/

/-- The frame tail always starts with `¢`, or with `#` when there are no frames. -/
public theorem frameTail_head_boundary
    {g : IndexedGrammar T} (frames : List (FrameBoundary g))
    {z : WorkSym g} {zs : List (WorkSym g)}
    (h : frameTail g frames = z :: zs) :
    z = WorkSym.close ∨ z = WorkSym.hash := by
  unfold frameTail at h
  cases hrev : frames.reverse with
  | nil =>
      rw [hrev] at h
      simp at h
      exact Or.inr h.1.symm
  | cons boundary rest =>
      rw [hrev] at h
      rcases boundary with ⟨pending, suffix⟩
      simp at h
      exact Or.inl h.1.symm

/-- Reach the actual delimiter-free segment represented at the innermost frame. -/
public theorem NestedRep.innermostSegment
    {g : IndexedGrammar T} [Fintype g.nt]
    {inherited : VisibleStack g} {frames : List (FrameBoundary g)}
    {current : List (WorkSym g)} {form : List g.ISym}
    (h : NestedRep g inherited frames current form) :
    ∃ baseStack before baseForm,
      SegmentRep g baseStack current before baseForm := by
  induction h with
  | current segment => exact ⟨_, _, _, segment⟩
  | frame suffixRep pendingRep pendingEnds innerRep ih => exact ih

/-- An ordinary focused symbol must be the head of the represented active segment. -/
public theorem CursorLayout.current_cons_of_focus
    {g : IndexedGrammar T} [Fintype g.nt]
    {inherited : VisibleStack g} {frames : List (FrameBoundary g)}
    {current : List (WorkSym g)} {form : List g.ISym}
    {cursor : WorkCursor g} {x : WorkSym g}
    (hclose : x ≠ WorkSym.close) (hhash : x ≠ WorkSym.hash)
    (hlayout : CursorLayout g frames current cursor)
    (hnested : NestedRep g inherited frames current form)
    (hfocus : cursor.focus = x) :
    ∃ xs, current = x :: xs ∧ cursor.left = frameLeft g frames ∧
      cursor.right = xs ++ frameTail g frames := by
  rcases hlayout with ⟨z, zs, hword, hleft, hz, hright⟩
  rw [hfocus] at hz
  subst z
  cases current with
  | nil =>
      have hboundary := frameTail_head_boundary frames hword
      exact False.elim (hboundary.elim hclose hhash)
  | cons y ys =>
      simp only [List.cons_append, List.cons.injEq] at hword
      rcases hword with ⟨hy, htail⟩
      subst y
      exact ⟨ys, rfl, hleft, by simpa [htail] using hright⟩

/-- A boundary focus cannot belong to the delimiter-free active segment, so that segment is
empty. -/
public theorem CursorLayout.current_nil_of_boundary_focus
    {g : IndexedGrammar T} [Fintype g.nt]
    {inherited : VisibleStack g} {frames : List (FrameBoundary g)}
    {current : List (WorkSym g)} {form : List g.ISym}
    {cursor : WorkCursor g} {boundary : WorkSym g}
    (hboundary : boundary = WorkSym.close ∨ boundary = WorkSym.hash)
    (hlayout : CursorLayout g frames current cursor)
    (hnested : NestedRep g inherited frames current form)
    (hfocus : cursor.focus = boundary) : current = [] := by
  rcases hlayout with ⟨z, zs, hword, hleft, hz, hright⟩
  rw [hfocus] at hz
  subst z
  cases current with
  | nil => rfl
  | cons x xs =>
      simp only [List.cons_append, List.cons.injEq] at hword
      rcases hword with ⟨rfl, htail⟩
      rcases hnested.innermostSegment with ⟨base, before, baseForm, hseg⟩
      rcases hboundary with rfl | rfl <;> cases hseg

/-- Productive marking gives the exact left and right halves expected by the machine. -/
public theorem markedFrameLayout
    {g : IndexedGrammar T} [Fintype g.nt]
    {inherited : VisibleStack g} {frames : List (FrameBoundary g)}
    {current : List (WorkSym g)} {form : List g.ISym}
    {alpha : List (WorkSym g)}
    (hnested : NestedRep g inherited frames current form)
    (hleft : alpha ++ [WorkSym.dollar] = frameLeft g frames) :
    frameLeft g (markInnermostFrames frames) =
        markProductivePrefix alpha ++ [WorkSym.dollar] ∧
      frameTail g (markInnermostFrames frames) = frameTail g frames ∧
      NestedRep g inherited (markInnermostFrames frames) current form := by
  rcases hnested.markInnermostUsed with ⟨hnested', hprefix, htail⟩
  have hpref : alpha = framePrefix g frames := by
    apply List.append_cancel_right
    calc
      alpha ++ [WorkSym.dollar] = frameLeft g frames := hleft
      _ = framePrefix g frames ++ [WorkSym.dollar] := frameLeft_eq_prefix g frames
  refine ⟨?_, htail, hnested'⟩
  rw [frameLeft_eq_prefix, hprefix, ← hpref]

/-- Grammar/consumption alternatives produced by one composite move. -/
public def StepEffect (g : IndexedGrammar T) [Fintype g.nt] (input : List T)
    (c c' : Config g) (form form' : List g.ISym) : Prop :=
  (c'.inputPos = c.inputPos ∧ g.Derives form form') ∨
    ∃ a, form = ISym.terminal a :: form' ∧
      input[c.inputPos]? = some a ∧ c'.inputPos = c.inputPos + 1

end BlockDenotation

namespace ControlDenotation

open BlockDenotation

/-! ## Local grammar effects in the execution-order denotation -/

public theorem ExecRep.plainBinary
    {g : IndexedGrammar T} [Fintype g.nt]
    {left : List (WorkSym g)} {next : WorkSym g} {right : List (WorkSym g)}
    {form : List g.ISym} {A B C : g.nt} (haug : AugBinary g A B C)
    (h : ExecRep g ⟨left, WorkSym.plain A, next :: right⟩ form) :
    ∃ form', ExecRep g
        ⟨left, WorkSym.plain B, WorkSym.plain C :: next :: right⟩ form' ∧
      g.Derives form form' := by
  cases h with
  | plain _ actual rightRep decorates tail =>
      refine ⟨_, ExecRep.plain B actual (RightRep.plain C rightRep) decorates
        (ExecRep.plain C actual rightRep decorates tail), ?_⟩
      simpa using deri_with_suffix _ (augBinary_derives haug actual)

public theorem ExecRep.plainTerminal
    {g : IndexedGrammar T} [Fintype g.nt]
    {left : List (WorkSym g)} {next : WorkSym g} {right : List (WorkSym g)}
    {form : List g.ISym} {A : g.nt} {a : T} (haug : AugTerminal g A a)
    (h : ExecRep g ⟨left, WorkSym.plain A, next :: right⟩ form) :
    ∃ form', ExecRep g ⟨left, WorkSym.terminal a, next :: right⟩ form' ∧
      g.Derives form form' := by
  cases h with
  | plain _ actual rightRep decorates tail =>
      refine ⟨_, ExecRep.terminal a tail, ?_⟩
      simpa using deri_with_suffix _ (augTerminal_derives haug actual)

public theorem ExecRep.plainPushSkip
    {g : IndexedGrammar T} [Fintype g.nt]
    {left : List (WorkSym g)} {next : WorkSym g} {right : List (WorkSym g)}
    {form : List g.ISym} {A B : g.nt} {f : g.flag} (haug : AugPush g A B f)
    (h : ExecRep g ⟨left, WorkSym.plain A, next :: right⟩ form) :
    ∃ form', ExecRep g ⟨left, WorkSym.plain B, next :: right⟩ form' ∧
      g.Derives form form' := by
  cases h with
  | plain _ actual rightRep decorates tail =>
      refine ⟨_, ExecRep.plain B (f :: actual) rightRep
        (decorates.pushHidden f) tail, ?_⟩
      simpa using deri_with_suffix _ (augPush_derives haug actual)

public theorem ExecRep.plainPushUse
    {g : IndexedGrammar T} [Fintype g.nt]
    {left : List (WorkSym g)} {next : WorkSym g} {right : List (WorkSym g)}
    {form : List g.ISym} {A B : g.nt} {f : g.flag} (haug : AugPush g A B f)
    (h : ExecRep g ⟨left, WorkSym.plain A, next :: right⟩ form) :
    ∃ form', ExecRep g
        ⟨left, WorkSym.live B,
          WorkSym.index (cflagBase g f) .firstPending :: next :: right⟩ form' ∧
      g.Derives form form' := by
  cases h with
  | plain _ actual rightRep decorates tail =>
      let block : VisibleBlock g := ⟨[f], false⟩
      have indexedRep : RightRep g
          (WorkSym.index (cflagBase g f) .firstPending :: next :: right)
          (block :: _) :=
        RightRep.index (cflagBase g f) .firstPending [f]
          (CFlag.Denotes.base f) rightRep
      refine ⟨_, ExecRep.live B (f :: actual) indexedRep
        (decorates.pushFirst f) (ExecRep.index _ _ tail), ?_⟩
      simpa using deri_with_suffix _ (augPush_derives haug actual)

public theorem ExecRep.liveBinaryBoth
    {g : IndexedGrammar T} [Fintype g.nt]
    {left : List (WorkSym g)} {next : WorkSym g} {right : List (WorkSym g)}
    {form : List g.ISym} {A B C : g.nt} (haug : AugBinary g A B C)
    (h : ExecRep g ⟨left, WorkSym.live A, next :: right⟩ form) :
    ∃ form', ExecRep g
        ⟨left, WorkSym.live B, WorkSym.live C :: next :: right⟩ form' ∧
      g.Derives form form' := by
  cases h with
  | live _ actual rightRep decorates tail =>
      refine ⟨_, ExecRep.live B actual (RightRep.live C rightRep) decorates
        (ExecRep.live C actual rightRep decorates tail), ?_⟩
      simpa using deri_with_suffix _ (augBinary_derives haug actual)

public theorem ExecRep.liveBinaryLeft
    {g : IndexedGrammar T} [Fintype g.nt]
    {left : List (WorkSym g)} {next : WorkSym g} {right : List (WorkSym g)}
    {form : List g.ISym} {A B C : g.nt} (haug : AugBinary g A B C)
    (h : ExecRep g ⟨left, WorkSym.live A, next :: right⟩ form) :
    ∃ form', ExecRep g
        ⟨left, WorkSym.live B, WorkSym.plain C :: next :: right⟩ form' ∧
      g.Derives form form' := by
  cases h with
  | live _ actual rightRep decorates tail =>
      refine ⟨_, ExecRep.live B actual (RightRep.plain C rightRep) decorates
        (ExecRep.plain C actual rightRep decorates.toDecorates tail), ?_⟩
      simpa using deri_with_suffix _ (augBinary_derives haug actual)

public theorem ExecRep.liveBinaryRight
    {g : IndexedGrammar T} [Fintype g.nt]
    {left : List (WorkSym g)} {next : WorkSym g} {right : List (WorkSym g)}
    {form : List g.ISym} {A B C : g.nt} (haug : AugBinary g A B C)
    (h : ExecRep g ⟨left, WorkSym.live A, next :: right⟩ form) :
    ∃ form', ExecRep g
        ⟨left, WorkSym.plain B, WorkSym.live C :: next :: right⟩ form' ∧
      g.Derives form form' := by
  cases h with
  | live _ actual rightRep decorates tail =>
      refine ⟨_, ExecRep.plain B actual (RightRep.live C rightRep)
        decorates.toDecorates (ExecRep.live C actual rightRep decorates tail), ?_⟩
      simpa using deri_with_suffix _ (augBinary_derives haug actual)

public theorem ExecRep.livePushFresh
    {g : IndexedGrammar T} [Fintype g.nt]
    {left : List (WorkSym g)} {next : WorkSym g} {right : List (WorkSym g)}
    {form : List g.ISym} {A B : g.nt} {f : g.flag} (haug : AugPush g A B f)
    (h : ExecRep g ⟨left, WorkSym.live A, next :: right⟩ form) :
    ∃ form', ExecRep g
        ⟨left, WorkSym.live B,
          WorkSym.index (cflagBase g f) .laterPending :: next :: right⟩ form' ∧
      g.Derives form form' := by
  cases h with
  | live _ actual rightRep decorates tail =>
      have indexedRep := RightRep.index (cflagBase g f) .laterPending [f]
        (CFlag.Denotes.base f) rightRep
      refine ⟨_, ExecRep.live B (f :: actual) indexedRep
        (decorates.pushLater f) (ExecRep.index _ _ tail), ?_⟩
      simpa using deri_with_suffix _ (augPush_derives haug actual)

public theorem ExecRep.livePushCompress
    {g : IndexedGrammar T} [Fintype g.nt]
    {left : List (WorkSym g)} {next : WorkSym g} {right : List (WorkSym g)}
    {form : List g.ISym} {A B : g.nt} {f : g.flag} {R : CFlag g} {d : IndexMark}
    (haug : AugPush g A B f)
    (h : ExecRep g
      ⟨left, WorkSym.live A, WorkSym.index R d :: next :: right⟩ form) :
    ∃ form', ExecRep g
        ⟨left, WorkSym.live B,
          WorkSym.index (cflagComp g (cflagBase g f) R) d :: next :: right⟩ form' ∧
      g.Derives form form' := by
  cases h with
  | live _ actual rightRep decorates tail =>
      cases rightRep with
      | index _ _ flags denotes restRep =>
          cases tail with
          | index _ _ restExec =>
              have denotes' : CFlag.Denotes g (f :: flags)
                  (cflagComp g (cflagBase g f) R) := by
                simpa using CFlag.Denotes.comp (CFlag.Denotes.base f) denotes
              have indexedRep := RightRep.index
                (cflagComp g (cflagBase g f) R) d (f :: flags) denotes' restRep
              refine ⟨_, ExecRep.live B (f :: actual) indexedRep
                (decorates.pushCompress f) (ExecRep.index _ _ restExec), ?_⟩
              simpa using deri_with_suffix _ (augPush_derives haug actual)

/-! ## Close-crossing pop effects -/

public theorem ExecRep.invertLive
    {g : IndexedGrammar T} [Fintype g.nt]
    {left : List (WorkSym g)} {next : WorkSym g} {right : List (WorkSym g)}
    {form : List g.ISym} {A : g.nt}
    (h : ExecRep g ⟨left, WorkSym.live A, next :: right⟩ form) :
    ∃ actual stack tailForm,
      form = ISym.indexed A actual :: tailForm ∧
        RightRep g (next :: right) stack ∧
        LiveDecorates stack actual ∧
        ExecRep g ⟨left, next, right⟩ tailForm := by
  cases h with
  | live _ actual rightRep decorates tail =>
      exact ⟨actual, _, _, rfl, rightRep, decorates, tail⟩

public theorem ExecRep.popPlain
    {g : IndexedGrammar T} [Fintype g.nt]
    {alpha beta gamma : List (WorkSym g)} {form : List g.ISym}
    {R : CFlag g} {d : IndexMark} {A B : g.nt}
    (hfree : IndexFree beta) (hedge : R A B = true)
    (h : ExecRep g
      ⟨alpha ++ [WorkSym.dollar], WorkSym.live A,
        beta ++ WorkSym.index R d :: gamma⟩ form) :
    ∃ form', ExecRep g
        ⟨alpha ++ [WorkSym.dollar] ++ beta ++
            [WorkSym.index R d, WorkSym.dollar],
          WorkSym.plain B, WorkSym.close :: gamma⟩ form' ∧
      g.Derives form form' := by
  cases beta with
  | nil =>
      simp only [List.nil_append, List.append_nil] at h ⊢
      rcases h.invertLive with
        ⟨actual, stack, tailForm, rfl, rightRep, decorates, tailExec⟩
      cases rightRep with
      | index _ _ flags denotes gammaRep =>
          rcases decorates.popPlain with ⟨rest, hactual, restDecorates⟩
          subst actual
          have returnExec : ExecRep g
              ⟨alpha ++ [WorkSym.dollar] ++
                  [WorkSym.index R d, WorkSym.dollar],
                WorkSym.close, gamma⟩ tailForm := by
            simpa [List.append_assoc] using
              (ExecRep.returnFrame (alpha := alpha) (beta := [])
                (gamma := gamma) (by simp [DollarFree]) tailExec)
          refine ⟨_, ExecRep.plain B rest (RightRep.close gammaRep)
            restDecorates returnExec, ?_⟩
          simpa using deri_with_suffix tailForm (denotes.edge_derives hedge rest)
  | cons z zs =>
      simp only [List.cons_append] at h ⊢
      rcases h.invertLive with
        ⟨actual, stack, tailForm, rfl, rightRep, decorates, tailExec⟩
      rcases rightRep_append (xs := z :: zs)
        (ys := WorkSym.index R d :: gamma) rightRep with
        ⟨middle, selectedRep, betaRep⟩
      have hstack := betaRep.stack_eq_of_indexFree hfree
      subst middle
      cases selectedRep with
      | index _ _ flags denotes gammaRep =>
          rcases decorates.popPlain with ⟨rest, hactual, restDecorates⟩
          subst actual
          have hfreeTail : DollarFree (zs ++ [WorkSym.index R d]) := by
            intro hm
            simp only [List.mem_append, List.mem_singleton] at hm
            rcases hm with hm | hm
            · exact betaRep.dollarFree (List.mem_cons_of_mem z hm)
            · cases hm
          have tailExec' : ExecRep g
              ⟨alpha ++ [WorkSym.dollar], z,
                (zs ++ [WorkSym.index R d]) ++ gamma⟩ tailForm := by
            simpa [List.append_assoc] using tailExec
          have returnExec : ExecRep g
              ⟨alpha ++ [WorkSym.dollar] ++ z :: zs ++
                  [WorkSym.index R d, WorkSym.dollar],
                WorkSym.close, gamma⟩ tailForm := by
                simpa [List.append_assoc] using
                  (ExecRep.returnFrame (alpha := alpha)
                    (beta := zs ++ [WorkSym.index R d])
                    (gamma := gamma) hfreeTail tailExec')
          refine ⟨_, ExecRep.plain B rest (RightRep.close gammaRep)
            restDecorates returnExec, ?_⟩
          simpa using deri_with_suffix tailForm (denotes.edge_derives hedge rest)

public theorem ExecRep.popLive
    {g : IndexedGrammar T} [Fintype g.nt]
    {alpha beta gamma : List (WorkSym g)} {form : List g.ISym}
    {R : CFlag g} {d : IndexMark} {A B : g.nt}
    (hfree : IndexFree beta) (hedge : R A B = true) (hlater : d.later = true)
    (h : ExecRep g
      ⟨alpha ++ [WorkSym.dollar], WorkSym.live A,
        beta ++ WorkSym.index R d :: gamma⟩ form) :
    ∃ form', ExecRep g
        ⟨alpha ++ [WorkSym.dollar] ++ beta ++
            [WorkSym.index R d, WorkSym.dollar],
          WorkSym.live B, WorkSym.close :: gamma⟩ form' ∧
      g.Derives form form' := by
  cases beta with
  | nil =>
      simp only [List.nil_append, List.append_nil] at h ⊢
      rcases h.invertLive with
        ⟨actual, stack, tailForm, rfl, rightRep, decorates, tailExec⟩
      cases rightRep with
      | index _ _ flags denotes gammaRep =>
          rcases decorates.popLive hlater with ⟨rest, hactual, restDecorates⟩
          subst actual
          have returnExec : ExecRep g
              ⟨alpha ++ [WorkSym.dollar] ++
                  [WorkSym.index R d, WorkSym.dollar],
                WorkSym.close, gamma⟩ tailForm := by
            simpa [List.append_assoc] using
              (ExecRep.returnFrame (alpha := alpha) (beta := [])
                (gamma := gamma) (by simp [DollarFree]) tailExec)
          refine ⟨_, ExecRep.live B rest (RightRep.close gammaRep)
            restDecorates returnExec, ?_⟩
          simpa using deri_with_suffix tailForm (denotes.edge_derives hedge rest)

  | cons z zs =>
      simp only [List.cons_append] at h ⊢
      rcases h.invertLive with
        ⟨actual, stack, tailForm, rfl, rightRep, decorates, tailExec⟩
      rcases rightRep_append (xs := z :: zs)
        (ys := WorkSym.index R d :: gamma) rightRep with
        ⟨middle, selectedRep, betaRep⟩
      have hstack := betaRep.stack_eq_of_indexFree hfree
      subst middle
      cases selectedRep with
      | index _ _ flags denotes gammaRep =>
          rcases decorates.popLive hlater with ⟨rest, hactual, restDecorates⟩
          subst actual
          have hfreeTail : DollarFree (zs ++ [WorkSym.index R d]) := by
            intro hm
            simp only [List.mem_append, List.mem_singleton] at hm
            rcases hm with hm | hm
            · exact betaRep.dollarFree (List.mem_cons_of_mem z hm)
            · cases hm
          have tailExec' : ExecRep g
              ⟨alpha ++ [WorkSym.dollar], z,
                (zs ++ [WorkSym.index R d]) ++ gamma⟩ tailForm := by
            simpa [List.append_assoc] using tailExec
          have returnExec : ExecRep g
              ⟨alpha ++ [WorkSym.dollar] ++ z :: zs ++
                  [WorkSym.index R d, WorkSym.dollar],
                WorkSym.close, gamma⟩ tailForm := by
            simpa [List.append_assoc] using
              (ExecRep.returnFrame (alpha := alpha)
                (beta := zs ++ [WorkSym.index R d])
                (gamma := gamma) hfreeTail tailExec')
          refine ⟨_, ExecRep.live B rest (RightRep.close gammaRep)
            restDecorates returnExec, ?_⟩
          simpa using deri_with_suffix tailForm (denotes.edge_derives hedge rest)

/-! ## Structural execution effects -/

public theorem ExecRep.matchTerminal
    {g : IndexedGrammar T} [Fintype g.nt]
    {left : List (WorkSym g)} {next : WorkSym g} {right : List (WorkSym g)}
    {form : List g.ISym} {a : T}
    (h : ExecRep g ⟨left, WorkSym.terminal a, next :: right⟩ form) :
    ∃ restForm, form = ISym.terminal a :: restForm ∧
      ExecRep g ⟨left, next, right⟩ restForm := by
  cases h with
  | terminal _ tail => exact ⟨_, rfl, tail⟩

public theorem ExecRep.eraseIndex
    {g : IndexedGrammar T} [Fintype g.nt]
    {left : List (WorkSym g)} {next : WorkSym g} {right : List (WorkSym g)}
    {form : List g.ISym} {R : CFlag g} {d : IndexMark}
    (h : ExecRep g ⟨left, WorkSym.index R d, next :: right⟩ form) :
    ExecRep g ⟨left, next, right⟩ form := by
  cases h with
  | index _ _ tail => exact tail

/-- Generic inversion at a close focus. -/
public theorem ExecRep.invertClose
    {g : IndexedGrammar T} [Fintype g.nt]
    {left right : List (WorkSym g)} {form : List g.ISym}
    (h : ExecRep g ⟨left, WorkSym.close, right⟩ form) :
    ∃ alpha beta Z,
      DollarFree beta ∧
        left = alpha ++ [WorkSym.dollar, Z] ++ beta ++ [WorkSym.dollar] ∧
        ExecRep g ⟨alpha ++ [WorkSym.dollar], Z, beta ++ right⟩ form := by
  cases h with
  | returnFrame hfree tail => exact ⟨_, _, _, hfree, rfl, tail⟩

public theorem ExecRep.focus_ne_dollar
    {g : IndexedGrammar T} [Fintype g.nt]
    {cursor : WorkCursor g} {form : List g.ISym}
    (h : ExecRep g cursor form) : cursor.focus ≠ WorkSym.dollar := by
  cases h <;> simp

public theorem ExecRep.right_ne_nil_of_plain_focus
    {g : IndexedGrammar T} [Fintype g.nt]
    {cursor : WorkCursor g} {form : List g.ISym} {A : g.nt}
    (h : ExecRep g cursor form) (hfocus : cursor.focus = WorkSym.plain A) :
    cursor.right ≠ [] := by
  induction h <;> simp_all

public theorem ExecRep.right_ne_nil_of_index_focus
    {g : IndexedGrammar T} [Fintype g.nt]
    {cursor : WorkCursor g} {form : List g.ISym} {R : CFlag g} {d : IndexMark}
    (h : ExecRep g cursor form) (hfocus : cursor.focus = WorkSym.index R d) :
    cursor.right ≠ [] := by
  induction h <;> simp_all

/-- Consume an adjacent ephemeral block and erase its representation immediately.  Unlike the
framed pop, no saved index is needed because this block is owned exclusively by the active
task. -/
public theorem ExecRep.popPlainErase
    {g : IndexedGrammar T} [Fintype g.nt]
    {alpha gamma : List (WorkSym g)} {form : List g.ISym}
    {R : CFlag g} {d : IndexMark} {A B : g.nt}
    (hedge : R A B = true)
    (h : ExecRep g
      ⟨alpha ++ [WorkSym.dollar], WorkSym.live A,
        WorkSym.index R d :: gamma⟩ form) :
    ∃ form', ExecRep g
        ⟨alpha ++ [WorkSym.dollar], WorkSym.plain B, gamma⟩ form' ∧
      g.Derives form form' := by
  rcases h.invertLive with
    ⟨actual, stack, tailForm, rfl, rightRep, decorates, tailExec⟩
  cases rightRep with
  | index _ _ flags denotes gammaRep =>
      rcases decorates.popPlain with ⟨rest, hactual, restDecorates⟩
      subst actual
      have hgamma : gamma ≠ [] := tailExec.right_ne_nil_of_index_focus rfl
      cases gamma with
      | nil => exact False.elim (hgamma rfl)
      | cons next right =>
          have tailExec' : ExecRep g
              ⟨alpha ++ [WorkSym.dollar], next, right⟩ tailForm :=
            tailExec.eraseIndex
          refine ⟨_, ExecRep.plain B rest gammaRep restDecorates tailExec', ?_⟩
          simpa using deri_with_suffix tailForm (denotes.edge_derives hedge rest)

/-- Live counterpart of `popPlainErase` for a lower represented stack that remains active. -/
public theorem ExecRep.popLiveErase
    {g : IndexedGrammar T} [Fintype g.nt]
    {alpha gamma : List (WorkSym g)} {form : List g.ISym}
    {R : CFlag g} {d : IndexMark} {A B : g.nt}
    (hedge : R A B = true) (hlater : d.later = true)
    (h : ExecRep g
      ⟨alpha ++ [WorkSym.dollar], WorkSym.live A,
        WorkSym.index R d :: gamma⟩ form) :
    ∃ form', ExecRep g
        ⟨alpha ++ [WorkSym.dollar], WorkSym.live B, gamma⟩ form' ∧
      g.Derives form form' := by
  rcases h.invertLive with
    ⟨actual, stack, tailForm, rfl, rightRep, decorates, tailExec⟩
  cases rightRep with
  | index _ _ flags denotes gammaRep =>
      rcases decorates.popLive hlater with ⟨rest, hactual, restDecorates⟩
      subst actual
      have hgamma : gamma ≠ [] := tailExec.right_ne_nil_of_index_focus rfl
      cases gamma with
      | nil => exact False.elim (hgamma rfl)
      | cons next right =>
          have tailExec' : ExecRep g
              ⟨alpha ++ [WorkSym.dollar], next, right⟩ tailForm :=
            tailExec.eraseIndex
          refine ⟨_, ExecRep.live B rest gammaRep restDecorates tailExec', ?_⟩
          simpa using deri_with_suffix tailForm (denotes.edge_derives hedge rest)

public theorem ExecRep.returnFrameSound
    {g : IndexedGrammar T} [Fintype g.nt]
    {alpha beta gamma : List (WorkSym g)} {Z : WorkSym g}
    {form : List g.ISym}
    (hZ : Z ≠ WorkSym.dollar) (hfree : DollarFree beta)
    (h : ExecRep g
      ⟨alpha ++ [WorkSym.dollar, Z] ++ beta ++ [WorkSym.dollar],
        WorkSym.close, gamma⟩ form) :
    ExecRep g ⟨alpha ++ [WorkSym.dollar], Z, beta ++ gamma⟩ form := by
  rcases h.invertClose with
    ⟨alpha', beta', Z', hfree', hleft, tail⟩
  have hZ' : Z' ≠ WorkSym.dollar := tail.focus_ne_dollar
  have hsuffix : DollarFree (Z :: beta) := by
    intro hm
    simp only [List.mem_cons] at hm
    exact hm.elim (fun heq => hZ heq.symm) hfree
  have hsuffix' : DollarFree (Z' :: beta') := by
    intro hm
    simp only [List.mem_cons] at hm
    exact hm.elim (fun heq => hZ' heq.symm) hfree'
  have hwithoutLast :
      alpha ++ WorkSym.dollar :: Z :: beta =
        alpha' ++ WorkSym.dollar :: Z' :: beta' := by
    apply List.append_cancel_right (bs := [WorkSym.dollar])
    simpa [List.append_assoc] using hleft
  rcases BlockDenotation.append_delimiter_unique
      hsuffix hsuffix' hwithoutLast with ⟨halpha, hsaved⟩
  simp only [List.cons.injEq] at hsaved
  rcases hsaved with ⟨hZeq, hbeta⟩
  subst alpha'
  subst Z'
  subst beta'
  exact tail

/-! ## Every finite certificate is denotationally sound -/

public def StepEffect (g : IndexedGrammar T) [Fintype g.nt] (input : List T)
    (c c' : Config g) (form form' : List g.ISym) : Prop :=
  (c'.inputPos = c.inputPos ∧ g.Derives form form') ∨
    ∃ a, form = ISym.terminal a :: form' ∧
      input[c.inputPos]? = some a ∧ c'.inputPos = c.inputPos + 1

public theorem certStep_preserves_represents
    {g : IndexedGrammar T} [Fintype g.nt] (input : List T)
    (cert : CompositeCert g) {c c' : Config g} {form : List g.ISym}
    (hstep : CertStep g input cert c c')
    (hrep : Config.Represents c form) :
    ∃ form', Config.Represents c' form' ∧ StepEffect g input c c' form form' := by
  change ExecRep g (normalizeCursor c.work) form at hrep
  cases cert with
  | plainBinary A B C =>
      rcases hstep with ⟨haug, alpha, beta, hc, hc'⟩
      rw [hc] at hrep
      cases beta with
      | nil =>
          simp only [normalizeCursor, List.map_append, List.map_singleton,
            normalizeWorkSym] at hrep
          exact False.elim (hrep.right_ne_nil_of_plain_focus rfl rfl)
      | cons next right =>
          simp only [normalizeCursor, List.map_append, List.map_singleton,
            List.map_cons, normalizeWorkSym] at hrep
          rcases hrep.plainBinary haug with ⟨form', hrep', hderiv⟩
          refine ⟨form', ?_, Or.inl ⟨?_, hderiv⟩⟩
          · change ExecRep g (normalizeCursor c'.work) form'
            rw [hc']
            simpa only [normalizeCursor, List.map_append, List.map_singleton,
              List.map_cons, normalizeWorkSym,
              normalizeWorkSym_markProductivePrefix] using hrep'
          · rw [hc']
  | plainTerminal A a =>
      rcases hstep with ⟨haug, alpha, beta, hc, hc'⟩
      rw [hc] at hrep
      cases beta with
      | nil =>
          simp only [normalizeCursor, List.map_append, List.map_singleton,
            normalizeWorkSym] at hrep
          exact False.elim (hrep.right_ne_nil_of_plain_focus rfl rfl)
      | cons next right =>
          simp only [normalizeCursor, List.map_append, List.map_singleton,
            List.map_cons, normalizeWorkSym] at hrep
          rcases hrep.plainTerminal haug with ⟨form', hrep', hderiv⟩
          refine ⟨form', ?_, Or.inl ⟨?_, hderiv⟩⟩
          · change ExecRep g (normalizeCursor c'.work) form'
            rw [hc']
            simpa only [normalizeCursor, List.map_append, List.map_singleton,
              List.map_cons, normalizeWorkSym,
              normalizeWorkSym_markProductivePrefix] using hrep'
          · rw [hc']
  | plainPushSkip A B f =>
      rcases hstep with ⟨haug, alpha, beta, hc, hc'⟩
      rw [hc] at hrep
      cases beta with
      | nil =>
          simp only [normalizeCursor, List.map_append, List.map_singleton,
            normalizeWorkSym] at hrep
          exact False.elim (hrep.right_ne_nil_of_plain_focus rfl rfl)
      | cons next right =>
          simp only [normalizeCursor, List.map_append, List.map_singleton,
            List.map_cons, normalizeWorkSym] at hrep
          rcases hrep.plainPushSkip haug with ⟨form', hrep', hderiv⟩
          refine ⟨form', ?_, Or.inl ⟨?_, hderiv⟩⟩
          · change ExecRep g (normalizeCursor c'.work) form'
            rw [hc']
            simpa only [normalizeCursor, List.map_append, List.map_singleton,
              List.map_cons, normalizeWorkSym,
              normalizeWorkSym_markProductivePrefix] using hrep'
          · rw [hc']
  | plainPushUse A B f =>
      rcases hstep with ⟨haug, alpha, beta, hc, hc'⟩
      rw [hc] at hrep
      cases beta with
      | nil =>
          simp only [normalizeCursor, List.map_append, List.map_singleton,
            normalizeWorkSym] at hrep
          exact False.elim (hrep.right_ne_nil_of_plain_focus rfl rfl)
      | cons next right =>
          simp only [normalizeCursor, List.map_append, List.map_singleton,
            List.map_cons, normalizeWorkSym] at hrep
          rcases hrep.plainPushUse haug with ⟨form', hrep', hderiv⟩
          refine ⟨form', ?_, Or.inl ⟨?_, hderiv⟩⟩
          · change ExecRep g (normalizeCursor c'.work) form'
            rw [hc']
            simpa only [normalizeCursor, List.map_append, List.map_singleton,
              List.map_cons, normalizeWorkSym, normalizeIndexMark] using hrep'
          · rw [hc']
  | liveBinaryBoth A B C =>
      rcases hstep with ⟨haug, alpha, Z, beta, hc, hc'⟩
      rw [hc] at hrep
      simp only [normalizeCursor, List.map_append, List.map_singleton,
        List.map_cons, normalizeWorkSym] at hrep
      rcases hrep.liveBinaryBoth haug with ⟨form', hrep', hderiv⟩
      refine ⟨form', ?_, Or.inl ⟨?_, hderiv⟩⟩
      · change ExecRep g (normalizeCursor c'.work) form'
        rw [hc']
        simpa only [normalizeCursor, List.map_append, List.map_singleton,
          List.map_cons, normalizeWorkSym,
          normalizeWorkSym_markProductivePrefix] using hrep'
      · rw [hc']
  | liveBinaryLeft A B C =>
      rcases hstep with ⟨haug, alpha, Z, beta, hc, hc'⟩
      rw [hc] at hrep
      simp only [normalizeCursor, List.map_append, List.map_singleton,
        List.map_cons, normalizeWorkSym] at hrep
      rcases hrep.liveBinaryLeft haug with ⟨form', hrep', hderiv⟩
      refine ⟨form', ?_, Or.inl ⟨?_, hderiv⟩⟩
      · change ExecRep g (normalizeCursor c'.work) form'
        rw [hc']
        simpa only [normalizeCursor, List.map_append, List.map_singleton,
          List.map_cons, normalizeWorkSym,
          normalizeWorkSym_markProductivePrefix] using hrep'
      · rw [hc']
  | liveBinaryRight A B C =>
      rcases hstep with ⟨haug, alpha, Z, beta, hc, hc'⟩
      rw [hc] at hrep
      simp only [normalizeCursor, List.map_append, List.map_singleton,
        List.map_cons, normalizeWorkSym] at hrep
      rcases hrep.liveBinaryRight haug with ⟨form', hrep', hderiv⟩
      refine ⟨form', ?_, Or.inl ⟨?_, hderiv⟩⟩
      · change ExecRep g (normalizeCursor c'.work) form'
        rw [hc']
        simpa only [normalizeCursor, List.map_append, List.map_singleton,
          List.map_cons, normalizeWorkSym,
          normalizeWorkSym_markProductivePrefix] using hrep'
      · rw [hc']
  | livePushFresh A B f =>
      rcases hstep with ⟨haug, alpha, Z, beta, hc, hc'⟩
      rw [hc] at hrep
      simp only [normalizeCursor, List.map_append, List.map_singleton,
        List.map_cons, normalizeWorkSym] at hrep
      rcases hrep.livePushFresh haug with ⟨form', hrep', hderiv⟩
      refine ⟨form', ?_, Or.inl ⟨?_, hderiv⟩⟩
      · change ExecRep g (normalizeCursor c'.work) form'
        rw [hc']
        simpa only [normalizeCursor, List.map_append, List.map_singleton,
          List.map_cons, normalizeWorkSym, normalizeIndexMark] using hrep'
      · rw [hc']
  | livePushCompress A B f R d =>
      rcases hstep with ⟨haug, _hne, alpha, beta, hc, hc'⟩
      rw [hc] at hrep
      cases beta with
      | nil =>
          simp only [normalizeCursor, List.map_append, List.map_singleton,
            normalizeWorkSym] at hrep
          rcases hrep.invertLive with
            ⟨actual, stack, tailForm, hform, rightRep, decorates, tailExec⟩
          exact False.elim (tailExec.right_ne_nil_of_index_focus rfl rfl)
      | cons next right =>
          simp only [normalizeCursor, List.map_append, List.map_singleton,
            List.map_cons, normalizeWorkSym] at hrep
          rcases hrep.livePushCompress haug with ⟨form', hrep', hderiv⟩
          refine ⟨form', ?_, Or.inl ⟨?_, hderiv⟩⟩
          · change ExecRep g (normalizeCursor c'.work) form'
            rw [hc']
            simpa only [normalizeCursor, List.map_append, List.map_singleton,
              List.map_cons, normalizeWorkSym] using hrep'
          · rw [hc']
  | popPlain R d A B =>
      rcases hstep with ⟨hedge, hframed | herase⟩
      · rcases hframed with ⟨alpha, beta, gamma, hfree, hc, hc'⟩
        rw [hc] at hrep
        simp only [normalizeCursor, List.map_append, List.map_singleton,
          List.map_cons, normalizeWorkSym] at hrep
        have hfree' : IndexFree (beta.map normalizeWorkSym) :=
          (indexFree_map_normalizeWorkSym beta).2 hfree
        rcases hrep.popPlain hfree' hedge with ⟨form', hrep', hderiv⟩
        refine ⟨form', ?_, Or.inl ⟨?_, hderiv⟩⟩
        · change ExecRep g (normalizeCursor c'.work) form'
          rw [hc']
          simpa only [normalizeCursor, List.map_append, List.map_singleton,
            List.map_cons, List.map_nil, List.nil_append, List.append_nil,
            List.singleton_append, List.cons_append, List.append_assoc,
            normalizeWorkSym, normalizeIndexMark,
            normalizeIndexMark_markUsed, IndexMark.later_markUsed] using hrep'
        · rw [hc']
      · rcases herase with ⟨alpha, gamma, hc, hc'⟩
        rw [hc] at hrep
        simp only [normalizeCursor, List.map_append, List.map_singleton,
          List.map_cons, normalizeWorkSym] at hrep
        rcases hrep.popPlainErase hedge with ⟨form', hrep', hderiv⟩
        refine ⟨form', ?_, Or.inl ⟨?_, hderiv⟩⟩
        · change ExecRep g (normalizeCursor c'.work) form'
          rw [hc']
          simpa only [normalizeCursor, List.map_append, List.map_singleton,
            List.map_cons, normalizeWorkSym] using hrep'
        · rw [hc']
  | popLive R d A B =>
      rcases hstep with ⟨hedge, hlater, hframed | herase⟩
      · rcases hframed with ⟨alpha, beta, gamma, hfree, hc, hc'⟩
        rw [hc] at hrep
        simp only [normalizeCursor, List.map_append, List.map_singleton,
          List.map_cons, normalizeWorkSym] at hrep
        have hfree' : IndexFree (beta.map normalizeWorkSym) :=
          (indexFree_map_normalizeWorkSym beta).2 hfree
        have hlater' : (normalizeIndexMark d).later = true := by simpa using hlater
        rcases hrep.popLive hfree' hedge hlater' with ⟨form', hrep', hderiv⟩
        refine ⟨form', ?_, Or.inl ⟨?_, hderiv⟩⟩
        · change ExecRep g (normalizeCursor c'.work) form'
          rw [hc']
          simpa only [normalizeCursor, List.map_append, List.map_singleton,
            List.map_cons, List.map_nil, List.nil_append, List.append_nil,
            List.singleton_append, List.cons_append, List.append_assoc,
            normalizeWorkSym, normalizeIndexMark,
            normalizeIndexMark_markUsed, IndexMark.later_markUsed] using hrep'
        · rw [hc']
      · rcases herase with ⟨alpha, gamma, hc, hc'⟩
        rw [hc] at hrep
        simp only [normalizeCursor, List.map_append, List.map_singleton,
          List.map_cons, normalizeWorkSym] at hrep
        have hlater' : (normalizeIndexMark d).later = true := by simpa using hlater
        rcases hrep.popLiveErase hedge hlater' with ⟨form', hrep', hderiv⟩
        refine ⟨form', ?_, Or.inl ⟨?_, hderiv⟩⟩
        · change ExecRep g (normalizeCursor c'.work) form'
          rw [hc']
          simpa only [normalizeCursor, List.map_append, List.map_singleton,
            List.map_cons, normalizeWorkSym] using hrep'
        · rw [hc']
  | matchTerminal a =>
      rcases hstep with ⟨hinput, alpha, Z, beta, hc, hc'⟩
      rw [hc] at hrep
      simp only [normalizeCursor, List.map_append, List.map_singleton,
        List.map_cons, normalizeWorkSym] at hrep
      rcases hrep.matchTerminal with ⟨restForm, hform, hrep'⟩
      refine ⟨restForm, ?_, Or.inr ⟨a, hform, hinput, ?_⟩⟩
      · change ExecRep g (normalizeCursor c'.work) restForm
        rw [hc']
        simpa only [normalizeCursor, List.map_append, List.map_singleton,
          List.map_cons, normalizeWorkSym] using hrep'
      · rw [hc']
  | eraseIndex R d =>
      rcases hstep with ⟨_herase, alpha, Z, beta, hc, hc'⟩
      rw [hc] at hrep
      simp only [normalizeCursor, List.map_append, List.map_singleton,
        List.map_cons, normalizeWorkSym] at hrep
      have hrep' := hrep.eraseIndex
      refine ⟨form, ?_, Or.inl ⟨?_, deri_self g form⟩⟩
      · change ExecRep g (normalizeCursor c'.work) form
        rw [hc']
        simpa only [normalizeCursor, List.map_append, List.map_singleton,
          List.map_cons, normalizeWorkSym] using hrep'
      · rw [hc']
  | returnFrame =>
      rcases hstep with ⟨alpha, Z, beta, gamma, hZ, hfree, hc, hc'⟩
      rw [hc] at hrep
      simp only [normalizeCursor, List.map_append, List.map_singleton,
        List.map_cons, normalizeWorkSym] at hrep
      have hZ' : normalizeWorkSym Z ≠ WorkSym.dollar :=
        (normalizeWorkSym_ne_dollar_iff Z).2 hZ
      have hfree' : DollarFree (beta.map normalizeWorkSym) :=
        (dollarFree_map_normalizeWorkSym beta).2 hfree
      have hrep' := hrep.returnFrameSound hZ' hfree'
      refine ⟨form, ?_, Or.inl ⟨?_, deri_self g form⟩⟩
      · change ExecRep g (normalizeCursor c'.work) form
        rw [hc']
        simpa only [normalizeCursor, List.map_append, List.map_singleton,
          List.map_cons, normalizeWorkSym] using hrep'
      · rw [hc']

/-! ## Forward derivation invariant and accepting-run soundness -/

/-- The consumed input prefix followed by the execution-ordered remaining form is derivable from
the grammar start symbol. -/
public def ForwardInvariant (g : IndexedGrammar T) [Fintype g.nt]
    (input : List T) (c : Config g) : Prop :=
  ∃ form,
    Config.Represents c form ∧
      c.inputPos ≤ input.length ∧
      g.Derives [ISym.indexed g.initial []]
        ((input.take c.inputPos).map ISym.terminal ++ form)

public theorem initial_forwardInvariant
    (g : IndexedGrammar T) [Fintype g.nt] (input : List T) :
    ForwardInvariant g input (initialConfig g) := by
  refine ⟨[ISym.indexed g.initial []], initialConfig_represents g, by simp [initialConfig], ?_⟩
  simpa [initialConfig] using
    (deri_self g [ISym.indexed g.initial []])

public theorem compositeStep_preserves_represents
    {g : IndexedGrammar T} [Fintype g.nt] (input : List T)
    {c c' : Config g} {form : List g.ISym}
    (hstep : CompositeStep g input c c')
    (hrep : Config.Represents c form) :
    ∃ form', Config.Represents c' form' ∧ StepEffect g input c c' form form' := by
  rcases hstep with ⟨cert, hcert⟩
  exact certStep_preserves_represents input cert hcert hrep

public theorem compositeStep_preserves_forwardInvariant
    {g : IndexedGrammar T} [Fintype g.nt] (input : List T)
    {c c' : Config g} (hstep : CompositeStep g input c c')
    (hinv : ForwardInvariant g input c) : ForwardInvariant g input c' := by
  rcases hinv with ⟨form, hrep, hpos, hderiv⟩
  rcases compositeStep_preserves_represents input hstep hrep with
    ⟨form', hrep', heffect⟩
  rcases heffect with ⟨hposEq, hgrammar⟩ | ⟨a, hform, hinput, hposEq⟩
  · refine ⟨form', hrep', ?_, ?_⟩
    · rw [hposEq]
      exact hpos
    · rw [hposEq]
      exact hderiv.trans
        (deri_with_prefix ((input.take c.inputPos).map ISym.terminal) hgrammar)
  · have hlt : c.inputPos < input.length :=
      (List.getElem?_eq_some_iff.mp hinput).choose
    refine ⟨form', hrep', ?_, ?_⟩
    · rw [hposEq]
      exact Nat.succ_le_of_lt hlt
    · rw [hposEq]
      rw [hform] at hderiv
      simpa [List.take_succ, hinput, List.map_append, List.append_assoc] using hderiv

public theorem reachable_forwardInvariant
    {g : IndexedGrammar T} [Fintype g.nt] (input : List T)
    {c : Config g}
    (hreach : Relation.ReflTransGen (CompositeStep g input) (initialConfig g) c) :
    ForwardInvariant g input c := by
  induction hreach with
  | refl => exact initial_forwardInvariant g input
  | tail _ hstep ih =>
      exact compositeStep_preserves_forwardInvariant input hstep ih

public theorem finalConfig_represents_only_nil
    (g : IndexedGrammar T) [Fintype g.nt] (n : ℕ) {form : List g.ISym}
    (hrep : Config.Represents (finalConfig g n) form) : form = [] := by
  change ExecRep g ⟨[WorkSym.dollar], WorkSym.hash, []⟩ form at hrep
  have hash_form_nil : ∀ {cursor : WorkCursor g} {w : List g.ISym},
      ExecRep g cursor w → cursor.focus = WorkSym.hash → w = [] := by
    intro cursor w h
    induction h <;> simp_all
  exact hash_form_nil hrep rfl

/-- Every accepting run of the composite machine spells a genuine indexed-grammar derivation. -/
public theorem ahoMachine_sound
    {g : IndexedGrammar T} [Fintype g.nt] {input : List T}
    (hreach : Relation.ReflTransGen (CompositeStep g input)
      (initialConfig g) (finalConfig g input.length)) :
    g.Generates input := by
  rcases reachable_forwardInvariant input hreach with
    ⟨form, hrep, _hpos, hderiv⟩
  have hform : form = [] := finalConfig_represents_only_nil g input.length hrep
  subst form
  simpa [Generates, finalConfig] using hderiv

end ControlDenotation
end Aho
end IndexedGrammar
