module

public import Langlib.Grammars.Indexed.NormalForm.Aho.Machine.InputSafety
public import Langlib.Grammars.Indexed.NormalForm.Aho.Machine.PaddedRows

@[expose]
public section

/-!
# Padded-row reachability for Aho's machine

This file proves that the semantic padded-row presentation is neither weaker nor stronger than
the bounded composite machine.  In particular, a path starting at a raw input row can initialize
only once.  Every later running row uniquely determines both the immutable input word and the
complete marked machine configuration.
-/

open List Relation

variable {T : Type}

namespace IndexedGrammar
namespace Aho

/-- The nonempty language accepted by semantic padded-row reachability. -/
public def paddedReachLanguage (g : IndexedGrammar T) [Fintype g.nt] : _root_.Language T :=
  fun w => w ≠ [] ∧ ∃ row,
    Relation.ReflTransGen (PaddedRowStep g) (inputRow g w) row ∧ FinalRow g row

/-- Raw input rows retain their input word injectively. -/
public theorem inputRow_injective (g : IndexedGrammar T) :
    Function.Injective (inputRow g) := by
  intro w u h
  exact (List.map_injective_iff.mpr (fun _ _ hxy => RowCell.input.inj hxy)) h

/-- A nonempty raw input row cannot also be a packed running row. -/
public theorem inputRow_ne_encodeRunRow_of_ne_nil (g : IndexedGrammar T)
    (w : List T) (hw : w ≠ []) (u : List T) (c : Config g) :
    inputRow g w ≠ encodeRunRow g u c := by
  intro h
  cases w with
  | nil => exact hw rfl
  | cons a w =>
      cases u with
      | nil =>
          have hlen := congrArg List.length h
          simp at hlen
      | cons b u =>
          simp only [inputRow, List.map_cons, encodeRunRow, encodeRunRowFrom] at h
          exact RowCell.input_ne_run a _ (List.cons.inj h).1

/-- The initial marked work word fits in the twenty-one-slot block of every nonempty input. -/
public theorem initialConfig_within_padded_bound (g : IndexedGrammar T)
    (w : List T) (hw : w ≠ []) :
    (initialConfig g).Within (w.length * workWidth) := by
  have hn : 0 < w.length := List.length_pos_of_ne_nil hw
  simp [Config.Within, initialConfig, WorkCursor.word, workWidth]
  omega

/-- The final marked work word fits in the twenty-one-slot block of every nonempty input. -/
public theorem finalConfig_within_padded_bound (g : IndexedGrammar T)
    (w : List T) (hw : w ≠ []) :
    (finalConfig g w.length).Within (w.length * workWidth) := by
  have hn : 0 < w.length := List.length_pos_of_ne_nil hw
  simp [Config.Within, finalConfig, WorkCursor.word, workWidth]
  omega

/-- Encode a bounded composite run as a semantic padded-composite row path.  Input-head safety
is threaded through the induction because it is a semantic consequence of reachability rather
than part of `BoundedReaches`'s stored edge predicate. -/
private theorem encode_boundedRun_to_paddedComposite
    {g : IndexedGrammar T} [Fintype g.nt] (w : List T) (hw : w ≠ [])
    {bound : ℕ} {c c' : Config g}
    (hbound : bound = w.length * workWidth)
    (hreach : Relation.ReflTransGen
      (fun x y => CompositeStep g w x y ∧ x.Within bound ∧ y.Within bound) c c')
    (hin : c.InputWithin w) :
    Relation.ReflTransGen (PaddedCompositeStep g)
      (encodeRunRow g w c) (encodeRunRow g w c') ∧ c'.InputWithin w := by
  induction hreach with
  | refl => exact ⟨Relation.ReflTransGen.refl, hin⟩
  | @tail middle last _hprev edge ih =>
      rcases ih with ⟨hrows, hmiddle⟩
      have hlast : last.InputWithin w :=
        compositeStep_preserves_inputWithin w edge.1 hmiddle
      have hpadded : PaddedCompositeStep g
          (encodeRunRow g w middle) (encodeRunRow g w last) := by
        refine ⟨w, middle, last, hw, hmiddle, hlast, ?_, ?_, edge.1, rfl, rfl⟩
        · change middle.Within (w.length * workWidth)
          simpa [hbound] using edge.2.1
        · change last.Within (w.length * workWidth)
          simpa [hbound] using edge.2.2
      exact ⟨Relation.ReflTransGen.tail hrows hpadded, hlast⟩

/-- A bounded accepting composite run gives an accepting semantic padded-row run. -/
public theorem mem_paddedReachLanguage_of_boundedReaches
    {g : IndexedGrammar T} [Fintype g.nt] {w : List T} (hw : w ≠ [])
    (hreach : BoundedReaches g w (w.length * workWidth)
      (initialConfig g) (finalConfig g w.length)) :
    w ∈ paddedReachLanguage g := by
  have hencoded := encode_boundedRun_to_paddedComposite w hw rfl hreach.2
    (initialConfig_inputWithin g w)
  refine ⟨hw, encodeRunRow g w (finalConfig g w.length), ?_, ?_⟩
  · exact Relation.ReflTransGen.head
      (show PaddedRowStep g (inputRow g w)
          (encodeRunRow g w (initialConfig g)) from
        Or.inl ⟨w, hw, rfl, rfl⟩)
      (hencoded.1.mono fun _ _ h => Or.inr h)
  · exact ⟨w, hw, rfl⟩

/-- A decoded running row reachable from a fixed raw input row. -/
private def DecodedReach (g : IndexedGrammar T) [Fintype g.nt]
    (w : List T) (row : List (RowCell g)) : Prop :=
  ∃ c : Config g,
    BoundedReaches g w (w.length * workWidth) (initialConfig g) c ∧
      c.InputWithin w ∧ c.Within (w.length * workWidth) ∧
        row = encodeRunRow g w c

/-- Every semantic padded-row path is either still the untouched raw input row, or uniquely
decodes to a bounded composite run of that same input word. -/
private theorem paddedPath_decodes
    {g : IndexedGrammar T} [Fintype g.nt] {w : List T} (hw : w ≠ [])
    {row : List (RowCell g)}
    (hpath : Relation.ReflTransGen (PaddedRowStep g) (inputRow g w) row) :
    row = inputRow g w ∨ DecodedReach g w row := by
  induction hpath with
  | refl => exact Or.inl rfl
  | @tail middle last _hprev step ih =>
      rcases ih with hraw | hdecoded
      · subst middle
        rcases step with hinit | hcomposite
        · rcases hinit with ⟨u, hu, hrow, hlast⟩
          have hwu : w = u := inputRow_injective g hrow
          subst u
          refine Or.inr ⟨initialConfig g,
            BoundedReaches.refl (initialConfig_within_padded_bound g w hw),
            initialConfig_inputWithin g w,
            initialConfig_within_padded_bound g w hw, ?_⟩
          exact hlast
        · rcases hcomposite with
            ⟨u, c, c', hu, _hcpos, _hc'pos, _hcwork, _hc'work,
              _hstep, hrow, _hlast⟩
          exact False.elim
            (inputRow_ne_encodeRunRow_of_ne_nil g w hw u c hrow)
      · rcases hdecoded with ⟨c, hreach, hcpos, hcwork, hmiddle⟩
        rcases step with hinit | hcomposite
        · rcases hinit with ⟨u, hu, hraw, _hlast⟩
          have himpossible : inputRow g u = encodeRunRow g w c := by
            rw [← hraw, hmiddle]
          exact False.elim
            (inputRow_ne_encodeRunRow_of_ne_nil g u hu w c himpossible)
        · rcases hcomposite with
            ⟨u, d, d', hu, hdpos, hd'pos, hdwork, hd'work,
              hdstep, hold, hlast⟩
          have hrows : encodeRunRow g w c = encodeRunRow g u d := by
            rw [← hmiddle, hold]
          rcases encodeRunRow_pair_injective_of_bounds g w u c d
              hcpos hdpos hcwork hdwork hrows with ⟨hwu, hcd⟩
          subst u
          subst d
          have hsingle : BoundedReaches g w (w.length * workWidth) c d' :=
            BoundedReaches.single hdwork hdstep hd'work
          have hd'input : d'.InputWithin w :=
            compositeStep_preserves_inputWithin w hdstep hdpos
          exact Or.inr ⟨d', hreach.trans hsingle, hd'input, hd'work, hlast⟩

/-- An accepting semantic padded-row path decodes to a bounded accepting composite run. -/
public theorem boundedReaches_of_mem_paddedReachLanguage
    {g : IndexedGrammar T} [Fintype g.nt] {w : List T}
    (hmem : w ∈ paddedReachLanguage g) :
    BoundedReaches g w (w.length * workWidth)
      (initialConfig g) (finalConfig g w.length) := by
  rcases hmem with ⟨hw, row, hpath, hfinal⟩
  rcases hfinal with ⟨u, hu, hrow⟩
  rcases paddedPath_decodes hw hpath with hraw | hdecoded
  · have himpossible : inputRow g w = encodeRunRow g u (finalConfig g u.length) := by
      rw [← hraw, hrow]
    exact False.elim
      (inputRow_ne_encodeRunRow_of_ne_nil g w hw u (finalConfig g u.length)
        himpossible)
  · rcases hdecoded with ⟨c, hreach, hcpos, hcwork, hdecodedRow⟩
    have hrows : encodeRunRow g w c =
        encodeRunRow g u (finalConfig g u.length) := by
      rw [← hdecodedRow, hrow]
    have hfinalPos : (finalConfig g u.length).inputPos ≤ u.length := by
      simp [finalConfig]
    have hfinalWork : (finalConfig g u.length).work.word.length ≤
        u.length * workWidth := finalConfig_within_padded_bound g u hu
    rcases encodeRunRow_pair_injective_of_bounds g w u c (finalConfig g u.length)
        hcpos hfinalPos hcwork hfinalWork hrows with ⟨rfl, hc⟩
    simpa [hc] using hreach

/-- Semantic padded-row reachability is exactly bounded acceptance by Aho's composite machine. -/
public theorem mem_paddedReachLanguage_iff_boundedReaches
    {g : IndexedGrammar T} [Fintype g.nt] {w : List T} :
    w ∈ paddedReachLanguage g ↔
      w ≠ [] ∧ BoundedReaches g w (w.length * workWidth)
        (initialConfig g) (finalConfig g w.length) := by
  constructor
  · intro h
    exact ⟨h.1, boundedReaches_of_mem_paddedReachLanguage h⟩
  · rintro ⟨hw, hreach⟩
    exact mem_paddedReachLanguage_of_boundedReaches hw hreach

end Aho
end IndexedGrammar
