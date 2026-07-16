module

public import Langlib.Grammars.LR.Equivalence.BufferCorrectness

/-!
# Preloading the canonical LR lookahead buffer

On a properly endmarked input, the buffered DPDA deterministically reads
either `k` terminals or the earlier endmarker.  The resulting parser control
contains exactly `observe k w`, and the remaining physical input is exactly
`unreadAfter k w`.
-/

@[expose]
public section

open Language PDA

namespace CF_grammar.LRk.Buffered

open CF_grammar.LRk

variable {T : Type} [Fintype T]

/-- Writing the next free slot of an observed short prefix extends that
prefix by one terminal. -/
public theorem setBuffer_observe_append_singleton (k : ℕ)
    (xs : List T) (a : T) (hxs : xs.length < k) :
    setBuffer (observe k xs) xs.length (some a) =
      observe k (xs ++ [a]) := by
  funext i
  unfold setBuffer observe
  by_cases hi : i.val = xs.length
  · rw [if_pos hi]
    simp [List.getElem?_append, hi]
  · rw [if_neg hi]
    by_cases hlt : i.val < xs.length
    · simp [List.getElem?_append, hlt]
    · have hgt : xs.length + 1 ≤ i.val := by omega
      rw [List.getElem?_eq_none (by omega),
        List.getElem?_eq_none (by simp; omega)]

/-- Padding after an early marker leaves the ordinary EOF-padded observation
unchanged. -/
public theorem finishBuffer_observe (k : ℕ) (xs : List T)
    (hxs : xs.length < k) :
    finishBuffer (observe k xs) xs.length = observe k xs := by
  funext i
  unfold finishBuffer observe
  by_cases hi : i.val < xs.length
  · simp [hi]
  · rw [if_neg hi, List.getElem?_eq_none (by omega)]

/-- Once a prefix of length `k` has been loaded, later terminals do not change
the observation. -/
public theorem observe_append_of_length_eq (k : ℕ) (xs ys : List T)
    (hxs : xs.length = k) :
    observe k (xs ++ ys) = observe k xs := by
  funext i
  unfold observe
  rw [List.getElem?_append]
  simp [hxs, i.isLt]

/-- The physical suffix after loading an exact `k`-terminal prefix. -/
public theorem unreadAfter_append_of_length_eq (k : ℕ)
    (xs ys : List T) (hxs : xs.length = k) :
    unreadAfter k (xs ++ ys) = ys.map some ++ [none] := by
  unfold unreadAfter
  rw [if_pos (by simp [hxs])]
  simp [hxs, List.drop_append]

noncomputable section

private theorem preloadFrom (G : CF_grammar T) (k : ℕ) (hk : 0 < k)
    (xs ys : List T) (hxs : xs.length < k) :
    (machine G k hk).toPDA.Reaches
      ⟨Control.load ⟨xs.length, by omega⟩ (observe k xs),
        ys.map some ++ [none], [none]⟩
      ⟨Control.parse (startKernel G k) (observe k (xs ++ ys)),
        unreadAfter k (xs ++ ys), [none]⟩ := by
  induction ys generalizing xs with
  | nil =>
      have hstep : (machine G k hk).toPDA.Reaches₁
          ⟨Control.load ⟨xs.length, by omega⟩ (observe k xs),
            [none], [none]⟩
          ⟨Control.parse (startKernel G k)
            (finishBuffer (observe k xs) xs.length), [], [none]⟩ := by
        simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, machine,
          inputTransition, hxs]
      have hfinish := finishBuffer_observe k xs hxs
      have hunread : unreadAfter k xs = [] := by
        unfold unreadAfter
        rw [if_neg (by omega)]
      simpa [hfinish, hunread] using
        (Relation.ReflTransGen.single hstep)
  | cons a ys ih =>
      have hbuffer := setBuffer_observe_append_singleton k xs a hxs
      by_cases hfull : xs.length + 1 = k
      · have hstep : (machine G k hk).toPDA.Reaches₁
            ⟨Control.load ⟨xs.length, by omega⟩ (observe k xs),
              some a :: (ys.map some ++ [none]), [none]⟩
            ⟨Control.parse (startKernel G k)
              (setBuffer (observe k xs) xs.length (some a)),
              ys.map some ++ [none], [none]⟩ := by
          simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, machine,
            inputTransition, hxs, hfull]
        have hprefLen : (xs ++ [a]).length = k := by simp [hfull]
        have hobserve := observe_append_of_length_eq k (xs ++ [a]) ys hprefLen
        have hunread := unreadAfter_append_of_length_eq k (xs ++ [a]) ys hprefLen
        have hword : xs ++ a :: ys = (xs ++ [a]) ++ ys := by simp
        have hobserve' : observe k (xs ++ a :: ys) =
            setBuffer (observe k xs) xs.length (some a) := by
          rw [hword, hobserve, hbuffer]
        have hunread' : unreadAfter k (xs ++ a :: ys) =
            ys.map some ++ [none] := by
          rw [hword, hunread]
        simpa [hobserve', hunread'] using
          (Relation.ReflTransGen.single hstep)
      · have hshort : (xs ++ [a]).length < k := by
          simp
          omega
        have hstep : (machine G k hk).toPDA.Reaches₁
            ⟨Control.load ⟨xs.length, by omega⟩ (observe k xs),
              some a :: (ys.map some ++ [none]), [none]⟩
            ⟨Control.load ⟨(xs ++ [a]).length, by omega⟩
              (observe k (xs ++ [a])), ys.map some ++ [none], [none]⟩ := by
          simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, machine,
            inputTransition, hxs, hfull, hbuffer]
        have htail := ih (xs ++ [a]) hshort
        have hrun := (Relation.ReflTransGen.single hstep).trans htail
        simpa [List.append_assoc] using hrun

/-- Exact preload theorem for a properly endmarked word. -/
public theorem machine_reaches_preload (G : CF_grammar T) (k : ℕ)
    (hk : 0 < k) (w : List T) :
    (machine G k hk).toPDA.Reaches
      ⟨(machine G k hk).initial_state, w.map some ++ [none],
        [(machine G k hk).start_symbol]⟩
      ⟨Control.parse (scanKernel G k []) (observe k w),
        unreadAfter k w, [none]⟩ := by
  have h := preloadFrom G k hk [] w (by simpa using hk)
  simpa [machine, initialControl, observe_nil, scanKernel_nil] using h

end

end CF_grammar.LRk.Buffered
