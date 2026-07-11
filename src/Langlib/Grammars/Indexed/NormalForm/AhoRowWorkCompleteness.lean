module

public import Langlib.Grammars.Indexed.NormalForm.AhoRowTrace

@[expose]
public section

open List Relation Classical

variable {T : Type}

namespace IndexedGrammar
namespace Aho

public theorem WorkTrace.append (g : IndexedGrammar T) [Fintype g.nt]
    (cert : CompositeCert g) {q r s : WorkScanState g}
    {xs ys : List (Option (WorkSlot g) × Option (WorkSlot g) × WorkPhase)}
    (h₁ : WorkTrace g cert q xs r) (h₂ : WorkTrace g cert r ys s) :
    WorkTrace g cert q (xs ++ ys) s := by
  induction h₁ with
  | nil => exact h₂
  | cons hedge htail ih => exact .cons hedge (ih h₂)

public def samePrefixRows (g : IndexedGrammar T) (xs : List (WorkSym g)) :
    List (Option (WorkSlot g) × Option (WorkSlot g) × WorkPhase) :=
  xs.map fun z => (inactive z, inactive z, .prefix)

@[simp] public theorem samePrefixRows_old (g : IndexedGrammar T) (xs : List (WorkSym g)) :
    (samePrefixRows g xs).map (fun r => r.1) = xs.map inactive := by
  simp [samePrefixRows]

@[simp] public theorem samePrefixRows_new (g : IndexedGrammar T) (xs : List (WorkSym g)) :
    (samePrefixRows g xs).map (fun r => r.2.1) = xs.map inactive := by
  simp [samePrefixRows]

public theorem trace_same_prefix (g : IndexedGrammar T) [Fintype g.nt]
    (cert : CompositeCert g) (h : WorkHistory g) (xs : List (WorkSym g))
    (henabled : CertEnabled g cert) :
    WorkTrace g cert ⟨.prefix, h, false, false⟩ (samePrefixRows g xs)
      ⟨.prefix, historySame h xs, false, false⟩ := by
  induction xs generalizing h with
  | nil => exact .nil _
  | cons z xs ih =>
      simp only [samePrefixRows, List.map_cons]
      apply WorkTrace.cons
      · refine ⟨by simp, by simp, by simp [paddingOK], by simp [paddingOK], ?_⟩
        rw [workEdge_prefix_iff g cert .prefix .prefix h _ _ (by simp)]
        simp [henabled, prefixEdge, SameInactiveSome]
      · simpa [advanceWorkState, historySame] using
          ih (updateHistory h (inactive z) (inactive z))

public theorem trace_productive_boundary (g : IndexedGrammar T) [Fintype g.nt]
    (cert : CompositeCert g) (alpha : List (WorkSym g))
    (henabled : CertEnabled g cert) (hproductive : cert.productive = true) :
    ∃ rows h,
      WorkTrace g cert (initialWorkScan g) rows ⟨.stage1, h, false, false⟩ ∧
      rows.map (fun r => r.1) =
        (alpha ++ [WorkSym.dollar]).map inactive ∧
      rows.map (fun r => r.2.1) =
        (markProductivePrefix alpha ++ [WorkSym.dollar]).map inactive := by
  induction alpha using List.reverseRecOn with
  | nil =>
      let row := (inactive (WorkSym.dollar : WorkSym g),
        inactive (WorkSym.dollar : WorkSym g), WorkPhase.stage1)
      refine ⟨[row], updateHistory (initialWorkScan g).history row.1 row.2.1, ?_, by simp [row], by simp [row]⟩
      apply WorkTrace.cons
      · refine ⟨by simp [initialWorkScan], by simp, by simp [initialWorkScan, paddingOK],
          by simp [initialWorkScan, paddingOK], ?_⟩
        simp only [initialWorkScan]
        rw [workEdge_prefix_iff g cert .prefix .stage1 _ _ _ (by simp)]
        simp [henabled, prefixEdge, Boundary, ProductiveBoundaryOK]
      · exact .nil _
  | @append_singleton alpha z ih =>
      by_cases hz : ∃ R d, z = WorkSym.index R d
      · rcases hz with ⟨R, d, rfl⟩
        let marked := (inactive (WorkSym.index R d),
          inactive (WorkSym.index R d.markUsed), WorkPhase.marked)
        let boundary := (inactive (WorkSym.dollar : WorkSym g),
          inactive (WorkSym.dollar : WorkSym g), WorkPhase.stage1)
        let h₀ := historySame (initialWorkScan g).history alpha
        let h₁ := updateHistory h₀ marked.1 marked.2.1
        let h₂ := updateHistory h₁ boundary.1 boundary.2.1
        refine ⟨samePrefixRows g alpha ++ [marked, boundary], h₂, ?_, ?_, ?_⟩
        · apply WorkTrace.append g cert (trace_same_prefix g cert _ alpha henabled)
          apply WorkTrace.cons
          · refine ⟨by simp, by simp [marked], by simp [paddingOK], by simp [paddingOK], ?_⟩
            change WorkEdge g cert .prefix .marked h₀
              (inactive (WorkSym.index R d)) (inactive (WorkSym.index R d.markUsed))
            rw [workEdge_prefix_iff g cert .prefix .marked h₀ _ _ (by simp)]
            refine ⟨henabled, ?_⟩
            simp only [prefixEdge, hproductive, true_and]
            exact ⟨R, d, rfl, rfl⟩
          · apply WorkTrace.cons
            · refine ⟨by simp [advanceWorkState], by simp [boundary], ?_, ?_, ?_⟩
              · change paddingOK false (inactive (WorkSym.dollar : WorkSym g))
                simp [paddingOK]
              · change paddingOK false (inactive (WorkSym.dollar : WorkSym g))
                simp [paddingOK]
              · change WorkEdge g cert .marked .stage1 h₁
                  (inactive WorkSym.dollar) (inactive WorkSym.dollar)
                rw [workEdge_prefix_iff g cert .marked .stage1 h₁ _ _ (by simp)]
                simp [henabled, prefixEdge, Boundary, hproductive, boundary]
            · exact .nil _
        · simp [samePrefixRows, marked, boundary]
        · simp [samePrefixRows, marked, boundary]
      · have hnot : ∀ R d, z ≠ WorkSym.index R d := by
          intro R d h
          exact hz ⟨R, d, h⟩
        -- A non-index last symbol is copied; the productive operation is the identity.
        let xs := alpha ++ [z]
        let h₀ := historySame (initialWorkScan g).history xs
        let boundary := (inactive (WorkSym.dollar : WorkSym g),
          inactive (WorkSym.dollar : WorkSym g), WorkPhase.stage1)
        refine ⟨samePrefixRows g xs ++ [boundary], updateHistory h₀ boundary.1 boundary.2.1,
          ?_, by simp [xs, boundary], ?_⟩
        · apply WorkTrace.append g cert (trace_same_prefix g cert _ xs henabled)
          apply WorkTrace.cons
          · refine ⟨by simp, by simp [boundary], by simp [paddingOK], by simp [paddingOK], ?_⟩
            change WorkEdge g cert .prefix .stage1 h₀
              (inactive WorkSym.dollar) (inactive WorkSym.dollar)
            rw [workEdge_prefix_iff g cert .prefix .stage1 h₀ _ _ (by simp)]
            refine ⟨henabled, ?_⟩
            simp only [prefixEdge]
            refine ⟨by simp [Boundary], ?_⟩
            right
            dsimp [h₀, xs, historySame, ProductiveBoundaryOK]
            simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
            cases z <;> simp_all [updateHistory, inactive]
          · exact .nil _
        · simp [xs, boundary, markProductivePrefix_append_nonindex _ _ hnot]

public theorem trace_plain_boundary (g : IndexedGrammar T) [Fintype g.nt]
    (cert : CompositeCert g) (alpha : List (WorkSym g))
    (henabled : CertEnabled g cert) (hproductive : cert.productive = false) :
    ∃ rows h,
      WorkTrace g cert (initialWorkScan g) rows ⟨.stage1, h, false, false⟩ ∧
      rows.map (fun r => r.1) = (alpha ++ [WorkSym.dollar]).map inactive ∧
      rows.map (fun r => r.2.1) = (alpha ++ [WorkSym.dollar]).map inactive := by
  let h₀ := historySame (initialWorkScan g).history alpha
  let boundary := (inactive (WorkSym.dollar : WorkSym g),
    inactive (WorkSym.dollar : WorkSym g), WorkPhase.stage1)
  refine ⟨samePrefixRows g alpha ++ [boundary], updateHistory h₀ boundary.1 boundary.2.1,
    ?_, by simp [boundary], by simp [boundary]⟩
  apply WorkTrace.append g cert (trace_same_prefix g cert _ alpha henabled)
  apply WorkTrace.cons
  · refine ⟨by simp, by simp [boundary], by simp [paddingOK], by simp [paddingOK], ?_⟩
    change WorkEdge g cert .prefix .stage1 h₀
      (inactive WorkSym.dollar) (inactive WorkSym.dollar)
    rw [workEdge_prefix_iff g cert .prefix .stage1 h₀ _ _ (by simp)]
    simp [henabled, prefixEdge, Boundary, hproductive]
  · exact .nil _

public def sameSuffixRows (xs : List (Option (WorkSlot g))) :
    List (Option (WorkSlot g) × Option (WorkSlot g) × WorkPhase) :=
  xs.map fun x => (x, x, .suffixSame)

private theorem trace_same_suffix_none (g : IndexedGrammar T) [Fintype g.nt]
    (cert : CompositeCert g) (h : WorkHistory g) (oldEnded newEnded : Bool) (k : ℕ)
    (hloop : ∀ h, WorkEdge g cert .suffixSame .suffixSame h none none) :
    ∃ result,
      WorkTrace g cert ⟨.suffixSame, h, oldEnded, newEnded⟩
        (sameSuffixRows (List.replicate k none)) result ∧
      result.phase = .suffixSame := by
  induction k generalizing h oldEnded newEnded with
  | zero => exact ⟨_, .nil _, rfl⟩
  | succ k ih =>
      simp only [List.replicate_succ, sameSuffixRows, List.map_cons]
      let q := advanceWorkState ⟨.suffixSame, h, oldEnded, newEnded⟩ none none .suffixSame
      rcases ih (h := q.history) (oldEnded := q.oldEnded) (newEnded := q.newEnded) with
        ⟨result, htrace, hphase⟩
      refine ⟨result, .cons ?_ htrace, hphase⟩
      exact ⟨by simp, by simp, by simp [paddingOK], by simp [paddingOK], hloop h⟩

public theorem trace_same_suffix_padded (g : IndexedGrammar T) [Fintype g.nt]
    (cert : CompositeCert g) (h : WorkHistory g) (beta : List (WorkSym g)) (k : ℕ)
    (hloop : ∀ h x, InactiveOpt x →
      WorkEdge g cert .suffixSame .suffixSame h x x) :
    ∃ result,
      WorkTrace g cert ⟨.suffixSame, h, false, false⟩
        (sameSuffixRows (beta.map inactive ++ List.replicate k none)) result ∧
      result.phase = .suffixSame := by
  induction beta generalizing h with
  | nil =>
      simpa using trace_same_suffix_none g cert h false false k (fun h => hloop h none (by simp [InactiveOpt]))
  | cons z beta ih =>
      simp only [List.map_cons, List.cons_append, sameSuffixRows, List.map_cons]
      let q := advanceWorkState ⟨.suffixSame, h, false, false⟩
        (inactive z) (inactive z) .suffixSame
      rcases ih (h := q.history) with ⟨result, htrace, hphase⟩
      refine ⟨result, .cons ?_ htrace, hphase⟩
      exact ⟨by simp, by simp, by simp [paddingOK], by simp [paddingOK],
        hloop h (inactive z) (by simp [InactiveOpt, inactive])⟩

public theorem accepts_replace_one (g : IndexedGrammar T) [Fintype g.nt]
    (cert : CompositeCert g)
    (prefixRows : List (Option (WorkSlot g) × Option (WorkSlot g) × WorkPhase))
    (h : WorkHistory g)
    (hprefix : WorkTrace g cert (initialWorkScan g) prefixRows
      ⟨.stage1, h, false, false⟩)
    (oldFocus newFocus : WorkSym g) (beta : List (WorkSym g)) (k : ℕ)
    (hfocus : ∀ h, WorkEdge g cert .stage1 .suffixSame h
      (active oldFocus) (active newFocus))
    (hloop : ∀ h x, InactiveOpt x →
      WorkEdge g cert .suffixSame .suffixSame h x x) :
    WorkTraceAccepts g cert
      (prefixRows.map (fun r => r.1) ++ [active oldFocus] ++
        beta.map inactive ++ List.replicate k none)
      (prefixRows.map (fun r => r.2.1) ++ [active newFocus] ++
        beta.map inactive ++ List.replicate k none) := by
  let focusRow := (active oldFocus, active newFocus, WorkPhase.suffixSame)
  let h₁ := updateHistory h focusRow.1 focusRow.2.1
  rcases trace_same_suffix_padded g cert h₁ beta k hloop with
    ⟨result, hsuffix, hphase⟩
  refine ⟨prefixRows ++ focusRow :: sameSuffixRows
      (beta.map inactive ++ List.replicate k none), result, ?_, ?_, ?_, ?_⟩
  · apply WorkTrace.append g cert hprefix
    apply WorkTrace.cons
    · exact ⟨by simp, by simp [focusRow], by simp [paddingOK], by simp [paddingOK], hfocus h⟩
    · simpa [advanceWorkState, focusRow, h₁] using hsuffix
  · simp [focusRow, sameSuffixRows]
  · simp [focusRow, sameSuffixRows]
  · unfold workScanDone
    rw [hphase]
    simp

public theorem accepts_plainTerminal (g : IndexedGrammar T) [Fintype g.nt]
    {A : g.nt} {a : T} {alpha beta : List (WorkSym g)} (k : ℕ)
    (hrule : AugTerminal g A a) :
    WorkTraceAccepts g (.plainTerminal A a)
      (((alpha ++ [WorkSym.dollar]).map inactive) ++ [active (WorkSym.plain A)] ++
        beta.map inactive ++ List.replicate k none)
      (((markProductivePrefix alpha ++ [WorkSym.dollar]).map inactive) ++
        [active (WorkSym.terminal a)] ++ beta.map inactive ++ List.replicate k none) := by
  rcases trace_productive_boundary g (.plainTerminal A a) alpha hrule rfl with
    ⟨prefixRows, h, hprefix, hold, hnew⟩
  have hacc := accepts_replace_one g (.plainTerminal A a) prefixRows h hprefix
    (WorkSym.plain A) (WorkSym.terminal a) beta k
    (fun h => by simp [WorkEdge, replaceOneEdge, hrule])
    (fun h x hx => by simp [WorkEdge, replaceOneEdge, hrule, sameSuffix, hx])
  simpa [hold, hnew] using hacc

public theorem accepts_plainPushSkip (g : IndexedGrammar T) [Fintype g.nt]
    {A B : g.nt} {f : g.flag} {alpha beta : List (WorkSym g)} (k : ℕ)
    (hrule : AugPush g A B f) :
    WorkTraceAccepts g (.plainPushSkip A B f)
      (((alpha ++ [WorkSym.dollar]).map inactive) ++ [active (WorkSym.plain A)] ++
        beta.map inactive ++ List.replicate k none)
      (((alpha ++ [WorkSym.dollar]).map inactive) ++ [active (WorkSym.plain B)] ++
        beta.map inactive ++ List.replicate k none) := by
  rcases trace_plain_boundary g (.plainPushSkip A B f) alpha hrule rfl with
    ⟨prefixRows, h, hprefix, hold, hnew⟩
  have hacc := accepts_replace_one g (.plainPushSkip A B f) prefixRows h hprefix
    (WorkSym.plain A) (WorkSym.plain B) beta k
    (fun h => by simp [WorkEdge, replaceOneEdge, hrule])
    (fun h x hx => by simp [WorkEdge, replaceOneEdge, hrule, sameSuffix, hx])
  simpa [hold, hnew] using hacc

public def shift1Rows (g : IndexedGrammar T) (prev : Option (WorkSlot g)) :
    List (Option (WorkSlot g)) →
      List (Option (WorkSlot g) × Option (WorkSlot g) × WorkPhase)
  | [] => [(none, prev, .suffixPlus1)]
  | x :: xs => (x, prev, .suffixPlus1) :: shift1Rows g x xs

@[simp] public theorem shift1Rows_old (g : IndexedGrammar T) (prev : Option (WorkSlot g))
    (xs : List (Option (WorkSlot g))) :
    (shift1Rows g prev xs).map (fun r => r.1) = xs ++ [none] := by
  induction xs generalizing prev with
  | nil => rfl
  | cons x xs ih => simp [shift1Rows, ih]

@[simp] public theorem shift1Rows_new (g : IndexedGrammar T) (prev : Option (WorkSlot g))
    (xs : List (Option (WorkSlot g))) :
    (shift1Rows g prev xs).map (fun r => r.2.1) = prev :: xs := by
  induction xs generalizing prev with
  | nil => rfl
  | cons x xs ih => simp [shift1Rows, ih]

private theorem trace_plus1_shift (g : IndexedGrammar T) [Fintype g.nt]
    (cert : CompositeCert g) (h : WorkHistory g) (oldEnded newEnded : Bool)
    (prev : Option (WorkSlot g)) (xs : List (Option (WorkSlot g)))
    (hprev : h.old1 = some prev) (hprevInactive : InactiveOpt prev)
    (hxsInactive : ∀ x ∈ xs, InactiveOpt x)
    (holdPad : PaddingStream g oldEnded (xs ++ [none]))
    (hnewPad : PaddingStream g newEnded (prev :: xs))
    (hloop : ∀ h old new, plus1Suffix h old new →
      WorkEdge g cert .suffixPlus1 .suffixPlus1 h old new) :
    ∃ result,
      WorkTrace g cert ⟨.suffixPlus1, h, oldEnded, newEnded⟩
        (shift1Rows g prev xs) result ∧
      result.phase = .suffixPlus1 ∧ lastOldNone result.history := by
  cases xs with
  | nil =>
      have holdHead : paddingOK oldEnded none :=
        (show PaddingStream g oldEnded [none] from by simpa using holdPad).head
      have hnewHead : paddingOK newEnded prev := hnewPad.head
      let result := advanceWorkState ⟨.suffixPlus1, h, oldEnded, newEnded⟩
        none prev .suffixPlus1
      refine ⟨result, ?_, rfl, ?_⟩
      · apply WorkTrace.cons
        · refine ⟨by simp, by simp, holdHead, hnewHead, hloop h none prev ?_⟩
          exact ⟨by simp [InactiveOpt], hprevInactive, hprev⟩
        · exact .nil _
      · simp [result, advanceWorkState, lastOldNone, updateHistory]
  | cons x xs =>
      have holdCons : PaddingStream g oldEnded (x :: (xs ++ [none])) := by
        simpa using holdPad
      have hnewCons : PaddingStream g newEnded (prev :: x :: xs) := hnewPad
      have holdHead := holdCons.head
      have holdTail := holdCons.tail
      have hnewHead := hnewCons.head
      have hnewTail := hnewCons.tail
      have hx : InactiveOpt x := hxsInactive x (by simp)
      have htailInactive : ∀ y ∈ xs, InactiveOpt y := by
        intro y hy
        exact hxsInactive y (by simp [hy])
      let q := advanceWorkState ⟨.suffixPlus1, h, oldEnded, newEnded⟩
        x prev .suffixPlus1
      have hqprev : q.history.old1 = some x := by
        simp [q, advanceWorkState, updateHistory]
      rcases trace_plus1_shift g cert q.history q.oldEnded q.newEnded x xs
          hqprev hx htailInactive holdTail hnewTail hloop with
        ⟨result, htrace, hphase, hlast⟩
      refine ⟨result, .cons ?_ htrace, hphase, hlast⟩
      refine ⟨by simp, by simp, holdHead, hnewHead, hloop h x prev ?_⟩
      exact ⟨hx, hprevInactive, hprev⟩
termination_by xs.length

public def plus2ShiftRows (g : IndexedGrammar T)
    (prev2 prev1 : Option (WorkSlot g)) : List (Option (WorkSlot g)) →
      List (Option (WorkSlot g) × Option (WorkSlot g) × WorkPhase)
  | [] => [(none, prev2, .suffixPlus2), (none, prev1, .suffixPlus2)]
  | x :: xs => (x, prev2, .suffixPlus2) :: plus2ShiftRows g prev1 x xs

@[simp] public theorem plus2ShiftRows_old (g : IndexedGrammar T)
    (prev2 prev1 : Option (WorkSlot g)) (xs : List (Option (WorkSlot g))) :
    (plus2ShiftRows g prev2 prev1 xs).map (fun r => r.1) = xs ++ [none, none] := by
  induction xs generalizing prev2 prev1 with
  | nil => rfl
  | cons x xs ih => simp [plus2ShiftRows, ih]

@[simp] public theorem plus2ShiftRows_new (g : IndexedGrammar T)
    (prev2 prev1 : Option (WorkSlot g)) (xs : List (Option (WorkSlot g))) :
    (plus2ShiftRows g prev2 prev1 xs).map (fun r => r.2.1) = prev2 :: prev1 :: xs := by
  induction xs generalizing prev2 prev1 with
  | nil => rfl
  | cons x xs ih => simp [plus2ShiftRows, ih]

private theorem trace_plus2_shift (g : IndexedGrammar T) [Fintype g.nt]
    (cert : CompositeCert g) (h : WorkHistory g) (oldEnded newEnded : Bool)
    (prev2 prev1 : Option (WorkSlot g)) (xs : List (Option (WorkSlot g)))
    (hprev2 : h.old2 = some prev2) (hprev1 : h.old1 = some prev1)
    (hinactive2 : InactiveOpt prev2) (hinactive1 : InactiveOpt prev1)
    (hxsInactive : ∀ x ∈ xs, InactiveOpt x)
    (holdPad : PaddingStream g oldEnded (xs ++ [none, none]))
    (hnewPad : PaddingStream g newEnded (prev2 :: prev1 :: xs))
    (hloop : ∀ h old new, plus2Suffix h old new →
      WorkEdge g cert .suffixPlus2 .suffixPlus2 h old new) :
    ∃ result,
      WorkTrace g cert ⟨.suffixPlus2, h, oldEnded, newEnded⟩
        (plus2ShiftRows g prev2 prev1 xs) result ∧
      result.phase = .suffixPlus2 ∧ lastTwoOldNone result.history := by
  cases xs with
  | nil =>
      have holdCons : PaddingStream g oldEnded [none, none] := by simpa using holdPad
      have hnewCons : PaddingStream g newEnded [prev2, prev1] := hnewPad
      let q := advanceWorkState ⟨.suffixPlus2, h, oldEnded, newEnded⟩ none prev2 .suffixPlus2
      let result := advanceWorkState q none prev1 .suffixPlus2
      refine ⟨result, ?_, rfl, ?_⟩
      · apply WorkTrace.cons
        · refine ⟨by simp, by simp, holdCons.head, hnewCons.head,
            hloop h none prev2 ⟨by simp [InactiveOpt], hinactive2, hprev2⟩⟩
        · apply WorkTrace.cons
          · refine ⟨by simp [q, advanceWorkState], by simp,
              holdCons.tail.head, hnewCons.tail.head, hloop q.history none prev1 ?_⟩
            refine ⟨by simp [InactiveOpt], hinactive1, ?_⟩
            simp [q, advanceWorkState, updateHistory, hprev1]
          · exact .nil _
      · simp [result, q, advanceWorkState, lastTwoOldNone, updateHistory]
  | cons x xs =>
      have holdCons : PaddingStream g oldEnded (x :: (xs ++ [none, none])) := by simpa using holdPad
      have hnewCons : PaddingStream g newEnded (prev2 :: prev1 :: x :: xs) := hnewPad
      have hx : InactiveOpt x := hxsInactive x (by simp)
      let q := advanceWorkState ⟨.suffixPlus2, h, oldEnded, newEnded⟩ x prev2 .suffixPlus2
      have hq2 : q.history.old2 = some prev1 := by simp [q, advanceWorkState, updateHistory, hprev1]
      have hq1 : q.history.old1 = some x := by simp [q, advanceWorkState, updateHistory]
      rcases trace_plus2_shift g cert q.history q.oldEnded q.newEnded prev1 x xs
          hq2 hq1 hinactive1 hx (by intro y hy; exact hxsInactive y (by simp [hy]))
          holdCons.tail hnewCons.tail hloop with ⟨result, hshift, hphase, hlast⟩
      refine ⟨result, .cons ?_ hshift, hphase, hlast⟩
      exact ⟨by simp, by simp, holdCons.head, hnewCons.head,
        hloop h x prev2 ⟨hx, hinactive2, hprev2⟩⟩
termination_by xs.length

public def plus2FromRows (g : IndexedGrammar T) (inserted1 inserted2 : WorkSym g) :
    List (Option (WorkSlot g)) →
      List (Option (WorkSlot g) × Option (WorkSlot g) × WorkPhase)
  | [] =>
      [(none, active inserted1, .stage3),
        (none, inactive inserted2, .suffixPlus2)]
  | [x] =>
      [(x, active inserted1, .stage3),
        (none, inactive inserted2, .suffixPlus2),
        (none, x, .suffixPlus2)]
  | x :: y :: xs =>
      (x, active inserted1, .stage3) ::
        (y, inactive inserted2, .suffixPlus2) :: plus2ShiftRows g x y xs

@[simp] public theorem plus2FromRows_old (g : IndexedGrammar T)
    (inserted1 inserted2 : WorkSym g) (xs : List (Option (WorkSlot g))) :
    (plus2FromRows g inserted1 inserted2 xs).map (fun r => r.1) =
      xs ++ [none, none] := by
  cases xs with
  | nil => rfl
  | cons x xs => cases xs <;> simp [plus2FromRows]

@[simp] public theorem plus2FromRows_new (g : IndexedGrammar T)
    (inserted1 inserted2 : WorkSym g) (xs : List (Option (WorkSlot g))) :
    (plus2FromRows g inserted1 inserted2 xs).map (fun r => r.2.1) =
      active inserted1 :: inactive inserted2 :: xs := by
  cases xs with
  | nil => rfl
  | cons x xs => cases xs <;> simp [plus2FromRows]

private theorem trace_plus2_from_stage2 (g : IndexedGrammar T) [Fintype g.nt]
    (cert : CompositeCert g) (h : WorkHistory g) (inserted1 inserted2 : WorkSym g)
    (xs : List (Option (WorkSlot g)))
    (hxsInactive : ∀ x ∈ xs, InactiveOpt x)
    (holdPad : PaddingStream g false (xs ++ [none, none]))
    (hnewPad : PaddingStream g false (active inserted1 :: inactive inserted2 :: xs))
    (hfirst : ∀ h old, InactiveOpt old →
      WorkEdge g cert .stage2 .stage3 h old (active inserted1))
    (hsecond : ∀ h old, InactiveOpt old →
      WorkEdge g cert .stage3 .suffixPlus2 h old (inactive inserted2))
    (hloop : ∀ h old new, plus2Suffix h old new →
      WorkEdge g cert .suffixPlus2 .suffixPlus2 h old new) :
    ∃ result,
      WorkTrace g cert ⟨.stage2, h, false, false⟩
        (plus2FromRows g inserted1 inserted2 xs) result ∧
      result.phase = .suffixPlus2 ∧ lastTwoOldNone result.history := by
  cases xs with
  | nil =>
      have holdCons : PaddingStream g false [none, none] := by simpa using holdPad
      have hnewCons : PaddingStream g false [active inserted1, inactive inserted2] := hnewPad
      let q := advanceWorkState ⟨.stage2, h, false, false⟩ none (active inserted1) .stage3
      let result := advanceWorkState q none (inactive inserted2) .suffixPlus2
      refine ⟨result, ?_, rfl, ?_⟩
      · apply WorkTrace.cons
        · exact ⟨by simp, by simp, holdCons.head, hnewCons.head,
            hfirst h none (by simp [InactiveOpt])⟩
        · apply WorkTrace.cons
          · exact ⟨by simp [q, advanceWorkState], by simp,
              holdCons.tail.head, hnewCons.tail.head,
              hsecond q.history none (by simp [InactiveOpt])⟩
          · exact .nil _
      · simp [result, q, advanceWorkState, lastTwoOldNone, updateHistory]
  | cons x xs =>
      cases xs with
      | nil =>
          have holdCons : PaddingStream g false [x, none, none] := by simpa using holdPad
          have hnewCons : PaddingStream g false [active inserted1, inactive inserted2, x] := hnewPad
          have hx : InactiveOpt x := hxsInactive x (by simp)
          let q₁ := advanceWorkState ⟨.stage2, h, false, false⟩ x (active inserted1) .stage3
          let q₂ := advanceWorkState q₁ none (inactive inserted2) .suffixPlus2
          let result := advanceWorkState q₂ none x .suffixPlus2
          refine ⟨result, ?_, rfl, ?_⟩
          · apply WorkTrace.cons
            · exact ⟨by simp, by simp, holdCons.head, hnewCons.head, hfirst h x hx⟩
            · apply WorkTrace.cons
              · exact ⟨by simp [q₁, advanceWorkState], by simp,
                  holdCons.tail.head, hnewCons.tail.head,
                  hsecond q₁.history none (by simp [InactiveOpt])⟩
              · apply WorkTrace.cons
                · refine ⟨by simp [q₂, q₁, advanceWorkState], by simp,
                      holdCons.tail.tail.head, hnewCons.tail.tail.head,
                      hloop q₂.history none x ?_⟩
                  refine ⟨by simp [InactiveOpt], hx, ?_⟩
                  simp [q₂, q₁, advanceWorkState, updateHistory]
                · exact .nil _
          · simp [result, q₂, q₁, advanceWorkState, lastTwoOldNone, updateHistory]
      | cons y ys =>
          have holdCons : PaddingStream g false (x :: y :: (ys ++ [none, none])) := by
            simpa using holdPad
          have hnewCons : PaddingStream g false
              (active inserted1 :: inactive inserted2 :: x :: y :: ys) := hnewPad
          have hx : InactiveOpt x := hxsInactive x (by simp)
          have hy : InactiveOpt y := hxsInactive y (by simp)
          let q₁ := advanceWorkState ⟨.stage2, h, false, false⟩ x (active inserted1) .stage3
          let q₂ := advanceWorkState q₁ y (inactive inserted2) .suffixPlus2
          have hq2 : q₂.history.old2 = some x := by
            simp [q₂, q₁, advanceWorkState, updateHistory]
          have hq1 : q₂.history.old1 = some y := by
            simp [q₂, q₁, advanceWorkState, updateHistory]
          rcases trace_plus2_shift g cert q₂.history q₂.oldEnded q₂.newEnded
              x y ys hq2 hq1 hx hy
              (by intro z hz; exact hxsInactive z (by simp [hz]))
              holdCons.tail.tail hnewCons.tail.tail hloop with
            ⟨result, hshift, hphase, hlast⟩
          refine ⟨result, ?_, hphase, hlast⟩
          apply WorkTrace.cons
          · exact ⟨by simp, by simp, holdCons.head, hnewCons.head, hfirst h x hx⟩
          · apply WorkTrace.cons
            · exact ⟨by simp [q₁, advanceWorkState], by simp,
                holdCons.tail.head, hnewCons.tail.head, hsecond q₁.history y hy⟩
            · simpa [q₂, q₁, advanceWorkState] using hshift

public def nextOr (fallback : X) : List X → X
  | [] => fallback
  | x :: _ => x

public def popChainRows (g : IndexedGrammar T) (R : CFlag g) (d : IndexMark) :
    List (WorkSym g) →
      List (Option (WorkSlot g) × Option (WorkSlot g) × WorkPhase)
  | [] => [(inactive (WorkSym.index R d), inactive WorkSym.dollar, .stage2)]
  | z :: beta =>
      (inactive z, inactive (nextOr (WorkSym.index R d.markUsed) beta), .popBeta) ::
        popChainRows g R d beta

@[simp] public theorem popChainRows_old (g : IndexedGrammar T) (R : CFlag g)
    (d : IndexMark) (beta : List (WorkSym g)) :
    (popChainRows g R d beta).map (fun r => r.1) =
      beta.map inactive ++ [inactive (WorkSym.index R d)] := by
  induction beta with
  | nil => rfl
  | cons z beta ih => simp [popChainRows, ih]

public theorem popChainRows_new (g : IndexedGrammar T) (R : CFlag g)
    (d : IndexMark) (beta : List (WorkSym g)) :
    inactive (nextOr (WorkSym.index R d.markUsed) beta) ::
        (popChainRows g R d beta).map (fun r => r.2.1) =
      beta.map inactive ++ [inactive (WorkSym.index R d.markUsed), inactive WorkSym.dollar] := by
  induction beta with
  | nil => rfl
  | cons z beta ih =>
      simp only [popChainRows, List.map_cons, nextOr, List.cons_append, Prod.snd,
        Prod.fst]
      exact congrArg (inactive z :: ·) ih

private theorem trace_pop_chain (g : IndexedGrammar T) [Fintype g.nt]
    (cert : CompositeCert g) (R : CFlag g) (d : IndexMark)
    (h : WorkHistory g) (beta : List (WorkSym g))
    (hprev : h.new1 = some (inactive (nextOr (WorkSym.index R d.markUsed) beta)))
    (hfree : IndexFree beta)
    (hloop : ∀ h old new, InactiveNonIndex old → h.new1 = some old →
      InactiveOpt new → WorkEdge g cert .popBeta .popBeta h old new)
    (hfinish : ∀ h, h.new1 = some (inactive (WorkSym.index R d.markUsed)) →
      WorkEdge g cert .popBeta .stage2 h
        (inactive (WorkSym.index R d)) (inactive WorkSym.dollar)) :
    ∃ h', WorkTrace g cert ⟨.popBeta, h, false, false⟩
      (popChainRows g R d beta) ⟨.stage2, h', false, false⟩ := by
  induction beta generalizing h with
  | nil =>
      refine ⟨updateHistory h (inactive (WorkSym.index R d)) (inactive WorkSym.dollar), ?_⟩
      apply WorkTrace.cons
      · exact ⟨by simp, by simp, by simp [paddingOK], by simp [paddingOK], hfinish h hprev⟩
      · exact .nil _
  | cons z beta ih =>
      have hzfree : z.isIndex = false := by
        cases z with
        | index R' d' => exact False.elim (hfree R' d' (by simp))
        | terminal a => rfl
        | plain A => rfl
        | live A => rfl
        | dollar => rfl
        | close => rfl
        | hash => rfl
      have htailFree : IndexFree beta := by
        intro R' d' hmem
        exact hfree R' d' (by simp [hmem])
      let q := advanceWorkState ⟨.popBeta, h, false, false⟩
        (inactive z) (inactive (nextOr (WorkSym.index R d.markUsed) beta)) .popBeta
      have hqprev : q.history.new1 =
          some (inactive (nextOr (WorkSym.index R d.markUsed) beta)) := by
        simp [q, advanceWorkState, updateHistory]
      rcases ih q.history hqprev htailFree with ⟨h', htrace⟩
      refine ⟨h', .cons ?_ htrace⟩
      refine ⟨by simp, by simp, by simp [paddingOK], by simp [paddingOK],
        hloop h (inactive z) (inactive (nextOr (WorkSym.index R d.markUsed) beta)) ?_ hprev ?_⟩
      · exact ⟨z, rfl, hzfree⟩
      · simp [InactiveOpt, inactive]

public theorem accepts_pop (g : IndexedGrammar T) [Fintype g.nt]
    (cert : CompositeCert g) (R : CFlag g) (d : IndexMark)
    (alpha beta gamma : List (WorkSym g)) (oldFocus newFocus : WorkSym g) (k : ℕ)
    (henabled : CertEnabled g cert) (hproductive : cert.productive = false)
    (hfree : IndexFree beta)
    (hfocus : ∀ h, WorkEdge g cert .stage1 .popBeta h
      (active oldFocus) (inactive (nextOr (WorkSym.index R d.markUsed) beta)))
    (hloopBeta : ∀ h old new, InactiveNonIndex old → h.new1 = some old →
      InactiveOpt new → WorkEdge g cert .popBeta .popBeta h old new)
    (hfinish : ∀ h, h.new1 = some (inactive (WorkSym.index R d.markUsed)) →
      WorkEdge g cert .popBeta .stage2 h
        (inactive (WorkSym.index R d)) (inactive WorkSym.dollar))
    (hnewFocus : ∀ h old, InactiveOpt old →
      WorkEdge g cert .stage2 .stage3 h old (active newFocus))
    (hclose : ∀ h old, InactiveOpt old →
      WorkEdge g cert .stage3 .suffixPlus2 h old (inactive WorkSym.close))
    (hloop2 : ∀ h old new, plus2Suffix h old new →
      WorkEdge g cert .suffixPlus2 .suffixPlus2 h old new) :
    WorkTraceAccepts g cert
      (((alpha ++ [WorkSym.dollar]).map inactive) ++ [active oldFocus] ++
        beta.map inactive ++ [inactive (WorkSym.index R d)] ++ gamma.map inactive ++
        List.replicate (k + 2) none)
      (((alpha ++ [WorkSym.dollar] ++ beta ++
          [WorkSym.index R d.markUsed, WorkSym.dollar]).map inactive) ++
        [active newFocus, inactive WorkSym.close] ++ gamma.map inactive ++
        List.replicate k none) := by
  rcases trace_plain_boundary g cert alpha henabled hproductive with
    ⟨prefixRows, h, hprefix, hold, hnew⟩
  let focusRow := (active oldFocus,
    inactive (nextOr (WorkSym.index R d.markUsed) beta), WorkPhase.popBeta)
  let h₁ := updateHistory h focusRow.1 focusRow.2.1
  have hh₁ : h₁.new1 = some (inactive (nextOr (WorkSym.index R d.markUsed) beta)) := by
    simp [h₁, focusRow, updateHistory]
  rcases trace_pop_chain g cert R d h₁ beta hh₁ hfree hloopBeta hfinish with
    ⟨h₂, hchain⟩
  let xs : List (Option (WorkSlot g)) := gamma.map inactive ++ List.replicate k none
  have hxsPad := paddingStream_inactive_append_none g gamma k
  have hold2 : PaddingStream g false (xs ++ [none, none]) := by
    simpa [xs, List.append_assoc] using hxsPad.append_none.append_none
  have hclosePad : PaddingStream g false (inactive WorkSym.close :: xs) := by
    apply PaddingStream.cons
    · simp [paddingOK]
    · simpa [inactive, xs] using hxsPad
  have hnew2 : PaddingStream g false (active newFocus :: inactive WorkSym.close :: xs) := by
    apply PaddingStream.cons
    · simp [paddingOK]
    · simpa [active] using hclosePad
  have hxsInactive : ∀ x ∈ xs, InactiveOpt x := by
    intro x hx
    simp only [xs, List.mem_append, List.mem_map, List.mem_replicate] at hx
    rcases hx with ⟨z, _, rfl⟩ | ⟨_, rfl⟩ <;> simp [InactiveOpt, inactive]
  rcases trace_plus2_from_stage2 g cert h₂ newFocus WorkSym.close xs hxsInactive
      hold2 hnew2 hnewFocus hclose hloop2 with ⟨result, htail, hphase, hlast⟩
  refine ⟨prefixRows ++ focusRow :: popChainRows g R d beta ++
      plus2FromRows g newFocus WorkSym.close xs, result, ?_, ?_, ?_, ?_⟩
  · have hmid : WorkTrace g cert ⟨.stage1, h, false, false⟩
        (focusRow :: (popChainRows g R d beta ++
          plus2FromRows g newFocus WorkSym.close xs)) result := by
      apply WorkTrace.cons
      · exact ⟨by simp, by simp [focusRow], by simp [paddingOK], by simp [paddingOK], hfocus h⟩
      · exact WorkTrace.append g cert
          (by simpa [advanceWorkState, focusRow, h₁] using hchain) htail
    simpa [List.append_assoc] using WorkTrace.append g cert hprefix hmid
  · simp [focusRow, xs, hold]
    rw [List.replicate_add]
    simp [List.append_assoc]
  · simp only [List.map_append, List.map_cons, List.map_nil]
    rw [hnew]
    rw [show focusRow.2.1 :: (popChainRows g R d beta).map (fun r => r.2.1) =
        beta.map inactive ++ [inactive (WorkSym.index R d.markUsed), inactive WorkSym.dollar] by
      simpa [focusRow] using popChainRows_new g R d beta]
    simp [focusRow, xs, List.map_append, List.append_assoc]
  · unfold workScanDone
    rw [hphase]
    simpa [lastTwoOldNone] using hlast

public theorem accepts_popPlain (g : IndexedGrammar T) [Fintype g.nt]
    {R : CFlag g} {d : IndexMark} {A B : g.nt}
    {alpha beta gamma : List (WorkSym g)} (k : ℕ)
    (hrule : R A B = true) (hfree : IndexFree beta) :
    WorkTraceAccepts g (.popPlain R d A B)
      (((alpha ++ [WorkSym.dollar]).map inactive) ++ [active (WorkSym.live A)] ++
        beta.map inactive ++ [inactive (WorkSym.index R d)] ++ gamma.map inactive ++
        List.replicate (k + 2) none)
      (((alpha ++ [WorkSym.dollar] ++ beta ++
          [WorkSym.index R d.markUsed, WorkSym.dollar]).map inactive) ++
        [active (WorkSym.plain B), inactive WorkSym.close] ++ gamma.map inactive ++
        List.replicate k none) := by
  apply accepts_pop g (.popPlain R d A B) R d alpha beta gamma
    (WorkSym.live A) (WorkSym.plain B) k hrule rfl hfree
  · intro h
    simp [WorkEdge, InactiveSome, hrule]
  · intro h old new hold hprev hnew
    simp [WorkEdge, hrule, hold, hprev, hnew]
  · intro h hprev
    simp [WorkEdge, hrule, hprev]
  · intro h old hold
    simp [WorkEdge, hrule, hold]
  · intro h old hold
    simp [WorkEdge, hrule, hold]
  · intro h old new hs
    simp [WorkEdge, hrule, hs]

public theorem accepts_popLive (g : IndexedGrammar T) [Fintype g.nt]
    {R : CFlag g} {d : IndexMark} {A B : g.nt}
    {alpha beta gamma : List (WorkSym g)} (k : ℕ)
    (hrule : R A B = true) (hlater : d.later = true) (hfree : IndexFree beta) :
    WorkTraceAccepts g (.popLive R d A B)
      (((alpha ++ [WorkSym.dollar]).map inactive) ++ [active (WorkSym.live A)] ++
        beta.map inactive ++ [inactive (WorkSym.index R d)] ++ gamma.map inactive ++
        List.replicate (k + 2) none)
      (((alpha ++ [WorkSym.dollar] ++ beta ++
          [WorkSym.index R d.markUsed, WorkSym.dollar]).map inactive) ++
        [active (WorkSym.live B), inactive WorkSym.close] ++ gamma.map inactive ++
        List.replicate k none) := by
  apply accepts_pop g (.popLive R d A B) R d alpha beta gamma
    (WorkSym.live A) (WorkSym.live B) k ⟨hrule, hlater⟩ rfl hfree
  · intro h
    simp [WorkEdge, InactiveSome, hrule, hlater]
  · intro h old new hold hprev hnew
    simp [WorkEdge, hrule, hlater, hold, hprev, hnew]
  · intro h hprev
    simp [WorkEdge, hrule, hlater, hprev]
  · intro h old hold
    simp [WorkEdge, hrule, hlater, hold]
  · intro h old hold
    simp [WorkEdge, hrule, hlater, hold]
  · intro h old new hs
    simp [WorkEdge, hrule, hlater, hs]

public def plus1FromRows (g : IndexedGrammar T) (inserted : WorkSym g) :
    List (Option (WorkSlot g)) →
      List (Option (WorkSlot g) × Option (WorkSlot g) × WorkPhase)
  | [] => [(none, inactive inserted, .suffixPlus1)]
  | x :: xs => (x, inactive inserted, .suffixPlus1) :: shift1Rows g x xs

public def firstPad : List (Option X) → Option X
  | [] => none
  | x :: _ => x

@[simp] public theorem plus1FromRows_old (g : IndexedGrammar T)
    (inserted : WorkSym g) (xs : List (Option (WorkSlot g))) :
    (plus1FromRows g inserted xs).map (fun r => r.1) = xs ++ [none] := by
  cases xs <;> simp [plus1FromRows]

@[simp] public theorem plus1FromRows_new (g : IndexedGrammar T)
    (inserted : WorkSym g) (xs : List (Option (WorkSlot g))) :
    (plus1FromRows g inserted xs).map (fun r => r.2.1) = inactive inserted :: xs := by
  cases xs <;> simp [plus1FromRows]

private theorem trace_plus1_from_stage2 (g : IndexedGrammar T) [Fintype g.nt]
    (cert : CompositeCert g) (h : WorkHistory g) (inserted : WorkSym g)
    (xs : List (Option (WorkSlot g)))
    (hxsInactive : ∀ x ∈ xs, InactiveOpt x)
    (holdPad : PaddingStream g false (xs ++ [none]))
    (hnewPad : PaddingStream g false (inactive inserted :: xs))
    (hinsert : ∀ h, WorkEdge g cert .stage2 .suffixPlus1 h
      (firstPad xs) (inactive inserted))
    (hloop : ∀ h old new, plus1Suffix h old new →
      WorkEdge g cert .suffixPlus1 .suffixPlus1 h old new) :
    ∃ result,
      WorkTrace g cert ⟨.stage2, h, false, false⟩
        (plus1FromRows g inserted xs) result ∧
      result.phase = .suffixPlus1 ∧ lastOldNone result.history := by
  cases xs with
  | nil =>
      have holdHead : paddingOK false none :=
        (show PaddingStream g false [none] from by simpa using holdPad).head
      have hnewHead : paddingOK false (inactive inserted) := hnewPad.head
      let result := advanceWorkState ⟨.stage2, h, false, false⟩
        none (inactive inserted) .suffixPlus1
      refine ⟨result, ?_, rfl, ?_⟩
      · apply WorkTrace.cons
        · exact ⟨by simp, by simp, holdHead, hnewHead, hinsert h⟩
        · exact .nil _
      · simp [result, advanceWorkState, lastOldNone, updateHistory]
  | cons x xs =>
      have holdCons : PaddingStream g false (x :: (xs ++ [none])) := by
        simpa using holdPad
      have hnewCons : PaddingStream g false (inactive inserted :: x :: xs) := hnewPad
      have hx : InactiveOpt x := hxsInactive x (by simp)
      let q := advanceWorkState ⟨.stage2, h, false, false⟩
        x (inactive inserted) .suffixPlus1
      have hqprev : q.history.old1 = some x := by
        simp [q, advanceWorkState, updateHistory]
      rcases trace_plus1_shift g cert q.history q.oldEnded q.newEnded x xs
          hqprev hx (by intro y hy; exact hxsInactive y (by simp [hy]))
          holdCons.tail hnewCons.tail hloop with ⟨result, hshift, hphase, hlast⟩
      refine ⟨result, .cons ?_ hshift, hphase, hlast⟩
      exact ⟨by simp, by simp, holdCons.head, hnewCons.head, hinsert h⟩

public theorem accepts_insert_one (g : IndexedGrammar T) [Fintype g.nt]
    (cert : CompositeCert g)
    (prefixRows : List (Option (WorkSlot g) × Option (WorkSlot g) × WorkPhase))
    (h : WorkHistory g)
    (hprefix : WorkTrace g cert (initialWorkScan g) prefixRows
      ⟨.stage1, h, false, false⟩)
    (oldFocus newFocus inserted : WorkSym g) (beta : List (WorkSym g)) (k : ℕ)
    (hfocus : ∀ h, WorkEdge g cert .stage1 .stage2 h
      (active oldFocus) (active newFocus))
    (hinsert : ∀ h, WorkEdge g cert .stage2 .suffixPlus1 h
      (firstPad (beta.map inactive ++ List.replicate k none)) (inactive inserted))
    (hloop : ∀ h old new, plus1Suffix h old new →
      WorkEdge g cert .suffixPlus1 .suffixPlus1 h old new) :
    WorkTraceAccepts g cert
      (prefixRows.map (fun r => r.1) ++ [active oldFocus] ++ beta.map inactive ++
        List.replicate (k + 1) none)
      (prefixRows.map (fun r => r.2.1) ++ [active newFocus, inactive inserted] ++
        beta.map inactive ++ List.replicate k none) := by
  let xs : List (Option (WorkSlot g)) := beta.map inactive ++ List.replicate k none
  have hxsPad : PaddingStream g false xs := paddingStream_inactive_append_none g beta k
  have holdPad : PaddingStream g false (xs ++ [none]) := hxsPad.append_none
  have hnewPad : PaddingStream g false (inactive inserted :: xs) :=
    .cons (by simp [paddingOK]) hxsPad
  have hxsInactive : ∀ x ∈ xs, InactiveOpt x := by
    intro x hx
    simp only [xs, List.mem_append, List.mem_map, List.mem_replicate] at hx
    rcases hx with ⟨z, _, rfl⟩ | ⟨_, rfl⟩ <;> simp [InactiveOpt, inactive]
  let focusRow := (active oldFocus, active newFocus, WorkPhase.stage2)
  let h₁ := updateHistory h focusRow.1 focusRow.2.1
  rcases trace_plus1_from_stage2 g cert h₁ inserted xs hxsInactive holdPad hnewPad
      (by simpa [xs] using hinsert) hloop with ⟨result, htail, hphase, hlast⟩
  refine ⟨prefixRows ++ focusRow :: plus1FromRows g inserted xs, result, ?_, ?_, ?_, ?_⟩
  · apply WorkTrace.append g cert hprefix
    apply WorkTrace.cons
    · exact ⟨by simp, by simp [focusRow], by simp [paddingOK], by simp [paddingOK], hfocus h⟩
    · simpa [advanceWorkState, focusRow, h₁] using htail
  · simp [focusRow, xs]
    rw [List.replicate_add]
    simp
  · simp [focusRow, xs]
  · unfold workScanDone
    rw [hphase]
    simpa [lastOldNone] using hlast

@[simp] public theorem firstPad_inactive_padded (g : IndexedGrammar T)
    (beta : List (WorkSym g)) (k : ℕ) :
    InactiveOpt (firstPad (beta.map inactive ++ List.replicate k none)) := by
  cases beta with
  | nil =>
      cases k with
      | zero => simp [firstPad, InactiveOpt]
      | succ k => change InactiveOpt (none : Option (WorkSlot g)); simp [InactiveOpt]
  | cons z beta => simp [firstPad, InactiveOpt, inactive]

public theorem firstPad_inactive_of_all (g : IndexedGrammar T)
    {xs : List (Option (WorkSlot g))}
    (hxs : ∀ x ∈ xs, InactiveOpt x) : InactiveOpt (firstPad xs) := by
  cases xs with
  | nil => simp [firstPad, InactiveOpt]
  | cons x xs => simpa [firstPad] using hxs x (by simp)

@[simp] public theorem length_markProductivePrefix (g : IndexedGrammar T)
    (alpha : List (WorkSym g)) :
    (markProductivePrefix alpha).length = alpha.length := by
  simp only [markProductivePrefix]
  split <;> simp_all

public theorem paddedCursor_eq_append (g : IndexedGrammar T) (n : ℕ)
    (c : WorkCursor g) (hwork : c.word.length ≤ n * workWidth) :
    paddedWork n c.slots =
      c.left.map inactive ++ [active c.focus] ++ c.right.map inactive ++
        List.replicate (n * workWidth - c.word.length) none := by
  rw [paddedWork_eq_append n c.slots (by simpa using hwork)]
  simp [WorkCursor.slots, WorkCursor.word, inactive, active, List.map_map,
    Function.comp_def, List.append_assoc]
  rfl

public theorem accepts_plainBinary (g : IndexedGrammar T) [Fintype g.nt]
    {A B C : g.nt} {alpha beta : List (WorkSym g)} (k : ℕ)
    (hrule : AugBinary g A B C) :
    WorkTraceAccepts g (.plainBinary A B C)
      (((alpha ++ [WorkSym.dollar]).map inactive) ++ [active (WorkSym.plain A)] ++
        beta.map inactive ++ List.replicate (k + 1) none)
      (((markProductivePrefix alpha ++ [WorkSym.dollar]).map inactive) ++
        [active (WorkSym.plain B), inactive (WorkSym.plain C)] ++
        beta.map inactive ++ List.replicate k none) := by
  rcases trace_productive_boundary g (.plainBinary A B C) alpha hrule rfl with
    ⟨prefixRows, h, hprefix, hold, hnew⟩
  have hacc := accepts_insert_one g (.plainBinary A B C) prefixRows h hprefix
    (WorkSym.plain A) (WorkSym.plain B) (WorkSym.plain C) beta k
    (fun h => by simp [WorkEdge, insertOneEdge, hrule])
    (fun h => by simp [WorkEdge, insertOneEdge, hrule, firstPad_inactive_padded])
    (fun h old new hs => by simp [WorkEdge, insertOneEdge, hrule, hs])
  simpa [hold, hnew] using hacc

public theorem accepts_plainPushUse (g : IndexedGrammar T) [Fintype g.nt]
    {A B : g.nt} {f : g.flag} {alpha beta : List (WorkSym g)} (k : ℕ)
    (hrule : AugPush g A B f) :
    WorkTraceAccepts g (.plainPushUse A B f)
      (((alpha ++ [WorkSym.dollar]).map inactive) ++ [active (WorkSym.plain A)] ++
        beta.map inactive ++ List.replicate (k + 1) none)
      (((alpha ++ [WorkSym.dollar]).map inactive) ++
        [active (WorkSym.live B), inactive (WorkSym.index (cflagBase g f) .firstPending)] ++
        beta.map inactive ++ List.replicate k none) := by
  rcases trace_plain_boundary g (.plainPushUse A B f) alpha hrule rfl with
    ⟨prefixRows, h, hprefix, hold, hnew⟩
  have hacc := accepts_insert_one g (.plainPushUse A B f) prefixRows h hprefix
    (WorkSym.plain A) (WorkSym.live B)
    (WorkSym.index (cflagBase g f) .firstPending) beta k
    (fun h => by simp [WorkEdge, insertOneEdge, hrule])
    (fun h => by simp [WorkEdge, insertOneEdge, hrule, firstPad_inactive_padded])
    (fun h old new hs => by simp [WorkEdge, insertOneEdge, hrule, hs])
  simpa [hold, hnew] using hacc

private theorem accepts_live_insert (g : IndexedGrammar T) [Fintype g.nt]
    (cert : CompositeCert g) (alpha : List (WorkSym g))
    (oldFocus newFocus inserted Z : WorkSym g) (beta : List (WorkSym g)) (k : ℕ)
    (henabled : CertEnabled g cert) (hproductive : cert.productive = true)
    (hfocus : ∀ h, WorkEdge g cert .stage1 .stage2 h (active oldFocus) (active newFocus))
    (hinsert : ∀ h, WorkEdge g cert .stage2 .suffixPlus1 h
      (inactive Z) (inactive inserted))
    (hloop : ∀ h old new, plus1Suffix h old new →
      WorkEdge g cert .suffixPlus1 .suffixPlus1 h old new) :
    WorkTraceAccepts g cert
      (((alpha ++ [WorkSym.dollar]).map inactive) ++ [active oldFocus, inactive Z] ++
        beta.map inactive ++ List.replicate (k + 1) none)
      (((markProductivePrefix alpha ++ [WorkSym.dollar]).map inactive) ++
        [active newFocus, inactive inserted, inactive Z] ++
        beta.map inactive ++ List.replicate k none) := by
  rcases trace_productive_boundary g cert alpha henabled hproductive with
    ⟨prefixRows, h, hprefix, hold, hnew⟩
  have hacc := accepts_insert_one g cert prefixRows h hprefix oldFocus newFocus inserted
    (Z :: beta) k hfocus (by simpa [firstPad] using hinsert) hloop
  simpa [hold, hnew] using hacc

public theorem accepts_liveBinaryBoth (g : IndexedGrammar T) [Fintype g.nt]
    {A B C : g.nt} {alpha beta : List (WorkSym g)} {Z : WorkSym g} (k : ℕ)
    (hrule : AugBinary g A B C) :
    WorkTraceAccepts g (.liveBinaryBoth A B C)
      (((alpha ++ [WorkSym.dollar]).map inactive) ++ [active (WorkSym.live A), inactive Z] ++
        beta.map inactive ++ List.replicate (k + 1) none)
      (((markProductivePrefix alpha ++ [WorkSym.dollar]).map inactive) ++
        [active (WorkSym.live B), inactive (WorkSym.live C), inactive Z] ++
        beta.map inactive ++ List.replicate k none) := by
  apply accepts_live_insert g (.liveBinaryBoth A B C) alpha (WorkSym.live A)
    (WorkSym.live B) (WorkSym.live C) Z beta k hrule rfl
  · intro h; simp [WorkEdge, insertOneEdge, hrule]
  · intro h; simp [WorkEdge, insertOneEdge, hrule, InactiveSome, inactive]
  · intro h old new hs; simp [WorkEdge, insertOneEdge, hrule, hs]

public theorem accepts_liveBinaryLeft (g : IndexedGrammar T) [Fintype g.nt]
    {A B C : g.nt} {alpha beta : List (WorkSym g)} {Z : WorkSym g} (k : ℕ)
    (hrule : AugBinary g A B C) :
    WorkTraceAccepts g (.liveBinaryLeft A B C)
      (((alpha ++ [WorkSym.dollar]).map inactive) ++ [active (WorkSym.live A), inactive Z] ++
        beta.map inactive ++ List.replicate (k + 1) none)
      (((markProductivePrefix alpha ++ [WorkSym.dollar]).map inactive) ++
        [active (WorkSym.live B), inactive (WorkSym.plain C), inactive Z] ++
        beta.map inactive ++ List.replicate k none) := by
  apply accepts_live_insert g (.liveBinaryLeft A B C) alpha (WorkSym.live A)
    (WorkSym.live B) (WorkSym.plain C) Z beta k hrule rfl
  · intro h; simp [WorkEdge, insertOneEdge, hrule]
  · intro h; simp [WorkEdge, insertOneEdge, hrule, InactiveSome, inactive]
  · intro h old new hs; simp [WorkEdge, insertOneEdge, hrule, hs]

public theorem accepts_liveBinaryRight (g : IndexedGrammar T) [Fintype g.nt]
    {A B C : g.nt} {alpha beta : List (WorkSym g)} {Z : WorkSym g} (k : ℕ)
    (hrule : AugBinary g A B C) :
    WorkTraceAccepts g (.liveBinaryRight A B C)
      (((alpha ++ [WorkSym.dollar]).map inactive) ++ [active (WorkSym.live A), inactive Z] ++
        beta.map inactive ++ List.replicate (k + 1) none)
      (((markProductivePrefix alpha ++ [WorkSym.dollar]).map inactive) ++
        [active (WorkSym.plain B), inactive (WorkSym.live C), inactive Z] ++
        beta.map inactive ++ List.replicate k none) := by
  apply accepts_live_insert g (.liveBinaryRight A B C) alpha (WorkSym.live A)
    (WorkSym.plain B) (WorkSym.live C) Z beta k hrule rfl
  · intro h; simp [WorkEdge, insertOneEdge, hrule]
  · intro h; simp [WorkEdge, insertOneEdge, hrule, InactiveSome, inactive]
  · intro h old new hs; simp [WorkEdge, insertOneEdge, hrule, hs]

public theorem accepts_livePushFresh (g : IndexedGrammar T) [Fintype g.nt]
    {A B : g.nt} {f : g.flag} {alpha beta : List (WorkSym g)} {Z : WorkSym g} (k : ℕ)
    (hrule : AugPush g A B f) :
    WorkTraceAccepts g (.livePushFresh A B f)
      (((alpha ++ [WorkSym.dollar]).map inactive) ++ [active (WorkSym.live A), inactive Z] ++
        beta.map inactive ++ List.replicate (k + 1) none)
      (((alpha ++ [WorkSym.dollar]).map inactive) ++
        [active (WorkSym.live B), inactive (WorkSym.index (cflagBase g f) .laterPending), inactive Z] ++
        beta.map inactive ++ List.replicate k none) := by
  rcases trace_plain_boundary g (.livePushFresh A B f) alpha hrule rfl with
    ⟨prefixRows, h, hprefix, hold, hnew⟩
  have hacc := accepts_insert_one g (.livePushFresh A B f) prefixRows h hprefix
    (WorkSym.live A) (WorkSym.live B) (WorkSym.index (cflagBase g f) .laterPending)
    (Z :: beta) k
    (fun h => by simp [WorkEdge, insertOneEdge, hrule])
    (fun h => by simp [WorkEdge, insertOneEdge, hrule, firstPad, InactiveSome, inactive])
    (fun h old new hs => by simp [WorkEdge, insertOneEdge, hrule, hs])
  simpa [hold, hnew] using hacc

public theorem accepts_replace_two (g : IndexedGrammar T) [Fintype g.nt]
    (cert : CompositeCert g)
    (prefixRows : List (Option (WorkSlot g) × Option (WorkSlot g) × WorkPhase))
    (h : WorkHistory g)
    (hprefix : WorkTrace g cert (initialWorkScan g) prefixRows
      ⟨.stage1, h, false, false⟩)
    (oldFocus newFocus oldNext newNext : WorkSym g)
    (beta : List (WorkSym g)) (k : ℕ)
    (hfocus : ∀ h, WorkEdge g cert .stage1 .stage2 h
      (active oldFocus) (active newFocus))
    (hnext : ∀ h, WorkEdge g cert .stage2 .suffixSame h
      (inactive oldNext) (inactive newNext))
    (hloop : ∀ h x, InactiveOpt x →
      WorkEdge g cert .suffixSame .suffixSame h x x) :
    WorkTraceAccepts g cert
      (prefixRows.map (fun r => r.1) ++ [active oldFocus, inactive oldNext] ++
        beta.map inactive ++ List.replicate k none)
      (prefixRows.map (fun r => r.2.1) ++ [active newFocus, inactive newNext] ++
        beta.map inactive ++ List.replicate k none) := by
  let focusRow := (active oldFocus, active newFocus, WorkPhase.stage2)
  let nextRow := (inactive oldNext, inactive newNext, WorkPhase.suffixSame)
  let h₁ := updateHistory h focusRow.1 focusRow.2.1
  let h₂ := updateHistory h₁ nextRow.1 nextRow.2.1
  rcases trace_same_suffix_padded g cert h₂ beta k hloop with
    ⟨result, hsuffix, hphase⟩
  refine ⟨prefixRows ++ [focusRow, nextRow] ++ sameSuffixRows
      (beta.map inactive ++ List.replicate k none), result, ?_, ?_, ?_, ?_⟩
  · have htail : WorkTrace g cert ⟨.stage1, h, false, false⟩
        ([focusRow, nextRow] ++ sameSuffixRows
          (beta.map inactive ++ List.replicate k none)) result := by
      apply WorkTrace.cons
      · exact ⟨by simp, by simp [focusRow], by simp [paddingOK], by simp [paddingOK], hfocus h⟩
      · apply WorkTrace.cons
        · exact ⟨by simp [advanceWorkState], by simp [nextRow],
            by simp [advanceWorkState, paddingOK, active, inactive],
            by simp [advanceWorkState, paddingOK, active, inactive], hnext h₁⟩
        · simpa [advanceWorkState, focusRow, nextRow, h₁, h₂] using hsuffix
    simpa [List.append_assoc] using WorkTrace.append g cert hprefix htail
  · simp [focusRow, nextRow, sameSuffixRows]
  · simp [focusRow, nextRow, sameSuffixRows]
  · unfold workScanDone
    rw [hphase]
    simp

public theorem accepts_livePushCompress (g : IndexedGrammar T) [Fintype g.nt]
    {A B : g.nt} {f : g.flag} {R : CFlag g} {d : IndexMark}
    {alpha beta : List (WorkSym g)} (k : ℕ)
    (hrule : AugPush g A B f) (hcomp : (cflagComp g (cflagBase g f) R).Nonempty) :
    WorkTraceAccepts g (.livePushCompress A B f R d)
      (((alpha ++ [WorkSym.dollar]).map inactive) ++
        [active (WorkSym.live A), inactive (WorkSym.index R d)] ++
        beta.map inactive ++ List.replicate k none)
      (((alpha ++ [WorkSym.dollar]).map inactive) ++
        [active (WorkSym.live B),
          inactive (WorkSym.index (cflagComp g (cflagBase g f) R) d)] ++
        beta.map inactive ++ List.replicate k none) := by
  rcases trace_plain_boundary g (.livePushCompress A B f R d) alpha
      ⟨hrule, hcomp⟩ rfl with ⟨prefixRows, h, hprefix, hold, hnew⟩
  have hacc := accepts_replace_two g (.livePushCompress A B f R d) prefixRows h hprefix
    (WorkSym.live A) (WorkSym.live B) (WorkSym.index R d)
    (WorkSym.index (cflagComp g (cflagBase g f) R) d) beta k
    (fun h => by simp [WorkEdge, replaceTwoEdge, hrule, hcomp])
    (fun h => by simp [WorkEdge, replaceTwoEdge, hrule, hcomp])
    (fun h x hx => by simp [WorkEdge, replaceTwoEdge, hrule, hcomp, sameSuffix, hx])
  simpa [hold, hnew] using hacc

public def minus1ShiftRows (g : IndexedGrammar T) (prev : Option (WorkSlot g)) :
    List (Option (WorkSlot g)) →
      List (Option (WorkSlot g) × Option (WorkSlot g) × WorkPhase)
  | [] => [(prev, none, .suffixMinus1)]
  | x :: xs => (prev, x, .suffixMinus1) :: minus1ShiftRows g x xs

@[simp] public theorem minus1ShiftRows_old (g : IndexedGrammar T)
    (prev : Option (WorkSlot g)) (xs : List (Option (WorkSlot g))) :
    (minus1ShiftRows g prev xs).map (fun r => r.1) = prev :: xs := by
  induction xs generalizing prev with
  | nil => rfl
  | cons x xs ih => simp [minus1ShiftRows, ih]

@[simp] public theorem minus1ShiftRows_new (g : IndexedGrammar T)
    (prev : Option (WorkSlot g)) (xs : List (Option (WorkSlot g))) :
    (minus1ShiftRows g prev xs).map (fun r => r.2.1) = xs ++ [none] := by
  induction xs generalizing prev with
  | nil => rfl
  | cons x xs ih => simp [minus1ShiftRows, ih]

private theorem trace_minus1_shift (g : IndexedGrammar T) [Fintype g.nt]
    (cert : CompositeCert g) (h : WorkHistory g) (oldEnded newEnded : Bool)
    (prev : Option (WorkSlot g)) (xs : List (Option (WorkSlot g)))
    (hprev : h.new1 = some prev) (hprevInactive : InactiveOpt prev)
    (hxsInactive : ∀ x ∈ xs, InactiveOpt x)
    (holdPad : PaddingStream g oldEnded (prev :: xs))
    (hnewPad : PaddingStream g newEnded (xs ++ [none]))
    (hloop : ∀ h old new, minus1Suffix h old new →
      WorkEdge g cert .suffixMinus1 .suffixMinus1 h old new) :
    ∃ result,
      WorkTrace g cert ⟨.suffixMinus1, h, oldEnded, newEnded⟩
        (minus1ShiftRows g prev xs) result ∧
      result.phase = .suffixMinus1 ∧ lastNewNone result.history := by
  cases xs with
  | nil =>
      have holdHead : paddingOK oldEnded prev := holdPad.head
      have hnewHead : paddingOK newEnded none :=
        (show PaddingStream g newEnded [none] from by simpa using hnewPad).head
      let result := advanceWorkState ⟨.suffixMinus1, h, oldEnded, newEnded⟩
        prev none .suffixMinus1
      refine ⟨result, ?_, rfl, ?_⟩
      · apply WorkTrace.cons
        · refine ⟨by simp, by simp, holdHead, hnewHead, hloop h prev none ?_⟩
          exact ⟨hprevInactive, by simp [InactiveOpt], hprev⟩
        · exact .nil _
      · simp [result, advanceWorkState, lastNewNone, updateHistory]
  | cons x xs =>
      have holdCons : PaddingStream g oldEnded (prev :: x :: xs) := holdPad
      have hnewCons : PaddingStream g newEnded (x :: (xs ++ [none])) := by
        simpa using hnewPad
      have hx : InactiveOpt x := hxsInactive x (by simp)
      let q := advanceWorkState ⟨.suffixMinus1, h, oldEnded, newEnded⟩
        prev x .suffixMinus1
      have hqprev : q.history.new1 = some x := by
        simp [q, advanceWorkState, updateHistory]
      rcases trace_minus1_shift g cert q.history q.oldEnded q.newEnded x xs
          hqprev hx (by intro y hy; exact hxsInactive y (by simp [hy]))
          holdCons.tail hnewCons.tail hloop with ⟨result, hshift, hphase, hlast⟩
      refine ⟨result, .cons ?_ hshift, hphase, hlast⟩
      exact ⟨by simp, by simp, holdCons.head, hnewCons.head,
        hloop h prev x ⟨hprevInactive, hx, hprev⟩⟩
termination_by xs.length

public def minus1FromRows (g : IndexedGrammar T) (nextFocus : WorkSym g) :
    List (Option (WorkSlot g)) →
      List (Option (WorkSlot g) × Option (WorkSlot g) × WorkPhase)
  | [] => [(inactive nextFocus, none, .suffixMinus1)]
  | x :: xs => (inactive nextFocus, x, .suffixMinus1) :: minus1ShiftRows g x xs

@[simp] public theorem minus1FromRows_old (g : IndexedGrammar T)
    (nextFocus : WorkSym g) (xs : List (Option (WorkSlot g))) :
    (minus1FromRows g nextFocus xs).map (fun r => r.1) = inactive nextFocus :: xs := by
  cases xs <;> simp [minus1FromRows]

@[simp] public theorem minus1FromRows_new (g : IndexedGrammar T)
    (nextFocus : WorkSym g) (xs : List (Option (WorkSlot g))) :
    (minus1FromRows g nextFocus xs).map (fun r => r.2.1) = xs ++ [none] := by
  cases xs <;> simp [minus1FromRows]

private theorem trace_minus1_from_first (g : IndexedGrammar T) [Fintype g.nt]
    (cert : CompositeCert g) (h : WorkHistory g) (nextFocus : WorkSym g)
    (xs : List (Option (WorkSlot g)))
    (hactive : h.new1 = some (active nextFocus))
    (hxsInactive : ∀ x ∈ xs, InactiveOpt x)
    (holdPad : PaddingStream g false (inactive nextFocus :: xs))
    (hnewPad : PaddingStream g false (xs ++ [none]))
    (hfirst : ∀ h, h.new1 = some (active nextFocus) →
      WorkEdge g cert .minus1First .suffixMinus1 h
        (inactive nextFocus) (firstPad xs))
    (hloop : ∀ h old new, minus1Suffix h old new →
      WorkEdge g cert .suffixMinus1 .suffixMinus1 h old new) :
    ∃ result,
      WorkTrace g cert ⟨.minus1First, h, false, false⟩
        (minus1FromRows g nextFocus xs) result ∧
      result.phase = .suffixMinus1 ∧ lastNewNone result.history := by
  cases xs with
  | nil =>
      have holdHead : paddingOK false (inactive nextFocus) := holdPad.head
      have hnewHead : paddingOK false none :=
        (show PaddingStream g false [none] from by simpa using hnewPad).head
      let result := advanceWorkState ⟨.minus1First, h, false, false⟩
        (inactive nextFocus) none .suffixMinus1
      refine ⟨result, ?_, rfl, ?_⟩
      · apply WorkTrace.cons
        · exact ⟨by simp, by simp, holdHead, hnewHead, hfirst h hactive⟩
        · exact .nil _
      · simp [result, advanceWorkState, lastNewNone, updateHistory]
  | cons x xs =>
      have holdCons : PaddingStream g false (inactive nextFocus :: x :: xs) := holdPad
      have hnewCons : PaddingStream g false (x :: (xs ++ [none])) := by
        simpa using hnewPad
      have hx : InactiveOpt x := hxsInactive x (by simp)
      let q := advanceWorkState ⟨.minus1First, h, false, false⟩
        (inactive nextFocus) x .suffixMinus1
      have hqprev : q.history.new1 = some x := by
        simp [q, advanceWorkState, updateHistory]
      rcases trace_minus1_shift g cert q.history q.oldEnded q.newEnded x xs
          hqprev hx (by intro y hy; exact hxsInactive y (by simp [hy]))
          holdCons.tail hnewCons.tail hloop with ⟨result, hshift, hphase, hlast⟩
      refine ⟨result, .cons ?_ hshift, hphase, hlast⟩
      exact ⟨by simp, by simp, holdCons.head, hnewCons.head, hfirst h hactive⟩

/-- Shift a suffix left after a preceding focus-replacement row has entered `stage2`.  The
first old square is the adjacent ephemeral index being deleted. -/
private theorem trace_minus1_from_minus1First (g : IndexedGrammar T) [Fintype g.nt]
    (cert : CompositeCert g) (h : WorkHistory g) (deletedNext : WorkSym g)
    (xs : List (Option (WorkSlot g)))
    (hxsInactive : ∀ x ∈ xs, InactiveOpt x)
    (holdPad : PaddingStream g false (inactive deletedNext :: xs))
    (hnewPad : PaddingStream g false (xs ++ [none]))
    (hfirst : ∀ h, WorkEdge g cert .minus1First .suffixMinus1 h
      (inactive deletedNext) (firstPad xs))
    (hloop : ∀ h old new, minus1Suffix h old new →
      WorkEdge g cert .suffixMinus1 .suffixMinus1 h old new) :
    ∃ result,
      WorkTrace g cert ⟨.minus1First, h, false, false⟩
        (minus1FromRows g deletedNext xs) result ∧
      result.phase = .suffixMinus1 ∧ lastNewNone result.history := by
  cases xs with
  | nil =>
      have holdHead : paddingOK false (inactive deletedNext) := holdPad.head
      have hnewHead : paddingOK false none :=
        (show PaddingStream g false [none] from by simpa using hnewPad).head
      let result := advanceWorkState ⟨.minus1First, h, false, false⟩
        (inactive deletedNext) none .suffixMinus1
      refine ⟨result, ?_, rfl, ?_⟩
      · apply WorkTrace.cons
        · exact ⟨by simp, by simp, holdHead, hnewHead, hfirst h⟩
        · exact .nil _
      · simp [result, advanceWorkState, lastNewNone, updateHistory]
  | cons x xs =>
      have holdCons : PaddingStream g false (inactive deletedNext :: x :: xs) := holdPad
      have hnewCons : PaddingStream g false (x :: (xs ++ [none])) := by
        simpa using hnewPad
      have hx : InactiveOpt x := hxsInactive x (by simp)
      let q := advanceWorkState ⟨.minus1First, h, false, false⟩
        (inactive deletedNext) x .suffixMinus1
      have hqprev : q.history.new1 = some x := by
        simp [q, advanceWorkState, updateHistory]
      rcases trace_minus1_shift g cert q.history q.oldEnded q.newEnded x xs
          hqprev hx (by intro y hy; exact hxsInactive y (by simp [hy]))
          holdCons.tail hnewCons.tail hloop with ⟨result, hshift, hphase, hlast⟩
      refine ⟨result, .cons ?_ hshift, hphase, hlast⟩
      exact ⟨by simp, by simp, holdCons.head, hnewCons.head, hfirst h⟩

/-- Replace the active task and delete its immediately adjacent index in the same certified
scan.  This is the row-level implementation of ephemeral pop-and-erase. -/
public theorem accepts_replace_delete_next (g : IndexedGrammar T) [Fintype g.nt]
    (cert : CompositeCert g) (alpha beta : List (WorkSym g))
    (oldFocus newFocus deletedNext : WorkSym g) (k : ℕ)
    (henabled : CertEnabled g cert) (hproductive : cert.productive = false)
    (hfocus : ∀ h, WorkEdge g cert .stage1 .minus1First h
      (active oldFocus) (active newFocus))
    (hfirst : ∀ h, WorkEdge g cert .minus1First .suffixMinus1 h
      (inactive deletedNext)
      (firstPad (beta.map inactive ++ List.replicate k none)))
    (hloop : ∀ h old new, minus1Suffix h old new →
      WorkEdge g cert .suffixMinus1 .suffixMinus1 h old new) :
    WorkTraceAccepts g cert
      (((alpha ++ [WorkSym.dollar]).map inactive) ++
        [active oldFocus, inactive deletedNext] ++ beta.map inactive ++
          List.replicate k none)
      (((alpha ++ [WorkSym.dollar]).map inactive) ++ [active newFocus] ++
        beta.map inactive ++ List.replicate (k + 1) none) := by
  rcases trace_plain_boundary g cert alpha henabled hproductive with
    ⟨prefixRows, h, hprefix, hold, hnew⟩
  let xs : List (Option (WorkSlot g)) := beta.map inactive ++ List.replicate k none
  have hxsPad : PaddingStream g false xs := paddingStream_inactive_append_none g beta k
  have holdPad : PaddingStream g false (inactive deletedNext :: xs) :=
    .cons (by simp [paddingOK]) hxsPad
  have hnewPad : PaddingStream g false (xs ++ [none]) := hxsPad.append_none
  have hxsInactive : ∀ x ∈ xs, InactiveOpt x := by
    intro x hx
    simp only [xs, List.mem_append, List.mem_map, List.mem_replicate] at hx
    rcases hx with ⟨z, _, rfl⟩ | ⟨_, rfl⟩ <;> simp [InactiveOpt, inactive]
  let focusRow := (active oldFocus, active newFocus, WorkPhase.minus1First)
  let h₁ := updateHistory h focusRow.1 focusRow.2.1
  rcases trace_minus1_from_minus1First g cert h₁ deletedNext xs hxsInactive
      holdPad hnewPad (by simpa [xs] using hfirst) hloop with
    ⟨result, htail, hphase, hlast⟩
  refine ⟨prefixRows ++ focusRow :: minus1FromRows g deletedNext xs,
    result, ?_, ?_, ?_, ?_⟩
  · apply WorkTrace.append g cert hprefix
    apply WorkTrace.cons
    · exact ⟨by simp, by simp [focusRow], by simp [paddingOK], by simp [paddingOK],
        hfocus h⟩
    · simpa [advanceWorkState, focusRow, h₁] using htail
  · simp [focusRow, xs, hold]
  · simp [focusRow, xs, hnew]
    rw [List.replicate_add]
    simp
  · unfold workScanDone
    rw [hphase]
    simpa [lastNewNone] using hlast

/-- Certified adjacent pop-and-erase trace for a plain residual task. -/
public theorem accepts_popPlainErase (g : IndexedGrammar T) [Fintype g.nt]
    {R : CFlag g} {d : IndexMark} {A B : g.nt}
    {alpha gamma : List (WorkSym g)} (k : ℕ) (hrule : R A B = true) :
    WorkTraceAccepts g (.popPlain R d A B)
      (((alpha ++ [WorkSym.dollar]).map inactive) ++
        [active (WorkSym.live A), inactive (WorkSym.index R d)] ++
        gamma.map inactive ++ List.replicate k none)
      (((alpha ++ [WorkSym.dollar]).map inactive) ++
        [active (WorkSym.plain B)] ++ gamma.map inactive ++
        List.replicate (k + 1) none) := by
  apply accepts_replace_delete_next g (.popPlain R d A B) alpha gamma
    (WorkSym.live A) (WorkSym.plain B) (WorkSym.index R d) k hrule rfl
  · intro h
    simp [WorkEdge, hrule]
  · intro h
    simp [WorkEdge, hrule, firstPad_inactive_padded]
  · intro h old new hs
    simp [WorkEdge, hrule, hs]

/-- Certified adjacent pop-and-erase trace for a live residual task. -/
public theorem accepts_popLiveErase (g : IndexedGrammar T) [Fintype g.nt]
    {R : CFlag g} {d : IndexMark} {A B : g.nt}
    {alpha gamma : List (WorkSym g)} (k : ℕ)
    (hrule : R A B = true) (hlater : d.later = true) :
    WorkTraceAccepts g (.popLive R d A B)
      (((alpha ++ [WorkSym.dollar]).map inactive) ++
        [active (WorkSym.live A), inactive (WorkSym.index R d)] ++
        gamma.map inactive ++ List.replicate k none)
      (((alpha ++ [WorkSym.dollar]).map inactive) ++
        [active (WorkSym.live B)] ++ gamma.map inactive ++
        List.replicate (k + 1) none) := by
  apply accepts_replace_delete_next g (.popLive R d A B) alpha gamma
    (WorkSym.live A) (WorkSym.live B) (WorkSym.index R d) k
    ⟨hrule, hlater⟩ rfl
  · intro h
    simp [WorkEdge, hrule, hlater]
  · intro h
    simp [WorkEdge, hrule, hlater, firstPad_inactive_padded]
  · intro h old new hs
    simp [WorkEdge, hrule, hlater, hs]

public theorem accepts_delete_one (g : IndexedGrammar T) [Fintype g.nt]
    (cert : CompositeCert g)
    (prefixRows : List (Option (WorkSlot g) × Option (WorkSlot g) × WorkPhase))
    (h : WorkHistory g)
    (hprefix : WorkTrace g cert (initialWorkScan g) prefixRows
      ⟨.stage1, h, false, false⟩)
    (deleted nextFocus : WorkSym g) (beta : List (WorkSym g)) (k : ℕ)
    (hfocus : ∀ h, WorkEdge g cert .stage1 .minus1First h
      (active deleted) (active nextFocus))
    (hfirst : ∀ h, h.new1 = some (active nextFocus) →
      WorkEdge g cert .minus1First .suffixMinus1 h
        (inactive nextFocus)
        (firstPad (beta.map inactive ++ List.replicate k none)))
    (hloop : ∀ h old new, minus1Suffix h old new →
      WorkEdge g cert .suffixMinus1 .suffixMinus1 h old new) :
    WorkTraceAccepts g cert
      (prefixRows.map (fun r => r.1) ++ [active deleted, inactive nextFocus] ++
        beta.map inactive ++ List.replicate k none)
      (prefixRows.map (fun r => r.2.1) ++ [active nextFocus] ++
        beta.map inactive ++ List.replicate (k + 1) none) := by
  let xs : List (Option (WorkSlot g)) := beta.map inactive ++ List.replicate k none
  have hxsPad : PaddingStream g false xs := paddingStream_inactive_append_none g beta k
  have holdPad : PaddingStream g false (inactive nextFocus :: xs) :=
    .cons (by simp [paddingOK]) hxsPad
  have hnewPad : PaddingStream g false (xs ++ [none]) := hxsPad.append_none
  have hxsInactive : ∀ x ∈ xs, InactiveOpt x := by
    intro x hx
    simp only [xs, List.mem_append, List.mem_map, List.mem_replicate] at hx
    rcases hx with ⟨z, _, rfl⟩ | ⟨_, rfl⟩ <;> simp [InactiveOpt, inactive]
  let focusRow := (active deleted, active nextFocus, WorkPhase.minus1First)
  let h₁ := updateHistory h focusRow.1 focusRow.2.1
  have hactive : h₁.new1 = some (active nextFocus) := by
    simp [h₁, focusRow, updateHistory]
  rcases trace_minus1_from_first g cert h₁ nextFocus xs hactive hxsInactive
      holdPad hnewPad (by simpa [xs] using hfirst) hloop with
    ⟨result, htail, hphase, hlast⟩
  refine ⟨prefixRows ++ focusRow :: minus1FromRows g nextFocus xs,
    result, ?_, ?_, ?_, ?_⟩
  · apply WorkTrace.append g cert hprefix
    apply WorkTrace.cons
    · exact ⟨by simp, by simp [focusRow], by simp [paddingOK], by simp [paddingOK], hfocus h⟩
    · simpa [advanceWorkState, focusRow, h₁] using htail
  · simp [focusRow, xs]
  · simp [focusRow, xs]
    rw [List.replicate_add]
    simp
  · unfold workScanDone
    rw [hphase]
    simpa [lastNewNone] using hlast

public theorem accepts_matchTerminal (g : IndexedGrammar T) [Fintype g.nt]
    {a : T} {alpha beta : List (WorkSym g)} {Z : WorkSym g} (k : ℕ) :
    WorkTraceAccepts g (.matchTerminal a)
      (((alpha ++ [WorkSym.dollar]).map inactive) ++
        [active (WorkSym.terminal a), inactive Z] ++
        beta.map inactive ++ List.replicate k none)
      (((alpha ++ [WorkSym.dollar]).map inactive) ++ [active Z] ++
        beta.map inactive ++ List.replicate (k + 1) none) := by
  rcases trace_plain_boundary g (.matchTerminal a) alpha trivial rfl with
    ⟨prefixRows, h, hprefix, hold, hnew⟩
  have hacc := accepts_delete_one g (.matchTerminal a) prefixRows h hprefix
    (WorkSym.terminal a) Z beta k
    (fun h => by simp [WorkEdge, deleteOneEdge])
    (fun h hh => by
      simp [WorkEdge, deleteOneEdge, sameSymbolFirstMinus1, hh,
        firstPad_inactive_padded, prefixEdge]
      exact ⟨Z, rfl, rfl⟩)
    (fun h old new hs => by simp [WorkEdge, deleteOneEdge, hs])
  simpa [hold, hnew] using hacc

public theorem accepts_eraseIndex (g : IndexedGrammar T) [Fintype g.nt]
    {R : CFlag g} {d : IndexMark} {alpha beta : List (WorkSym g)}
    {Z : WorkSym g} (k : ℕ) (herase : d.erasable = true) :
    WorkTraceAccepts g (.eraseIndex R d)
      (((alpha ++ [WorkSym.dollar]).map inactive) ++
        [active (WorkSym.index R d), inactive Z] ++
        beta.map inactive ++ List.replicate k none)
      (((alpha ++ [WorkSym.dollar]).map inactive) ++ [active Z] ++
        beta.map inactive ++ List.replicate (k + 1) none) := by
  rcases trace_plain_boundary g (.eraseIndex R d) alpha herase rfl with
    ⟨prefixRows, h, hprefix, hold, hnew⟩
  have hacc := accepts_delete_one g (.eraseIndex R d) prefixRows h hprefix
    (WorkSym.index R d) Z beta k
    (fun h => by simp [WorkEdge, deleteOneEdge, herase])
    (fun h hh => by
      simp [WorkEdge, deleteOneEdge, herase, sameSymbolFirstMinus1, hh,
        firstPad_inactive_padded, prefixEdge]
      exact ⟨Z, rfl, rfl⟩)
    (fun h old new hs => by simp [WorkEdge, deleteOneEdge, herase, hs])
  simpa [hold, hnew] using hacc

namespace LegacyPlus2

public def plus2ShiftRows (g : IndexedGrammar T)
    (prev2 prev1 : Option (WorkSlot g)) : List (Option (WorkSlot g)) →
      List (Option (WorkSlot g) × Option (WorkSlot g) × WorkPhase)
  | [] => [(none, prev2, .suffixPlus2), (none, prev1, .suffixPlus2)]
  | x :: xs => (x, prev2, .suffixPlus2) :: plus2ShiftRows g prev1 x xs

@[simp] public theorem plus2ShiftRows_old (g : IndexedGrammar T)
    (prev2 prev1 : Option (WorkSlot g)) (xs : List (Option (WorkSlot g))) :
    (plus2ShiftRows g prev2 prev1 xs).map (fun r => r.1) = xs ++ [none, none] := by
  induction xs generalizing prev2 prev1 with
  | nil => rfl
  | cons x xs ih => simp [plus2ShiftRows, ih]

@[simp] public theorem plus2ShiftRows_new (g : IndexedGrammar T)
    (prev2 prev1 : Option (WorkSlot g)) (xs : List (Option (WorkSlot g))) :
    (plus2ShiftRows g prev2 prev1 xs).map (fun r => r.2.1) = prev2 :: prev1 :: xs := by
  induction xs generalizing prev2 prev1 with
  | nil => rfl
  | cons x xs ih => simp [plus2ShiftRows, ih]

private theorem trace_plus2_shift (g : IndexedGrammar T) [Fintype g.nt]
    (cert : CompositeCert g) (h : WorkHistory g) (oldEnded newEnded : Bool)
    (prev2 prev1 : Option (WorkSlot g)) (xs : List (Option (WorkSlot g)))
    (hprev2 : h.old2 = some prev2) (hprev1 : h.old1 = some prev1)
    (hinactive2 : InactiveOpt prev2) (hinactive1 : InactiveOpt prev1)
    (hxsInactive : ∀ x ∈ xs, InactiveOpt x)
    (holdPad : PaddingStream g oldEnded (xs ++ [none, none]))
    (hnewPad : PaddingStream g newEnded (prev2 :: prev1 :: xs))
    (hloop : ∀ h old new, plus2Suffix h old new →
      WorkEdge g cert .suffixPlus2 .suffixPlus2 h old new) :
    ∃ result,
      WorkTrace g cert ⟨.suffixPlus2, h, oldEnded, newEnded⟩
        (plus2ShiftRows g prev2 prev1 xs) result ∧
      result.phase = .suffixPlus2 ∧ lastTwoOldNone result.history := by
  cases xs with
  | nil =>
      have holdCons : PaddingStream g oldEnded [none, none] := by simpa using holdPad
      have hnewCons : PaddingStream g newEnded [prev2, prev1] := hnewPad
      let q := advanceWorkState ⟨.suffixPlus2, h, oldEnded, newEnded⟩
        none prev2 .suffixPlus2
      let result := advanceWorkState q none prev1 .suffixPlus2
      refine ⟨result, ?_, rfl, ?_⟩
      · apply WorkTrace.cons
        · refine ⟨by simp, by simp, holdCons.head, hnewCons.head,
            hloop h none prev2 ⟨by simp [InactiveOpt], hinactive2, hprev2⟩⟩
        · apply WorkTrace.cons
          · refine ⟨by simp [q, advanceWorkState], by simp,
              holdCons.tail.head, hnewCons.tail.head, hloop q.history none prev1 ?_⟩
            refine ⟨by simp [InactiveOpt], hinactive1, ?_⟩
            simp [q, advanceWorkState, updateHistory, hprev1]
          · exact .nil _
      · simp [result, q, advanceWorkState, lastTwoOldNone, updateHistory]
  | cons x xs =>
      have holdCons : PaddingStream g oldEnded (x :: (xs ++ [none, none])) := by
        simpa using holdPad
      have hnewCons : PaddingStream g newEnded (prev2 :: prev1 :: x :: xs) := hnewPad
      have hx : InactiveOpt x := hxsInactive x (by simp)
      let q := advanceWorkState ⟨.suffixPlus2, h, oldEnded, newEnded⟩
        x prev2 .suffixPlus2
      have hq2 : q.history.old2 = some prev1 := by
        simp [q, advanceWorkState, updateHistory, hprev1]
      have hq1 : q.history.old1 = some x := by
        simp [q, advanceWorkState, updateHistory]
      rcases trace_plus2_shift g cert q.history q.oldEnded q.newEnded prev1 x xs
          hq2 hq1 hinactive1 hx (by intro y hy; exact hxsInactive y (by simp [hy]))
          holdCons.tail hnewCons.tail hloop with ⟨result, hshift, hphase, hlast⟩
      refine ⟨result, .cons ?_ hshift, hphase, hlast⟩
      exact ⟨by simp, by simp, holdCons.head, hnewCons.head,
        hloop h x prev2 ⟨hx, hinactive2, hprev2⟩⟩
termination_by xs.length

end LegacyPlus2

public def minus2ShiftRows (g : IndexedGrammar T)
    (prev2 prev1 : Option (WorkSlot g)) : List (Option (WorkSlot g)) →
      List (Option (WorkSlot g) × Option (WorkSlot g) × WorkPhase)
  | [] => [(prev2, none, .suffixMinus2), (prev1, none, .suffixMinus2)]
  | x :: xs => (prev2, x, .suffixMinus2) :: minus2ShiftRows g prev1 x xs

@[simp] public theorem minus2ShiftRows_old (g : IndexedGrammar T)
    (prev2 prev1 : Option (WorkSlot g)) (xs : List (Option (WorkSlot g))) :
    (minus2ShiftRows g prev2 prev1 xs).map (fun r => r.1) = prev2 :: prev1 :: xs := by
  induction xs generalizing prev2 prev1 with
  | nil => rfl
  | cons x xs ih => simp [minus2ShiftRows, ih]

@[simp] public theorem minus2ShiftRows_new (g : IndexedGrammar T)
    (prev2 prev1 : Option (WorkSlot g)) (xs : List (Option (WorkSlot g))) :
    (minus2ShiftRows g prev2 prev1 xs).map (fun r => r.2.1) = xs ++ [none, none] := by
  induction xs generalizing prev2 prev1 with
  | nil => rfl
  | cons x xs ih => simp [minus2ShiftRows, ih]

private theorem trace_minus2_shift (g : IndexedGrammar T) [Fintype g.nt]
    (cert : CompositeCert g) (h : WorkHistory g) (oldEnded newEnded : Bool)
    (prev2 prev1 : Option (WorkSlot g)) (xs : List (Option (WorkSlot g)))
    (hprev2 : h.new2 = some prev2) (hprev1 : h.new1 = some prev1)
    (hinactive2 : InactiveOpt prev2) (hinactive1 : InactiveOpt prev1)
    (hxsInactive : ∀ x ∈ xs, InactiveOpt x)
    (holdPad : PaddingStream g oldEnded (prev2 :: prev1 :: xs))
    (hnewPad : PaddingStream g newEnded (xs ++ [none, none]))
    (hloop : ∀ h old new, minus2Suffix h old new →
      WorkEdge g cert .suffixMinus2 .suffixMinus2 h old new) :
    ∃ result,
      WorkTrace g cert ⟨.suffixMinus2, h, oldEnded, newEnded⟩
        (minus2ShiftRows g prev2 prev1 xs) result ∧
      result.phase = .suffixMinus2 ∧ lastTwoNewNone result.history := by
  cases xs with
  | nil =>
      have holdCons : PaddingStream g oldEnded [prev2, prev1] := holdPad
      have hnewCons : PaddingStream g newEnded [none, none] := by simpa using hnewPad
      let q := advanceWorkState ⟨.suffixMinus2, h, oldEnded, newEnded⟩ prev2 none .suffixMinus2
      let result := advanceWorkState q prev1 none .suffixMinus2
      refine ⟨result, ?_, rfl, ?_⟩
      · apply WorkTrace.cons
        · refine ⟨by simp, by simp, holdCons.head, hnewCons.head,
            hloop h prev2 none ⟨hinactive2, by simp [InactiveOpt], hprev2⟩⟩
        · apply WorkTrace.cons
          · refine ⟨by simp [q, advanceWorkState], by simp,
              holdCons.tail.head, hnewCons.tail.head, hloop q.history prev1 none ?_⟩
            refine ⟨hinactive1, by simp [InactiveOpt], ?_⟩
            simp [q, advanceWorkState, updateHistory, hprev1]
          · exact .nil _
      · simp [result, q, advanceWorkState, lastTwoNewNone, updateHistory]
  | cons x xs =>
      have holdCons : PaddingStream g oldEnded (prev2 :: prev1 :: x :: xs) := holdPad
      have hnewCons : PaddingStream g newEnded (x :: (xs ++ [none, none])) := by
        simpa using hnewPad
      have hx : InactiveOpt x := hxsInactive x (by simp)
      let q := advanceWorkState ⟨.suffixMinus2, h, oldEnded, newEnded⟩ prev2 x .suffixMinus2
      have hq2 : q.history.new2 = some prev1 := by simp [q, advanceWorkState, updateHistory, hprev1]
      have hq1 : q.history.new1 = some x := by simp [q, advanceWorkState, updateHistory]
      rcases trace_minus2_shift g cert q.history q.oldEnded q.newEnded prev1 x xs
          hq2 hq1 hinactive1 hx (by intro y hy; exact hxsInactive y (by simp [hy]))
          holdCons.tail hnewCons.tail hloop with ⟨result, hshift, hphase, hlast⟩
      refine ⟨result, .cons ?_ hshift, hphase, hlast⟩
      exact ⟨by simp, by simp, holdCons.head, hnewCons.head,
        hloop h prev2 x ⟨hinactive2, hx, hprev2⟩⟩
termination_by xs.length

public def minus2FromRows (g : IndexedGrammar T) : List (Option (WorkSlot g)) →
    List (Option (WorkSlot g) × Option (WorkSlot g) × WorkPhase)
  | [] =>
      [(inactive WorkSym.dollar, none, .stage2),
        (active WorkSym.close, none, .suffixMinus2)]
  | [x] =>
      [(inactive WorkSym.dollar, x, .stage2),
        (active WorkSym.close, none, .suffixMinus2),
        (x, none, .suffixMinus2)]
  | x :: y :: xs =>
      (inactive WorkSym.dollar, x, .stage2) ::
        (active WorkSym.close, y, .suffixMinus2) :: minus2ShiftRows g x y xs

@[simp] public theorem minus2FromRows_old (g : IndexedGrammar T)
    (xs : List (Option (WorkSlot g))) :
    (minus2FromRows g xs).map (fun r => r.1) =
      inactive WorkSym.dollar :: active WorkSym.close :: xs := by
  cases xs with
  | nil => rfl
  | cons x xs => cases xs <;> simp [minus2FromRows]

@[simp] public theorem minus2FromRows_new (g : IndexedGrammar T)
    (xs : List (Option (WorkSlot g))) :
    (minus2FromRows g xs).map (fun r => r.2.1) = xs ++ [none, none] := by
  cases xs with
  | nil => rfl
  | cons x xs => cases xs <;> simp [minus2FromRows]

private theorem trace_minus2_from_return (g : IndexedGrammar T) [Fintype g.nt]
    (cert : CompositeCert g) (h : WorkHistory g) (xs : List (Option (WorkSlot g)))
    (hxsInactive : ∀ x ∈ xs, InactiveOpt x)
    (holdPad : PaddingStream g false
      (inactive WorkSym.dollar :: active WorkSym.close :: xs))
    (hnewPad : PaddingStream g false (xs ++ [none, none]))
    (hdollar : ∀ h, WorkEdge g cert .returnBeta .stage2 h
      (inactive WorkSym.dollar) (firstPad xs))
    (hclose : ∀ h, WorkEdge g cert .stage2 .suffixMinus2 h
      (active WorkSym.close) (firstPad (xs.drop 1)))
    (hloop : ∀ h old new, minus2Suffix h old new →
      WorkEdge g cert .suffixMinus2 .suffixMinus2 h old new) :
    ∃ result,
      WorkTrace g cert ⟨.returnBeta, h, false, false⟩
        (minus2FromRows g xs) result ∧
      result.phase = .suffixMinus2 ∧ lastTwoNewNone result.history := by
  cases xs with
  | nil =>
      have holdCons : PaddingStream g false
          [inactive WorkSym.dollar, active WorkSym.close] := holdPad
      have hnewCons : PaddingStream g false [none, none] := by simpa using hnewPad
      let q := advanceWorkState ⟨.returnBeta, h, false, false⟩
        (inactive WorkSym.dollar) none .stage2
      let result := advanceWorkState q (active WorkSym.close) none .suffixMinus2
      refine ⟨result, ?_, rfl, ?_⟩
      · apply WorkTrace.cons
        · exact ⟨by simp, by simp, holdCons.head, hnewCons.head, hdollar h⟩
        · apply WorkTrace.cons
          · exact ⟨by simp [q, advanceWorkState], by simp,
              holdCons.tail.head, hnewCons.tail.head, hclose q.history⟩
          · exact .nil _
      · simp [result, q, advanceWorkState, lastTwoNewNone, updateHistory]
  | cons x xs =>
      cases xs with
      | nil =>
          have holdCons : PaddingStream g false
              [inactive WorkSym.dollar, active WorkSym.close, x] := holdPad
          have hnewCons : PaddingStream g false [x, none, none] := by simpa using hnewPad
          have hx : InactiveOpt x := hxsInactive x (by simp)
          let q₁ := advanceWorkState ⟨.returnBeta, h, false, false⟩
            (inactive WorkSym.dollar) x .stage2
          let q₂ := advanceWorkState q₁ (active WorkSym.close) none .suffixMinus2
          let result := advanceWorkState q₂ x none .suffixMinus2
          refine ⟨result, ?_, rfl, ?_⟩
          · apply WorkTrace.cons
            · exact ⟨by simp, by simp, holdCons.head, hnewCons.head, hdollar h⟩
            · apply WorkTrace.cons
              · exact ⟨by simp [q₁, advanceWorkState], by simp,
                  holdCons.tail.head, hnewCons.tail.head, hclose q₁.history⟩
              · apply WorkTrace.cons
                · refine ⟨by simp [q₂, q₁, advanceWorkState], by simp,
                      holdCons.tail.tail.head, hnewCons.tail.tail.head,
                      hloop q₂.history x none ?_⟩
                  refine ⟨hx, by simp [InactiveOpt], ?_⟩
                  simp [q₂, q₁, advanceWorkState, updateHistory]
                · exact .nil _
          · simp [result, q₂, q₁, advanceWorkState, lastTwoNewNone, updateHistory]
      | cons y ys =>
          have holdCons : PaddingStream g false
              (inactive WorkSym.dollar :: active WorkSym.close :: x :: y :: ys) := holdPad
          have hnewCons : PaddingStream g false (x :: y :: (ys ++ [none, none])) := by
            simpa using hnewPad
          have hx : InactiveOpt x := hxsInactive x (by simp)
          have hy : InactiveOpt y := hxsInactive y (by simp)
          let q₁ := advanceWorkState ⟨.returnBeta, h, false, false⟩
            (inactive WorkSym.dollar) x .stage2
          let q₂ := advanceWorkState q₁ (active WorkSym.close) y .suffixMinus2
          have hq2 : q₂.history.new2 = some x := by
            simp [q₂, q₁, advanceWorkState, updateHistory]
          have hq1 : q₂.history.new1 = some y := by
            simp [q₂, q₁, advanceWorkState, updateHistory]
          rcases trace_minus2_shift g cert q₂.history q₂.oldEnded q₂.newEnded
              x y ys hq2 hq1 hx hy
              (by intro z hz; exact hxsInactive z (by simp [hz]))
              holdCons.tail.tail hnewCons.tail.tail hloop with
            ⟨result, hshift, hphase, hlast⟩
          refine ⟨result, ?_, hphase, hlast⟩
          apply WorkTrace.cons
          · exact ⟨by simp, by simp, holdCons.head, hnewCons.head, hdollar h⟩
          · apply WorkTrace.cons
            · exact ⟨by simp [q₁, advanceWorkState], by simp,
                holdCons.tail.head, hnewCons.tail.head, hclose q₁.history⟩
            · simpa [q₂, q₁, advanceWorkState] using hshift

public def returnBetaRows (g : IndexedGrammar T) (xs : List (WorkSym g)) :
    List (Option (WorkSlot g) × Option (WorkSlot g) × WorkPhase) :=
  xs.map fun z => (inactive z, inactive z, .returnBeta)

@[simp] public theorem returnBetaRows_old (g : IndexedGrammar T) (xs : List (WorkSym g)) :
    (returnBetaRows g xs).map (fun r => r.1) = xs.map inactive := by
  simp [returnBetaRows]

@[simp] public theorem returnBetaRows_new (g : IndexedGrammar T) (xs : List (WorkSym g)) :
    (returnBetaRows g xs).map (fun r => r.2.1) = xs.map inactive := by
  simp [returnBetaRows]

private theorem trace_return_beta (g : IndexedGrammar T) [Fintype g.nt]
    (cert : CompositeCert g) (h : WorkHistory g) (beta : List (WorkSym g))
    (hfree : DollarFree beta)
    (hloop : ∀ h z, z ≠ WorkSym.dollar →
      WorkEdge g cert .returnBeta .returnBeta h (inactive z) (inactive z)) :
    ∃ h', WorkTrace g cert ⟨.returnBeta, h, false, false⟩
      (returnBetaRows g beta) ⟨.returnBeta, h', false, false⟩ := by
  induction beta generalizing h with
  | nil => exact ⟨h, .nil _⟩
  | cons z beta ih =>
      have hz : z ≠ WorkSym.dollar := by
        intro hz
        subst z
        exact hfree (by simp)
      have htail : DollarFree beta := by
        intro hmem
        exact hfree (by simp [hmem])
      let h₁ := updateHistory h (inactive z) (inactive z)
      rcases ih h₁ htail with ⟨h', htrace⟩
      refine ⟨h', .cons ?_ htrace⟩
      exact ⟨by simp, by simp, by simp [paddingOK], by simp [paddingOK], hloop h z hz⟩

public theorem accepts_returnFrame (g : IndexedGrammar T) [Fintype g.nt]
    {alpha beta gamma : List (WorkSym g)} {Z : WorkSym g} (k : ℕ)
    (hZ : Z ≠ WorkSym.dollar) (hfree : DollarFree beta) :
    WorkTraceAccepts g .returnFrame
      (((alpha ++ [WorkSym.dollar, Z] ++ beta ++ [WorkSym.dollar]).map inactive) ++
        [active WorkSym.close] ++ gamma.map inactive ++ List.replicate k none)
      (((alpha ++ [WorkSym.dollar]).map inactive) ++ [active Z] ++
        (beta ++ gamma).map inactive ++ List.replicate (k + 2) none) := by
  rcases trace_plain_boundary g .returnFrame alpha trivial rfl with
    ⟨prefixRows, h, hprefix, hold, hnew⟩
  let focusRow := (inactive Z, active Z, WorkPhase.returnBeta)
  let h₁ := updateHistory h focusRow.1 focusRow.2.1
  rcases trace_return_beta g .returnFrame h₁ beta hfree
      (fun h z hz => by
        simp [WorkEdge, prefixEdge, sameSuffix]
        constructor
        · simp [InactiveOpt, inactive]
        · intro heq
          apply hz
          simpa [inactive] using heq) with ⟨h₂, hbeta⟩
  let xs : List (Option (WorkSlot g)) := gamma.map inactive ++ List.replicate k none
  have hxsPad := paddingStream_inactive_append_none g gamma k
  have holdTail : PaddingStream g false
      (inactive WorkSym.dollar :: active WorkSym.close :: xs) := by
    apply PaddingStream.cons
    · simp [paddingOK]
    · apply PaddingStream.cons
      · simp [paddingOK, inactive]
      · simpa [active, xs] using hxsPad
  have hnewTail : PaddingStream g false (xs ++ [none, none]) := by
    simpa [xs, List.append_assoc] using hxsPad.append_none.append_none
  have hxsInactive : ∀ x ∈ xs, InactiveOpt x := by
    intro x hx
    simp only [xs, List.mem_append, List.mem_map, List.mem_replicate] at hx
    rcases hx with ⟨z, _, rfl⟩ | ⟨_, rfl⟩ <;> simp [InactiveOpt, inactive]
  have hfirstInactive : InactiveOpt (firstPad xs) :=
    firstPad_inactive_of_all g hxsInactive
  have hsecondInactive : InactiveOpt (firstPad (xs.drop 1)) :=
    firstPad_inactive_of_all g (fun x hx => hxsInactive x (List.mem_of_mem_drop hx))
  rcases trace_minus2_from_return g .returnFrame h₂ xs hxsInactive holdTail hnewTail
      (fun h => by simp [WorkEdge, prefixEdge, hfirstInactive])
      (fun h => by simpa [WorkEdge, prefixEdge, List.drop_one] using hsecondInactive)
      (fun h old new hs => by simp [WorkEdge, hs]) with
    ⟨result, htail, hphase, hlast⟩
  refine ⟨prefixRows ++ focusRow :: returnBetaRows g beta ++ minus2FromRows g xs,
    result, ?_, ?_, ?_, ?_⟩
  · have hmid : WorkTrace g .returnFrame ⟨.stage1, h, false, false⟩
        (focusRow :: (returnBetaRows g beta ++ minus2FromRows g xs)) result := by
      apply WorkTrace.cons
      · refine ⟨by simp, by simp [focusRow], by simp [paddingOK], by simp [paddingOK], ?_⟩
        simpa [WorkEdge, prefixEdge, focusRow] using
          (show ∃ z, z ≠ WorkSym.dollar ∧ inactive Z = inactive z ∧ active Z = active z from
            ⟨Z, hZ, rfl, rfl⟩)
      · exact WorkTrace.append g .returnFrame
          (by simpa [advanceWorkState, focusRow, h₁] using hbeta) htail
    simpa [List.append_assoc] using WorkTrace.append g .returnFrame hprefix hmid
  · simp [focusRow, xs, hold, List.map_append, List.append_assoc]
  · simp [focusRow, xs, hnew, List.map_append, List.append_assoc]
    rw [List.replicate_add]
    simp [List.append_assoc]
  · unfold workScanDone
    rw [hphase]
    simpa [lastTwoNewNone] using hlast

public theorem accepts_padded_plainBinary_of_step (g : IndexedGrammar T) [Fintype g.nt]
    (input : List T) {A B C : g.nt} {c c' : Config g} (n : ℕ)
    (hstep : CertStep g input (.plainBinary A B C) c c')
    (hold : c.work.word.length ≤ n * workWidth)
    (hnew : c'.work.word.length ≤ n * workWidth) :
    WorkTraceAccepts g (.plainBinary A B C)
      (paddedWork n c.work.slots) (paddedWork n c'.work.slots) := by
  rcases hstep with ⟨hrule, alpha, beta, hc, hc'⟩
  rw [hc] at hold ⊢
  rw [hc'] at hnew ⊢
  rw [paddedCursor_eq_append g n _ hold, paddedCursor_eq_append g n _ hnew]
  let k := n * workWidth -
    (⟨markProductivePrefix alpha ++ [WorkSym.dollar], WorkSym.plain B,
      WorkSym.plain C :: beta⟩ : WorkCursor g).word.length
  have hpad : n * workWidth -
      (⟨alpha ++ [WorkSym.dollar], WorkSym.plain A, beta⟩ : WorkCursor g).word.length =
      k + 1 := by
    simp [k, WorkCursor.word] at hold hnew ⊢
    omega
  rw [hpad]
  simpa [k, WorkCursor.word, List.map_append, List.append_assoc] using
    (accepts_plainBinary g (alpha := alpha) (beta := beta) k hrule)

public theorem accepts_padded_plainTerminal_of_step (g : IndexedGrammar T) [Fintype g.nt]
    (input : List T) {A : g.nt} {a : T} {c c' : Config g} (n : ℕ)
    (hstep : CertStep g input (.plainTerminal A a) c c')
    (hold : c.work.word.length ≤ n * workWidth)
    (hnew : c'.work.word.length ≤ n * workWidth) :
    WorkTraceAccepts g (.plainTerminal A a)
      (paddedWork n c.work.slots) (paddedWork n c'.work.slots) := by
  rcases hstep with ⟨hrule, alpha, beta, hc, hc'⟩
  rw [hc] at hold ⊢
  rw [hc'] at hnew ⊢
  rw [paddedCursor_eq_append g n _ hold, paddedCursor_eq_append g n _ hnew]
  let k := n * workWidth -
    (⟨alpha ++ [WorkSym.dollar], WorkSym.plain A, beta⟩ : WorkCursor g).word.length
  have hpad : n * workWidth -
      (⟨markProductivePrefix alpha ++ [WorkSym.dollar], WorkSym.terminal a,
        beta⟩ : WorkCursor g).word.length = k := by
    simp [k, WorkCursor.word]
  rw [hpad]
  simpa [k, WorkCursor.word, List.map_append, List.append_assoc] using
    (accepts_plainTerminal g (alpha := alpha) (beta := beta) k hrule)

public theorem accepts_padded_plainPushSkip_of_step (g : IndexedGrammar T) [Fintype g.nt]
    (input : List T) {A B : g.nt} {f : g.flag} {c c' : Config g} (n : ℕ)
    (hstep : CertStep g input (.plainPushSkip A B f) c c')
    (hold : c.work.word.length ≤ n * workWidth)
    (hnew : c'.work.word.length ≤ n * workWidth) :
    WorkTraceAccepts g (.plainPushSkip A B f)
      (paddedWork n c.work.slots) (paddedWork n c'.work.slots) := by
  rcases hstep with ⟨hrule, alpha, beta, hc, hc'⟩
  rw [hc] at hold ⊢
  rw [hc'] at hnew ⊢
  rw [paddedCursor_eq_append g n _ hold, paddedCursor_eq_append g n _ hnew]
  let k := n * workWidth -
    (⟨alpha ++ [WorkSym.dollar], WorkSym.plain A, beta⟩ : WorkCursor g).word.length
  have hpad : n * workWidth -
      (⟨alpha ++ [WorkSym.dollar], WorkSym.plain B, beta⟩ : WorkCursor g).word.length =
      k := by simp [k, WorkCursor.word]
  rw [hpad]
  simpa [k, WorkCursor.word, List.map_append, List.append_assoc] using
    (accepts_plainPushSkip g (alpha := alpha) (beta := beta) k hrule)

public theorem accepts_padded_livePushCompress_of_step
    (g : IndexedGrammar T) [Fintype g.nt] (input : List T)
    {A B : g.nt} {f : g.flag} {R : CFlag g} {d : IndexMark}
    {c c' : Config g} (n : ℕ)
    (hstep : CertStep g input (.livePushCompress A B f R d) c c')
    (hold : c.work.word.length ≤ n * workWidth)
    (hnew : c'.work.word.length ≤ n * workWidth) :
    WorkTraceAccepts g (.livePushCompress A B f R d)
      (paddedWork n c.work.slots) (paddedWork n c'.work.slots) := by
  rcases hstep with ⟨hrule, hcomp, alpha, beta, hc, hc'⟩
  rw [hc] at hold ⊢
  rw [hc'] at hnew ⊢
  rw [paddedCursor_eq_append g n _ hold, paddedCursor_eq_append g n _ hnew]
  let k := n * workWidth -
    (⟨alpha ++ [WorkSym.dollar], WorkSym.live A,
      WorkSym.index R d :: beta⟩ : WorkCursor g).word.length
  have hpad : n * workWidth -
      (⟨alpha ++ [WorkSym.dollar], WorkSym.live B,
        WorkSym.index (cflagComp g (cflagBase g f) R) d :: beta⟩ :
        WorkCursor g).word.length = k := by
    simp [k, WorkCursor.word]
  rw [hpad]
  simpa [k, WorkCursor.word, List.map_append, List.append_assoc] using
    (accepts_livePushCompress g (alpha := alpha) (beta := beta) k hrule hcomp)

public theorem accepts_padded_plainPushUse_of_step (g : IndexedGrammar T) [Fintype g.nt]
    (input : List T) {A B : g.nt} {f : g.flag} {c c' : Config g} (n : ℕ)
    (hstep : CertStep g input (.plainPushUse A B f) c c')
    (hold : c.work.word.length ≤ n * workWidth)
    (hnew : c'.work.word.length ≤ n * workWidth) :
    WorkTraceAccepts g (.plainPushUse A B f)
      (paddedWork n c.work.slots) (paddedWork n c'.work.slots) := by
  rcases hstep with ⟨hrule, alpha, beta, hc, hc'⟩
  rw [hc] at hold ⊢
  rw [hc'] at hnew ⊢
  rw [paddedCursor_eq_append g n _ hold, paddedCursor_eq_append g n _ hnew]
  let k := n * workWidth -
    (⟨alpha ++ [WorkSym.dollar], WorkSym.live B,
      WorkSym.index (cflagBase g f) .firstPending :: beta⟩ : WorkCursor g).word.length
  have hpad : n * workWidth -
      (⟨alpha ++ [WorkSym.dollar], WorkSym.plain A, beta⟩ : WorkCursor g).word.length =
      k + 1 := by
    simp [k, WorkCursor.word] at hold hnew ⊢
    omega
  rw [hpad]
  simpa [k, WorkCursor.word, List.map_append, List.append_assoc] using
    (accepts_plainPushUse g (alpha := alpha) (beta := beta) k hrule)

public theorem accepts_padded_liveBinaryBoth_of_step (g : IndexedGrammar T) [Fintype g.nt]
    (input : List T) {A B C : g.nt} {c c' : Config g} (n : ℕ)
    (hstep : CertStep g input (.liveBinaryBoth A B C) c c')
    (hold : c.work.word.length ≤ n * workWidth)
    (hnew : c'.work.word.length ≤ n * workWidth) :
    WorkTraceAccepts g (.liveBinaryBoth A B C)
      (paddedWork n c.work.slots) (paddedWork n c'.work.slots) := by
  rcases hstep with ⟨hrule, alpha, Z, beta, hc, hc'⟩
  rw [hc] at hold ⊢
  rw [hc'] at hnew ⊢
  rw [paddedCursor_eq_append g n _ hold, paddedCursor_eq_append g n _ hnew]
  let k := n * workWidth -
    (⟨markProductivePrefix alpha ++ [WorkSym.dollar], WorkSym.live B,
      WorkSym.live C :: Z :: beta⟩ : WorkCursor g).word.length
  have hpad : n * workWidth -
      (⟨alpha ++ [WorkSym.dollar], WorkSym.live A, Z :: beta⟩ : WorkCursor g).word.length =
      k + 1 := by
    simp [k, WorkCursor.word] at hold hnew ⊢
    omega
  rw [hpad]
  simpa [k, WorkCursor.word, List.map_append, List.append_assoc] using
    (accepts_liveBinaryBoth g (alpha := alpha) (beta := beta) (Z := Z) k hrule)

public theorem accepts_padded_liveBinaryLeft_of_step (g : IndexedGrammar T) [Fintype g.nt]
    (input : List T) {A B C : g.nt} {c c' : Config g} (n : ℕ)
    (hstep : CertStep g input (.liveBinaryLeft A B C) c c')
    (hold : c.work.word.length ≤ n * workWidth)
    (hnew : c'.work.word.length ≤ n * workWidth) :
    WorkTraceAccepts g (.liveBinaryLeft A B C)
      (paddedWork n c.work.slots) (paddedWork n c'.work.slots) := by
  rcases hstep with ⟨hrule, alpha, Z, beta, hc, hc'⟩
  rw [hc] at hold ⊢
  rw [hc'] at hnew ⊢
  rw [paddedCursor_eq_append g n _ hold, paddedCursor_eq_append g n _ hnew]
  let k := n * workWidth -
    (⟨markProductivePrefix alpha ++ [WorkSym.dollar], WorkSym.live B,
      WorkSym.plain C :: Z :: beta⟩ : WorkCursor g).word.length
  have hpad : n * workWidth -
      (⟨alpha ++ [WorkSym.dollar], WorkSym.live A, Z :: beta⟩ : WorkCursor g).word.length =
      k + 1 := by
    simp [k, WorkCursor.word] at hold hnew ⊢
    omega
  rw [hpad]
  simpa [k, WorkCursor.word, List.map_append, List.append_assoc] using
    (accepts_liveBinaryLeft g (alpha := alpha) (beta := beta) (Z := Z) k hrule)

public theorem accepts_padded_liveBinaryRight_of_step (g : IndexedGrammar T) [Fintype g.nt]
    (input : List T) {A B C : g.nt} {c c' : Config g} (n : ℕ)
    (hstep : CertStep g input (.liveBinaryRight A B C) c c')
    (hold : c.work.word.length ≤ n * workWidth)
    (hnew : c'.work.word.length ≤ n * workWidth) :
    WorkTraceAccepts g (.liveBinaryRight A B C)
      (paddedWork n c.work.slots) (paddedWork n c'.work.slots) := by
  rcases hstep with ⟨hrule, alpha, Z, beta, hc, hc'⟩
  rw [hc] at hold ⊢
  rw [hc'] at hnew ⊢
  rw [paddedCursor_eq_append g n _ hold, paddedCursor_eq_append g n _ hnew]
  let k := n * workWidth -
    (⟨markProductivePrefix alpha ++ [WorkSym.dollar], WorkSym.plain B,
      WorkSym.live C :: Z :: beta⟩ : WorkCursor g).word.length
  have hpad : n * workWidth -
      (⟨alpha ++ [WorkSym.dollar], WorkSym.live A, Z :: beta⟩ : WorkCursor g).word.length =
      k + 1 := by
    simp [k, WorkCursor.word] at hold hnew ⊢
    omega
  rw [hpad]
  simpa [k, WorkCursor.word, List.map_append, List.append_assoc] using
    (accepts_liveBinaryRight g (alpha := alpha) (beta := beta) (Z := Z) k hrule)

public theorem accepts_padded_livePushFresh_of_step (g : IndexedGrammar T) [Fintype g.nt]
    (input : List T) {A B : g.nt} {f : g.flag} {c c' : Config g} (n : ℕ)
    (hstep : CertStep g input (.livePushFresh A B f) c c')
    (hold : c.work.word.length ≤ n * workWidth)
    (hnew : c'.work.word.length ≤ n * workWidth) :
    WorkTraceAccepts g (.livePushFresh A B f)
      (paddedWork n c.work.slots) (paddedWork n c'.work.slots) := by
  rcases hstep with ⟨hrule, alpha, Z, beta, hc, hc'⟩
  rw [hc] at hold ⊢
  rw [hc'] at hnew ⊢
  rw [paddedCursor_eq_append g n _ hold, paddedCursor_eq_append g n _ hnew]
  let k := n * workWidth -
    (⟨alpha ++ [WorkSym.dollar], WorkSym.live B,
      WorkSym.index (cflagBase g f) .laterPending :: Z :: beta⟩ : WorkCursor g).word.length
  have hpad : n * workWidth -
      (⟨alpha ++ [WorkSym.dollar], WorkSym.live A, Z :: beta⟩ : WorkCursor g).word.length =
      k + 1 := by
    simp [k, WorkCursor.word] at hold hnew ⊢
    omega
  rw [hpad]
  simpa [k, WorkCursor.word, List.map_append, List.append_assoc] using
    (accepts_livePushFresh g (alpha := alpha) (beta := beta) (Z := Z) k hrule)

public theorem accepts_padded_popPlain_of_step (g : IndexedGrammar T) [Fintype g.nt]
    (input : List T) {R : CFlag g} {d : IndexMark} {A B : g.nt}
    {c c' : Config g} (n : ℕ)
    (hstep : CertStep g input (.popPlain R d A B) c c')
    (hold : c.work.word.length ≤ n * workWidth)
    (hnew : c'.work.word.length ≤ n * workWidth) :
    WorkTraceAccepts g (.popPlain R d A B)
      (paddedWork n c.work.slots) (paddedWork n c'.work.slots) := by
  rcases hstep with ⟨hrule, hshape⟩
  rcases hshape with hframed | herase
  · rcases hframed with ⟨alpha, beta, gamma, hfree, hc, hc'⟩
    rw [hc] at hold ⊢
    rw [hc'] at hnew ⊢
    rw [paddedCursor_eq_append g n _ hold, paddedCursor_eq_append g n _ hnew]
    let k := n * workWidth -
      (⟨alpha ++ [WorkSym.dollar] ++ beta ++
          [WorkSym.index R d.markUsed, WorkSym.dollar], WorkSym.plain B,
        WorkSym.close :: gamma⟩ : WorkCursor g).word.length
    have hpad : n * workWidth -
        (⟨alpha ++ [WorkSym.dollar], WorkSym.live A,
          beta ++ WorkSym.index R d :: gamma⟩ : WorkCursor g).word.length = k + 2 := by
      simp [k, WorkCursor.word] at hold hnew ⊢
      omega
    rw [hpad]
    simpa [k, WorkCursor.word, List.map_append, List.append_assoc] using
      (accepts_popPlain g (alpha := alpha) (beta := beta) (gamma := gamma)
        k hrule hfree)
  · rcases herase with ⟨alpha, gamma, hc, hc'⟩
    rw [hc] at hold ⊢
    rw [hc'] at hnew ⊢
    rw [paddedCursor_eq_append g n _ hold, paddedCursor_eq_append g n _ hnew]
    let k := n * workWidth -
      (⟨alpha ++ [WorkSym.dollar], WorkSym.live A,
        WorkSym.index R d :: gamma⟩ : WorkCursor g).word.length
    have hpad : n * workWidth -
        (⟨alpha ++ [WorkSym.dollar], WorkSym.plain B, gamma⟩ : WorkCursor g).word.length =
          k + 1 := by
      simp [k, WorkCursor.word] at hold hnew ⊢
      omega
    rw [hpad]
    simpa [k, WorkCursor.word, List.map_append, List.append_assoc] using
      (accepts_popPlainErase g (alpha := alpha) (gamma := gamma) k hrule)

public theorem accepts_padded_popLive_of_step (g : IndexedGrammar T) [Fintype g.nt]
    (input : List T) {R : CFlag g} {d : IndexMark} {A B : g.nt}
    {c c' : Config g} (n : ℕ)
    (hstep : CertStep g input (.popLive R d A B) c c')
    (hold : c.work.word.length ≤ n * workWidth)
    (hnew : c'.work.word.length ≤ n * workWidth) :
    WorkTraceAccepts g (.popLive R d A B)
      (paddedWork n c.work.slots) (paddedWork n c'.work.slots) := by
  rcases hstep with ⟨hrule, hlater, hshape⟩
  rcases hshape with hframed | herase
  · rcases hframed with ⟨alpha, beta, gamma, hfree, hc, hc'⟩
    rw [hc] at hold ⊢
    rw [hc'] at hnew ⊢
    rw [paddedCursor_eq_append g n _ hold, paddedCursor_eq_append g n _ hnew]
    let k := n * workWidth -
      (⟨alpha ++ [WorkSym.dollar] ++ beta ++
          [WorkSym.index R d.markUsed, WorkSym.dollar], WorkSym.live B,
        WorkSym.close :: gamma⟩ : WorkCursor g).word.length
    have hpad : n * workWidth -
        (⟨alpha ++ [WorkSym.dollar], WorkSym.live A,
          beta ++ WorkSym.index R d :: gamma⟩ : WorkCursor g).word.length = k + 2 := by
      simp [k, WorkCursor.word] at hold hnew ⊢
      omega
    rw [hpad]
    simpa [k, WorkCursor.word, List.map_append, List.append_assoc] using
      (accepts_popLive g (alpha := alpha) (beta := beta) (gamma := gamma)
        k hrule hlater hfree)
  · rcases herase with ⟨alpha, gamma, hc, hc'⟩
    rw [hc] at hold ⊢
    rw [hc'] at hnew ⊢
    rw [paddedCursor_eq_append g n _ hold, paddedCursor_eq_append g n _ hnew]
    let k := n * workWidth -
      (⟨alpha ++ [WorkSym.dollar], WorkSym.live A,
        WorkSym.index R d :: gamma⟩ : WorkCursor g).word.length
    have hpad : n * workWidth -
        (⟨alpha ++ [WorkSym.dollar], WorkSym.live B, gamma⟩ : WorkCursor g).word.length =
          k + 1 := by
      simp [k, WorkCursor.word] at hold hnew ⊢
      omega
    rw [hpad]
    simpa [k, WorkCursor.word, List.map_append, List.append_assoc] using
      (accepts_popLiveErase g (alpha := alpha) (gamma := gamma) k hrule hlater)

public theorem accepts_padded_matchTerminal_of_step (g : IndexedGrammar T) [Fintype g.nt]
    (input : List T) {a : T} {c c' : Config g} (n : ℕ)
    (hstep : CertStep g input (.matchTerminal a) c c')
    (hold : c.work.word.length ≤ n * workWidth)
    (hnew : c'.work.word.length ≤ n * workWidth) :
    WorkTraceAccepts g (.matchTerminal a)
      (paddedWork n c.work.slots) (paddedWork n c'.work.slots) := by
  rcases hstep with ⟨_, alpha, Z, beta, hc, hc'⟩
  rw [hc] at hold ⊢
  rw [hc'] at hnew ⊢
  rw [paddedCursor_eq_append g n _ hold, paddedCursor_eq_append g n _ hnew]
  let k := n * workWidth -
    (⟨alpha ++ [WorkSym.dollar], WorkSym.terminal a,
      Z :: beta⟩ : WorkCursor g).word.length
  have hpad : n * workWidth -
      (⟨alpha ++ [WorkSym.dollar], Z, beta⟩ : WorkCursor g).word.length = k + 1 := by
    simp [k, WorkCursor.word] at hold hnew ⊢
    omega
  rw [hpad]
  simpa [k, WorkCursor.word, List.map_append, List.append_assoc] using
    (accepts_matchTerminal g (alpha := alpha) (beta := beta) (Z := Z) k)

public theorem accepts_padded_eraseIndex_of_step (g : IndexedGrammar T) [Fintype g.nt]
    (input : List T) {R : CFlag g} {d : IndexMark} {c c' : Config g} (n : ℕ)
    (hstep : CertStep g input (.eraseIndex R d) c c')
    (hold : c.work.word.length ≤ n * workWidth)
    (hnew : c'.work.word.length ≤ n * workWidth) :
    WorkTraceAccepts g (.eraseIndex R d)
      (paddedWork n c.work.slots) (paddedWork n c'.work.slots) := by
  rcases hstep with ⟨herase, alpha, Z, beta, hc, hc'⟩
  rw [hc] at hold ⊢
  rw [hc'] at hnew ⊢
  rw [paddedCursor_eq_append g n _ hold, paddedCursor_eq_append g n _ hnew]
  let k := n * workWidth -
    (⟨alpha ++ [WorkSym.dollar], WorkSym.index R d,
      Z :: beta⟩ : WorkCursor g).word.length
  have hpad : n * workWidth -
      (⟨alpha ++ [WorkSym.dollar], Z, beta⟩ : WorkCursor g).word.length = k + 1 := by
    simp [k, WorkCursor.word] at hold hnew ⊢
    omega
  rw [hpad]
  simpa [k, WorkCursor.word, List.map_append, List.append_assoc] using
    (accepts_eraseIndex g (alpha := alpha) (beta := beta) (Z := Z) k herase)

public theorem accepts_padded_returnFrame_of_step (g : IndexedGrammar T) [Fintype g.nt]
    (input : List T) {c c' : Config g} (n : ℕ)
    (hstep : CertStep g input .returnFrame c c')
    (hold : c.work.word.length ≤ n * workWidth)
    (hnew : c'.work.word.length ≤ n * workWidth) :
    WorkTraceAccepts g .returnFrame
      (paddedWork n c.work.slots) (paddedWork n c'.work.slots) := by
  rcases hstep with ⟨alpha, Z, beta, gamma, hZ, hfree, hc, hc'⟩
  rw [hc] at hold ⊢
  rw [hc'] at hnew ⊢
  rw [paddedCursor_eq_append g n _ hold, paddedCursor_eq_append g n _ hnew]
  let k := n * workWidth -
    (⟨alpha ++ [WorkSym.dollar, Z] ++ beta ++ [WorkSym.dollar],
      WorkSym.close, gamma⟩ : WorkCursor g).word.length
  have hpad : n * workWidth -
      (⟨alpha ++ [WorkSym.dollar], Z, beta ++ gamma⟩ : WorkCursor g).word.length =
      k + 2 := by
    simp [k, WorkCursor.word] at hold hnew ⊢
    omega
  rw [hpad]
  simpa [k, WorkCursor.word, List.map_append, List.append_assoc] using
    (accepts_returnFrame g (alpha := alpha) (beta := beta) (gamma := gamma)
      (Z := Z) k hZ hfree)

/-- Every bounded machine certificate has an accepting synchronized logical-slot trace. -/
public theorem workTraceAccepts_of_certStep (g : IndexedGrammar T) [Fintype g.nt]
    (input : List T) (cert : CompositeCert g) {c c' : Config g} (n : ℕ)
    (hstep : CertStep g input cert c c')
    (hold : c.work.word.length ≤ n * workWidth)
    (hnew : c'.work.word.length ≤ n * workWidth) :
    WorkTraceAccepts g cert
      (paddedWork n c.work.slots) (paddedWork n c'.work.slots) := by
  cases cert with
  | plainBinary A B C => exact accepts_padded_plainBinary_of_step g input n hstep hold hnew
  | plainTerminal A a => exact accepts_padded_plainTerminal_of_step g input n hstep hold hnew
  | plainPushSkip A B f => exact accepts_padded_plainPushSkip_of_step g input n hstep hold hnew
  | plainPushUse A B f => exact accepts_padded_plainPushUse_of_step g input n hstep hold hnew
  | liveBinaryBoth A B C => exact accepts_padded_liveBinaryBoth_of_step g input n hstep hold hnew
  | liveBinaryLeft A B C => exact accepts_padded_liveBinaryLeft_of_step g input n hstep hold hnew
  | liveBinaryRight A B C => exact accepts_padded_liveBinaryRight_of_step g input n hstep hold hnew
  | livePushFresh A B f => exact accepts_padded_livePushFresh_of_step g input n hstep hold hnew
  | livePushCompress A B f R d =>
      exact accepts_padded_livePushCompress_of_step g input n hstep hold hnew
  | popPlain R d A B => exact accepts_padded_popPlain_of_step g input n hstep hold hnew
  | popLive R d A B => exact accepts_padded_popLive_of_step g input n hstep hold hnew
  | matchTerminal a => exact accepts_padded_matchTerminal_of_step g input n hstep hold hnew
  | eraseIndex R d => exact accepts_padded_eraseIndex_of_step g input n hstep hold hnew
  | returnFrame => exact accepts_padded_returnFrame_of_step g input n hstep hold hnew

end Aho
end IndexedGrammar
