module

public import Langlib.Classes.ContextFree.Decidability.MalformedHistories.FiniteVerifier
public import Langlib.Classes.ContextFree.Decidability.MalformedHistories.Syntax
public import Langlib.Classes.ContextFree.Decidability.MirrorPair
public import Langlib.Classes.ContextFree.Closure.Concatenation
public import Langlib.Classes.ContextFree.Closure.Union
public import Langlib.Classes.Regular.Inclusion.ContextFree

@[expose]
public section

/-!
# Context-free realizations of failed history steps

The transition certificate is stored on the destination row.  A fixed finite
pair verifier can therefore check an adjacent row pair deterministically.  Its
rejecting mirror languages, together with the unequal-width mirror language,
recognize exactly the failed transitions in either alternating orientation.
-/

namespace ContextFree.MalformedHistories

variable {I A C Q F : Type}

/-- The finite pair verifier obtained by reading the certificate attached to
each destination cell.  `none` is an ordinary rejecting verifier state here;
the outer `Option` in `FinitePairVerifier.eval` remains reserved for a width
mismatch. -/
def bundledPairVerifier (S : CertifiedRowSystem I A C Q F) :
    FinitePairVerifier (BundledCell A C) (Option Q) where
  start := some S.stepStart
  step
    | some q, old, (new, some cert) =>
        some (S.stepCell q old.1 new cert)
    | _, _, _ => none
  done
    | some q => S.stepDone q
    | none => false

namespace bundledPairVerifier

variable (S : CertifiedRowSystem I A C Q F)

private theorem evalFrom_none_ne_some_some
    (old new : List (BundledCell A C)) (q : Q) :
    (bundledPairVerifier S).evalFrom none old new ≠ some (some q) := by
  induction old generalizing new with
  | nil => cases new <;> simp [FinitePairVerifier.evalFrom]
  | cons old oldTail ih =>
      cases new with
      | nil => simp [FinitePairVerifier.evalFrom]
      | cons new newTail =>
          simpa [FinitePairVerifier.evalFrom, bundledPairVerifier] using
            ih newTail

/-- Successful paired evaluation is exactly successful cellwise evaluation
with the certificate read from the destination row. -/
theorem evalFrom_eq_some_some_iff (start final : Q)
    (old new : List (BundledCell A C)) :
    (bundledPairVerifier S).evalFrom (some start) old new =
        some (some final) ↔
      ∃ cert, incomingCertificate new = some cert ∧
        S.evalStep start (underlyingRow old) (underlyingRow new) cert =
          some final := by
  induction old generalizing start final new with
  | nil =>
      cases new with
      | nil => simp [FinitePairVerifier.evalFrom, incomingCertificate,
          CertifiedRowSystem.evalStep, underlyingRow]
      | cons new newTail =>
          simp [FinitePairVerifier.evalFrom, incomingCertificate,
            CertifiedRowSystem.evalStep, underlyingRow]
  | cons old oldTail ih =>
      cases new with
      | nil =>
          simp [FinitePairVerifier.evalFrom, incomingCertificate,
            CertifiedRowSystem.evalStep, underlyingRow]
      | cons new newTail =>
          rcases old with ⟨oldCell, oldCert⟩
          rcases new with ⟨newCell, none | cert⟩
          · constructor
            · intro h
              exact (evalFrom_none_ne_some_some S oldTail newTail final h).elim
            · simp [incomingCertificate]
          · change
              (bundledPairVerifier S).evalFrom
                  (some (S.stepCell start oldCell newCell cert))
                  oldTail newTail = some (some final) ↔ _
            constructor
            · intro h
              obtain ⟨certs, hcerts, heval⟩ :=
                (ih (S.stepCell start oldCell newCell cert) final
                  newTail).mp h
              exact ⟨cert :: certs, by simp [hcerts], by
                simpa [underlyingRow, CertifiedRowSystem.evalStep] using heval⟩
            · rintro ⟨allCerts, hcerts, heval⟩
              cases htail : incomingCertificate newTail with
              | none => simp [htail] at hcerts
              | some certs =>
                  simp only [incomingCertificate_cons_some, htail,
                    Option.map_some, Option.some.injEq, List.cons.injEq]
                    at hcerts
                  subst allCerts
                  apply (ih (S.stepCell start oldCell newCell cert) final
                    newTail).mpr
                  exact ⟨certs, htail, by
                    simpa [underlyingRow, CertifiedRowSystem.evalStep] using heval⟩

/-- The verifier accepts an equal-width bundled pair exactly when it is a
certified row step. -/
theorem accepts_iff (old new : List (BundledCell A C)) :
    (∃ state,
      (bundledPairVerifier S).eval old new = some state ∧
        (bundledPairVerifier S).done state = true) ↔
      BundledStep S old new := by
  rw [bundledStep_iff]
  constructor
  · rintro ⟨none | q, heval, hdone⟩
    · simp [bundledPairVerifier] at hdone
    · obtain ⟨cert, hcert, hstep⟩ :=
        (evalFrom_eq_some_some_iff S S.stepStart q old new).mp heval
      exact ⟨cert, q, hcert, hstep, hdone⟩
  · rintro ⟨cert, q, hcert, hstep, hdone⟩
    exact ⟨some q,
      (evalFrom_eq_some_some_iff S S.stepStart q old new).mpr
        ⟨cert, hcert, hstep⟩,
      hdone⟩

/-- At equal width, rejection by the finite verifier is the negation of the
bundled step predicate. -/
theorem rejects_iff_of_length_eq {old new : List (BundledCell A C)}
    (hlen : old.length = new.length) :
    (∃ state,
      (bundledPairVerifier S).eval old new = some state ∧
        (bundledPairVerifier S).done state = false) ↔
      ¬ BundledStep S old new := by
  constructor
  · rintro ⟨state, heval, hdone⟩ hstep
    obtain ⟨accepted, haccepted, hdone'⟩ :=
      (accepts_iff S old new).mpr hstep
    rw [heval] at haccepted
    cases haccepted
    simp_all
  · intro hstep
    have hne : (bundledPairVerifier S).eval old new ≠ none := by
      intro heval
      have := ((bundledPairVerifier S).eval_eq_none_iff old new).mp heval
      exact this hlen
    cases heval : (bundledPairVerifier S).eval old new with
    | none => exact (hne heval).elim
    | some state =>
        refine ⟨state, rfl, ?_⟩
        cases hdone : (bundledPairVerifier S).done state with
        | false => rfl
        | true =>
            exact (hstep ((accepts_iff S old new).mp
              ⟨state, heval, hdone⟩)).elim

end bundledPairVerifier

/-! ## Failed-pair mirror cores -/

/-- Failed bundled transitions in the forward/backward mirror orientation. -/
def evenBadStepCore (S : CertifiedRowSystem I A C Q F) :
    Language (Symbol (BundledCell A C)) :=
  (bundledPairVerifier S).evenRejectLanguage +
    FinitePairVerifier.lengthMismatchLanguage (BundledCell A C)

/-- Failed bundled transitions in the backward/forward mirror orientation. -/
def oddBadStepCore (S : CertifiedRowSystem I A C Q F) :
    Language (Symbol (BundledCell A C)) :=
  (bundledPairVerifier S).oddRejectLanguage +
    FinitePairVerifier.lengthMismatchLanguage (BundledCell A C)

theorem mem_evenBadStepCore_iff
    (S : CertifiedRowSystem I A C Q F)
    (w : List (Symbol (BundledCell A C))) :
    w ∈ evenBadStepCore S ↔
      ∃ old new : List (BundledCell A C),
        ¬ BundledStep S old new ∧
          w = old.map Symbol.cell ++
            Symbol.separator :: new.reverse.map Symbol.cell := by
  rw [evenBadStepCore, Language.mem_add]
  constructor
  · rintro (hreject | hmismatch)
    · obtain ⟨old, new, state, heval, hdone, rfl⟩ := hreject
      have hlen : old.length = new.length :=
        (bundledPairVerifier S).evalFrom_eq_some_length heval
      exact ⟨old, new,
        (bundledPairVerifier.rejects_iff_of_length_eq S hlen).mp
          ⟨state, heval, hdone⟩,
        rfl⟩
    · obtain ⟨old, new, hlen, rfl⟩ := hmismatch
      exact ⟨old, new, fun hstep => hlen (bundledStep_length S hstep), rfl⟩
  · rintro ⟨old, new, hbad, rfl⟩
    by_cases hlen : old.length = new.length
    · left
      obtain ⟨state, heval, hdone⟩ :=
        (bundledPairVerifier.rejects_iff_of_length_eq S hlen).mpr hbad
      exact ⟨old, new, state, heval, hdone, rfl⟩
    · right
      exact ⟨old, new, hlen, rfl⟩

theorem mem_oddBadStepCore_iff
    (S : CertifiedRowSystem I A C Q F)
    (w : List (Symbol (BundledCell A C))) :
    w ∈ oddBadStepCore S ↔
      ∃ old new : List (BundledCell A C),
        ¬ BundledStep S old new ∧
          w = old.reverse.map Symbol.cell ++
            Symbol.separator :: new.map Symbol.cell := by
  rw [oddBadStepCore, Language.mem_add]
  constructor
  · rintro (hreject | hmismatch)
    · obtain ⟨old, new, state, heval, hdone, rfl⟩ := hreject
      have hlen : old.length = new.length :=
        (bundledPairVerifier S).evalFrom_eq_some_length heval
      exact ⟨old, new,
        (bundledPairVerifier.rejects_iff_of_length_eq S hlen).mp
          ⟨state, heval, hdone⟩,
        rfl⟩
    · obtain ⟨xs, ys, hlen, rfl⟩ := hmismatch
      refine ⟨xs.reverse, ys.reverse, ?_, ?_⟩
      · intro hstep
        have := bundledStep_length S hstep
        simp only [List.length_reverse] at this
        exact hlen this
      · simp
  · rintro ⟨old, new, hbad, rfl⟩
    by_cases hlen : old.length = new.length
    · left
      obtain ⟨state, heval, hdone⟩ :=
        (bundledPairVerifier.rejects_iff_of_length_eq S hlen).mpr hbad
      exact ⟨old, new, state, heval, hdone, rfl⟩
    · right
      refine ⟨old.reverse, new.reverse, ?_, ?_⟩
      · simpa using hlen
      · simp

section Finite

variable [Fintype A] [DecidableEq A] [Fintype C] [DecidableEq C]
  [Fintype Q] [DecidableEq Q]

theorem evenBadStepCore_is_CF
    (S : CertifiedRowSystem I A C Q F) : is_CF (evenBadStepCore S) := by
  apply CF_of_CF_u_CF
  exact ⟨(bundledPairVerifier S).evenRejectLanguage_is_CF,
    FinitePairVerifier.lengthMismatchLanguage_is_CF⟩

theorem oddBadStepCore_is_CF
    (S : CertifiedRowSystem I A C Q F) : is_CF (oddBadStepCore S) := by
  apply CF_of_CF_u_CF
  exact ⟨(bundledPairVerifier S).oddRejectLanguage_is_CF,
    FinitePairVerifier.lengthMismatchLanguage_is_CF⟩

end Finite

/-! ## Selecting a failed pair inside a history -/

theorem exists_rowsOfPairs_of_length_eq_two_mul
    (pre : List (List A)) (n : Nat)
    (hlen : pre.length = 2 * n) :
    ∃ pairs : List (List A × List A), rowsOfPairs pairs = pre := by
  induction n generalizing pre with
  | zero =>
      cases pre with
      | nil => exact ⟨[], rfl⟩
      | cons first rest => simp at hlen
  | succ n ih =>
      cases pre with
      | nil => simp at hlen
      | cons first rest =>
          cases rest with
          | nil =>
              simp only [List.length_cons, List.length_nil] at hlen
              omega
          | cons second rest =>
              have hrest : rest.length = 2 * n := by
                simp only [List.length_cons] at hlen
                omega
              obtain ⟨pairs, hpairs⟩ := ih rest hrest
              exact ⟨(first, second) :: pairs, by
                simpa [rowsOfPairs] using hpairs⟩

theorem exists_rowsOfPairs_append_singleton_of_length_eq
    (pre : List (List A)) (n : Nat)
    (hlen : pre.length = 2 * n + 1) :
    ∃ (pairs : List (List A × List A)) (last : List A),
      rowsOfPairs pairs ++ [last] = pre := by
  induction n generalizing pre with
  | zero =>
      cases pre with
      | nil => simp at hlen
      | cons last rest =>
          cases rest with
          | nil => exact ⟨[], last, rfl⟩
          | cons next rest =>
              simp only [List.length_cons, List.length_nil] at hlen
              omega
  | succ n ih =>
      cases pre with
      | nil => simp at hlen
      | cons first rest =>
          cases rest with
          | nil => simp at hlen
          | cons second rest =>
              have hrest : rest.length = 2 * n + 1 := by
                simp only [List.length_cons] at hlen
                omega
              obtain ⟨pairs, last, hpairs⟩ := ih rest hrest
              exact ⟨(first, second) :: pairs, last, by
                simpa [rowsOfPairs] using hpairs⟩

private theorem split_two_getElems (rows : List (List A)) (i : Nat)
    (hi : i + 1 < rows.length) :
    rows = rows.take i ++ rows[i] :: rows[i + 1] :: rows.drop (i + 2) := by
  have hi0 : i < rows.length := by omega
  calc
    rows = rows.take i ++ rows.drop i := (List.take_append_drop i rows).symm
    _ = rows.take i ++ rows[i] :: rows.drop (i + 1) := by
      rw [List.drop_eq_getElem_cons hi0]
    _ = rows.take i ++ rows[i] :: rows[i + 1] ::
        rows.drop ((i + 1) + 1) := by
      rw [List.drop_eq_getElem_cons hi]
    _ = rows.take i ++ rows[i] :: rows[i + 1] ::
        rows.drop (i + 2) := by
      rw [show (i + 1) + 1 = i + 2 by omega]

/-- Even-indexed bad steps are precisely those preceded by whole row pairs. -/
theorem badStepAtParity_zero_iff (Step : List A → List A → Prop)
    (h : Rows A) :
    BadStepAtParity 0 Step h ↔
      ∃ (pairs : List (List A × List A)) (old new : List A)
          (tail : List (List A)),
        h.toList = rowsOfPairs pairs ++ old :: new :: tail ∧
          ¬ Step old new := by
  constructor
  · rintro ⟨i, hi, hparity, hbad⟩
    have hi0 : i < h.toList.length := by omega
    have hprelen : (h.toList.take i).length = i := by
      simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi0)]
    obtain ⟨n, hin⟩ := even_iff_exists_two_mul.mp
      (Nat.even_iff.mpr hparity)
    obtain ⟨pairs, hpairs⟩ :=
      exists_rowsOfPairs_of_length_eq_two_mul (h.toList.take i) n
        (hprelen.trans hin)
    refine ⟨pairs, h.toList[i], h.toList[i + 1],
      h.toList.drop (i + 2), ?_, hbad⟩
    rw [hpairs]
    exact split_two_getElems h.toList i hi
  · rintro ⟨pairs, old, new, tail, hrows, hbad⟩
    let i := (rowsOfPairs pairs).length
    refine ⟨i, ?_, ?_, ?_⟩
    · rw [hrows]
      simp [i]
    · simp [i, rowsOfPairs, List.length_flatMap]
    · simpa [hrows, i] using hbad

/-- Odd-indexed bad steps are precisely those preceded by whole row pairs and
one additional row. -/
theorem badStepAtParity_one_iff (Step : List A → List A → Prop)
    (h : Rows A) :
    BadStepAtParity 1 Step h ↔
      ∃ (pairs : List (List A × List A)) (prior old new : List A)
          (tail : List (List A)),
        h.toList = rowsOfPairs pairs ++ prior :: old :: new :: tail ∧
          ¬ Step old new := by
  constructor
  · rintro ⟨i, hi, hparity, hbad⟩
    have hi0 : i < h.toList.length := by omega
    have hprelen : (h.toList.take i).length = i := by
      simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi0)]
    obtain ⟨n, hin⟩ := odd_iff_exists_bit1.mp
      (Nat.odd_iff.mpr hparity)
    obtain ⟨pairs, prior, hpairs⟩ :=
      exists_rowsOfPairs_append_singleton_of_length_eq
        (h.toList.take i) n (hprelen.trans hin)
    refine ⟨pairs, prior, h.toList[i], h.toList[i + 1],
      h.toList.drop (i + 2), ?_, hbad⟩
    have hsplit := split_two_getElems h.toList i hi
    rw [← hpairs] at hsplit
    simpa [List.append_assoc] using hsplit
  · rintro ⟨pairs, prior, old, new, tail, hrows, hbad⟩
    let i := (rowsOfPairs pairs).length + 1
    refine ⟨i, ?_, ?_, ?_⟩
    · rw [hrows]
      simp only [List.length_append, List.length_cons]
      dsimp [i]
      omega
    · simp [i, rowsOfPairs, List.length_flatMap]
    · simpa [hrows, i, Nat.add_assoc] using hbad

/-- The separator ending the selected second row, followed by arbitrary
complete row blocks. -/
def afterPairLanguage : Language (Symbol A) :=
  ({[Symbol.separator]} : Language (Symbol A)) * blocksLanguage

theorem afterPairLanguage_isRegular :
    afterPairLanguage (A := A).IsRegular :=
  (Language.isRegular_singleton_word [Symbol.separator]).mul'
    blocksLanguage_isRegular

theorem mem_afterPairLanguage_iff (even : Bool) (w : List (Symbol A)) :
    w ∈ afterPairLanguage (A := A) ↔
      ∃ tail : List (List A), w = Symbol.separator :: encodeAux even tail := by
  rw [afterPairLanguage, Language.mem_mul]
  constructor
  · rintro ⟨pre, hpre, suffix, hsuffix, rfl⟩
    change pre = [Symbol.separator] at hpre
    subst pre
    obtain ⟨tail, htail⟩ :=
      (mem_blocksLanguage_iff_exists_encodeAux even suffix).mp hsuffix
    refine ⟨tail, ?_⟩
    rw [← htail]
    rfl
  · rintro ⟨tail, rfl⟩
    exact ⟨[Symbol.separator], Set.mem_singleton _, encodeAux even tail,
      (mem_blocksLanguage_iff_exists_encodeAux even _).mpr ⟨tail, rfl⟩,
      rfl⟩

private def evenSelectedHistory (pairs : List (List A × List A))
    (old new : List A) (tail : List (List A)) : Rows A :=
  match pairs with
  | [] => (old, new :: tail)
  | (first, second) :: pairs =>
      (first, second :: rowsOfPairs pairs ++ old :: new :: tail)

@[simp] private theorem evenSelectedHistory_toList
    (pairs : List (List A × List A)) (old new : List A)
    (tail : List (List A)) :
    (evenSelectedHistory pairs old new tail).toList =
      rowsOfPairs pairs ++ old :: new :: tail := by
  cases pairs with
  | nil => rfl
  | cons pair pairs =>
      rcases pair with ⟨first, second⟩
      rfl

private def oddSelectedHistory (pairs : List (List A × List A))
    (prior old new : List A) (tail : List (List A)) : Rows A :=
  match pairs with
  | [] => (prior, old :: new :: tail)
  | (first, second) :: pairs =>
      (first, second :: rowsOfPairs pairs ++ prior :: old :: new :: tail)

@[simp] private theorem oddSelectedHistory_toList
    (pairs : List (List A × List A)) (prior old new : List A)
    (tail : List (List A)) :
    (oddSelectedHistory pairs prior old new tail).toList =
      rowsOfPairs pairs ++ prior :: old :: new :: tail := by
  cases pairs with
  | nil => rfl
  | cons pair pairs =>
      rcases pair with ⟨first, second⟩
      rfl

/-- Select an even-indexed adjacent pair and recognize its failed bundled
transition. -/
def evenBadStepRealization (S : CertifiedRowSystem I A C Q F) :
    Language (Symbol (BundledCell A C)) :=
  evenPrefixLanguage * (evenBadStepCore S * afterPairLanguage)

/-- Select an odd-indexed adjacent pair and recognize its failed bundled
transition. -/
def oddBadStepRealization (S : CertifiedRowSystem I A C Q F) :
    Language (Symbol (BundledCell A C)) :=
  oddPrefixLanguage * (oddBadStepCore S * afterPairLanguage)

private theorem encode_evenSelected_eq
    (pairs : List (List A × List A)) (old new : List A)
    (tail : List (List A)) :
    encode (rowsOfPairs pairs ++ old :: new :: tail) =
      (Symbol.separator :: encodeAux true (rowsOfPairs pairs)) ++
        ((old.map Symbol.cell ++
            Symbol.separator :: new.reverse.map Symbol.cell) ++
          (Symbol.separator :: encodeAux true tail)) := by
  simp [encode, encodeAux_rowsOfPairs_append, encodeAux, orientRow,
    List.append_assoc]

private theorem encode_oddSelected_eq
    (pairs : List (List A × List A)) (prior old new : List A)
    (tail : List (List A)) :
    encode (rowsOfPairs pairs ++ prior :: old :: new :: tail) =
      (Symbol.separator ::
          encodeAux true (rowsOfPairs pairs ++ [prior])) ++
        ((old.reverse.map Symbol.cell ++
            Symbol.separator :: new.map Symbol.cell) ++
          (Symbol.separator :: encodeAux false tail)) := by
  simp [encode, encodeAux_rowsOfPairs_append, encodeAux, orientRow,
    List.append_assoc]

theorem evenBadStepRealization_eq
    (S : CertifiedRowSystem I A C Q F) :
    evenBadStepRealization S =
      relaxedBadStepLanguage 0 (BundledStep S) := by
  ext w
  constructor
  · intro hw
    rw [evenBadStepRealization, Language.mem_mul] at hw
    obtain ⟨pre, hpre, rest, hrest, rfl⟩ := hw
    rw [Language.mem_mul] at hrest
    obtain ⟨core, hcore, suffix, hsuffix, rfl⟩ := hrest
    obtain ⟨pairs, hpre⟩ := (mem_evenPrefixLanguage_iff pre).mp hpre
    obtain ⟨old, new, hbad, hcore⟩ :=
      (mem_evenBadStepCore_iff S core).mp hcore
    obtain ⟨tail, hsuffix⟩ :=
      (mem_afterPairLanguage_iff true suffix).mp hsuffix
    subst pre
    subst core
    subst suffix
    let h := evenSelectedHistory pairs old new tail
    refine ⟨h, ?_, ?_⟩
    · simpa [RawRepresents, h] using
        encode_evenSelected_eq pairs old new tail
    · apply (badStepAtParity_zero_iff (BundledStep S) h).mpr
      exact ⟨pairs, old, new, tail, by simp [h], hbad⟩
  · rintro ⟨h, hraw, hbad⟩
    obtain ⟨pairs, old, new, tail, hrows, hstep⟩ :=
      (badStepAtParity_zero_iff (BundledStep S) h).mp hbad
    let pre := Symbol.separator :: encodeAux true (rowsOfPairs pairs)
    let core := old.map Symbol.cell ++
      Symbol.separator :: new.reverse.map Symbol.cell
    let suffix := Symbol.separator :: encodeAux true tail
    rw [evenBadStepRealization, Language.mem_mul]
    refine ⟨pre, (mem_evenPrefixLanguage_iff pre).mpr ⟨pairs, rfl⟩,
      core ++ suffix, ?_, ?_⟩
    · rw [Language.mem_mul]
      exact ⟨core, (mem_evenBadStepCore_iff S core).mpr
          ⟨old, new, hstep, rfl⟩,
        suffix, (mem_afterPairLanguage_iff true suffix).mpr
          ⟨tail, rfl⟩,
        rfl⟩
    · have hencoded := encode_evenSelected_eq pairs old new tail
      exact hencoded.symm.trans
        ((congrArg encode hrows).symm.trans hraw)

theorem oddBadStepRealization_eq
    (S : CertifiedRowSystem I A C Q F) :
    oddBadStepRealization S =
      relaxedBadStepLanguage 1 (BundledStep S) := by
  ext w
  constructor
  · intro hw
    rw [oddBadStepRealization, Language.mem_mul] at hw
    obtain ⟨pre, hpre, rest, hrest, rfl⟩ := hw
    rw [Language.mem_mul] at hrest
    obtain ⟨core, hcore, suffix, hsuffix, rfl⟩ := hrest
    obtain ⟨pairs, prior, hpre⟩ :=
      (mem_oddPrefixLanguage_iff pre).mp hpre
    obtain ⟨old, new, hbad, hcore⟩ :=
      (mem_oddBadStepCore_iff S core).mp hcore
    obtain ⟨tail, hsuffix⟩ :=
      (mem_afterPairLanguage_iff false suffix).mp hsuffix
    subst pre
    subst core
    subst suffix
    let h := oddSelectedHistory pairs prior old new tail
    refine ⟨h, ?_, ?_⟩
    · simpa [RawRepresents, h] using
        encode_oddSelected_eq pairs prior old new tail
    · apply (badStepAtParity_one_iff (BundledStep S) h).mpr
      exact ⟨pairs, prior, old, new, tail, by simp [h], hbad⟩
  · rintro ⟨h, hraw, hbad⟩
    obtain ⟨pairs, prior, old, new, tail, hrows, hstep⟩ :=
      (badStepAtParity_one_iff (BundledStep S) h).mp hbad
    let pre := Symbol.separator ::
      encodeAux true (rowsOfPairs pairs ++ [prior])
    let core := old.reverse.map Symbol.cell ++
      Symbol.separator :: new.map Symbol.cell
    let suffix := Symbol.separator :: encodeAux false tail
    rw [oddBadStepRealization, Language.mem_mul]
    refine ⟨pre, (mem_oddPrefixLanguage_iff pre).mpr
        ⟨pairs, prior, rfl⟩,
      core ++ suffix, ?_, ?_⟩
    · rw [Language.mem_mul]
      exact ⟨core, (mem_oddBadStepCore_iff S core).mpr
          ⟨old, new, hstep, rfl⟩,
        suffix, (mem_afterPairLanguage_iff false suffix).mpr
          ⟨tail, rfl⟩,
        rfl⟩
    · have hencoded := encode_oddSelected_eq pairs prior old new tail
      exact hencoded.symm.trans
        ((congrArg encode hrows).symm.trans hraw)

section FiniteRealizations

variable [Fintype A] [DecidableEq A] [Fintype C] [DecidableEq C]
  [Fintype Q] [DecidableEq Q]

theorem evenBadStepRealization_is_CF
    (S : CertifiedRowSystem I A C Q F) :
    is_CF (evenBadStepRealization S) := by
  apply CF_of_CF_c_CF
  refine ⟨is_CF_of_is_RG (is_RG_of_isRegular
      (evenPrefixLanguage_isRegular (A := BundledCell A C))), ?_⟩
  apply CF_of_CF_c_CF
  exact ⟨evenBadStepCore_is_CF S,
    is_CF_of_is_RG (is_RG_of_isRegular
      (afterPairLanguage_isRegular (A := BundledCell A C)))⟩

theorem oddBadStepRealization_is_CF
    (S : CertifiedRowSystem I A C Q F) :
    is_CF (oddBadStepRealization S) := by
  apply CF_of_CF_c_CF
  refine ⟨is_CF_of_is_RG (is_RG_of_isRegular
      (oddPrefixLanguage_isRegular (A := BundledCell A C))), ?_⟩
  apply CF_of_CF_c_CF
  exact ⟨oddBadStepCore_is_CF S,
    is_CF_of_is_RG (is_RG_of_isRegular
      (afterPairLanguage_isRegular (A := BundledCell A C)))⟩

theorem relaxedBadStepLanguage_zero_is_CF
    (S : CertifiedRowSystem I A C Q F) :
    is_CF (relaxedBadStepLanguage 0 (BundledStep S)) := by
  rw [← evenBadStepRealization_eq S]
  exact evenBadStepRealization_is_CF S

theorem relaxedBadStepLanguage_one_is_CF
    (S : CertifiedRowSystem I A C Q F) :
    is_CF (relaxedBadStepLanguage 1 (BundledStep S)) := by
  rw [← oddBadStepRealization_eq S]
  exact oddBadStepRealization_is_CF S

end FiniteRealizations

end ContextFree.MalformedHistories
