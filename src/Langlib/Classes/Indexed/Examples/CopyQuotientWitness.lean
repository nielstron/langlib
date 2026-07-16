module

public import Langlib.Classes.Indexed.Examples.IntersectionWitness
import Langlib.Utilities.Tactics

@[expose]
public section

/-!
# A balanced-copy indexed language for the quotient counterexample

Let `A = {(a b^n)^m | n,m > 0}` be the first intersection witness.  This
file constructs an indexed grammar for

`{ code(w) # reverse(code(w)) | w ∈ A }`.

The grammar chooses the common `b`-run length on its flag stack.  A recursive
nonterminal then emits matched block generators on the two sides of the
separator.  Every nonterminal created by an indexed production receives the
same stack, so the two halves agree without putting an oracle into the
language representation.
-/

open List

namespace IndexedIntersectionWitness

/-- Three-letter alphabet used to separate the copied halves. -/
public inductive CopyLetter where
  | a | b | separator
deriving DecidableEq, Fintype, Inhabited

/-- Embed the binary witness alphabet into the copy alphabet. -/
public def copyCode : Bool → CopyLetter
  | false => .a
  | true => .b

public theorem copyCode_injective : Function.Injective copyCode := by
  intro x y h
  cases x <;> cases y <;> simp [copyCode] at h ⊢

/-- The numerator of the indexed right-quotient witness. -/
public def indexedCopyNumerator : Language CopyLetter := fun w =>
  ∃ n m : Nat, 0 < n ∧ 0 < m ∧
    w = (blockPower n m).map copyCode ++
      [.separator] ++ (blockPower n m).reverse.map copyCode

public inductive CopyNT where
  | S | X | Z | W | Y | P | Q
deriving DecidableEq

public inductive CopyFlag where
  | count | bottom
deriving DecidableEq

/-- Indexed grammar producing a word from `A`, a separator, and its reversal. -/
public def grammarIndexedCopyNumerator : IndexedGrammar CopyLetter where
  nt := CopyNT
  flag := CopyFlag
  initial := .S
  rules := [
    { lhs := .S, consume := none,
      rhs := [.nonterminal .X (some .bottom)] },
    { lhs := .X, consume := none,
      rhs := [.nonterminal .Z (some .count)] },
    { lhs := .Z, consume := none,
      rhs := [.nonterminal .Z (some .count)] },
    { lhs := .Z, consume := none,
      rhs := [.nonterminal .Y none, .nonterminal .W none,
        .nonterminal .Q none] },
    { lhs := .W, consume := none,
      rhs := [.nonterminal .Y none, .nonterminal .W none,
        .nonterminal .Q none] },
    { lhs := .W, consume := none, rhs := [.terminal .separator] },
    { lhs := .Y, consume := none,
      rhs := [.terminal .a, .nonterminal .P none] },
    { lhs := .P, consume := some .count,
      rhs := [.terminal .b, .nonterminal .P none] },
    { lhs := .P, consume := some .bottom, rhs := [] },
    { lhs := .Q, consume := some .count,
      rhs := [.terminal .b, .nonterminal .Q none] },
    { lhs := .Q, consume := some .bottom, rhs := [.terminal .a] }
  ]

private abbrev CG := grammarIndexedCopyNumerator
private abbrev cS (s : List CopyFlag) : CG.ISym := .indexed .S s
private abbrev cX (s : List CopyFlag) : CG.ISym := .indexed .X s
private abbrev cZ (s : List CopyFlag) : CG.ISym := .indexed .Z s
private abbrev cW (s : List CopyFlag) : CG.ISym := .indexed .W s
private abbrev cY (s : List CopyFlag) : CG.ISym := .indexed .Y s
private abbrev cP (s : List CopyFlag) : CG.ISym := .indexed .P s
private abbrev cQ (s : List CopyFlag) : CG.ISym := .indexed .Q s
private abbrev ca : CG.ISym := .terminal .a
private abbrev cb : CG.ISym := .terminal .b
private abbrev csep : CG.ISym := .terminal .separator

private def cStack (n : Nat) : List CopyFlag :=
  replicate n .count ++ [.bottom]

@[simp] private lemma cStack_zero : cStack 0 = [.bottom] := by
  simp [cStack]

private lemma cStack_succ (n : Nat) :
    cStack (n + 1) = .count :: cStack n := by
  simp [cStack, replicate_succ]

private def copiedBlock (n : Nat) : List CopyLetter :=
  .a :: replicate n .b

@[simp] private lemma map_copyCode_abBlock (n : Nat) :
    (abBlock n).map copyCode = copiedBlock n := by
  simp [abBlock, copiedBlock, copyCode]

private lemma map_copyCode_blockPower (n m : Nat) :
    (blockPower n m).map copyCode =
      (replicate m (copiedBlock n)).flatten := by
  induction m with
  | zero => simp [blockPower]
  | succ m ih =>
      rw [blockPower_succ, List.map_append, map_copyCode_abBlock, ih]
      rw [List.replicate_succ, List.flatten_cons]

private lemma reverse_map_copyCode_blockPower (n m : Nat) :
    (blockPower n m).reverse.map copyCode =
      (replicate m (copiedBlock n).reverse).flatten := by
  rw [List.map_reverse]
  rw [map_copyCode_blockPower]
  simp [List.reverse_flatten]

private lemma cStepS : CG.Transforms [cS []] [cX (cStack 0)] := by
  refine ⟨⟨.S, none, [.nonterminal .X (some .bottom)]⟩,
    [], [], [], ?_, rfl, ?_⟩
  · simp [grammarIndexedCopyNumerator]
  · simp [IndexedGrammar.expandRhs, cStack]

private lemma cStepX : CG.Transforms [cX (cStack 0)] [cZ (cStack 1)] := by
  refine ⟨⟨.X, none, [.nonterminal .Z (some .count)]⟩,
    [], [], cStack 0, ?_, rfl, ?_⟩
  · simp [grammarIndexedCopyNumerator]
  · simp [IndexedGrammar.expandRhs, cStack, replicate_succ]

private lemma cPushZ (n : Nat) :
    CG.Transforms [cZ (cStack n)] [cZ (cStack (n + 1))] := by
  refine ⟨⟨.Z, none, [.nonterminal .Z (some .count)]⟩,
    [], [], cStack n, ?_, rfl, ?_⟩
  · simp [grammarIndexedCopyNumerator]
  · simp [IndexedGrammar.expandRhs, cStack_succ]

private lemma cPushZMany (n : Nat) :
    CG.Derives [cZ (cStack 1)] [cZ (cStack (n + 1))] := by
  induction n with
  | zero => exact Relation.ReflTransGen.refl
  | succ n ih => exact ih.tail (cPushZ (n + 1))

private lemma cStartPairs (n : Nat) :
    CG.Transforms [cZ (cStack n)]
      [cY (cStack n), cW (cStack n), cQ (cStack n)] := by
  refine ⟨⟨.Z, none, [.nonterminal .Y none, .nonterminal .W none,
    .nonterminal .Q none]⟩, [], [], cStack n, ?_, rfl, ?_⟩
  · simp [grammarIndexedCopyNumerator]
  · simp [IndexedGrammar.expandRhs]

private lemma cExpandW (n : Nat) :
    CG.Transforms [cW (cStack n)]
      [cY (cStack n), cW (cStack n), cQ (cStack n)] := by
  refine ⟨⟨.W, none, [.nonterminal .Y none, .nonterminal .W none,
    .nonterminal .Q none]⟩, [], [], cStack n, ?_, rfl, ?_⟩
  · simp [grammarIndexedCopyNumerator]
  · simp [IndexedGrammar.expandRhs]

private lemma cExpandWMany (n k : Nat) :
    CG.Derives [cW (cStack n)]
      (replicate k (cY (cStack n)) ++ [cW (cStack n)] ++
        replicate k (cQ (cStack n))) := by
  induction k with
  | zero => simp; exact Relation.ReflTransGen.refl
  | succ k ih =>
      apply IndexedGrammar.deri_of_tran_deri (cExpandW n)
      have hctx := IndexedGrammar.deri_with_prefix [cY (cStack n)]
        (IndexedGrammar.deri_with_suffix [cQ (cStack n)] ih)
      have hy : replicate (k + 1) (cY (cStack n)) =
          cY (cStack n) :: replicate k (cY (cStack n)) := by
        rw [List.replicate_succ]
      have hq : replicate (k + 1) (cQ (cStack n)) =
          replicate k (cQ (cStack n)) ++ [cQ (cStack n)] := by
        rw [List.replicate_succ']
      rw [hy, hq]
      simpa [replicate_succ, List.append_assoc] using hctx

private lemma cStopW (n : Nat) :
    CG.Transforms [cW (cStack n)] [csep] := by
  refine ⟨⟨.W, none, [.terminal .separator]⟩,
    [], [], cStack n, ?_, rfl, ?_⟩
  · simp [grammarIndexedCopyNumerator]
  · simp [IndexedGrammar.expandRhs]

private lemma cConsumeP (n : Nat) :
    CG.Derives [cP (cStack n)] (replicate n cb) := by
  induction n with
  | zero =>
      exact Relation.ReflTransGen.single
        ⟨⟨.P, some .bottom, []⟩, [], [], [], by
          simp [grammarIndexedCopyNumerator], by simp [cStack], by
          simp [IndexedGrammar.expandRhs]⟩
  | succ n ih =>
      apply IndexedGrammar.deri_of_tran_deri
      · refine ⟨⟨.P, some .count,
          [.terminal .b, .nonterminal .P none]⟩,
          [], [], cStack n, ?_, ?_, rfl⟩
        · simp [grammarIndexedCopyNumerator]
        · simp [cStack_succ]
      · convert IndexedGrammar.deri_with_prefix [cb] ih using 1 <;>
          simp [replicate_succ]

private lemma cConsumeQ (n : Nat) :
    CG.Derives [cQ (cStack n)] (replicate n cb ++ [ca]) := by
  induction n with
  | zero =>
      exact Relation.ReflTransGen.single
        ⟨⟨.Q, some .bottom, [.terminal .a]⟩,
          [], [], [], by simp [grammarIndexedCopyNumerator], by simp [cStack], by
          simp [IndexedGrammar.expandRhs]⟩
  | succ n ih =>
      apply IndexedGrammar.deri_of_tran_deri
      · refine ⟨⟨.Q, some .count,
          [.terminal .b, .nonterminal .Q none]⟩,
          [], [], cStack n, ?_, ?_, rfl⟩
        · simp [grammarIndexedCopyNumerator]
        · simp [cStack_succ]
      · convert IndexedGrammar.deri_with_prefix [cb] ih using 1 <;>
          simp [replicate_succ, List.append_assoc]

private lemma cGenerateY (n : Nat) :
    CG.Derives [cY (cStack n)]
      ((copiedBlock n).map IndexedGrammar.ISym.terminal) := by
  apply IndexedGrammar.deri_of_tran_deri
  · refine ⟨⟨.Y, none, [.terminal .a, .nonterminal .P none]⟩,
      [], [], cStack n, ?_, rfl, rfl⟩
    · simp [grammarIndexedCopyNumerator]
  · convert IndexedGrammar.deri_with_prefix [ca] (cConsumeP n) using 1 <;>
      simp [copiedBlock, replicate_succ]

private lemma cGenerateQ (n : Nat) :
    CG.Derives [cQ (cStack n)]
      ((copiedBlock n).reverse.map IndexedGrammar.ISym.terminal) := by
  simpa [copiedBlock, List.map_append, List.append_assoc] using cConsumeQ n

private lemma cGenerateRepeatedY (n m : Nat) :
    CG.Derives (replicate m (cY (cStack n)))
      (((replicate m (copiedBlock n)).flatten).map
        IndexedGrammar.ISym.terminal) := by
  induction m with
  | zero => simp; exact Relation.ReflTransGen.refl
  | succ m ih =>
      have hy : replicate (m + 1) (cY (cStack n)) =
          cY (cStack n) :: replicate m (cY (cStack n)) := by
        rw [List.replicate_succ]
      have hb : replicate (m + 1) (copiedBlock n) =
          copiedBlock n :: replicate m (copiedBlock n) := by
        rw [List.replicate_succ]
      rw [hy, hb, List.flatten_cons, List.map_append]
      exact IndexedGrammar.deri_of_deri_deri
        (IndexedGrammar.deri_with_suffix
          (replicate m (cY (cStack n))) (cGenerateY n))
        (IndexedGrammar.deri_with_prefix
          ((copiedBlock n).map IndexedGrammar.ISym.terminal) ih)

private lemma cGenerateRepeatedQ (n m : Nat) :
    CG.Derives (replicate m (cQ (cStack n)))
      (((replicate m (copiedBlock n).reverse).flatten).map
        IndexedGrammar.ISym.terminal) := by
  induction m with
  | zero => simp; exact Relation.ReflTransGen.refl
  | succ m ih =>
      have hq : replicate (m + 1) (cQ (cStack n)) =
          cQ (cStack n) :: replicate m (cQ (cStack n)) := by
        rw [List.replicate_succ]
      have hb : replicate (m + 1) (copiedBlock n).reverse =
          (copiedBlock n).reverse ::
            replicate m (copiedBlock n).reverse := by
        rw [List.replicate_succ]
      rw [hq, hb, List.flatten_cons, List.map_append]
      exact IndexedGrammar.deri_of_deri_deri
        (IndexedGrammar.deri_with_suffix
          (replicate m (cQ (cStack n))) (cGenerateQ n))
        (IndexedGrammar.deri_with_prefix
          ((copiedBlock n).reverse.map IndexedGrammar.ISym.terminal) ih)

private lemma cBuildPairs (n k : Nat) :
    CG.Derives [cZ (cStack n)]
      (replicate (k + 1) (cY (cStack n)) ++ [cW (cStack n)] ++
        replicate (k + 1) (cQ (cStack n))) := by
  apply IndexedGrammar.deri_of_tran_deri (cStartPairs n)
  have hctx := IndexedGrammar.deri_with_prefix [cY (cStack n)]
    (IndexedGrammar.deri_with_suffix [cQ (cStack n)]
      (cExpandWMany n k))
  have hy : replicate (k + 1) (cY (cStack n)) =
      cY (cStack n) :: replicate k (cY (cStack n)) := by
    rw [List.replicate_succ]
  have hq : replicate (k + 1) (cQ (cStack n)) =
      replicate k (cQ (cStack n)) ++ [cQ (cStack n)] := by
    rw [List.replicate_succ']
  rw [hy, hq]
  simpa [List.append_assoc] using hctx

private lemma cStopBetweenPairs (n m : Nat) :
    CG.Derives
      (replicate m (cY (cStack n)) ++ [cW (cStack n)] ++
        replicate m (cQ (cStack n)))
      (replicate m (cY (cStack n)) ++ [csep] ++
        replicate m (cQ (cStack n))) := by
  simpa [List.append_assoc] using
    (IndexedGrammar.deri_with_prefix (replicate m (cY (cStack n)))
      (IndexedGrammar.deri_with_suffix (replicate m (cQ (cStack n)))
        (Relation.ReflTransGen.single (cStopW n))))

private lemma cGeneratePairForm (n m : Nat) :
    CG.Derives
      (replicate m (cY (cStack n)) ++ [csep] ++
        replicate m (cQ (cStack n)))
      ((((replicate m (copiedBlock n)).flatten ++ [CopyLetter.separator] ++
        (replicate m (copiedBlock n).reverse).flatten).map
          IndexedGrammar.ISym.terminal)) := by
  let left := (replicate m (copiedBlock n)).flatten
  let right := (replicate m (copiedBlock n).reverse).flatten
  have hleft := IndexedGrammar.deri_with_suffix
    ([csep] ++ replicate m (cQ (cStack n))) (cGenerateRepeatedY n m)
  have hright := IndexedGrammar.deri_with_prefix
    (left.map IndexedGrammar.ISym.terminal ++ [csep]) (cGenerateRepeatedQ n m)
  exact IndexedGrammar.deri_of_deri_deri
    (by simpa [left, List.append_assoc] using hleft)
    (by simpa [left, right, List.map_append, List.append_assoc] using hright)

private lemma indexedCopyNumerator_subset_grammar :
    indexedCopyNumerator ≤ CG.Language := by
  rintro w ⟨n, m, hn, hm, rfl⟩
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  show CG.Generates
    ((blockPower (n + 1) (m + 1)).map copyCode ++ [.separator] ++
      (blockPower (n + 1) (m + 1)).reverse.map copyCode)
  unfold IndexedGrammar.Generates
  apply IndexedGrammar.deri_of_tran_deri cStepS
  apply IndexedGrammar.deri_of_tran_deri cStepX
  apply IndexedGrammar.deri_of_deri_deri (cPushZMany n)
  apply IndexedGrammar.deri_of_deri_deri (cBuildPairs (n + 1) m)
  apply IndexedGrammar.deri_of_deri_deri (cStopBetweenPairs (n + 1) (m + 1))
  have hgen := cGeneratePairForm (n + 1) (m + 1)
  rw [map_copyCode_blockPower, reverse_map_copyCode_blockPower]
  simpa [List.map_append, List.append_assoc] using hgen

/-! ## A compositional soundness interpretation -/

/-- Number of count flags before the first bottom marker. -/
private def cHeight : List CopyFlag → Option Nat
  | [] => none
  | .bottom :: _ => some 0
  | .count :: s => (cHeight s).map Nat.succ

@[simp] private lemma cHeight_bottom (s : List CopyFlag) :
    cHeight (.bottom :: s) = some 0 := rfl

@[simp] private lemma cHeight_count (s : List CopyFlag) :
    cHeight (.count :: s) = (cHeight s).map Nat.succ := rfl

private def cShape (n m : Nat) : List CopyLetter :=
  (blockPower n m).map copyCode ++ [.separator] ++
    (blockPower n m).reverse.map copyCode

private lemma cShape_succ (n m : Nat) :
    cShape n (m + 1) =
      copiedBlock n ++ cShape n m ++ (copiedBlock n).reverse := by
  simp [cShape, blockPower, map_copyCode_abBlock, List.map_append,
    List.reverse_append, List.append_assoc]

private def cFrom (lower : Nat) (w : List CopyLetter) : Prop :=
  ∃ n m : Nat, lower ≤ n ∧ 0 < m ∧ w = cShape n m

private def cSymSem : CG.ISym → List CopyLetter → Prop
  | .terminal t, w => w = [t]
  | .indexed .S _, w => cFrom 1 w
  | .indexed .X s, w =>
      ∃ n, cHeight (.count :: s) = some n ∧ cFrom n w
  | .indexed .Z s, w =>
      ∃ n, cHeight s = some n ∧ cFrom n w
  | .indexed .W s, w =>
      ∀ n, cHeight s = some n → ∃ m, w = cShape n m
  | .indexed .Y s, w =>
      ∃ n, cHeight s = some n ∧ w = copiedBlock n
  | .indexed .P s, w =>
      ∃ n, cHeight s = some n ∧ w = replicate n .b
  | .indexed .Q s, w =>
      ∃ n, cHeight s = some n ∧ w = (copiedBlock n).reverse

private def cFormSem : List CG.ISym → List CopyLetter → Prop
  | [], w => w = []
  | x :: xs, w =>
      ∃ u v, cSymSem x u ∧ cFormSem xs v ∧ w = u ++ v

private lemma cFormSem_append (xs ys : List CG.ISym) (w : List CopyLetter) :
    cFormSem (xs ++ ys) w ↔
      ∃ u v, cFormSem xs u ∧ cFormSem ys v ∧ w = u ++ v := by
  induction xs generalizing w with
  | nil => simp [cFormSem]
  | cons x xs ih =>
      simp only [List.cons_append, cFormSem]
      constructor
      · rintro ⟨p, q, hp, hq, rfl⟩
        obtain ⟨u, v, hu, hv, rfl⟩ := (ih q).mp hq
        exact ⟨p ++ u, v, ⟨p, u, hp, hu, rfl⟩, hv,
          by simp [List.append_assoc]⟩
      · rintro ⟨u, v, ⟨p, q, hp, hq, rfl⟩, hv, rfl⟩
        exact ⟨p, q ++ v, hp, (ih (q ++ v)).mpr
          ⟨q, v, hq, hv, rfl⟩, by simp [List.append_assoc]⟩

@[simp] private lemma cFormSem_singleton (x : CG.ISym)
    (w : List CopyLetter) :
    cFormSem [x] w ↔ cSymSem x w := by
  simp [cFormSem]

private lemma cFormSem_terminals (w : List CopyLetter) :
    cFormSem (w.map IndexedGrammar.ISym.terminal) w := by
  induction w with
  | nil => simp [cFormSem]
  | cons x xs ih => exact ⟨[x], xs, rfl, ih, rfl⟩

private lemma cFormSem_context {lhs : CG.ISym} {rhs u v : List CG.ISym}
    (hsound : ∀ w, cFormSem rhs w → cSymSem lhs w)
    {w : List CopyLetter} (h : cFormSem (u ++ rhs ++ v) w) :
    cFormSem (u ++ [lhs] ++ v) w := by
  rw [List.append_assoc] at h
  obtain ⟨wu, wrv, hu, hrv, rfl⟩ :=
    (cFormSem_append u (rhs ++ v) w).mp h
  obtain ⟨wr, wv, hr, hv, rfl⟩ :=
    (cFormSem_append rhs v wrv).mp hrv
  rw [List.append_assoc]
  apply (cFormSem_append u ([lhs] ++ v) _).mpr
  refine ⟨wu, wr ++ wv, hu, ?_, by simp [List.append_assoc]⟩
  exact (cFormSem_append [lhs] v _).mpr
    ⟨wr, wv, cFormSem_singleton lhs wr |>.mpr (hsound wr hr), hv, rfl⟩

private lemma cThreeSem {x y z : CG.ISym} {w : List CopyLetter}
    (h : cFormSem [x, y, z] w) :
    ∃ u v q, cSymSem x u ∧ cSymSem y v ∧ cSymSem z q ∧
      w = u ++ v ++ q := by
  obtain ⟨u, rest, hu, hrest, rfl⟩ :=
    (cFormSem_append [x] [y, z] w).mp h
  rw [cFormSem_singleton] at hu
  obtain ⟨v, q, hv, hq, rfl⟩ :=
    (cFormSem_append [y] [z] rest).mp hrest
  rw [cFormSem_singleton] at hv hq
  exact ⟨u, v, q, hu, hv, hq, by simp [List.append_assoc]⟩

private lemma cRuleSound (r : IRule CopyLetter CopyNT CopyFlag)
    (hr : r ∈ CG.rules) (s : List CopyFlag) (w : List CopyLetter)
    (h : cFormSem (CG.expandRhs r.rhs s) w) :
    cSymSem (.indexed r.lhs
      (match r.consume with | none => s | some f => f :: s)) w := by
  simp only [grammarIndexedCopyNumerator, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl
  · have h' : cSymSem (cX (.bottom :: s)) w :=
      (cFormSem_singleton _ _).mp (by
        simpa [IndexedGrammar.expandRhs] using h)
    change cSymSem (cS s) w
    simpa [cSymSem, cHeight, cFrom] using h'
  · have h' : cSymSem (cZ (.count :: s)) w :=
      (cFormSem_singleton _ _).mp (by
        simpa [IndexedGrammar.expandRhs] using h)
    change cSymSem (cX s) w
    simpa only [cSymSem] using h'
  · have h' : cSymSem (cZ (.count :: s)) w :=
      (cFormSem_singleton _ _).mp (by
        simpa [IndexedGrammar.expandRhs] using h)
    change cSymSem (cZ s) w
    simp only [cSymSem] at h' ⊢
    rcases h' with ⟨k, hk, q, m, hq, hm, hw⟩
    cases hs : cHeight s with
    | none => simp [hs] at hk
    | some j =>
        simp [hs] at hk
        subst k
        exact ⟨j, rfl, q, m, Nat.le_trans (Nat.le_succ j) hq, hm, hw⟩
  · have h' : cFormSem [cY s, cW s, cQ s] w := by
      simpa [IndexedGrammar.expandRhs] using h
    obtain ⟨u, v, qword, hu, hv, hq, rfl⟩ := cThreeSem h'
    change ∃ n, cHeight s = some n ∧ cFrom n (u ++ v ++ qword)
    change ∃ n, cHeight s = some n ∧ u = copiedBlock n at hu
    change ∀ n, cHeight s = some n → ∃ m, v = cShape n m at hv
    change ∃ n, cHeight s = some n ∧ qword = (copiedBlock n).reverse at hq
    rcases hu with ⟨n, hn, rfl⟩
    obtain ⟨m, rfl⟩ := hv n hn
    rcases hq with ⟨n', hn', hqword⟩
    have hnn : n' = n := by simpa [hn] using hn'.symm
    subst n'
    subst qword
    refine ⟨n, hn, n, m + 1, Nat.le_refl n, Nat.succ_pos m, ?_⟩
    exact (cShape_succ n m).symm
  · have h' : cFormSem [cY s, cW s, cQ s] w := by
      simpa [IndexedGrammar.expandRhs] using h
    obtain ⟨u, v, qword, hu, hv, hq, rfl⟩ := cThreeSem h'
    change ∀ n, cHeight s = some n →
      ∃ m, u ++ v ++ qword = cShape n m
    intro n hn
    change ∃ n', cHeight s = some n' ∧ u = copiedBlock n' at hu
    change ∀ n', cHeight s = some n' → ∃ m, v = cShape n' m at hv
    change ∃ n', cHeight s = some n' ∧
      qword = (copiedBlock n').reverse at hq
    rcases hu with ⟨n₁, hn₁, rfl⟩
    obtain ⟨m, rfl⟩ := hv n hn
    rcases hq with ⟨n₂, hn₂, rfl⟩
    have hn₁n : n₁ = n := by simpa [hn] using hn₁.symm
    have hn₂n : n₂ = n := by simpa [hn] using hn₂.symm
    subst n₁
    subst n₂
    exact ⟨m + 1, (cShape_succ n m).symm⟩
  · have h' : cSymSem csep w :=
      (cFormSem_singleton _ _).mp (by
        simpa [IndexedGrammar.expandRhs] using h)
    change ∀ n, cHeight s = some n → ∃ m, w = cShape n m
    intro n _hn
    exact ⟨0, by simpa [cShape] using h'⟩
  · have h' : cFormSem [ca, cP s] w := by
      simpa [IndexedGrammar.expandRhs] using h
    obtain ⟨u, v, hu, hv, rfl⟩ :=
      (cFormSem_append [ca] [cP s] w).mp h'
    rw [cFormSem_singleton] at hu hv
    change u = [.a] at hu
    change ∃ n, cHeight s = some n ∧ v = replicate n .b at hv
    subst u
    rcases hv with ⟨n, hn, rfl⟩
    exact ⟨n, hn, by simp [copiedBlock]⟩
  · have h' : cFormSem [cb, cP s] w := by
      simpa [IndexedGrammar.expandRhs] using h
    obtain ⟨u, v, hu, hv, rfl⟩ :=
      (cFormSem_append [cb] [cP s] w).mp h'
    rw [cFormSem_singleton] at hu hv
    change u = [.b] at hu
    change ∃ n, cHeight s = some n ∧ v = replicate n .b at hv
    subst u
    rcases hv with ⟨n, hn, rfl⟩
    refine ⟨n + 1, ?_, ?_⟩
    · change (cHeight s).map Nat.succ = some (n + 1)
      rw [hn]
      simp
    · rw [List.replicate_succ]
      rfl
  · have hw : w = [] := by
      simpa [IndexedGrammar.expandRhs, cFormSem] using h
    subst w
    exact ⟨0, rfl, rfl⟩
  · have h' : cFormSem [cb, cQ s] w := by
      simpa [IndexedGrammar.expandRhs] using h
    obtain ⟨u, v, hu, hv, rfl⟩ :=
      (cFormSem_append [cb] [cQ s] w).mp h'
    rw [cFormSem_singleton] at hu hv
    change u = [.b] at hu
    change ∃ n, cHeight s = some n ∧ v = (copiedBlock n).reverse at hv
    subst u
    rcases hv with ⟨n, hn, rfl⟩
    refine ⟨n + 1, ?_, ?_⟩
    · change (cHeight s).map Nat.succ = some (n + 1)
      rw [hn]
      simp
    · simp only [copiedBlock, List.reverse_cons, List.reverse_replicate]
      rw [List.replicate_succ]
      rfl
  · have h' : cSymSem ca w :=
      (cFormSem_singleton _ _).mp (by
        simpa [IndexedGrammar.expandRhs] using h)
    exact ⟨0, rfl, by simpa [copiedBlock] using h'⟩

private lemma cTransforms_sound {x y : List CG.ISym}
    (hxy : CG.Transforms x y) {w : List CopyLetter}
    (hy : cFormSem y w) : cFormSem x w := by
  rcases hxy with ⟨r, u, v, s, hr, hx, rfl⟩
  cases hc : r.consume with
  | none =>
      rw [hc] at hx
      rw [hx]
      exact cFormSem_context (fun z hz => by
        simpa [hc] using cRuleSound r hr s z hz) hy
  | some f =>
      rw [hc] at hx
      rw [hx]
      exact cFormSem_context (fun z hz => by
        simpa [hc] using cRuleSound r hr s z hz) hy

private lemma cDerives_sound {x y : List CG.ISym}
    (hxy : CG.Derives x y) {w : List CopyLetter}
    (hy : cFormSem y w) : cFormSem x w := by
  induction hxy with
  | refl => exact hy
  | tail _ ht ih => exact ih (cTransforms_sound ht hy)

private lemma grammar_subset_indexedCopyNumerator :
    CG.Language ≤ indexedCopyNumerator := by
  intro w hw
  have hs := cDerives_sound hw (cFormSem_terminals w)
  rw [cFormSem_singleton] at hs
  change cSymSem (cS []) w at hs
  change cFrom 1 w at hs
  rcases hs with ⟨n, m, hn, hm, rfl⟩
  exact ⟨n, m, by omega, hm, rfl⟩

/-- The balanced-copy grammar generates exactly the numerator witness. -/
public theorem grammarIndexedCopyNumerator_language :
    grammarIndexedCopyNumerator.Language = indexedCopyNumerator := by
  exact le_antisymm grammar_subset_indexedCopyNumerator
    indexedCopyNumerator_subset_grammar

/-- The balanced-copy numerator is indexed. -/
public theorem indexedCopyNumerator_isIndexed :
    is_Indexed indexedCopyNumerator :=
  ⟨grammarIndexedCopyNumerator, grammarIndexedCopyNumerator_language⟩

end IndexedIntersectionWitness
