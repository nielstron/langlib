module

public import Langlib.Automata.LinearBounded.CertifiedRowSystem
public import Langlib.Classes.Regular.Closure.Homomorphism
import Mathlib.Tactic

@[expose]
public section

/-!
# Fixed-depth certified-row reachability is regular

For a fixed number `k` of row edges, all intermediate rows and all edge certificates can be
guessed one input column at a time.  A finite automaton then runs the `k` local edge verifiers and
the final-row verifier in parallel.  Projecting away the guessed tracks leaves the original input.

This is a genuinely finite-depth result: the state type contains one verifier state for each of
the fixed `k` edges.  It does not provide a uniform automaton when the path depth is allowed to
grow with the input.
-/

open Classical

namespace CertifiedRowSystem

variable {I A C Q F : Type*} (S : CertifiedRowSystem I A C Q F)

/-- One vertical column of a depth-`k` row-path witness.

The first component is the input symbol.  The `Fin k → A` component contains the cells of rows
`1, ..., k`; row zero is forced to be `S.inputCell input`.  The last component contains one
certificate cell for each of the `k` edges. -/
public abbrev FixedDepthColumn (I A C : Type*) (k : ℕ) :=
  I × (Fin k → A) × (Fin k → C)

/-- The cell at a specified row of a vertical witness column. -/
public def FixedDepthColumn.row {k : ℕ} (column : FixedDepthColumn I A C k) :
    Fin (k + 1) → A :=
  Fin.cases (S.inputCell column.1) column.2.1

/-- Reconstruct one horizontal row from a list of vertical witness columns. -/
public def fixedDepthRow {k : ℕ} (columns : List (FixedDepthColumn I A C k))
    (depth : Fin (k + 1)) : List A :=
  columns.map fun column => column.row S depth

/-- Reconstruct the certificate row for one edge from vertical witness columns. -/
public def fixedDepthCertificate {k : ℕ} (columns : List (FixedDepthColumn I A C k))
    (edge : Fin k) : List C :=
  columns.map fun column => column.2.2 edge

/-- Finite control used while scanning a fixed-depth witness.

The Boolean records whether at least one column has been read, the function stores the local
verifier state for each edge, and the final component stores the target-row verifier state. -/
public abbrev FixedDepthState (Q F : Type*) (k : ℕ) :=
  Bool × (Fin k → Q) × F

/-- A DFA over complete vertical witnesses for an accepting path of exactly `k` row edges. -/
public def fixedDepthDFA (k : ℕ) :
    DFA (FixedDepthColumn I A C k) (FixedDepthState Q F k) where
  start := (false, (fun _ => S.stepStart), S.finalStart)
  step state column :=
    (true,
      (fun edge =>
        S.stepCell (state.2.1 edge)
          (column.row S edge.castSucc)
          (column.row S edge.succ)
          (column.2.2 edge)),
      S.finalCell state.2.2 (column.row S (Fin.last k)))
  accept := { state |
    state.1 = true ∧
      (∀ edge, S.stepDone (state.2.1 edge) = true) ∧
      S.finalDone state.2.2 = true }

private theorem fixedDepthDFA_seen
    {k : ℕ} (columns : List (FixedDepthColumn I A C k))
    (state : FixedDepthState Q F k) :
    ((S.fixedDepthDFA k).evalFrom state columns).1 =
      (state.1 || decide (columns ≠ [])) := by
  induction columns generalizing state with
  | nil => simp [fixedDepthDFA]
  | cons column columns ih =>
      rw [DFA.evalFrom_cons, ih]
      simp [fixedDepthDFA]

private theorem fixedDepthDFA_edge
    {k : ℕ} (columns : List (FixedDepthColumn I A C k))
    (state : FixedDepthState Q F k) (edge : Fin k) :
    S.evalStep (state.2.1 edge)
        (S.fixedDepthRow columns edge.castSucc)
        (S.fixedDepthRow columns edge.succ)
        (fixedDepthCertificate columns edge) =
      some (((S.fixedDepthDFA k).evalFrom state columns).2.1 edge) := by
  induction columns generalizing state with
  | nil => simp [fixedDepthRow, fixedDepthCertificate, evalStep, fixedDepthDFA]
  | cons column columns ih =>
      simp only [fixedDepthRow, fixedDepthCertificate, List.map_cons, evalStep,
        DFA.evalFrom_cons]
      exact ih ((S.fixedDepthDFA k).step state column)

private theorem fixedDepthDFA_final
    {k : ℕ} (columns : List (FixedDepthColumn I A C k))
    (state : FixedDepthState Q F k) :
    S.evalFinal state.2.2 (S.fixedDepthRow columns (Fin.last k)) =
      ((S.fixedDepthDFA k).evalFrom state columns).2.2 := by
  induction columns generalizing state with
  | nil => simp [fixedDepthRow, evalFinal, fixedDepthDFA]
  | cons column columns ih =>
      simp only [fixedDepthRow, List.map_cons, evalFinal, DFA.evalFrom_cons]
      exact ih ((S.fixedDepthDFA k).step state column)

/-- The witness DFA accepts exactly the nonempty column lists whose reconstructed adjacent rows
pass all `k` certified edge checks and whose last row is final. -/
public theorem mem_fixedDepthDFA_accepts_iff
    {k : ℕ} (columns : List (FixedDepthColumn I A C k)) :
    columns ∈ (S.fixedDepthDFA k).accepts ↔
      columns ≠ [] ∧
      (∀ edge : Fin k,
        ∃ q,
          S.evalStep S.stepStart
              (S.fixedDepthRow columns edge.castSucc)
              (S.fixedDepthRow columns edge.succ)
              (fixedDepthCertificate columns edge) = some q ∧
            S.stepDone q = true) ∧
      S.Final (S.fixedDepthRow columns (Fin.last k)) := by
  rw [DFA.mem_accepts]
  change
    ((S.fixedDepthDFA k).evalFrom (S.fixedDepthDFA k).start columns).1 = true ∧
        (∀ edge,
          S.stepDone
            (((S.fixedDepthDFA k).evalFrom
              (S.fixedDepthDFA k).start columns).2.1 edge) =
              true) ∧
        S.finalDone
          ((S.fixedDepthDFA k).evalFrom (S.fixedDepthDFA k).start columns).2.2 = true ↔ _
  rw [S.fixedDepthDFA_seen columns (S.fixedDepthDFA k).start]
  rw [← S.fixedDepthDFA_final columns (S.fixedDepthDFA k).start]
  simp only [fixedDepthDFA, Bool.false_or, decide_eq_true_eq]
  constructor
  · rintro ⟨hne, hedges, hfinal⟩
    refine ⟨hne, ?_, hfinal⟩
    intro edge
    refine ⟨_, S.fixedDepthDFA_edge columns (S.fixedDepthDFA k).start edge, ?_⟩
    exact hedges edge
  · rintro ⟨hne, hedges, hfinal⟩
    refine ⟨hne, ?_, hfinal⟩
    intro edge
    obtain ⟨q, heval, hdone⟩ := hedges edge
    have hcanonical :=
      S.fixedDepthDFA_edge columns (S.fixedDepthDFA k).start edge
    change
      S.evalStep S.stepStart
          (S.fixedDepthRow columns edge.castSucc)
          (S.fixedDepthRow columns edge.succ)
          (fixedDepthCertificate columns edge) =
        some (((S.fixedDepthDFA k).evalFrom
          (S.fixedDepthDFA k).start columns).2.1 edge) at hcanonical
    rw [heval] at hcanonical
    exact Option.some.inj hcanonical ▸ hdone

/-- The original-input language obtained by projecting away all fixed-depth row and certificate
tracks from accepted vertical witnesses. -/
public def rowReachExactlyLanguage (k : ℕ) : Language I :=
  Language.map (fun column : FixedDepthColumn I A C k => column.1)
    (S.fixedDepthDFA k).accepts

/-- A conventional, row-oriented description of an accepting path with exactly `k` edges.

Rows are represented as functions on the positions of `w`; `List.ofFn` turns them back into
ordinary rows.  This representation builds the common row length into the type and avoids adding
redundant length equalities to the predicate. -/
public def HasRowPathExactly (k : ℕ) (w : List I) : Prop :=
  ∃ rows : Fin (k + 1) → Fin w.length → A,
    (∀ position, rows 0 position = S.inputCell (w.get position)) ∧
    (∀ edge : Fin k,
      S.RowStep
        (List.ofFn (rows edge.castSucc))
        (List.ofFn (rows edge.succ))) ∧
    S.Final (List.ofFn (rows (Fin.last k)))

private theorem ofFn_get_cast {X : Type*} (xs : List X) {n : ℕ}
    (h : n = xs.length) :
    List.ofFn (fun position : Fin n => xs.get (Fin.cast h position)) = xs := by
  subst n
  exact List.ofFn_get xs

/-- Membership in the projected fixed-depth language gives an ordinary row path of exactly the
specified depth. -/
public theorem mem_rowReachExactlyLanguage_imp_hasRowPathExactly
    {k : ℕ} {w : List I} (hw : w ∈ S.rowReachExactlyLanguage k) :
    w ≠ [] ∧ S.HasRowPathExactly k w := by
  rcases hw with ⟨columns, hcolumns, rfl⟩
  rw [S.mem_fixedDepthDFA_accepts_iff] at hcolumns
  rcases hcolumns with ⟨hcolumnsNe, hedges, hfinal⟩
  have hinputNe :
      List.map (fun column : FixedDepthColumn I A C k => column.1) columns ≠ [] := by
    simpa using hcolumnsNe
  refine ⟨hinputNe, ?_⟩
  let rows :
      Fin (k + 1) →
        Fin (List.map (fun column : FixedDepthColumn I A C k => column.1)
          columns).length → A :=
    fun depth position =>
      (S.fixedDepthRow columns depth).get
        (Fin.cast (by simp [fixedDepthRow]) position)
  have hrows (depth : Fin (k + 1)) :
      List.ofFn (rows depth) = S.fixedDepthRow columns depth := by
    exact ofFn_get_cast _ (by simp [fixedDepthRow])
  refine ⟨rows, ?_, ?_, ?_⟩
  · intro position
    simp [rows, fixedDepthRow, FixedDepthColumn.row]
  · intro edge
    obtain ⟨q, heval, hdone⟩ := hedges edge
    refine ⟨fixedDepthCertificate columns edge, q, ?_, hdone⟩
    rw [hrows, hrows]
    exact heval
  · rw [hrows]
    exact hfinal

/-- Every ordinary nonempty row path of exactly `k` edges can be transposed into an accepted
vertical witness and hence belongs to the projected fixed-depth language. -/
public theorem hasRowPathExactly_imp_mem_rowReachExactlyLanguage
    {k : ℕ} {w : List I} (hw : w ≠ []) (hpath : S.HasRowPathExactly k w) :
    w ∈ S.rowReachExactlyLanguage k := by
  rcases hpath with ⟨rows, hinput, hedges, hfinal⟩
  have hedgeWitness :
      ∀ edge : Fin k,
        ∃ cert q,
          S.evalStep S.stepStart
              (List.ofFn (rows edge.castSucc))
              (List.ofFn (rows edge.succ))
              cert = some q ∧
            S.stepDone q = true :=
    hedges
  choose certificates outputs heval hdone using hedgeWitness
  have hcertificateLength (edge : Fin k) :
      w.length = (certificates edge).length := by
    have hlength := (S.evalStep_nil_iff (heval edge)).2
    simpa using hlength
  let certificateCells : Fin k → Fin w.length → C :=
    fun edge position =>
      (certificates edge).get
        (Fin.cast (hcertificateLength edge) position)
  let columns : List (FixedDepthColumn I A C k) :=
    List.ofFn fun position =>
      (w.get position,
        (fun edge => rows edge.succ position),
        (fun edge => certificateCells edge position))
  have hprojection :
      List.map (fun column : FixedDepthColumn I A C k => column.1) columns = w := by
    simp [columns, List.map_ofFn, Function.comp_def]
  have hcolumnsNe : columns ≠ [] := by
    intro hnil
    apply hw
    calc
      w = List.map (fun column : FixedDepthColumn I A C k => column.1) columns :=
        hprojection.symm
      _ = [] := by simp [hnil]
  have hinputRow :
      List.ofFn (rows 0) = w.map S.inputCell := by
    calc
      List.ofFn (rows 0) =
          List.ofFn (fun position => S.inputCell (w.get position)) := by
            apply congrArg List.ofFn
            funext position
            exact hinput position
      _ = List.map S.inputCell (List.ofFn w.get) := by
            rw [List.map_ofFn]
            rfl
      _ = w.map S.inputCell := by rw [List.ofFn_get]
  have hrow (depth : Fin (k + 1)) :
      S.fixedDepthRow columns depth = List.ofFn (rows depth) := by
    refine Fin.cases ?_ (fun edge => ?_) depth
    · simp [columns, fixedDepthRow, FixedDepthColumn.row, List.map_ofFn,
        Function.comp_def]
      exact hinputRow.symm
    · simp [columns, fixedDepthRow, FixedDepthColumn.row, List.map_ofFn,
        Function.comp_def]
  have hcertificate (edge : Fin k) :
      fixedDepthCertificate columns edge = certificates edge := by
    simp only [fixedDepthCertificate, columns, List.map_ofFn]
    change
      List.ofFn (fun position : Fin w.length =>
        (certificates edge).get
          (Fin.cast (hcertificateLength edge) position)) =
        certificates edge
    exact ofFn_get_cast _ (hcertificateLength edge)
  have haccepted : columns ∈ (S.fixedDepthDFA k).accepts := by
    rw [S.mem_fixedDepthDFA_accepts_iff]
    refine ⟨hcolumnsNe, ?_, ?_⟩
    · intro edge
      refine ⟨outputs edge, ?_, hdone edge⟩
      rw [hrow, hrow, hcertificate]
      exact heval edge
    · rw [hrow]
      exact hfinal
  exact ⟨columns, haccepted, hprojection⟩

/-- The fixed-depth projected language is exactly the language of nonempty inputs admitting an
accepting row path with exactly `k` certified edges. -/
public theorem mem_rowReachExactlyLanguage_iff
    {k : ℕ} {w : List I} :
    w ∈ S.rowReachExactlyLanguage k ↔
      w ≠ [] ∧ S.HasRowPathExactly k w := by
  constructor
  · exact S.mem_rowReachExactlyLanguage_imp_hasRowPathExactly
  · rintro ⟨hw, hpath⟩
    exact S.hasRowPathExactly_imp_mem_rowReachExactlyLanguage hw hpath

/-- Inputs with an accepting row path of at most `k` edges, presented as a finite union of the
exact-depth languages. -/
public def rowReachAtMostLanguage : ℕ → Language I
  | 0 => S.rowReachExactlyLanguage 0
  | k + 1 => rowReachAtMostLanguage k + S.rowReachExactlyLanguage (k + 1)

/-- The recursive finite union has the expected bounded-path semantics. -/
public theorem mem_rowReachAtMostLanguage_iff
    {k : ℕ} {w : List I} :
    w ∈ S.rowReachAtMostLanguage k ↔
      w ≠ [] ∧ ∃ depth ≤ k, S.HasRowPathExactly depth w := by
  induction k with
  | zero =>
      rw [rowReachAtMostLanguage, S.mem_rowReachExactlyLanguage_iff]
      constructor
      · rintro ⟨hw, hpath⟩
        exact ⟨hw, 0, Nat.le_refl 0, hpath⟩
      · rintro ⟨hw, depth, hdepth, hpath⟩
        have : depth = 0 := Nat.eq_zero_of_le_zero hdepth
        subst depth
        exact ⟨hw, hpath⟩
  | succ k ih =>
      rw [rowReachAtMostLanguage, Language.mem_add, ih,
        S.mem_rowReachExactlyLanguage_iff]
      constructor
      · rintro (⟨hw, depth, hdepth, hpath⟩ | ⟨hw, hpath⟩)
        · exact ⟨hw, depth, Nat.le.step hdepth, hpath⟩
        · exact ⟨hw, k + 1, Nat.le_refl _, hpath⟩
      · rintro ⟨hw, depth, hdepth, hpath⟩
        by_cases hle : depth ≤ k
        · exact Or.inl ⟨hw, depth, hle, hpath⟩
        · have heq : depth = k + 1 := by omega
          subst depth
          exact Or.inr ⟨hw, hpath⟩

/-- Fixed-depth certified-row reachability is regular.

All alphabet and verifier types are finite, while the theorem is uniform in the chosen natural
number `k`.  The resulting automaton itself depends on `k`. -/
public theorem rowReachExactlyLanguage_isRegular
    [Fintype I] [Fintype A] [Fintype C] [Fintype Q] [Fintype F]
    (k : ℕ) :
    (S.rowReachExactlyLanguage k).IsRegular := by
  apply Language.IsRegular.map
  rw [Language.isRegular_iff]
  exact ⟨FixedDepthState Q F k, inferInstance, S.fixedDepthDFA k, rfl⟩

/-- Reachability bounded by any fixed number of row edges is regular. -/
public theorem rowReachAtMostLanguage_isRegular
    [Fintype I] [Fintype A] [Fintype C] [Fintype Q] [Fintype F]
    (k : ℕ) :
    (S.rowReachAtMostLanguage k).IsRegular := by
  induction k with
  | zero =>
      exact S.rowReachExactlyLanguage_isRegular 0
  | succ k ih =>
      simpa [rowReachAtMostLanguage] using
        ih.add (S.rowReachExactlyLanguage_isRegular (k + 1))

end CertifiedRowSystem

end
