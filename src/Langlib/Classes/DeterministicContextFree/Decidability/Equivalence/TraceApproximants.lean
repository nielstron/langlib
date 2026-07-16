module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.RegularTermEquivalence

@[expose]
public section

/-!
# Finite trace approximants for deterministic first-order grammars

This file supplies the effective finite-depth equivalences used by both the
finite-basis and equivalence-level presentations of the positive decidability
argument.  The ambient action type need not be finite: at any term only labels
from the finite rule table, plus the private label of a variable root, can be
enabled.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- A finite superset of all labels enabled at a term.  Including actions whose
rule has a different left-hand side keeps the enumeration proof simple. -/
@[expose] public def candidateLabels (g : EncodedFirstOrderGrammar Action)
    (term : RegularTerm) : List (Label Action) :=
  g.rawRules.map (fun rule => .inl rule.action) ++
    match term.rootNode? with
    | some (.inl x) => [.inr x]
    | _ => []

/-- Every enabled label occurs in the finite candidate list. -/
public theorem mem_candidateLabels_of_step?_eq_some
    {g : EncodedFirstOrderGrammar Action} {label : Label Action}
    {source target : RegularTerm} (hstep : g.step? label source = some target) :
    label ∈ g.candidateLabels source := by
  cases label with
  | inl action =>
      unfold step? rootRewrite? at hstep
      cases hroot : source.rootApplication? with
      | none => simp [hroot] at hstep
      | some app =>
          rcases app with ⟨X, children⟩
          simp only [hroot] at hstep
          obtain ⟨rhs, hrule, _htarget⟩ := Option.map_eq_some_iff.mp hstep
          unfold ruleLookup at hrule
          obtain ⟨rule, hfind, _hrhs⟩ := Option.map_eq_some_iff.mp hrule
          have hmem := findRule_mem hfind
          have hkey := findRule_key hfind
          unfold candidateLabels
          apply List.mem_append_left
          exact List.mem_map.mpr ⟨rule, hmem, by simp [hkey.2]⟩
  | inr x =>
      unfold step? at hstep
      cases hroot : source.rootNode? with
      | none => simp [hroot] at hstep
      | some node =>
          cases node with
          | inr app => simp [hroot] at hstep
          | inl y =>
              have hxy : x = y := by
                by_contra hne
                simp [hroot, hne] at hstep
              subst y
              simp [candidateLabels, hroot]

public theorem step?_eq_none_of_not_mem_candidateLabels
    (g : EncodedFirstOrderGrammar Action) (label : Label Action)
    (source : RegularTerm) (hnot : label ∉ g.candidateLabels source) :
    g.step? label source = none := by
  cases hstep : g.step? label source with
  | none => rfl
  | some target => exact (hnot (mem_candidateLabels_of_step?_eq_some hstep)).elim

/-- Agreement of the two deterministic transition trees through depth `n`. -/
@[expose] public def TraceApprox (g : EncodedFirstOrderGrammar Action) :
    ℕ → RegularTerm → RegularTerm → Prop
  | 0, _, _ => True
  | n + 1, left, right => ∀ label,
      Option.Rel (g.TraceApprox n) (g.step? label left) (g.step? label right)

/-- Executable finite-depth trace comparison. -/
@[expose] public def traceApproxCode (g : EncodedFirstOrderGrammar Action) :
    ℕ → RegularTerm → RegularTerm → Bool
  | 0, _, _ => true
  | n + 1, left, right =>
      (g.candidateLabels left ++ g.candidateLabels right).all fun label =>
        match g.step? label left, g.step? label right with
        | none, none => true
        | some left', some right' => g.traceApproxCode n left' right'
        | _, _ => false

/-- The finite Boolean comparison is exact despite the possibly infinite action
type, because enabled labels are finitely supported by the grammar and root. -/
public theorem traceApproxCode_eq_true_iff (g : EncodedFirstOrderGrammar Action)
    (n : ℕ) (left right : RegularTerm) :
    g.traceApproxCode n left right = true ↔ g.TraceApprox n left right := by
  induction n generalizing left right with
  | zero => simp [traceApproxCode, TraceApprox]
  | succ n ih =>
      simp only [traceApproxCode, TraceApprox, List.all_eq_true]
      constructor
      · intro hall label
        by_cases hmem : label ∈
            g.candidateLabels left ++ g.candidateLabels right
        · have htest := hall label hmem
          cases hleft : g.step? label left with
          | none =>
              cases hright : g.step? label right with
              | none => exact .none
              | some right' => simp [hleft, hright] at htest
          | some left' =>
              cases hright : g.step? label right with
              | none => simp [hleft, hright] at htest
              | some right' =>
                  exact .some ((ih left' right').mp (by
                    simpa [hleft, hright] using htest))
        · have hleftNot : label ∉ g.candidateLabels left := by
            exact fun h => hmem (List.mem_append_left _ h)
          have hrightNot : label ∉ g.candidateLabels right := by
            exact fun h => hmem (List.mem_append_right _ h)
          rw [step?_eq_none_of_not_mem_candidateLabels
              g label left hleftNot,
            step?_eq_none_of_not_mem_candidateLabels
              g label right hrightNot]
          exact .none
      · intro happ label _hmem
        have hrel := happ label
        cases hleft : g.step? label left with
        | none =>
            rw [hleft] at hrel
            cases hright : g.step? label right with
            | none => rfl
            | some right' =>
                rw [hright] at hrel
                cases hrel
        | some left' =>
            rw [hleft] at hrel
            cases hright : g.step? label right with
            | none =>
                rw [hright] at hrel
                cases hrel
            | some right' =>
                rw [hright] at hrel
                cases hrel with
                | some hnext =>
                    exact (ih left' right').mpr hnext

public instance traceApproxDecidable (g : EncodedFirstOrderGrammar Action)
    (n : ℕ) (left right : RegularTerm) :
    Decidable (g.TraceApprox n left right) :=
  decidable_of_iff (g.traceApproxCode n left right = true)
    (traceApproxCode_eq_true_iff g n left right)

/-- Equality of trace membership for all words of length at most `n`. -/
@[expose] public def SameTracesThrough
    (g : EncodedFirstOrderGrammar Action) (n : ℕ)
    (left right : RegularTerm) : Prop :=
  ∀ word, word.length ≤ n →
    (g.IsTrace left word ↔ g.IsTrace right word)

public theorem traceApprox_iff_sameTracesThrough
    (g : EncodedFirstOrderGrammar Action) (n : ℕ)
    (left right : RegularTerm) :
    g.TraceApprox n left right ↔
      g.SameTracesThrough n left right := by
  induction n generalizing left right with
  | zero =>
      constructor
      · intro _ word hlength
        have hword : word = [] := List.length_eq_zero_iff.mp (by omega)
        subst word
        simp [IsTrace]
      · intro _
        trivial
  | succ n ih =>
      constructor
      · intro happrox word hlength
        cases word with
        | nil => simp [IsTrace]
        | cons label word =>
            have hrel := happrox label
            cases hleft : g.step? label left with
            | none =>
                rw [hleft] at hrel
                cases hright : g.step? label right with
                | none => simp [IsTrace, hleft, hright]
                | some right' =>
                    rw [hright] at hrel
                    cases hrel
            | some left' =>
                rw [hleft] at hrel
                cases hright : g.step? label right with
                | none =>
                    rw [hright] at hrel
                    cases hrel
                | some right' =>
                    rw [hright] at hrel
                    cases hrel with
                    | some hnext =>
                        have htail := (ih left' right').mp hnext word (by
                          simpa using Nat.le_of_succ_le_succ hlength)
                        simpa [IsTrace, hleft, hright] using htail
      · intro hsame label
        cases hleft : g.step? label left with
        | none =>
            cases hright : g.step? label right with
            | none => exact .none
            | some right' =>
                have hone := hsame [label] (by simp)
                simp [IsTrace, hleft, hright] at hone
        | some left' =>
            cases hright : g.step? label right with
            | none =>
                have hone := hsame [label] (by simp)
                simp [IsTrace, hleft, hright] at hone
            | some right' =>
                apply Option.Rel.some
                apply (ih left' right').mpr
                intro word hlength
                have hcons := hsame (label :: word) (by simp; omega)
                simpa [IsTrace, hleft, hright] using hcons

@[refl] public theorem traceApprox_refl
    (g : EncodedFirstOrderGrammar Action) (n : ℕ) (term : RegularTerm) :
    g.TraceApprox n term term := by
  apply (traceApprox_iff_sameTracesThrough g n term term).mpr
  intro word _
  rfl

@[symm] public theorem TraceApprox.symm
    {g : EncodedFirstOrderGrammar Action} {n : ℕ}
    {left right : RegularTerm} (h : g.TraceApprox n left right) :
    g.TraceApprox n right left := by
  apply (traceApprox_iff_sameTracesThrough g n right left).mpr
  intro word hlength
  exact ((traceApprox_iff_sameTracesThrough g n left right).mp
    h word hlength).symm

@[trans] public theorem TraceApprox.trans
    {g : EncodedFirstOrderGrammar Action} {n : ℕ}
    {left middle right : RegularTerm}
    (hleft : g.TraceApprox n left middle)
    (hright : g.TraceApprox n middle right) :
    g.TraceApprox n left right := by
  apply (traceApprox_iff_sameTracesThrough g n left right).mpr
  intro word hlength
  exact ((traceApprox_iff_sameTracesThrough g n left middle).mp
    hleft word hlength).trans
      ((traceApprox_iff_sameTracesThrough g n middle right).mp
        hright word hlength)

public theorem traceApprox_anti
    (g : EncodedFirstOrderGrammar Action) {m n : ℕ} (hmn : m ≤ n)
    {left right : RegularTerm} (h : g.TraceApprox n left right) :
    g.TraceApprox m left right := by
  apply (traceApprox_iff_sameTracesThrough g m left right).mpr
  intro word hlength
  exact (traceApprox_iff_sameTracesThrough g n left right).mp
    h word (hlength.trans hmn)

/-- Trace equivalence is the intersection of all effective finite-depth
approximants. -/
public theorem traceEquivalent_iff_forall_traceApprox
    (g : EncodedFirstOrderGrammar Action) (left right : RegularTerm) :
    g.TraceEquivalent left right ↔
      ∀ n, g.TraceApprox n left right := by
  constructor
  · intro hequivalent n
    apply (traceApprox_iff_sameTracesThrough g n left right).mpr
    intro word _hlength
    change word ∈ g.traceLanguage left ↔ word ∈ g.traceLanguage right
    rw [hequivalent]
  · intro happrox
    apply Set.ext
    intro word
    change g.IsTrace left word ↔ g.IsTrace right word
    exact (traceApprox_iff_sameTracesThrough g word.length left right).mp
      (happrox word.length) word (by simp)

public theorem not_traceEquivalent_iff_exists_failedApprox
    (g : EncodedFirstOrderGrammar Action) (left right : RegularTerm) :
    ¬g.TraceEquivalent left right ↔
      ∃ n, g.traceApproxCode n left right = false := by
  rw [traceEquivalent_iff_forall_traceApprox]
  push_neg
  apply exists_congr
  intro n
  rw [← Bool.not_eq_true, traceApproxCode_eq_true_iff]

end EncodedFirstOrderGrammar

end DCFEquivalence
