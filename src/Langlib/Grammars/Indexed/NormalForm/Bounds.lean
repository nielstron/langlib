module

public import Langlib.Grammars.Indexed.Definition
public import Mathlib.Data.Set.Finite.List
import Mathlib.Tactic
@[expose]
public section

/-! # Basic bounds for indexed normal form

These lemmas record the local length behavior of indexed grammars in normal form. They are
intended as infrastructure for the finite normal-form simulation used in the indexed-to-CS
inclusion.
-/

variable {T : Type}

namespace IndexedGrammar

/-! ## Sentential-form measures -/

def ISym.isIndexed {g : IndexedGrammar T} : g.ISym → Bool
  | ISym.terminal _ => false
  | ISym.indexed _ _ => true

def ISym.isTerminal {g : IndexedGrammar T} : g.ISym → Bool
  | ISym.terminal _ => true
  | ISym.indexed _ _ => false

def ISym.stackHeight {g : IndexedGrammar T} : g.ISym → ℕ
  | ISym.terminal _ => 0
  | ISym.indexed _ σ => σ.length

def sententialNonterminalCount {g : IndexedGrammar T} (w : List g.ISym) : ℕ :=
  w.countP ISym.isIndexed

def sententialTerminalCount {g : IndexedGrammar T} (w : List g.ISym) : ℕ :=
  w.countP ISym.isTerminal

def sententialStackHeight {g : IndexedGrammar T} (w : List g.ISym) : ℕ :=
  (w.map ISym.stackHeight).sum

def sententialMaxStackHeight {g : IndexedGrammar T} : List g.ISym → ℕ
  | [] => 0
  | s :: w => max s.stackHeight (sententialMaxStackHeight w)

@[simp] theorem ISym.isIndexed_terminal {g : IndexedGrammar T} (a : T) :
    ISym.isIndexed (g := g) (ISym.terminal a) = false := rfl

@[simp] theorem ISym.isIndexed_indexed {g : IndexedGrammar T} (A : g.nt)
    (σ : List g.flag) :
    ISym.isIndexed (g := g) (ISym.indexed A σ) = true := rfl

@[simp] theorem ISym.isTerminal_terminal {g : IndexedGrammar T} (a : T) :
    ISym.isTerminal (g := g) (ISym.terminal a) = true := rfl

@[simp] theorem ISym.isTerminal_indexed {g : IndexedGrammar T} (A : g.nt)
    (σ : List g.flag) :
    ISym.isTerminal (g := g) (ISym.indexed A σ) = false := rfl

@[simp] theorem ISym.stackHeight_terminal {g : IndexedGrammar T} (a : T) :
    ISym.stackHeight (g := g) (ISym.terminal a) = 0 := rfl

@[simp] theorem ISym.stackHeight_indexed {g : IndexedGrammar T} (A : g.nt)
    (σ : List g.flag) :
    ISym.stackHeight (g := g) (ISym.indexed A σ) = σ.length := rfl

@[simp] theorem sententialNonterminalCount_nil {g : IndexedGrammar T} :
    sententialNonterminalCount ([] : List g.ISym) = 0 := rfl

@[simp] theorem sententialNonterminalCount_append {g : IndexedGrammar T}
    (u v : List g.ISym) :
    sententialNonterminalCount (u ++ v) =
      sententialNonterminalCount u + sententialNonterminalCount v := by
  simp [sententialNonterminalCount, List.countP_append]

@[simp] theorem sententialNonterminalCount_terminal {g : IndexedGrammar T} (a : T) :
    sententialNonterminalCount ([ISym.terminal a] : List g.ISym) = 0 := by
  simp [sententialNonterminalCount]

@[simp] theorem sententialNonterminalCount_indexed {g : IndexedGrammar T} (A : g.nt)
    (σ : List g.flag) :
    sententialNonterminalCount ([ISym.indexed A σ] : List g.ISym) = 1 := by
  simp [sententialNonterminalCount]

@[simp] theorem sententialNonterminalCount_cons_terminal {g : IndexedGrammar T}
    (a : T) (w : List g.ISym) :
    sententialNonterminalCount (ISym.terminal a :: w) =
      sententialNonterminalCount w := by
  simp [sententialNonterminalCount]

@[simp] theorem sententialNonterminalCount_cons_indexed {g : IndexedGrammar T}
    (A : g.nt) (σ : List g.flag) (w : List g.ISym) :
    sententialNonterminalCount (ISym.indexed A σ :: w) =
      sententialNonterminalCount w + 1 := by
  simp [sententialNonterminalCount]

@[simp] theorem sententialNonterminalCount_map_terminal {g : IndexedGrammar T}
    (w : List T) :
    sententialNonterminalCount
        (w.map fun a => (ISym.terminal a : g.ISym)) = 0 := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      simpa using ih

theorem sententialNonterminalCount_le_length {g : IndexedGrammar T}
    (w : List g.ISym) :
    sententialNonterminalCount w ≤ w.length := by
  exact List.countP_le_length

@[simp] theorem sententialTerminalCount_nil {g : IndexedGrammar T} :
    sententialTerminalCount ([] : List g.ISym) = 0 := rfl

@[simp] theorem sententialTerminalCount_append {g : IndexedGrammar T}
    (u v : List g.ISym) :
    sententialTerminalCount (u ++ v) =
      sententialTerminalCount u + sententialTerminalCount v := by
  simp [sententialTerminalCount, List.countP_append]

@[simp] theorem sententialTerminalCount_terminal {g : IndexedGrammar T} (a : T) :
    sententialTerminalCount ([ISym.terminal a] : List g.ISym) = 1 := by
  simp [sententialTerminalCount]

@[simp] theorem sententialTerminalCount_indexed {g : IndexedGrammar T} (A : g.nt)
    (σ : List g.flag) :
    sententialTerminalCount ([ISym.indexed A σ] : List g.ISym) = 0 := by
  simp [sententialTerminalCount]

@[simp] theorem sententialTerminalCount_cons_terminal {g : IndexedGrammar T}
    (a : T) (w : List g.ISym) :
    sententialTerminalCount (ISym.terminal a :: w) =
      sententialTerminalCount w + 1 := by
  simp [sententialTerminalCount]

@[simp] theorem sententialTerminalCount_cons_indexed {g : IndexedGrammar T}
    (A : g.nt) (σ : List g.flag) (w : List g.ISym) :
    sententialTerminalCount (ISym.indexed A σ :: w) =
      sententialTerminalCount w := by
  simp [sententialTerminalCount]

@[simp] theorem sententialTerminalCount_map_terminal {g : IndexedGrammar T}
    (w : List T) :
    sententialTerminalCount
        (w.map fun a => (ISym.terminal a : g.ISym)) = w.length := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      simp [ih]

theorem sententialTerminalCount_le_length {g : IndexedGrammar T}
    (w : List g.ISym) :
    sententialTerminalCount w ≤ w.length := by
  exact List.countP_le_length

theorem sententialTerminalCount_add_nonterminalCount {g : IndexedGrammar T}
    (w : List g.ISym) :
    sententialTerminalCount w + sententialNonterminalCount w = w.length := by
  induction w with
  | nil => simp
  | cons s w ih =>
      cases s <;> simp [sententialTerminalCount, sententialNonterminalCount] at ih ⊢ <;> omega

@[simp] theorem sententialStackHeight_nil {g : IndexedGrammar T} :
    sententialStackHeight ([] : List g.ISym) = 0 := rfl

@[simp] theorem sententialStackHeight_append {g : IndexedGrammar T}
    (u v : List g.ISym) :
    sententialStackHeight (u ++ v) =
      sententialStackHeight u + sententialStackHeight v := by
  simp [sententialStackHeight, List.map_append, List.sum_append]

@[simp] theorem sententialStackHeight_terminal {g : IndexedGrammar T} (a : T) :
    sententialStackHeight ([ISym.terminal a] : List g.ISym) = 0 := by
  simp [sententialStackHeight]

@[simp] theorem sententialStackHeight_indexed {g : IndexedGrammar T} (A : g.nt)
    (σ : List g.flag) :
    sententialStackHeight ([ISym.indexed A σ] : List g.ISym) = σ.length := by
  simp [sententialStackHeight]

@[simp] theorem sententialStackHeight_cons_terminal {g : IndexedGrammar T}
    (a : T) (w : List g.ISym) :
    sententialStackHeight (ISym.terminal a :: w) =
      sententialStackHeight w := by
  simp [sententialStackHeight]

@[simp] theorem sententialStackHeight_cons_indexed {g : IndexedGrammar T}
    (A : g.nt) (σ : List g.flag) (w : List g.ISym) :
    sententialStackHeight (ISym.indexed A σ :: w) =
      σ.length + sententialStackHeight w := by
  simp [sententialStackHeight]

@[simp] theorem sententialStackHeight_map_terminal {g : IndexedGrammar T}
    (w : List T) :
    sententialStackHeight
        (w.map fun a => (ISym.terminal a : g.ISym)) = 0 := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      simpa using ih

@[simp] theorem sententialMaxStackHeight_nil {g : IndexedGrammar T} :
    sententialMaxStackHeight ([] : List g.ISym) = 0 := rfl

@[simp] theorem sententialMaxStackHeight_cons {g : IndexedGrammar T}
    (s : g.ISym) (w : List g.ISym) :
    sententialMaxStackHeight (s :: w) =
      max s.stackHeight (sententialMaxStackHeight w) := rfl

@[simp] theorem sententialMaxStackHeight_append {g : IndexedGrammar T}
    (u v : List g.ISym) :
    sententialMaxStackHeight (u ++ v) =
      max (sententialMaxStackHeight u) (sententialMaxStackHeight v) := by
  induction u with
  | nil => simp
  | cons s u ih =>
      simp [ih, Nat.max_assoc, Nat.max_comm]

@[simp] theorem sententialMaxStackHeight_terminal {g : IndexedGrammar T} (a : T) :
    sententialMaxStackHeight ([ISym.terminal a] : List g.ISym) = 0 := by
  simp

@[simp] theorem sententialMaxStackHeight_indexed {g : IndexedGrammar T} (A : g.nt)
    (σ : List g.flag) :
    sententialMaxStackHeight ([ISym.indexed A σ] : List g.ISym) = σ.length := by
  simp

@[simp] theorem sententialMaxStackHeight_cons_terminal {g : IndexedGrammar T}
    (a : T) (w : List g.ISym) :
    sententialMaxStackHeight (ISym.terminal a :: w) =
      sententialMaxStackHeight w := by
  simp

@[simp] theorem sententialMaxStackHeight_cons_indexed {g : IndexedGrammar T}
    (A : g.nt) (σ : List g.flag) (w : List g.ISym) :
    sententialMaxStackHeight (ISym.indexed A σ :: w) =
      max σ.length (sententialMaxStackHeight w) := by
  rfl

@[simp] theorem sententialMaxStackHeight_map_terminal {g : IndexedGrammar T}
    (w : List T) :
    sententialMaxStackHeight
        (w.map fun a => (ISym.terminal a : g.ISym)) = 0 := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      simpa using ih

theorem stackHeight_le_sententialMaxStackHeight_of_mem {g : IndexedGrammar T}
    {s : g.ISym} {w : List g.ISym} (hs : s ∈ w) :
    s.stackHeight ≤ sententialMaxStackHeight w := by
  induction w with
  | nil => simp at hs
  | cons x w ih =>
      simp only [List.mem_cons] at hs
      rcases hs with rfl | hs
      · simp
      · exact le_trans (ih hs) (by simp)

/-! ## Stack-prefix projections -/

def ISym.truncateStack {g : IndexedGrammar T} (k : ℕ) : g.ISym → g.ISym
  | ISym.terminal a => ISym.terminal a
  | ISym.indexed A σ => ISym.indexed A (σ.take k)

def truncateStacks {g : IndexedGrammar T} (k : ℕ) (w : List g.ISym) : List g.ISym :=
  w.map (ISym.truncateStack k)

@[simp] theorem ISym.truncateStack_terminal {g : IndexedGrammar T} (k : ℕ) (a : T) :
    ISym.truncateStack (g := g) k (ISym.terminal a) = ISym.terminal a := rfl

@[simp] theorem ISym.truncateStack_indexed {g : IndexedGrammar T} (k : ℕ)
    (A : g.nt) (σ : List g.flag) :
    ISym.truncateStack (g := g) k (ISym.indexed A σ) =
      ISym.indexed A (σ.take k) := rfl

@[simp] theorem truncateStacks_nil {g : IndexedGrammar T} (k : ℕ) :
    truncateStacks (g := g) k [] = [] := rfl

@[simp] theorem truncateStacks_cons {g : IndexedGrammar T} (k : ℕ)
    (s : g.ISym) (w : List g.ISym) :
    truncateStacks k (s :: w) = ISym.truncateStack k s :: truncateStacks k w := rfl

@[simp] theorem truncateStacks_append {g : IndexedGrammar T} (k : ℕ)
    (u v : List g.ISym) :
    truncateStacks k (u ++ v) = truncateStacks k u ++ truncateStacks k v := by
  simp [truncateStacks, List.map_append]

@[simp] theorem truncateStacks_length {g : IndexedGrammar T} (k : ℕ)
    (w : List g.ISym) :
    (truncateStacks k w).length = w.length := by
  simp [truncateStacks]

@[simp] theorem ISym.isIndexed_truncateStack {g : IndexedGrammar T} (k : ℕ)
    (s : g.ISym) :
    (ISym.truncateStack k s).isIndexed = s.isIndexed := by
  cases s <;> rfl

@[simp] theorem ISym.isTerminal_truncateStack {g : IndexedGrammar T} (k : ℕ)
    (s : g.ISym) :
    (ISym.truncateStack k s).isTerminal = s.isTerminal := by
  cases s <;> rfl

@[simp] theorem sententialNonterminalCount_truncateStacks {g : IndexedGrammar T}
    (k : ℕ) (w : List g.ISym) :
    sententialNonterminalCount (truncateStacks k w) =
      sententialNonterminalCount w := by
  induction w with
  | nil => rfl
  | cons s w ih =>
      cases s <;> simpa [truncateStacks, sententialNonterminalCount] using ih

@[simp] theorem sententialTerminalCount_truncateStacks {g : IndexedGrammar T}
    (k : ℕ) (w : List g.ISym) :
    sententialTerminalCount (truncateStacks k w) =
      sententialTerminalCount w := by
  induction w with
  | nil => rfl
  | cons s w ih =>
      cases s <;> simpa [truncateStacks, sententialTerminalCount] using ih

theorem ISym.stackHeight_truncateStack_le_self {g : IndexedGrammar T} (k : ℕ)
    (s : g.ISym) :
    (ISym.truncateStack k s).stackHeight ≤ s.stackHeight := by
  cases s with
  | terminal a => simp
  | indexed A σ => simp [ISym.truncateStack]

theorem ISym.stackHeight_truncateStack_le {g : IndexedGrammar T} (k : ℕ)
    (s : g.ISym) :
    (ISym.truncateStack k s).stackHeight ≤ k := by
  cases s with
  | terminal a => simp
  | indexed A σ => simp [ISym.truncateStack]

theorem ISym.truncateStack_eq_self_of_stackHeight_le {g : IndexedGrammar T}
    {k : ℕ} {s : g.ISym} (h : s.stackHeight ≤ k) :
    ISym.truncateStack k s = s := by
  cases s with
  | terminal a => rfl
  | indexed A σ =>
      simp [ISym.truncateStack, (List.take_eq_self_iff σ).mpr h]

theorem sententialMaxStackHeight_truncateStacks_le_self {g : IndexedGrammar T}
    (k : ℕ) (w : List g.ISym) :
    sententialMaxStackHeight (truncateStacks k w) ≤ sententialMaxStackHeight w := by
  induction w with
  | nil => simp
  | cons s w ih =>
      exact max_le_max (ISym.stackHeight_truncateStack_le_self k s) ih

theorem sententialMaxStackHeight_truncateStacks_le {g : IndexedGrammar T}
    (k : ℕ) (w : List g.ISym) :
    sententialMaxStackHeight (truncateStacks k w) ≤ k := by
  induction w with
  | nil => simp
  | cons s w ih =>
      exact Nat.max_le.mpr ⟨ISym.stackHeight_truncateStack_le k s, ih⟩

theorem truncateStacks_eq_self_of_sententialMaxStackHeight_le {g : IndexedGrammar T}
    {k : ℕ} {w : List g.ISym} (h : sententialMaxStackHeight w ≤ k) :
    truncateStacks k w = w := by
  induction w with
  | nil => rfl
  | cons s w ih =>
      have hs : s.stackHeight ≤ k :=
        le_trans (Nat.le_max_left s.stackHeight (sententialMaxStackHeight w)) h
      have hw : sententialMaxStackHeight w ≤ k :=
        le_trans (Nat.le_max_right s.stackHeight (sententialMaxStackHeight w)) h
      rw [truncateStacks_cons, ISym.truncateStack_eq_self_of_stackHeight_le hs, ih hw]

/-! ## Finite bounded sentential forms -/

/-- The finite set of symbols whose attached stack has height at most `n`. -/
def stackBoundedSymbols (g : IndexedGrammar T) (n : ℕ) : Set g.ISym :=
  {s | s.stackHeight ≤ n}

theorem stackBoundedSymbols_finite (g : IndexedGrammar T)
    [Fintype T] [Fintype g.nt] [Fintype g.flag] (n : ℕ) :
    (stackBoundedSymbols g n).Finite := by
  classical
  have hterm :
      (Set.range (fun a : T => ISym.terminal (g := g) a) : Set g.ISym).Finite :=
    Set.finite_range _
  have hstacks : ({σ : List g.flag | σ.length ≤ n} : Set (List g.flag)).Finite :=
    List.finite_length_le g.flag n
  have hindexed :
      (⋃ A : g.nt,
        (fun σ : List g.flag => ISym.indexed (g := g) A σ) ''
          ({σ : List g.flag | σ.length ≤ n} : Set (List g.flag))).Finite := by
    apply Set.finite_iUnion
    intro A
    exact hstacks.image fun σ => ISym.indexed (g := g) A σ
  have hcover :
      ((Set.range (fun a : T => ISym.terminal (g := g) a) : Set g.ISym) ∪
        ⋃ A : g.nt,
          (fun σ : List g.flag => ISym.indexed (g := g) A σ) ''
            ({σ : List g.flag | σ.length ≤ n} : Set (List g.flag))).Finite := by
    rw [Set.finite_union]
    exact ⟨hterm, hindexed⟩
  apply hcover.subset
  intro s hs
  cases s with
  | terminal a =>
      exact Or.inl ⟨a, rfl⟩
  | indexed A σ =>
      right
      refine Set.mem_iUnion.mpr ⟨A, ?_⟩
      have hσ : σ.length ≤ n := by
        simpa [stackBoundedSymbols] using hs
      exact ⟨σ, hσ, rfl⟩

/-! ## Finite surface forms -/

/-- A visible indexed-grammar symbol whose stack has been truncated to height at most `k`. -/
def SurfaceSymbol (g : IndexedGrammar T) (k : ℕ) : Type :=
  {s : g.ISym // s.stackHeight ≤ k}

/-- A sentential form over the finite visible stack-prefix alphabet. -/
def SurfaceForm (g : IndexedGrammar T) (k : ℕ) : Type :=
  List (SurfaceSymbol g k)

noncomputable instance SurfaceSymbol.instFintype (g : IndexedGrammar T)
    [Fintype T] [Fintype g.nt] [Fintype g.flag] (k : ℕ) :
    Fintype (SurfaceSymbol g k) :=
  (stackBoundedSymbols_finite g k).fintype

noncomputable instance SurfaceSymbol.instDecidableEq (g : IndexedGrammar T) (k : ℕ) :
    DecidableEq (SurfaceSymbol g k) :=
  Classical.decEq _

def surfaceOfTruncatedSymbol {g : IndexedGrammar T} (k : ℕ)
    (s : g.ISym) : SurfaceSymbol g k :=
  ⟨ISym.truncateStack k s, ISym.stackHeight_truncateStack_le k s⟩

def surfaceOfTruncatedForm {g : IndexedGrammar T} (k : ℕ)
    (w : List g.ISym) : SurfaceForm g k :=
  w.map (surfaceOfTruncatedSymbol k)

def eraseSurfaceSymbol {g : IndexedGrammar T} {k : ℕ}
    (s : SurfaceSymbol g k) : g.ISym :=
  s.1

def eraseSurfaceForm {g : IndexedGrammar T} {k : ℕ}
    (w : SurfaceForm g k) : List g.ISym :=
  w.map eraseSurfaceSymbol

@[simp] theorem surfaceOfTruncatedForm_nil {g : IndexedGrammar T} (k : ℕ) :
    surfaceOfTruncatedForm (g := g) k [] = [] := rfl

@[simp] theorem surfaceOfTruncatedForm_cons {g : IndexedGrammar T} (k : ℕ)
    (s : g.ISym) (w : List g.ISym) :
    surfaceOfTruncatedForm k (s :: w) =
      surfaceOfTruncatedSymbol k s :: surfaceOfTruncatedForm k w := rfl

@[simp] theorem surfaceOfTruncatedForm_length {g : IndexedGrammar T} (k : ℕ)
    (w : List g.ISym) :
    (surfaceOfTruncatedForm k w).length = w.length := by
  simp [surfaceOfTruncatedForm]

@[simp] theorem eraseSurfaceForm_nil {g : IndexedGrammar T} {k : ℕ} :
    eraseSurfaceForm ([] : SurfaceForm g k) = [] := rfl

@[simp] theorem eraseSurfaceForm_cons {g : IndexedGrammar T} {k : ℕ}
    (s : SurfaceSymbol g k) (w : SurfaceForm g k) :
    eraseSurfaceForm (s :: w) = s.1 :: eraseSurfaceForm w := rfl

@[simp] theorem eraseSurfaceForm_length {g : IndexedGrammar T} {k : ℕ}
    (w : SurfaceForm g k) :
    (eraseSurfaceForm w).length = w.length := by
  simp [eraseSurfaceForm]

@[simp] theorem eraseSurfaceSymbol_surfaceOfTruncatedSymbol {g : IndexedGrammar T}
    (k : ℕ) (s : g.ISym) :
    eraseSurfaceSymbol (surfaceOfTruncatedSymbol k s) = ISym.truncateStack k s := rfl

@[simp] theorem eraseSurfaceForm_surfaceOfTruncatedForm {g : IndexedGrammar T}
    (k : ℕ) (w : List g.ISym) :
    eraseSurfaceForm (surfaceOfTruncatedForm k w) = truncateStacks k w := by
  induction w with
  | nil => rfl
  | cons s w ih =>
      simp [surfaceOfTruncatedForm, eraseSurfaceForm, truncateStacks]

theorem eraseSurfaceForm_surfaceOfTruncatedForm_eq_self_of_sententialMaxStackHeight_le
    {g : IndexedGrammar T} {k : ℕ} {w : List g.ISym}
    (h : sententialMaxStackHeight w ≤ k) :
    eraseSurfaceForm (surfaceOfTruncatedForm k w) = w := by
  rw [eraseSurfaceForm_surfaceOfTruncatedForm,
    truncateStacks_eq_self_of_sententialMaxStackHeight_le h]

theorem eraseSurfaceForm_maxStackHeight_le {g : IndexedGrammar T} {k : ℕ}
    (w : SurfaceForm g k) :
    sententialMaxStackHeight (eraseSurfaceForm w) ≤ k := by
  induction w with
  | nil => simp [eraseSurfaceForm]
  | cons s w ih =>
      exact Nat.max_le.mpr ⟨s.2, ih⟩

/-- Surface forms of bounded length. Their alphabet is already stack-bounded by construction. -/
def boundedSurfaceForms (g : IndexedGrammar T) (lengthBound stackBound : ℕ) :
    Set (SurfaceForm g stackBound) :=
  {w | w.length ≤ lengthBound}

theorem boundedSurfaceForms_finite (g : IndexedGrammar T)
    [Fintype T] [Fintype g.nt] [Fintype g.flag]
    (lengthBound stackBound : ℕ) :
    (boundedSurfaceForms g lengthBound stackBound).Finite := by
  dsimp [boundedSurfaceForms]
  exact List.finite_length_le (SurfaceSymbol g stackBound) lengthBound

theorem surfaceOfTruncatedForm_mem_boundedSurfaceForms {g : IndexedGrammar T}
    {lengthBound stackBound : ℕ} {w : List g.ISym}
    (hlen : w.length ≤ lengthBound) :
    surfaceOfTruncatedForm stackBound w ∈
      boundedSurfaceForms g lengthBound stackBound := by
  simpa [boundedSurfaceForms] using hlen

/-- Sentential forms whose length and maximum stack height are both bounded. -/
def boundedSententialForms (g : IndexedGrammar T) (lengthBound stackBound : ℕ) :
    Set (List g.ISym) :=
  {w | w.length ≤ lengthBound ∧ sententialMaxStackHeight w ≤ stackBound}

theorem eraseSurfaceForm_mem_boundedSententialForms {g : IndexedGrammar T}
    {lengthBound stackBound : ℕ} {w : SurfaceForm g stackBound}
    (hw : w ∈ boundedSurfaceForms g lengthBound stackBound) :
    eraseSurfaceForm w ∈ boundedSententialForms g lengthBound stackBound := by
  exact ⟨by simpa [boundedSurfaceForms] using hw,
    eraseSurfaceForm_maxStackHeight_le w⟩

theorem truncateStacks_mem_boundedSententialForms {g : IndexedGrammar T}
    {lengthBound stackBound : ℕ} {w : List g.ISym}
    (hlen : w.length ≤ lengthBound) :
    truncateStacks stackBound w ∈ boundedSententialForms g lengthBound stackBound := by
  exact ⟨by simpa using hlen, sententialMaxStackHeight_truncateStacks_le stackBound w⟩

def surfaceTrace {g : IndexedGrammar T} (stackBound : ℕ)
    (trace : List (List g.ISym)) : List (SurfaceForm g stackBound) :=
  trace.map (surfaceOfTruncatedForm stackBound)

@[simp] theorem surfaceTrace_nil {g : IndexedGrammar T} (stackBound : ℕ) :
    surfaceTrace (g := g) stackBound [] = [] := rfl

@[simp] theorem surfaceTrace_cons {g : IndexedGrammar T} (stackBound : ℕ)
    (w : List g.ISym) (trace : List (List g.ISym)) :
    surfaceTrace stackBound (w :: trace) =
      surfaceOfTruncatedForm stackBound w :: surfaceTrace stackBound trace := rfl

@[simp] theorem surfaceTrace_length {g : IndexedGrammar T} (stackBound : ℕ)
    (trace : List (List g.ISym)) :
    (surfaceTrace stackBound trace).length = trace.length := by
  simp [surfaceTrace]

theorem surfaceTrace_get {g : IndexedGrammar T} (stackBound : ℕ)
    (trace : List (List g.ISym)) {i : ℕ} (hi : i < trace.length) :
    (surfaceTrace stackBound trace).get ⟨i, by simpa using hi⟩ =
      surfaceOfTruncatedForm stackBound (trace.get ⟨i, hi⟩) := by
  simp [surfaceTrace]

theorem boundedSententialForms_finite (g : IndexedGrammar T)
    [Fintype T] [Fintype g.nt] [Fintype g.flag]
    (lengthBound stackBound : ℕ) :
    (boundedSententialForms g lengthBound stackBound).Finite := by
  classical
  let B := {s : g.ISym // s.stackHeight ≤ stackBound}
  haveI : Fintype B := (stackBoundedSymbols_finite g stackBound).fintype
  let erase : List B → List g.ISym := fun w => w.map Subtype.val
  let boundedLists : Set (List B) := {w | w.length ≤ lengthBound}
  have hboundedLists : boundedLists.Finite := by
    dsimp [boundedLists]
    exact List.finite_length_le B lengthBound
  have himage : (erase '' boundedLists).Finite := hboundedLists.image erase
  apply himage.subset
  intro w hw
  rcases hw with ⟨hlen, hheight⟩
  let lift : List B :=
    w.attach.map fun s =>
      ⟨s.1, le_trans (stackHeight_le_sententialMaxStackHeight_of_mem s.2) hheight⟩
  have hlift_len : lift.length ≤ lengthBound := by
    simpa [lift] using hlen
  have herase : erase lift = w := by
    dsimp [erase, lift]
    rw [List.map_map]
    simp [Function.comp_def]
  exact ⟨lift, hlift_len, herase⟩

/-! ## Counted derivations -/

/-- `DerivesIn g n w₁ w₂` means that `w₁` derives `w₂` in exactly `n` indexed-grammar
steps. This is a counted counterpart to `Derives`, useful when extracting minimal accepting
derivations. -/
def DerivesIn (g : IndexedGrammar T) : ℕ → List g.ISym → List g.ISym → Prop
  | 0, w₁, w₂ => w₁ = w₂
  | n + 1, w₁, w₂ => ∃ w, DerivesIn g n w₁ w ∧ g.Transforms w w₂

@[simp] theorem derivesIn_zero {g : IndexedGrammar T} {w₁ w₂ : List g.ISym} :
    g.DerivesIn 0 w₁ w₂ ↔ w₁ = w₂ :=
  Iff.rfl

@[simp] theorem derivesIn_succ {g : IndexedGrammar T} {n : ℕ}
    {w₁ w₂ : List g.ISym} :
    g.DerivesIn (n + 1) w₁ w₂ ↔
      ∃ w, g.DerivesIn n w₁ w ∧ g.Transforms w w₂ :=
  Iff.rfl

theorem derivesIn_refl {g : IndexedGrammar T} (w : List g.ISym) :
    g.DerivesIn 0 w w :=
  rfl

theorem derivesIn_one_of_transforms {g : IndexedGrammar T}
    {w₁ w₂ : List g.ISym} (h : g.Transforms w₁ w₂) :
    g.DerivesIn 1 w₁ w₂ :=
  ⟨w₁, rfl, h⟩

theorem derives_of_derivesIn {g : IndexedGrammar T} {n : ℕ}
    {w₁ w₂ : List g.ISym} (h : g.DerivesIn n w₁ w₂) :
    g.Derives w₁ w₂ := by
  induction n generalizing w₂ with
  | zero =>
      have hw : w₁ = w₂ := by simpa using h
      subst w₂
      exact g.deri_self w₁
  | succ n ih =>
      rcases h with ⟨w, hprev, hstep⟩
      exact (ih hprev).tail hstep

theorem exists_derivesIn_of_derives {g : IndexedGrammar T}
    {w₁ w₂ : List g.ISym} (h : g.Derives w₁ w₂) :
    ∃ n, g.DerivesIn n w₁ w₂ := by
  induction h with
  | refl =>
      exact ⟨0, rfl⟩
  | tail _ hstep ih =>
      rcases ih with ⟨n, hn⟩
      exact ⟨n + 1, ⟨_, hn, hstep⟩⟩

theorem derives_iff_exists_derivesIn {g : IndexedGrammar T}
    {w₁ w₂ : List g.ISym} :
    g.Derives w₁ w₂ ↔ ∃ n, g.DerivesIn n w₁ w₂ := by
  constructor
  · exact exists_derivesIn_of_derives
  · rintro ⟨n, h⟩
    exact derives_of_derivesIn h

/-- Any derivation has a propositionally least step count. This avoids requiring decidability
of one-step rewriting. -/
theorem exists_minimal_derivesIn_of_derives {g : IndexedGrammar T}
    {w₁ w₂ : List g.ISym} (h : g.Derives w₁ w₂) :
    ∃ n, g.DerivesIn n w₁ w₂ ∧
      ∀ m, g.DerivesIn m w₁ w₂ → n ≤ m := by
  obtain ⟨n, hmin⟩ :=
    exists_minimal_of_wellFoundedLT
      (P := fun n => g.DerivesIn n w₁ w₂)
      (exists_derivesIn_of_derives h)
  refine ⟨n, hmin.1, ?_⟩
  intro m hm
  rcases le_total m n with hmn | hnm
  · exact hmin.2 hm hmn
  · exact hnm

theorem derivesIn_trans {g : IndexedGrammar T} {m n : ℕ}
    {w₁ w₂ w₃ : List g.ISym}
    (h₁ : g.DerivesIn m w₁ w₂) (h₂ : g.DerivesIn n w₂ w₃) :
    g.DerivesIn (m + n) w₁ w₃ := by
  induction n generalizing w₃ with
  | zero =>
      have hw : w₂ = w₃ := by simpa using h₂
      subst w₃
      simpa using h₁
  | succ n ih =>
      rcases h₂ with ⟨w, hprev, hstep⟩
      exact ⟨w, by simpa [Nat.add_assoc] using ih hprev, hstep⟩

/-! ## Derivation traces -/

/-- A concrete list of successive sentential forms, each adjacent pair related by one
indexed-grammar step. Length information is carried by the theorems using the trace. -/
def IsDerivationTrace (g : IndexedGrammar T) : List (List g.ISym) → Prop
  | [] => True
  | [_] => True
  | w₁ :: w₂ :: rest => g.Transforms w₁ w₂ ∧ IsDerivationTrace g (w₂ :: rest)

@[simp] theorem isDerivationTrace_nil {g : IndexedGrammar T} :
    IsDerivationTrace g [] := by
  simp [IsDerivationTrace]

@[simp] theorem isDerivationTrace_singleton {g : IndexedGrammar T}
    (w : List g.ISym) :
    IsDerivationTrace g [w] := by
  simp [IsDerivationTrace]

@[simp] theorem isDerivationTrace_cons_cons {g : IndexedGrammar T}
    (w₁ w₂ : List g.ISym) (rest : List (List g.ISym)) :
    IsDerivationTrace g (w₁ :: w₂ :: rest) ↔
      g.Transforms w₁ w₂ ∧ IsDerivationTrace g (w₂ :: rest) := by
  rfl

theorem isDerivationTrace_append_step {g : IndexedGrammar T}
    {trace : List (List g.ISym)} {w w' : List g.ISym}
    (htrace : IsDerivationTrace g trace)
    (hlast : trace.getLast? = some w)
    (hstep : g.Transforms w w') :
    IsDerivationTrace g (trace ++ [w']) := by
  induction trace with
  | nil =>
      simp at hlast
  | cons a rest ih =>
      cases rest with
      | nil =>
          simp at hlast
          subst a
          simp [hstep]
      | cons b rest =>
          simp only [isDerivationTrace_cons_cons] at htrace ⊢
          constructor
          · exact htrace.1
          · exact ih htrace.2 (by simpa using hlast)

theorem exists_isDerivationTrace_of_derivesIn {g : IndexedGrammar T} {n : ℕ}
    {w₁ w₂ : List g.ISym} (h : g.DerivesIn n w₁ w₂) :
    ∃ trace,
      IsDerivationTrace g trace ∧ trace.length = n + 1 ∧
        trace.head? = some w₁ ∧ trace.getLast? = some w₂ := by
  induction n generalizing w₂ with
  | zero =>
      have hw : w₁ = w₂ := by simpa using h
      subst w₂
      exact ⟨[w₁], by simp⟩
  | succ n ih =>
      rcases h with ⟨w, hprev, hstep⟩
      rcases ih hprev with ⟨trace, htrace, hlen, hhead, hlast⟩
      refine ⟨trace ++ [w₂], ?_, ?_, ?_, ?_⟩
      · exact isDerivationTrace_append_step htrace hlast hstep
      · simp [hlen]
      · rw [List.head?_append]
        simp [hhead]
      · simp

theorem derivesIn_of_isDerivationTrace {g : IndexedGrammar T} {n : ℕ}
    {trace : List (List g.ISym)} {w₁ w₂ : List g.ISym}
    (htrace : IsDerivationTrace g trace)
    (hlen : trace.length = n + 1)
    (hhead : trace.head? = some w₁)
    (hlast : trace.getLast? = some w₂) :
    g.DerivesIn n w₁ w₂ := by
  induction n generalizing trace w₁ w₂ with
  | zero =>
      cases trace with
      | nil => simp at hlen
      | cons a rest =>
          cases rest with
          | nil =>
              simp at hhead hlast
              subst a
              simpa using hlast
          | cons b rest =>
              simp at hlen
  | succ n ih =>
      cases trace with
      | nil => simp at hlen
      | cons a rest =>
          cases rest with
          | nil => simp at hlen
          | cons b rest =>
              simp only [isDerivationTrace_cons_cons] at htrace
              have ha : a = w₁ := by simpa using hhead
              subst a
              have hlen_tail : (b :: rest).length = n + 1 := by
                simpa using hlen
              have hlast_tail : (b :: rest).getLast? = some w₂ := by
                simpa using hlast
              have htail : g.DerivesIn n b w₂ :=
                ih htrace.2 hlen_tail (by simp) hlast_tail
              have hone : g.DerivesIn 1 w₁ b :=
                derivesIn_one_of_transforms htrace.1
              simpa [Nat.add_comm] using derivesIn_trans hone htail

theorem derivesIn_iff_exists_isDerivationTrace {g : IndexedGrammar T} {n : ℕ}
    {w₁ w₂ : List g.ISym} :
    g.DerivesIn n w₁ w₂ ↔
      ∃ trace,
        IsDerivationTrace g trace ∧ trace.length = n + 1 ∧
          trace.head? = some w₁ ∧ trace.getLast? = some w₂ := by
  constructor
  · exact exists_isDerivationTrace_of_derivesIn
  · rintro ⟨trace, htrace, hlen, hhead, hlast⟩
    exact derivesIn_of_isDerivationTrace htrace hlen hhead hlast

/-- Adjacent entries in a derivation trace are related by one grammar step. -/
theorem isDerivationTrace_get_transform {g : IndexedGrammar T}
    {trace : List (List g.ISym)}
    (htrace : IsDerivationTrace g trace) {i : ℕ}
    (hi : i + 1 < trace.length) :
    g.Transforms
      (trace.get ⟨i, by omega⟩)
      (trace.get ⟨i + 1, hi⟩) := by
  induction trace generalizing i with
  | nil =>
      simp at hi
  | cons a rest ih =>
      cases rest with
      | nil =>
          simp at hi
      | cons b rest =>
          simp only [isDerivationTrace_cons_cons] at htrace
          cases i with
          | zero =>
              simpa using htrace.1
          | succ i =>
              have hi_tail : i + 1 < (b :: rest).length := by
                simpa using hi
              simpa using ih htrace.2 hi_tail

theorem isDerivationTrace_derivesIn_from_head_get {g : IndexedGrammar T}
    {trace : List (List g.ISym)} {w₁ : List g.ISym}
    (htrace : IsDerivationTrace g trace)
    (hhead : trace.head? = some w₁) {i : ℕ}
    (hi : i < trace.length) :
    g.DerivesIn i w₁ (trace.get ⟨i, hi⟩) := by
  induction i with
  | zero =>
      cases trace with
      | nil => simp at hi
      | cons a rest =>
          simp at hhead
          subst a
          rfl
  | succ i ih =>
      have hi_prev : i < trace.length := by omega
      have hprev := ih hi_prev
      have hstep := isDerivationTrace_get_transform htrace (i := i) hi
      exact ⟨trace.get ⟨i, hi_prev⟩, hprev, hstep⟩

theorem isDerivationTrace_derivesIn_get_to_last {g : IndexedGrammar T}
    {trace : List (List g.ISym)} {w₂ : List g.ISym}
    (htrace : IsDerivationTrace g trace)
    (hlast : trace.getLast? = some w₂) {i : ℕ}
    (hi : i < trace.length) :
    g.DerivesIn (trace.length - 1 - i) (trace.get ⟨i, hi⟩) w₂ := by
  induction trace generalizing i with
  | nil =>
      simp at hi
  | cons a rest ih =>
      cases rest with
      | nil =>
          have hi0 : i = 0 := by simpa using hi
          subst i
          simp at hlast
          subst a
          rfl
      | cons b rest =>
          simp only [isDerivationTrace_cons_cons] at htrace
          cases i with
          | zero =>
              have htrace_full : IsDerivationTrace g (a :: b :: rest) := by
                simpa only [isDerivationTrace_cons_cons] using htrace
              exact derivesIn_of_isDerivationTrace htrace_full
                (by simp)
                (by simp)
                hlast
          | succ i =>
              have hi_tail : i < (b :: rest).length := by
                simpa using hi
              have htail := ih htrace.2 hlast hi_tail
              simpa using htail

/-- Split a counted derivation after `m` steps. -/
theorem derivesIn_split {g : IndexedGrammar T} {m n : ℕ}
    {w₁ w₃ : List g.ISym}
    (h : g.DerivesIn (m + n) w₁ w₃) :
    ∃ w₂, g.DerivesIn m w₁ w₂ ∧ g.DerivesIn n w₂ w₃ := by
  induction n generalizing w₃ with
  | zero =>
      exact ⟨w₃, by simpa using h, rfl⟩
  | succ n ih =>
      rcases (show g.DerivesIn ((m + n) + 1) w₁ w₃ by
        simpa [Nat.add_assoc] using h) with ⟨w, hprev, hstep⟩
      rcases ih hprev with ⟨w₂, hm, hn⟩
      exact ⟨w₂, hm, ⟨w, hn, hstep⟩⟩

/-- Split a counted derivation at any index `i ≤ n`. -/
theorem derivesIn_split_at {g : IndexedGrammar T} {n i : ℕ}
    {w₁ w₂ : List g.ISym} (hi : i ≤ n)
    (h : g.DerivesIn n w₁ w₂) :
    ∃ x, g.DerivesIn i w₁ x ∧ g.DerivesIn (n - i) x w₂ := by
  have h' : g.DerivesIn (i + (n - i)) w₁ w₂ := by
    simpa [Nat.add_sub_of_le hi] using h
  exact derivesIn_split (g := g) (m := i) (n := n - i) h'

/-- `x` is the sentential form seen at step `i` of an `n`-step derivation from `w₁` to
`w₂`. -/
def DerivesInIntermediate (g : IndexedGrammar T) (n : ℕ)
    (w₁ w₂ : List g.ISym) (i : ℕ) (x : List g.ISym) : Prop :=
  i ≤ n ∧ g.DerivesIn i w₁ x ∧ g.DerivesIn (n - i) x w₂

theorem exists_derivesInIntermediate {g : IndexedGrammar T} {n i : ℕ}
    {w₁ w₂ : List g.ISym} (hi : i ≤ n)
    (h : g.DerivesIn n w₁ w₂) :
    ∃ x, DerivesInIntermediate g n w₁ w₂ i x := by
  rcases derivesIn_split_at (g := g) hi h with ⟨x, hpre, hsuf⟩
  exact ⟨x, hi, hpre, hsuf⟩

/-- A shortest counted derivation cannot see the same intermediate sentential form at two
different step indices. -/
theorem minimal_derivesIn_intermediate_index_eq {g : IndexedGrammar T} {n : ℕ}
    {w₁ w₂ x : List g.ISym}
    (hmin : ∀ m, g.DerivesIn m w₁ w₂ → n ≤ m)
    {i j : ℕ}
    (hi : DerivesInIntermediate g n w₁ w₂ i x)
    (hj : DerivesInIntermediate g n w₁ w₂ j x) :
    i = j := by
  rcases hi with ⟨hin, hpre_i, hsuf_i⟩
  rcases hj with ⟨hjn, hpre_j, hsuf_j⟩
  rcases lt_trichotomy i j with hij | rfl | hji
  · have hshort : g.DerivesIn (i + (n - j)) w₁ w₂ :=
      derivesIn_trans hpre_i hsuf_j
    have hshort_lt : i + (n - j) < n := by omega
    exact False.elim ((not_lt_of_ge (hmin _ hshort)) hshort_lt)
  · rfl
  · have hshort : g.DerivesIn (j + (n - i)) w₁ w₂ :=
      derivesIn_trans hpre_j hsuf_i
    have hshort_lt : j + (n - i) < n := by omega
    exact False.elim ((not_lt_of_ge (hmin _ hshort)) hshort_lt)

theorem isDerivationTrace_get_intermediate {g : IndexedGrammar T}
    {trace : List (List g.ISym)} {n i : ℕ}
    {w₁ w₂ : List g.ISym}
    (htrace : IsDerivationTrace g trace)
    (hlen : trace.length = n + 1)
    (hhead : trace.head? = some w₁)
    (hlast : trace.getLast? = some w₂)
    (hi : i ≤ n) :
    DerivesInIntermediate g n w₁ w₂ i
      (trace.get ⟨i, by omega⟩) := by
  have hi_len : i < trace.length := by omega
  refine ⟨hi, ?_, ?_⟩
  · simpa using isDerivationTrace_derivesIn_from_head_get htrace hhead hi_len
  · have hsuf := isDerivationTrace_derivesIn_get_to_last htrace hlast hi_len
    simpa [hlen] using hsuf

theorem minimal_derivationTrace_nodup {g : IndexedGrammar T}
    {trace : List (List g.ISym)} {n : ℕ} {w₁ w₂ : List g.ISym}
    (htrace : IsDerivationTrace g trace)
    (hlen : trace.length = n + 1)
    (hhead : trace.head? = some w₁)
    (hlast : trace.getLast? = some w₂)
    (hmin : ∀ m, g.DerivesIn m w₁ w₂ → n ≤ m) :
    trace.Nodup := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_iff_get]
  intro i j hij hsame
  have hi_le : i.1 ≤ n := by
    have hi_len := i.2
    omega
  have hj_le : j.1 ≤ n := by
    have hj_len := j.2
    omega
  have hmid_i :=
    isDerivationTrace_get_intermediate (g := g) htrace hlen hhead hlast hi_le
  have hmid_j :
      DerivesInIntermediate g n w₁ w₂ j.1 (trace.get i) := by
    have hmid_j0 :=
      isDerivationTrace_get_intermediate (g := g) htrace hlen hhead hlast hj_le
    convert hmid_j0 using 1
  have hij_eq : i.1 = j.1 :=
    minimal_derivesIn_intermediate_index_eq (g := g) (n := n) hmin hmid_i hmid_j
  exact (ne_of_lt hij) (Fin.ext hij_eq)

/-- A duplicate-free list whose entries all lie in a finite set has length bounded by the
cardinality of that set. This formulation avoids requiring decidable equality on the ambient
type. -/
theorem List.Nodup.length_le_finite_set_card_of_get_mem {α : Type}
    {xs : List α} (hxs : xs.Nodup) (S : Set α) (hS : S.Finite)
    (hmem : ∀ i : Fin xs.length, xs.get i ∈ S) :
    xs.length ≤ (Set.Finite.toFinset hS).card := by
  classical
  haveI : Fintype S := hS.fintype
  let f : Fin xs.length → S := fun i => ⟨xs.get i, hmem i⟩
  have hf : Function.Injective f := by
    intro i j hij
    have hget : xs.get i = xs.get j := congrArg Subtype.val hij
    exact (List.Nodup.get_inj_iff hxs).mp hget
  have hcard := Fintype.card_le_of_injective f hf
  simpa [Set.Finite.card_toFinset hS] using hcard

theorem List.exists_get_eq_of_not_nodup {α : Type} {xs : List α}
    (hxs : ¬ xs.Nodup) :
    ∃ i j : Fin xs.length, i < j ∧ xs.get i = xs.get j := by
  classical
  have hnotinj : ¬ Function.Injective xs.get := by
    intro hinj
    exact hxs (List.nodup_iff_injective_get.mpr hinj)
  simp only [Function.Injective] at hnotinj
  push_neg at hnotinj
  rcases hnotinj with ⟨i, j, hget, hij⟩
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · exact ⟨i, j, hijlt, hget⟩
  · exact ⟨j, i, hjilt, hget.symm⟩

theorem List.exists_get_eq_of_finite_set_card_lt_length {α : Type}
    {xs : List α} (S : Set α) (hS : S.Finite)
    (hmem : ∀ i : Fin xs.length, xs.get i ∈ S)
    (hcard : (Set.Finite.toFinset hS).card < xs.length) :
    ∃ i j : Fin xs.length, i < j ∧ xs.get i = xs.get j := by
  apply List.exists_get_eq_of_not_nodup
  intro hnodup
  have hlen := List.Nodup.length_le_finite_set_card_of_get_mem hnodup S hS hmem
  exact (not_lt_of_ge hlen) hcard

/-- If all intermediates of a shortest `n`-step derivation lie in a finite set `S`, then
there are at most `|S|` step indices. -/
theorem minimal_derivesIn_steps_succ_le_card_of_intermediates_mem
    {g : IndexedGrammar T} {n : ℕ} {w₁ w₂ : List g.ISym}
    (h : g.DerivesIn n w₁ w₂)
    (hmin : ∀ m, g.DerivesIn m w₁ w₂ → n ≤ m)
    (S : Set (List g.ISym)) (hS : S.Finite)
    (hmem : ∀ i x, DerivesInIntermediate g n w₁ w₂ i x → x ∈ S) :
    n + 1 ≤ (Set.Finite.toFinset hS).card := by
  classical
  haveI : Fintype S := hS.fintype
  let mid (i : Fin (n + 1)) : List g.ISym :=
    Classical.choose (exists_derivesInIntermediate (g := g)
      (i := i.1) (w₁ := w₁) (w₂ := w₂)
      (Nat.lt_succ_iff.mp i.2) h)
  have hmid (i : Fin (n + 1)) :
      DerivesInIntermediate g n w₁ w₂ i.1 (mid i) :=
    Classical.choose_spec (exists_derivesInIntermediate (g := g)
      (i := i.1) (w₁ := w₁) (w₂ := w₂)
      (Nat.lt_succ_iff.mp i.2) h)
  let f : Fin (n + 1) → S := fun i => ⟨mid i, hmem i.1 (mid i) (hmid i)⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    have hsame : mid i = mid j := by
      exact congrArg Subtype.val hij
    exact minimal_derivesIn_intermediate_index_eq (g := g) (n := n) hmin
      (x := mid i) (hmid i) (by simpa [hsame] using hmid j)
  have hcard := Fintype.card_le_of_injective f hf
  simpa [Set.Finite.card_toFinset hS] using hcard

theorem generates_iff_exists_derivesIn (g : IndexedGrammar T) (w : List T) :
    g.Generates w ↔
      ∃ n, g.DerivesIn n [ISym.indexed g.initial []] (w.map ISym.terminal) := by
  rw [Generates, derives_iff_exists_derivesIn]

theorem exists_accepting_derivationTrace_of_generates {g : IndexedGrammar T}
    {w : List T} (hgen : g.Generates w) :
    ∃ n trace,
      IsDerivationTrace g trace ∧ trace.length = n + 1 ∧
        trace.head? = some [ISym.indexed g.initial []] ∧
        trace.getLast? = some (w.map ISym.terminal) := by
  obtain ⟨n, hder⟩ :=
    (generates_iff_exists_derivesIn g w).mp hgen
  obtain ⟨trace, htrace, hlen, hhead, hlast⟩ :=
    exists_isDerivationTrace_of_derivesIn hder
  exact ⟨n, trace, htrace, hlen, hhead, hlast⟩

/-- Any generated word has a propositionally least accepting derivation length. -/
theorem exists_minimal_derivesIn_of_generates {g : IndexedGrammar T}
    {w : List T} (h : g.Generates w) :
    ∃ n, g.DerivesIn n [ISym.indexed g.initial []] (w.map ISym.terminal) ∧
      ∀ m, g.DerivesIn m [ISym.indexed g.initial []] (w.map ISym.terminal) → n ≤ m := by
  exact exists_minimal_derivesIn_of_derives (g := g) (by simpa [Generates] using h)

theorem exists_minimal_accepting_derivationTrace_nodup_of_generates {g : IndexedGrammar T}
    {w : List T} (hgen : g.Generates w) :
    ∃ n trace,
      IsDerivationTrace g trace ∧ trace.length = n + 1 ∧
        trace.head? = some [ISym.indexed g.initial []] ∧
        trace.getLast? = some (w.map ISym.terminal) ∧
        trace.Nodup := by
  obtain ⟨n, hder, hmin⟩ := exists_minimal_derivesIn_of_generates (g := g) hgen
  obtain ⟨trace, htrace, hlen, hhead, hlast⟩ :=
    exists_isDerivationTrace_of_derivesIn hder
  exact ⟨n, trace, htrace, hlen, hhead, hlast,
    minimal_derivationTrace_nodup htrace hlen hhead hlast hmin⟩

theorem derivesIn_length_le_of_noEpsilon {g : IndexedGrammar T}
    (hne : g.NoEpsilon') {n : ℕ} {w₁ w₂ : List g.ISym}
    (h : g.DerivesIn n w₁ w₂) : w₁.length ≤ w₂.length :=
  derives_length_le_of_noEpsilon hne (derives_of_derivesIn h)

private theorem max_push_le_succ (a b c : ℕ) :
    max a (max (b + 1) c) ≤ max a (max b c) + 1 := by
  apply Nat.max_le.mpr
  constructor
  · exact le_trans (Nat.le_max_left a (max b c)) (Nat.le_succ _)
  · apply Nat.max_le.mpr
    constructor
    · have hb : b ≤ max a (max b c) :=
        le_trans (Nat.le_max_left b c) (Nat.le_max_right a (max b c))
      exact Nat.succ_le_succ hb
    · have hc : c ≤ max a (max b c) :=
        le_trans (Nat.le_max_right b c) (Nat.le_max_right a (max b c))
      exact le_trans hc (Nat.le_succ _)

private theorem max_pop_le_succ (a b c : ℕ) :
    max a (max b c) ≤ max a (max (b + 1) c) + 1 := by
  have hbase : max a (max b c) ≤ max a (max (b + 1) c) := by
    apply Nat.max_le.mpr
    constructor
    · exact Nat.le_max_left a (max (b + 1) c)
    · apply Nat.max_le.mpr
      constructor
      · exact le_trans (le_trans (Nat.le_succ b) (Nat.le_max_left (b + 1) c))
          (Nat.le_max_right a (max (b + 1) c))
      · exact le_trans (Nat.le_max_right (b + 1) c)
          (Nat.le_max_right a (max (b + 1) c))
  exact le_trans hbase (Nat.le_succ _)

private theorem max_terminal_le_succ (a b c : ℕ) :
    max a c ≤ max a (max b c) + 1 := by
  have hbase : max a c ≤ max a (max b c) := by
    apply Nat.max_le.mpr
    constructor
    · exact Nat.le_max_left a (max b c)
    · exact le_trans (Nat.le_max_right b c) (Nat.le_max_right a (max b c))
  exact le_trans hbase (Nat.le_succ _)

/-! ## Normal-form step bounds -/

theorem IRule.rhs_length_eq_one_or_two_of_isNF {N F : Type} [DecidableEq N]
    {r : IRule T N F} {start : N} (hNF : IRule.IsNF r start) :
    r.rhs.length = 1 ∨ r.rhs.length = 2 := by
  rcases hNF with hbin | hpop | hpush | hterm
  · rcases hbin with ⟨_, _, _, hrhs, _, _⟩
    right
    simp [hrhs]
  · rcases hpop with ⟨_, _, _, hrhs, _⟩
    left
    simp [hrhs]
  · rcases hpush with ⟨_, _, _, hrhs, _⟩
    left
    simp [hrhs]
  · rcases hterm with ⟨_, _, hrhs⟩
    left
    simp [hrhs]

theorem IRule.rhs_length_le_two_of_isNF {N F : Type} [DecidableEq N]
    {r : IRule T N F} {start : N} (hNF : IRule.IsNF r start) :
    r.rhs.length ≤ 2 := by
  rcases IRule.rhs_length_eq_one_or_two_of_isNF (T := T) hNF with h | h <;> omega

theorem expandRhs_length (g : IndexedGrammar T)
    (rhs : List (IRhsSymbol T g.nt g.flag)) (σ : List g.flag) :
    (g.expandRhs rhs σ).length = rhs.length := by
  simp [expandRhs]

/-- A normal-form step either preserves sentential-form length or increases it by one. -/
theorem transforms_length_eq_or_succ_of_isNormalForm {g : IndexedGrammar T}
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {w₁ w₂ : List g.ISym} (h : g.Transforms w₁ w₂) :
    w₂.length = w₁.length ∨ w₂.length = w₁.length + 1 := by
  rcases h with ⟨r, u, v, σ, hr, hw₁, hw₂⟩
  subst w₂
  rcases hNF r hr with hbin | hpop | hpush | hterm
  · rcases hbin with ⟨hc, B, C, hrhs, _, _⟩
    rw [hc] at hw₁
    subst w₁
    right
    simp [expandRhs, hrhs, List.length_append]
    omega
  · rcases hpop with ⟨f, hc, B, hrhs, _⟩
    rw [hc] at hw₁
    subst w₁
    left
    simp [expandRhs, hrhs, List.length_append]
  · rcases hpush with ⟨hc, B, f, hrhs, _⟩
    rw [hc] at hw₁
    subst w₁
    left
    simp [expandRhs, hrhs, List.length_append]
  · rcases hterm with ⟨hc, a, hrhs⟩
    rw [hc] at hw₁
    subst w₁
    left
    simp [expandRhs, hrhs, List.length_append]

theorem transforms_length_le_succ_of_isNormalForm {g : IndexedGrammar T}
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {w₁ w₂ : List g.ISym} (h : g.Transforms w₁ w₂) :
    w₂.length ≤ w₁.length + 1 := by
  rcases transforms_length_eq_or_succ_of_isNormalForm hNF h with hlen | hlen <;> omega

/-- A one-step rewrite in normal form has exactly one of the four indexed-normal-form
shapes: binary split, flag pop, flag push, or terminal emission. -/
theorem transforms_cases_of_isNormalForm {g : IndexedGrammar T}
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {w₁ w₂ : List g.ISym} (h : g.Transforms w₁ w₂) :
    (∃ A B C : g.nt, ∃ u v : List g.ISym, ∃ σ : List g.flag,
      B ≠ g.initial ∧ C ≠ g.initial ∧
      w₁ = u ++ [ISym.indexed A σ] ++ v ∧
      w₂ = u ++ [ISym.indexed B σ, ISym.indexed C σ] ++ v) ∨
    (∃ A B : g.nt, ∃ f : g.flag, ∃ u v : List g.ISym, ∃ σ : List g.flag,
      B ≠ g.initial ∧
      w₁ = u ++ [ISym.indexed A (f :: σ)] ++ v ∧
      w₂ = u ++ [ISym.indexed B σ] ++ v) ∨
    (∃ A B : g.nt, ∃ f : g.flag, ∃ u v : List g.ISym, ∃ σ : List g.flag,
      B ≠ g.initial ∧
      w₁ = u ++ [ISym.indexed A σ] ++ v ∧
      w₂ = u ++ [ISym.indexed B (f :: σ)] ++ v) ∨
    (∃ A : g.nt, ∃ a : T, ∃ u v : List g.ISym, ∃ σ : List g.flag,
      w₁ = u ++ [ISym.indexed A σ] ++ v ∧
      w₂ = u ++ [ISym.terminal a] ++ v) := by
  rcases h with ⟨r, u, v, σ, hr, hw₁, hw₂⟩
  rcases hNF r hr with hbin | hpop | hpush | hterm
  · rcases hbin with ⟨hc, B, C, hrhs, hB, hC⟩
    left
    refine ⟨r.lhs, B, C, u, v, σ, hB, hC, ?_, ?_⟩
    · simpa [hc] using hw₁
    · rw [hw₂, hrhs]
      simp [expandRhs]
  · rcases hpop with ⟨f, hc, B, hrhs, hB⟩
    right
    left
    refine ⟨r.lhs, B, f, u, v, σ, hB, ?_, ?_⟩
    · simpa [hc] using hw₁
    · rw [hw₂, hrhs]
      simp [expandRhs]
  · rcases hpush with ⟨hc, B, f, hrhs, hB⟩
    right
    right
    left
    refine ⟨r.lhs, B, f, u, v, σ, hB, ?_, ?_⟩
    · simpa [hc] using hw₁
    · rw [hw₂, hrhs]
      simp [expandRhs]
  · rcases hterm with ⟨hc, a, hrhs⟩
    right
    right
    right
    refine ⟨r.lhs, a, u, v, σ, ?_, ?_⟩
    · simpa [hc] using hw₁
    · rw [hw₂, hrhs]
      simp [expandRhs]

/-- A normal-form step either increases the number of nonterminals by one, preserves it, or
decreases it by one. -/
theorem transforms_nonterminalCount_cases_of_isNormalForm {g : IndexedGrammar T}
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {w₁ w₂ : List g.ISym} (h : g.Transforms w₁ w₂) :
    sententialNonterminalCount w₂ = sententialNonterminalCount w₁ + 1 ∨
      sententialNonterminalCount w₂ = sententialNonterminalCount w₁ ∨
      sententialNonterminalCount w₁ = sententialNonterminalCount w₂ + 1 := by
  rcases transforms_cases_of_isNormalForm hNF h with hbin | hpop | hpush | hterm
  · rcases hbin with ⟨A, B, C, u, v, σ, _, _, hw₁, hw₂⟩
    left
    rw [hw₁, hw₂]
    simp [List.append_assoc]
    omega
  · rcases hpop with ⟨A, B, f, u, v, σ, _, hw₁, hw₂⟩
    right
    left
    rw [hw₁, hw₂]
    simp [List.append_assoc]
  · rcases hpush with ⟨A, B, f, u, v, σ, _, hw₁, hw₂⟩
    right
    left
    rw [hw₁, hw₂]
    simp [List.append_assoc]
  · rcases hterm with ⟨A, a, u, v, σ, hw₁, hw₂⟩
    right
    right
    rw [hw₁, hw₂]
    simp [List.append_assoc]
    omega

/-- A normal-form step either preserves the number of terminals or increases it by one. -/
theorem transforms_terminalCount_cases_of_isNormalForm {g : IndexedGrammar T}
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {w₁ w₂ : List g.ISym} (h : g.Transforms w₁ w₂) :
    sententialTerminalCount w₂ = sententialTerminalCount w₁ ∨
      sententialTerminalCount w₂ = sententialTerminalCount w₁ + 1 := by
  rcases transforms_cases_of_isNormalForm hNF h with hbin | hpop | hpush | hterm
  · rcases hbin with ⟨A, B, C, u, v, σ, _, _, hw₁, hw₂⟩
    left
    rw [hw₁, hw₂]
    simp [List.append_assoc]
  · rcases hpop with ⟨A, B, f, u, v, σ, _, hw₁, hw₂⟩
    left
    rw [hw₁, hw₂]
    simp [List.append_assoc]
  · rcases hpush with ⟨A, B, f, u, v, σ, _, hw₁, hw₂⟩
    left
    rw [hw₁, hw₂]
    simp [List.append_assoc]
  · rcases hterm with ⟨A, a, u, v, σ, hw₁, hw₂⟩
    right
    rw [hw₁, hw₂]
    simp [List.append_assoc]
    omega

theorem transforms_terminalCount_le_succ_of_isNormalForm {g : IndexedGrammar T}
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {w₁ w₂ : List g.ISym} (h : g.Transforms w₁ w₂) :
    sententialTerminalCount w₂ ≤ sententialTerminalCount w₁ + 1 := by
  rcases transforms_terminalCount_cases_of_isNormalForm hNF h with htc | htc <;> omega

/-- A normal-form step can increase the maximum stack height by at most one. -/
theorem transforms_maxStackHeight_le_succ_of_isNormalForm {g : IndexedGrammar T}
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {w₁ w₂ : List g.ISym} (h : g.Transforms w₁ w₂) :
    sententialMaxStackHeight w₂ ≤ sententialMaxStackHeight w₁ + 1 := by
  rcases transforms_cases_of_isNormalForm hNF h with hbin | hpop | hpush | hterm
  · rcases hbin with ⟨A, B, C, u, v, σ, _, _, hw₁, hw₂⟩
    rw [hw₁, hw₂]
    simp [List.append_assoc, Nat.max_comm]
  · rcases hpop with ⟨A, B, f, u, v, σ, _, hw₁, hw₂⟩
    rw [hw₁, hw₂]
    simpa [List.append_assoc, Nat.max_assoc, Nat.max_comm] using
      max_pop_le_succ (sententialMaxStackHeight u) σ.length (sententialMaxStackHeight v)
  · rcases hpush with ⟨A, B, f, u, v, σ, _, hw₁, hw₂⟩
    rw [hw₁, hw₂]
    simpa [List.append_assoc, Nat.max_assoc, Nat.max_comm] using
      max_push_le_succ (sententialMaxStackHeight u) σ.length (sententialMaxStackHeight v)
  · rcases hterm with ⟨A, a, u, v, σ, hw₁, hw₂⟩
    rw [hw₁, hw₂]
    simpa [List.append_assoc, Nat.max_assoc, Nat.max_comm] using
      max_terminal_le_succ (sententialMaxStackHeight u) σ.length (sententialMaxStackHeight v)

/-- In a counted normal-form derivation, sentential-form length grows by at most the number of
steps. -/
theorem derivesIn_length_le_add_of_isNormalForm {g : IndexedGrammar T}
    [DecidableEq g.nt] (hNF : g.IsNormalForm) {n : ℕ}
    {w₁ w₂ : List g.ISym} (h : g.DerivesIn n w₁ w₂) :
    w₂.length ≤ w₁.length + n := by
  induction n generalizing w₂ with
  | zero =>
      have hw : w₁ = w₂ := by simpa using h
      subst w₂
      simp
  | succ n ih =>
      rcases h with ⟨w, hprev, hstep⟩
      have hprev_len := ih hprev
      have hstep_len := transforms_length_le_succ_of_isNormalForm hNF hstep
      omega

/-- In a counted normal-form derivation, the terminal count grows by at most the number of
steps. -/
theorem derivesIn_terminalCount_le_add_of_isNormalForm {g : IndexedGrammar T}
    [DecidableEq g.nt] (hNF : g.IsNormalForm) {n : ℕ}
    {w₁ w₂ : List g.ISym} (h : g.DerivesIn n w₁ w₂) :
    sententialTerminalCount w₂ ≤ sententialTerminalCount w₁ + n := by
  induction n generalizing w₂ with
  | zero =>
      have hw : w₁ = w₂ := by simpa using h
      subst w₂
      simp
  | succ n ih =>
      rcases h with ⟨w, hprev, hstep⟩
      have hprev_term := ih hprev
      have hstep_term := transforms_terminalCount_le_succ_of_isNormalForm hNF hstep
      omega

/-- In a counted normal-form derivation, the maximum stack height grows by at most the number
of steps. -/
theorem derivesIn_maxStackHeight_le_add_of_isNormalForm {g : IndexedGrammar T}
    [DecidableEq g.nt] (hNF : g.IsNormalForm) {n : ℕ}
    {w₁ w₂ : List g.ISym} (h : g.DerivesIn n w₁ w₂) :
    sententialMaxStackHeight w₂ ≤ sententialMaxStackHeight w₁ + n := by
  induction n generalizing w₂ with
  | zero =>
      have hw : w₁ = w₂ := by simpa using h
      subst w₂
      simp
  | succ n ih =>
      rcases h with ⟨w, hprev, hstep⟩
      have hprev_height := ih hprev
      have hstep_height := transforms_maxStackHeight_le_succ_of_isNormalForm hNF hstep
      omega

/-- A counted accepting normal-form derivation for a word of length `k` uses at least `k`
steps. -/
theorem generated_length_le_derivesIn_steps_of_isNormalForm {g : IndexedGrammar T}
    [DecidableEq g.nt] (hNF : g.IsNormalForm) {n : ℕ} {w : List T}
    (h : g.DerivesIn n [ISym.indexed g.initial []] (w.map ISym.terminal)) :
    w.length ≤ n := by
  have hterm := derivesIn_terminalCount_le_add_of_isNormalForm hNF h
  simpa using hterm

theorem accepting_derivationTrace_get_length_le_target_of_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {w : List T}
    (htrace : IsDerivationTrace g trace)
    (hlast : trace.getLast? = some (w.map ISym.terminal))
    {i : ℕ} (hi : i < trace.length) :
    (trace.get ⟨i, hi⟩).length ≤ w.length := by
  have hsuffix := isDerivationTrace_derivesIn_get_to_last (g := g) htrace hlast hi
  have hlen :=
    derivesIn_length_le_of_noEpsilon (g.noEpsilon_of_isNormalForm hNF) hsuffix
  simpa using hlen

theorem accepting_derivationTrace_get_maxStackHeight_le_index_of_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)}
    (htrace : IsDerivationTrace g trace)
    (hhead : trace.head? = some [ISym.indexed g.initial []])
    {i : ℕ} (hi : i < trace.length) :
    sententialMaxStackHeight (trace.get ⟨i, hi⟩) ≤ i := by
  have hprefix :=
    isDerivationTrace_derivesIn_from_head_get (g := g) htrace hhead hi
  have hheight := derivesIn_maxStackHeight_le_add_of_isNormalForm hNF hprefix
  simpa using hheight

theorem accepting_derivationTrace_get_mem_boundedSententialForms_of_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {n : ℕ} {w : List T}
    (htrace : IsDerivationTrace g trace)
    (hlen : trace.length = n + 1)
    (hhead : trace.head? = some [ISym.indexed g.initial []])
    (hlast : trace.getLast? = some (w.map ISym.terminal))
    {i : ℕ} (hi : i < trace.length) :
    trace.get ⟨i, hi⟩ ∈ boundedSententialForms g w.length n := by
  refine ⟨?_, ?_⟩
  · exact accepting_derivationTrace_get_length_le_target_of_isNormalForm hNF htrace hlast hi
  · have hheight :=
      accepting_derivationTrace_get_maxStackHeight_le_index_of_isNormalForm hNF htrace hhead hi
    have hi_le : i ≤ n := by omega
    exact le_trans hheight hi_le

theorem accepting_derivationTrace_get_surface_mem_boundedSurfaceForms_of_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {w : List T} {B : ℕ}
    (htrace : IsDerivationTrace g trace)
    (hlast : trace.getLast? = some (w.map ISym.terminal))
    {i : ℕ} (hi : i < trace.length) :
    surfaceOfTruncatedForm B (trace.get ⟨i, hi⟩) ∈
      boundedSurfaceForms g w.length B := by
  apply surfaceOfTruncatedForm_mem_boundedSurfaceForms
  exact accepting_derivationTrace_get_length_le_target_of_isNormalForm hNF htrace hlast hi

theorem accepting_surfaceTrace_get_mem_boundedSurfaceForms_of_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {w : List T} {B : ℕ}
    (htrace : IsDerivationTrace g trace)
    (hlast : trace.getLast? = some (w.map ISym.terminal))
    (i : Fin (surfaceTrace B trace).length) :
    (surfaceTrace B trace).get i ∈ boundedSurfaceForms g w.length B := by
  have hi : i.1 < trace.length := by
    simpa using i.2
  rw [surfaceTrace_get B trace hi]
  exact accepting_derivationTrace_get_surface_mem_boundedSurfaceForms_of_isNormalForm
    hNF htrace hlast hi

theorem accepting_derivationTrace_exists_surface_repeat_of_card_lt_length
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {w : List T} {B : ℕ}
    (htrace : IsDerivationTrace g trace)
    (hlast : trace.getLast? = some (w.map ISym.terminal))
    (hcard :
      (Set.Finite.toFinset (boundedSurfaceForms_finite g w.length B)).card <
        trace.length) :
    ∃ i j : Fin trace.length, i < j ∧
      surfaceOfTruncatedForm B (trace.get i) =
        surfaceOfTruncatedForm B (trace.get j) := by
  have hcard' :
      (Set.Finite.toFinset (boundedSurfaceForms_finite g w.length B)).card <
        (surfaceTrace B trace).length := by
    simpa using hcard
  rcases List.exists_get_eq_of_finite_set_card_lt_length
      (xs := surfaceTrace B trace)
      (boundedSurfaceForms g w.length B)
      (boundedSurfaceForms_finite g w.length B)
      (fun i =>
        accepting_surfaceTrace_get_mem_boundedSurfaceForms_of_isNormalForm
          hNF htrace hlast i)
      hcard' with ⟨i, j, hij, hget⟩
  let i' : Fin trace.length := ⟨i.1, by simpa using i.2⟩
  let j' : Fin trace.length := ⟨j.1, by simpa using j.2⟩
  have hi : i.1 < trace.length := i'.2
  have hj : j.1 < trace.length := j'.2
  have hget' :
      (surfaceTrace B trace).get ⟨i.1, by simpa using hi⟩ =
        (surfaceTrace B trace).get ⟨j.1, by simpa using hj⟩ := by
    simpa using hget
  have hsurface :
      surfaceOfTruncatedForm B (trace.get ⟨i.1, hi⟩) =
        surfaceOfTruncatedForm B (trace.get ⟨j.1, hj⟩) := by
    rw [surfaceTrace_get B trace hi] at hget'
    rw [surfaceTrace_get B trace hj] at hget'
    exact hget'
  refine ⟨i', j', ?_, ?_⟩
  · exact hij
  · exact hsurface

theorem accepting_derivationTrace_length_le_boundedSententialForms_card_of_stackBound
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {w : List T} {B : ℕ}
    (htrace : IsDerivationTrace g trace)
    (hlast : trace.getLast? = some (w.map ISym.terminal))
    (hnodup : trace.Nodup)
    (hstack : ∀ i (hi : i < trace.length),
      sententialMaxStackHeight (trace.get ⟨i, hi⟩) ≤ B) :
    trace.length ≤
      (Set.Finite.toFinset (boundedSententialForms_finite g w.length B)).card := by
  exact List.Nodup.length_le_finite_set_card_of_get_mem hnodup
    (boundedSententialForms g w.length B)
    (boundedSententialForms_finite g w.length B)
    (fun i => ⟨accepting_derivationTrace_get_length_le_target_of_isNormalForm
        hNF htrace hlast i.2,
      hstack i.1 i.2⟩)

theorem minimal_accepting_derivationTrace_length_le_boundedSententialForms_card_of_stackBound
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {trace : List (List g.ISym)} {n : ℕ} {w : List T} {B : ℕ}
    (htrace : IsDerivationTrace g trace)
    (hlen : trace.length = n + 1)
    (hhead : trace.head? = some [ISym.indexed g.initial []])
    (hlast : trace.getLast? = some (w.map ISym.terminal))
    (hmin : ∀ m,
      g.DerivesIn m [ISym.indexed g.initial []] (w.map ISym.terminal) → n ≤ m)
    (hstack : ∀ i (hi : i < trace.length),
      sententialMaxStackHeight (trace.get ⟨i, hi⟩) ≤ B) :
    trace.length ≤
      (Set.Finite.toFinset (boundedSententialForms_finite g w.length B)).card := by
  have hnodup := minimal_derivationTrace_nodup htrace hlen hhead hlast hmin
  exact accepting_derivationTrace_length_le_boundedSententialForms_card_of_stackBound
    hNF htrace hlast hnodup hstack

theorem accepting_derivesInIntermediate_length_le_target_of_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {n i : ℕ} {w : List T} {x : List g.ISym}
    (hmid : DerivesInIntermediate g n [ISym.indexed g.initial []]
      (w.map ISym.terminal) i x) :
    x.length ≤ w.length := by
  have hlen :=
    derivesIn_length_le_of_noEpsilon (g.noEpsilon_of_isNormalForm hNF) hmid.2.2
  simpa using hlen

theorem accepting_derivesInIntermediate_maxStackHeight_le_index_of_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {n i : ℕ} {w : List T} {x : List g.ISym}
    (hmid : DerivesInIntermediate g n [ISym.indexed g.initial []]
      (w.map ISym.terminal) i x) :
    sententialMaxStackHeight x ≤ i := by
  have hheight := derivesIn_maxStackHeight_le_add_of_isNormalForm hNF hmid.2.1
  simpa using hheight

theorem accepting_derivesInIntermediate_mem_boundedSententialForms_of_isNormalForm
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {n i : ℕ} {w : List T} {x : List g.ISym}
    (hmid : DerivesInIntermediate g n [ISym.indexed g.initial []]
      (w.map ISym.terminal) i x) :
    x ∈ boundedSententialForms g w.length n := by
  exact ⟨accepting_derivesInIntermediate_length_le_target_of_isNormalForm hNF hmid,
    le_trans (accepting_derivesInIntermediate_maxStackHeight_le_index_of_isNormalForm hNF hmid)
      hmid.1⟩

/-- If a shortest accepting derivation has all intermediate stack heights bounded by `B`, then
its step count is bounded by the finite set of sentential forms with length at most the target
word and stack height at most `B`. -/
theorem minimal_accepting_derivesIn_steps_succ_le_boundedSententialForms_card_of_stackBound
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {n : ℕ} {w : List T}
    (h : g.DerivesIn n [ISym.indexed g.initial []] (w.map ISym.terminal))
    (hmin : ∀ m,
      g.DerivesIn m [ISym.indexed g.initial []] (w.map ISym.terminal) → n ≤ m)
    {B : ℕ}
    (hstack : ∀ i x,
      DerivesInIntermediate g n [ISym.indexed g.initial []] (w.map ISym.terminal) i x →
        sententialMaxStackHeight x ≤ B) :
    n + 1 ≤
      (Set.Finite.toFinset (boundedSententialForms_finite g w.length B)).card := by
  refine minimal_derivesIn_steps_succ_le_card_of_intermediates_mem h hmin
    (boundedSententialForms g w.length B)
    (boundedSententialForms_finite g w.length B) ?_
  intro i x hmid
  exact ⟨accepting_derivesInIntermediate_length_le_target_of_isNormalForm hNF hmid,
    hstack i x hmid⟩

/-- The previous cardinal bound instantiated with the elementary per-step stack-height bound. -/
theorem minimal_accepting_derivesIn_steps_succ_le_boundedSententialForms_card
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {n : ℕ} {w : List T}
    (h : g.DerivesIn n [ISym.indexed g.initial []] (w.map ISym.terminal))
    (hmin : ∀ m,
      g.DerivesIn m [ISym.indexed g.initial []] (w.map ISym.terminal) → n ≤ m) :
    n + 1 ≤
      (Set.Finite.toFinset (boundedSententialForms_finite g w.length n)).card := by
  apply minimal_accepting_derivesIn_steps_succ_le_boundedSententialForms_card_of_stackBound
    hNF h hmin
  intro i x hmid
  exact le_trans
    (accepting_derivesInIntermediate_maxStackHeight_le_index_of_isNormalForm hNF hmid)
    hmid.1

/-- Every generated word has a shortest accepting derivation whose step count is squeezed
between the word length and the finite set of elementary bounded sentential forms. -/
theorem exists_minimal_accepting_derivesIn_with_boundedSententialForms_card
    {g : IndexedGrammar T} [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm) {w : List T}
    (hgen : g.Generates w) :
    ∃ n,
      g.DerivesIn n [ISym.indexed g.initial []] (w.map ISym.terminal) ∧
      (∀ m,
        g.DerivesIn m [ISym.indexed g.initial []] (w.map ISym.terminal) → n ≤ m) ∧
      w.length ≤ n ∧
      n + 1 ≤
        (Set.Finite.toFinset (boundedSententialForms_finite g w.length n)).card := by
  obtain ⟨n, hder, hmin⟩ := exists_minimal_derivesIn_of_generates (g := g) hgen
  exact ⟨n, hder, hmin, generated_length_le_derivesIn_steps_of_isNormalForm hNF hder,
    minimal_accepting_derivesIn_steps_succ_le_boundedSententialForms_card hNF hder hmin⟩

/-- In an accepting derivation of a no-ε grammar, every intermediate sentential form on the
chosen suffix has length at most the target word. -/
theorem intermediate_length_le_target_of_noEpsilon {g : IndexedGrammar T}
    (hne : g.NoEpsilon') {x : List g.ISym} {w : List T}
    (hsuffix : g.Derives x (w.map ISym.terminal)) :
    x.length ≤ w.length := by
  have hlen := derives_length_le_of_noEpsilon hne hsuffix
  simpa using hlen

/-- Every sentential form reachable from the start of a no-ε grammar is nonempty. -/
theorem reachable_length_pos_of_noEpsilon {g : IndexedGrammar T}
    (hne : g.NoEpsilon') {x : List g.ISym}
    (hprefix : g.Derives [ISym.indexed g.initial []] x) :
    0 < x.length := by
  have hlen := derives_length_le_of_noEpsilon hne hprefix
  simp at hlen
  omega

/-- In an accepting derivation of a no-ε grammar, every intermediate sentential form is
nonempty and has length at most the target word. -/
theorem accepting_intermediate_length_bounds_of_noEpsilon {g : IndexedGrammar T}
    (hne : g.NoEpsilon') {x : List g.ISym} {w : List T}
    (hprefix : g.Derives [ISym.indexed g.initial []] x)
    (hsuffix : g.Derives x (w.map ISym.terminal)) :
    0 < x.length ∧ x.length ≤ w.length :=
  ⟨reachable_length_pos_of_noEpsilon hne hprefix,
    intermediate_length_le_target_of_noEpsilon hne hsuffix⟩

/-- In an accepting derivation of a no-ε grammar, the number of live nonterminals in any
intermediate sentential form is bounded by the target word length. -/
theorem intermediate_nonterminalCount_le_target_of_noEpsilon {g : IndexedGrammar T}
    (hne : g.NoEpsilon') {x : List g.ISym} {w : List T}
    (hsuffix : g.Derives x (w.map ISym.terminal)) :
    sententialNonterminalCount x ≤ w.length :=
  le_trans (sententialNonterminalCount_le_length x)
    (intermediate_length_le_target_of_noEpsilon hne hsuffix)

/-- In an accepting derivation of a normal-form grammar, every intermediate sentential form on
the chosen suffix has length at most the target word. -/
theorem intermediate_length_le_target_of_isNormalForm {g : IndexedGrammar T}
    [DecidableEq g.nt] (hNF : g.IsNormalForm) {x : List g.ISym} {w : List T}
    (hsuffix : g.Derives x (w.map ISym.terminal)) :
    x.length ≤ w.length :=
  intermediate_length_le_target_of_noEpsilon (g.noEpsilon_of_isNormalForm hNF) hsuffix

/-- In an accepting derivation of a normal-form grammar, every intermediate sentential form is
nonempty and has length at most the target word. -/
theorem accepting_intermediate_length_bounds_of_isNormalForm {g : IndexedGrammar T}
    [DecidableEq g.nt] (hNF : g.IsNormalForm) {x : List g.ISym} {w : List T}
    (hprefix : g.Derives [ISym.indexed g.initial []] x)
    (hsuffix : g.Derives x (w.map ISym.terminal)) :
    0 < x.length ∧ x.length ≤ w.length :=
  accepting_intermediate_length_bounds_of_noEpsilon (g.noEpsilon_of_isNormalForm hNF)
    hprefix hsuffix

/-- In an accepting derivation of a normal-form grammar, the number of live nonterminals in
any intermediate sentential form is bounded by the target word length. -/
theorem intermediate_nonterminalCount_le_target_of_isNormalForm {g : IndexedGrammar T}
    [DecidableEq g.nt] (hNF : g.IsNormalForm) {x : List g.ISym} {w : List T}
    (hsuffix : g.Derives x (w.map ISym.terminal)) :
    sententialNonterminalCount x ≤ w.length :=
  intermediate_nonterminalCount_le_target_of_noEpsilon
    (g.noEpsilon_of_isNormalForm hNF) hsuffix

/-- A no-ε indexed grammar can only generate nonempty words. -/
theorem generated_length_pos_of_noEpsilon {g : IndexedGrammar T}
    (hne : g.NoEpsilon') {w : List T} (hgen : g.Generates w) :
    0 < w.length := by
  have hlen := derives_length_le_of_noEpsilon hne hgen
  simpa using hlen

/-- A normal-form indexed grammar can only generate nonempty words. -/
theorem generated_length_pos_of_isNormalForm {g : IndexedGrammar T}
    [DecidableEq g.nt] (hNF : g.IsNormalForm) {w : List T} (hgen : g.Generates w) :
    0 < w.length :=
  generated_length_pos_of_noEpsilon (g.noEpsilon_of_isNormalForm hNF) hgen

end IndexedGrammar
