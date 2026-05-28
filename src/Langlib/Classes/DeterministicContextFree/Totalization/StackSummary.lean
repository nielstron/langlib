import Mathlib.Computability.DFA

/-! # Finite Stack Summaries for Regular Lookahead

Regular lookahead on a pushdown stack can be implemented by storing, with each
stack symbol, the DFA transition summary of the suffix below that symbol.  If a
DFA state type is finite, the summary type `σ → σ` is finite, so these
annotations keep the stack alphabet finite.
-/

namespace DFA

variable {S σ : Type}

/-- The transition function induced by reading an entire stack suffix. -/
def stackSummary (D : DFA S σ) (γ : List S) : σ → σ :=
  fun s => D.evalFrom s γ

@[simp]
theorem stackSummary_nil (D : DFA S σ) :
    D.stackSummary [] = id := by
  funext s
  rfl

theorem stackSummary_append (D : DFA S σ) (γ δ : List S) :
    D.stackSummary (γ ++ δ) = D.stackSummary δ ∘ D.stackSummary γ := by
  funext s
  simp [stackSummary, DFA.evalFrom, List.foldl_append]

/-- The summary of a block `γ` placed above a suffix whose summary is `below`. -/
def summaryAbove (D : DFA S σ) (below : σ → σ) (γ : List S) : σ → σ :=
  below ∘ D.stackSummary γ

@[simp]
theorem summaryAbove_nil (D : DFA S σ) (below : σ → σ) :
    D.summaryAbove below [] = below := by
  funext s
  rfl

theorem summaryAbove_cons (D : DFA S σ) (below : σ → σ) (Z : S) (γ : List S) :
    D.summaryAbove below (Z :: γ) =
      D.summaryAbove (D.summaryAbove below γ) [Z] := by
  funext s
  simp [summaryAbove, stackSummary, DFA.evalFrom, Function.comp_def]

/-- Annotate a block of stack symbols to be placed above a suffix with known summary.
The annotation stored at each symbol is the summary of the suffix below it. -/
def annotateAbove (D : DFA S σ) (below : σ → σ) : List S → List (S × (σ → σ))
  | [] => []
  | Z :: γ => (Z, D.summaryAbove below γ) :: D.annotateAbove below γ

@[simp]
theorem annotateAbove_nil (D : DFA S σ) (below : σ → σ) :
    D.annotateAbove below [] = [] :=
  rfl

@[simp]
theorem annotateAbove_cons (D : DFA S σ) (below : σ → σ) (Z : S) (γ : List S) :
    D.annotateAbove below (Z :: γ) =
      (Z, D.summaryAbove below γ) :: D.annotateAbove below γ :=
  rfl

theorem annotateAbove_map_fst (D : DFA S σ) (below : σ → σ) (γ : List S) :
    (D.annotateAbove below γ).map Prod.fst = γ := by
  induction γ with
  | nil => rfl
  | cons Z γ ih => simp [ih]

/-- The summary stored at the top of a nonempty annotated block is the summary of
the block below that top symbol, together with the external suffix summary. -/
theorem annotateAbove_head?_tail_summary (D : DFA S σ) (below : σ → σ)
    (Z : S) (γ : List S) :
    (D.annotateAbove below (Z :: γ)).head? = some (Z, D.summaryAbove below γ) :=
  rfl

end DFA
