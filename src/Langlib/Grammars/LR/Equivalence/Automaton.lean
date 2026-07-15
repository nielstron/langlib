module

public import Langlib.Grammars.LR.Equivalence.Initial

@[expose]
public section

/-!
# The finite canonical viable-prefix automaton

Starting from the augmented kernel, `scanKernel` follows canonical goto edges
over a grammar-symbol prefix.  Actions are taken from its epsilon closure.  The
main theorem here is the soundness half of the viable-prefix theorem: every
item reached after scanning `gamma` is semantically valid at `gamma`.
-/

open Language

namespace CF_grammar.LRk

variable {T : Type}

/-- Raw canonical kernel after scanning a grammar-symbol word.  Closure is
performed by `goto` before every dot advancement, and once more when the state
is inspected. -/
@[expose]
public noncomputable def scanKernel [Fintype T] (G : CF_grammar T) (k : ℕ) :
    List (symbol T G.augment.nt) → Finset (Item G.augment k) :=
  List.foldl (goto G.augment k) (startKernel G k)

/-- The closed canonical item state after scanning `gamma`. -/
@[expose]
public noncomputable def itemState [Fintype T] (G : CF_grammar T) (k : ℕ)
    (gamma : List (symbol T G.augment.nt)) : Finset (Item G.augment k) :=
  closure G.augment k (scanKernel G k gamma)

@[simp]
public theorem scanKernel_nil [Fintype T] (G : CF_grammar T) (k : ℕ) :
    scanKernel G k [] = startKernel G k := rfl

@[simp]
public theorem scanKernel_append [Fintype T] (G : CF_grammar T) (k : ℕ)
    (gamma delta : List (symbol T G.augment.nt)) :
    scanKernel G k (gamma ++ delta) =
      delta.foldl (goto G.augment k) (scanKernel G k gamma) := by
  simp [scanKernel, List.foldl_append]

@[simp]
public theorem scanKernel_append_singleton [Fintype T]
    (G : CF_grammar T) (k : ℕ)
    (gamma : List (symbol T G.augment.nt)) (X : symbol T G.augment.nt) :
    scanKernel G k (gamma ++ [X]) =
      goto G.augment k (scanKernel G k gamma) X := by
  simp

@[simp]
public theorem itemState_nil [Fintype T] (G : CF_grammar T) (k : ℕ) :
    itemState G k [] = closure G.augment k (startKernel G k) := rfl

/-- Every item in a canonical state is semantically valid for the scanned
prefix. -/
public theorem itemState_valid [Fintype T] (G : CF_grammar T) (k : ℕ)
    (gamma : List (symbol T G.augment.nt)) {i : Item G.augment k}
    (hi : i ∈ itemState G k gamma) : Valid G.augment k gamma i := by
  induction gamma using List.reverseRecOn generalizing i with
  | nil =>
      exact startClosure_valid G k (by simpa [itemState] using hi)
  | append_singleton gamma X ih =>
      have hraw : ∀ j ∈ scanKernel G k gamma,
          Valid G.augment k gamma j := by
        intro j hj
        exact ih (subset_closure G.augment k _ hj)
      have hgoto : ∀ j ∈ goto G.augment k (scanKernel G k gamma) X,
          Valid G.augment k (gamma ++ [X]) j := by
        intro j hj
        exact Valid.goto hraw hj
      apply Valid.of_mem_closure hgoto
      simpa [itemState] using hi

end CF_grammar.LRk
