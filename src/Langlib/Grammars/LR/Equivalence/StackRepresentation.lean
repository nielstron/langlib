module

public import Langlib.Grammars.LR.Equivalence.Preload
public import Langlib.Grammars.LR.Equivalence.CanonicalParser

/-!
# Concrete parser-stack representation

The DPDA stores canonical kernels rather than grammar symbols.  For every
symbol in a canonical parser stack it stores the kernel reached after the
corresponding prefix, with the current kernel on top and `none` as a permanent
bottom marker.
-/

@[expose]
public section

open Language PDA

namespace CF_grammar.LRk.Buffered

open CF_grammar.LRk

variable {T : Type} [Fintype T]

/-- Complete concrete stack representing a grammar-symbol parser stack. -/
@[expose]
public noncomputable def stackRep (G : CF_grammar T) (k : ℕ)
    (gamma : List (symbol T G.augment.nt)) :
    List (StackSymbol G k) :=
  ((gamma.inits.tail.map (scanKernel G k)).reverse.map some) ++ [none]

@[simp]
public theorem stackRep_nil (G : CF_grammar T) (k : ℕ) :
    stackRep G k [] = [none] := by
  simp [stackRep]

@[simp]
public theorem stackRep_append_singleton (G : CF_grammar T) (k : ℕ)
    (gamma : List (symbol T G.augment.nt))
    (X : symbol T G.augment.nt) :
    stackRep G k (gamma ++ [X]) =
      some (scanKernel G k (gamma ++ [X])) :: stackRep G k gamma := by
  simp only [stackRep, List.inits_append, List.inits, List.tail_cons,
    List.map_append, List.map_singleton, scanKernel_append_singleton,
    List.reverse_append, List.reverse_singleton, List.map_reverse,
    List.map_map, Function.comp_apply]
  rw [List.tail_append_singleton_of_ne_nil (by
    cases gamma <;> simp [List.inits])]
  simp

/-- The represented stack is always nonempty, and its top denotes the current
canonical kernel (with `none` denoting the initial kernel). -/
public theorem stackRep_top (G : CF_grammar T) (k : ℕ)
    (gamma : List (symbol T G.augment.nt)) :
    ∃ Z rest, stackRep G k gamma = Z :: rest ∧
      kernelOfTop G k Z = scanKernel G k gamma := by
  induction gamma using List.reverseRecOn with
  | nil => exact ⟨none, [], by simp [kernelOfTop]⟩
  | append_singleton gamma X ih =>
      exact ⟨some (scanKernel G k (gamma ++ [X])), stackRep G k gamma,
        by simp [kernelOfTop]⟩

/-- Appending `delta` grammar symbols adds exactly `delta.length` non-bottom
frames above the representation of the old prefix. -/
public theorem stackRep_append_frames (G : CF_grammar T) (k : ℕ)
    (gamma delta : List (symbol T G.augment.nt)) :
    ∃ frames : List (StackSymbol G k),
      frames.length = delta.length ∧
      (∀ Z ∈ frames, Z ≠ none) ∧
      stackRep G k (gamma ++ delta) = frames ++ stackRep G k gamma := by
  induction delta using List.reverseRecOn with
  | nil => exact ⟨[], rfl, by simp, by simp⟩
  | append_singleton delta X ih =>
      rcases ih with ⟨frames, hlen, hsome, hstack⟩
      refine ⟨some (scanKernel G k (gamma ++ delta ++ [X])) :: frames,
        ?_, ?_, ?_⟩
      · simp [hlen]
      · intro Z hZ
        simp only [List.mem_cons] at hZ
        rcases hZ with rfl | hZ
        · simp
        · exact hsome Z hZ
      · rw [← List.append_assoc, stackRep_append_singleton, hstack]
        rfl

end CF_grammar.LRk.Buffered
