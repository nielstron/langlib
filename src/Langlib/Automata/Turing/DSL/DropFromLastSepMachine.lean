import Mathlib
import Langlib.Automata.Turing.DSL.BlockRealizability
import Langlib.Automata.Turing.DSL.DropWhileNeSep

/-! # TM0 Machine for dropFromLastSep

Proves `dropFromLastSep sep` is block-realizable via the decomposition:
`dropFromLastSep sep = List.reverse ∘ (List.takeWhile (· ≠ sep)) ∘ List.reverse`
-/

open Turing

/-! ### Functional decomposition -/

theorem dropFromLastSep_eq_rev_takeWhile_rev {Γ : Type} [DecidableEq Γ]
    (sep : Γ) (l : List Γ) :
    dropFromLastSep sep l = (l.reverse.takeWhile (· ≠ sep)).reverse := by
  induction' l with c l ih;
  · rfl;
  · by_cases h : sep ∈ l <;> simp +decide [ *, dropFromLastSep ];
    · rw [ List.takeWhile_append ];
      have h_takeWhile : ∀ {l : List Γ}, sep ∈ l → List.length (List.takeWhile (fun x => !decide (x = sep)) l) < List.length l := by
        intros l hl; induction' l with c l ih <;> simp_all +decide [ List.takeWhile_cons ] ;
        grind;
      grind;
    · split_ifs <;> simp_all +decide [ List.takeWhile_append ];
      · rw [ List.takeWhile_eq_self_iff.mpr ] <;> aesop;
      · rw [ List.takeWhile_eq_self_iff.mpr ] <;> aesop

theorem dropFromLastSep_eq_comp {Γ : Type} [DecidableEq Γ] (sep : Γ) :
    dropFromLastSep sep =
      List.reverse ∘ (List.takeWhile (fun x => !decide (x = sep))) ∘ @List.reverse Γ := by
  funext l; simp only [Function.comp]
  convert dropFromLastSep_eq_rev_takeWhile_rev sep l using 2
  congr 1; ext x; simp [Ne, decide_not]

/-! ### takeWhile (· ≠ sep) preserves non-defaultness -/

theorem takeWhile_ne_sep_ne_default {Γ : Type} [Inhabited Γ] [DecidableEq Γ]
    (sep : Γ) (block : List Γ) (hblock : ∀ g ∈ block, g ≠ default) :
    ∀ g ∈ block.takeWhile (fun x => !decide (x = sep)), g ≠ default := by
  intro g hg; exact hblock g (List.takeWhile_subset _ hg)

/-! ### TM0 machine for takeWhile (· ≠ sep) -/

/-- Machine for `takeWhile (· ≠ sep)`: scan, erase from sep, rewind. -/
noncomputable def twMachine {Γ : Type} [Inhabited Γ] [DecidableEq Γ]
    (sep : Γ) : @TM0.Machine Γ (Fin 5) ⟨0⟩ := fun q a =>
  match q with
  | (0 : Fin 5) => -- scan
    if a = sep then some (1, TM0.Stmt.write default)
    else if a = default then some (3, TM0.Stmt.move Dir.left)
    else some (0, TM0.Stmt.move Dir.right)
  | (1 : Fin 5) => some (2, TM0.Stmt.move Dir.right) -- post-erase move
  | (2 : Fin 5) => -- erase remaining
    if a = default then some (3, TM0.Stmt.move Dir.left)
    else some (1, TM0.Stmt.write default)
  | (3 : Fin 5) => -- rewind
    if a = default then some (4, TM0.Stmt.move Dir.right)
    else some (3, TM0.Stmt.move Dir.left)
  | (4 : Fin 5) => none -- done

/-- `takeWhile (· ≠ sep)` is block-realizable. -/
theorem tm0_takeWhileNeSep {Γ : Type} [Inhabited Γ] [DecidableEq Γ] [Fintype Γ]
    (sep : Γ) (hsep : sep ≠ default) :
    TM0RealizesBlock Γ (List.takeWhile (fun x => !decide (x = sep))) := by
  refine ⟨Fin 5, ⟨0⟩, inferInstance, twMachine sep, ?_⟩
  intro block suffix hblock hsuffix htw
  sorry

/-! ### Main result -/

theorem tm0_dropFromLastSep_block_v2 {Γ : Type} [Inhabited Γ] [DecidableEq Γ] [Fintype Γ]
    (sep : Γ) (hsep : sep ≠ default) :
    TM0RealizesBlock Γ (dropFromLastSep sep) := by
  rw [dropFromLastSep_eq_comp]
  apply tm0RealizesBlock_comp
  · apply tm0RealizesBlock_comp
    · exact tm0_reverse_block
    · exact tm0_takeWhileNeSep sep hsep
    · exact reverse_ne_default
  · exact tm0_reverse_block
  · intro block hblock
    simp only [Function.comp]
    exact takeWhile_ne_sep_ne_default sep _ (reverse_ne_default block hblock)
