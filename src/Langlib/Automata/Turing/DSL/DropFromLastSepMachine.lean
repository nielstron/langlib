import Mathlib
import Langlib.Automata.Turing.DSL.BlockRealizability
import Langlib.Automata.Turing.DSL.DropWhileNeSep
import Langlib.Automata.Turing.DSL.TakeWhileBlock

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

/-- `takeWhile (· ≠ sep)` is block-realizable.
    Proved via the decomposition `reverse ∘ dropFromLastSep sep ∘ reverse`
    and the general `tm0_dropFromLastSep_direct` theorem. -/
theorem tm0_takeWhileNeSep {Γ : Type} [Inhabited Γ] [DecidableEq Γ] [Fintype Γ]
    (sep : Γ) (hsep : sep ≠ default) :
    TM0RealizesBlock Γ (List.takeWhile (fun x => !decide (x = sep))) :=
  tm0_takeWhileNeSep' sep hsep

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
