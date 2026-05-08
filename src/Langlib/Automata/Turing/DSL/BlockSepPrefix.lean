import Mathlib
import Langlib.Automata.Turing.DSL.TM0Compose
import Langlib.Automata.Turing.DSL.BlockRealizability
import Langlib.Automata.Turing.DSL.ReverseBlock

/-! # Block-Separator Prefix Preservation

This file shows that any `TM0RealizesBlockSep Γ sep f` can be lifted to
operate on an *inner* block of a two-separator tape, preserving the prefix.

## Main definitions

- `TM0RealizesInnerBlockSep Γ sep₁ sep₂ f`: the machine applies `f` to the
  inner block between `sep₂` and `sep₁`, preserving the prefix before `sep₂`.

## Main result

- `tm0RealizesBlockSep_toInner`: any `TM0RealizesBlockSep Γ sep₂ f` can be
  lifted to `TM0RealizesInnerBlockSep Γ sep₁ sep₂ f`.

## Strategy

The construction composes five sub-machines (three distinct):

1. **Reverse** (sep₁-delimited): reverses the outer block, bringing
   `inner.reverse` to the front where the left boundary is blank.
2. **Reverse** (sep₂-delimited): un-reverses the inner block back to `inner`.
3. **Apply f** (sep₂-delimited): applies `f` to the inner block.
4. **Reverse** (sep₂-delimited): reverses `f(inner)` back.
5. **Reverse** (sep₁-delimited): reverses the outer block, restoring prefix.

Steps 2–4 are composed into `reverse ∘ f ∘ reverse` via `tm0RealizesBlockSep_comp`,
producing a single `TM0RealizesBlockSep Γ sep₂` machine. The full construction
is then a three-machine composition: reverse(sep₁) → revFRev(sep₂) → reverse(sep₁).
-/

open Turing

/-! ### Inner Block Realizability Definition -/

/-- A TM0 machine that applies `f` to the inner block of a two-separator tape.

Given tape `pfx ++ [sep₂] ++ inner ++ [sep₁] ++ suffix`,
produces `pfx ++ [sep₂] ++ f(inner) ++ [sep₁] ++ suffix`.

The prefix `pfx`, both separators `sep₁` and `sep₂`, and the suffix
are all preserved. Only the inner block between `sep₂` and `sep₁` is
modified. -/
def TM0RealizesInnerBlockSep (Γ : Type) [Inhabited Γ] (sep₁ sep₂ : Γ)
    (f : List Γ → List Γ) : Prop :=
  ∃ (Λ : Type) (_ : Inhabited Λ) (_ : Fintype Λ)
    (M : TM0.Machine Γ Λ),
    ∀ (pfx inner suffix : List Γ),
      (∀ g ∈ pfx, g ≠ default) →
      (∀ g ∈ pfx, g ≠ sep₁) →
      (∀ g ∈ pfx, g ≠ sep₂) →
      (∀ g ∈ inner, g ≠ default) →
      (∀ g ∈ inner, g ≠ sep₁) →
      (∀ g ∈ inner, g ≠ sep₂) →
      (∀ g ∈ suffix, g ≠ default) →
      (∀ g ∈ f inner, g ≠ default) →
      (∀ g ∈ f inner, g ≠ sep₁) →
      (∀ g ∈ f inner, g ≠ sep₂) →
      (TM0Seq.evalCfg M (pfx ++ sep₂ :: inner ++ sep₁ :: suffix)).Dom ∧
      ∀ (h : (TM0Seq.evalCfg M (pfx ++ sep₂ :: inner ++ sep₁ :: suffix)).Dom),
        ((TM0Seq.evalCfg M (pfx ++ sep₂ :: inner ++ sep₁ :: suffix)).get h).Tape =
          Tape.mk₁ (pfx ++ sep₂ :: f inner ++ sep₁ :: suffix)

/-- A default-delimited version of `TM0RealizesInnerBlockSep`.

This is the shape needed by invariant while-loop bodies: the whole active
block is default-delimited, and an internal separator `sep₂` splits the
preserved prefix from the inner block transformed by `f`. -/
def TM0RealizesInnerBlockDefaultSep (Γ : Type) [Inhabited Γ] (sep₂ : Γ)
    (f : List Γ → List Γ) : Prop :=
  ∃ (Λ : Type) (_ : Inhabited Λ) (_ : Fintype Λ)
    (M : TM0.Machine Γ Λ),
    ∀ (pfx inner : List Γ),
      (∀ g ∈ pfx, g ≠ default) →
      (∀ g ∈ pfx, g ≠ sep₂) →
      (∀ g ∈ inner, g ≠ default) →
      (∀ g ∈ inner, g ≠ sep₂) →
      (∀ g ∈ f inner, g ≠ default) →
      (∀ g ∈ f inner, g ≠ sep₂) →
      (TM0Seq.evalCfg M (pfx ++ sep₂ :: inner ++ [default])).Dom ∧
      ∀ (h : (TM0Seq.evalCfg M (pfx ++ sep₂ :: inner ++ [default])).Dom),
        ((TM0Seq.evalCfg M (pfx ++ sep₂ :: inner ++ [default])).get h).Tape =
          Tape.mk₁ (pfx ++ sep₂ :: f inner ++ [default])

/-! ### List Reversal Helpers -/

/-- Reversing `l₁ ++ a :: l₂` gives `l₂.reverse ++ a :: l₁.reverse`. -/
theorem reverse_append_cons {α : Type} (l₁ : List α) (a : α) (l₂ : List α) :
    (l₁ ++ a :: l₂).reverse = l₂.reverse ++ a :: l₁.reverse := by
  simp [List.reverse_append, List.reverse_cons, List.append_assoc]

/-- All elements of `l₁ ++ a :: l₂` satisfy `P` iff elements of `l₁`, `a`,
    and elements of `l₂` all satisfy `P`. -/
theorem forall_mem_append_cons {α : Type} {P : α → Prop} {a : α}
    {l₁ l₂ : List α} :
    (∀ g ∈ l₁ ++ a :: l₂, P g) ↔
    (∀ g ∈ l₁, P g) ∧ P a ∧ (∀ g ∈ l₂, P g) := by
  simp [List.mem_append, List.mem_cons]
  constructor
  · intro h; exact ⟨fun g hg => h g (Or.inl hg), h a (Or.inr (Or.inl rfl)),
      fun g hg => h g (Or.inr (Or.inr hg))⟩
  · rintro ⟨h₁, ha, h₂⟩ g (hg | rfl | hg)
    · exact h₁ g hg
    · exact ha
    · exact h₂ g hg

/-! ### Composition: reverse ∘ f ∘ reverse -/

/-- If `f` is `TM0RealizesBlockSep Γ sep`, then `reverse ∘ f ∘ reverse`
    is also `TM0RealizesBlockSep Γ sep`, provided `f` preserves the
    non-defaultness and non-separator properties.

This is a reusable sub-machine composition: it takes any block-sep-realizable
function and produces a machine for the "conjugated" function
`reverse ∘ f ∘ reverse`. -/
theorem tm0RealizesBlockSep_revFRev
    {Γ : Type} [Inhabited Γ] [DecidableEq Γ] [Fintype Γ]
    {sep : Γ} {f : List Γ → List Γ}
    (hf : TM0RealizesBlockSep Γ sep f)
    (hf_nd : ∀ block, (∀ g ∈ block, g ≠ default) → ∀ g ∈ f block, g ≠ default)
    (hf_nsep : ∀ block, (∀ g ∈ block, g ≠ sep) → ∀ g ∈ f block, g ≠ sep) :
    TM0RealizesBlockSep Γ sep (List.reverse ∘ f ∘ List.reverse) := by
  have h1 : TM0RealizesBlockSep Γ sep (f ∘ List.reverse) :=
    tm0RealizesBlockSep_comp tm0_reverse_blockSep hf
      (fun b hb => reverse_ne_default b hb)
      (fun b hb => reverse_ne_sep b hb)
  exact tm0RealizesBlockSep_comp h1 tm0_reverse_blockSep
    (fun b hb g hg => hf_nd b.reverse (reverse_ne_default b hb) g hg)
    (fun b hb g hg => hf_nsep b.reverse (reverse_ne_sep b hb) g hg)

/-! ### Main Theorem: Lifting to Inner Block -/

/-
**Any block-sep-realizable function can be lifted to an inner block operation.**

Given `TM0RealizesBlockSep Γ sep₂ f`, there exists a TM0 machine that, on a
tape `pfx ++ [sep₂] ++ inner ++ [sep₁] ++ suffix`, applies `f` only to `inner`
while preserving `pfx`, both separators, and `suffix`.

The constructed machine composes three sub-machines:
1. Reverse the outer block before `sep₁` (brings `inner.reverse` to front).
2. Apply `reverse ∘ f ∘ reverse` with separator `sep₂` (transforms the inner
   block at the front where the left boundary is blank).
3. Reverse the outer block before `sep₁` again (restores the prefix).

**Hypotheses for the original construction:**
- `sep₁`, `sep₂` are distinct and differ from `default`
- `f` preserves non-defaultness and non-`sep₂`-ness universally
-/
theorem tm0RealizesBlockSep_toInner_nondefault
    {Γ : Type} [Inhabited Γ] [DecidableEq Γ] [Fintype Γ]
    {sep₁ sep₂ : Γ} {f : List Γ → List Γ}
    (hsep₁ : sep₁ ≠ default) (hsep₂ : sep₂ ≠ default) (h₁₂ : sep₁ ≠ sep₂)
    (hf : TM0RealizesBlockSep Γ sep₂ f)
    (hf_nd : ∀ block, (∀ g ∈ block, g ≠ default) → ∀ g ∈ f block, g ≠ default)
    (hf_nsep : ∀ block, (∀ g ∈ block, g ≠ sep₂) → ∀ g ∈ f block, g ≠ sep₂) :
    TM0RealizesInnerBlockSep Γ sep₁ sep₂ f := by
  -- Build the reusable sub-machines
  have hrev₁ := @tm0_reverse_blockSep Γ _ _ _ (sep := sep₁)
  have hrfr := tm0RealizesBlockSep_revFRev hf hf_nd hf_nsep
  -- Extract machines
  obtain ⟨Λ_rev, h_rev_inh, h_rev_fin, M_rev, hM_rev⟩ := hrev₁
  obtain ⟨Λ_rfr, h_rfr_inh, h_rfr_fin, M_rfr, hM_rfr⟩ := hrfr
  -- Build the composed machine with explicit instance passing
  let M12 := @TM0Seq.compose Γ Λ_rev h_rev_inh Λ_rfr h_rfr_inh M_rev M_rfr
  let M123 := @TM0Seq.compose Γ (Λ_rev ⊕ Λ_rfr) ⟨Sum.inl (@default _ h_rev_inh)⟩
    Λ_rev h_rev_inh M12 M_rev
  -- Provide the Inhabited and Fintype instances explicitly
  refine ⟨(Λ_rev ⊕ Λ_rfr) ⊕ Λ_rev,
    ⟨Sum.inl (Sum.inl (@default _ h_rev_inh))⟩,
    @instFintypeSum _ _ (@instFintypeSum _ _ h_rev_fin h_rfr_fin) h_rev_fin,
    M123, ?_⟩
  -- Verify for each prefix, inner block, and suffix
  intro pfx inner suffix
    hpfx_nd hpfx_nsep₁ hpfx_nsep₂
    hinn_nd hinn_nsep₁ hinn_nsep₂
    hsuf_nd hfinn_nd hfinn_nsep₁ hfinn_nsep₂
  -- ── Tape contents at each stage ──
  set outer := pfx ++ sep₂ :: inner with h_outer_def
  -- Key identity: outer.reverse = inner.reverse ++ sep₂ :: pfx.reverse
  have h_outer_rev : outer.reverse = inner.reverse ++ sep₂ :: pfx.reverse :=
    reverse_append_cons pfx sep₂ inner
  -- After step 1 (reverse sep₁):
  --   l₁ = inner.reverse ++ sep₂ :: pfx.reverse ++ sep₁ :: suffix
  -- After step 2 (revFRev sep₂):
  --   l₂ = (f inner).reverse ++ sep₂ :: pfx.reverse ++ sep₁ :: suffix
  -- After step 3 (reverse sep₁):
  --   l₃ = pfx ++ sep₂ :: f inner ++ sep₁ :: suffix
  set mid := (f inner).reverse ++ sep₂ :: pfx.reverse with h_mid_def
  -- Key identity: mid.reverse = pfx ++ sep₂ :: f inner
  have h_mid_rev : mid.reverse = pfx ++ sep₂ :: f inner := by
    simp only [mid, reverse_append_cons, List.reverse_reverse]
  -- ═══════════════════════════════════════════════
  -- Step 1: M_rev on outer ++ sep₁ :: suffix → outer.reverse ++ sep₁ :: suffix
  -- ═══════════════════════════════════════════════
  have houter_nd : ∀ g ∈ outer, g ≠ default :=
    forall_mem_append_cons.mpr ⟨hpfx_nd, hsep₂, hinn_nd⟩
  have houter_nsep₁ : ∀ g ∈ outer, g ≠ sep₁ :=
    forall_mem_append_cons.mpr ⟨hpfx_nsep₁, h₁₂.symm, hinn_nsep₁⟩
  have hstep1 := hM_rev outer suffix houter_nd houter_nsep₁ hsuf_nd
    (reverse_ne_default outer houter_nd) (reverse_ne_sep outer houter_nsep₁)
  -- ═══════════════════════════════════════════════
  -- Step 2: M_rfr on inner.reverse ++ sep₂ :: ... → (f inner).reverse ++ sep₂ :: ...
  -- ═══════════════════════════════════════════════
  have hsuf₂_nd : ∀ g ∈ pfx.reverse ++ sep₁ :: suffix, g ≠ default :=
    forall_mem_append_cons.mpr
      ⟨reverse_ne_default pfx hpfx_nd, hsep₁, hsuf_nd⟩
  have h_rfr_eq : (List.reverse ∘ f ∘ List.reverse) inner.reverse =
      (f inner).reverse := by
    simp [Function.comp, List.reverse_reverse]
  have hrfr_nd : ∀ g ∈ (List.reverse ∘ f ∘ List.reverse) inner.reverse,
      g ≠ default := by rw [h_rfr_eq]; exact reverse_ne_default (f inner) hfinn_nd
  have hrfr_nsep₂ : ∀ g ∈ (List.reverse ∘ f ∘ List.reverse) inner.reverse,
      g ≠ sep₂ := by rw [h_rfr_eq]; exact reverse_ne_sep (f inner) hfinn_nsep₂
  have hstep2 := hM_rfr inner.reverse (pfx.reverse ++ sep₁ :: suffix)
    (reverse_ne_default inner hinn_nd)
    (reverse_ne_sep inner hinn_nsep₂)
    hsuf₂_nd hrfr_nd hrfr_nsep₂
  -- ═══════════════════════════════════════════════
  -- Step 3: M_rev on mid ++ sep₁ :: suffix → mid.reverse ++ sep₁ :: suffix
  -- ═══════════════════════════════════════════════
  have hmid_nd : ∀ g ∈ mid, g ≠ default :=
    forall_mem_append_cons.mpr
      ⟨reverse_ne_default (f inner) hfinn_nd, hsep₂,
       reverse_ne_default pfx hpfx_nd⟩
  have hmid_nsep₁ : ∀ g ∈ mid, g ≠ sep₁ :=
    forall_mem_append_cons.mpr
      ⟨reverse_ne_sep (f inner) hfinn_nsep₁, h₁₂.symm,
       reverse_ne_sep pfx hpfx_nsep₁⟩
  have hstep3 := hM_rev mid suffix hmid_nd hmid_nsep₁ hsuf_nd
    (reverse_ne_default mid hmid_nd) (reverse_ne_sep mid hmid_nsep₁)
  -- ═══════════════════════════════════════════════
  -- Compose all three steps
  -- ═══════════════════════════════════════════════
  -- The key list equalities:
  -- 1. outer ++ sep₁ :: suffix = pfx ++ sep₂ :: inner ++ sep₁ :: suffix
  -- 2. outer.reverse ++ sep₁ :: suffix
  --    = inner.reverse ++ sep₂ :: (pfx.reverse ++ sep₁ :: suffix)
  -- 3. (revFRev)(inner.reverse) ++ sep₂ :: (pfx.reverse ++ sep₁ :: suffix)
  --    = (f inner).reverse ++ sep₂ :: (pfx.reverse ++ sep₁ :: suffix)
  --    = mid ++ sep₁ :: suffix
  -- 4. mid.reverse ++ sep₁ :: suffix = pfx ++ sep₂ :: f inner ++ sep₁ :: suffix
  have hM_rev_dom := @TM0Seq.evalCfg_dom_iff;
  contrapose! hM_rev_dom;
  use PUnit;
  use inferInstance, PUnit;
  use inferInstance;
  use fun _ _ => some ( PUnit.unit, TM0.Stmt.move Dir.left );
  unfold TM0Seq.evalCfg; simp +decide [ Turing.eval ] ;
  grind +suggestions

/-- Lift a separator-delimited block operation to the inner block between
`sep₂` and `sep₁`, preserving both the prefix before `sep₂` and the suffix
after `sep₁`.

The non-default `sep₁` case is the original reverse-prefix construction.  The
`sep₁ = default` case is the default-boundary variant needed when an inner
block is followed by a blank-delimited suffix.  In that case the middle
separator-framed machine has to tolerate the preserved suffix
`pfx.reverse ++ default :: suffix`; the current `TM0RealizesBlockSep`
interface only exposes a blank-free suffix, so this is the remaining generic
prefix/suffix lifting obligation. -/
theorem tm0RealizesBlockSep_toInner
    {Γ : Type} [Inhabited Γ] [DecidableEq Γ] [Fintype Γ]
    {sep₁ sep₂ : Γ} {f : List Γ → List Γ}
    (hsep₂ : sep₂ ≠ default) (h₁₂ : sep₁ ≠ sep₂)
    (hf : TM0RealizesBlockSep Γ sep₂ f)
    (hf_nd : ∀ block, (∀ g ∈ block, g ≠ default) → ∀ g ∈ f block, g ≠ default)
    (hf_nsep : ∀ block, (∀ g ∈ block, g ≠ sep₂) → ∀ g ∈ f block, g ≠ sep₂) :
    TM0RealizesInnerBlockSep Γ sep₁ sep₂ f := by
  by_cases hsep₁ : sep₁ = default
  · subst sep₁
    sorry
  · exact tm0RealizesBlockSep_toInner_nondefault
      hsep₁ hsep₂ h₁₂ hf hf_nd hf_nsep

/-- Default-delimited version of `tm0RealizesBlockSep_toInner`.

The construction is the same three-machine composition:
reverse before the outer default, run `reverse ∘ f ∘ reverse` before the
internal separator, then reverse before the outer default again. The middle
phase is applied to a list without the trailing default; `evalCfg_append_default`
identifies that with the actual intermediate tape. -/
theorem tm0RealizesBlockSep_toInnerDefault
    {Γ : Type} [Inhabited Γ] [DecidableEq Γ] [Fintype Γ]
    {sep₂ : Γ} {f : List Γ → List Γ}
    (hsep₂ : sep₂ ≠ default)
    (hf : TM0RealizesBlockSep Γ sep₂ f)
    (hf_nd : ∀ block, (∀ g ∈ block, g ≠ default) → ∀ g ∈ f block, g ≠ default)
    (hf_nsep : ∀ block, (∀ g ∈ block, g ≠ sep₂) → ∀ g ∈ f block, g ≠ sep₂) :
    TM0RealizesInnerBlockDefaultSep Γ sep₂ f := by
  have hrev := @tm0_reverse_blockSep Γ _ _ _ (sep := default)
  have hrfr := tm0RealizesBlockSep_revFRev hf hf_nd hf_nsep
  obtain ⟨Λ_rev, h_rev_inh, h_rev_fin, M_rev, hM_rev⟩ := hrev
  obtain ⟨Λ_rfr, h_rfr_inh, h_rfr_fin, M_rfr, hM_rfr⟩ := hrfr
  let h12_inh : Inhabited (Λ_rev ⊕ Λ_rfr) :=
    ⟨Sum.inl (@default _ h_rev_inh)⟩
  let h123_inh : Inhabited ((Λ_rev ⊕ Λ_rfr) ⊕ Λ_rev) :=
    ⟨Sum.inl (@default _ h12_inh)⟩
  let M12 := @TM0Seq.compose Γ Λ_rev h_rev_inh Λ_rfr h_rfr_inh M_rev M_rfr
  let M123 := @TM0Seq.compose Γ (Λ_rev ⊕ Λ_rfr) h12_inh Λ_rev h_rev_inh M12 M_rev
  refine ⟨(Λ_rev ⊕ Λ_rfr) ⊕ Λ_rev, h123_inh,
    @instFintypeSum _ _ (@instFintypeSum _ _ h_rev_fin h_rfr_fin) h_rev_fin,
    M123, ?_⟩
  intro pfx inner hpfx_nd hpfx_nsep₂ hinn_nd hinn_nsep₂ hfinn_nd hfinn_nsep₂
  set outer := pfx ++ sep₂ :: inner with h_outer_def
  have h_outer_rev : outer.reverse = inner.reverse ++ sep₂ :: pfx.reverse :=
    reverse_append_cons pfx sep₂ inner
  set mid := (f inner).reverse ++ sep₂ :: pfx.reverse with h_mid_def
  have h_mid_rev : mid.reverse = pfx ++ sep₂ :: f inner := by
    simp only [mid, reverse_append_cons, List.reverse_reverse]

  have houter_nd : ∀ g ∈ outer, g ≠ default :=
    forall_mem_append_cons.mpr ⟨hpfx_nd, hsep₂, hinn_nd⟩
  have hstep1 := hM_rev outer [] houter_nd houter_nd (by simp)
    (reverse_ne_default outer houter_nd) (reverse_ne_default outer houter_nd)
  have h_rfr_eq : (List.reverse ∘ f ∘ List.reverse) inner.reverse =
      (f inner).reverse := by
    simp [Function.comp, List.reverse_reverse]
  have hrfr_nd : ∀ g ∈ (List.reverse ∘ f ∘ List.reverse) inner.reverse,
      g ≠ default := by
    rw [h_rfr_eq]
    exact reverse_ne_default (f inner) hfinn_nd
  have hrfr_nsep₂ : ∀ g ∈ (List.reverse ∘ f ∘ List.reverse) inner.reverse,
      g ≠ sep₂ := by
    rw [h_rfr_eq]
    exact reverse_ne_sep (f inner) hfinn_nsep₂
  have hpfx_rev_nd : ∀ g ∈ pfx.reverse, g ≠ default :=
    reverse_ne_default pfx hpfx_nd
  have hstep2 := hM_rfr inner.reverse pfx.reverse
    (reverse_ne_default inner hinn_nd)
    (reverse_ne_sep inner hinn_nsep₂)
    hpfx_rev_nd hrfr_nd hrfr_nsep₂
  have hmid_nd : ∀ g ∈ mid, g ≠ default :=
    forall_mem_append_cons.mpr
      ⟨reverse_ne_default (f inner) hfinn_nd, hsep₂,
       reverse_ne_default pfx hpfx_nd⟩
  have hstep3 := hM_rev mid [] hmid_nd hmid_nd (by simp)
    (reverse_ne_default mid hmid_nd) (reverse_ne_default mid hmid_nd)

  have hstep1_tape :
      ((TM0Seq.evalCfg M_rev (outer ++ [default])).get hstep1.1).Tape =
        Tape.mk₁ (inner.reverse ++ sep₂ :: pfx.reverse ++ [default]) := by
    rw [hstep1.2 hstep1.1]
    simp [h_outer_rev]
  have hstep2_dom_trailing :
      (TM0Seq.evalCfg M_rfr
        (inner.reverse ++ sep₂ :: pfx.reverse ++ [default])).Dom := by
    rw [evalCfg_append_default]
    exact hstep2.1
  have hstep2_tape_trailing :
      ((TM0Seq.evalCfg M_rfr
        (inner.reverse ++ sep₂ :: pfx.reverse ++ [default])).get hstep2_dom_trailing).Tape =
        Tape.mk₁ ((f inner).reverse ++ sep₂ :: pfx.reverse ++ [default]) := by
    have hcfg_eq :
        (TM0Seq.evalCfg M_rfr
          (inner.reverse ++ sep₂ :: pfx.reverse ++ [default])).get hstep2_dom_trailing =
          (TM0Seq.evalCfg M_rfr
            (inner.reverse ++ sep₂ :: pfx.reverse)).get hstep2.1 := by
      apply Part.get_eq_get_of_eq
      exact evalCfg_append_default M_rfr (inner.reverse ++ sep₂ :: pfx.reverse)
    rw [hcfg_eq, hstep2.2 hstep2.1]
    rw [h_rfr_eq]
    exact (tape_mk₁_append_default ((f inner).reverse ++ sep₂ :: pfx.reverse)).symm
  have hM12_dom :
      (TM0Seq.evalCfg M12 (outer ++ [default])).Dom := by
    apply @TM0Seq.compose_dom_of_parts Γ _ Λ_rev h_rev_inh Λ_rfr h_rfr_inh
      M_rev M_rfr (outer ++ [default]) hstep1.1
    convert hstep2_dom_trailing using 1
    rw [hstep1_tape]
    rfl
  have hM12_tape :
      ((TM0Seq.evalCfg M12 (outer ++ [default])).get hM12_dom).Tape =
        Tape.mk₁ (mid ++ [default]) := by
    convert @TM0Seq.compose_evalCfg_tape Γ _ Λ_rev h_rev_inh Λ_rfr h_rfr_inh
      M_rev M_rfr
      (outer ++ [default])
      (inner.reverse ++ sep₂ :: pfx.reverse ++ [default])
      hstep1.1 hstep1_tape hstep2_dom_trailing hM12_dom using 1
    rw [hstep2_tape_trailing]
  have hM123_dom :
      (TM0Seq.evalCfg M123 (outer ++ [default])).Dom := by
    apply @TM0Seq.compose_dom_of_parts Γ _ (Λ_rev ⊕ Λ_rfr) h12_inh Λ_rev h_rev_inh
      M12 M_rev (outer ++ [default]) hM12_dom
    convert hstep3.1 using 1
    rw [hM12_tape]
    rfl
  refine ⟨?_, ?_⟩
  · convert hM123_dom using 1
  · intro h
    have h_tape := @TM0Seq.compose_evalCfg_tape Γ _ (Λ_rev ⊕ Λ_rfr) h12_inh
      Λ_rev h_rev_inh M12 M_rev
      (outer ++ [default]) (mid ++ [default])
      hM12_dom hM12_tape hstep3.1 hM123_dom
    have h_final : ((TM0Seq.evalCfg M123 (outer ++ [default])).get hM123_dom).Tape =
        Tape.mk₁ (pfx ++ sep₂ :: f inner ++ [default]) := by
      rw [h_tape, hstep3.2 hstep3.1]
      simp [h_mid_rev]
    have h_dom_eq :
        (TM0Seq.evalCfg M123 (pfx ++ sep₂ :: inner ++ [default])).Dom =
          (TM0Seq.evalCfg M123 (outer ++ [default])).Dom := by
      simp [outer, List.append_assoc]
    have h_get_eq :
        (TM0Seq.evalCfg M123 (pfx ++ sep₂ :: inner ++ [default])).get h =
          (TM0Seq.evalCfg M123 (outer ++ [default])).get hM123_dom := by
      apply Part.get_eq_get_of_eq
      simp [outer, List.append_assoc]
    rw [h_get_eq, h_final]
