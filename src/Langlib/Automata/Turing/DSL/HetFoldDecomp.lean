import Mathlib
import Langlib.Automata.Turing.DSL.BlockRealizability
import Langlib.Automata.Turing.DSL.PairedAddHelpers

/-! # Heterogeneous Fold via Reverse + While Loop

This file decomposes `tm0Het_fold_blockRealizable` into two
`TM0RealizesBlock` operations:

1. **Reverse**: `TM0RealizesBlock _ List.reverse` (from `tm0_reverse_block`)
2. **While loop**: `TM0RealizesBlock _ (hetFoldWhile f)`, where the body
   pops the leftmost `Sum.inl` tag and applies `f` to the accumulator.

## Architecture

The while-loop body is expressed as a `TM0RealizesBlockCond`, which extends
`TM0RealizesBlock` with conditional halting: the body machine halts at a
designated continuation state `q_cont` when the loop should continue (an
`inl` tag was processed), and at a different state when no `inl` tag
remains (loop terminates).

The general combinator `tm0RealizesBlock_while` builds a `TM0RealizesBlock`
from a `TM0RealizesBlockCond` body using `tm0WhileLoop`.

### Tape Layout

Throughout the while loop, the tape holds a single contiguous non-default
block of the form:

```
  [some(inl tⱼ), ..., some(inl t₁), some(inr g₁), ..., some(inr gₖ)]
```

where `tⱼ, ..., t₁` are the remaining unprocessed tags and
`g₁, ..., gₖ` is the current accumulator. All elements are `some _`,
hence non-default (`none`), so this is a valid block for
`TM0RealizesBlock (Option (T ⊕ Γ₀))`.

### Fold Identity

The fold identity `List.foldr f [] w = List.foldl (fun a t => f t a) [] w.reverse`
connects the right-to-left fold to the left-to-right while loop on the
reversed input.
-/

open Turing

/-! ## Conditional Block Realizability -/

/-- A TM0 block step with conditional continuation.

When `cond block` holds: transforms block to `step block`, halts at `q_cont`.
When `¬cond block`: leaves block unchanged, halts at state ≠ `q_cont`.

This models a single iteration of a while loop body. The halting state
signals whether the loop should continue or terminate. -/
def TM0RealizesBlockCond {Γ : Type} [Inhabited Γ]
    (step : List Γ → List Γ) (cond : List Γ → Prop) [DecidablePred cond] : Prop :=
  ∃ (Λ : Type) (_ : Inhabited Λ) (_ : Fintype Λ)
    (M : TM0.Machine Γ Λ) (q_cont : Λ),
    ∀ (block suffix : List Γ),
      (∀ g ∈ block, g ≠ default) →
      (∀ g ∈ suffix, g ≠ default) →
      (cond block → ∀ g ∈ step block, g ≠ default) →
      (TM0Seq.evalCfg M (block ++ default :: suffix)).Dom ∧
      ∀ (h : (TM0Seq.evalCfg M (block ++ default :: suffix)).Dom),
        let cfg := (TM0Seq.evalCfg M (block ++ default :: suffix)).get h
        if cond block then
          cfg.q = q_cont ∧
          cfg.Tape = Tape.mk₁ (step block ++ default :: suffix)
        else
          cfg.q ≠ q_cont ∧
          cfg.Tape = Tape.mk₁ (block ++ default :: suffix)

/-! ## Fuel-Bounded While-Loop Iteration -/

/-- Iterate a step function while a condition holds, bounded by fuel.
    Returns the block after at most `n` applications of `step`. -/
def blockIterateWhile {Γ : Type} (step : List Γ → List Γ) (cond : List Γ → Prop)
    [DecidablePred cond] : ℕ → List Γ → List Γ
  | 0, block => block
  | n + 1, block => if cond block then blockIterateWhile step cond n (step block) else block

theorem blockIterateWhile_succ_true {Γ : Type} (step : List Γ → List Γ) (cond : List Γ → Prop)
    [DecidablePred cond] (n : ℕ) (block : List Γ) (hcond : cond block) :
    blockIterateWhile step cond (n + 1) block =
      blockIterateWhile step cond n (step block) := by
  simp [blockIterateWhile, hcond]

theorem blockIterateWhile_succ_false {Γ : Type} (step : List Γ → List Γ) (cond : List Γ → Prop)
    [DecidablePred cond] (n : ℕ) (block : List Γ) (hcond : ¬cond block) :
    blockIterateWhile step cond (n + 1) block = block := by
  simp [blockIterateWhile, hcond]

/-! ## While-Loop Helper Lemmas -/

/-
When body M halts at state q ≠ q_cont, the while loop `tm0WhileLoop M q_cont`
    also halts with the body's output tape.

    Proof: M's trajectory from init(l) to cfg is replayed by W (via
    `tm0WhileLoop_reaches_of_M`). At cfg, M halts and cfg.q ≠ q_cont,
    so W also halts (via `tm0WhileLoop_halt`).
-/
theorem whileLoop_eval_not_cont
    {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ] [DecidableEq Λ]
    (M : TM0.Machine Γ Λ) (q_cont : Λ) (l : List Γ)
    (h_body_dom : (TM0Seq.evalCfg M l).Dom)
    (h_body_q : ((TM0Seq.evalCfg M l).get h_body_dom).q ≠ q_cont) :
    (TM0Seq.evalCfg (tm0WhileLoop M q_cont) l).Dom ∧
    ∀ (h : (TM0Seq.evalCfg (tm0WhileLoop M q_cont) l).Dom),
      ((TM0Seq.evalCfg (tm0WhileLoop M q_cont) l).get h).Tape =
      ((TM0Seq.evalCfg M l).get h_body_dom).Tape := by
  obtain ⟨c, hc⟩ : ∃ c : TM0.Cfg Γ Λ, Reaches (TM0.step M) (TM0.init l) c ∧ TM0.step M c = none ∧ c.Tape = ((TM0Seq.evalCfg M l).get h_body_dom).Tape ∧ c.q = ((TM0Seq.evalCfg M l).get h_body_dom).q := by
    have := Turing.mem_eval.mp ( ( TM0Seq.evalCfg M l ).get_mem h_body_dom );
    exact ⟨ _, this.1, this.2, rfl, rfl ⟩;
  obtain ⟨h_reaches, h_halt, h_tape, h_q⟩ := hc;
  have h_reaches_while : Reaches (TM0.step (tm0WhileLoop M q_cont)) (TM0.init l) c := by
    exact tm0WhileLoop_reaches_of_M M q_cont (TM0.init l) c h_reaches
  have h_halt_while : TM0.step (tm0WhileLoop M q_cont) c = none := by
    unfold TM0.step at *;
    unfold tm0WhileLoop at *;
    grind;
  have h_eval_while : c ∈ TM0Seq.evalCfg (tm0WhileLoop M q_cont) l := by
    apply Turing.mem_eval.mpr;
    exact ⟨ h_reaches_while, h_halt_while ⟩;
  grind +suggestions

/-
At a configuration where M halts at q_cont, the while loop W's step
    from `⟨q_cont, T⟩` equals W's step from `⟨default, T⟩`.

    Both evaluate to `(M default T.head).map ...` because:
    - W q_cont T.head = M default T.head (restart branch of tm0WhileLoop)
    - W default T.head = M default T.head (either M steps, or M halts and
      the `if default = q_cont` branch also gives M default T.head or none)
-/
theorem whileLoop_step_restart_eq
    {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ] [DecidableEq Λ]
    (M : TM0.Machine Γ Λ) (q_cont : Λ) (T : Tape Γ)
    (h_halt : M q_cont T.head = none) :
    TM0.step (tm0WhileLoop M q_cont) ⟨q_cont, T⟩ =
    TM0.step (tm0WhileLoop M q_cont) ⟨default, T⟩ := by
  unfold tm0WhileLoop;
  unfold TM0.step; aesop;

/-
When body M halts at q_cont with tape `Tape.mk₁ l'`, and the while loop
    W = `tm0WhileLoop M q_cont` is Dom on l', then W is also Dom on l
    and produces the same output tape as W on l'.

    Proof: W replays M's trajectory reaching `⟨q_cont, Tape.mk₁ l'⟩`.
    At this point, M halts but W restarts: `W q_cont head = M default head`.
    - If `M default head = some (q', s)`: both W from `⟨q_cont, tape⟩` and
      W from `⟨default, tape⟩` step to the same `⟨q', tape'⟩`, so by
      `reaches_eval` their evals are equal.
    - If `M default head = none`: both W from `⟨q_cont, tape⟩` and
      W from `⟨default, tape⟩` halt immediately with the same tape.
-/
theorem whileLoop_eval_cont
    {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ] [DecidableEq Λ]
    (M : TM0.Machine Γ Λ) (q_cont : Λ) (l l' : List Γ)
    (h_body_dom : (TM0Seq.evalCfg M l).Dom)
    (h_body_q : ((TM0Seq.evalCfg M l).get h_body_dom).q = q_cont)
    (h_body_tape : ((TM0Seq.evalCfg M l).get h_body_dom).Tape = Tape.mk₁ l')
    (h_W_dom' : (TM0Seq.evalCfg (tm0WhileLoop M q_cont) l').Dom) :
    (TM0Seq.evalCfg (tm0WhileLoop M q_cont) l).Dom ∧
    ∀ (h : (TM0Seq.evalCfg (tm0WhileLoop M q_cont) l).Dom),
      ((TM0Seq.evalCfg (tm0WhileLoop M q_cont) l).get h).Tape =
      ((TM0Seq.evalCfg (tm0WhileLoop M q_cont) l').get h_W_dom').Tape := by
  obtain ⟨c, hc⟩ : ∃ c : TM0.Cfg Γ Λ, Reaches (TM0.step M) (TM0.init l) c ∧ TM0.step M c = none ∧ c.q = q_cont ∧ c.Tape = Tape.mk₁ l' := by
    have := Part.get_mem h_body_dom;
    exact ⟨ _, mem_eval.mp this |>.1, mem_eval.mp this |>.2, h_body_q, h_body_tape ⟩;
  have h_reach : Reaches (TM0.step (tm0WhileLoop M q_cont)) (TM0.init l) c := by
    exact tm0WhileLoop_reaches_of_M _ _ _ _ hc.1;
  have h_reach' : TM0.step (tm0WhileLoop M q_cont) c = TM0.step (tm0WhileLoop M q_cont) (TM0.init l') := by
    convert whileLoop_step_restart_eq M q_cont ( Tape.mk₁ l' ) _;
    · exact hc.2.2.1;
    · exact hc.2.2.2;
    · unfold TM0.step at hc; aesop;
  cases h : TM0.step ( tm0WhileLoop M q_cont ) c <;> simp_all +decide [ TM0Seq.evalCfg ];
  · rw [ eq_comm ] at h_reach';
    have h_eval_eq : ∀ (c₁ c₂ : TM0.Cfg Γ Λ), Reaches (TM0.step (tm0WhileLoop M q_cont)) c₁ c₂ → TM0.step (tm0WhileLoop M q_cont) c₂ = none → (eval (TM0.step (tm0WhileLoop M q_cont)) c₁).Dom ∧ ∀ (h : (eval (TM0.step (tm0WhileLoop M q_cont)) c₁).Dom), ((eval (TM0.step (tm0WhileLoop M q_cont)) c₁).get h) = c₂ := by
      intros c₁ c₂ h_reach h_step_none
      apply And.intro;
      · apply Part.dom_iff_mem.mpr;
        use c₂;
        grind +suggestions;
      · intro h_dom
        have h_eval_eq : c₂ ∈ eval (TM0.step (tm0WhileLoop M q_cont)) c₁ := by
          grind +suggestions;
        exact Part.get_eq_of_mem h_eval_eq h_dom
    have := h_eval_eq _ _ h_reach ( by aesop );
    have := h_eval_eq _ _ ( Relation.ReflTransGen.refl ) h_reach'; aesop;
  · have h_reach'' : Reaches (TM0.step (tm0WhileLoop M q_cont)) (TM0.init l) ‹_› := by
      exact h_reach.tail ( by aesop )
    have h_reach''' : Reaches (TM0.step (tm0WhileLoop M q_cont)) (TM0.init l') ‹_› := by
      exact Relation.ReflTransGen.single ( by aesop )
    have h_eval_eq : eval (TM0.step (tm0WhileLoop M q_cont)) (TM0.init l) = eval (TM0.step (tm0WhileLoop M q_cont)) ‹_› := by
      apply_rules [ Turing.reaches_eval ]
    have h_eval_eq' : eval (TM0.step (tm0WhileLoop M q_cont)) (TM0.init l') = eval (TM0.step (tm0WhileLoop M q_cont)) ‹_› := by
      apply Turing.reaches_eval; assumption;
    simp_all +decide [ TM0Seq.evalCfg ];
    exact h_eval_eq'.symm ▸ h_W_dom'

/-! ## While-Loop Block Realizability Combinator -/

/-- **While-loop block realizability combinator.**

Given a conditionally block-realizable body (`TM0RealizesBlockCond`),
a `result` function that equals the iterated application of `step`
with sufficient fuel, the result function is block-realizable.

The TM0 machine is built using `tm0WhileLoop M_body q_cont`, which
reruns `M_body` whenever it halts at `q_cont`, and halts when
`M_body` halts at any other state. -/
theorem tm0RealizesBlock_while {Γ : Type} [Inhabited Γ] [DecidableEq Γ] [Fintype Γ]
    (step result : List Γ → List Γ) (cond : List Γ → Prop) [DecidablePred cond]
    (hbody : TM0RealizesBlockCond step cond)
    (hstep_nd : ∀ block, (∀ g ∈ block, g ≠ default) → cond block →
      ∀ g ∈ step block, g ≠ default)
    (hresult_eq : ∀ block, (∀ g ∈ block, g ≠ default) →
      ∃ n, result block = blockIterateWhile step cond n block ∧
        ¬cond (blockIterateWhile step cond n block))
    (hresult_nd : ∀ block, (∀ g ∈ block, g ≠ default) →
      ∀ g ∈ result block, g ≠ default) :
    TM0RealizesBlock Γ result := by
  obtain ⟨Λ, hΛi, hΛf, M, q_cont, hM⟩ := hbody
  haveI : DecidableEq Λ := Classical.decEq Λ
  refine ⟨Λ, hΛi, hΛf, tm0WhileLoop M q_cont, ?_⟩
  intro block suffix hblock hsuffix hresult
  obtain ⟨n, hn_eq, hn_not_cond⟩ := hresult_eq block hblock
  -- Key inductive claim: the while loop computes blockIterateWhile
  suffices key : ∀ (m : ℕ) (blk : List Γ),
    (∀ g ∈ blk, g ≠ default) →
    ¬cond (blockIterateWhile step cond m blk) →
    (TM0Seq.evalCfg (tm0WhileLoop M q_cont) (blk ++ default :: suffix)).Dom ∧
    ∀ (hd : (TM0Seq.evalCfg (tm0WhileLoop M q_cont) (blk ++ default :: suffix)).Dom),
      ((TM0Seq.evalCfg (tm0WhileLoop M q_cont) (blk ++ default :: suffix)).get hd).Tape =
      Tape.mk₁ (blockIterateWhile step cond m blk ++ default :: suffix) by
    obtain ⟨h_dom, h_tape⟩ := key n block hblock hn_not_cond
    exact ⟨h_dom, fun hd => by rw [hn_eq, h_tape hd]⟩
  intro m
  induction m with
  | zero =>
    intro blk hblk hn_not
    simp only [blockIterateWhile] at hn_not ⊢
    obtain ⟨h_body_dom, h_body_spec⟩ := hM blk suffix hblk hsuffix
      (fun hc => hstep_nd blk hblk hc)
    have h_body_spec' := h_body_spec h_body_dom
    simp only [hn_not, ↓reduceIte] at h_body_spec'
    obtain ⟨h_q_ne, h_tape_eq⟩ := h_body_spec'
    obtain ⟨h_dom, h_tape⟩ := whileLoop_eval_not_cont M q_cont _ h_body_dom h_q_ne
    exact ⟨h_dom, fun hd => by rw [h_tape hd, h_tape_eq]⟩
  | succ m ih =>
    intro blk hblk hn_not
    by_cases hcond : cond blk
    · -- cond blk: body halts at q_cont, while loop continues on step blk
      rw [blockIterateWhile_succ_true _ _ _ _ hcond] at hn_not ⊢
      have h_step_nd := hstep_nd blk hblk hcond
      obtain ⟨h_body_dom, h_body_spec⟩ := hM blk suffix hblk hsuffix
        (fun _ => h_step_nd)
      have h_body_spec' := h_body_spec h_body_dom
      simp only [hcond, ↓reduceIte] at h_body_spec'
      obtain ⟨h_q_cont, h_tape_step⟩ := h_body_spec'
      obtain ⟨h_W_step_dom, h_W_step_tape⟩ := ih (step blk) h_step_nd hn_not
      obtain ⟨h_W_dom, h_W_tape⟩ := whileLoop_eval_cont M q_cont _ _
        h_body_dom h_q_cont h_tape_step h_W_step_dom
      exact ⟨h_W_dom, fun hd => by rw [h_W_tape hd, h_W_step_tape h_W_step_dom]⟩
    · -- ¬cond blk: blockIterateWhile (m+1) = blk
      rw [blockIterateWhile_succ_false _ _ _ _ hcond] at hn_not ⊢
      obtain ⟨h_body_dom, h_body_spec⟩ := hM blk suffix hblk hsuffix
        (fun hc => absurd hc hcond)
      have h_body_spec' := h_body_spec h_body_dom
      simp only [hcond, ↓reduceIte] at h_body_spec'
      obtain ⟨h_q_ne, h_tape_eq⟩ := h_body_spec'
      obtain ⟨h_dom, h_tape⟩ := whileLoop_eval_not_cont M q_cont _ h_body_dom h_q_ne
      exact ⟨h_dom, fun hd => by rw [h_tape hd, h_tape_eq]⟩

/-! ## Heterogeneous Fold Definitions -/

section HetFold

variable {T : Type} [DecidableEq T] [Fintype T]
variable {Γ₀ : Type} [Inhabited Γ₀] [DecidableEq Γ₀] [Fintype Γ₀]

/-- Check if a het block element is an `inl` tag. -/
def isHetInl (x : Option (T ⊕ Γ₀)) : Bool :=
  match x with | some (Sum.inl _) => true | _ => false

/-- Condition: block starts with an `inl` tag (signals the while loop
    should continue). -/
def hasHetInlHead : List (Option (T ⊕ Γ₀)) → Prop
  | (some (Sum.inl _)) :: _ => True
  | _ => False

instance : DecidablePred (@hasHetInlHead T Γ₀) := fun block =>
  match block with
  | (some (Sum.inl _)) :: _ => isTrue trivial
  | [] => isFalse (by simp [hasHetInlHead])
  | none :: _ => isFalse (by simp [hasHetInlHead])
  | (some (Sum.inr _)) :: _ => isFalse (by simp [hasHetInlHead])

/-- Mixed het block representation: `inl` tags followed by `inr` accumulator. -/
def hetMix (ts : List T) (acc : List Γ₀) : List (Option (T ⊕ Γ₀)) :=
  ts.map (some ∘ Sum.inl) ++ acc.map (some ∘ Sum.inr)

/-- One step of the het fold while loop.
    Pops the leftmost `inl t` tag and applies `f t` to the `inr` accumulator.

    On a block `hetMix (t :: ts) acc`, produces `hetMix ts (f t acc)`. -/
noncomputable def hetFoldStep
    (f : T → List Γ₀ → List Γ₀) :
    List (Option (T ⊕ Γ₀)) → List (Option (T ⊕ Γ₀))
  | (some (Sum.inl t)) :: rest =>
    let inlTail := rest.takeWhile (isHetInl (T := T) (Γ₀ := Γ₀))
    let inrPart := rest.dropWhile (isHetInl (T := T) (Γ₀ := Γ₀))
    let acc := inrPart.filterMap
      (fun x => match x with | some (Sum.inr g) => some g | _ => none)
    inlTail ++ (f t acc).map (some ∘ Sum.inr)
  | block => block

/-- The full while-loop result function, defined as iterated application
    of `hetFoldStep` with fuel equal to the number of leading `inl` tags.

    This directly models what the `tm0WhileLoop` machine computes:
    iterate `hetFoldStep` while `hasHetInlHead`, stopping when no more
    `inl` tags remain at the head. -/
noncomputable def hetFoldWhile
    (f : T → List Γ₀ → List Γ₀)
    (block : List (Option (T ⊕ Γ₀))) : List (Option (T ⊕ Γ₀)) :=
  blockIterateWhile (hetFoldStep f) hasHetInlHead
    (block.takeWhile (isHetInl (T := T) (Γ₀ := Γ₀))).length block

/-! ## Mathematical Correctness -/

/-- `hetMix` with a non-empty tag list starts with `inl`. -/
theorem hasHetInlHead_hetMix_cons (t : T) (ts : List T) (acc : List Γ₀) :
    hasHetInlHead (hetMix (t :: ts) acc) := by
  simp [hetMix, hasHetInlHead]

/-- `hetMix` with empty tag list does NOT start with `inl`. -/
theorem not_hasHetInlHead_hetMix_nil (acc : List Γ₀) :
    ¬hasHetInlHead (hetMix ([] : List T) acc) := by
  simp only [hetMix, List.map, List.nil_append]
  cases acc with
  | nil => simp [hasHetInlHead]
  | cons a rest => simp [hasHetInlHead]

/-- One step is correct on `hetMix`: pops the head tag and applies `f`. -/
theorem hetFoldStep_hetMix
    (f : T → List Γ₀ → List Γ₀) (t : T) (ts : List T) (acc : List Γ₀) :
    hetFoldStep f (hetMix (t :: ts) acc) = hetMix ts (f t acc) := by
  unfold hetFoldStep
  unfold hetMix; simp +decide [isHetInl]
  rw [List.takeWhile_eq_nil_iff.mpr]
  · rw [show List.dropWhile isHetInl (List.map (some ∘ Sum.inr) acc) =
        List.map (some ∘ Sum.inr) acc from ?_]
    · rw [List.filterMap_map]
      rw [List.filterMap_congr]
      rotate_right
      exacts [fun x => some x, by simp +decide, fun x hx => rfl]
    · induction acc <;> simp +decide [*, isHetInl]
  · unfold isHetInl; aesop

/-
The `takeWhile isHetInl` length of `hetMix ts acc` is `ts.length`.
-/
theorem takeWhile_isHetInl_hetMix (ts : List T) (acc : List Γ₀) :
    (hetMix (T := T) (Γ₀ := Γ₀) ts acc).takeWhile
      (isHetInl (T := T) (Γ₀ := Γ₀)) = ts.map (some ∘ Sum.inl) := by
  induction' ts with t ts ih;
  · unfold hetMix;
    induction acc <;> aesop;
  · convert congr_arg ( fun l => some ( Sum.inl t ) :: l ) ih using 1

/-- `hetFoldWhile` is correct on `hetMix`: computes `foldl`. -/
theorem hetFoldWhile_hetMix
    (f : T → List Γ₀ → List Γ₀) (ts : List T) (acc : List Γ₀) :
    hetFoldWhile f (hetMix ts acc) =
      (List.foldl (fun a t => f t a) acc ts).map (some ∘ Sum.inr) := by
  unfold hetFoldWhile
  rw [takeWhile_isHetInl_hetMix, List.length_map]
  induction ts generalizing acc with
  | nil =>
    simp only [List.length, blockIterateWhile, List.foldl_nil]
    rfl
  | cons t ts ih =>
    rw [List.length_cons, blockIterateWhile_succ_true _ _ _ _
        (hasHetInlHead_hetMix_cons t ts acc)]
    rw [hetFoldStep_hetMix]
    exact ih (f t acc)

/-- The fold identity: `foldl` on the reversed list equals `foldr`. -/
theorem foldl_flip_reverse_eq_foldr
    {α β : Type} (f : α → β → β) (z : β) (w : List α) :
    List.foldl (fun a t => f t a) z w.reverse = List.foldr f z w := by
  rw [List.foldl_reverse]

/-- **Decomposition identity**: `hetFoldWhile ∘ reverse` on a pure `inl`
    block equals the `foldr` result. -/
theorem hetFold_decomp
    (f : T → List Γ₀ → List Γ₀) (w : List T) :
    hetFoldWhile f ((w.map (some ∘ Sum.inl)).reverse) =
      (List.foldr f [] w).map (some ∘ @Sum.inr T Γ₀) := by
  rw [← List.map_reverse]
  have : hetMix (T := T) (Γ₀ := Γ₀) w.reverse [] =
      List.map (some ∘ Sum.inl) w.reverse := by simp [hetMix]
  rw [← this, hetFoldWhile_hetMix, foldl_flip_reverse_eq_foldr]

/-
`hetFoldWhile` equals iterated `hetFoldStep` with sufficient fuel.
    This is immediate from the definition: `hetFoldWhile` IS defined as
    `blockIterateWhile`.
-/
theorem hetFoldWhile_eq_iterateWhile
    (f : T → List Γ₀ → List Γ₀)
    (_hf_nd : ∀ t block, (∀ g ∈ block, g ≠ default) → ∀ g ∈ f t block, g ≠ default)
    (block : List (Option (T ⊕ Γ₀)))
    (hblock : ∀ g ∈ block, g ≠ (default : Option (T ⊕ Γ₀))) :
    ∃ n, hetFoldWhile f block =
      blockIterateWhile (hetFoldStep f) hasHetInlHead n block ∧
      ¬hasHetInlHead (blockIterateWhile (hetFoldStep f) hasHetInlHead n block) := by
  -- By definition of `hetFoldWhile`, we know that it is equal to `blockIterateWhile` with the appropriate parameters.
  use (block.takeWhile isHetInl).length;
  induction' n : ( block.takeWhile isHetInl ).length with n ih generalizing block <;> simp_all +decide;
  · rcases block <;> simp_all +decide;
    · exact ⟨ rfl, by rintro ⟨ ⟩ ⟩;
    · cases ‹Option ( T ⊕ Γ₀ ) › <;> simp_all +decide [ isHetInl ];
      · tauto;
      · cases ‹T ⊕ Γ₀› <;> tauto;
  · -- Since the length of the takeWhile is n+1, the block must start with an inl element.
    obtain ⟨t, ts, h_block⟩ : ∃ t ts, block = some (Sum.inl t) :: ts := by
      rcases block with ( _ | ⟨ x, block ⟩ ) <;> simp_all +decide;
      rcases x with ( _ | _ | x ) <;> simp_all +decide [ isHetInl ];
    specialize ih (hetFoldStep f block) (by
    intro g hg; contrapose! hg; simp_all +decide [ hetFoldStep ] ;
    intro h; have := List.mem_takeWhile_imp h; simp_all +decide [ isHetInl ] ;) (by
    simp_all +decide [ List.takeWhile_cons ];
    rw [ show hetFoldStep f ( some ( Sum.inl t ) :: ts ) = List.takeWhile isHetInl ts ++ ( f t ( List.filterMap ( fun x => match x with | some ( Sum.inr g ) => some g | _ => none ) ( List.dropWhile isHetInl ts ) ) |> List.map ( some ∘ Sum.inr ) ) from ?_ ];
    · rw [ List.takeWhile_append ];
      rw [ List.takeWhile_takeWhile ] ; aesop;
    · grind +locals);
    unfold hetFoldWhile at *; simp_all +decide [ List.takeWhile ] ;
    convert ih.2 using 1

/-! ## Non-Defaultness -/

omit [DecidableEq T] [Fintype T] [DecidableEq Γ₀] [Fintype Γ₀] in
/-- All elements of `hetMix` are non-default (`some _`). -/
theorem hetMix_ne_default (ts : List T) (acc : List Γ₀)
    (_hacc : ∀ g ∈ acc, g ≠ (default : Γ₀)) :
    ∀ g ∈ hetMix (T := T) ts acc, g ≠ (default : Option (T ⊕ Γ₀)) := by
  unfold hetMix; aesop

omit [DecidableEq T] [Fintype T] [Inhabited Γ₀] [DecidableEq Γ₀] [Fintype Γ₀] in
/-- Elements of `w.map (some ∘ Sum.inl)` are non-default. -/
theorem map_inl_ne_default (w : List T) :
    ∀ g ∈ w.map (some ∘ @Sum.inl T Γ₀), g ≠ (default : Option (T ⊕ Γ₀)) := by
  intro g hg
  simp only [List.mem_map, Function.comp] at hg
  obtain ⟨_, _, rfl⟩ := hg
  exact Option.some_ne_none _

omit [DecidableEq T] [Fintype T] [DecidableEq Γ₀] [Fintype Γ₀] in
/-- `hetFoldStep` preserves non-defaultness when the condition holds. -/
theorem hetFoldStep_ne_default
    (f : T → List Γ₀ → List Γ₀)
    (_hf_nd : ∀ t block, (∀ g ∈ block, g ≠ default) → ∀ g ∈ f t block, g ≠ default)
    (block : List (Option (T ⊕ Γ₀)))
    (hblock : ∀ g ∈ block, g ≠ (default : Option (T ⊕ Γ₀)))
    (hcond : hasHetInlHead block) :
    ∀ g ∈ hetFoldStep f block, g ≠ (default : Option (T ⊕ Γ₀)) := by
  cases block with
  | nil => cases hcond
  | cons h t =>
    rcases h with (_ | ⟨_ | t'⟩) <;> simp_all +decide [hasHetInlHead]
    unfold hetFoldStep; simp +decide [*]
    rintro g (hg | ⟨a, ha, rfl⟩)
    · have := List.mem_takeWhile_imp hg
      cases g <;> simp_all +decide [isHetInl]
    · exact fun h => by cases h

omit [DecidableEq T] [Fintype T] [DecidableEq Γ₀] [Fintype Γ₀] in
/-
`hetFoldWhile` output is non-default on well-formed (hetMix) blocks.
    For general non-default blocks, this also holds since the while loop
    either preserves the block (when ¬hasHetInlHead) or produces a
    pure `inr` block (when processing succeeds).
-/
theorem hetFoldWhile_ne_default
    (f : T → List Γ₀ → List Γ₀)
    (hf_nd : ∀ t block, (∀ g ∈ block, g ≠ default) → ∀ g ∈ f t block, g ≠ default)
    (block : List (Option (T ⊕ Γ₀)))
    (hblock : ∀ g ∈ block, g ≠ (default : Option (T ⊕ Γ₀))) :
    ∀ g ∈ hetFoldWhile f block, g ≠ (default : Option (T ⊕ Γ₀)) := by
  intro g hg;
  have h_block_ne_default : ∀ block, (∀ g ∈ block, g ≠ default) → ∀ n, (∀ g ∈ blockIterateWhile (hetFoldStep f) hasHetInlHead n block, g ≠ default) := by
    intros block hblock n
    induction' n with n ih generalizing block;
    · exact hblock;
    · by_cases h : hasHetInlHead block <;> simp +decide [ *, blockIterateWhile ];
      · exact ih _ ( hetFoldStep_ne_default f hf_nd block hblock h );
      · exact hblock;
  exact h_block_ne_default block hblock _ _ hg

/-! ## Invariant-Restricted Block Realizability -/

/-- A conditional block step with an invariant restricting which blocks
    the machine must handle.

    This weakens `TM0RealizesBlockCond` by only requiring the machine to
    work on blocks satisfying `blockInv`, with empty suffix.
    This is necessary for the het fold step because the lifted inner
    machine `M_t` (from `TM0RealizesBlock Γ₀ (f t)`) can only correctly
    handle well-formed het blocks: through the alphabet inverse `hetInv`,
    `Sum.inl` elements map to `default`, making them indistinguishable
    from blanks. A machine proved via `TM0RealizesBlock Γ₀` may write to
    cells outside the block during execution and restore them at the end;
    through the lift, such writes corrupt `Sum.inl` elements that happen
    to appear in the "blank" region from the lifted machine's perspective.
    Restricting to well-formed blocks (where `inl` and `inr` elements are
    properly separated) with empty suffix avoids this issue. -/
def TM0RealizesBlockCondInv {Γ : Type} [Inhabited Γ]
    (step : List Γ → List Γ) (cond : List Γ → Prop) [DecidablePred cond]
    (blockInv : List Γ → Prop) : Prop :=
  ∃ (Λ : Type) (_ : Inhabited Λ) (_ : Fintype Λ)
    (M : TM0.Machine Γ Λ) (q_cont : Λ),
    ∀ (block : List Γ),
      blockInv block →
      (∀ g ∈ block, g ≠ default) →
      (cond block → ∀ g ∈ step block, g ≠ default) →
      (TM0Seq.evalCfg M (block ++ [default])).Dom ∧
      ∀ (h : (TM0Seq.evalCfg M (block ++ [default])).Dom),
        let cfg := (TM0Seq.evalCfg M (block ++ [default])).get h
        if cond block then
          cfg.q = q_cont ∧
          cfg.Tape = Tape.mk₁ (step block ++ [default])
        else
          cfg.q ≠ q_cont ∧
          cfg.Tape = Tape.mk₁ (block ++ [default])

/-- Well-formedness predicate for het blocks: the block is of the form
    `hetMix ts acc` for some tag list `ts` and accumulator `acc` with
    all accumulator elements non-default. -/
def isWellFormedHetBlock (block : List (Option (T ⊕ Γ₀))) : Prop :=
  ∃ (ts : List T) (acc : List Γ₀), block = hetMix ts acc ∧
    ∀ g ∈ acc, g ≠ (default : Γ₀)

/-! ## While-Loop with Invariant -/

/-- **While-loop combinator with block invariant (empty suffix).**

    Like `tm0RealizesBlock_while` but:
    - The body only needs to work on blocks satisfying `blockInv`
    - Only empty suffix is required
    - The invariant must be preserved by `step` -/
theorem tm0RealizesBlock_while_inv {Γ : Type} [Inhabited Γ] [DecidableEq Γ] [Fintype Γ]
    (step result : List Γ → List Γ) (cond : List Γ → Prop) [DecidablePred cond]
    (blockInv : List Γ → Prop)
    (hbody : TM0RealizesBlockCondInv step cond blockInv)
    (hinv_step : ∀ block, blockInv block → (∀ g ∈ block, g ≠ default) →
      cond block → blockInv (step block))
    (hstep_nd : ∀ block, (∀ g ∈ block, g ≠ default) → cond block →
      ∀ g ∈ step block, g ≠ default)
    (hresult_eq : ∀ block, (∀ g ∈ block, g ≠ default) → blockInv block →
      ∃ n, result block = blockIterateWhile step cond n block ∧
        ¬cond (blockIterateWhile step cond n block))
    (hresult_nd : ∀ block, (∀ g ∈ block, g ≠ default) → blockInv block →
      ∀ g ∈ result block, g ≠ default) :
    ∃ (Λ : Type) (_ : Inhabited Λ) (_ : Fintype Λ)
      (M : TM0.Machine Γ Λ),
      ∀ (block : List Γ),
        blockInv block →
        (∀ g ∈ block, g ≠ default) →
        (∀ g ∈ result block, g ≠ default) →
        (TM0Seq.evalCfg M (block ++ [default])).Dom ∧
        ∀ (h : (TM0Seq.evalCfg M (block ++ [default])).Dom),
          ((TM0Seq.evalCfg M (block ++ [default])).get h).Tape =
            Tape.mk₁ (result block ++ [default]) := by
  obtain ⟨Λ, hΛi, hΛf, M, q_cont, hM⟩ := hbody
  haveI : DecidableEq Λ := Classical.decEq Λ
  refine ⟨Λ, hΛi, hΛf, tm0WhileLoop M q_cont, ?_⟩
  intro block hblockInv hblock hresult
  obtain ⟨n, hn_eq, hn_not_cond⟩ := hresult_eq block hblock hblockInv
  suffices key : ∀ (m : ℕ) (blk : List Γ),
    blockInv blk →
    (∀ g ∈ blk, g ≠ default) →
    ¬cond (blockIterateWhile step cond m blk) →
    (TM0Seq.evalCfg (tm0WhileLoop M q_cont) (blk ++ [default])).Dom ∧
    ∀ (hd : (TM0Seq.evalCfg (tm0WhileLoop M q_cont) (blk ++ [default])).Dom),
      ((TM0Seq.evalCfg (tm0WhileLoop M q_cont) (blk ++ [default])).get hd).Tape =
      Tape.mk₁ (blockIterateWhile step cond m blk ++ [default]) by
    obtain ⟨h_dom, h_tape⟩ := key n block hblockInv hblock hn_not_cond
    exact ⟨h_dom, fun hd => by rw [hn_eq, h_tape hd]⟩
  intro m
  induction m with
  | zero =>
    intro blk hblkInv hblk hn_not
    simp only [blockIterateWhile] at hn_not ⊢
    obtain ⟨h_body_dom, h_body_spec⟩ := hM blk hblkInv hblk
      (fun hc => hstep_nd blk hblk hc)
    have h_body_spec' := h_body_spec h_body_dom
    simp only [hn_not, ↓reduceIte] at h_body_spec'
    obtain ⟨h_q_ne, h_tape_eq⟩ := h_body_spec'
    have hsuffix : (∀ g ∈ ([] : List Γ), g ≠ default) := by simp
    obtain ⟨h_dom, h_tape⟩ := whileLoop_eval_not_cont M q_cont _ h_body_dom h_q_ne
    exact ⟨h_dom, fun hd => by rw [h_tape hd, h_tape_eq]⟩
  | succ m ih =>
    intro blk hblkInv hblk hn_not
    by_cases hcond : cond blk
    · rw [blockIterateWhile_succ_true _ _ _ _ hcond] at hn_not ⊢
      have h_step_nd := hstep_nd blk hblk hcond
      have h_step_inv := hinv_step blk hblkInv hblk hcond
      obtain ⟨h_body_dom, h_body_spec⟩ := hM blk hblkInv hblk
        (fun _ => h_step_nd)
      have h_body_spec' := h_body_spec h_body_dom
      simp only [hcond, ↓reduceIte] at h_body_spec'
      obtain ⟨h_q_cont, h_tape_step⟩ := h_body_spec'
      obtain ⟨h_W_step_dom, h_W_step_tape⟩ := ih (step blk) h_step_inv h_step_nd hn_not
      obtain ⟨h_W_dom, h_W_tape⟩ := whileLoop_eval_cont M q_cont _ _
        h_body_dom h_q_cont h_tape_step h_W_step_dom
      exact ⟨h_W_dom, fun hd => by rw [h_W_tape hd, h_W_step_tape h_W_step_dom]⟩
    · rw [blockIterateWhile_succ_false _ _ _ _ hcond] at hn_not ⊢
      obtain ⟨h_body_dom, h_body_spec⟩ := hM blk hblkInv hblk
        (fun hc => absurd hc hcond)
      have h_body_spec' := h_body_spec h_body_dom
      simp only [hcond, ↓reduceIte] at h_body_spec'
      obtain ⟨h_q_ne, h_tape_eq⟩ := h_body_spec'
      obtain ⟨h_dom, h_tape⟩ := whileLoop_eval_not_cont M q_cont _ h_body_dom h_q_ne
      exact ⟨h_dom, fun hd => by rw [h_tape hd, h_tape_eq]⟩

/-! ## Block Realizability -/

/-- **Het fold step is conditionally block-realizable (with invariant).**

    Weakened from the original `TM0RealizesBlockCond` to
    `TM0RealizesBlockCondInv` with the `isWellFormedHetBlock` invariant.

    The original statement required the constructed machine to work on ALL
    non-default blocks with ALL non-default suffixes. This is too strong
    because the inner machine `M_t` (from `hf_block : ∀ t, TM0RealizesBlock Γ₀ (f t)`)
    is lifted to the `Option (T ⊕ Γ₀)` alphabet via `hetInv`, which maps
    `Sum.inl` elements to `default`. This means:
    - `Sum.inl` elements in the block appear as blank cells to `M_t`
    - If `M_t` writes to cells outside its block during execution
      (allowed by `TM0RealizesBlock`), it may corrupt `Sum.inl` elements
    - The suffix through `hetInv` may contain spurious `default` values

    By restricting to well-formed blocks (`hetMix ts acc`) with empty
    suffix, we ensure:
    - The `inr` accumulator forms a valid contiguous `Γ₀` block
    - The `inl` tail appears as blanks to the left (consistent with `M_t`)
    - No suffix interference

    The body machine:
    1. Reads the head of the block.
    2. If `some(inl t)`: records `t` in the finite state, scans right past
       remaining `inl` tags, applies the lifted `f t` machine to the `inr`
       accumulator, shifts back to close the gap. Halts at `q_cont`.
    3. If not `some(inl _)`: halts immediately at a state ≠ `q_cont`. -/
theorem tm0RealizesBlockCond_hetFoldStep
    (f : T → List Γ₀ → List Γ₀)
    (hf_block : ∀ t, TM0RealizesBlock Γ₀ (f t))
    (hf_nd : ∀ t block, (∀ g ∈ block, g ≠ default) → ∀ g ∈ f t block, g ≠ default) :
    TM0RealizesBlockCondInv (hetFoldStep f) (@hasHetInlHead T Γ₀)
      (isWellFormedHetBlock (T := T) (Γ₀ := Γ₀)) := by
  sorry

/-- `isWellFormedHetBlock` is preserved by `hetFoldStep` when the
    condition holds. -/
theorem isWellFormedHetBlock_step
    (f : T → List Γ₀ → List Γ₀)
    (hf_nd : ∀ t block, (∀ g ∈ block, g ≠ default) → ∀ g ∈ f t block, g ≠ default)
    (block : List (Option (T ⊕ Γ₀)))
    (hInv : isWellFormedHetBlock block)
    (hblock : ∀ g ∈ block, g ≠ (default : Option (T ⊕ Γ₀)))
    (hcond : hasHetInlHead block) :
    isWellFormedHetBlock (hetFoldStep f block) := by
  obtain ⟨ts, acc, rfl, hacc⟩ := hInv
  cases ts with
  | nil => exact absurd hcond (not_hasHetInlHead_hetMix_nil acc)
  | cons t ts =>
    rw [hetFoldStep_hetMix]
    exact ⟨ts, f t acc, rfl, hf_nd t acc hacc⟩

/-- `hetFoldWhile_eq_iterateWhile` restricted to well-formed blocks. -/
theorem hetFoldWhile_eq_iterateWhile_wf
    (f : T → List Γ₀ → List Γ₀)
    (hf_nd : ∀ t block, (∀ g ∈ block, g ≠ default) → ∀ g ∈ f t block, g ≠ default)
    (block : List (Option (T ⊕ Γ₀)))
    (hblock : ∀ g ∈ block, g ≠ (default : Option (T ⊕ Γ₀)))
    (hInv : isWellFormedHetBlock block) :
    ∃ n, hetFoldWhile f block =
      blockIterateWhile (hetFoldStep f) hasHetInlHead n block ∧
      ¬hasHetInlHead (blockIterateWhile (hetFoldStep f) hasHetInlHead n block) :=
  hetFoldWhile_eq_iterateWhile f hf_nd block hblock

/-- **Het fold while loop machine exists for well-formed blocks.**

    Derived from:
    - `tm0RealizesBlockCond_hetFoldStep` (body is conditionally realizable
      with invariant)
    - `tm0RealizesBlock_while_inv` (while-loop combinator with invariant)
    - `hetFoldWhile_eq_iterateWhile_wf` (iteration equals definition) -/
theorem tm0RealizesBlock_hetFoldWhile_inv
    (f : T → List Γ₀ → List Γ₀)
    (hf_block : ∀ t, TM0RealizesBlock Γ₀ (f t))
    (hf_nd : ∀ t block, (∀ g ∈ block, g ≠ default) → ∀ g ∈ f t block, g ≠ default) :
    ∃ (Λ : Type) (_ : Inhabited Λ) (_ : Fintype Λ)
      (M : TM0.Machine (Option (T ⊕ Γ₀)) Λ),
      ∀ (block : List (Option (T ⊕ Γ₀))),
        isWellFormedHetBlock block →
        (∀ g ∈ block, g ≠ (default : Option (T ⊕ Γ₀))) →
        (∀ g ∈ hetFoldWhile f block, g ≠ (default : Option (T ⊕ Γ₀))) →
        (TM0Seq.evalCfg M (block ++ [default])).Dom ∧
        ∀ (h : (TM0Seq.evalCfg M (block ++ [default])).Dom),
          ((TM0Seq.evalCfg M (block ++ [default])).get h).Tape =
            Tape.mk₁ (hetFoldWhile f block ++ [default]) :=
  tm0RealizesBlock_while_inv
    (hetFoldStep f) (hetFoldWhile f) hasHetInlHead
    isWellFormedHetBlock
    (tm0RealizesBlockCond_hetFoldStep f hf_block hf_nd)
    (fun block hInv hnd hcond => isWellFormedHetBlock_step f hf_nd block hInv hnd hcond)
    (fun block hblock hcond => hetFoldStep_ne_default f hf_nd block hblock hcond)
    (fun block hblock hInv => hetFoldWhile_eq_iterateWhile_wf f hf_nd block hblock hInv)
    (fun block hblock _hInv => hetFoldWhile_ne_default f hf_nd block hblock)

/-- `w.map (some ∘ Sum.inl)` forms a well-formed het block. -/
theorem isWellFormedHetBlock_map_inl (w : List T) :
    isWellFormedHetBlock (T := T) (Γ₀ := Γ₀) (w.map (some ∘ Sum.inl)) := by
  exact ⟨w, [], by simp [hetMix], by simp⟩

/-- Reversed well-formed het block is still well-formed. -/
theorem isWellFormedHetBlock_reverse_map_inl (w : List T) :
    isWellFormedHetBlock (T := T) (Γ₀ := Γ₀) ((w.map (some ∘ Sum.inl)).reverse) := by
  rw [← List.map_reverse]
  exact ⟨w.reverse, [], by simp [hetMix], by simp⟩

/-! ## Deriving the Original Fold Spec -/

/-
**Derive `tm0Het_fold_blockRealizable` from the invariant-restricted
    decomposition.**

    The proof composes:
    1. `tm0_reverse_block` for reversing the input
    2. `tm0RealizesBlock_hetFoldWhile_inv` for the while loop

    Since the final theorem only needs the machine to work on specific inputs
    `w.map (some ∘ Sum.inl)` (which are well-formed het blocks with all-`inl`
    elements), the invariant-restricted version suffices.
-/
theorem tm0Het_fold_blockRealizable'
    (T : Type) [DecidableEq T] [Fintype T]
    {Γ₀ : Type} [Inhabited Γ₀] [DecidableEq Γ₀] [Fintype Γ₀]
    (f : T → List Γ₀ → List Γ₀)
    (hf_block : ∀ t, TM0RealizesBlock Γ₀ (f t))
    (hf_nd : ∀ t block, (∀ g ∈ block, g ≠ default) →
      ∀ g ∈ f t block, g ≠ default) :
    ∃ (Λ : Type) (_ : Inhabited Λ) (_ : Fintype Λ)
      (M : TM0.Machine (Option (T ⊕ Γ₀)) Λ),
      ∀ w : List T,
        (TM0Seq.evalCfg M (w.map (some ∘ Sum.inl))).Dom ∧
        ∀ (h : (TM0Seq.evalCfg M (w.map (some ∘ Sum.inl))).Dom),
          ((TM0Seq.evalCfg M (w.map (some ∘ Sum.inl))).get h).Tape =
            Tape.mk₁ ((List.foldr f [] w).map
              (some ∘ @Sum.inr T Γ₀)) := by
  obtain ⟨ Λ, _, _, M, hM ⟩ := tm0RealizesBlock_hetFoldWhile_inv f hf_block hf_nd;
  -- Let's obtain the machine M_rev from the theorem tm0_reverse_block.
  obtain ⟨Λ_rev, _, _, M_rev, hM_rev⟩ := tm0_reverse_block (Γ := Option (T ⊕ Γ₀));
  refine' ⟨ _, _, _, TM0Seq.compose M_rev M, _ ⟩;
  · infer_instance;
  · intro w;
    refine' ⟨ _, _ ⟩;
    · have h_dom_rev : (TM0Seq.evalCfg M_rev (List.map (some ∘ Sum.inl) w ++ [default])).Dom := by
        convert hM_rev ( List.map ( some ∘ Sum.inl ) w ) [ ] _ _ _ |> And.left using 1 <;> simp +decide [ List.map ];
      have h_dom_while : (TM0Seq.evalCfg M ((List.map (some ∘ Sum.inl) w).reverse ++ [default])).Dom := by
        apply (hM ((List.map (some ∘ Sum.inl) w).reverse) (isWellFormedHetBlock_reverse_map_inl w) (by
        simp +decide [ List.mem_reverse, List.mem_map ]) (by
        apply hetFoldWhile_ne_default;
        · exact hf_nd;
        · simp +decide [ List.mem_reverse, List.mem_map ])).left;
      convert TM0Seq.compose_dom_of_parts M_rev M ( List.map ( some ∘ Sum.inl ) w ) _ _ using 1;
      convert h_dom_rev using 1;
      grind +suggestions;
      convert h_dom_while using 1;
      congr;
      convert hM_rev ( List.map ( some ∘ Sum.inl ) w ) [ ] _ _ _ |> And.right |> fun h => h _ using 1;
      any_goals assumption;
      · grind +suggestions;
      · simp +decide [ Function.comp ];
      · simp +decide;
      · simp +decide [ Function.comp ];
    · intro h;
      convert TM0Seq.compose_evalCfg_tape M_rev M _ _ _ _ _ _ using 1;
      rotate_left;
      exact ( List.map ( some ∘ Sum.inl ) w ).reverse;
      all_goals generalize_proofs at *;
      · convert hM_rev ( List.map ( some ∘ Sum.inl ) w ) [ ] _ _ _ |>.1 using 1;
        · grind +suggestions;
        · simp +decide [ Function.comp ];
        · simp +decide;
        · simp +decide [ List.mem_reverse, List.mem_map ];
      · convert hM_rev ( List.map ( some ∘ Sum.inl ) w ) [ ] _ _ _ |> And.right using 1;
        · grind +suggestions;
        · grind;
        · simp +decide;
        · simp +decide [ List.mem_reverse, List.mem_map ];
      · specialize hM ( List.map ( some ∘ Sum.inl ) w |> List.reverse ) ?_ ?_ ?_;
        · grind +suggestions;
        · simp +decide [ List.mem_reverse, List.mem_map ];
        · apply hetFoldWhile_ne_default;
          · exact hf_nd;
          · simp +decide [ List.mem_reverse ];
        · grind +suggestions;
      · specialize hM ( List.map ( some ∘ Sum.inl ) w |> List.reverse ) ; simp_all +decide [ isWellFormedHetBlock_reverse_map_inl ];
        convert hM _ |>.2 _ |> Eq.symm using 1;
        all_goals generalize_proofs at *;
        · rw [ ← tape_mk₁_append_default ];
          rw [ hetFold_decomp ];
        · grind +suggestions;
        · apply hetFoldWhile_ne_default;
          · exact hf_nd;
          · simp +decide [ List.mem_reverse, List.mem_map ];
        · grind +suggestions

end HetFold