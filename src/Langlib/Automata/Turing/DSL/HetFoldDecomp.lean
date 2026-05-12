import Mathlib
import Langlib.Automata.Turing.DSL.BlockRealizability
import Langlib.Automata.Turing.DSL.PairedAddHelpers
import Langlib.Automata.Turing.DSL.DropUntilFirstSepMachine

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

/-! ## Generic Prefix Fold -/

section PrefixFold

variable {Gamma Tag : Type}

/-- A generic fold step over one ambient alphabet.

The fold layer only knows how to decode the first cell as a tag.  The body
already operates on the same alphabet as the tape block. -/
noncomputable def prefixFoldStep
    (tagOf : Gamma → Option Tag) (F : Tag → List Gamma → List Gamma) :
    List Gamma → List Gamma
  | c :: rest =>
      match tagOf c with
      | some t => F t rest
      | none => c :: rest
  | [] => []

/-- Generic head condition for the prefix fold. -/
def hasTagHead (tagOf : Gamma → Option Tag) : List Gamma → Prop
  | c :: _ => (tagOf c).isSome
  | [] => False

instance (tagOf : Gamma → Option Tag) : DecidablePred (hasTagHead tagOf)
  | [] => isFalse id
  | c :: _ => by
      dsimp [hasTagHead]
      infer_instance

/-- Boolean predicate used for the fuel bound of the prefix fold. -/
def isTagCell (tagOf : Gamma → Option Tag) (c : Gamma) : Bool :=
  (tagOf c).isSome

/-- Generic while-style fold over a leading tag prefix.

This is the folding mechanism.  It is deliberately independent of any
embedding/decoding between alphabets. -/
noncomputable def prefixFoldWhile
    (tagOf : Gamma → Option Tag) (F : Tag → List Gamma → List Gamma)
    (block : List Gamma) : List Gamma :=
  blockIterateWhile (prefixFoldStep tagOf F) (hasTagHead tagOf)
    (block.takeWhile (isTagCell tagOf)).length block

end PrefixFold

/-! ## Generic Separated Layout Mapping -/

section SeparatedFold

variable {Gamma Tag Acc : Type}

/-- Generic separated block layout: remaining tags, one explicit separator,
then accumulator content.  The concrete alphabet is supplied by the embeddings. -/
def separatedMix (tagEmb : Tag → Gamma) (sep : Gamma) (accEmb : Acc → Gamma)
    (tags : List Tag) (acc : List Acc) : List Gamma :=
  tags.map tagEmb ++ [sep] ++ acc.map accEmb

/-- Generic layout/mapping adapter over a separated block.

It keeps the tag prefix, consumes exactly the first non-tag cell as separator,
decodes the accumulator suffix, applies the accumulator operation, and writes
the result back using `accEmb`.

This is not the fold.  It is the alphabet/layout bridge that turns an
accumulator-alphabet operation into an ambient-alphabet block operation. -/
noncomputable def separatedAccLift
    (isTag : Gamma → Bool) (sep : Gamma) (decodeAcc : Gamma → Option Acc)
    (accEmb : Acc → Gamma) (f : Tag → List Acc → List Acc) (t : Tag) :
    List Gamma → List Gamma :=
  fun rest =>
    let tagTail := rest.takeWhile isTag
    let afterTags := rest.dropWhile isTag
    let accPart :=
      match afterTags with
      | [] => []
      | _sep :: tail => tail
    let acc := accPart.filterMap decodeAcc
    tagTail ++ [sep] ++ (f t acc).map accEmb

/-- Backwards-compatible name for the separated layout adapter. -/
noncomputable def separatedFoldAdapt
    (isTag : Gamma → Bool) (sep : Gamma) (decodeAcc : Gamma → Option Acc)
    (accEmb : Acc → Gamma) (f : Tag → List Acc → List Acc) (t : Tag) :
    List Gamma → List Gamma :=
  separatedAccLift isTag sep decodeAcc accEmb f t

/-- Trivial same-alphabet interface for the generic separated adapter.

The old statement tried to derive this from an accumulator-alphabet block
machine.  That is not valid without stronger assumptions on the concrete
encoding/decoding and on suffix preservation.  Callers should provide the
same-alphabet block machine for the actual adapter they use. -/
theorem tm0_separatedAccLift_block_of_sameAlphabet
    {Gamma Tag Acc : Type} [Inhabited Gamma] [DecidableEq Gamma] [Fintype Gamma]
    [Inhabited Acc] [DecidableEq Acc] [Fintype Acc]
    (isTag : Gamma → Bool) (sep : Gamma) (decodeAcc : Gamma → Option Acc)
    (accEmb : Acc → Gamma) (f : Tag → List Acc → List Acc) (t : Tag)
    (hf : TM0RealizesBlock Gamma
      (separatedAccLift isTag sep decodeAcc accEmb f t)) :
    TM0RealizesBlock Gamma (separatedAccLift isTag sep decodeAcc accEmb f t) :=
  hf

/-- Trivial same-alphabet interface for the separated layout adapter. -/
theorem tm0_separatedFoldAdapt_block_of_sameAlphabet
    {Gamma Tag Acc : Type} [Inhabited Gamma] [DecidableEq Gamma] [Fintype Gamma]
    [Inhabited Acc] [DecidableEq Acc] [Fintype Acc]
    (isTag : Gamma → Bool) (sep : Gamma) (decodeAcc : Gamma → Option Acc)
    (accEmb : Acc → Gamma) (f : Tag → List Acc → List Acc) (t : Tag)
    (hf : TM0RealizesBlock Gamma
      (separatedFoldAdapt isTag sep decodeAcc accEmb f t)) :
    TM0RealizesBlock Gamma (separatedFoldAdapt isTag sep decodeAcc accEmb f t) := by
  exact hf

end SeparatedFold

/-! ## Heterogeneous Fold Definitions -/

section HetFold

variable {T : Type} [DecidableEq T] [Fintype T]
variable {Γ₀ : Type} [Inhabited Γ₀] [DecidableEq Γ₀] [Fintype Γ₀]

/-- Check if a het block element is an `inl` tag. -/
def isHetInl (x : Option (T ⊕ Γ₀)) : Bool :=
  match x with | some (Sum.inl _) => true | _ => false

/-- Decode fold tags from the concrete heterogeneous alphabet. -/
def hetTagDecode : Option (T ⊕ Γ₀) → Option T
  | some (Sum.inl t) => some t
  | _ => none

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

/-- Explicit separator between the remaining `inl` tags and the `inr`
accumulator.  The accumulator invariant excludes `default : Γ₀`, so
`some (Sum.inr default)` is fresh for accumulator contents while still being a
nonblank tape symbol. -/
def hetSep : Option (T ⊕ Γ₀) :=
  some (Sum.inr default)

/-- Embed fold tags into the concrete heterogeneous alphabet. -/
def hetTagEmb (t : T) : Option (T ⊕ Γ₀) :=
  some (Sum.inl t)

/-- Embed accumulator symbols into the concrete heterogeneous alphabet. -/
def hetAccEmb (g : Γ₀) : Option (T ⊕ Γ₀) :=
  some (Sum.inr g)

/-- Decode accumulator cells from the concrete heterogeneous alphabet. -/
def hetAccDecode : Option (T ⊕ Γ₀) → Option Γ₀
  | some (Sum.inr g) => some g
  | _ => none

/-- Mixed het block representation with an explicit separator:
`inl` tags, then `sep`, then the `inr` accumulator. -/
def hetMixSep (sep : Option (T ⊕ Γ₀)) (ts : List T) (acc : List Γ₀) :
    List (Option (T ⊕ Γ₀)) :=
  separatedMix (hetTagEmb (Γ₀ := Γ₀)) sep (hetAccEmb (T := T)) ts acc

/-- Default concrete het layout separator.  Prefer proving generic facts about
`hetMixSep` when the separator matters. -/
def hetMix (ts : List T) (acc : List Γ₀) : List (Option (T ⊕ Γ₀)) :=
  hetMixSep (hetSep (T := T) (Γ₀ := Γ₀)) ts acc

/-- One step of the het fold while loop.
    Pops the leftmost `inl t` tag and runs the same-alphabet step `F t` on
    the remaining block.

    The fact that `F t` preserves the remaining tags and updates only the
    accumulator is a function-level obligation, not part of this generic fold
    construction. -/
noncomputable def hetFoldStep
    (F : T → List (Option (T ⊕ Γ₀)) → List (Option (T ⊕ Γ₀))) :
    List (Option (T ⊕ Γ₀)) → List (Option (T ⊕ Γ₀)) :=
  prefixFoldStep (hetTagDecode (Γ₀ := Γ₀)) F

/-- The full while-loop result function, defined as iterated application
    of `hetFoldStep` with fuel equal to the number of leading `inl` tags.

    This directly models what the `tm0WhileLoop` machine computes:
    iterate `hetFoldStep` while `hasHetInlHead`, stopping when no more
    `inl` tags remain at the head. -/
noncomputable def hetFoldWhile
    (F : T → List (Option (T ⊕ Γ₀)) → List (Option (T ⊕ Γ₀)))
    (block : List (Option (T ⊕ Γ₀))) : List (Option (T ⊕ Γ₀)) :=
  blockIterateWhile (hetFoldStep F) hasHetInlHead
    (block.takeWhile (isHetInl (T := T) (Γ₀ := Γ₀))).length block

/-- Function-level adapter from an accumulator operation to a homogeneous
    het-tape operation.

This is intentionally not part of the generic fold theorem.  Any machine
realizability proof for this adapter must account for the alphabet/layout
boundary explicitly. -/
noncomputable def hetFoldAdaptSep
    (sep : Option (T ⊕ Γ₀))
    (f : T → List Γ₀ → List Γ₀) (t : T) :
    List (Option (T ⊕ Γ₀)) → List (Option (T ⊕ Γ₀)) :=
  separatedAccLift
    (isHetInl (T := T) (Γ₀ := Γ₀)) sep
    (hetAccDecode (T := T)) (hetAccEmb (T := T)) f t

/-- Concrete default separator instantiation of `hetFoldAdaptSep`. -/
noncomputable def hetFoldAdapt
    (f : T → List Γ₀ → List Γ₀) (t : T) :
    List (Option (T ⊕ Γ₀)) → List (Option (T ⊕ Γ₀)) :=
  hetFoldAdaptSep (hetSep (T := T) (Γ₀ := Γ₀)) f t

/-- Same-alphabet machine obligation for `hetFoldAdaptSep`.

This theorem deliberately no longer claims that an accumulator-alphabet
machine is enough.  Preserving the leading `inl` tail is a concrete
same-alphabet obligation. -/
theorem tm0_hetFoldAdaptSep_block_of_sameAlphabet
    (sep : Option (T ⊕ Γ₀))
    (f : T → List Γ₀ → List Γ₀) (t : T)
    (hf : TM0RealizesBlock (Option (T ⊕ Γ₀)) (hetFoldAdaptSep sep f t)) :
    TM0RealizesBlock (Option (T ⊕ Γ₀)) (hetFoldAdaptSep sep f t) :=
  hf

theorem tm0_hetFoldAdapt_block_of_sameAlphabet
    (f : T → List Γ₀ → List Γ₀) (t : T)
    (hf : TM0RealizesBlock (Option (T ⊕ Γ₀)) (hetFoldAdapt f t)) :
    TM0RealizesBlock (Option (T ⊕ Γ₀)) (hetFoldAdapt f t) := by
  exact hf

/-! ## Mathematical Correctness -/

/-- `hetMix` with a non-empty tag list starts with `inl`. -/
theorem hasHetInlHead_hetMix_cons (t : T) (ts : List T) (acc : List Γ₀) :
    hasHetInlHead (hetMix (t :: ts) acc) := by
  simp [hetMix, hetMixSep, separatedMix, hetTagEmb, hasHetInlHead]

/-- `hetMix` with empty tag list does NOT start with `inl`. -/
theorem not_hasHetInlHead_hetMix_nil (acc : List Γ₀) :
    ¬hasHetInlHead (hetMix ([] : List T) acc) := by
  simp [hetMix, hetMixSep, separatedMix, hetSep, hasHetInlHead]

/-- One step is correct on `hetMix` when the same-alphabet step has the
    intended function-level behavior. -/
theorem hetFoldStep_hetMix
    (F : T → List (Option (T ⊕ Γ₀)) → List (Option (T ⊕ Γ₀)))
    (f : T → List Γ₀ → List Γ₀)
    (hF : ∀ t ts acc, F t (hetMix (T := T) (Γ₀ := Γ₀) ts acc) = hetMix ts (f t acc))
    (t : T) (ts : List T) (acc : List Γ₀) :
    hetFoldStep F (hetMix (t :: ts) acc) = hetMix ts (f t acc) := by
  simp [hetFoldStep, hetMix, hetMixSep, separatedMix, hetTagEmb]
  simpa [hetMix, hetMixSep, separatedMix, hetTagEmb, hetAccEmb] using hF t ts acc

theorem hetFoldAdapt_hetMix
    (f : T → List Γ₀ → List Γ₀) (t : T) (ts : List T) (acc : List Γ₀) :
    hetFoldAdapt f t (hetMix ts acc) = hetMix ts (f t acc) := by
  have hdecode : List.filterMap (hetAccDecode (T := T) ∘ hetAccEmb (T := T)) acc = acc := by
    induction acc with
    | nil => simp
    | cons g acc ih => simp [Function.comp, hetAccDecode, hetAccEmb, ih]
  induction ts with
  | nil =>
      simp [hetFoldAdapt, hetFoldAdaptSep, separatedAccLift, hetMix, hetMixSep,
        separatedMix, hetSep, isHetInl, hdecode]
  | cons t' ts ih =>
      simp [hetFoldAdapt, hetFoldAdaptSep, separatedAccLift, hetMix, hetMixSep,
        separatedMix, hetTagEmb, hetSep, isHetInl, hdecode]

/-
The `takeWhile isHetInl` length of `hetMix ts acc` is `ts.length`.
-/
theorem takeWhile_isHetInl_hetMix (ts : List T) (acc : List Γ₀) :
    (hetMix (T := T) (Γ₀ := Γ₀) ts acc).takeWhile
      (isHetInl (T := T) (Γ₀ := Γ₀)) = ts.map (some ∘ Sum.inl) := by
  induction' ts with t ts ih
  · simp [hetMix, hetMixSep, separatedMix, hetSep, isHetInl]
  · simp [hetMix, hetMixSep, separatedMix, hetTagEmb, hetAccEmb, hetSep, isHetInl, ih]

/-- `hetFoldWhile` is correct on `hetMix`: computes `foldl`. -/
theorem hetFoldWhile_hetMix
    (F : T → List (Option (T ⊕ Γ₀)) → List (Option (T ⊕ Γ₀)))
    (f : T → List Γ₀ → List Γ₀)
    (hF : ∀ t ts acc, F t (hetMix (T := T) (Γ₀ := Γ₀) ts acc) = hetMix ts (f t acc))
    (ts : List T) (acc : List Γ₀) :
    hetFoldWhile F (hetMix ts acc) =
      hetMix [] (List.foldl (fun a t => f t a) acc ts) := by
  unfold hetFoldWhile
  rw [takeWhile_isHetInl_hetMix, List.length_map]
  induction ts generalizing acc with
  | nil =>
    simp only [List.length, blockIterateWhile, List.foldl_nil]
  | cons t ts ih =>
    rw [List.length_cons, blockIterateWhile_succ_true _ _ _ _
        (hasHetInlHead_hetMix_cons t ts acc)]
    rw [hetFoldStep_hetMix F f hF]
    exact ih (f t acc)

/-- The fold identity: `foldl` on the reversed list equals `foldr`. -/
theorem foldl_flip_reverse_eq_foldr
    {α β : Type} (f : α → β → β) (z : β) (w : List α) :
    List.foldl (fun a t => f t a) z w.reverse = List.foldr f z w := by
  rw [List.foldl_reverse]

/-- **Decomposition identity**: `hetFoldWhile ∘ reverse` on a pure `inl`
    block equals the `foldr` result. -/
theorem hetFold_decomp
    (F : T → List (Option (T ⊕ Γ₀)) → List (Option (T ⊕ Γ₀)))
    (f : T → List Γ₀ → List Γ₀)
    (hF : ∀ t ts acc, F t (hetMix (T := T) (Γ₀ := Γ₀) ts acc) = hetMix ts (f t acc))
    (w : List T) :
    hetFoldWhile F ((w.map (some ∘ Sum.inl)).reverse ++
        [hetSep (T := T) (Γ₀ := Γ₀)]) =
      hetMix [] (List.foldr f [] w) := by
  rw [← List.map_reverse]
  have : hetMix (T := T) (Γ₀ := Γ₀) w.reverse [] =
      List.map (some ∘ Sum.inl) w.reverse ++
        [hetSep (T := T) (Γ₀ := Γ₀)] := by
    simp [hetMix, hetMixSep, separatedMix, hetTagEmb]
  rw [← this, hetFoldWhile_hetMix F f hF, foldl_flip_reverse_eq_foldr]

/-! ## Non-Defaultness -/

omit [DecidableEq T] [Fintype T] [DecidableEq Γ₀] [Fintype Γ₀] in
/-- All elements of `hetMix` are non-default (`some _`). -/
theorem hetMix_ne_default (ts : List T) (acc : List Γ₀)
    (_hacc : ∀ g ∈ acc, g ≠ (default : Γ₀)) :
    ∀ g ∈ hetMix (T := T) ts acc, g ≠ (default : Option (T ⊕ Γ₀)) := by
  intro g hg
  simp [hetMix, hetMixSep, separatedMix, hetTagEmb, hetAccEmb, hetSep] at hg
  rcases hg with htag | hsep | hacc
  · rcases htag with ⟨t, _ht, hg⟩
    rw [← hg]
    simp
  · rw [hsep]
    simp
  · rcases hacc with ⟨a, _ha, hg⟩
    rw [← hg]
    simp

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
    (F : T → List (Option (T ⊕ Γ₀)) → List (Option (T ⊕ Γ₀)))
    (hF_nd : ∀ t block, (∀ g ∈ block, g ≠ default) → ∀ g ∈ F t block, g ≠ default)
    (block : List (Option (T ⊕ Γ₀)))
    (hblock : ∀ g ∈ block, g ≠ (default : Option (T ⊕ Γ₀)))
    (hcond : hasHetInlHead block) :
    ∀ g ∈ hetFoldStep F block, g ≠ (default : Option (T ⊕ Γ₀)) := by
  cases block with
  | nil => cases hcond
  | cons h rest =>
    cases h with
    | none => cases hcond
    | some s =>
      cases s with
      | inl t =>
          simpa [hetFoldStep] using
            hF_nd t rest (fun g hg => hblock g (List.mem_cons_of_mem _ hg))
      | inr g => cases hcond

omit [DecidableEq T] [Fintype T] [DecidableEq Γ₀] [Fintype Γ₀] in
/-
`hetFoldWhile` output is non-default on well-formed (hetMix) blocks.
    For general non-default blocks, this also holds since the while loop
    either preserves the block (when ¬hasHetInlHead) or produces a
    pure `inr` block (when processing succeeds).
-/
theorem hetFoldWhile_ne_default
    (F : T → List (Option (T ⊕ Γ₀)) → List (Option (T ⊕ Γ₀)))
    (hF_nd : ∀ t block, (∀ g ∈ block, g ≠ default) → ∀ g ∈ F t block, g ≠ default)
    (block : List (Option (T ⊕ Γ₀)))
    (hblock : ∀ g ∈ block, g ≠ (default : Option (T ⊕ Γ₀))) :
    ∀ g ∈ hetFoldWhile F block, g ≠ (default : Option (T ⊕ Γ₀)) := by
  intro g hg;
  have h_block_ne_default : ∀ block, (∀ g ∈ block, g ≠ default) → ∀ n, (∀ g ∈ blockIterateWhile (hetFoldStep F) hasHetInlHead n block, g ≠ default) := by
    intros block hblock n
    induction' n with n ih generalizing block;
    · exact hblock;
    · by_cases h : hasHetInlHead block <;> simp +decide [ *, blockIterateWhile ];
      · exact ih _ ( hetFoldStep_ne_default F hF_nd block hblock h );
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

abbrev HetFoldStepState (T : Type) (Λ : T → Type) :=
  Unit ⊕ Unit ⊕ T ⊕ (Σ t, Λ t)

namespace HetFoldStepState

def start {T : Type} {Λ : T → Type} : HetFoldStepState T Λ :=
  Sum.inl ()

def cont {T : Type} {Λ : T → Type} : HetFoldStepState T Λ :=
  Sum.inr (Sum.inl ())

def move {T : Type} {Λ : T → Type} (t : T) : HetFoldStepState T Λ :=
  Sum.inr (Sum.inr (Sum.inl t))

def run {T : Type} {Λ : T → Type} (t : T) (q : Λ t) : HetFoldStepState T Λ :=
  Sum.inr (Sum.inr (Sum.inr ⟨t, q⟩))

instance {T : Type} {Λ : T → Type} : Inhabited (HetFoldStepState T Λ) :=
  ⟨start⟩

end HetFoldStepState

noncomputable def tm0HetFoldStepMachine
    {T Γ₀ : Type} [DecidableEq T]
    (Λ : T → Type) [∀ t, Inhabited (Λ t)]
    (M : ∀ t, TM0.Machine (Option (T ⊕ Γ₀)) (Λ t)) :
    TM0.Machine (Option (T ⊕ Γ₀)) (HetFoldStepState T Λ) :=
  fun q a =>
    match q with
    | .inl () =>
        match a with
        | some (Sum.inl t) => some (HetFoldStepState.move t, .write default)
        | _ => none
    | .inr (.inl ()) => none
    | .inr (.inr (.inl t)) =>
        some (HetFoldStepState.run t default, .move Dir.right)
    | .inr (.inr (.inr tq)) =>
        match M tq.1 tq.2 a with
        | some (q', s) => some (HetFoldStepState.run tq.1 q', s)
        | none => some (HetFoldStepState.cont, .write a)

theorem tm0HetFoldStepMachine_run_step
    {T Γ₀ : Type} [DecidableEq T]
    (Λ : T → Type) [∀ t, Inhabited (Λ t)]
    (M : ∀ t, TM0.Machine (Option (T ⊕ Γ₀)) (Λ t))
    (t : T)
    {c c' : TM0.Cfg (Option (T ⊕ Γ₀)) (Λ t)}
    (h : c' ∈ TM0.step (M t) c) :
    ⟨HetFoldStepState.run t c'.q, c'.Tape⟩ ∈
      TM0.step (tm0HetFoldStepMachine (T := T) (Γ₀ := Γ₀) Λ M)
        ⟨HetFoldStepState.run t c.q, c.Tape⟩ := by
  rcases c with ⟨q, tape⟩
  rcases c' with ⟨q', tape'⟩
  have hstep : TM0.step (M t) ⟨q, tape⟩ = some ⟨q', tape'⟩ :=
    Option.mem_def.mp h
  unfold TM0.step at hstep ⊢
  simp only [tm0HetFoldStepMachine, HetFoldStepState.run]
  cases hm : M t q tape.head with
  | none =>
      simp [hm] at hstep
  | some step =>
      rcases step with ⟨qNext, stmt⟩
      simp [hm] at hstep ⊢
      rcases hstep with ⟨hq, htape⟩
      cases hq
      cases htape
      exact ⟨rfl, rfl⟩

theorem tm0HetFoldStepMachine_run_reaches
    {T Γ₀ : Type} [DecidableEq T]
    (Λ : T → Type) [∀ t, Inhabited (Λ t)]
    (M : ∀ t, TM0.Machine (Option (T ⊕ Γ₀)) (Λ t))
    (t : T) {l : List (Option (T ⊕ Γ₀))}
    {c : TM0.Cfg (Option (T ⊕ Γ₀)) (Λ t)}
    (h : Reaches (TM0.step (M t)) (TM0.init l) c) :
    Reaches (TM0.step (tm0HetFoldStepMachine (T := T) (Γ₀ := Γ₀) Λ M))
      ⟨HetFoldStepState.run t default, Tape.mk₁ l⟩
      ⟨HetFoldStepState.run t c.q, c.Tape⟩ := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hreach hstep ih =>
      exact ih.tail
        (tm0HetFoldStepMachine_run_step Λ M t hstep)

/-- **Het fold step is conditionally block-realizable (with invariant).**

    This is the local machine-construction obligation for one fold-body step. -/
theorem tm0RealizesBlockCond_hetFoldStep
    (F : T → List (Option (T ⊕ Γ₀)) → List (Option (T ⊕ Γ₀)))
    (hf_block : ∀ t, TM0RealizesBlock (Option (T ⊕ Γ₀)) (F t))
    (hf_nd : ∀ t block, (∀ g ∈ block, g ≠ default) → ∀ g ∈ F t block, g ≠ default) :
    TM0RealizesBlockCondInv (hetFoldStep F) (@hasHetInlHead T Γ₀)
      (isWellFormedHetBlock (T := T) (Γ₀ := Γ₀)) := by
  classical
  choose Λ hΛi hΛf M hM using hf_block
  refine ⟨HetFoldStepState T Λ, inferInstance, inferInstance,
    tm0HetFoldStepMachine (T := T) (Γ₀ := Γ₀) Λ M,
    HetFoldStepState.cont, ?_⟩
  intro block hInv hblock hstep_nd
  obtain ⟨ts, acc, rfl, hacc_nd⟩ := hInv
  cases ts with
  | nil =>
      constructor
      · apply Part.dom_iff_mem.mpr
        refine ⟨⟨HetFoldStepState.start, Tape.mk₁ (hetMix ([] : List T) acc ++ [default])⟩,
          Turing.mem_eval.mpr ⟨Relation.ReflTransGen.refl, ?_⟩⟩
        simp [TM0.step, tm0HetFoldStepMachine, HetFoldStepState.start,
          hetMix, hetMixSep, separatedMix, hetSep, Tape.mk₁, Tape.mk₂, Tape.mk']
      · intro h
        have hmem := Part.get_mem h
        have hhalt :
            ⟨HetFoldStepState.start,
              Tape.mk₁ (hetMix (T := T) (Γ₀ := Γ₀) ([] : List T) acc ++ [default])⟩ ∈
              TM0Seq.evalCfg
                (tm0HetFoldStepMachine (T := T) (Γ₀ := Γ₀) Λ M)
                (hetMix (T := T) (Γ₀ := Γ₀) ([] : List T) acc ++ [default]) := by
          exact Turing.mem_eval.mpr ⟨Relation.ReflTransGen.refl, by
            simp [TM0.step, tm0HetFoldStepMachine, HetFoldStepState.start,
              hetMix, hetMixSep, separatedMix, hetSep, Tape.mk₁, Tape.mk₂, Tape.mk']⟩
        rw [Part.mem_unique hmem hhalt]
        simp [HetFoldStepState.start, HetFoldStepState.cont]
        exact not_hasHetInlHead_hetMix_nil acc
  | cons t ts =>
      let rest : List (Option (T ⊕ Γ₀)) := hetMix (T := T) (Γ₀ := Γ₀) ts acc
      let input : List (Option (T ⊕ Γ₀)) :=
        hetMix (T := T) (Γ₀ := Γ₀) (t :: ts) acc ++ [default]
      let Mstep := tm0HetFoldStepMachine (T := T) (Γ₀ := Γ₀) Λ M
      have hrest_nd : ∀ g ∈ rest, g ≠ (default : Option (T ⊕ Γ₀)) := by
        intro g hg
        have htail :
            (∃ a ∈ ts, some (Sum.inl a) = g) ∨
              g = hetSep (T := T) (Γ₀ := Γ₀) ∨
              ∃ a ∈ acc, hetAccEmb (T := T) a = g := by
          simpa [rest, hetMix, hetMixSep, separatedMix, hetTagEmb] using hg
        exact hblock g (by
          simp [hetMix, hetMixSep, separatedMix, hetTagEmb]
          exact Or.inr htail)
      have hF_nd : ∀ g ∈ F t rest, g ≠ (default : Option (T ⊕ Γ₀)) :=
        hf_nd t rest hrest_nd
      obtain ⟨hbody_dom, hbody_tape⟩ :=
        hM t rest [] hrest_nd (by simp) hF_nd
      let bodyCfg :=
        (TM0Seq.evalCfg (M t) (rest ++ [default])).get hbody_dom
      have hbody_mem : bodyCfg ∈ TM0Seq.evalCfg (M t) (rest ++ [default]) :=
        Part.get_mem hbody_dom
      obtain ⟨hbody_reach, hbody_halt⟩ := Turing.mem_eval.mp hbody_mem
      have hbody_tape' : bodyCfg.Tape = Tape.mk₁ (F t rest ++ [default]) :=
        hbody_tape hbody_dom
      have hstart :
          TM0.step Mstep ⟨HetFoldStepState.start, Tape.mk₁ input⟩ =
            some ⟨HetFoldStepState.move t,
              Tape.write default (Tape.mk₁ input)⟩ := by
        simp [TM0.step, Mstep, tm0HetFoldStepMachine, HetFoldStepState.start,
          HetFoldStepState.move, input, hetMix, hetMixSep, separatedMix,
          hetTagEmb, Tape.mk₁, Tape.mk₂, Tape.mk']
      have hmove :
          TM0.step Mstep
              ⟨HetFoldStepState.move t, Tape.write default (Tape.mk₁ input)⟩ =
            some ⟨HetFoldStepState.run t default, Tape.mk₁ (rest ++ [default])⟩ := by
        simp [TM0.step, Mstep, tm0HetFoldStepMachine, HetFoldStepState.move,
          HetFoldStepState.run]
        change Tape.move Dir.right
            (Tape.write default
              (Tape.mk₁ ((some (Sum.inl t) : Option (T ⊕ Γ₀)) ::
                (rest ++ [default])))) =
          Tape.mk₁ (rest ++ [default])
        exact tape_erase_step (some (Sum.inl t) : Option (T ⊕ Γ₀))
          (rest ++ [default])
      have hrun_reach :
          Reaches (TM0.step Mstep)
            ⟨HetFoldStepState.run t default, Tape.mk₁ (rest ++ [default])⟩
            ⟨HetFoldStepState.run t bodyCfg.q, bodyCfg.Tape⟩ :=
        tm0HetFoldStepMachine_run_reaches Λ M t hbody_reach
      have hfinal_step :
          TM0.step Mstep ⟨HetFoldStepState.run t bodyCfg.q, bodyCfg.Tape⟩ =
            some ⟨HetFoldStepState.cont, bodyCfg.Tape⟩ := by
        rcases bodyCfg with ⟨q, tape⟩
        unfold TM0.step at hbody_halt ⊢
        simp [Mstep, tm0HetFoldStepMachine, HetFoldStepState.run,
          HetFoldStepState.cont] at hbody_halt ⊢
        simpa [hbody_halt]
      have hreach :
          Reaches (TM0.step Mstep)
            (TM0.init input)
            ⟨HetFoldStepState.cont, bodyCfg.Tape⟩ := by
        let c0 : TM0.Cfg (Option (T ⊕ Γ₀)) (HetFoldStepState T Λ) :=
          TM0.init input
        let c1 : TM0.Cfg (Option (T ⊕ Γ₀)) (HetFoldStepState T Λ) :=
          ⟨HetFoldStepState.move t, Tape.write default (Tape.mk₁ input)⟩
        let c2 : TM0.Cfg (Option (T ⊕ Γ₀)) (HetFoldStepState T Λ) :=
          ⟨HetFoldStepState.run t default, Tape.mk₁ (rest ++ [default])⟩
        let c3 : TM0.Cfg (Option (T ⊕ Γ₀)) (HetFoldStepState T Λ) :=
          ⟨HetFoldStepState.run t bodyCfg.q, bodyCfg.Tape⟩
        have h01 : c1 ∈ TM0.step Mstep c0 := Option.mem_def.mpr hstart
        have h12 : c2 ∈ TM0.step Mstep c1 := Option.mem_def.mpr hmove
        have h34 :
            ⟨HetFoldStepState.cont, bodyCfg.Tape⟩ ∈ TM0.step Mstep c3 :=
          Option.mem_def.mpr hfinal_step
        have r01 : Reaches (TM0.step Mstep) c0 c1 :=
          Relation.ReflTransGen.single h01
        have r12 : Reaches (TM0.step Mstep) c1 c2 :=
          Relation.ReflTransGen.single h12
        exact ((r01.trans r12).trans hrun_reach).tail h34
      have hhalt :
          TM0.step Mstep ⟨HetFoldStepState.cont, bodyCfg.Tape⟩ = none := by
        simp [TM0.step, Mstep, tm0HetFoldStepMachine, HetFoldStepState.cont]
      constructor
      · apply Part.dom_iff_mem.mpr
        exact ⟨⟨HetFoldStepState.cont, bodyCfg.Tape⟩,
          Turing.mem_eval.mpr ⟨hreach, hhalt⟩⟩
      · intro h
        have hmem := Part.get_mem h
        have htarget :
            ⟨HetFoldStepState.cont, bodyCfg.Tape⟩ ∈
              TM0Seq.evalCfg Mstep input :=
          Turing.mem_eval.mpr ⟨hreach, hhalt⟩
        rw [Part.mem_unique hmem htarget]
        simp [hasHetInlHead, HetFoldStepState.cont, hbody_tape',
          hetFoldStep, prefixFoldStep, hetTagDecode, input, rest, hetMix,
          hetMixSep, separatedMix, hetTagEmb]

/-- `isWellFormedHetBlock` is preserved by `hetFoldStep` when the
    condition holds. -/
theorem isWellFormedHetBlock_step
    (F : T → List (Option (T ⊕ Γ₀)) → List (Option (T ⊕ Γ₀)))
    (f : T → List Γ₀ → List Γ₀)
    (hF : ∀ t ts acc, F t (hetMix (T := T) (Γ₀ := Γ₀) ts acc) = hetMix ts (f t acc))
    (hf_nd : ∀ t block, (∀ g ∈ block, g ≠ default) → ∀ g ∈ f t block, g ≠ default)
    (block : List (Option (T ⊕ Γ₀)))
    (hInv : isWellFormedHetBlock block)
    (hblock : ∀ g ∈ block, g ≠ (default : Option (T ⊕ Γ₀)))
    (hcond : hasHetInlHead block) :
    isWellFormedHetBlock (hetFoldStep F block) := by
  obtain ⟨ts, acc, rfl, hacc⟩ := hInv
  cases ts with
  | nil => exact absurd hcond (not_hasHetInlHead_hetMix_nil acc)
  | cons t ts =>
    rw [hetFoldStep_hetMix F f hF]
    exact ⟨ts, f t acc, rfl, hf_nd t acc hacc⟩

/-- `hetFoldWhile` equals an iteration that has actually stopped on
    well-formed blocks.  The semantic `hF` is the important assumption:
    each successful step removes one leading tag from the `hetMix` block. -/
theorem hetFoldWhile_eq_iterateWhile_wf
    (F : T → List (Option (T ⊕ Γ₀)) → List (Option (T ⊕ Γ₀)))
    (f : T → List Γ₀ → List Γ₀)
    (hF : ∀ t ts acc, F t (hetMix (T := T) (Γ₀ := Γ₀) ts acc) = hetMix ts (f t acc))
    (block : List (Option (T ⊕ Γ₀)))
    (hInv : isWellFormedHetBlock block) :
    ∃ n, hetFoldWhile F block =
      blockIterateWhile (hetFoldStep F) hasHetInlHead n block ∧
      ¬hasHetInlHead (blockIterateWhile (hetFoldStep F) hasHetInlHead n block) := by
  obtain ⟨ts, acc, rfl, _hacc⟩ := hInv
  refine ⟨ts.length, ?_, ?_⟩
  · unfold hetFoldWhile
    rw [takeWhile_isHetInl_hetMix, List.length_map]
  · have hiter :
        blockIterateWhile (hetFoldStep F) hasHetInlHead ts.length
            (hetMix (T := T) (Γ₀ := Γ₀) ts acc) =
          hetMix [] (List.foldl (fun a t => f t a) acc ts) := by
      rw [← hetFoldWhile_hetMix F f hF ts acc]
      unfold hetFoldWhile
      rw [takeWhile_isHetInl_hetMix, List.length_map]
    rw [hiter]
    simpa [hetMix] using
      (not_hasHetInlHead_hetMix_nil
        (T := T) (Γ₀ := Γ₀) (List.foldl (fun a t => f t a) acc ts))

/-- **Het fold while loop machine exists for well-formed blocks.**

    Derived from:
    - a supplied conditional body machine for `hetFoldStep`
    - `tm0RealizesBlock_while_inv` (while-loop combinator with invariant)
    - `hetFoldWhile_eq_iterateWhile_wf` (iteration equals definition) -/
theorem tm0RealizesBlock_hetFoldWhile_inv
    (F : T → List (Option (T ⊕ Γ₀)) → List (Option (T ⊕ Γ₀)))
    (f : T → List Γ₀ → List Γ₀)
    (hF : ∀ t ts acc, F t (hetMix (T := T) (Γ₀ := Γ₀) ts acc) = hetMix ts (f t acc))
    (hf_block : ∀ t, TM0RealizesBlock (Option (T ⊕ Γ₀)) (F t))
    (hF_nd : ∀ t block, (∀ g ∈ block, g ≠ default) → ∀ g ∈ F t block, g ≠ default)
    (hf_nd : ∀ t block, (∀ g ∈ block, g ≠ default) → ∀ g ∈ f t block, g ≠ default) :
    ∃ (Λ : Type) (_ : Inhabited Λ) (_ : Fintype Λ)
      (M : TM0.Machine (Option (T ⊕ Γ₀)) Λ),
      ∀ (block : List (Option (T ⊕ Γ₀))),
        isWellFormedHetBlock block →
        (∀ g ∈ block, g ≠ (default : Option (T ⊕ Γ₀))) →
        (∀ g ∈ hetFoldWhile F block, g ≠ (default : Option (T ⊕ Γ₀))) →
        (TM0Seq.evalCfg M (block ++ [default])).Dom ∧
        ∀ (h : (TM0Seq.evalCfg M (block ++ [default])).Dom),
          ((TM0Seq.evalCfg M (block ++ [default])).get h).Tape =
            Tape.mk₁ (hetFoldWhile F block ++ [default]) :=
  tm0RealizesBlock_while_inv
    (hetFoldStep F) (hetFoldWhile F) hasHetInlHead
    isWellFormedHetBlock
    (tm0RealizesBlockCond_hetFoldStep F hf_block hF_nd)
    (fun block hInv hnd hcond => isWellFormedHetBlock_step F f hF hf_nd block hInv hnd hcond)
    (fun block hblock hcond => hetFoldStep_ne_default F hF_nd block hblock hcond)
    (fun block _hblock hInv => hetFoldWhile_eq_iterateWhile_wf F f hF block hInv)
    (fun block hblock _hInv => hetFoldWhile_ne_default F hF_nd block hblock)

/-- `w.map (some ∘ Sum.inl) ++ [hetSep]` forms a well-formed het block. -/
theorem isWellFormedHetBlock_map_inl_sep (w : List T) :
    isWellFormedHetBlock (T := T) (Γ₀ := Γ₀)
      (w.map (some ∘ Sum.inl) ++ [hetSep (T := T) (Γ₀ := Γ₀)]) := by
  exact ⟨w, [], by simp [hetMix, hetMixSep, separatedMix, hetTagEmb], by simp⟩

/-- Reversed well-formed het block is still well-formed. -/
theorem isWellFormedHetBlock_reverse_map_inl_sep (w : List T) :
    isWellFormedHetBlock (T := T) (Γ₀ := Γ₀)
      ((w.map (some ∘ Sum.inl)).reverse ++
        [hetSep (T := T) (Γ₀ := Γ₀)]) := by
  rw [← List.map_reverse]
  exact ⟨w.reverse, [], by simp [hetMix, hetMixSep, separatedMix, hetTagEmb], by simp⟩

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
    (F : T → List (Option (T ⊕ Γ₀)) → List (Option (T ⊕ Γ₀)))
    (f : T → List Γ₀ → List Γ₀)
    (hF : ∀ t ts acc, F t (hetMix (T := T) (Γ₀ := Γ₀) ts acc) = hetMix ts (f t acc))
    (hf_block : ∀ t, TM0RealizesBlock (Option (T ⊕ Γ₀)) (F t))
    (hF_nd : ∀ t block, (∀ g ∈ block, g ≠ default) →
      ∀ g ∈ F t block, g ≠ default)
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
  let Γ := Option (T ⊕ Γ₀)
  let sep : Γ := hetSep (T := T) (Γ₀ := Γ₀)
  have hsep_nd : sep ≠ (default : Γ) := by
    simp [sep, hetSep]

  have hcons_nd :
      ∀ block : List Γ, (∀ g ∈ block, g ≠ default) →
        ∀ g ∈ (sep :: block), g ≠ default := by
    intro block hblock g hg
    simp only [List.mem_cons] at hg
    rcases hg with rfl | hg
    · exact hsep_nd
    · exact hblock g hg

  have hrev_cons_block :
      TM0RealizesBlock Γ (List.reverse ∘ (fun block : List Γ => sep :: block)) :=
    tm0RealizesBlock_comp
      (tm0_cons_block sep hsep_nd)
      (tm0_reverse_block (Γ := Γ))
      hcons_nd

  obtain ⟨Λ₁, hΛ₁i, hΛ₁f, M₁, hM₁⟩ := hrev_cons_block
  obtain ⟨Λ₂, hΛ₂i, hΛ₂f, M₂, hM₂⟩ :=
    tm0RealizesBlock_hetFoldWhile_inv F f hF hf_block hF_nd hf_nd
  obtain ⟨Λ₃, hΛ₃i, hΛ₃f, M₃, hM₃⟩ :=
    tm0_dropUntilFirstSep_block sep hsep_nd

  letI : Inhabited (Λ₂ ⊕ Λ₃) := ⟨Sum.inl default⟩
  let M₂₃ : TM0.Machine Γ (Λ₂ ⊕ Λ₃) := TM0Seq.compose M₂ M₃
  letI : Inhabited (Λ₁ ⊕ (Λ₂ ⊕ Λ₃)) := ⟨Sum.inl default⟩
  let M : TM0.Machine Γ (Λ₁ ⊕ (Λ₂ ⊕ Λ₃)) := TM0Seq.compose M₁ M₂₃

  refine ⟨Λ₁ ⊕ (Λ₂ ⊕ Λ₃), inferInstance, inferInstance, M, ?_⟩
  intro w
  let input : List Γ := w.map (some ∘ @Sum.inl T Γ₀)
  let mid : List Γ := (List.reverse ∘ (fun block : List Γ => sep :: block)) input
  let folded : List Γ := hetFoldWhile F mid
  let output : List Γ := dropUntilFirstSep sep folded

  have hinput_nd : ∀ g ∈ input, g ≠ (default : Γ) := by
    simpa [input, Γ] using (map_inl_ne_default (T := T) (Γ₀ := Γ₀) w)
  have hmid_eq : mid =
      (w.map (some ∘ @Sum.inl T Γ₀)).reverse ++
        [hetSep (T := T) (Γ₀ := Γ₀)] := by
    simp [mid, input, sep, Function.comp]
  have hmid_wf : isWellFormedHetBlock (T := T) (Γ₀ := Γ₀) mid := by
    rw [hmid_eq]
    exact isWellFormedHetBlock_reverse_map_inl_sep (T := T) (Γ₀ := Γ₀) w
  have hmid_nd : ∀ g ∈ mid, g ≠ (default : Γ) := by
    rw [hmid_eq]
    intro g hg
    simp only [List.mem_append, List.mem_reverse, List.mem_map,
      Function.comp, List.mem_singleton] at hg
    rcases hg with htag | hsep
    · rcases htag with ⟨t, _ht, rfl⟩
      simp [Γ]
    · rw [hsep]
      exact hsep_nd
  have hfolded_nd : ∀ g ∈ folded, g ≠ (default : Γ) := by
    exact hetFoldWhile_ne_default F hF_nd mid hmid_nd
  have houtput_nd : ∀ g ∈ output, g ≠ (default : Γ) := by
    exact dropUntilFirstSep_ne_default sep folded hfolded_nd
  have hfolded_eq :
      folded = hetMix (T := T) (Γ₀ := Γ₀) [] (List.foldr f [] w) := by
    simp [folded]
    rw [hmid_eq]
    exact hetFold_decomp F f hF w
  have houtput_eq :
      output = (List.foldr f [] w).map (some ∘ @Sum.inr T Γ₀) := by
    simp [output, hfolded_eq, sep, hetMix, hetMixSep, separatedMix, hetSep,
      hetAccEmb, dropUntilFirstSep]

  have hM₁_eval := hM₁ input [] hinput_nd (by simp) (by
    simpa [mid] using hmid_nd)
  obtain ⟨hM₁_dom, hM₁_tape⟩ := hM₁_eval

  have hM₂_eval := hM₂ mid hmid_wf hmid_nd hfolded_nd
  obtain ⟨hM₂_dom, hM₂_tape⟩ := hM₂_eval

  have hM₃_eval := hM₃ folded [] hfolded_nd (by simp) houtput_nd
  obtain ⟨hM₃_dom, hM₃_tape⟩ := hM₃_eval

  have hM₂M₃_dom :
      (TM0Seq.evalCfg M₂₃ (mid ++ [default])).Dom := by
    change (TM0Seq.evalCfg (TM0Seq.compose M₂ M₃) (mid ++ [default])).Dom
    exact (TM0Seq.compose_dom_iff' M₂ M₃ (mid ++ [default])
      (folded ++ [default]) hM₂_dom (hM₂_tape hM₂_dom)).2 hM₃_dom

  have hM₂M₃_tape
      (h : (TM0Seq.evalCfg M₂₃ (mid ++ [default])).Dom) :
      ((TM0Seq.evalCfg M₂₃ (mid ++ [default])).get h).Tape =
        Tape.mk₁ (output ++ [default]) := by
    change ((TM0Seq.evalCfg (TM0Seq.compose M₂ M₃) (mid ++ [default])).get h).Tape =
      Tape.mk₁ (output ++ [default])
    rw [TM0Seq.compose_evalCfg_tape M₂ M₃ (mid ++ [default])
      (folded ++ [default]) hM₂_dom (hM₂_tape hM₂_dom) hM₃_dom h,
      hM₃_tape hM₃_dom]

  have hcomp_dom_default :
      (TM0Seq.evalCfg M (input ++ [default])).Dom := by
    change (TM0Seq.evalCfg (TM0Seq.compose M₁ M₂₃) (input ++ [default])).Dom
    exact (TM0Seq.compose_dom_iff' M₁ M₂₃ (input ++ [default])
      (mid ++ [default]) hM₁_dom (hM₁_tape hM₁_dom)).2 hM₂M₃_dom

  have hcomp_tape_default
      (h : (TM0Seq.evalCfg M (input ++ [default])).Dom) :
      ((TM0Seq.evalCfg M (input ++ [default])).get h).Tape =
          Tape.mk₁ (output ++ [default]) := by
    change ((TM0Seq.evalCfg (TM0Seq.compose M₁ M₂₃)
      (input ++ [default])).get h).Tape = Tape.mk₁ (output ++ [default])
    rw [TM0Seq.compose_evalCfg_tape M₁ M₂₃
      (input ++ [default]) (mid ++ [default]) hM₁_dom
      (hM₁_tape hM₁_dom) hM₂M₃_dom h]
    exact hM₂M₃_tape hM₂M₃_dom

  have heval_input :
      TM0Seq.evalCfg M input = TM0Seq.evalCfg M (input ++ [default]) := by
    rw [evalCfg_append_default]

  constructor
  · change (TM0Seq.evalCfg M input).Dom
    rw [heval_input]
    exact hcomp_dom_default
  · intro h
    have h' :
        (TM0Seq.evalCfg M (input ++ [default])).Dom := by
      rw [← heval_input]
      exact h
    change ((TM0Seq.evalCfg M input).get h).Tape =
      Tape.mk₁ ((List.foldr f [] w).map (some ∘ @Sum.inr T Γ₀))
    have hget :
        (TM0Seq.evalCfg M input).get h =
          (TM0Seq.evalCfg M (input ++ [default])).get h' := by
      apply Part.get_eq_get_of_eq
      exact heval_input
    rw [hget]
    rw [hcomp_tape_default h', houtput_eq, tape_mk₁_append_default]

end HetFold
