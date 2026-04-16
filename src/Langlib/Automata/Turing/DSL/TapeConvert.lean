import Mathlib
import Langlib.Automata.Turing.DSL.Compile
import Langlib.Automata.Turing.DSL.TM0Compose

/-! # Tape Conversion: Identity Encoding → Chain Format

This file provides the infrastructure for converting between identity-encoded
input and the Partrec chain's tape format.

## Architecture

We define `TM0Realizes Γ f` — asserting that a total function `f` on
tape lists can be computed by a TM0 machine that always halts with
`Tape.mk₁ (f input)`. We then show:

1. `TM0Realizes` is closed under composition (`tm0Realizes_comp`).
2. A halting converter can be composed with any machine to run the latter
   on the converter's output (`tm0Realizes_compose_eval`).
3. The full converter function is TM0-realizable (`converter_fn_realizes`).
4. `converter_tm_exists` (in `EncodingBridge.lean`) follows from these.

## Blank-Preserving Embedding

The blank-preserving embedding `blankPreservingEmb` and its inverse are
defined here (used by `EncodingBridge.lean` for alphabet lifting).
-/

open Turing PartrecToTM2 TM2to1

/-! ### Blank-Preserving Embedding -/

/-- Embed a `Γ₀` value into `Option (T ⊕ Γ₀)`, mapping the default
(blank) to `none` and everything else to `some (Sum.inr γ)`. -/
noncomputable def blankPreservingEmb {T Γ₀ : Type} [DecidableEq Γ₀] [Inhabited Γ₀]
    (γ : Γ₀) : Option (T ⊕ Γ₀) :=
  if γ = default then none else some (Sum.inr γ)

/-- Inverse of `blankPreservingEmb`: extract the `Γ₀` component,
defaulting to `default` for `none` or `Sum.inl` values. -/
noncomputable def blankPreservingInv {T Γ₀ : Type} [Inhabited Γ₀]
    (a : Option (T ⊕ Γ₀)) : Γ₀ :=
  match a with
  | some (Sum.inr γ) => γ
  | _ => default

theorem blankPreservingEmb_default {T Γ₀ : Type} [DecidableEq Γ₀] [Inhabited Γ₀] :
    blankPreservingEmb (T := T) (default : Γ₀) = (default : Option (T ⊕ Γ₀)) := by
  unfold blankPreservingEmb
  simp [show (default : Option (T ⊕ Γ₀)) = none from rfl]

theorem blankPreservingInv_emb {T Γ₀ : Type} [DecidableEq Γ₀] [Inhabited Γ₀]
    (γ : Γ₀) : blankPreservingInv (T := T) (blankPreservingEmb γ) = γ := by
  unfold blankPreservingEmb blankPreservingInv
  split <;> simp_all

/-! ### DecidableEq for ChainΓ -/

instance decEqChainΓ : DecidableEq ChainΓ :=
  instDecidableEqProd (α := Bool) (β := (PartrecToTM2.K' → Option PartrecToTM2.Γ'))

/-! ### Distinguished ChainΓ cells -/

/-- The ChainΓ value representing a bit-0 in the main track. -/
noncomputable def chainBit0 : ChainΓ :=
  (false, Function.update (fun _ => none) K'.main (some Γ'.bit0))

/-- The ChainΓ value representing a bit-1 in the main track. -/
noncomputable def chainBit1 : ChainΓ :=
  (false, Function.update (fun _ => none) K'.main (some Γ'.bit1))

/-! ### TM0 Realizability -/

/-- A total function `f : List Γ → List Γ` is **TM0-realizable** if there
exists a finite-state TM0 machine that always halts on any input `l` and
produces `Tape.mk₁ (f l)` as the output tape. -/
def TM0Realizes (Γ : Type) [Inhabited Γ] (f : List Γ → List Γ) : Prop :=
  ∃ (Λ : Type) (_ : Inhabited Λ) (_ : Fintype Λ)
    (M : TM0.Machine Γ Λ),
    ∀ l : List Γ,
      (TM0Seq.evalCfg M l).Dom ∧
      ∀ (h : (TM0Seq.evalCfg M l).Dom),
        ((TM0Seq.evalCfg M l).get h).Tape = Tape.mk₁ (f l)

/-! ### Compose output tape tracking -/

/-
When `evalCfg` halts, the step at the halting config is `none`.
-/
theorem evalCfg_step_none {Γ : Type} [Inhabited Γ]
    {Λ : Type} [Inhabited Λ]
    (M : TM0.Machine Γ Λ) (l : List Γ)
    (h : (TM0Seq.evalCfg M l).Dom) :
    TM0.step M ((TM0Seq.evalCfg M l).get h) = none := by
  have := @Turing.mem_eval;
  exact this.mp ( Part.get_mem _ ) |>.2

/-
From M₁'s halt state, the composed machine's eval gives a config whose
tape matches M₂'s eval output tape.
-/
theorem TM0Seq.compose_eval_from_halt_tape {Γ : Type} [Inhabited Γ]
    {Λ₁ : Type} [Inhabited Λ₁] {Λ₂ : Type} [Inhabited Λ₂]
    (M₁ : TM0.Machine Γ Λ₁) (M₂ : TM0.Machine Γ Λ₂)
    (q₁ : Λ₁) (T : Tape Γ)
    (h_halt : TM0.step M₁ ⟨q₁, T⟩ = none)
    (h₂ : (TM0Seq.evalFromCfg M₂ ⟨default, T⟩).Dom) :
    ∃ c : TM0.Cfg Γ (Λ₁ ⊕ Λ₂),
      c ∈ @Turing.eval (TM0.Cfg Γ (Λ₁ ⊕ Λ₂))
        (@TM0.step Γ (Λ₁ ⊕ Λ₂) ⟨Sum.inl default⟩ _
          (TM0Seq.compose M₁ M₂))
        ⟨Sum.inl q₁, T⟩ ∧
      c.Tape = ((TM0Seq.evalFromCfg M₂ ⟨default, T⟩).get h₂).Tape := by
  by_cases h₂' : TM0.step M₂ ⟨ default, T ⟩ = none;
  · have h_c₂ : (evalFromCfg M₂ ⟨default, T⟩).get h₂ = ⟨default, T⟩ := by
      have h_c₂ : ∀ c ∈ eval (TM0.step M₂) ⟨default, T⟩, c = ⟨default, T⟩ := by
        intro c hc; exact (by
        exact (by
          have := hc;
          rw [ eval ] at this;
          rw [ PFun.mem_fix_iff ] at this;
          aesop
        ));
      exact h_c₂ _ ( Part.get_mem _ );
    use ⟨Sum.inl q₁, T⟩;
    rw [ Turing.eval ];
    rw [ PFun.mem_fix_iff ];
    rw [ TM0Seq.compose_step_on_halt ] <;> aesop;
  · obtain ⟨ c₂', hc₂' ⟩ := Option.ne_none_iff_exists'.mp h₂';
    have h_reaches : TM0Seq.evalFromCfg M₂ ⟨ default, T ⟩ = TM0Seq.evalFromCfg M₂ c₂' := by
      apply Turing.reaches_eval;
      exact Relation.ReflTransGen.single hc₂';
    have h_tr_eval : ∀ {c₂ : TM0.Cfg Γ Λ₂} {c : TM0.Cfg Γ (Λ₁ ⊕ Λ₂)},
      c₂.Tape = c.Tape →
      c.q = Sum.inr c₂.q →
      ∀ {c₂_final : TM0.Cfg Γ Λ₂},
        c₂_final ∈ Turing.eval (TM0.step M₂) c₂ →
        ∃ b₂ : TM0.Cfg Γ (Λ₁ ⊕ Λ₂),
          b₂.Tape = c₂_final.Tape ∧ b₂ ∈ Turing.eval (@TM0.step Γ (Λ₁ ⊕ Λ₂) ⟨Sum.inl default⟩ _ (compose M₁ M₂)) c := by
            intros c₂ c hc₂ hc q₂ hq₂;
            have := TM0Seq.compose_phase2_respects M₁ M₂;
            have := tr_eval this ⟨ hc, hc₂.symm ⟩ hq₂;
            exact ⟨ this.choose, this.choose_spec.1.2, this.choose_spec.2 ⟩;
    obtain ⟨c₂_final, hc₂_final⟩ : ∃ c₂_final : TM0.Cfg Γ Λ₂,
        c₂_final ∈ Turing.eval (TM0.step M₂) c₂' ∧
        c₂_final.Tape = ((evalFromCfg M₂ { q := default, Tape := T }).get h₂).Tape := by
                                            use (evalFromCfg M₂ { q := default, Tape := T }).get h₂;
                                            simp [h_reaches];
                                            exact Part.get_mem _;
    have h_reaches : Turing.eval (@TM0.step Γ (Λ₁ ⊕ Λ₂) ⟨Sum.inl default⟩ _ (compose M₁ M₂)) ⟨Sum.inl q₁, T⟩ = Turing.eval (@TM0.step Γ (Λ₁ ⊕ Λ₂) ⟨Sum.inl default⟩ _ (compose M₁ M₂)) ⟨Sum.inr c₂'.q, c₂'.Tape⟩ := by
      apply reaches_eval;
      apply Relation.ReflTransGen.single;
      rw [ TM0Seq.compose_step_on_halt ] <;> aesop;
    exact h_reaches.symm ▸ h_tr_eval rfl rfl hc₂_final.1 |> fun ⟨ b₂, hb₂₁, hb₂₂ ⟩ => ⟨ b₂, hb₂₂, hb₂₁.trans hc₂_final.2 ⟩

/-- The composed machine's eval result is related to M₂'s eval result
via the phase 2 bisimulation. Specifically, if M₁ halts with tape
`Tape.mk₁ l'` and M₂ halts on `l'`, then there exists a config in
the composed machine's eval that has the same tape as M₂'s output. -/
theorem TM0Seq.compose_eval_tape_mem {Γ : Type} [Inhabited Γ]
    {Λ₁ : Type} [Inhabited Λ₁] {Λ₂ : Type} [Inhabited Λ₂]
    (M₁ : TM0.Machine Γ Λ₁) (M₂ : TM0.Machine Γ Λ₂)
    (l l' : List Γ)
    (h₁ : (TM0Seq.evalCfg M₁ l).Dom)
    (h₁_tape : ((TM0Seq.evalCfg M₁ l).get h₁).Tape = Tape.mk₁ l')
    (h₂ : (TM0Seq.evalCfg M₂ l').Dom) :
    ∃ c : TM0.Cfg Γ (Λ₁ ⊕ Λ₂),
      c ∈ @Turing.eval (TM0.Cfg Γ (Λ₁ ⊕ Λ₂))
        (@TM0.step Γ (Λ₁ ⊕ Λ₂) ⟨Sum.inl default⟩ _
          (TM0Seq.compose M₁ M₂))
        (@TM0.init Γ (Λ₁ ⊕ Λ₂) ⟨Sum.inl default⟩ _ l) ∧
      c.Tape = ((TM0Seq.evalCfg M₂ l').get h₂).Tape := by
  -- Get M₁'s halting config and its halt proof
  set c₁ := (TM0Seq.evalCfg M₁ l).get h₁
  have h_step_none := evalCfg_step_none M₁ l h₁
  -- Use compose_eval_split to rewrite eval from init to eval from M₁'s halt state
  have h_split := TM0Seq.compose_eval_split M₁ M₂ l h₁
  -- Get the tape equality from compose_eval_from_halt_tape
  have h₂' : (TM0Seq.evalFromCfg M₂ ⟨default, c₁.Tape⟩).Dom := by
    rw [h₁_tape]; exact h₂
  obtain ⟨c, hc_mem, hc_tape⟩ := TM0Seq.compose_eval_from_halt_tape M₁ M₂
    c₁.q c₁.Tape h_step_none h₂'
  -- c is in eval compose from ⟨Sum.inl c₁.q, c₁.Tape⟩
  -- By compose_eval_split, this equals eval compose from init l
  refine ⟨c, ?_, ?_⟩
  · rw [h_split]; exact hc_mem
  · rw [hc_tape]
    congr 1
    apply Part.get_eq_get_of_eq
    show TM0Seq.evalFromCfg M₂ ⟨default, c₁.Tape⟩ = TM0Seq.evalCfg M₂ l'
    rw [h₁_tape]; rfl

/-- When the composed machine halts, its output tape matches M₂'s output tape. -/
theorem TM0Seq.compose_evalCfg_tape {Γ : Type} [Inhabited Γ]
    {Λ₁ : Type} [Inhabited Λ₁] {Λ₂ : Type} [Inhabited Λ₂]
    (M₁ : TM0.Machine Γ Λ₁) (M₂ : TM0.Machine Γ Λ₂)
    (l l' : List Γ)
    (h₁ : (TM0Seq.evalCfg M₁ l).Dom)
    (h₁_tape : ((TM0Seq.evalCfg M₁ l).get h₁).Tape = Tape.mk₁ l')
    (h₂ : (TM0Seq.evalCfg M₂ l').Dom)
    (h_comp : (@TM0Seq.evalCfg Γ _ (Λ₁ ⊕ Λ₂) ⟨Sum.inl default⟩
      (TM0Seq.compose M₁ M₂) l).Dom) :
    ((@TM0Seq.evalCfg Γ _ (Λ₁ ⊕ Λ₂) ⟨Sum.inl default⟩
      (TM0Seq.compose M₁ M₂) l).get h_comp).Tape =
    ((TM0Seq.evalCfg M₂ l').get h₂).Tape := by
  obtain ⟨c, hc_mem, hc_tape⟩ := TM0Seq.compose_eval_tape_mem M₁ M₂ l l' h₁ h₁_tape h₂
  have h_get_mem := Part.get_mem h_comp
  have h_unique := Part.mem_unique h_get_mem hc_mem
  rw [h_unique]; exact hc_tape

/-! ### TM0Realizes closure properties -/

/-- Composition of TM0-realizable functions is TM0-realizable.
Uses `TM0Seq.compose` for sequential composition of TM0 machines,
and `compose_evalCfg_tape` for output tape tracking. -/
theorem tm0Realizes_comp {Γ : Type} [Inhabited Γ]
    {f g : List Γ → List Γ}
    (hg : TM0Realizes Γ g) (hf : TM0Realizes Γ f) :
    TM0Realizes Γ (f ∘ g) := by
  obtain ⟨Λ_g, _, _, M_g, hg⟩ := hg
  obtain ⟨Λ_f, _, _, M_f, hf⟩ := hf
  letI : Inhabited (Λ_g ⊕ Λ_f) := ⟨Sum.inl default⟩
  exact ⟨Λ_g ⊕ Λ_f, inferInstance, inferInstance,
    TM0Seq.compose M_g M_f, fun l => by
    have hg_dom := (hg l).1
    have hg_tape := (hg l).2 hg_dom
    have hf_dom := (hf (g l)).1
    have hf_tape := (hf (g l)).2 hf_dom
    constructor
    · -- The composed machine halts
      rw [TM0Seq.evalCfg_dom_iff]
      exact (TM0Seq.compose_dom_iff' M_g M_f l (g l) hg_dom hg_tape).mpr
        ((TM0Seq.evalCfg_dom_iff M_f (g l)).mp hf_dom)
    · -- The output tape is correct
      intro h_comp
      rw [TM0Seq.compose_evalCfg_tape M_g M_f l (g l) hg_dom hg_tape hf_dom h_comp]
      exact hf_tape⟩

/-- The identity function is TM0-realizable (by an immediately-halting TM). -/
theorem tm0Realizes_id (Γ : Type) [Inhabited Γ] :
    TM0Realizes Γ id := by
  refine' ⟨ PUnit, inferInstance, inferInstance, fun _ _ => none, _ ⟩;
  intro l; exact ⟨by
  constructor;
  swap;
  constructor;
  all_goals simp +decide [ TM0.step ];
  exact ⟨ ⟨ ⟩, by tauto ⟩, by
    intro h; exact (by
    obtain ⟨ n, hn ⟩ := h;
    cases n ; tauto);⟩

/-! ### Composition of halting converter with another machine -/

/-- **Halting converter composition**: If `f` is TM0-realizable (always halts and
produces `Tape.mk₁ (f l)`), then for any machine `M₂`, there exists a composed
machine that halts on `l` iff `M₂` halts on `f l`.

This is the key lemma for composing a tape-converting machine with a
computation machine: the converter transforms the input format, then
the computation machine runs on the converted input.

**Example use**: Given a converter that transforms identity-encoded input
`w.map (Sum.inl ∘ some)` into chain format, and the Partrec chain machine `M₀`,
the composed machine halts on identity-encoded input iff `M₀` halts on chain
format — bridging the encoding gap. -/
theorem tm0Realizes_compose_eval {Γ : Type} [Inhabited Γ]
    {f : List Γ → List Γ} (hf : TM0Realizes Γ f)
    {Λ₂ : Type} [Inhabited Λ₂] [Fintype Λ₂] (M₂ : TM0.Machine Γ Λ₂) :
    ∃ (Λ : Type) (_ : Inhabited Λ) (_ : Fintype Λ) (M : TM0.Machine Γ Λ),
      ∀ l : List Γ,
        (TM0.eval M l).Dom ↔ (TM0.eval M₂ (f l)).Dom := by
  obtain ⟨Λ₁, hΛ₁i, hΛ₁f, M₁, hM₁⟩ := hf
  letI : Inhabited (Λ₁ ⊕ Λ₂) := ⟨Sum.inl default⟩
  exact ⟨Λ₁ ⊕ Λ₂, inferInstance, inferInstance,
    TM0Seq.compose M₁ M₂, fun l => by
    have h1 := (hM₁ l).1
    have h2 := (hM₁ l).2 h1
    exact TM0Seq.compose_dom_iff' M₁ M₂ l (f l) h1 h2⟩

/-! ### Identity Decoding -/

/-- Extract a `List T` from an identity-encoded tape. Elements that are not
of the form `some (Sum.inl t)` are ignored. -/
def identityDecode {T Γ₀ : Type} (l : List (Option (T ⊕ Γ₀))) : List T :=
  l.filterMap (fun a => match a with | some (Sum.inl t) => some t | _ => none)

/-
Identity decoding of identity-encoded input recovers the original list.
-/
theorem identityDecode_identity {T Γ₀ : Type} (w : List T) :
    identityDecode (Γ₀ := Γ₀) (w.map (fun x => some (Sum.inl x))) = w := by
  unfold identityDecode; induction w <;> aesop;

/-! ### Converter Function -/

/-- The converter function: maps any list over `Option (T ⊕ ChainΓ)` to the
chain tape format of the identity-decoded input.

For identity-encoded input `w.map (fun x => some (Sum.inl x))`, this produces
`(trInit K'.main (trList [Encodable.encode w])).map blankPreservingEmb`. -/
noncomputable def converter_fn (T : Type) [DecidableEq T] [Fintype T] [Primcodable T]
    (l : List (Option (T ⊕ ChainΓ))) : List (Option (T ⊕ ChainΓ)) :=
  (TM2to1.trInit PartrecToTM2.K'.main
    (PartrecToTM2.trList [Encodable.encode (identityDecode l)])).map
      (blankPreservingEmb (T := T))

/-- The converter function applied to identity-encoded input gives the
expected chain tape format output. -/
theorem converter_fn_on_identity {T : Type} [DecidableEq T] [Fintype T] [Primcodable T]
    (w : List T) :
    converter_fn T (w.map (fun x => some (Sum.inl x))) =
    (TM2to1.trInit PartrecToTM2.K'.main
      (PartrecToTM2.trList [Encodable.encode w])).map (blankPreservingEmb (T := T)) := by
  simp [converter_fn, identityDecode_identity]

/-! ### Converter TM0 Realizability -/

/-- **Converter TM0 realizability**: The converter function is TM0-realizable.

This is the key lemma for `converter_tm_exists`. It asserts that there exists
a TM0 over `Option (T ⊕ ChainΓ)` that always halts and maps any input `l`
to `converter_fn T l`.

The construction proceeds by:
1. Reading identity-encoded input right-to-left, maintaining an accumulator
   for `Encodable.encode (identityDecode l)` via iterated `Nat.pair + 1`
2. Converting the accumulator to `trInit K'.main (trList [acc])` format
3. Mapping through `blankPreservingEmb`

Since `T` is `Fintype`, each `Encodable.encode t` is a compile-time constant
that can be hardcoded in the TM's finite state. The binary arithmetic
(successor, addition, multiplication for `Nat.pair`) uses `chainBit0/chainBit1`
cells on the tape's work area. -/
theorem converter_fn_realizes {T : Type} [DecidableEq T] [Fintype T] [Primcodable T] :
    TM0Realizes (Option (T ⊕ ChainΓ)) (converter_fn T) := by
  sorry

/-! ### Binary Successor (supporting infrastructure) -/

/-- States for binary successor TM. -/
inductive BinSuccState
  | carry     -- propagating carry, about to read next bit
  | moveRight -- just wrote bit0, need to move right to continue carry
  | done      -- finished incrementing, halt
  deriving DecidableEq, Fintype, Inhabited

/-- Binary successor TM0 over `Option (T ⊕ ChainΓ)`.
Head starts at LSB. Increments the number by 1 and halts. -/
noncomputable def binSuccTM (T : Type) [DecidableEq T] :
    TM0.Machine (Option (T ⊕ ChainΓ)) BinSuccState := fun q a =>
  match q with
  | .carry =>
    if a = some (Sum.inr chainBit0) then
      some (.done, .write (some (Sum.inr chainBit1)))
    else if a = some (Sum.inr chainBit1) then
      some (.moveRight, .write (some (Sum.inr chainBit0)))
    else if a = none then
      some (.done, .write (some (Sum.inr chainBit1)))
    else
      none
  | .moveRight =>
    some (.carry, .move .right)
  | .done =>
    none

/-- The successor TM halts on any binary input. -/
theorem binSuccTM_halts (T : Type) [DecidableEq T]
    (l : List (Option (T ⊕ ChainΓ))) :
    (TM0Seq.evalCfg (binSuccTM T) l).Dom := by
  sorry

/-! ### Main Converter -/