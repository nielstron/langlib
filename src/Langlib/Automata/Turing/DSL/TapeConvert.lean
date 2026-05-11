import Mathlib
import Langlib.Automata.Turing.DSL.Compile
import Langlib.Automata.Turing.DSL.TM0Compose
import Langlib.Automata.Turing.DSL.TM0BuildingBlocks
import Langlib.Automata.Turing.DSL.ChainEncodeDecomp

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
3. The full converter function is TM0-realizable (`chain_converter_fn_realizes`).
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

/-! ### TM0 Realizability (Homogeneous) -/

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
machine that halts on `l` iff `M₂` halts on `f l`. -/
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

/-! ### General Converter Function -/

/-- General converter function: given a target alphabet `Γ₀` and an encoding
function `encode_fn : List T → List Γ₀`, maps any list over `Option (T ⊕ Γ₀)`
to `(encode_fn (identityDecode l)).map blankPreservingEmb`. -/
noncomputable def converter_fn {T Γ₀ : Type} [DecidableEq T] [DecidableEq Γ₀] [Inhabited Γ₀]
    (encode_fn : List T → List Γ₀)
    (l : List (Option (T ⊕ Γ₀))) : List (Option (T ⊕ Γ₀)) :=
  (encode_fn (identityDecode l)).map (blankPreservingEmb (T := T))

/-- The converter function applied to identity-encoded input gives the
expected output. -/
theorem converter_fn_on_identity {T Γ₀ : Type} [DecidableEq T] [DecidableEq Γ₀] [Inhabited Γ₀]
    (encode_fn : List T → List Γ₀)
    (w : List T) :
    converter_fn encode_fn (w.map (fun x => some (Sum.inl x))) =
    (encode_fn w).map (blankPreservingEmb (T := T)) := by
  simp [converter_fn, identityDecode_identity]


/-- The chain encoding function: encodes a `List T` into the chain tape format
`trInit K'.main (trList [Encodable.encode w])`. -/
noncomputable def chainEncode (T : Type) [Primcodable T]
    (w : List T) : List ChainΓ :=
  TM2to1.trInit PartrecToTM2.K'.main
    (PartrecToTM2.trList [Encodable.encode w])

/-- The chain converter function is the general converter instantiated with
`chainEncode`. -/
noncomputable def chain_converter_fn (T : Type) [DecidableEq T] [Primcodable T] :=
  converter_fn (chainEncode T)

/-- The chain converter applied to identity-encoded input gives the expected
chain tape format output. -/
theorem chain_converter_fn_on_identity {T : Type} [DecidableEq T] [Primcodable T]
    (w : List T) :
    chain_converter_fn T (w.map (fun x => some (Sum.inl x))) =
    (chainEncode T w).map (blankPreservingEmb (T := T)) :=
  converter_fn_on_identity (chainEncode T) w

/-! ### Chain encoding never produces default ChainΓ -/

/-
Every element of `trInit k L` is non-default. The first element has
`true` as its bottom marker (while default has `false`), and the remaining
elements have `some a` in stack `k` (while default has `none`).
-/
theorem trInit_ne_default (k : PartrecToTM2.K') (L : List PartrecToTM2.Γ') :
    ∀ γ ∈ trInit k L, γ ≠ (default : ChainΓ) := by
  unfold trInit;
  simp +zetaDelta at *;
  constructor;
  · intro h; have := congr_arg Prod.fst h; simp at this;
  · intro a ha;
    have := List.mem_of_mem_dropLast ha;
    obtain ⟨ b, hb, rfl ⟩ := List.mem_map.mp this; simp +decide;
    cases k <;> cases b <;> simp +decide

/-- Every element of `chainEncode T w` is non-default. -/
theorem chainEncode_ne_default {T : Type} [Primcodable T] (w : List T) :
    ∀ γ ∈ chainEncode T w, γ ≠ (default : ChainΓ) :=
  trInit_ne_default _ _

/-- For non-default `γ`, `blankPreservingEmb γ = some (Sum.inr γ)`. -/
theorem blankPreservingEmb_ne_default {T Γ₀ : Type} [DecidableEq Γ₀] [Inhabited Γ₀]
    (γ : Γ₀) (hγ : γ ≠ default) :
    blankPreservingEmb (T := T) γ = some (Sum.inr γ) := by
  unfold blankPreservingEmb; simp [hγ]

/-- On chainEncode output, `blankPreservingEmb` agrees with `some ∘ Sum.inr`. -/
theorem chainEncode_map_blankPreservingEmb {T : Type} [DecidableEq T] [Primcodable T]
    (w : List T) :
    (chainEncode T w).map (blankPreservingEmb (T := T)) =
    (chainEncode T w).map (some ∘ Sum.inr) := by
  apply List.map_congr_left
  intro γ hγ
  exact blankPreservingEmb_ne_default γ (chainEncode_ne_default w γ hγ)

/-! ### Component realizability for chain_converter_fn -/

/-- The chain encoding equals formatting applied to the binary representation. -/
theorem chainEncode_eq_format (T : Type) [Primcodable T] (w : List T) :
    chainEncode T w =
      chainConsBottom :: (chainBinaryRepr (Encodable.encode w)).reverse :=
  trInit_trList_singleton_eq (Encodable.encode w)

theorem chainEncode_realizes
    {T : Type} [DecidableEq T] [Fintype T] [Primcodable T] :
    ∃ (Λ : Type) (_ : Inhabited Λ) (_ : Fintype Λ)
      (M : TM0.Machine (Option (T ⊕ ChainΓ)) Λ),
      ∀ w : List T,
        (TM0Seq.evalCfg M (w.map (some ∘ Sum.inl))).Dom ∧
        ∀ (h : (TM0Seq.evalCfg M (w.map (some ∘ Sum.inl))).Dom),
          ((TM0Seq.evalCfg M (w.map (some ∘ Sum.inl))).get h).Tape =
            Tape.mk₁ ((chainEncode T w).map (some ∘ Sum.inr)) := by
  obtain ⟨Λ₁, hΛ₁i, hΛ₁f, M₁, hM₁⟩ := chainEncode_fold T
  obtain ⟨Λ₂, hΛ₂i, hΛ₂f, M₂, hM₂⟩ := chainEncode_format T
  letI : Inhabited (Λ₁ ⊕ Λ₂) := ⟨Sum.inl default⟩
  refine ⟨Λ₁ ⊕ Λ₂, inferInstance, inferInstance, TM0Seq.compose M₁ M₂, fun w => ?_⟩
  -- Phase 1: M₁ halts on w.map(inl) producing the binary accumulator
  have h1_dom := (hM₁ w).1
  have h1_tape := (hM₁ w).2 h1_dom
  -- Phase 2: M₂ halts on the accumulator producing the formatted output
  set l' := (chainBinaryRepr (Encodable.encode w)).map (some ∘ @Sum.inr T ChainΓ) with hl'
  have h2_spec := hM₂ (chainBinaryRepr (Encodable.encode w)) (chainBinaryRepr_ne_default _)
  have h2_dom := h2_spec.1
  have h2_tape := h2_spec.2 h2_dom
  -- evalFromCfg M₂ ⟨default, M₁_output_tape⟩ halts (rewrite via h1_tape)
  have h_from : (TM0Seq.evalFromCfg M₂
      ⟨default, ((TM0Seq.evalCfg M₁ (w.map (some ∘ Sum.inl))).get h1_dom).Tape⟩).Dom := by
    rw [h1_tape]; exact h2_dom
  -- Composed machine halts (compose_dom_of_parts gives TM0.eval Dom)
  have h_eval_dom := TM0Seq.compose_dom_of_parts M₁ M₂ _ h1_dom h_from
  have h_comp_dom : (TM0Seq.evalCfg (TM0Seq.compose M₁ M₂)
      (w.map (some ∘ Sum.inl))).Dom :=
    (TM0Seq.evalCfg_dom_iff _ _).mpr h_eval_dom
  exact ⟨h_comp_dom, fun h => by
    -- Output tape tracking: composed tape = M₂'s tape on l'
    have h_tape := TM0Seq.compose_evalCfg_tape M₁ M₂ _ l' h1_dom h1_tape h2_dom h
    rw [h_tape, h2_tape]
    -- Remains: (chainConsBottom :: repr.reverse).map(inr) = (chainEncode T w).map(inr)
    congr 1; exact congr_arg _ (chainEncode_eq_format T w).symm⟩

/-- **The chain converter function is realizable on identity-encoded inputs.**

There exists a TM0 machine on `Option (T ⊕ ChainΓ)` that, given
identity-encoded input `w.map (some ∘ Sum.inl)`, always halts and
produces the chain tape format
`Tape.mk₁ ((chainEncode T w).map (blankPreservingEmb (T := T)))`.

The proof uses `chainEncode_realizes` (which gives a machine on
`Option (T ⊕ ChainΓ)`) and the fact that `blankPreservingEmb` agrees
with `some ∘ Sum.inr` on chain-encoded data (since chain-encoded
values are never default). -/
theorem chain_converter_fn_realizes
    {T : Type} [DecidableEq T] [Fintype T] [Primcodable T] :
    ∃ (Λ : Type) (_ : Inhabited Λ) (_ : Fintype Λ)
      (M : TM0.Machine (Option (T ⊕ ChainΓ)) Λ),
      ∀ w : List T,
        let input := w.map (fun x => some (Sum.inl x))
        (TM0Seq.evalCfg M input).Dom ∧
        ∀ (h : (TM0Seq.evalCfg M input).Dom),
          ((TM0Seq.evalCfg M input).get h).Tape =
            Tape.mk₁ ((chainEncode T w).map (blankPreservingEmb (T := T))) := by
  obtain ⟨Λ, hΛi, hΛf, M, hM⟩ := chainEncode_realizes (T := T)
  refine ⟨Λ, hΛi, hΛf, M, fun w => ?_⟩
  have ⟨hdom, htape⟩ := hM w
  refine ⟨hdom, fun h => ?_⟩
  have h1 := htape h
  convert h1 using 2
  exact chainEncode_map_blankPreservingEmb w
