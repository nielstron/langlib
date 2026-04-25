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

We also define `TM0RealizesFn Γ T f` for heterogeneous functions
`f : List Γ → List T`, using `Option (Γ ⊕ T)` as the tape alphabet
with `none` as blank. This enables composing functions between different
types (e.g., `f : T → S` and `g : S → U`).

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

/-! ### TM0 Realizability (Heterogeneous) -/

/-- A total function `f : List Γ → List T` is **heterogeneously TM0-realizable**
if there exists a finite-state TM0 machine over the tape alphabet
`Option (Γ ⊕ T)` (where `none` serves as the blank symbol) that always halts
on any input `l` (encoded as `l.map (some ∘ Sum.inl)`) and produces
`Tape.mk₁ ((f l).map (some ∘ Sum.inr))` as the output tape.

The tape type `Option (Γ ⊕ T)` separates input symbols (via `Sum.inl`)
from output symbols (via `Sum.inr`), with `none` as the universal blank.
This enables composing functions between different types. -/
def TM0RealizesFn (Γ T : Type) (f : List Γ → List T) : Prop :=
  ∃ (Λ : Type) (_ : Inhabited Λ) (_ : Fintype Λ)
    (M : TM0.Machine (Option (Γ ⊕ T)) Λ),
    ∀ l : List Γ,
      (TM0Seq.evalCfg M (l.map (some ∘ Sum.inl))).Dom ∧
      ∀ (h : (TM0Seq.evalCfg M (l.map (some ∘ Sum.inl))).Dom),
        ((TM0Seq.evalCfg M (l.map (some ∘ Sum.inl))).get h).Tape =
          Tape.mk₁ ((f l).map (some ∘ Sum.inr))

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

/-! ### Alphabet lifting: tape tracking -/

/-
When a TM0 machine halts producing `Tape.mk₁ l'`, the lifted machine
halts producing `Tape.mk₁ (l'.map emb)`. This extends `lift_eval_dom`
with output tape tracking.
-/
theorem TM0AlphabetSim.lift_evalCfg_tape {Γ₁ Γ₂ : Type} [Inhabited Γ₁] [Inhabited Γ₂]
    {Λ : Type} [Inhabited Λ]
    (M : TM0.Machine Γ₁ Λ) (emb : Γ₁ → Γ₂) (inv : Γ₂ → Γ₁)
    (hemb : ∀ a, inv (emb a) = a) (hemb_default : emb default = default)
    (l l' : List Γ₁)
    (h : (TM0Seq.evalCfg M l).Dom)
    (htape : ((TM0Seq.evalCfg M l).get h).Tape = Tape.mk₁ l') :
    ∃ h' : (TM0Seq.evalCfg (TM0AlphabetSim.liftMachine M emb inv) (l.map emb)).Dom,
      ((TM0Seq.evalCfg (TM0AlphabetSim.liftMachine M emb inv) (l.map emb)).get h').Tape =
        Tape.mk₁ (l'.map emb) := by
  obtain ⟨c₁, hc₁⟩ : ∃ c₁, c₁ ∈ Turing.eval (TM0.step M) (TM0.init l) ∧ c₁.Tape = Tape.mk₁ l' := by
    exact ⟨ _, Part.get_mem _, htape ⟩;
  have := Turing.tr_eval ( TM0AlphabetSim.lift_respects M emb inv hemb hemb_default ) ( TM0AlphabetSim.lift_init_rel emb inv hemb hemb_default l ) hc₁.1;
  obtain ⟨ c₂, hc₂₁, hc₂₂ ⟩ := this;
  obtain ⟨h', hc'⟩ : ∃ h' : (TM0Seq.evalCfg (liftMachine M emb inv) (l.map emb)).Dom, ((TM0Seq.evalCfg (liftMachine M emb inv) (l.map emb)).get h') = c₂ := by
    exact Set.mem_range.mp hc₂₂
  generalize_proofs at *; (
  use h';
  rw [ hc', hc₂₁.2, hc₁.2, Tape.map_mk₁ ];
  unfold embPM; aesop;)

/-! ### Heterogeneous composition -/

/-- Embedding from `Option (Γ₁ ⊕ Γ₂)` into `Option (Γ₁ ⊕ (Γ₂ ⊕ Γ₃))`,
preserving the blank (none → none). Used to lift the first machine in
a heterogeneous composition. -/
noncomputable def sumEmbLeft {Γ₁ Γ₂ Γ₃ : Type}
    (x : Option (Γ₁ ⊕ Γ₂)) : Option (Γ₁ ⊕ (Γ₂ ⊕ Γ₃)) :=
  match x with
  | none => none
  | some (Sum.inl a) => some (Sum.inl a)
  | some (Sum.inr b) => some (Sum.inr (Sum.inl b))

/-- Inverse of `sumEmbLeft`. -/
noncomputable def sumEmbLeftInv {Γ₁ Γ₂ Γ₃ : Type}
    (x : Option (Γ₁ ⊕ (Γ₂ ⊕ Γ₃))) : Option (Γ₁ ⊕ Γ₂) :=
  match x with
  | none => none
  | some (Sum.inl a) => some (Sum.inl a)
  | some (Sum.inr (Sum.inl b)) => some (Sum.inr b)
  | some (Sum.inr (Sum.inr _)) => none

/-- Embedding from `Option (Γ₂ ⊕ Γ₃)` into `Option (Γ₁ ⊕ (Γ₂ ⊕ Γ₃))`,
preserving the blank (none → none). Used to lift the second machine in
a heterogeneous composition. -/
noncomputable def sumEmbRight {Γ₁ Γ₂ Γ₃ : Type}
    (x : Option (Γ₂ ⊕ Γ₃)) : Option (Γ₁ ⊕ (Γ₂ ⊕ Γ₃)) :=
  match x with
  | none => none
  | some (Sum.inl b) => some (Sum.inr (Sum.inl b))
  | some (Sum.inr c) => some (Sum.inr (Sum.inr c))

/-- Inverse of `sumEmbRight`. -/
noncomputable def sumEmbRightInv {Γ₁ Γ₂ Γ₃ : Type}
    (x : Option (Γ₁ ⊕ (Γ₂ ⊕ Γ₃))) : Option (Γ₂ ⊕ Γ₃) :=
  match x with
  | none => none
  | some (Sum.inl _) => none
  | some (Sum.inr (Sum.inl b)) => some (Sum.inl b)
  | some (Sum.inr (Sum.inr c)) => some (Sum.inr c)

theorem sumEmbLeft_default {Γ₁ Γ₂ Γ₃ : Type} :
    sumEmbLeft (Γ₃ := Γ₃) (default : Option (Γ₁ ⊕ Γ₂)) =
      (default : Option (Γ₁ ⊕ (Γ₂ ⊕ Γ₃))) := by
  rfl

theorem sumEmbRight_default {Γ₁ Γ₂ Γ₃ : Type} :
    sumEmbRight (Γ₁ := Γ₁) (default : Option (Γ₂ ⊕ Γ₃)) =
      (default : Option (Γ₁ ⊕ (Γ₂ ⊕ Γ₃))) := by
  rfl

theorem sumEmbLeftInv_emb {Γ₁ Γ₂ Γ₃ : Type} (x : Option (Γ₁ ⊕ Γ₂)) :
    sumEmbLeftInv (Γ₃ := Γ₃) (sumEmbLeft x) = x := by
  cases x with
  | none => simp [sumEmbLeft, sumEmbLeftInv]
  | some v => cases v <;> simp [sumEmbLeft, sumEmbLeftInv]

theorem sumEmbRightInv_emb {Γ₁ Γ₂ Γ₃ : Type} (x : Option (Γ₂ ⊕ Γ₃)) :
    sumEmbRightInv (Γ₁ := Γ₁) (sumEmbRight x) = x := by
  cases x with
  | none => simp [sumEmbRight, sumEmbRightInv]
  | some v => cases v <;> simp [sumEmbRight, sumEmbRightInv]

/-- After M_f produces output `(f l).map (some ∘ Sum.inr)` on `Option (T ⊕ S)`,
the lifted version on `Option (T ⊕ (S ⊕ U))` produces
`(f l).map (some ∘ Sum.inr ∘ Sum.inl)`, which matches M_g's expected input
`(f l).map (some ∘ Sum.inl)` after lifting via `sumEmbRight`. -/
theorem sumEmbLeft_output_eq_sumEmbRight_input {T S U : Type}
    (l : List S) :
    (l.map (sumEmbLeft (Γ₃ := U) ∘ some ∘ @Sum.inr T S)) =
    (l.map (sumEmbRight (Γ₁ := T) ∘ some ∘ @Sum.inl S U)) := by
  simp [sumEmbLeft, sumEmbRight, Function.comp]

/-
**Heterogeneous composition**: If `f : List T → List S` and `g : List S → List U`
are both TM0-realizable (heterogeneously), then `g ∘ f` can be computed by a TM0
machine on the enlarged tape alphabet `Option (T ⊕ (S ⊕ U))`.

Both M_f and M_g are lifted to this common alphabet using blank-preserving embeddings.
The key insight is that M_f's output format (`Sum.inr (Sum.inl s)` for S-values)
matches M_g's input format after lifting.

The result is stated as a raw existential rather than `TM0RealizesFn T U` because
the composed machine operates on `Option (T ⊕ (S ⊕ U))` (which contains the
intermediate type S), not `Option (T ⊕ U)`.
-/
theorem tm0RealizesFn_comp {T S U : Type}
    {f : List T → List S} {g : List S → List U}
    (hf : TM0RealizesFn T S f) (hg : TM0RealizesFn S U g) :
    ∃ (Λ : Type) (_ : Inhabited Λ) (_ : Fintype Λ)
      (M : TM0.Machine (Option (T ⊕ (S ⊕ U))) Λ),
      ∀ l : List T,
        (TM0Seq.evalCfg M (l.map (some ∘ Sum.inl))).Dom ∧
        ∀ (h : (TM0Seq.evalCfg M (l.map (some ∘ Sum.inl))).Dom),
          ((TM0Seq.evalCfg M (l.map (some ∘ Sum.inl))).get h).Tape =
            Tape.mk₁ ((g (f l)).map (some ∘ Sum.inr ∘ Sum.inr)) := by
  obtain ⟨Λ_f, _, _, M_f, hf⟩ := hf
  obtain ⟨Λ_g, _, _, M_g, hg⟩ := hg
  -- Lift both machines to the common alphabet Option (T ⊕ (S ⊕ U))
  let M_f' := TM0AlphabetSim.liftMachine M_f
    (sumEmbLeft (Γ₃ := U)) (sumEmbLeftInv (Γ₃ := U))
  let M_g' := TM0AlphabetSim.liftMachine M_g
    (sumEmbRight (Γ₁ := T)) (sumEmbRightInv (Γ₁ := T))
  letI : Inhabited (Λ_f ⊕ Λ_g) := ⟨Sum.inl default⟩
  refine ⟨Λ_f ⊕ Λ_g, inferInstance, inferInstance,
    TM0Seq.compose M_f' M_g', fun l => ?_⟩
  have h_lift_f : ∃ h_f : (TM0Seq.evalCfg M_f' (l.map (some ∘ Sum.inl))).Dom,
    ((TM0Seq.evalCfg M_f' (l.map (some ∘ Sum.inl))).get h_f).Tape = Tape.mk₁ ((f l).map (fun s => some (Sum.inr (Sum.inl s)))) := by
      convert TM0AlphabetSim.lift_evalCfg_tape M_f sumEmbLeft sumEmbLeftInv _ _ _ _ _ _ using 1;
      any_goals exact hf l |>.1;
      any_goals exact hf l |>.2 _;
      all_goals norm_num [ Function.comp ];
      any_goals tauto;
      · congr! 3;
        exact List.ext_get ( by simp +decide ) ( by simp +decide [ sumEmbLeft ] );
      · exact fun a => sumEmbLeftInv_emb a;
  have h_lift_g : ∃ h_g : (TM0Seq.evalCfg M_g' ((f l).map (fun s => some (Sum.inr (Sum.inl s))))).Dom,
    ((TM0Seq.evalCfg M_g' ((f l).map (fun s => some (Sum.inr (Sum.inl s))))).get h_g).Tape = Tape.mk₁ ((g (f l)).map (some ∘ Sum.inr ∘ Sum.inr)) := by
      convert TM0AlphabetSim.lift_evalCfg_tape M_g sumEmbRight sumEmbRightInv _ _ _ _ _ _ using 1;
      any_goals exact hg ( f l ) |>.1;
      any_goals exact hg ( f l ) |>.2 _;
      congr! 1;
      · congr! 1;
        exact List.ext_get ( by aesop ) ( by aesop );
      · congr! 2;
        · congr! 1;
          exact List.ext_get ( by simp +decide ) ( by simp +decide [ sumEmbRight ] );
        · congr! 2;
          exact congr_arg _ ( by ext; simp +decide [ sumEmbRight ] );
        · congr! 1;
          exact List.ext_get ( by aesop ) ( by aesop );
      · exact fun a => sumEmbRightInv_emb a;
      · exact sumEmbRight_default;
  obtain ⟨h_f, h_f_tape⟩ := h_lift_f
  obtain ⟨h_g, h_g_tape⟩ := h_lift_g
  have h_comp_dom : (TM0Seq.evalCfg (TM0Seq.compose M_f' M_g') (l.map (some ∘ Sum.inl))).Dom := by
    apply TM0Seq.compose_dom_of_parts;
    convert h_g using 1;
    rw [ h_f_tape ];
    exact Part.eq_of_get_eq_get h_g h_g rfl
  have h_comp_tape : ((TM0Seq.evalCfg (TM0Seq.compose M_f' M_g') (l.map (some ∘ Sum.inl))).get h_comp_dom).Tape = Tape.mk₁ ((g (f l)).map (some ∘ Sum.inr ∘ Sum.inr)) := by
    convert TM0Seq.compose_evalCfg_tape M_f' M_g' ( List.map ( some ∘ Sum.inl ) l ) ( List.map ( fun s => some ( Sum.inr ( Sum.inl s ) ) ) ( f l ) ) h_f h_f_tape h_g h_comp_dom using 1
    (generalize_proofs at *; aesop;)
  exact ⟨h_comp_dom, fun h => h_comp_tape⟩

/-! ### Bridging heterogeneous to homogeneous -/

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

/-! ### Pointwise heterogeneous maps are TM0-realizable -/

/-
Pointwise heterogeneous maps are TM0-realizable.

Given a function `φ : T → S` between Fintypes, the pointwise map
`fun l => l.map φ` is `TM0RealizesFn T S`. The proof lifts
`tm0_map_blankfree` to the heterogeneous setting by defining a
homogeneous map `ψ : Option (T ⊕ S) → Option (T ⊕ S)` that sends
`Sum.inl t ↦ Sum.inr (φ t)` and is the identity elsewhere.
-/
theorem tm0RealizesFn_pointwise {T S : Type}
    [DecidableEq T] [DecidableEq S] [Fintype T] [Fintype S]
    (φ : T → S) :
    TM0RealizesFn T S (fun l => l.map φ) := by
  convert TM0BB.tm0_map_blankfree _ _ _;
  rotate_left;
  exact Option ( T ⊕ S );
  all_goals try infer_instance;
  exact fun x => x.map ( fun y => y.elim ( fun t => Sum.inr ( φ t ) ) fun s => Sum.inr s );
  · rfl;
  · grind +extAll;
  · constructor;
    · intro h;
      convert TM0BB.tm0_map_blankfree _ _ _;
      · infer_instance;
      · infer_instance;
      · rfl;
      · rintro ( _ | _ | a ) <;> simp +decide;
    · rintro ⟨ Λ, x, x_1, M, hM ⟩;
      use Λ, x, x_1, M;
      intro l; specialize hM ( List.map ( some ∘ Sum.inl ) l ) ; aesop;

/-! ### Component realizability for chain_converter_fn -/

/-- Chain encoding is TM0-realizable: given a list of T values encoded
as `Sum.inl` on the tape, compute `chainEncode T` and write the result
as `Sum.inr` values.

Since T is Fintype, each `Encodable.encode t` is a fixed constant.
The encoding `Encodable.encode (w : List T)` uses iterated `Nat.pair`,
which can be computed by binary arithmetic on the tape.

## Proof strategy (not yet formalized)

The TM0 machine on `Option (T ⊕ ChainΓ)` would process the input list
right-to-left, maintaining an accumulator in binary using `Sum.inr`
(ChainΓ) symbols on the tape. For each input element `t`, it computes
`Nat.pair(Encodable.encode t, acc) + 1` and updates the accumulator.

Since `Encodable.encode t < |T|` for all `t : T`, the `Nat.pair(a, acc)`
computation has fixed first argument `a`. For `a ≤ acc` (the common case),
this reduces to `acc² + a`, requiring binary squaring (via shift-and-add
multiplication), binary addition of small constant (via carry propagation),
and binary increment (for the `+1`).

After processing all elements, the binary accumulator is formatted as
`trInit K'.main (trList [result])` and written as `Sum.inr` symbols.

An alternative approach uses `ToPartrec.Code.fix` to build a Code for
the list-pairing fold, compiled via the chain to a TM0 on ChainΓ,
composed with a flat-map converter for identity → multi-element chain
format. This avoids explicit binary arithmetic in the TM0 construction
but requires chain output tracking (showing the chain TM0 produces
specific tape contents when the Code halts with a specific value).

**Chain encoding is TM0-realizable (heterogeneous).**

The proof uses the decomposition from `ChainEncodeDecomp`:
1. The list encoding is a right fold: `encodable_encode_list_fold`
2. Each fold step (Nat.pair + succ) is block-realizable: `tm0_binPairConstSucc_block`
3. Block operations compose serially: `tm0RealizesBlock_iterate`
4. The final formatting is `trInit_trList_singleton_eq`
5. Binary succ is the "singleton function" from which all operations derive

The TM0 on `Option (T ⊕ ChainΓ)` works as follows:
- Read input elements `Sum.inl t₁, ..., Sum.inl tₙ` right-to-left
- For each element t, compute `Nat.pair(encode t, acc) + 1` on the
  binary accumulator stored as `Sum.inr` ChainΓ cells
- Each step uses `binPairConstSucc (Encodable.encode t)` which is
  block-realizable (preserving unprocessed Sum.inl elements)
- After processing all elements, format the accumulator as
  `trInit K'.main (trList [result])` -/
theorem chainEncode_realizes {T : Type} [DecidableEq T] [Fintype T] [Primcodable T] :
    TM0RealizesFn T ChainΓ (chainEncode T) := by
  sorry

/-- **The chain converter function is realizable on identity-encoded inputs.**

There exists a TM0 machine on `Option (T ⊕ ChainΓ)` that, given
identity-encoded input `w.map (some ∘ Sum.inl)`, always halts and
produces the chain tape format
`Tape.mk₁ ((chainEncode T w).map (blankPreservingEmb (T := T)))`.

The proof uses `chainEncode_realizes` (which gives a machine on
`Option (T ⊕ ChainΓ)`) and the fact that `blankPreservingEmb` agrees
with `some ∘ Sum.inr` on chain-encoded data (since chain-encoded
values are never default). -/
theorem chain_converter_fn_realizes {T : Type} [DecidableEq T] [Fintype T] [Primcodable T] :
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