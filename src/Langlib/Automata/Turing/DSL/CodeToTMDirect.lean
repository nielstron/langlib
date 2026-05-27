import Mathlib
import Langlib.Automata.Turing.Definition
import Langlib.Automata.Turing.DSL.TM0AlphabetSimulation
import Langlib.Automata.Turing.DSL.InnerBlockRealizability
import Langlib.Automata.Turing.DSL.PartrecChainAlphabet
import Langlib.Automata.Turing.DSL.ListEncodeCode
import Langlib.Automata.Turing.DSL.HetFoldBlockRealizability
import Langlib.Automata.Turing.DSL.PartrecCodeToTM0
import Langlib.Automata.Turing.DSL.TM0Composition

/-! # Direct `ToPartrec.Code` → TM Recognition

This file factors the encoding bridge through `ListEncodeCode.lean`.

The old bridge asks a preprocessing TM to compute `Encodable.encode w` on the
tape.  The direct route composes the user `ToPartrec.Code` with a Code-level
list encoder, then uses the generalized Partrec chain on a variable-length
`List ℕ` input.  The remaining machine obligation is therefore only a finite
per-symbol conversion from identity input to `shiftedEncoding`.

## Key results

- `shifted_converter_exists`: realizes the finite per-symbol conversion.
- `directEmbedTM0_eval_dom`: alphabet lifting preserves the embedded TM0's
  halting domain.
- `code_implies_isTM_direct`: a `ToPartrec.Code` recognizing a language gives
  `is_TM` for that language.
-/

open Turing PartrecToTM2 TM2to1
open Langlib.TMCodeListEncode

/-! ### Blank-preserving embedding -/

noncomputable def directBlankEmb {T Γ₀ : Type} [DecidableEq Γ₀] [Inhabited Γ₀]
    (γ : Γ₀) : Option (T ⊕ Γ₀) :=
  if γ = default then none else some (Sum.inr γ)

noncomputable def directBlankInv {T Γ₀ : Type} [Inhabited Γ₀]
    (a : Option (T ⊕ Γ₀)) : Γ₀ :=
  match a with
  | some (Sum.inr γ) => γ
  | _ => default

theorem directBlankEmb_default {T Γ₀ : Type} [DecidableEq Γ₀] [Inhabited Γ₀] :
    directBlankEmb (T := T) (default : Γ₀) =
      (default : Option (T ⊕ Γ₀)) := by
  unfold directBlankEmb
  simp [show (default : Option (T ⊕ Γ₀)) = none from rfl]

theorem directBlankInv_emb {T Γ₀ : Type} [DecidableEq Γ₀] [Inhabited Γ₀]
    (γ : Γ₀) : directBlankInv (T := T) (directBlankEmb γ) = γ := by
  unfold directBlankEmb directBlankInv
  split <;> simp_all

theorem directBlankEmb_ne_default {T Γ₀ : Type} [DecidableEq Γ₀] [Inhabited Γ₀]
    (γ : Γ₀) (hγ : γ ≠ default) :
    directBlankEmb (T := T) γ = some (Sum.inr γ) := by
  unfold directBlankEmb
  simp [hγ]

/-! ### Direct shifted tape construction -/

noncomputable def directChainCons : ChainΓ :=
  γ'ToChainΓ Γ'.cons

noncomputable def shiftedNatBlock (n : ℕ) : List ChainΓ :=
  directChainCons :: (chainBinaryRepr n).reverse

noncomputable def shiftedSymbolBlock {T : Type} [Primcodable T] (t : T) :
    List ChainΓ :=
  shiftedNatBlock (Encodable.encode t + 1)

noncomputable def shiftedPayload {T : Type} [Primcodable T] : List T → List ChainΓ :=
  List.foldr (fun t acc => shiftedSymbolBlock t ++ acc) []

noncomputable def shiftedChainTape {T : Type} [Primcodable T] (w : List T) :
    List ChainΓ :=
  chainConsBottom :: shiftedPayload w ++ [directChainCons]

theorem directChainCons_ne_default :
    directChainCons ≠ (default : ChainΓ) := by
  unfold directChainCons γ'ToChainΓ
  intro h
  have hmain := congrArg (fun x : ChainΓ => x.2 K'.main) h
  simp at hmain

theorem shiftedNatBlock_ne_default (n : ℕ) :
    ∀ g ∈ shiftedNatBlock n, g ≠ (default : ChainΓ) := by
  intro g hg
  simp [shiftedNatBlock] at hg
  rcases hg with rfl | hg
  · exact directChainCons_ne_default
  · exact chainBinaryRepr_ne_default n g (by simpa using hg)

theorem shiftedSymbolBlock_ne_default {T : Type} [Primcodable T] (t : T) :
    ∀ g ∈ shiftedSymbolBlock t, g ≠ (default : ChainΓ) :=
  shiftedNatBlock_ne_default _

theorem shiftedPayload_ne_default {T : Type} [Primcodable T] (w : List T) :
    ∀ g ∈ shiftedPayload w, g ≠ (default : ChainΓ) := by
  induction w with
  | nil => simp [shiftedPayload]
  | cons t ts ih =>
      intro g hg
      simp only [shiftedPayload, List.foldr_cons, List.mem_append] at hg
      rcases hg with hg | hg
      · exact shiftedSymbolBlock_ne_default t g hg
      · exact ih g hg

theorem shiftedChainTape_ne_default {T : Type} [Primcodable T] (w : List T) :
    ∀ g ∈ shiftedChainTape w, g ≠ (default : ChainΓ) := by
  intro g hg
  simp [shiftedChainTape, List.mem_append] at hg
  rcases hg with rfl | hg | rfl
  · exact chainConsBottom_ne_default
  · exact shiftedPayload_ne_default w g hg
  · exact directChainCons_ne_default

theorem trList_eq_flatMap (ns : List ℕ) :
    PartrecToTM2.trList ns =
      ns.flatMap (fun n => PartrecToTM2.trNat n ++ [Γ'.cons]) := by
  induction ns with
  | nil => simp [PartrecToTM2.trList]
  | cons n ns ih => simp [PartrecToTM2.trList, ih]

theorem trInit_trList_append_zero (ns : List ℕ) :
    TM2to1.trInit PartrecToTM2.K'.main
        (PartrecToTM2.trList (ns ++ [0])) =
      chainConsBottom :: List.flatMap shiftedNatBlock ns.reverse := by
  rw [trList_eq_flatMap]
  simp [List.flatMap_append, PartrecToTM2.trNat, PartrecToTM2.trNum]
  rw [TM2to1.trInit]
  simp [List.reverse_append, List.reverse_flatMap, Function.comp_def,
    List.map_flatMap]
  constructor
  · simp [chainConsBottom]
  · apply List.flatMap_congr
    intro n _hn
    simp [shiftedNatBlock, directChainCons, chainBinaryRepr, γ'ToChainΓ,
      PartrecToTM2.trNat, PartrecToTM2.trNum]

theorem flatMap_shiftedNatBlock_map_encode
    {T : Type} [Primcodable T] (w : List T) :
    List.flatMap shiftedNatBlock
        (List.map ((fun x => x + 1) ∘ Encodable.encode) w) =
      shiftedPayload w := by
  induction w with
  | nil => simp [shiftedPayload]
  | cons t ts ih =>
      simp [shiftedPayload, shiftedSymbolBlock, shiftedNatBlock, ih]

theorem trInit_trList_shiftedEncoding_eq
    {T : Type} [Primcodable T] (w : List T) :
    TM2to1.trInit PartrecToTM2.K'.main
        (PartrecToTM2.trList (shiftedEncoding w)) =
      shiftedChainTape w := by
  unfold shiftedEncoding
  rw [show 0 :: (List.map Encodable.encode w).reverse.map (· + 1) ++ [0] =
      (0 :: (List.map Encodable.encode w).reverse.map (· + 1)) ++ [0] by simp]
  rw [trInit_trList_append_zero]
  simp only [List.reverse_cons, List.flatMap_append, List.flatMap_singleton]
  rw [List.map_reverse]
  simp [flatMap_shiftedNatBlock_map_encode, shiftedChainTape,
    shiftedNatBlock, directChainCons, chainBinaryRepr_zero]

noncomputable def shiftedFoldAccStep {T : Type} [Primcodable T]
    (t : T) (acc : List ChainΓ) : List ChainΓ :=
  shiftedSymbolBlock t ++ acc

noncomputable def shiftedFoldTapeStep
    (T : Type) [DecidableEq T] [Fintype T] [Primcodable T] (t : T) :
    List (Option (T ⊕ ChainΓ)) → List (Option (T ⊕ ChainΓ)) :=
  hetFoldAdapt (T := T) (Γ₀ := ChainΓ) shiftedFoldAccStep t

theorem shiftedFoldTapeStep_hetMix
    (T : Type) [DecidableEq T] [Fintype T] [Primcodable T]
    (t : T) (ts : List T) (acc : List ChainΓ) :
    shiftedFoldTapeStep T t (hetMix (T := T) (Γ₀ := ChainΓ) ts acc) =
      hetMix ts (shiftedFoldAccStep t acc) := by
  exact hetFoldAdapt_hetMix (T := T) (Γ₀ := ChainΓ) shiftedFoldAccStep t ts acc

theorem shiftedFoldAccStep_ne_default
    {T : Type} [Primcodable T] (t : T) (acc : List ChainΓ)
    (hacc : ∀ g ∈ acc, g ≠ (default : ChainΓ)) :
    ∀ g ∈ shiftedFoldAccStep t acc, g ≠ (default : ChainΓ) := by
  intro g hg
  simp [shiftedFoldAccStep, List.mem_append] at hg
  rcases hg with hg | hg
  · exact shiftedSymbolBlock_ne_default t g hg
  · exact hacc g hg

theorem shiftedFoldTapeStep_ne_default
    (T : Type) [DecidableEq T] [Fintype T] [Primcodable T] (t : T)
    (block : List (Option (T ⊕ ChainΓ)))
    (hblock : ∀ g ∈ block, g ≠ default) :
    ∀ g ∈ shiftedFoldTapeStep T t block, g ≠ default := by
  intro g hg
  unfold shiftedFoldTapeStep hetFoldAdapt hetFoldAdaptSep separatedAccLift at hg
  exact (List.mem_append.mp hg).elim
    (fun hleft => (List.mem_append.mp hleft).elim
      (fun htag => hblock g ((List.takeWhile_sublist _).subset htag))
      (fun hsep => by
        simp at hsep
        subst g
        simp [hetSep]))
    (fun hmap => by
      obtain ⟨a, _ha, haeq⟩ := List.mem_map.mp hmap
      rw [← haeq]
      simp [hetAccEmb])

theorem shiftedFoldBody
    (T : Type) [DecidableEq T] [Fintype T] [Primcodable T] :
    TM0RealizesHetFoldBody (T := T) (Γ₀ := ChainΓ)
      (shiftedFoldTapeStep T) := by
  classical
  let Γ := Option (T ⊕ ChainΓ)
  let sep : Γ := hetSep (T := T) (Γ₀ := ChainΓ)
  let pref (t : T) : List Γ :=
    (shiftedSymbolBlock t).map (hetAccEmb (T := T))
  have hsep_nd : sep ≠ (default : Γ) := by
    simp [sep, hetSep]
  have hinner : ∀ t : T,
      TM0RealizesInnerBlockDefaultSep Γ sep
        (fun inner => pref t ++ inner) := by
    intro t
    have hpref_nd : ∀ g ∈ pref t, g ≠ (default : Γ) := by
      intro g hg
      rcases List.mem_map.mp hg with ⟨a, _ha, rfl⟩
      simp [pref, hetAccEmb]
    have hpref_nsep : ∀ g ∈ pref t, g ≠ sep := by
      intro g hg
      rcases List.mem_map.mp hg with ⟨a, ha, rfl⟩
      have ha_nd := shiftedSymbolBlock_ne_default t a ha
      intro h
      injection h with hsum
      injection hsum with ha
      exact ha_nd ha
    have hfsep : TM0RealizesBlockSep Γ sep (fun inner => pref t ++ inner) :=
      tm0_prependList_blockSep (pref t) hpref_nd hpref_nsep
    refine tm0RealizesBlockSep_toInnerDefault hsep_nd hfsep ?_ ?_
    · intro block hblock
      exact prependList_ne_default' (pref t) block hpref_nd hblock
    · intro block hblock g hg
      simp [List.mem_append] at hg
      rcases hg with hg | hg
      · exact hpref_nsep g hg
      · exact hblock g hg
  choose Λ hΛi hΛf M hM using hinner
  refine ⟨Λ, hΛi, hΛf, M, ?_⟩
  intro t ts acc hacc_nd
  let pfx : List Γ := ts.map (hetTagEmb (Γ₀ := ChainΓ))
  let inner : List Γ := acc.map (hetAccEmb (T := T))
  have hpfx_nd : ∀ g ∈ pfx, g ≠ (default : Γ) := by
    intro g hg
    rcases List.mem_map.mp hg with ⟨a, _ha, rfl⟩
    simp [pfx, hetTagEmb]
  have hpfx_nsep : ∀ g ∈ pfx, g ≠ sep := by
    intro g hg
    rcases List.mem_map.mp hg with ⟨a, _ha, rfl⟩
    intro h
    injection h with hsum
    cases hsum
  have hinner_nd : ∀ g ∈ inner, g ≠ (default : Γ) := by
    intro g hg
    rcases List.mem_map.mp hg with ⟨a, _ha, rfl⟩
    simp [inner, hetAccEmb]
  have hinner_nsep : ∀ g ∈ inner, g ≠ sep := by
    intro g hg
    rcases List.mem_map.mp hg with ⟨a, ha, rfl⟩
    have ha_nd := hacc_nd a ha
    intro h
    injection h with hsum
    injection hsum with ha
    exact ha_nd ha
  have hout_nd : ∀ g ∈ pref t ++ inner, g ≠ (default : Γ) := by
    intro g hg
    simp [List.mem_append] at hg
    rcases hg with hg | hg
    · rcases List.mem_map.mp hg with ⟨a, _ha, rfl⟩
      simp [pref, hetAccEmb]
    · exact hinner_nd g hg
  have hout_nsep : ∀ g ∈ pref t ++ inner, g ≠ sep := by
    intro g hg
    simp [List.mem_append] at hg
    rcases hg with hg | hg
    · rcases List.mem_map.mp hg with ⟨a, ha, rfl⟩
      have ha_nd := shiftedSymbolBlock_ne_default t a ha
      intro h
      injection h with hsum
      injection hsum with ha
      exact ha_nd ha
    · exact hinner_nsep g hg
  obtain ⟨hdom, htape⟩ :=
    hM t pfx inner hpfx_nd hpfx_nsep hinner_nd hinner_nsep
      hout_nd hout_nsep
  have hinput :
      hetMix (T := T) (Γ₀ := ChainΓ) ts acc ++ [default] =
        pfx ++ sep :: inner ++ [default] := by
    simp [pfx, inner, sep, hetMix, hetMixSep, separatedMix]
  refine ⟨?_, ?_⟩
  · simpa [hinput] using hdom
  · intro h
    have h' :
        (TM0Seq.evalCfg (M t) (pfx ++ sep :: inner ++ [default])).Dom := by
      simpa [hinput] using h
    have hget :
        (TM0Seq.evalCfg (M t)
          (hetMix (T := T) (Γ₀ := ChainΓ) ts acc ++ [default])).get h =
        (TM0Seq.evalCfg (M t) (pfx ++ sep :: inner ++ [default])).get h' := by
      apply Part.get_eq_get_of_eq
      simp [hinput]
    rw [hget, htape h']
    congr 1
    rw [shiftedFoldTapeStep_hetMix]
    simp [shiftedFoldAccStep, pfx, inner, pref, sep, hetMix, hetMixSep,
      separatedMix]

theorem shiftedFoldRealizes
    {T : Type} [DecidableEq T] [Fintype T] [Primcodable T] :
    ∃ (Λ : Type) (_ : Inhabited Λ) (_ : Fintype Λ)
      (M : TM0.Machine (Option (T ⊕ ChainΓ)) Λ),
      ∀ w : List T,
        (TM0Seq.evalCfg M (w.map (some ∘ Sum.inl))).Dom ∧
        ∀ (h : (TM0Seq.evalCfg M (w.map (some ∘ Sum.inl))).Dom),
          ((TM0Seq.evalCfg M (w.map (some ∘ Sum.inl))).get h).Tape =
            Tape.mk₁ ((shiftedPayload w).map (some ∘ @Sum.inr T ChainΓ)) := by
  obtain ⟨Λ, hΛi, hΛf, M, hM⟩ :=
    tm0Het_fold_blockRealizable' T
      (shiftedFoldTapeStep T)
      shiftedFoldAccStep
      (shiftedFoldTapeStep_hetMix T)
      (shiftedFoldBody T)
      (shiftedFoldTapeStep_ne_default T)
      (fun t block hblock => shiftedFoldAccStep_ne_default t block hblock)
  exact ⟨Λ, hΛi, hΛf, M, fun w => by
    obtain ⟨hdom, htape⟩ := hM w
    exact ⟨hdom, fun h => by
      rw [htape h]
      rfl⟩⟩

noncomputable def shiftedFinishBlock {T : Type}
    (block : List (Option (T ⊕ ChainΓ))) : List (Option (T ⊕ ChainΓ)) :=
  some (Sum.inr chainConsBottom) :: block ++ [some (Sum.inr directChainCons)]

theorem shiftedFinishBlock_realizes
    (T : Type) [DecidableEq T] [Fintype T] :
    TM0RealizesBlock (Option (T ⊕ ChainΓ)) (shiftedFinishBlock (T := T)) := by
  let Γ := Option (T ⊕ ChainΓ)
  have hlast_nd :
      ∀ g ∈ ([some (Sum.inr directChainCons)] : List Γ), g ≠ default := by
    intro g hg
    rw [List.mem_singleton] at hg
    subst g
    simp [Γ]
  have hlast_nsep :
      ∀ g ∈ ([some (Sum.inr directChainCons)] : List Γ), g ≠ (default : Γ) := hlast_nd
  have happ_sep : TM0RealizesBlockSepAnySuffix Γ (default : Γ)
      (fun block => block ++ [some (Sum.inr directChainCons)]) :=
    tm0_appendList_blockSep_anySuffix [some (Sum.inr directChainCons)]
      hlast_nd hlast_nsep
  have happ : TM0RealizesBlock Γ
      (fun block : List Γ => block ++ [some (Sum.inr directChainCons)]) :=
    tm0RealizesBlock_of_anySuffix
      (tm0RealizesBlockAnySuffix_of_sep_default happ_sep)
  have hcons : TM0RealizesBlock Γ
      (fun block : List Γ => some (Sum.inr chainConsBottom) :: block) :=
    tm0_cons_block (some (Sum.inr chainConsBottom)) (by simp [Γ])
  have happ_nd :
      ∀ block : List Γ, (∀ g ∈ block, g ≠ default) →
        ∀ g ∈ block ++ [some (Sum.inr directChainCons)], g ≠ default := by
    intro block hblock g hg
    simp [List.mem_append] at hg
    rcases hg with hg | rfl
    · exact hblock g hg
    · simp [Γ]
  have hcomp := tm0RealizesBlock_comp happ hcons happ_nd
  simpa [shiftedFinishBlock, Function.comp, Γ] using hcomp

theorem shiftedFinishBlock_on_payload
    {T : Type} [Primcodable T] (w : List T) :
    shiftedFinishBlock (T := T)
        ((shiftedPayload w).map (some ∘ @Sum.inr T ChainΓ)) =
      (shiftedChainTape w).map (directBlankEmb (T := T)) := by
  have hpayload :
      (shiftedPayload w).map (some ∘ @Sum.inr T ChainΓ) =
        (shiftedPayload w).map (directBlankEmb (T := T)) := by
    apply List.map_congr_left
    intro a ha
    exact (directBlankEmb_ne_default a
      (shiftedPayload_ne_default w a ha)).symm
  simp [shiftedFinishBlock, shiftedChainTape, hpayload,
    directBlankEmb_ne_default, chainConsBottom_ne_default,
    directChainCons_ne_default]

/-! ### Remaining direct-converter obligation -/

/-- The reduced converter obligation for the direct bridge.

It maps identity-encoded input `w` to the embedded Partrec-chain tape for
`shiftedEncoding w`.  Since `T` is finite, this is implemented by the finite
per-symbol substitution fold above rather than binary arithmetic on the tape. -/
def ShiftedEncodingConverter
    (T : Type) [DecidableEq T] [Fintype T] [Primcodable T] : Prop :=
  ∃ (Λ_conv : Type) (_ : Inhabited Λ_conv) (_ : Fintype Λ_conv)
    (M_conv : TM0.Machine (Option (T ⊕ ChainΓ)) Λ_conv),
    ∀ w : List T,
      (TM0Seq.evalCfg M_conv (w.map (fun x => some (Sum.inl x)))).Dom ∧
      ∀ (h : (TM0Seq.evalCfg M_conv
          (w.map (fun x => some (Sum.inl x)))).Dom),
        ((TM0Seq.evalCfg M_conv
          (w.map (fun x => some (Sum.inl x)))).get h).Tape =
          Tape.mk₁
            ((TM2to1.trInit PartrecToTM2.K'.main
              (PartrecToTM2.trList (shiftedEncoding w))).map
              (directBlankEmb (T := T)))

theorem shifted_converter_exists
    {T : Type} [DecidableEq T] [Fintype T] [Primcodable T] :
    ShiftedEncodingConverter T := by
  obtain ⟨Λ₁, hΛ₁i, hΛ₁f, M₁, hM₁⟩ := shiftedFoldRealizes (T := T)
  obtain ⟨Λ₂, hΛ₂i, hΛ₂f, M₂, hM₂⟩ := shiftedFinishBlock_realizes T
  letI : Inhabited (Λ₁ ⊕ Λ₂) := ⟨Sum.inl default⟩
  refine ⟨Λ₁ ⊕ Λ₂, inferInstance, inferInstance,
    TM0Seq.compose M₁ M₂, ?_⟩
  intro w
  let mid : List (Option (T ⊕ ChainΓ)) :=
    (shiftedPayload w).map (some ∘ @Sum.inr T ChainΓ)
  let out : List (Option (T ⊕ ChainΓ)) :=
    (shiftedChainTape w).map (directBlankEmb (T := T))
  have h1_dom := (hM₁ w).1
  have h1_tape := (hM₁ w).2 h1_dom
  have hmid_nd : ∀ g ∈ mid, g ≠ (default : Option (T ⊕ ChainΓ)) := by
    intro g hg
    rcases List.mem_map.mp hg with ⟨a, _ha, rfl⟩
    simp [mid]
  have hfinish_eq : shiftedFinishBlock (T := T) mid = out := by
    simpa [mid, out] using shiftedFinishBlock_on_payload (T := T) w
  have h2_spec := hM₂ mid [] hmid_nd (by simp) (by
    rw [hfinish_eq]
    intro g hg
    rcases List.mem_map.mp hg with ⟨a, ha, rfl⟩
    rw [directBlankEmb_ne_default a (shiftedChainTape_ne_default w a ha)]
    simp)
  have h2_dom := h2_spec.1
  have h2_tape := h2_spec.2
  have heval2 :
      TM0Seq.evalCfg M₂ mid = TM0Seq.evalCfg M₂ (mid ++ [default]) := by
    rw [evalCfg_append_default]
  have h2_dom_mid : (TM0Seq.evalCfg M₂ mid).Dom := by
    rw [heval2]
    exact h2_dom
  have h2_tape_mid (h : (TM0Seq.evalCfg M₂ mid).Dom) :
      ((TM0Seq.evalCfg M₂ mid).get h).Tape = Tape.mk₁ out := by
    have h' : (TM0Seq.evalCfg M₂ (mid ++ [default])).Dom := by
      rw [← heval2]
      exact h
    have hget :
        (TM0Seq.evalCfg M₂ mid).get h =
          (TM0Seq.evalCfg M₂ (mid ++ [default])).get h' := by
      apply Part.get_eq_get_of_eq
      exact heval2
    rw [hget, h2_tape h', hfinish_eq, tape_mk₁_append_default]
  have hcomp_dom :
      (TM0Seq.evalCfg (TM0Seq.compose M₁ M₂)
        (w.map (fun x => some (Sum.inl x)))).Dom := by
    exact (TM0Seq.compose_dom_iff' M₁ M₂
      (w.map (fun x => some (Sum.inl x))) mid
      (by simpa [Function.comp] using h1_dom)
      (by simpa [mid, Function.comp] using h1_tape)).2 h2_dom_mid
  refine ⟨hcomp_dom, ?_⟩
  intro h
  have htape_comp :
      ((TM0Seq.evalCfg (TM0Seq.compose M₁ M₂)
        (w.map (fun x => some (Sum.inl x)))).get h).Tape =
        Tape.mk₁ (out ++ []) := by
    rw [TM0Seq.compose_evalCfg_tape M₁ M₂
      (w.map (fun x => some (Sum.inl x))) mid
      (by simpa [Function.comp] using h1_dom)
      (by simpa [mid, Function.comp] using h1_tape)
      h2_dom_mid h]
    rw [h2_tape_mid h2_dom_mid]
    simp
  rw [htape_comp]
  simp [out, trInit_trList_shiftedEncoding_eq]

/-! ### Local alphabet embedding -/

/-- Embed a `ChainΓ` TM0 into `Option (T ⊕ ChainΓ)`, preserving blanks. -/
noncomputable def directEmbedTM0 {T : Type}
    {Λ : Type} [Inhabited Λ]
    (M : TM0.Machine ChainΓ Λ) :
    TM0.Machine (Option (T ⊕ ChainΓ)) Λ :=
  TM0AlphabetSim.liftMachine M
    (directBlankEmb (T := T))
    (directBlankInv (T := T))

/-- The direct embedding preserves halting behavior. -/
theorem directEmbedTM0_eval_dom {T : Type}
    {Λ : Type} [Inhabited Λ]
    (M : TM0.Machine ChainΓ Λ) (l : List ChainΓ) :
    (TM0.eval M l).Dom ↔
    (TM0.eval (directEmbedTM0 (T := T) M)
      (l.map (directBlankEmb (T := T)))).Dom :=
  TM0AlphabetSim.lift_eval_dom M _ _
    (directBlankInv_emb (T := T))
    (directBlankEmb_default (T := T))
    l

/-- Once the reduced converter exists, any `ToPartrec.Code`-semidecidable
language is `is_TM`.

This is the sound replacement target for the current arithmetic converter:
the Code-level list encoding is already handled by `composedCode`, and the
tape-level converter only needs to write `shiftedEncoding w`. -/
theorem code_implies_isTM_of_shifted_converter
    {T : Type} [DecidableEq T] [Fintype T] [Primcodable T]
    (hconv : ShiftedEncodingConverter T)
    (L : Language T)
    (c : ToPartrec.Code)
    (hL : ∀ w : List T, w ∈ L ↔ (c.eval [Encodable.encode w]).Dom) :
    is_TM L := by
  let c' := composedCode c
  obtain ⟨Λ₀, hΛ₀i, hΛ₀f, M₀, hM₀⟩ := code_to_tm0_fintype_general c'
  obtain ⟨Λ_conv, hΛci, hΛcf, M_conv, hM_conv⟩ := hconv
  letI : Inhabited (Λ_conv ⊕ Λ₀) := ⟨Sum.inl default⟩
  refine ⟨T ⊕ ChainΓ, inferInstance, Λ_conv ⊕ Λ₀, inferInstance,
    inferInstance,
    TM0Seq.compose M_conv (directEmbedTM0 (T := T) M₀),
    Sum.inl, ?_⟩
  intro w
  let input : List (Option (T ⊕ ChainΓ)) :=
    w.map (fun x => some (Sum.inl x))
  let chainInput : List ChainΓ :=
    TM2to1.trInit PartrecToTM2.K'.main
      (PartrecToTM2.trList (shiftedEncoding w))
  obtain ⟨hconv_dom, hconv_tape⟩ := hM_conv w
  have hconv_tape' :
      ((TM0Seq.evalCfg M_conv input).get (by simpa [input] using hconv_dom)).Tape =
        Tape.mk₁ (chainInput.map (directBlankEmb (T := T))) := by
    have hget :
        (TM0Seq.evalCfg M_conv input).get (by simpa [input] using hconv_dom) =
        (TM0Seq.evalCfg M_conv
          (w.map (fun x => some (Sum.inl x)))).get hconv_dom := by
      apply Part.get_eq_get_of_eq
      simp [input]
    rw [hget]
    simpa [chainInput] using hconv_tape hconv_dom
  have hcomp :
      (TM0.eval
        (TM0Seq.compose M_conv (directEmbedTM0 (T := T) M₀))
        input).Dom ↔
      (TM0.eval (directEmbedTM0 (T := T) M₀)
        (chainInput.map (directBlankEmb (T := T)))).Dom := by
    exact TM0Seq.compose_dom_iff' M_conv (directEmbedTM0 (T := T) M₀)
      input (chainInput.map (directBlankEmb (T := T)))
      (by simpa [input] using hconv_dom)
      hconv_tape'
  rw [hL]
  rw [← composedCode_halts_iff c w]
  rw [hM₀ (shiftedEncoding w)]
  rw [directEmbedTM0_eval_dom (T := T) M₀ chainInput]
  exact hcomp.symm

theorem code_implies_isTM_direct
    {T : Type} [DecidableEq T] [Fintype T] [Primcodable T]
    (L : Language T)
    (c : ToPartrec.Code)
    (hL : ∀ w : List T, w ∈ L ↔ (c.eval [Encodable.encode w]).Dom) :
    is_TM L :=
  code_implies_isTM_of_shifted_converter
    (shifted_converter_exists (T := T)) L c hL
