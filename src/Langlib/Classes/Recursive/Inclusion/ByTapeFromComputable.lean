module

public import Langlib.Automata.Recursive.Equivalence.TapeCharacterization
public import Langlib.Automata.Turing.DSL.PartrecCodeToTM0
public import Langlib.Automata.Turing.DSL.CodeToTMDirect
public import Mathlib.Computability.TMToPartrec
@[expose]
public section

/-! # `is_Recursive_byTape` from a computable decider

This file builds, from a total computable decider `f : List T → Bool` for a
language `L`, an always-halting TM0 over `Option (T ⊕ Γ)` that leaves a
designated `acceptSym` under the head exactly on the words of `L`, i.e.
`is_Recursive_byTape L`.

The construction threads the Mathlib `Code → TM2 → TM1 → TM0` translation chain,
but unlike the `.Dom`-only bridge `code_implies_isTM_direct`, it tracks the final
**tape** (not just halting), because acceptance is read off the head symbol.
-/

open Turing ToPartrec PartrecToTM2 TM2to1
open Langlib.TMCodeListEncode

namespace ByTapeFromComputable

/-! ## SPIKE: `Computable f → ToPartrec.Code` with characterized output

Given `f : List T → Bool` computable, we produce a `ToPartrec.Code` `bitCode`
with `bitCode.eval [Encodable.encode w] = some [if f w then 1 else 0]`.
-/

variable {T : Type} [DecidableEq T] [Fintype T] [Primcodable T]

/-- The unary `ℕ → ℕ` function: decode the input as a word and return the bit. -/
noncomputable def bitFn (f : List T → Bool) : ℕ → ℕ :=
  fun n => if ((Encodable.decode (α := List T) n).map f).getD false then 1 else 0

omit [DecidableEq T] [Fintype T] in
theorem bitFn_encode (f : List T → Bool) (w : List T) :
    bitFn f (Encodable.encode w) = if f w then 1 else 0 := by
  simp [bitFn, Encodable.encodek]

omit [DecidableEq T] [Fintype T] in
theorem computable_bitFn (f : List T → Bool) (hf : Computable f) :
    Computable (bitFn f) := by
  have hdec : Computable (fun n : ℕ => (Encodable.decode (α := List T) n).map f) :=
    Computable.option_map Computable.decode (hf.comp Computable.snd)
  have hgd : Computable (fun n : ℕ => ((Encodable.decode (α := List T) n).map f).getD false) :=
    Computable.option_getD hdec (Computable.const false)
  refine (Computable.cond hgd (Computable.const 1) (Computable.const 0)).of_eq ?_
  intro n
  unfold bitFn
  cases ((Encodable.decode (α := List T) n).map f).getD false <;> simp

omit [DecidableEq T] [Fintype T] in
theorem partrec_bitFn (f : List T → Bool) (hf : Computable f) :
    Nat.Partrec' (fun v : List.Vector ℕ 1 => (↑(bitFn f) : ℕ →. ℕ) v.head) := by
  rw [Nat.Partrec'.part_iff₁]
  exact Computable.partrec (computable_bitFn f hf)

/-- A `ToPartrec.Code` computing `bitFn f` (as a singleton output). -/
noncomputable def bitCode₀ (f : List T → Bool) (hf : Computable f) : Code :=
  (Code.exists_code (partrec_bitFn f hf)).choose

omit [DecidableEq T] [Fintype T] in
theorem bitCode₀_eval (f : List T → Bool) (hf : Computable f) (n : ℕ) :
    (bitCode₀ f hf).eval [n] = Part.some [bitFn f n] := by
  have hspec := (Code.exists_code (partrec_bitFn f hf)).choose_spec
  have := hspec (n ::ᵥ List.Vector.nil)
  simpa [bitCode₀] using this

/-! ## Output shaping: bit → `[]` / `[0]`

`Code.case Code.zero Code.nil` maps `[0] ↦ [0]` (reject) and `[1] ↦ []` (accept).
Composed with `bitCode₀`, the full code outputs `[]` exactly when `f w = true`. -/

/-- The full decider code on the encoded input. Outputs `[]` iff `f w = true`. -/
noncomputable def deciderCode (f : List T → Bool) (hf : Computable f) : Code :=
  Code.comp (Code.case Code.zero Code.nil) (bitCode₀ f hf)

omit [DecidableEq T] [Fintype T] in
theorem deciderCode_eval (f : List T → Bool) (hf : Computable f) (w : List T) :
    (deciderCode f hf).eval [Encodable.encode w] =
      Part.some (if f w then [] else [0]) := by
  unfold deciderCode
  rw [Code.comp_eval]
  simp only []
  rw [bitCode₀_eval, bitFn_encode]
  by_cases h : f w <;> simp [h, Code.case_eval, Code.zero_eval, Code.nil_eval]

omit [DecidableEq T] [Fintype T] in
theorem deciderCode_eval_dom (f : List T → Bool) (hf : Computable f) (w : List T) :
    ((deciderCode f hf).eval [Encodable.encode w]).Dom := by
  rw [deciderCode_eval]; exact trivial

/-! ## TM2 final configuration

By `PartrecToTM2.tr_eval`, the TM2 machine reaches `halt v` where `v` is the
output of the code. -/

/-- The output word of the decider code on `w`. -/
noncomputable def outWord (f : List T → Bool) (w : List T) : List ℕ :=
  if f w then [] else [0]

omit [DecidableEq T] [Fintype T] in
/-- The composed code (with list-encoding prefix) on `shiftedEncoding w`
evaluates to `outWord f w`. -/
theorem composedCode_outWord (f : List T → Bool) (hf : Computable f) (w : List T) :
    (composedCode (deciderCode f hf)).eval (shiftedEncoding w) =
      Part.some (outWord f w) := by
  have h := composedCode_eval (deciderCode f hf) (w.map Encodable.encode)
  rw [show (0 :: (List.map Encodable.encode w).reverse.map (· + 1) ++ [0]) =
      shiftedEncoding w from rfl] at h
  rw [h, ← list_encode_eq, deciderCode_eval]
  rfl

omit [DecidableEq T] [Fintype T] in
theorem tm2_eval_halt_composed (f : List T → Bool) (hf : Computable f) (w : List T) :
    PartrecToTM2.halt (outWord f w) ∈
      Turing.eval (TM2.step PartrecToTM2.tr)
        (PartrecToTM2.init (composedCode (deciderCode f hf)) (shiftedEncoding w)) := by
  rw [PartrecToTM2.tr_eval, composedCode_outWord]
  simp

/-! ## Generic chain tape descent (TM2 `halt v` → TM0 tape)

For any code `c` and input `v` such that the TM2 reaches `halt v`, the chain TM0
`ChainTM0` reaches a configuration whose tape head is the embedded final-tape
head. We track the full configuration via the Mathlib `Respects` relations.
-/

/-- The chain TM1 initial config (matches `partrec_init_trCfg`). -/
abbrev chainTM1Init (c : Code) (v : List ℕ) :
    TM1.Cfg ChainΓ ChainΛ_TM1 (Option PartrecToTM2.Γ') :=
  ⟨Option.map TM2to1.Λ'.normal (PartrecToTM2.init c v).l,
   (PartrecToTM2.init c v).var,
   (TM1.init (TM2to1.trInit PartrecToTM2.K'.main (PartrecToTM2.trList v)) :
     TM1.Cfg ChainΓ ChainΛ_TM1 (Option PartrecToTM2.Γ')).Tape⟩

/-- TM1 descent: the chain TM1 reaches some config with `TrCfg (halt vOut) cfg₁`,
where `vIn` is the input and `vOut` the reached output. -/
theorem tm1_descent (c : Code) (vIn vOut : List ℕ)
    (hhalt : PartrecToTM2.halt vOut ∈
      Turing.eval (TM2.step PartrecToTM2.tr) (PartrecToTM2.init c vIn)) :
    ∃ cfg₁ : TM1.Cfg ChainΓ ChainΛ_TM1 (Option PartrecToTM2.Γ'),
      TM2to1.TrCfg (PartrecToTM2.halt vOut) cfg₁ ∧
      cfg₁ ∈ Turing.eval (TM1.step ChainTM1) (chainTM1Init c vIn) := by
  have hresp := TM2to1.tr_respects (M := PartrecToTM2.tr)
  obtain ⟨cfg₁, htr, hmem⟩ := Turing.tr_eval hresp (partrec_init_trCfg c vIn) hhalt
  exact ⟨cfg₁, htr, hmem⟩

/-- TM0 descent: the chain TM0 reaches a config whose tape is the TM1 final tape,
starting from `TM1to0.trCfg ChainTM1 (chainTM1Init c v)`. -/
theorem tm0_descent (c : Code) (v : List ℕ)
    (cfg₁ : TM1.Cfg ChainΓ ChainΛ_TM1 (Option PartrecToTM2.Γ'))
    (hmem : cfg₁ ∈ Turing.eval (TM1.step ChainTM1) (chainTM1Init c v)) :
    (TM1to0.trCfg ChainTM1 cfg₁) ∈
      Turing.eval (TM0.step ChainTM0)
        (TM1to0.trCfg ChainTM1 (chainTM1Init c v)) := by
  have hresp := TM1to0.tr_respects (M := ChainTM1)
  obtain ⟨cfg₀, htr, hmem₀⟩ :=
    Turing.tr_eval hresp (a₁ := chainTM1Init c v)
      (a₂ := TM1to0.trCfg ChainTM1 (chainTM1Init c v)) rfl hmem
  rw [← htr] at hmem₀
  exact hmem₀

/-! ## Tape-tracking eval lemmas for reroot / restrict / alphabet-lift

Each underlying `Respects` relation preserves the tape, so `Turing.tr_eval`
transports a final config of known tape. -/

/-- Re-rooted TM0: a final config with tape `T` is reached, given the original
reaches a final config with tape `T` from `⟨q₀, Tape.mk₁ l⟩`. -/
theorem reroot_eval_tape {Γ : Type} [Inhabited Γ] {Λ : Type} [Inhabited Λ]
    (M : TM0.Machine Γ Λ) (q₀ : Λ) (l : List Γ) (cf : TM0.Cfg Γ Λ)
    (hmem : cf ∈ Turing.eval (TM0.step M) (⟨q₀, Tape.mk₁ l⟩ : TM0.Cfg Γ Λ)) :
    ∃ cf' : TM0.Cfg Γ (ParrecToTM0.Rooted Λ q₀),
      cf'.Tape = cf.Tape ∧
      cf' ∈ Turing.eval
        (ParrecToTM0.tm0Reroot M q₀ |> @TM0.step Γ (ParrecToTM0.Rooted Λ q₀) ⟨⟨q₀⟩⟩ _)
        (@TM0.init Γ (ParrecToTM0.Rooted Λ q₀) ⟨⟨q₀⟩⟩ _ l) := by
  have hresp := ParrecToTM0.tm0Reroot_respects M q₀
  obtain ⟨cf', hrel, hmem'⟩ :=
    Turing.tr_eval hresp
      (show (fun c₁ c₂ => c₁.q = c₂.q.val ∧ c₁.Tape = c₂.Tape)
        (⟨q₀, Tape.mk₁ l⟩ : TM0.Cfg Γ Λ)
        (⟨⟨q₀⟩, Tape.mk₁ l⟩ : TM0.Cfg Γ (ParrecToTM0.Rooted Λ q₀)) from ⟨rfl, rfl⟩)
      hmem
  exact ⟨cf', hrel.2.symm, hmem'⟩

/-- Restricted TM0: tape-tracking version of `restrict_eval_dom_iff`. -/
theorem restrict_eval_tape {Γ : Type} [Inhabited Γ] {Λ : Type} [Inhabited Λ]
    (M : TM0.Machine Γ Λ) (S : Finset Λ) (hS : TM0.Supports M ↑S) (l : List Γ)
    (cf : TM0.Cfg Γ Λ)
    (hmem : cf ∈ Turing.eval (TM0.step M) (TM0.init l)) :
    ∃ cf' : TM0.Cfg Γ {q : Λ // q ∈ S},
      cf'.Tape = cf.Tape ∧
      cf' ∈ @Turing.eval _ (@TM0.step Γ _ ⟨⟨default, hS.1⟩⟩ _ (Turing.TM0.restrict M S hS))
        (@TM0.init Γ _ ⟨⟨default, hS.1⟩⟩ _ l) := by
  have hresp := Turing.TM0.restrict_respects M S hS
  obtain ⟨cf', hrel, hmem'⟩ :=
    Turing.tr_eval hresp (Turing.TM0.restrict_init_rel M S hS l) hmem
  exact ⟨cf', hrel.2.symm, hmem'⟩

/-- Restrict+reroot TM0: tape-tracking version of `tm0RestrictReroot_eval_dom`. -/
theorem restrictReroot_eval_tape {Γ : Type} [Inhabited Γ] {Λ : Type} [Inhabited Λ]
    (M : TM0.Machine Γ Λ) (S : Finset Λ) (hS : TM0.Supports M ↑S)
    (q₀ : Λ) (hq₀ : q₀ ∈ S) (l : List Γ) (cf : TM0.Cfg Γ Λ)
    (hmem : cf ∈ Turing.eval (TM0.step M) (⟨q₀, Tape.mk₁ l⟩ : TM0.Cfg Γ Λ)) :
    letI : Inhabited
        { q : ParrecToTM0.Rooted Λ q₀ // q ∈ S.map (ParrecToTM0.rootedEmbFn (q₀ := q₀)) } :=
      ⟨⟨⟨q₀⟩, by rw [Finset.mem_map]; exact ⟨q₀, hq₀, rfl⟩⟩⟩
    ∃ cf' : TM0.Cfg Γ
        { q : ParrecToTM0.Rooted Λ q₀ // q ∈ S.map (ParrecToTM0.rootedEmbFn (q₀ := q₀)) },
      cf'.Tape = cf.Tape ∧
      cf' ∈ Turing.eval
        (TM0.step (ParrecToTM0.tm0RestrictReroot M S hS q₀ hq₀))
        (TM0.init l) := by
  obtain ⟨cf₁, hcf₁tape, hcf₁mem⟩ := reroot_eval_tape M q₀ l cf hmem
  have hS' := ParrecToTM0.tm0Reroot_supports M S hS q₀ hq₀
  obtain ⟨cf₂, hcf₂tape, hcf₂mem⟩ :=
    restrict_eval_tape (ParrecToTM0.tm0Reroot M q₀) (S.map ParrecToTM0.rootedEmbFn) hS' l cf₁
      hcf₁mem
  refine ⟨cf₂, by rw [hcf₂tape, hcf₁tape], ?_⟩
  exact hcf₂mem

/-- Alphabet-lifted TM0: tape-tracking version of `lift_eval_dom`. -/
theorem lift_eval_tape {Γ Γ₂ : Type} [Inhabited Γ] [Inhabited Γ₂] {Λ : Type} [Inhabited Λ]
    (M : TM0.Machine Γ Λ) (emb : Γ → Γ₂) (inv : Γ₂ → Γ)
    (hemb : ∀ a, inv (emb a) = a) (hemb_default : emb default = default)
    (l : List Γ) (cf : TM0.Cfg Γ Λ)
    (hmem : cf ∈ Turing.eval (TM0.step M) (TM0.init l)) :
    ∃ cf' : TM0.Cfg Γ₂ Λ,
      cf'.Tape = cf.Tape.map (TM0AlphabetSim.embPM emb hemb_default) ∧
      cf' ∈ Turing.eval (TM0.step (TM0AlphabetSim.liftMachine M emb inv)) (TM0.init (l.map emb)) := by
  have hresp := TM0AlphabetSim.lift_respects M emb inv hemb hemb_default
  obtain ⟨cf', hrel, hmem'⟩ :=
    Turing.tr_eval hresp
      (TM0AlphabetSim.lift_init_rel emb inv hemb hemb_default l) hmem
  exact ⟨cf', hrel.2, hmem'⟩

/-! ## The final TM1 tape head for a `halt v` config

From `TrCfg (halt v) cfg₁`, the TM1 tape head is `(true, L.head)` where each
stack component is the head of the reversed encoded stack. -/

theorem trCfg_halt_head (v : List ℕ)
    (cfg₁ : TM1.Cfg ChainΓ ChainΛ_TM1 (Option PartrecToTM2.Γ'))
    (htr : TM2to1.TrCfg (PartrecToTM2.halt v) cfg₁) :
    cfg₁.Tape.head =
      (true, fun k => ((PartrecToTM2.K'.elim (PartrecToTM2.trList v) [] [] [] k).map
        some).reverse.headI) := by
  rcases htr with @⟨q, var, S, L, hL⟩
  -- The TM1 config is ⟨none, none, Tape.mk' ∅ (addBottom L)⟩; its head = (addBottom L).head.
  simp only [TM2to1.addBottom] at *
  rw [Tape.mk'_head]
  rw [show (ListBlank.cons (true, L.head)
      (L.tail.map ⟨Prod.mk false, rfl⟩)).head = (true, L.head) from
    ListBlank.head_cons _ _]
  congr 1
  funext k
  have hk := congrArg ListBlank.head (hL k)
  rw [ListBlank.head_map, ListBlank.head_mk] at hk
  -- hk : (proj k) L.head = ((K'.elim ... k).map some).reverse.headI
  exact hk

/-- The TM1 final tape head for the accepting output `[]`. -/
theorem trCfg_halt_head_accept
    (cfg₁ : TM1.Cfg ChainΓ ChainΛ_TM1 (Option PartrecToTM2.Γ'))
    (htr : TM2to1.TrCfg (PartrecToTM2.halt ([] : List ℕ)) cfg₁) :
    cfg₁.Tape.head = ((true, fun _ => none) : ChainΓ) := by
  rw [trCfg_halt_head [] cfg₁ htr]
  congr 1
  funext k
  cases k <;> simp [PartrecToTM2.K'.elim, PartrecToTM2.trList,
    show (default : Option PartrecToTM2.Γ') = none from rfl]

/-- The TM1 final tape head for the rejecting output `[0]`. -/
theorem trCfg_halt_head_reject
    (cfg₁ : TM1.Cfg ChainΓ ChainΛ_TM1 (Option PartrecToTM2.Γ'))
    (htr : TM2to1.TrCfg (PartrecToTM2.halt ([0] : List ℕ)) cfg₁) :
    (cfg₁.Tape.head).2 PartrecToTM2.K'.main = some PartrecToTM2.Γ'.cons := by
  rw [trCfg_halt_head [0] cfg₁ htr]
  simp [PartrecToTM2.K'.elim, PartrecToTM2.trList, PartrecToTM2.trNat]

omit [DecidableEq T] [Fintype T] [Primcodable T] in
/-- `directBlankEmb` is injective (it has the left inverse `directBlankInv`). -/
theorem directBlankEmb_injective :
    Function.Injective (directBlankEmb (T := T) (Γ₀ := ChainΓ)) := by
  intro a b h
  have := congrArg (directBlankInv (T := T)) h
  rwa [directBlankInv_emb, directBlankInv_emb] at this

/-- The accepting symbol: the embedding of the accept TM1 head. -/
noncomputable def acceptSym : Option (T ⊕ ChainΓ) :=
  directBlankEmb (T := T) ((true, fun _ => none) : ChainΓ)

omit [DecidableEq T] [Fintype T] [Primcodable T] in
/-- A reject head (whose `main` component is `some cons`) embeds to something
different from `acceptSym`. -/
theorem reject_head_ne_acceptSym (h : ChainΓ)
    (hh : h.2 PartrecToTM2.K'.main = some PartrecToTM2.Γ'.cons) :
    directBlankEmb (T := T) h ≠ acceptSym (T := T) := by
  intro heq
  unfold acceptSym at heq
  have := directBlankEmb_injective (T := T) heq
  rw [this] at hh
  simp at hh

/-! ## Chain TM0 with Fintype states and final tape

The analogue of `code_to_tm0_fintype_general`, but additionally producing the
final tape (the embedded `addBottom L` head). -/

theorem code_to_tm0_tape (c : Code) :
    ∃ (ΛTy : Type) (_ : Inhabited ΛTy) (_ : Fintype ΛTy)
      (M : TM0.Machine ChainΓ ΛTy),
      ∀ (vIn vOut : List ℕ),
        PartrecToTM2.halt vOut ∈
          Turing.eval (TM2.step PartrecToTM2.tr) (PartrecToTM2.init c vIn) →
        ∃ cf : TM0.Cfg ChainΓ ΛTy,
          cf ∈ Turing.eval (TM0.step M)
            (TM0.init (TM2to1.trInit PartrecToTM2.K'.main (PartrecToTM2.trList vIn))) ∧
          ∀ (cfg₁ : TM1.Cfg ChainΓ ChainΛ_TM1 (Option PartrecToTM2.Γ')),
            TM2to1.TrCfg (PartrecToTM2.halt vOut) cfg₁ →
            cfg₁ ∈ Turing.eval (TM1.step ChainTM1) (chainTM1Init c vIn) →
            cf.Tape = cfg₁.Tape := by
  letI inhΛ' : Inhabited PartrecToTM2.Λ' :=
    ⟨PartrecToTM2.trNormal c PartrecToTM2.Cont'.halt⟩
  have hTM2 := PartrecToTM2.tr_supports c PartrecToTM2.Cont'.halt
  have hTM1 := TM2to1.tr_supports PartrecToTM2.tr hTM2
  let M₀ : TM0.Machine ChainΓ ChainΛ_TM0 := TM1to0.tr (TM2to1.tr PartrecToTM2.tr)
  have hTM0 : TM0.Supports M₀
      ↑(TM1to0.trStmts (TM2to1.tr PartrecToTM2.tr)
        (TM2to1.trSupp PartrecToTM2.tr (PartrecToTM2.codeSupp c .halt))) :=
    TM1to0.tr_supports (TM2to1.tr PartrecToTM2.tr) hTM1
  let S := TM1to0.trStmts (TM2to1.tr PartrecToTM2.tr)
    (TM2to1.trSupp PartrecToTM2.tr (PartrecToTM2.codeSupp c .halt))
  let q₀ : TM1to0.Λ' (TM2to1.tr PartrecToTM2.tr) := default
  have hq₀ : q₀ ∈ S := hTM0.1
  refine ⟨{ q : ParrecToTM0.Rooted ChainΛ_TM0 q₀ // q ∈ S.map ParrecToTM0.rootedEmbFn },
    ⟨⟨⟨q₀⟩, by rw [Finset.mem_map]; exact ⟨q₀, hq₀, rfl⟩⟩⟩,
    ParrecToTM0.tm0RestrictReroot_fintype S q₀,
    ParrecToTM0.tm0RestrictReroot M₀ S hTM0 q₀ hq₀,
    fun vIn vOut hhalt => ?_⟩
  -- Descend TM2 → TM1 → TM0 (chain machine).
  obtain ⟨cfg₁, htr, hmem₁⟩ := tm1_descent c vIn vOut hhalt
  have hmem₀ := tm0_descent c vIn cfg₁ hmem₁
  -- Rewrite chain TM0 start config to ⟨default, mk₁ (trInit...)⟩.
  rw [chainTM0_trCfg_eq_general c vIn] at hmem₀
  -- Apply restrict+reroot tape tracking.
  obtain ⟨cf, hcf_tape, hcf_mem⟩ :=
    restrictReroot_eval_tape M₀ S hTM0 q₀ hq₀
      (TM2to1.trInit PartrecToTM2.K'.main (PartrecToTM2.trList vIn))
      (TM1to0.trCfg ChainTM1 cfg₁) hmem₀
  refine ⟨cf, hcf_mem, ?_⟩
  intro cfg₁' htr' hmem₁'
  -- cfg₁ and cfg₁' both reached and trCfg-related to halt v; identify their tapes.
  have hcf_tape' : cf.Tape = (TM1to0.trCfg ChainTM1 cfg₁).Tape := hcf_tape
  -- TM1 final config is unique: cfg₁ = cfg₁'.
  have huniq : cfg₁ = cfg₁' := Part.mem_unique hmem₁ hmem₁'
  rw [hcf_tape', ← huniq]
  rfl

/-! ## Final assembly -/

/-- The chain input tape (over `ChainΓ`) for word `w`. -/
noncomputable def chainInput (w : List T) : List ChainΓ :=
  TM2to1.trInit PartrecToTM2.K'.main (PartrecToTM2.trList (shiftedEncoding w))

/-- **`is_Recursive_byTape` from a computable decider.**

The assembled TM0 over `Option (T ⊕ ChainΓ)` is
`compose M_conv (directEmbedTM0 M)`, where `M_conv` writes the chain input from
`w`, `M` is the chain decider, and the alphabet is lifted via `directBlankEmb`.
It always halts and its final head is `acceptSym` exactly on words of `L`. -/
theorem is_Recursive_byTape_of_computable_decide
    (L : Language T) (f : List T → Bool) (hf : Computable f)
    (hL : ∀ w, w ∈ L ↔ f w = true) :
    is_Recursive_byTape L := by
  classical
  -- The chain decider machine and its tape spec.
  obtain ⟨Λ₀, hΛ₀i, hΛ₀f, M, hM⟩ := code_to_tm0_tape (composedCode (deciderCode f hf))
  -- The converter machine.
  obtain ⟨Λ_conv, hΛci, hΛcf, M_conv, hM_conv⟩ := shifted_converter_exists (T := T)
  letI : Inhabited (Λ_conv ⊕ Λ₀) := ⟨Sum.inl default⟩
  -- Core per-word fact: the composed machine halts, and its final config tape
  -- equals the embedded TM1 final tape for `halt (outWord f w)`.
  have hcore : ∀ w : List T,
      ∃ cfg₁ : TM1.Cfg ChainΓ ChainΛ_TM1 (Option PartrecToTM2.Γ'),
        TM2to1.TrCfg (PartrecToTM2.halt (outWord f w)) cfg₁ ∧
        ∃ cf : TM0.Cfg (Option (T ⊕ ChainΓ)) (Λ_conv ⊕ Λ₀),
          cf ∈ Turing.eval (TM0.step (TM0Seq.compose M_conv (directEmbedTM0 (T := T) M)))
            (TM0.init (w.map fun t => some (Sum.inl t))) ∧
          cf.Tape.head = directBlankEmb (T := T) cfg₁.Tape.head := by
    intro w
    -- 1. M halts on chainInput w with tape = cfg₁.Tape.
    have hhaltM := tm2_eval_halt_composed f hf w
    obtain ⟨cfM, hcfM_mem, hcfM_tape⟩ := hM (shiftedEncoding w) (outWord f w) hhaltM
    -- Recover the TM1 final config cfg₁.
    obtain ⟨cfg₁, htr, hmem₁⟩ :=
      tm1_descent (composedCode (deciderCode f hf)) (shiftedEncoding w) (outWord f w) hhaltM
    have hcfM_tape' : cfM.Tape = cfg₁.Tape := hcfM_tape cfg₁ htr hmem₁
    -- 2. Lift M to directEmbedTM0: halts on chainInput.map directBlankEmb, tape = embedded.
    obtain ⟨cfL, hcfL_tape, hcfL_mem⟩ :=
      lift_eval_tape M (directBlankEmb (T := T)) (directBlankInv (T := T))
        (directBlankInv_emb (T := T)) (directBlankEmb_default (T := T))
        (chainInput w) cfM
        (by simpa [chainInput] using hcfM_mem)
    -- 3. Converter final tape.
    obtain ⟨hconv_dom, hconv_tape⟩ := hM_conv w
    -- 4. Compose: identify everything via the tape-tracking lemmas.
    refine ⟨cfg₁, htr, ?_⟩
    -- the converter output tape (list form).
    set midList : List (Option (T ⊕ ChainΓ)) :=
      (chainInput w).map (directBlankEmb (T := T)) with hmidList
    have hconv_dom' : (TM0Seq.evalCfg M_conv (w.map fun t => some (Sum.inl t))).Dom := hconv_dom
    have hconv_tape' :
        ((TM0Seq.evalCfg M_conv (w.map fun t => some (Sum.inl t))).get hconv_dom).Tape =
          Tape.mk₁ midList := by
      simpa [chainInput, midList] using hconv_tape hconv_dom
    -- lifted machine halts on midList.
    have hL2_dom : (TM0Seq.evalCfg (directEmbedTM0 (T := T) M) midList).Dom := by
      refine Part.dom_iff_mem.mpr ⟨cfL, ?_⟩
      simpa [TM0Seq.evalCfg, midList, directEmbedTM0, TM0.init] using hcfL_mem
    -- composition halts.
    have hcomp_dom :
        (TM0Seq.evalCfg (TM0Seq.compose M_conv (directEmbedTM0 (T := T) M))
          (w.map fun t => some (Sum.inl t))).Dom :=
      (TM0Seq.compose_dom_iff' M_conv (directEmbedTM0 (T := T) M)
        (w.map fun t => some (Sum.inl t)) midList hconv_dom' hconv_tape').2
        (by simpa [TM0Seq.evalCfg] using hL2_dom)
    -- composition final tape = lifted machine final tape on midList.
    have hcomp_tape :
        ((TM0Seq.evalCfg (TM0Seq.compose M_conv (directEmbedTM0 (T := T) M))
          (w.map fun t => some (Sum.inl t))).get hcomp_dom).Tape =
          ((TM0Seq.evalCfg (directEmbedTM0 (T := T) M) midList).get
            (by simpa [TM0Seq.evalCfg] using hL2_dom)).Tape :=
      TM0Seq.compose_evalCfg_tape M_conv (directEmbedTM0 (T := T) M)
        (w.map fun t => some (Sum.inl t)) midList hconv_dom' hconv_tape'
        (by simpa [TM0Seq.evalCfg] using hL2_dom) hcomp_dom
    -- lifted machine final config is cfL.
    have hcfL_get :
        (TM0Seq.evalCfg (directEmbedTM0 (T := T) M) midList).get
          (by simpa [TM0Seq.evalCfg] using hL2_dom) = cfL := by
      apply Part.get_eq_of_mem
      simpa [TM0Seq.evalCfg, midList, directEmbedTM0, TM0.init] using hcfL_mem
    -- assemble.
    set cf := (TM0Seq.evalCfg (TM0Seq.compose M_conv (directEmbedTM0 (T := T) M))
      (w.map fun t => some (Sum.inl t))).get hcomp_dom with hcfdef
    have hcf_eq : cf.Tape = cfg₁.Tape.map
        (TM0AlphabetSim.embPM (directBlankEmb (T := T)) (directBlankEmb_default (T := T))) := by
      rw [hcfdef, hcomp_tape, hcfL_get, hcfL_tape, hcfM_tape']
    refine ⟨cf, Part.get_mem hcomp_dom, ?_⟩
    rw [hcf_eq, Tape.map_fst]
    rfl
  -- Now split into the two `is_Recursive_byTape` obligations.
  refine ⟨ChainΓ, inferInstance, inferInstance, Λ_conv ⊕ Λ₀, inferInstance, inferInstance,
    TM0Seq.compose M_conv (directEmbedTM0 (T := T) M), acceptSym (T := T),
    fun w => ?_, fun w h => ?_⟩
  · obtain ⟨cfg₁, htr, cf, hcf_mem, _⟩ := hcore w
    exact Part.dom_iff_mem.mpr ⟨cf, hcf_mem⟩
  · obtain ⟨cfg₁, htr, cf, hcf_mem, hcf_head⟩ := hcore w
    have hget :
        (Turing.eval (TM0.step (TM0Seq.compose M_conv (directEmbedTM0 (T := T) M)))
          (TM0.init (w.map fun t => some (Sum.inl t)))).get h = cf :=
      Part.get_eq_of_mem hcf_mem h
    rw [hget, hcf_head, hL]
    -- Characterize via outWord: f w = true ↔ head = acceptSym.
    by_cases hfw : f w = true
    · -- accept: outWord = [], head = (true, fun _ => none), embed = acceptSym.
      have hout : outWord f w = ([] : List ℕ) := by simp [outWord, hfw]
      rw [hout] at htr
      rw [trCfg_halt_head_accept cfg₁ htr]
      simp only [acceptSym, hfw]
    · -- reject: outWord = [0], head.2 main = some cons, embed ≠ acceptSym.
      have hfw' : f w = false := by simpa using hfw
      have hout : outWord f w = ([0] : List ℕ) := by simp [outWord, hfw']
      rw [hout] at htr
      have hmain := trCfg_halt_head_reject cfg₁ htr
      have hne := reject_head_ne_acceptSym (T := T) cfg₁.Tape.head hmain
      simp only [hfw', Bool.false_eq_true, false_iff]
      exact hne

end ByTapeFromComputable

/-- **`is_Recursive_byTape` from a computable decider** (top-level form). -/
theorem is_Recursive_byTape_of_computable_decide
    {T : Type} [DecidableEq T] [Fintype T] [Primcodable T]
    (L : Language T) (f : List T → Bool) (hf : Computable f)
    (hL : ∀ w, w ∈ L ↔ f w = true) :
    is_Recursive_byTape L :=
  ByTapeFromComputable.is_Recursive_byTape_of_computable_decide L f hf hL

/-- **A total computable Boolean decision procedure yields a recursive language.**
Combining the tape-output decider construction with the tape-vs-state acceptance
equivalence `is_Recursive_of_byTape`. -/
theorem is_Recursive_of_computable_decide
    {T : Type} [DecidableEq T] [Fintype T] [Primcodable T]
    (L : Language T) (f : List T → Bool) (hf : Computable f)
    (hL : ∀ w, w ∈ L ↔ f w = true) :
    is_Recursive L :=
  is_Recursive_of_byTape (is_Recursive_byTape_of_computable_decide L f hf hL)
