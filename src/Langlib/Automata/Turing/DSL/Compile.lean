import Mathlib
import Langlib.Automata.Turing.DSL.SearchProc
import Langlib.Automata.Turing.DSL.TM0Restrict
import Langlib.Automata.Turing.DSL.AlphabetSim
import Langlib.Automata.Turing.DSL.EmptyTM
import Langlib.Automata.Turing.DSL.ParrecToTM0
import Langlib.Automata.Turing.DSL.ParrecChain

/-! # Compilation of Search Procedures to TM0

This file proves the key compilation theorem: if a language can be expressed
as `{ w | ∃ a : α, test a w = true }` for a `Primcodable` witness type `α`
and a `Computable₂` test function, then the language is TM-recognizable
by a TM0 machine.

## Main results

- `search_is_partrec` — the µ-search is Partrec
- `code_to_tm0` — Code → TM0 evaluation
- `search_halts_tm0` — **PROVED**: the search is TM0-recognizable (with an
  internal `Fintype` tape alphabet)
- `is_TM_of_searchable` — **PROVED**: searchable languages are internally
  TM-recognizable

## Architecture note

The compilation produces a TM0 over the chain's internal alphabet (`ChainΓ`),
not over `Option T`. Converting to `Option T` requires **alphabet simulation**
(encoding `ChainΓ` symbols as blocks of `Option T` symbols), which is a
standard but substantial result in TM theory. The theorem
`is_TM_internal_to_TM` in `InternalTM.lean` provides this conversion
(currently sorry'd).

The key mathematical content — that computable search is TM-recognizable —
is fully proved here. The alphabet simulation is a separate, orthogonal concern.
-/

open Turing

/-! ### Fintype instances for Partrec types -/

instance : Fintype PartrecToTM2.K' :=
  Fintype.ofList [.main, .rev, .aux, .stack] (by intro x; cases x <;> simp)

instance : Fintype PartrecToTM2.Γ' :=
  Fintype.ofList [.consₗ, .cons, .bit0, .bit1] (by intro x; cases x <;> simp)

/-! ### Search Step Function -/

/-- The "step" function of the search: enumerate the `n`-th witness and test it. -/
def searchStep {T : Type} {α : Type} [Encodable α]
    (test : α → List T → Bool) (w : List T) (n : ℕ) : Bool :=
  match Encodable.decode (α := α) n with
  | some a => test a w
  | none => false

/-- The search succeeds iff there exists a witness. -/
theorem searchStep_iff {T : Type} {α : Type} [Encodable α]
    (test : α → List T → Bool) (w : List T) :
    (∃ n, searchStep test w n = true) ↔ (∃ a : α, test a w = true) := by
  constructor
  · rintro ⟨n, hn⟩
    simp [searchStep] at hn
    cases h : Encodable.decode (α := α) n with
    | none => simp [h] at hn
    | some a => exact ⟨a, by simp [h] at hn; exact hn⟩
  · rintro ⟨a, ha⟩
    exact ⟨Encodable.encode a, by simp [searchStep, Encodable.encodek, ha]⟩

/-! ### Sub-problem 1: Computable₂ test → Code (PROVED) -/

set_option maxHeartbeats 800000

/-- The encoded search step function on ℕ × ℕ.
Maps `(m, k)` to `true` if `k` decodes to a witness `a` such that
`test a (decode m)` is true. -/
private def gEnc {T : Type} {α : Type} [Primcodable T] [Primcodable α]
    (test : α → List T → Bool) (m k : ℕ) : Bool :=
  ((Encodable.decode (α := α) k).map
    (fun a => test a ((Encodable.decode (α := List T) m).getD []))).getD false

/-- For `m = encode w`, `gEnc test (encode w) k` matches the search step. -/
private lemma gEnc_encode_eq {T : Type} {α : Type} [Primcodable T] [Primcodable α]
    (test : α → List T → Bool) (w : List T) (k : ℕ) :
    gEnc test (Encodable.encode w) k =
    match Encodable.decode (α := α) k with
    | some a => test a w
    | none => false := by
  simp [gEnc, Encodable.encodek]
  cases Encodable.decode (α := α) k <;> simp

@[simp] private lemma vector_head_singleton (n : ℕ) :
    List.Vector.head (⟨[n], rfl⟩ : List.Vector ℕ 1) = n := rfl

/-- **Sub-problem 1** (PROVED): The µ-search over a computable test is Partrec. -/
theorem search_is_partrec {T : Type} {α : Type}
    [Primcodable T] [Primcodable α]
    (test : α → List T → Bool) (hc : Computable₂ test) :
    ∃ c : ToPartrec.Code,
      ∀ w : List T,
        (∃ a : α, test a w = true) ↔ (c.eval [Encodable.encode w]).Dom := by
  -- Step 1: gEnc is Computable₂
  have hg : Computable₂ (gEnc test) := by
    unfold gEnc
    exact Computable.option_getD
      (Computable.option_map
        (Computable.decode.comp Computable.snd)
        (hc.comp
          (g := fun x : (ℕ × ℕ) × α => x.2)
          (h := fun x => ((Encodable.decode (α := List T) x.1.1).getD []))
          Computable.snd
          ((Computable.decode.comp (Computable.fst.comp Computable.fst)).option_getD
            (Computable.const []))))
      (Computable.const false)
  -- Step 2: µ-search is Partrec via Partrec.rfind
  have hf : Partrec (fun m => Nat.rfind (fun k => Part.some (gEnc test m k))) :=
    Partrec.rfind hg.partrec
  -- Step 3: Convert to Nat.Partrec'
  rw [← Nat.Partrec'.part_iff₁] at hf
  -- Step 4: Get Code via exists_code
  obtain ⟨c, hc'⟩ := ToPartrec.Code.exists_code hf
  refine ⟨c, fun w => ?_⟩
  -- Step 5: Show Dom equivalence
  have key : (c.eval [Encodable.encode w]).Dom ↔
      ∃ k, gEnc test (Encodable.encode w) k = true := by
    have h := hc' ⟨[Encodable.encode w], rfl⟩
    simp [vector_head_singleton] at h
    rw [show [Encodable.encode w] =
        (⟨[Encodable.encode w], rfl⟩ : List.Vector ℕ 1).val from rfl, h]
    simp [Nat.rfind_dom]
  rw [key]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨Encodable.encode a, by rw [gEnc_encode_eq]; simp [Encodable.encodek, ha]⟩
  · rintro ⟨k, hk⟩
    rw [gEnc_encode_eq] at hk
    cases h : Encodable.decode (α := α) k with
    | none => simp [h] at hk
    | some a => exact ⟨a, by simp [h] at hk; exact hk⟩

/-! ### Sub-problem 2: Code → TM0 (PROVED) -/

/-- **Sub-problem 2** (PROVED): Partrec Code → TM0 evaluation. -/
theorem code_to_tm0 (c : ToPartrec.Code) :
    ∃ (Γ : Type) (Λ : Type)
      (_ : Inhabited Λ)
      (_ : Inhabited Γ) (_ : Fintype Γ)
      (encode_input : ℕ → List Γ)
      (M : TM0.Machine Γ Λ),
      ∀ n : ℕ,
        (c.eval [n]).Dom ↔ (TM0.eval M (encode_input n)).Dom := by
  let q₀ : ChainΛ_TM0 :=
    (TM1to0.trCfg ChainTM1
      ⟨Option.map TM2to1.Λ'.normal (PartrecToTM2.init c [0]).l,
       (PartrecToTM2.init c [0]).var,
       (TM1.init (TM2to1.trInit PartrecToTM2.K'.main (PartrecToTM2.trList [0])) :
         TM1.Cfg ChainΓ ChainΛ_TM1 (Option PartrecToTM2.Γ')).Tape⟩).q
  refine ⟨ChainΓ, ParrecToTM0.Rooted ChainΛ_TM0 q₀, ⟨⟨q₀⟩⟩,
    inferInstance, inferInstance,
    fun n => TM2to1.trInit PartrecToTM2.K'.main (PartrecToTM2.trList [n]),
    ParrecToTM0.tm0Reroot ChainTM0 q₀, fun n => ?_⟩
  have hq : q₀ = (TM1to0.trCfg ChainTM1
      ⟨Option.map TM2to1.Λ'.normal (PartrecToTM2.init c [n]).l,
       (PartrecToTM2.init c [n]).var,
       (TM1.init (TM2to1.trInit PartrecToTM2.K'.main (PartrecToTM2.trList [n])) :
         TM1.Cfg ChainΓ ChainΛ_TM1 (Option PartrecToTM2.Γ')).Tape⟩).q := by
    simp [q₀, TM1to0.trCfg, PartrecToTM2.init]
  rw [hq]
  exact code_to_tm0_halts c [n]

/-! ### Core Compilation Theorem (PROVED) -/

/-- **The core compilation theorem** (PROVED, 0 sorry).

The enumerate-and-test search pattern is implementable by a TM0 machine
over the Partrec chain's internal `Fintype` alphabet `ChainΓ`. The TM0
halts on `enc w` if and only if there exists a witness `a` such that
`test a w = true`.

This theorem captures the full mathematical content: computable search
procedures yield TM-recognizable languages. The tape alphabet is the
chain's internal alphabet rather than `Option T`; converting to `Option T`
requires alphabet simulation (see `tm0_alphabet_simulation` below). -/
theorem search_halts_tm0 {T : Type} [Primcodable T]
    {α : Type} [Primcodable α]
    (test : α → List T → Bool)
    (hc : Computable₂ test) :
    ∃ (Γ : Type) (_ : Inhabited Γ) (_ : Fintype Γ)
      (Λ : Type) (_ : Inhabited Λ)
      (M : TM0.Machine Γ Λ)
      (enc : List T → List Γ),
      ∀ w : List T,
        (∃ a : α, test a w = true) ↔ (TM0.eval M (enc w)).Dom := by
  obtain ⟨c, hc_code⟩ := search_is_partrec test hc
  obtain ⟨Γ₀, Λ₀, hΛ₀, hΓ₀, hΓ₀f, encode_input, M₀, hM₀⟩ := code_to_tm0 c
  exact ⟨Γ₀, hΓ₀, hΓ₀f, Λ₀, hΛ₀, M₀,
    fun w => encode_input (Encodable.encode w),
    fun w => by rw [hc_code, hM₀]⟩

/-! ### Main Compilation Theorem (PROVED) -/

/-- **Main Compilation Theorem** (PROVED, 0 sorry): If we can search over
a `Primcodable` domain with a `Computable₂` test, the resulting language
is TM-recognizable (with an internal `Fintype` tape alphabet).

This is the `is_TM_internal`-style result (without `Fintype` on states).
For the full `is_TM` result (with `Option T` tape alphabet), see
`is_TM_internal_to_TM` in `InternalTM.lean`. -/
theorem is_TM_of_searchable {T : Type} [Primcodable T]
    {α : Type} [Primcodable α]
    (test : α → List T → Bool)
    (hc : Computable₂ test)
    (L : Language T)
    (hL : L = { w | ∃ a : α, test a w = true }) :
    ∃ (Γ : Type) (_ : Inhabited Γ) (_ : Fintype Γ)
      (Λ : Type) (_ : Inhabited Λ)
      (M : TM0.Machine Γ Λ)
      (enc : List T → List Γ),
      ∀ w : List T,
        w ∈ L ↔ (TM0.eval M (enc w)).Dom := by
  obtain ⟨Γ, hΓ, hΓf, Λ, hΛ, M, enc, hM⟩ := search_halts_tm0 test hc
  exact ⟨Γ, hΓ, hΓf, Λ, hΛ, M, enc, fun w => by rw [hL]; exact hM w⟩

/-! ### Alphabet Simulation (separate concern) -/

/-- **Alphabet simulation**: TM0 over any `Fintype` alphabet can be
simulated by TM0 over `Option T`.

This is a standard result in TM theory involving block encoding of tape
symbols. It is separated from the core compilation theorem because it is
orthogonal to the search compilation logic.

Together with `search_halts_tm0`, this gives `is_TM` (TM0-recognizability
with `Option T` tape alphabet). -/
theorem tm0_alphabet_simulation {T : Type} [DecidableEq T] [Fintype T]
    [Primcodable T]
    {Γ : Type} [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
    [Primcodable Γ]
    {Λ : Type} [Inhabited Λ]
    (M : TM0.Machine Γ Λ)
    (encode_word : List T → List Γ)
    (henc : Computable encode_word) :
    ∃ (Λ' : Type) (_ : Inhabited Λ') (_ : Fintype Λ')
      (M' : TM0.Machine (Option T) Λ'),
      ∀ w : List T,
        (TM0.eval M (encode_word w)).Dom ↔
        (TM0.eval M' (w.map Option.some)).Dom := by
  sorry
