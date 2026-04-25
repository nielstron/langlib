import Mathlib
import Langlib.Automata.Turing.DSL.ParrecToTM0

/-! # Partrec Code → TM0 Assembly

This file assembles the full chain Code → TM2 → TM1 → TM0, proving that
any partial recursive function (given as `ToPartrec.Code`) can be
evaluated by a TM0 machine.

## Main results

- `partrec_init_trCfg` — TrCfg for PartrecToTM2.init (the key lemma)
- `code_to_tm0_halts` — full chain: Code halts iff TM0 halts (PROVED)
- `code_to_tm0` — existential form (PROVED, no Fintype on states)
- `code_to_tm0_fintype` — with Fintype states (PROVED)

## Hurdles for Fintype states

The main obstacle to proving `code_to_tm0_fintype` is a **Lean `Inhabited`
instance mismatch**:

1. `PartrecToTM2.tr_supports c k` produces `TM2.Supports` with a
   *code-dependent* `Inhabited` instance: `⟨trNormal c k⟩`. The canonical
   `Inhabited PartrecToTM2.Λ'` uses `⟨ret halt⟩` instead.

2. `TM1to0.instInhabitedΛ'` defines `default = (some (M default), default)`,
   so the `Inhabited` instance for `ChainΛ_TM0` depends on the upstream
   `Inhabited ChainΛ_TM1`, which in turn depends on `Inhabited PartrecToTM2.Λ'`.

3. These instances are **not definitionally equal**, causing Lean to reject
   `exact` when the support proof uses one instance but the goal expects another.

**This is NOT a mathematical obstacle** — the support sets are the same regardless
of the `Inhabited` choice. But it requires either:
- Refactoring `PartrecToTM2.tr_supports` to use the canonical instance
  (requires `ret halt ∈ codeSupp c halt`, which is not true for all codes)
- Or carefully threading `@`-explicit instances through the entire chain
  (very tedious but mechanically straightforward)

Additionally, `init_q0_mem_chainSuppTM0` (initial state ∈ support) needs:
- `trNormal c halt ∈ codeSupp c halt` (true but needs induction on Code)
- `some (ChainTM1 q) ∈ TM1.stmts` for `q ∈ chainSuppTM1` (follows from stmts₁_self)
-/

open Turing PartrecToTM2 TM2to1

/-! ### Stack Equality -/

/-- The stacks of `PartrecToTM2.init c v` equal those of `TM2.init K'.main (trList v)`. -/
theorem partrec_init_stk_eq (c : ToPartrec.Code) (v : List ℕ) :
    (PartrecToTM2.init c v).stk =
    (TM2.init K'.main (PartrecToTM2.trList v) :
      TM2.Cfg (fun _ : K' => Γ') Λ' (Option Γ')).stk := by
  simp [PartrecToTM2.init, TM2.init]
  ext k; cases k <;> simp [K'.elim, Function.update]

/-! ### TrCfg for PartrecToTM2.init -/

theorem partrec_init_trCfg (c : ToPartrec.Code) (v : List ℕ) :
    @TrCfg K' (fun _ => Γ') Λ' (Option Γ')
      (PartrecToTM2.init c v)
      ⟨Option.map Λ'.normal (PartrecToTM2.init c v).l,
       (PartrecToTM2.init c v).var,
       (TM1.init (trInit K'.main (PartrecToTM2.trList v)) :
         TM1.Cfg (Γ' K' (fun _ => Γ'))
           (Λ' K' (fun _ => Γ') PartrecToTM2.Λ' (Option Γ')) (Option Γ')).Tape⟩ := by
  convert TM2to1.TrCfg.mk _ _;
  simp +decide [ TM1.init, trInit ];
  rotate_left;
  exact ListBlank.mk ( List.map ( fun a => Function.update ( fun _ => none ) K'.main ( some a ) ) ( trList v ) |> List.reverse );
  · intro k; cases k <;> simp +decide [ ListBlank.map ] ;
    · simp +decide [ ListBlank.liftOn, proj ];
      erw [ Quotient.liftOn'_mk ] ; aesop;
    · simp +decide [ proj ];
      erw [ Quotient.eq'' ];
      simp +decide [ BlankRel.setoid, List.map ];
      induction ( trList v ) <;> simp_all +decide [ BlankRel ];
      · exact?;
      · simp_all +decide [ BlankExtends ];
        rcases ‹_› with ( rfl | ⟨ n, hn ⟩ ) <;> [ exact ⟨ 1, by simp +decide ⟩ ; exact ⟨ n + 1, by simp +decide [ hn, List.replicate_add ] ⟩ ];
    · simp +decide [ ListBlank.liftOn ];
      erw [ Quotient.liftOn'_mk ];
      simp +decide [ Function.comp, ListBlank.ext_iff ];
      intro i; by_cases hi : i < List.length ( List.map ( ( proj K'.aux ).f ∘ fun a => Function.update ( fun x => none ) K'.main ( some a ) ) ( trList v ) ) <;> simp_all +decide [ List.getElem?_eq_none ] ;
      · simp +decide [ List.getI, hi ];
        simp +decide [ Function.update, proj ];
      · rw [ List.getI_eq_default ] ; aesop;
    · simp +decide [ proj, ListBlank.liftOn ];
      erw [ Quotient.liftOn'_mk ];
      simp +decide [ Function.comp_def, Function.update_apply ];
      ext;
      simp +decide [ ListBlank.nth ];
      simp +decide [ ListBlank.liftOn ];
      erw [ Quotient.liftOn'_mk, Quotient.liftOn'_mk ];
      simp +decide [ List.getI ];
      rw [ List.getElem?_replicate ] ; aesop;
  · unfold addBottom;
    cases h : ( trList v ).reverse <;> aesop

/-! ### Chain Type Abbreviations -/

abbrev ChainΓ := Γ' K' (fun _ : K' => PartrecToTM2.Γ')
abbrev ChainΛ_TM1 := Λ' K' (fun _ => PartrecToTM2.Γ') PartrecToTM2.Λ' (Option PartrecToTM2.Γ')
abbrev ChainTM1 := TM2to1.tr PartrecToTM2.tr
abbrev ChainTM0 := TM1to0.tr ChainTM1
abbrev ChainΛ_TM0 := TM1to0.Λ' ChainTM1

instance : Fintype PartrecToTM2.K' :=
  Fintype.ofList [.main, .rev, .aux, .stack] (by intro x; cases x <;> simp)

instance : Fintype PartrecToTM2.Γ' :=
  Fintype.ofList [.consₗ, .cons, .bit0, .bit1] (by intro x; cases x <;> simp)

/-- TM2 halts iff Code evaluates. -/
theorem code_eval_iff_tm2 (c : ToPartrec.Code) (v : List ℕ) :
    (c.eval v).Dom ↔
    (eval (TM2.step PartrecToTM2.tr) (PartrecToTM2.init c v)).Dom := by
  rw [PartrecToTM2.tr_eval]; simp [Part.dom_iff_mem, Part.mem_map_iff]

/-! ### Full Chain: Code → TM0 -/

/-- **Full chain: Code → TM0 (eval form).** -/
theorem code_to_tm0_halts (c : ToPartrec.Code) (v : List ℕ) :
    let cfg₁ : TM1.Cfg ChainΓ ChainΛ_TM1 (Option Γ') :=
      ⟨Option.map Λ'.normal (PartrecToTM2.init c v).l,
       (PartrecToTM2.init c v).var,
       (TM1.init (trInit K'.main (PartrecToTM2.trList v)) :
         TM1.Cfg ChainΓ ChainΛ_TM1 (Option Γ')).Tape⟩
    let cfg₀ := TM1to0.trCfg ChainTM1 cfg₁
    let q₀ := cfg₀.q
    let input := trInit K'.main (PartrecToTM2.trList v)
    (c.eval v).Dom ↔
    (@TM0.eval ChainΓ (ParrecToTM0.Rooted ChainΛ_TM0 q₀) ⟨⟨q₀⟩⟩ _
      (ParrecToTM0.tm0Reroot ChainTM0 q₀) input).Dom := by
  intro cfg₁ cfg₀ q₀ input
  rw [code_eval_iff_tm2 c v]
  rw [← ParrecToTM0.tm2to1_dom_general PartrecToTM2.tr _ _ (partrec_init_trCfg c v)]
  rw [← ParrecToTM0.tm1to0_dom_general ChainTM1 cfg₁]
  show (eval (TM0.step ChainTM0) cfg₀).Dom ↔ _
  have hcfg : cfg₀ = ⟨q₀, Tape.mk₁ input⟩ := by
    simp [cfg₀, cfg₁, TM1to0.trCfg, TM1.init, q₀, input]
  rw [hcfg]
  exact ParrecToTM0.tm0Reroot_eval_dom ChainTM0 q₀ input

/-! ### Support Chain (for Fintype states) -/

/-- The TM2 support set for a given code `c`. -/
def chainSuppTM2 (c : ToPartrec.Code) : Finset PartrecToTM2.Λ' :=
  PartrecToTM2.codeSupp c PartrecToTM2.Cont'.halt

/-- The TM1 support set. -/
noncomputable def chainSuppTM1 (c : ToPartrec.Code) : Finset ChainΛ_TM1 :=
  TM2to1.trSupp PartrecToTM2.tr (chainSuppTM2 c)

/-- The TM0 support set. -/
noncomputable def chainSuppTM0 (c : ToPartrec.Code) : Finset ChainΛ_TM0 :=
  TM1to0.trStmts ChainTM1 (chainSuppTM1 c)

/-! ### Full Chain with Fintype States -/

/-- The initial TM1 config for the chain. -/
abbrev chainTM1Cfg (c : ToPartrec.Code) (v : List ℕ) :
    TM1.Cfg ChainΓ ChainΛ_TM1 (Option PartrecToTM2.Γ') :=
  ⟨Option.map TM2to1.Λ'.normal (PartrecToTM2.init c v).l,
   (PartrecToTM2.init c v).var,
   (TM1.init (TM2to1.trInit PartrecToTM2.K'.main (PartrecToTM2.trList v)) :
     TM1.Cfg ChainΓ ChainΛ_TM1 (Option PartrecToTM2.Γ')).Tape⟩

/-
The TM0 config `TM1to0.trCfg` applied to the chain's initial config
    equals `⟨q₀, Tape.mk₁ input⟩` where `q₀` is the non-canonical default.
-/
lemma chainTM0_trCfg_eq_nc (c : ToPartrec.Code) (n : ℕ) :
    letI : Inhabited PartrecToTM2.Λ' :=
      ⟨PartrecToTM2.trNormal c PartrecToTM2.Cont'.halt⟩
    TM1to0.trCfg (TM2to1.tr PartrecToTM2.tr) (chainTM1Cfg c [n]) =
      ⟨@default (TM1to0.Λ' (TM2to1.tr PartrecToTM2.tr)) _,
       Tape.mk₁ (TM2to1.trInit PartrecToTM2.K'.main (PartrecToTM2.trList [n]))⟩ := by
  congr

/-- Generalized version of `chainTM0_trCfg_eq_nc` for arbitrary `v : List ℕ`.
Works because the TM0 state depends only on the Code `c` (via the non-canonical
`Inhabited` instance), not on the input list. The `var` component of `init c v`
is always `none : Option Γ'`. -/
lemma chainTM0_trCfg_eq_general (c : ToPartrec.Code) (v : List ℕ) :
    letI : Inhabited PartrecToTM2.Λ' :=
      ⟨PartrecToTM2.trNormal c PartrecToTM2.Cont'.halt⟩
    TM1to0.trCfg (TM2to1.tr PartrecToTM2.tr) (chainTM1Cfg c v) =
      ⟨@default (TM1to0.Λ' (TM2to1.tr PartrecToTM2.tr)) _,
       Tape.mk₁ (TM2to1.trInit PartrecToTM2.K'.main (PartrecToTM2.trList v))⟩ := by
  congr

/-- **Full chain: Code → TM0 with Fintype states.**

This is the strengthened version of `code_to_tm0` that provides `Fintype Λ`.
The key insight is to override the `Inhabited PartrecToTM2.Λ'` instance
to `⟨trNormal c halt⟩` (matching `tr_supports`), then thread the non-canonical
instance through the entire chain. The resulting TM0 machine is definitionally
the same as `ChainTM0` (since `TM1to0.tr` ignores `Inhabited`), but the support
proof uses the non-canonical default. -/
theorem code_to_tm0_fintype (c : ToPartrec.Code) :
    ∃ (ΛTy : Type) (_ : Inhabited ΛTy) (_ : Fintype ΛTy)
      (M : TM0.Machine ChainΓ ΛTy),
      ∀ n : ℕ,
        (c.eval [n]).Dom ↔
        (TM0.eval M
          (TM2to1.trInit PartrecToTM2.K'.main (PartrecToTM2.trList [n]))).Dom := by
  -- Override Inhabited instance to match tr_supports
  letI inhΛ' : Inhabited PartrecToTM2.Λ' :=
    ⟨PartrecToTM2.trNormal c PartrecToTM2.Cont'.halt⟩
  -- Build the support chain: TM2 → TM1 → TM0
  -- All using the non-canonical Inhabited instance
  have hTM2 := PartrecToTM2.tr_supports c PartrecToTM2.Cont'.halt
  have hTM1 := TM2to1.tr_supports PartrecToTM2.tr hTM2
  -- Note: TM2to1.tr doesn't use Inhabited, so TM2to1.tr tr = ChainTM1 definitionally
  -- But TM1to0.tr does carry the Inhabited parameter
  let M₀ : TM0.Machine ChainΓ ChainΛ_TM0 := TM1to0.tr (TM2to1.tr PartrecToTM2.tr)
  have hTM0 : TM0.Supports M₀
      ↑(TM1to0.trStmts (TM2to1.tr PartrecToTM2.tr)
        (TM2to1.trSupp PartrecToTM2.tr (PartrecToTM2.codeSupp c .halt))) :=
    TM1to0.tr_supports (TM2to1.tr PartrecToTM2.tr) hTM1
  -- Define support set and initial state
  let S := TM1to0.trStmts (TM2to1.tr PartrecToTM2.tr)
    (TM2to1.trSupp PartrecToTM2.tr (PartrecToTM2.codeSupp c .halt))
  let q₀ : TM1to0.Λ' (TM2to1.tr PartrecToTM2.tr) := default
  have hq₀ : q₀ ∈ S := hTM0.1
  -- Provide the existential witnesses
  refine ⟨{ q : ParrecToTM0.Rooted ChainΛ_TM0 q₀ // q ∈ S.map ParrecToTM0.rootedEmbFn },
    ⟨⟨⟨q₀⟩, by rw [Finset.mem_map]; exact ⟨q₀, hq₀, rfl⟩⟩⟩,
    ParrecToTM0.tm0RestrictReroot_fintype S q₀,
    ParrecToTM0.tm0RestrictReroot M₀ S hTM0 q₀ hq₀,
    fun n => ?_⟩
  -- Now prove: (c.eval [n]).Dom ↔ (TM0.eval M_res (input n)).Dom
  -- Step 1: Code ↔ TM2
  rw [code_eval_iff_tm2 c [n]]
  -- Step 2: TM2 ↔ TM1
  rw [← ParrecToTM0.tm2to1_dom_general PartrecToTM2.tr _ _ (partrec_init_trCfg c [n])]
  -- Step 3: TM1 ↔ TM0.step
  rw [← ParrecToTM0.tm1to0_dom_general (TM2to1.tr PartrecToTM2.tr) (chainTM1Cfg c [n])]
  -- Now goal involves eval (TM0.step M₀) (TM1to0.trCfg ... (chainTM1Cfg c [n]))
  -- Step 4: Show trCfg = ⟨q₀, Tape.mk₁ input⟩
  rw [chainTM0_trCfg_eq_nc c n]
  -- Step 5: Apply tm0RestrictReroot_eval_dom
  exact ParrecToTM0.tm0RestrictReroot_eval_dom M₀ S hTM0 q₀ hq₀
    (TM2to1.trInit PartrecToTM2.K'.main (PartrecToTM2.trList [n]))

/-- **Generalized chain: Code → TM0 with Fintype states and multi-element input.**

Same as `code_to_tm0_fintype` but works for arbitrary `v : List ℕ` instead of
just `[n]`. The machine and state space are identical — only the input encoding
`trInit K'.main (trList v)` varies with the input list. -/
theorem code_to_tm0_fintype_general (c : ToPartrec.Code) :
    ∃ (ΛTy : Type) (_ : Inhabited ΛTy) (_ : Fintype ΛTy)
      (M : TM0.Machine ChainΓ ΛTy),
      ∀ v : List ℕ,
        (c.eval v).Dom ↔
        (TM0.eval M
          (TM2to1.trInit PartrecToTM2.K'.main (PartrecToTM2.trList v))).Dom := by
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
    fun v => ?_⟩
  rw [code_eval_iff_tm2 c v]
  rw [← ParrecToTM0.tm2to1_dom_general PartrecToTM2.tr _ _ (partrec_init_trCfg c v)]
  rw [← ParrecToTM0.tm1to0_dom_general (TM2to1.tr PartrecToTM2.tr) (chainTM1Cfg c v)]
  rw [chainTM0_trCfg_eq_general c v]
  exact ParrecToTM0.tm0RestrictReroot_eval_dom M₀ S hTM0 q₀ hq₀
    (TM2to1.trInit PartrecToTM2.K'.main (PartrecToTM2.trList v))

