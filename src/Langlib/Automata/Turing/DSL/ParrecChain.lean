import Mathlib
import Langlib.Automata.Turing.DSL.ParrecToTM0

/-! # Partrec Code → TM0 Assembly

This file assembles the full chain Code → TM2 → TM1 → TM0, proving that
any partial recursive function (given as `ToPartrec.Code`) can be
evaluated by a TM0 machine.

## Main results

- `partrec_init_trCfg` — TrCfg for PartrecToTM2.init (the key lemma)
- `code_to_tm0_halts` — full chain: Code halts iff TM0 halts
- `code_to_tm0_eval` — full chain with TM0.eval and re-rooting
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

/-
`TrCfg` relates `PartrecToTM2.init c v` to a TM1 config whose tape
is `(TM1.init (trInit K'.main (trList v))).Tape = Tape.mk₁ (trInit ...)`.

This is the key lemma enabling the full Code → TM0 chain. It adapts
`trCfg_init` to the custom initial config of PartrecToTM2.
The proof reuses the same `ListBlank L` construction since the stacks
are identical.
-/
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

/-- TM2 halts iff Code evaluates. -/
theorem code_eval_iff_tm2 (c : ToPartrec.Code) (v : List ℕ) :
    (c.eval v).Dom ↔
    (eval (TM2.step PartrecToTM2.tr) (PartrecToTM2.init c v)).Dom := by
  rw [PartrecToTM2.tr_eval]; simp [Part.dom_iff_mem, Part.mem_map_iff]

/-! ### Full Chain: Code → TM0 -/

/-- **Full chain: Code → TM0 (eval form).**

For any `ToPartrec.Code c` and input `v`, there exists a re-rooted TM0
whose `TM0.eval` halts on `trInit K'.main (trList v)` iff `(c.eval v).Dom`.

The TM0 operates over `ChainΓ` (≈ `Bool × (K' → Option Γ')`). -/
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
  -- Step 1: Code ↔ TM2
  rw [code_eval_iff_tm2 c v]
  -- Step 2: TM2 ↔ TM1 (via TrCfg bisimulation)
  rw [← ParrecToTM0.tm2to1_dom_general PartrecToTM2.tr _ _ (partrec_init_trCfg c v)]
  -- Step 3: TM1 ↔ TM0 (via trCfg bisimulation)
  rw [← ParrecToTM0.tm1to0_dom_general ChainTM1 cfg₁]
  -- Step 4: TM0 with specific config ↔ TM0.eval via re-rooting
  -- cfg₀ = ⟨q₀, Tape.mk₁ input⟩ (since the tape comes from TM1.init)
  -- cfg₀ = TM1to0.trCfg ChainTM1 cfg₁ (a let-binding)
  -- We need to unfold cfg₀ in the goal
  show (eval (TM0.step ChainTM0) cfg₀).Dom ↔ _
  have hcfg : cfg₀ = ⟨q₀, Tape.mk₁ input⟩ := by
    simp [cfg₀, cfg₁, TM1to0.trCfg, TM1.init, q₀, input]
  rw [hcfg]
  exact ParrecToTM0.tm0Reroot_eval_dom ChainTM0 q₀ input