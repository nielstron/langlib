module

public import Langlib.Automata.LinearBounded.Equivalence.CSGToLBA.Construction
import Mathlib.Tactic
@[expose]
public section

/-!
# CSG → LBA (Kuroda): completeness

This file proves the **completeness** half: a derivation `[S] ⇒* w` of the grammar is replayed
in reverse by an accepting run of `kMachine g₀` (`kMachine_complete`).

The core is `applyRule_pass_gen`, a single backward rule-application pass that rewrites one
`output`-occurrence on the work track to the rule's input pattern `patList`, skipping blanks.
The `Complete` section then repositions the head freely (`sim_reaches`), locates the rewrite
window (`list_split_filterMap`), chains one pass per derivation step (`step_back`, `derive_back`)
and finishes with the accept check.
-/

namespace KurodaConstruction

open List Relation Classical

noncomputable section

variable {T : Type}
/-! ### `applyRule` single-pass steps -/
section Apply

variable [Fintype T] [DecidableEq T] (g₀ : grammar T) [Fintype g₀.nt] [DecidableEq g₀.nt]

/-- Every element of a `ℕ`-list is `≤` its `foldr max 0`. -/
lemma le_foldr_max (L : List ℕ) (x : ℕ) (hx : x ∈ L) : x ≤ L.foldr max 0 := by
  induction L with
  | nil => simp at hx
  | cons a t ih =>
      simp only [List.foldr_cons]
      rcases List.mem_cons.mp hx with h | h
      · subst h; exact le_max_left _ _
      · exact le_trans (ih h) (le_max_right _ _)

/-- Each rule's output length is within `ruleBound`. -/
lemma output_length_le_ruleBound (ri : Fin g₀.rules.length) :
    (g₀.rules[ri]).output_string.length ≤ ruleBound g₀ := by
  apply le_foldr_max
  exact List.mem_map.mpr ⟨g₀.rules[ri], List.getElem_mem _, rfl⟩

/-- From `sim`, begin applying rule `ri` at the current cell (echo, stay). -/
lemma kStep_sim_applyRule {n : ℕ} (c : Fin (n + 1) → KCell g₀) (i : Fin (n + 1))
    (ri : Fin g₀.rules.length) (l r : Bool) (ws : KWork g₀) (hc : c i = some (Sum.inr (l, r, ws))) :
    LBA.Step (kMachine g₀) ⟨KState.sim, ⟨c, i⟩⟩ ⟨KState.applyRule ri 0, ⟨c, i⟩⟩ := by
  refine kStep_echo_stay g₀ (st' := KState.applyRule ri 0) ?_
  rw [hc]
  simp only [kTransition, Set.mem_union, Set.mem_setOf_eq]
  exact Or.inr ⟨ri, rfl⟩

/-- Skip a blank during the rule-application pass (echo, move right, keep the match position). -/
lemma kStep_applyRule_blank {n : ℕ} (c : Fin (n + 1) → KCell g₀) (i : Fin (n + 1))
    (ri : Fin g₀.rules.length) (k : Fin (ruleBound g₀ + 1)) (l r : Bool) (hlt : i.val < n)
    (hc : c i = some (Sum.inr (l, r, none))) (hr : r = false) :
    LBA.Step (kMachine g₀) ⟨KState.applyRule ri k, ⟨c, i⟩⟩
      ⟨KState.applyRule ri k, ⟨c, ⟨i.val + 1, by omega⟩⟩⟩ := by
  subst hr
  refine kStep_echo_right g₀ hlt (st' := KState.applyRule ri k) ?_
  rw [hc]; simp [kTransition]

/-- Match the `k`-th output symbol and write the replacement, continuing the pass (`k+1 < |out|`). -/
lemma kStep_applyRule_continue {n : ℕ} (c : Fin (n + 1) → KCell g₀) (i : Fin (n + 1))
    (ri : Fin g₀.rules.length) (k : Fin (ruleBound g₀ + 1)) (l r : Bool) (s : symbol T g₀.nt)
    (hlt : i.val < n) (hc : c i = some (Sum.inr (l, r, some s)))
    (hm : (g₀.rules[ri]).output_string[k.val]? = some s)
    (hk : k.val + 1 < (g₀.rules[ri]).output_string.length) (hr : r = false) :
    LBA.Step (kMachine g₀) ⟨KState.applyRule ri k, ⟨c, i⟩⟩
      ⟨KState.applyRule ri (k + 1),
        ⟨Function.update c i (some (Sum.inr (l, r, (patList g₀ g₀.rules[ri])[k.val]?))),
          ⟨i.val + 1, by omega⟩⟩⟩ := by
  subst hr
  refine ⟨KState.applyRule ri (k + 1),
    some (Sum.inr (l, false, (patList g₀ g₀.rules[ri])[k.val]?)), DLBA.Dir.right, ?_, ?_⟩
  · show (KState.applyRule ri (k + 1), some (Sum.inr (l, false, (patList g₀ g₀.rules[ri])[k.val]?)),
        DLBA.Dir.right) ∈ kTransition g₀ (KState.applyRule ri k) (c i)
    rw [hc]; simp only [kTransition]; rw [if_pos hm, if_pos hk]; simp
  · simp only [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead, dif_pos hlt]

/-- Match the last output symbol (`k+1 = |out|`); the replacement is written and the pass ends
(return to `sim`). -/
lemma kStep_applyRule_last {n : ℕ} (c : Fin (n + 1) → KCell g₀) (i : Fin (n + 1))
    (ri : Fin g₀.rules.length) (k : Fin (ruleBound g₀ + 1)) (l r : Bool) (s : symbol T g₀.nt)
    (hlt : i.val < n) (hc : c i = some (Sum.inr (l, r, some s)))
    (hm : (g₀.rules[ri]).output_string[k.val]? = some s)
    (hk : k.val + 1 = (g₀.rules[ri]).output_string.length) :
    LBA.Step (kMachine g₀) ⟨KState.applyRule ri k, ⟨c, i⟩⟩
      ⟨KState.sim,
        ⟨Function.update c i (some (Sum.inr (l, r, (patList g₀ g₀.rules[ri])[k.val]?))),
          ⟨i.val + 1, by omega⟩⟩⟩ := by
  have hk' : ¬ k.val + 1 < (g₀.rules[ri]).output_string.length := by omega
  refine ⟨KState.sim,
    some (Sum.inr (l, r, (patList g₀ g₀.rules[ri])[k.val]?)), DLBA.Dir.right, ?_, ?_⟩
  · show (KState.sim, some (Sum.inr (l, r, (patList g₀ g₀.rules[ri])[k.val]?)),
        DLBA.Dir.right) ∈ kTransition g₀ (KState.applyRule ri k) (c i)
    rw [hc]; simp only [kTransition]; rw [if_pos hm, if_neg hk', if_pos hk]; rfl
  · simp only [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead, dif_pos hlt]

/-- Match the last output symbol when the cell is the rightmost (`i.val = n`); moving right
clamps, so the head stays at `n`. -/
lemma kStep_applyRule_last_clamp {n : ℕ} (c : Fin (n + 1) → KCell g₀) (i : Fin (n + 1))
    (ri : Fin g₀.rules.length) (k : Fin (ruleBound g₀ + 1)) (l r : Bool) (s : symbol T g₀.nt)
    (hin : i.val = n) (hc : c i = some (Sum.inr (l, r, some s)))
    (hm : (g₀.rules[ri]).output_string[k.val]? = some s)
    (hk : k.val + 1 = (g₀.rules[ri]).output_string.length) :
    LBA.Step (kMachine g₀) ⟨KState.applyRule ri k, ⟨c, i⟩⟩
      ⟨KState.sim,
        ⟨Function.update c i (some (Sum.inr (l, r, (patList g₀ g₀.rules[ri])[k.val]?))), i⟩⟩ := by
  have hk' : ¬ k.val + 1 < (g₀.rules[ri]).output_string.length := by omega
  have hmv : ¬ i.val < n := by omega
  refine ⟨KState.sim,
    some (Sum.inr (l, r, (patList g₀ g₀.rules[ri])[k.val]?)), DLBA.Dir.right, ?_, ?_⟩
  · show (KState.sim, some (Sum.inr (l, r, (patList g₀ g₀.rules[ri])[k.val]?)),
        DLBA.Dir.right) ∈ kTransition g₀ (KState.applyRule ri k) (c i)
    rw [hc]; simp only [kTransition]; rw [if_pos hm, if_neg hk', if_pos hk]; rfl
  · simp only [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead, dif_neg hmv]

/-- **The rule-application pass** (contiguous window). From `applyRule ri k` at cell `start+k`,
where the window holds `output_string[k..]`, scan to the end writing the replacement, reaching
`sim` with the work function updated on `[start+k, start+q)` to `patList[·]?`. -/
lemma applyRule_pass {n : ℕ} (ri : Fin g₀.rules.length)
    (start : ℕ) (hq : start + (g₀.rules[ri]).output_string.length ≤ n + 1) :
    ∀ d : ℕ, ∀ (W : Fin (n + 1) → KWork g₀) (k : Fin (ruleBound g₀ + 1))
      (hk : k.val < (g₀.rules[ri]).output_string.length)
      (_ : (g₀.rules[ri]).output_string.length - 1 - k.val = d)
      (_ : ∀ j, k.val ≤ j → ∀ (hj : j < (g₀.rules[ri]).output_string.length),
        W ⟨start + j, by omega⟩ = some ((g₀.rules[ri]).output_string[j])),
      ∃ h : Fin (n + 1), LBA.Reaches (kMachine g₀)
        ⟨KState.applyRule ri k, ⟨fun p => mkCell g₀ p (W p), ⟨start + k.val, by omega⟩⟩⟩
        ⟨KState.sim, ⟨fun p => mkCell g₀ p
          (if start + k.val ≤ p.val ∧ p.val < start + (g₀.rules[ri]).output_string.length
            then (patList g₀ g₀.rules[ri])[p.val - start]? else W p), h⟩⟩ := by
  intro d
  induction d with
  | zero =>
      intro W k hk hd hmatch
      have hkq : k.val + 1 = (g₀.rules[ri]).output_string.length := by omega
      have hW : W ⟨start + k.val, by omega⟩ = some ((g₀.rules[ri]).output_string[k.val]) :=
        hmatch k.val (le_refl _) hk
      have hc : (fun p => mkCell g₀ p (W p)) ⟨start + k.val, by omega⟩
          = some (Sum.inr (decide ((start + k.val) = 0), decide ((start + k.val) = n),
              some ((g₀.rules[ri]).output_string[k.val]))) := by
        simp only [mkCell]; rw [hW]
      have hm : (g₀.rules[ri]).output_string[k.val]? = some ((g₀.rules[ri]).output_string[k.val]) :=
        List.getElem?_eq_getElem hk
      have hWset : ∀ p : Fin (n + 1),
          (if start + k.val ≤ p.val ∧ p.val < start + (g₀.rules[ri]).output_string.length
            then (patList g₀ g₀.rules[ri])[p.val - start]? else W p)
          = Function.update W (⟨start + k.val, by omega⟩ : Fin (n + 1))
              ((patList g₀ g₀.rules[ri])[k.val]?) p := by
        intro p
        rw [Function.update_apply]
        by_cases hp : p.val = start + k.val
        · rw [if_pos (Fin.ext hp), if_pos ⟨by omega, by omega⟩]
          congr 1; omega
        · rw [if_neg (fun he => hp (congrArg Fin.val he)), if_neg (by rintro ⟨h1, h2⟩; omega)]
      have htape : (fun p => mkCell g₀ p
            (if start + k.val ≤ p.val ∧ p.val < start + (g₀.rules[ri]).output_string.length
              then (patList g₀ g₀.rules[ri])[p.val - start]? else W p))
          = Function.update (fun p => mkCell g₀ p (W p)) (⟨start + k.val, by omega⟩ : Fin (n + 1))
              (mkCell g₀ (⟨start + k.val, by omega⟩ : Fin (n + 1))
                ((patList g₀ g₀.rules[ri])[k.val]?)) := by
        conv_lhs => ext p; rw [hWset p]
        exact (update_mkCell g₀ W ⟨start + k.val, by omega⟩
          ((patList g₀ g₀.rules[ri])[k.val]?)).symm
      by_cases hlt : start + k.val < n
      · refine ⟨⟨start + k.val + 1, by omega⟩, Relation.ReflTransGen.single ?_⟩
        rw [htape]
        exact kStep_applyRule_last g₀ (fun p => mkCell g₀ p (W p)) ⟨start + k.val, by omega⟩
          ri k _ _ _ hlt hc hm hkq
      · refine ⟨⟨start + k.val, by omega⟩, Relation.ReflTransGen.single ?_⟩
        rw [htape]
        exact kStep_applyRule_last_clamp g₀ (fun p => mkCell g₀ p (W p)) ⟨start + k.val, by omega⟩
          ri k _ _ _ (by show start + k.val = n; omega) hc hm hkq
  | succ e ih =>
      intro W k hk hd hmatch
      have hltq : k.val + 1 < (g₀.rules[ri]).output_string.length := by omega
      have hkrb : k.val + 1 < ruleBound g₀ + 1 := by
        have := output_length_le_ruleBound g₀ ri; omega
      have hW : W ⟨start + k.val, by omega⟩ = some ((g₀.rules[ri]).output_string[k.val]) :=
        hmatch k.val (le_refl _) hk
      have hc : (fun p => mkCell g₀ p (W p)) ⟨start + k.val, by omega⟩
          = some (Sum.inr (decide ((start + k.val) = 0), decide ((start + k.val) = n),
              some ((g₀.rules[ri]).output_string[k.val]))) := by
        simp only [mkCell]; rw [hW]
      have hm : (g₀.rules[ri]).output_string[k.val]? = some ((g₀.rules[ri]).output_string[k.val]) :=
        List.getElem?_eq_getElem hk
      have hlt : start + k.val < n := by omega
      have hval : ((k + 1 : Fin (ruleBound g₀ + 1))).val = k.val + 1 :=
        Fin.val_add_one_of_lt' (by omega)
      have hstep : LBA.Step (kMachine g₀)
          ⟨KState.applyRule ri k, ⟨fun p => mkCell g₀ p (W p), ⟨start + k.val, by omega⟩⟩⟩
          ⟨KState.applyRule ri (k + 1), ⟨fun p => mkCell g₀ p
            (Function.update W (⟨start + k.val, by omega⟩ : Fin (n + 1))
              ((patList g₀ g₀.rules[ri])[k.val]?) p), ⟨start + k.val + 1, by omega⟩⟩⟩ := by
        have hcont := kStep_applyRule_continue g₀ (fun p => mkCell g₀ p (W p))
          ⟨start + k.val, by omega⟩ ri k _ _ _ hlt hc hm hltq (by simp; omega)
        rw [show (fun p => mkCell g₀ p (Function.update W (⟨start + k.val, by omega⟩ : Fin (n + 1))
                ((patList g₀ g₀.rules[ri])[k.val]?) p))
              = Function.update (fun p => mkCell g₀ p (W p)) (⟨start + k.val, by omega⟩ : Fin (n + 1))
                  (mkCell g₀ (⟨start + k.val, by omega⟩ : Fin (n + 1))
                    ((patList g₀ g₀.rules[ri])[k.val]?))
            from (update_mkCell g₀ W ⟨start + k.val, by omega⟩
              ((patList g₀ g₀.rules[ri])[k.val]?)).symm]
        exact hcont
      have hmatch1 : ∀ j, (k + 1).val ≤ j → ∀ (hj : j < (g₀.rules[ri]).output_string.length),
          (Function.update W (⟨start + k.val, by omega⟩ : Fin (n + 1))
            ((patList g₀ g₀.rules[ri])[k.val]?)) ⟨start + j, by omega⟩
            = some ((g₀.rules[ri]).output_string[j]) := by
        intro j hj1 hj
        rw [hval] at hj1
        rw [Function.update_of_ne (fun he => by have := congrArg Fin.val he; simp only [] at this; omega)]
        exact hmatch j (by omega) hj
      obtain ⟨h, hreach⟩ := ih (Function.update W (⟨start + k.val, by omega⟩ : Fin (n + 1))
        ((patList g₀ g₀.rules[ri])[k.val]?)) (k + 1) (by rw [hval]; omega) (by rw [hval]; omega)
        hmatch1
      refine ⟨h, Relation.ReflTransGen.head hstep ?_⟩
      simp only [hval] at hreach
      have hWeq : (fun p => mkCell g₀ p
            (if start + (k.val + 1) ≤ p.val ∧ p.val < start + (g₀.rules[ri]).output_string.length
              then (patList g₀ g₀.rules[ri])[p.val - start]?
              else Function.update W (⟨start + k.val, by omega⟩ : Fin (n + 1))
                ((patList g₀ g₀.rules[ri])[k.val]?) p))
          = (fun p => mkCell g₀ p
            (if start + k.val ≤ p.val ∧ p.val < start + (g₀.rules[ri]).output_string.length
              then (patList g₀ g₀.rules[ri])[p.val - start]? else W p)) := by
        funext p
        congr 1
        by_cases hp0 : p.val = start + k.val
        · rw [if_neg (by omega), if_pos ⟨by omega, by omega⟩,
            Function.update_apply, if_pos (Fin.ext hp0)]
          congr 1; omega
        · by_cases hp1 : start + (k.val + 1) ≤ p.val ∧
              p.val < start + (g₀.rules[ri]).output_string.length
          · rw [if_pos hp1, if_pos ⟨by omega, hp1.2⟩]
          · rw [if_neg hp1, if_neg (by rintro ⟨h1, h2⟩; omega),
              Function.update_of_ne (fun he => hp0 (congrArg Fin.val he))]
      exact (congrArg (LBA.Reaches (kMachine g₀) _) (cfg_eq g₀ rfl hWeq rfl)).mp hreach

/-- **The general rule-application pass** (skips interspersed blanks). From `applyRule ri k` at
cell `pos`, where the non-blank cells from `pos` begin with `output_string[k..]` followed by `v`,
scan right (skipping blanks, matching each output symbol and writing the replacement) and reach
`sim` with the work track's non-blank tail now `patList[k..] ++ v`, leaving cells `< pos` fixed. -/
lemma applyRule_pass_gen {n : ℕ} (ri : Fin g₀.rules.length) (v : List (symbol T g₀.nt))
    (hpat : (patList g₀ g₀.rules[ri]).length ≤ (g₀.rules[ri]).output_string.length) :
    ∀ d : ℕ, ∀ (W : Fin (n + 1) → KWork g₀) (pos : ℕ) (hpn : pos < n + 1)
      (k : Fin (ruleBound g₀ + 1)) (hk : k.val < (g₀.rules[ri]).output_string.length)
      (_ : n - pos = d)
      (_ : ((List.ofFn W).drop pos).filterMap id
            = (g₀.rules[ri]).output_string.drop k.val ++ v),
      ∃ (W' : Fin (n + 1) → KWork g₀) (h : Fin (n + 1)),
        LBA.Reaches (kMachine g₀)
          ⟨KState.applyRule ri k, ⟨fun p => mkCell g₀ p (W p), ⟨pos, hpn⟩⟩⟩
          ⟨KState.sim, ⟨fun p => mkCell g₀ p (W' p), h⟩⟩
        ∧ (∀ p : Fin (n + 1), p.val < pos → W' p = W p)
        ∧ ((List.ofFn W').drop pos).filterMap id
            = (patList g₀ g₀.rules[ri]).drop k.val ++ v := by
  intro d
  induction d with
  | zero =>
      intro W pos hpn k hk hd hfm
      have hpos : pos = n := by omega
      have hdropn : (List.ofFn W).drop pos = [W ⟨pos, hpn⟩] := by
        rw [List.drop_eq_getElem_cons (by rw [List.length_ofFn]; exact hpn), List.getElem_ofFn,
          List.drop_eq_nil_of_le (by rw [List.length_ofFn]; omega)]
      rw [hdropn] at hfm
      rcases hw : W ⟨pos, hpn⟩ with _ | s
      · rw [hw] at hfm; simp only [List.filterMap_cons, id, List.filterMap_nil] at hfm
        have hz : ((g₀.rules[ri]).output_string.drop k.val).length = 0 := by
          have := congrArg List.length hfm
          simp only [List.length_nil, List.length_append] at this; omega
        rw [List.length_drop] at hz; omega
      · rw [hw] at hfm; simp only [List.filterMap_cons, id, List.filterMap_nil] at hfm
        have hlen : 1 = (g₀.rules[ri]).output_string.length - k.val + v.length := by
          have := congrArg List.length hfm
          simp only [List.length_cons, List.length_nil, List.length_append, List.length_drop] at this
          omega
        have hkq : k.val + 1 = (g₀.rules[ri]).output_string.length := by omega
        have hv : v = [] := by
          have : v.length = 0 := by omega
          exact List.length_eq_zero_iff.mp this
        subst hv
        have hm : (g₀.rules[ri]).output_string[k.val]? = some s := by
          have hds : (g₀.rules[ri]).output_string.drop k.val = [s] := by
            rw [← List.append_nil ((g₀.rules[ri]).output_string.drop k.val)]; exact hfm.symm
          have hcons : (g₀.rules[ri]).output_string[k.val]
              :: (g₀.rules[ri]).output_string.drop (k.val + 1) = [s] :=
            (List.drop_eq_getElem_cons hk).symm.trans hds
          rw [List.getElem?_eq_getElem hk]
          simp only [List.cons.injEq] at hcons
          rw [hcons.1]
        have hc : (fun p => mkCell g₀ p (W p)) ⟨pos, hpn⟩
            = some (Sum.inr (decide (pos = 0), decide (pos = n), some s)) := by
          simp only [mkCell]; rw [hw]
        refine ⟨Function.update W ⟨pos, hpn⟩ ((patList g₀ g₀.rules[ri])[k.val]?), ⟨pos, hpn⟩,
          Relation.ReflTransGen.single ?_, ?_, ?_⟩
        · have hstep := kStep_applyRule_last_clamp g₀ (fun p => mkCell g₀ p (W p)) ⟨pos, hpn⟩
            ri k _ _ s hpos hc hm hkq
          rw [show (fun p => mkCell g₀ p (Function.update W ⟨pos, hpn⟩
                ((patList g₀ g₀.rules[ri])[k.val]?) p))
              = Function.update (fun p => mkCell g₀ p (W p)) (⟨pos, hpn⟩ : Fin (n + 1))
                  (mkCell g₀ (⟨pos, hpn⟩ : Fin (n + 1)) ((patList g₀ g₀.rules[ri])[k.val]?))
              from (update_mkCell g₀ W ⟨pos, hpn⟩ ((patList g₀ g₀.rules[ri])[k.val]?)).symm]
          exact hstep
        · intro p hp; rw [Function.update_of_ne (fun he => by rw [he] at hp; simp at hp)]
        · rw [ofFn_update]
          rw [show (((List.ofFn W).set (⟨pos, hpn⟩ : Fin (n + 1)).val
                ((patList g₀ g₀.rules[ri])[k.val]?)).drop pos)
              = [((patList g₀ g₀.rules[ri])[k.val]?)] from by
            rw [show (⟨pos, hpn⟩ : Fin (n + 1)).val = pos from rfl,
              List.drop_eq_getElem_cons (by simpa using hpn),
              List.getElem_set_self,
              List.drop_eq_nil_of_le (by simp; omega)]]
          rw [List.append_nil]
          have h0 := cons_getElem?_filterMap_drop (patList g₀ g₀.rules[ri]) k.val
          rwa [List.drop_eq_nil_of_le (show (patList g₀ g₀.rules[ri]).length ≤ k.val + 1 by omega),
            List.append_nil] at h0
  | succ e ih =>
      intro W pos hpn k hk hd hfm
      have hlt : pos < n := by omega
      rcases hw : W ⟨pos, hpn⟩ with _ | s
      · -- blank: skip
        have hfm' : ((List.ofFn W).drop (pos + 1)).filterMap id
            = (g₀.rules[ri]).output_string.drop k.val ++ v := by
          rw [← drop_filterMap_blank g₀ W ⟨pos, hpn⟩ hw]; exact hfm
        obtain ⟨W', h, hreach, hpre, hsuf⟩ := ih W (pos + 1) (by omega) k hk (by omega) hfm'
        refine ⟨W', h, ?_, ?_, ?_⟩
        · exact Relation.ReflTransGen.head
            (kStep_applyRule_blank g₀ (fun p => mkCell g₀ p (W p)) ⟨pos, hpn⟩ ri k _ _ hlt
              (by simp only [mkCell]; rw [hw]) (by simp; omega)) hreach
        · intro p hp; exact hpre p (by omega)
        · rw [show (List.ofFn W').drop pos = W' ⟨pos, hpn⟩ :: (List.ofFn W').drop (pos + 1) from by
            rw [List.drop_eq_getElem_cons (by rw [List.length_ofFn]; exact hpn), List.getElem_ofFn]]
          rw [hpre ⟨pos, hpn⟩ (Nat.lt_succ_self pos), hw]
          simp only [List.filterMap_cons, id]
          exact hsuf
      · -- symbol: match and write
        have hds := drop_filterMap_some g₀ W ⟨pos, hpn⟩ s hw
        rw [hfm] at hds
        -- hds : output.drop k.val ++ v = s :: ((ofFn W).drop (pos+1)).filterMap id
        have hsk : (g₀.rules[ri]).output_string[k.val] = s ∧
            ((List.ofFn W).drop (pos + 1)).filterMap id
              = (g₀.rules[ri]).output_string.drop (k.val + 1) ++ v := by
          rw [show (g₀.rules[ri]).output_string.drop k.val
                = (g₀.rules[ri]).output_string[k.val] :: (g₀.rules[ri]).output_string.drop (k.val + 1)
              from List.drop_eq_getElem_cons hk] at hds
          simp only [List.cons_append, List.cons.injEq] at hds
          exact ⟨hds.1, hds.2.symm⟩
        have hm : (g₀.rules[ri]).output_string[k.val]? = some s := by
          rw [List.getElem?_eq_getElem hk, hsk.1]
        have hc : (fun p => mkCell g₀ p (W p)) ⟨pos, hpn⟩
            = some (Sum.inr (decide (pos = 0), decide (pos = n), some s)) := by
          simp only [mkCell]; rw [hw]
        set W₁ := Function.update W (⟨pos, hpn⟩ : Fin (n + 1)) ((patList g₀ g₀.rules[ri])[k.val]?)
          with hW₁
        have hbridge : (fun p => mkCell g₀ p (W₁ p))
            = Function.update (fun p => mkCell g₀ p (W p)) (⟨pos, hpn⟩ : Fin (n + 1))
                (mkCell g₀ (⟨pos, hpn⟩ : Fin (n + 1)) ((patList g₀ g₀.rules[ri])[k.val]?)) := by
          rw [hW₁]; exact (update_mkCell g₀ W ⟨pos, hpn⟩ ((patList g₀ g₀.rules[ri])[k.val]?)).symm
        have hfm1 : ((List.ofFn W₁).drop (pos + 1)).filterMap id
            = (g₀.rules[ri]).output_string.drop (k.val + 1) ++ v := by
          rw [show (List.ofFn W₁).drop (pos + 1) = (List.ofFn W).drop (pos + 1) from by
            rw [ofFn_update, show (⟨pos, hpn⟩ : Fin (n + 1)).val = pos from rfl]
            apply List.ext_getElem?
            intro j
            rw [List.getElem?_drop, List.getElem?_drop, List.getElem?_set_ne (by omega)]]
          exact hsk.2
        have hW1pos : W₁ ⟨pos, hpn⟩ = (patList g₀ g₀.rules[ri])[k.val]? := by
          rw [hW₁, Function.update_self]
        by_cases hkq : k.val + 1 < (g₀.rules[ri]).output_string.length
        · have hval : ((k + 1 : Fin (ruleBound g₀ + 1))).val = k.val + 1 := by
            apply Fin.val_add_one_of_lt'
            have := output_length_le_ruleBound g₀ ri; omega
          obtain ⟨W', h, hreach, hpre, hsuf⟩ :=
            ih W₁ (pos + 1) (by omega) (k + 1) (by rw [hval]; omega) (by omega)
              (by rw [hval]; exact hfm1)
          refine ⟨W', h, ?_, ?_, ?_⟩
          · refine Relation.ReflTransGen.head ?_ hreach
            have hstep := kStep_applyRule_continue g₀ (fun p => mkCell g₀ p (W p)) ⟨pos, hpn⟩
              ri k _ _ s hlt hc hm hkq (by simp; omega)
            rw [hbridge]; exact hstep
          · intro p hp
            rw [hpre p (by omega), hW₁, Function.update_of_ne (fun he => by rw [he] at hp; simp at hp)]
          · rw [show (List.ofFn W').drop pos = W' ⟨pos, hpn⟩ :: (List.ofFn W').drop (pos + 1) from by
              rw [List.drop_eq_getElem_cons (by rw [List.length_ofFn]; exact hpn), List.getElem_ofFn]]
            rw [hpre ⟨pos, hpn⟩ (Nat.lt_succ_self pos), hW1pos]
            rw [hval] at hsuf
            rw [← List.singleton_append, List.filterMap_append, hsuf, ← List.append_assoc,
              cons_getElem?_filterMap_drop]
        · have hkq' : k.val + 1 = (g₀.rules[ri]).output_string.length := by omega
          refine ⟨W₁, ⟨pos + 1, by omega⟩, ?_, ?_, ?_⟩
          · have hstep := kStep_applyRule_last g₀ (fun p => mkCell g₀ p (W p)) ⟨pos, hpn⟩
              ri k _ _ s hlt hc hm hkq'
            rw [hbridge]; exact Relation.ReflTransGen.single hstep
          · intro p hp
            rw [hW₁, Function.update_of_ne (fun he => by rw [he] at hp; simp at hp)]
          · rw [show (List.ofFn W₁).drop pos = W₁ ⟨pos, hpn⟩ :: (List.ofFn W₁).drop (pos + 1) from by
              rw [List.drop_eq_getElem_cons (by rw [List.length_ofFn]; exact hpn), List.getElem_ofFn]]
            rw [hW1pos, ← List.singleton_append, List.filterMap_append, hfm1,
              List.drop_eq_nil_of_le (show (g₀.rules[ri]).output_string.length ≤ k.val + 1 by omega),
              List.nil_append]
            have h0 := cons_getElem?_filterMap_drop (patList g₀ g₀.rules[ri]) k.val
            rw [List.drop_eq_nil_of_le (show (patList g₀ g₀.rules[ri]).length ≤ k.val + 1 by omega),
              List.append_nil] at h0
            rw [h0]

end Apply

/-! ### Replaying a derivation backwards (completeness) -/
section Complete

variable [Fintype T] [DecidableEq T] (g₀ : grammar T) [Fintype g₀.nt] [DecidableEq g₀.nt]

/-- In `sim`, the head may move one cell right (the tape is unchanged). -/
lemma kStep_sim_right {n : ℕ} (W : Fin (n + 1) → KWork g₀) (i : Fin (n + 1)) (hlt : i.val < n) :
    LBA.Step (kMachine g₀) ⟨KState.sim, ⟨fun k => mkCell g₀ k (W k), i⟩⟩
      ⟨KState.sim, ⟨fun k => mkCell g₀ k (W k), ⟨i.val + 1, by omega⟩⟩⟩ := by
  refine kStep_echo_right g₀ hlt (st' := KState.sim) ?_
  simp only [mkCell]; simp [kTransition]

/-- In `sim`, the head may move one cell left (the tape is unchanged). -/
lemma kStep_sim_left {n : ℕ} (W : Fin (n + 1) → KWork g₀) (i : Fin (n + 1)) (hpos : 0 < i.val) :
    LBA.Step (kMachine g₀) ⟨KState.sim, ⟨fun k => mkCell g₀ k (W k), i⟩⟩
      ⟨KState.sim, ⟨fun k => mkCell g₀ k (W k), ⟨i.val - 1, by omega⟩⟩⟩ := by
  refine kStep_echo_left g₀ hpos (st' := KState.sim) ?_
  simp only [mkCell]; simp [kTransition]

/-- From `sim` at any cell, reach `sim` at the left end (cell 0). -/
lemma sim_reaches_zero {n : ℕ} (W : Fin (n + 1) → KWork g₀) (i : Fin (n + 1)) :
    LBA.Reaches (kMachine g₀) ⟨KState.sim, ⟨fun k => mkCell g₀ k (W k), i⟩⟩
      ⟨KState.sim, ⟨fun k => mkCell g₀ k (W k), 0⟩⟩ := by
  suffices H : ∀ m, ∀ i : Fin (n + 1), i.val = m →
      LBA.Reaches (kMachine g₀) ⟨KState.sim, ⟨fun k => mkCell g₀ k (W k), i⟩⟩
        ⟨KState.sim, ⟨fun k => mkCell g₀ k (W k), 0⟩⟩ from H i.val i rfl
  intro m
  induction m with
  | zero => intro i hi; obtain rfl : i = 0 := Fin.ext (by simpa using hi); exact .refl
  | succ k ih =>
      intro i hi
      have hpos : 0 < i.val := by omega
      exact Relation.ReflTransGen.head (kStep_sim_left g₀ W i hpos)
        (ih ⟨i.val - 1, by omega⟩ (by show i.val - 1 = k; omega))

/-- From `sim` at the left end, reach `sim` at any cell `j` (sweep right). -/
lemma sim_zero_reaches {n : ℕ} (W : Fin (n + 1) → KWork g₀) (j : Fin (n + 1)) :
    LBA.Reaches (kMachine g₀) ⟨KState.sim, ⟨fun k => mkCell g₀ k (W k), 0⟩⟩
      ⟨KState.sim, ⟨fun k => mkCell g₀ k (W k), j⟩⟩ := by
  suffices H : ∀ m, ∀ j : Fin (n + 1), j.val = m →
      LBA.Reaches (kMachine g₀) ⟨KState.sim, ⟨fun k => mkCell g₀ k (W k), 0⟩⟩
        ⟨KState.sim, ⟨fun k => mkCell g₀ k (W k), j⟩⟩ from H j.val j rfl
  intro m
  induction m with
  | zero => intro j hj; obtain rfl : j = 0 := Fin.ext (by simpa using hj); exact .refl
  | succ k ih =>
      intro j hj
      have hjlt := j.isLt
      have hkn : k < n := by omega
      have hk1 : k + 1 < n + 1 := by omega
      have hjeq : j = (⟨k + 1, hk1⟩ : Fin (n + 1)) := Fin.ext (by simpa using hj)
      rw [hjeq]
      exact (ih ⟨k, by omega⟩ rfl).tail (kStep_sim_right g₀ W ⟨k, by omega⟩ hkn)

/-- From `sim`, the head may be repositioned to any cell. -/
lemma sim_reaches {n : ℕ} (W : Fin (n + 1) → KWork g₀) (i j : Fin (n + 1)) :
    LBA.Reaches (kMachine g₀) ⟨KState.sim, ⟨fun k => mkCell g₀ k (W k), i⟩⟩
      ⟨KState.sim, ⟨fun k => mkCell g₀ k (W k), j⟩⟩ :=
  (sim_reaches_zero g₀ W i).trans (sim_zero_reaches g₀ W j)

/-- Locate a tape split point realizing a given prefix of the decoded form: if a list of
work cells filters to `u ++ z` with `z` non-empty, some position `p` (a valid cell index)
splits the tape with `u` to the left and `z` to the right. -/
lemma list_split_filterMap {α : Type*} (L : List (Option α)) (u z : List α)
    (h : L.filterMap id = u ++ z) (hz : z ≠ []) :
    ∃ p, p < L.length ∧ (L.take p).filterMap id = u ∧ (L.drop p).filterMap id = z := by
  induction L generalizing u with
  | nil => simp only [List.filterMap_nil] at h; exact absurd (List.append_eq_nil_iff.mp h.symm).2 hz
  | cons a t ih =>
      rcases ha : a with _ | x
      · -- blank head: recurse on the tail, shift the split right by one
        rw [ha] at h; simp only [List.filterMap_cons, id, ha] at h
        obtain ⟨p, hp, ht, hd⟩ := ih u h
        refine ⟨p + 1, by simp only [List.length_cons]; omega, ?_, ?_⟩
        · simp only [List.take_succ_cons, List.filterMap_cons, id, ha]; exact ht
        · simp only [List.drop_succ_cons]; exact hd
      · -- symbol head: either it is the first symbol of `z` (`u = []`) or of `u`
        rw [ha] at h; simp only [List.filterMap_cons, id, ha] at h
        cases u with
        | nil =>
            refine ⟨0, by simp only [List.length_cons]; omega, by simp, ?_⟩
            simp only [List.drop_zero, List.filterMap_cons, id, ha]; simpa using h
        | cons b u' =>
            simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
            obtain ⟨p, hp, ht, hd⟩ := ih u' h.2
            refine ⟨p + 1, by simp only [List.length_cons]; omega, ?_, ?_⟩
            · simp only [List.take_succ_cons, List.filterMap_cons, id, ha, h.1]; rw [ht]
            · simp only [List.drop_succ_cons]; exact hd

/-- **One backward derivation step.** If the work track decodes to `u ++ output ++ v` for some
rule `r` (output non-empty by non-contraction), the simulator can reposition, run one backward
`applyRule` pass, and arrive in `sim` with the track decoding to `u ++ patList r ++ v` — i.e. it
undoes the forward step `u ++ patList r ++ v ⇒ u ++ output ++ v`. -/
lemma step_back {n : ℕ} (hnc : grammar_noncontracting g₀) (W : Fin (n + 1) → KWork g₀)
    (i : Fin (n + 1)) (r : grule T g₀.nt) (hr : r ∈ g₀.rules) (u v : List (symbol T g₀.nt))
    (hform : formW g₀ W = u ++ r.output_string ++ v) :
    ∃ (W' : Fin (n + 1) → KWork g₀) (h : Fin (n + 1)),
      LBA.Reaches (kMachine g₀) ⟨KState.sim, ⟨fun k => mkCell g₀ k (W k), i⟩⟩
        ⟨KState.sim, ⟨fun k => mkCell g₀ k (W' k), h⟩⟩
      ∧ formW g₀ W' = u ++ patList g₀ r ++ v := by
  -- Locate the rule's index and the non-contraction bounds.
  obtain ⟨ri, hri⟩ : ∃ ri : Fin g₀.rules.length, g₀.rules[ri] = r := by
    obtain ⟨idx, hidx, he⟩ := List.getElem_of_mem hr
    exact ⟨⟨idx, hidx⟩, he⟩
  have hncr := hnc r hr
  have hpatlen : (patList g₀ r).length ≤ r.output_string.length := by
    simp only [patList, List.length_append, List.length_cons, List.length_nil] at *; omega
  have houtpos : 0 < r.output_string.length := by omega
  -- Find the split position `p`: `u` to the left, `output ++ v` to the right.
  obtain ⟨p, hp, htake, hdropv⟩ :=
    list_split_filterMap (List.ofFn W) u (r.output_string ++ v)
      (by rw [← List.append_assoc]; exact hform) (by simp [houtpos, List.ne_nil_of_length_pos])
  rw [List.length_ofFn] at hp
  -- Run the backward pass starting at `p` (entered from `sim`).
  obtain ⟨W', h, hreach, hpre, hsuf⟩ :=
    applyRule_pass_gen g₀ ri v (by rw [hri]; exact hpatlen) (n - p) W p hp
      (0 : Fin (ruleBound g₀ + 1)) (by rw [hri]; exact houtpos) rfl
      (by rw [hri]; simpa using hdropv)
  refine ⟨W', h, ?_, ?_⟩
  · -- reposition to `p`, take one `sim → applyRule` step, then the pass.
    refine (sim_reaches g₀ W i ⟨p, hp⟩).trans
      (Relation.ReflTransGen.head
        (kStep_sim_applyRule g₀ (fun k => mkCell g₀ k (W k)) ⟨p, hp⟩ ri _ _ _ rfl) ?_)
    exact hreach
  · -- the decoded form: prefix `u` unchanged, suffix becomes `patList r ++ v`.
    have hagree : (List.ofFn W').take p = (List.ofFn W).take p := by
      apply List.ext_getElem
      · simp [List.length_take, List.length_ofFn]
      · intro j h1 _
        have hjp : j < p := by
          rw [List.length_take, List.length_ofFn] at h1; omega
        simp only [List.getElem_take, List.getElem_ofFn]
        exact hpre ⟨j, by omega⟩ hjp
    simp only [Fin.val_zero, List.drop_zero, hri] at hsuf
    rw [formW_split g₀ W' p, hagree, htake, hsuf, ← List.append_assoc]

/-- **Replaying a whole derivation backwards.** If `β ⇒* γ` and the work track decodes to `γ`,
the simulator reaches `sim` with the track decoding to `β`. -/
lemma derive_back {n : ℕ} (hnc : grammar_noncontracting g₀)
    {β γ : List (symbol T g₀.nt)} (hd : grammar_derives g₀ β γ)
    (W : Fin (n + 1) → KWork g₀) (i : Fin (n + 1)) (hform : formW g₀ W = γ) :
    ∃ (W' : Fin (n + 1) → KWork g₀) (h : Fin (n + 1)),
      LBA.Reaches (kMachine g₀) ⟨KState.sim, ⟨fun k => mkCell g₀ k (W k), i⟩⟩
        ⟨KState.sim, ⟨fun k => mkCell g₀ k (W' k), h⟩⟩
      ∧ formW g₀ W' = β := by
  induction hd using Relation.ReflTransGen.head_induction_on generalizing W i with
  | refl => exact ⟨W, i, .refl, hform⟩
  | @head a c hac _ ih =>
      obtain ⟨W₁, h₁, hreach₁, hform₁⟩ := ih W i hform
      obtain ⟨r, hr, u, v, hbeq, hceq⟩ := hac
      obtain ⟨W₂, h₂, hreach₂, hform₂⟩ :=
        step_back g₀ hnc W₁ h₁ r hr u v (by rw [hform₁, hceq])
      refine ⟨W₂, h₂, hreach₁.trans hreach₂, ?_⟩
      rw [hform₂, hbeq]; simp only [patList, List.append_assoc]

/-- If the work track decodes to a single symbol `s`, exactly one cell holds it (the rest blank). -/
lemma filterMap_ofFn_singleton {α : Type*} {n : ℕ} (W : Fin (n + 1) → Option α) (s : α)
    (h : (List.ofFn W).filterMap id = [s]) :
    ∃ j : Fin (n + 1), W j = some s ∧ ∀ k, k ≠ j → W k = none := by
  induction n with
  | zero =>
      have hof : List.ofFn W = [W 0] := by simp [List.ofFn_succ, List.ofFn_zero]
      rw [hof] at h
      rcases hw : W 0 with _ | x
      · rw [hw] at h; simp at h
      · rw [hw] at h; simp only [List.filterMap_cons, id, List.filterMap_nil] at h
        obtain rfl : x = s := by simpa using h
        refine ⟨0, hw, fun k hk => ?_⟩
        rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨k', _⟩
        · exact absurd rfl hk
        · exact k'.elim0
  | succ m ih =>
      have hof : List.ofFn W = W 0 :: List.ofFn (fun i => W i.succ) := by rw [List.ofFn_succ]
      rw [hof] at h
      rcases hw : W 0 with _ | x
      · rw [hw] at h; simp only [List.filterMap_cons, id, List.filterMap_nil] at h
        obtain ⟨j', hj', hoth'⟩ := ih (fun i => W i.succ) h
        refine ⟨j'.succ, hj', ?_⟩
        intro k hk
        rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨k', rfl⟩
        · exact hw
        · exact hoth' k' (fun he => hk (by rw [he]))
      · rw [hw] at h; simp only [List.filterMap_cons, id] at h
        obtain ⟨rfl, hnil⟩ : x = s ∧ (List.ofFn (fun i => W i.succ)).filterMap id = [] := by
          simpa using h
        refine ⟨0, hw, ?_⟩
        intro k hk
        rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨k', rfl⟩
        · exact absurd rfl hk
        · have hmem : W k'.succ ∈ List.ofFn (fun i => W i.succ) := List.mem_ofFn.mpr ⟨k', rfl⟩
          exact List.filterMap_eq_nil_iff.mp hnil _ hmem

end Complete

/-- **Completeness of the simulator.** A derivation `[S] ⇒* w` is replayed in reverse on the
tape (convert input, repeatedly bubble blanks and apply rules backward, then verify `[S]`),
yielding an accepting run. Non-contraction keeps every sentential form within `|w|` cells. -/
theorem kMachine_complete [Fintype T] [DecidableEq T] (g₀ : grammar T)
    [Fintype g₀.nt] [DecidableEq g₀.nt] (hnc : grammar_noncontracting g₀) (w : List T) :
    grammar_language g₀ w → LBA.LanguageViaEmbed (kMachine g₀) (fun t => some (Sum.inl t)) w := by
  intro hw
  -- `hw : grammar_derives g₀ [S] (w.map terminal)`.
  -- Non-contraction forbids deriving the empty word, so `w ≠ []`.
  have htrlen : ∀ {a b : List (symbol T g₀.nt)}, grammar_transforms g₀ a b → a.length ≤ b.length := by
    rintro a b ⟨r, hr, u, v, rfl, rfl⟩
    have := hnc r hr
    simp only [List.length_append, List.length_cons, List.length_nil]; omega
  have hderlen : ∀ {a b : List (symbol T g₀.nt)}, grammar_derives g₀ a b → a.length ≤ b.length := by
    intro a b hab
    induction hab with
    | refl => exact le_refl _
    | tail _ h₂ ih => exact le_trans ih (htrlen h₂)
  have hwne : w ≠ [] := by
    intro h0; have hl := hderlen hw; rw [h0] at hl; simp at hl
  have hmapne : List.map (fun t => some (Sum.inl t)) w ≠ ([] : List (KCell g₀)) := by
    simpa using hwne
  refine ⟨hmapne, ?_⟩
  set L := List.map (fun t => some (Sum.inl t)) w with hL
  have hLlen : L.length = w.length := by rw [hL, List.length_map]
  have hLpos : 0 < L.length := List.length_pos_of_ne_nil hmapne
  set n := L.length - 1 with hn
  have hn1 : n + 1 = w.length := by omega
  have hbound : ∀ i : Fin (n + 1), i.val < w.length := fun i => by have := i.isLt; omega
  set input : Fin (n + 1) → T := fun i => w.get ⟨i.val, hbound i⟩ with hinput
  -- The initial configuration is the raw input tape (`cAt input 0`) at the left end.
  have htape : (LBA.loadList L hmapne).contents = cAt g₀ input 0 := by
    funext i
    simp only [LBA.loadList, cAt, Nat.not_lt_zero, if_false, hinput, hL,
      List.get_eq_getElem, List.getElem_map]
  -- After the init sweep the work track holds `terminal (input k)` in every cell.
  obtain ⟨h0, hinit⟩ := init_reaches g₀ input
  set W₀ : Fin (n + 1) → KWork g₀ := fun k => some (symbol.terminal (input k)) with hW₀
  have hform0 : formW g₀ W₀ = List.map symbol.terminal w := by
    rw [formW_of_forall_some g₀ W₀ (fun k => symbol.terminal (input k)) (fun _ => rfl)]
    apply List.ext_getElem
    · simp only [List.length_ofFn, List.length_map]; omega
    · intro j h1 _
      simp only [List.getElem_ofFn, List.getElem_map, hinput, List.get_eq_getElem]
  -- Replay the derivation backwards down to `[S]`.
  obtain ⟨W', h', hderiv, hformS⟩ := derive_back g₀ hnc hw W₀ h0 hform0
  obtain ⟨j, hj, hother⟩ :=
    filterMap_ofFn_singleton W' (symbol.nonterminal g₀.initial) hformS
  -- The accept check then succeeds.
  obtain ⟨cfg_acc, hreach_acc, hacc_state⟩ := accept_from_S g₀ W' j hj hother h'
  refine ⟨cfg_acc, ?_, hacc_state⟩
  -- Stitch: init config = `⟨init0, cAt input 0, 0⟩`, then init ⟶ sim ⟶ [S] ⟶ accept.
  have hbridge : LBA.initCfgList (kMachine g₀) L hmapne
      = (⟨KState.init0, ⟨cAt g₀ input 0, ⟨0, by omega⟩⟩⟩ : DLBA.Cfg (KCell g₀) (KState g₀) n) := by
    refine cfg_eq g₀ rfl htape (Fin.ext ?_)
    simp [LBA.loadList]
  rw [hbridge]
  exact (hinit.trans hderiv).trans hreach_acc
end

end KurodaConstruction
