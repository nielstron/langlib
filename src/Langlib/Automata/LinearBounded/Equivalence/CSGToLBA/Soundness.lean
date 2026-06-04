module

public import Langlib.Automata.LinearBounded.Equivalence.CSGToLBA.Completeness
import Mathlib.Tactic
@[expose]
public section

/-!
# CSG → LBA (Kuroda): soundness

This file proves the **soundness** half: every accepting run of `kMachine g₀` on `w` exhibits a
derivation `[S] ⇒* w` (`kMachine_sound`).

It is a forward invariant `SoundClaim` over configurations reachable from the initial one
(`sound_invariant`, by induction on the run), with one phase per machine state. The simulator
reduces the decoded form toward `[S]` by reverse rule applications, so the current form always
forward-derives to the target `w·terminal`; the `applyRule` phase carries the loop invariant of
a backward pass, and the accept-check phase (`check_sound`, `gotoLeft_check_sound`) certifies the
final form is exactly `[S]`.
-/

namespace KurodaConstruction

open List Relation Classical

noncomputable section

variable {T : Type}
/-! ### Soundness: a reachable accepting run exhibits a derivation -/
section Sound

variable [Fintype T] [DecidableEq T] (g₀ : grammar T) [Fintype g₀.nt] [DecidableEq g₀.nt]

/-- Decode one tape cell to the sentential-form symbol it represents: a raw input cell
`some (inl t)` decodes to `terminal t` (so the decoded form is unchanged during the init sweep),
a work cell decodes to its work symbol, a blank to nothing. -/
def decodeCell : KCell g₀ → KWork g₀
  | none => none
  | some (Sum.inl t) => some (symbol.terminal t)
  | some (Sum.inr (_, _, ws)) => ws

/-- The sentential form represented by a whole tape (the non-blank decoded cells, in order). -/
def decodeForm {n : ℕ} (c : Fin (n + 1) → KCell g₀) : List (symbol T g₀.nt) :=
  (List.ofFn (fun k => decodeCell g₀ (c k))).filterMap id

@[simp] lemma decodeCell_mkCell {n : ℕ} (k : Fin (n + 1)) (ws : KWork g₀) :
    decodeCell g₀ (mkCell g₀ k ws) = ws := rfl

/-- The decoded form of a canonical work tape is its `formW`. -/
lemma decodeForm_mkCell {n : ℕ} (W : Fin (n + 1) → KWork g₀) :
    decodeForm g₀ (fun k => mkCell g₀ k (W k)) = formW g₀ W := by
  simp only [decodeForm, decodeCell_mkCell, formW]

@[simp] lemma decodeCell_inl (t : T) :
    decodeCell g₀ (some (Sum.inl t)) = some (symbol.terminal t) := rfl

/-- During the init sweep the decoded form is constant: every raw or converted cell of
`cAt input i` decodes to `terminal (input k)`. -/
lemma decodeForm_cAt {n : ℕ} (input : Fin (n + 1) → T) (i : ℕ) :
    decodeForm g₀ (cAt g₀ input i) = List.ofFn (fun k => symbol.terminal (input k)) := by
  have hcell : ∀ k, decodeCell g₀ (cAt g₀ input i k) = some (symbol.terminal (input k)) := by
    intro k
    simp only [cAt]
    by_cases hk : k.val < i
    · rw [if_pos hk]; simp only [tmpCell, decodeCell]
    · rw [if_neg hk]; simp only [decodeCell]
  simp only [decodeForm, hcell]
  rw [show (fun k => some (symbol.terminal (input k))) = (fun k => (some (symbol.terminal (input k)) : KWork g₀)) from rfl]
  rw [← formW]
  exact formW_of_forall_some g₀ _ (fun k => symbol.terminal (input k)) (fun _ => rfl)

/-- `take (i+1)` peels the `i`-th cell off the decoded prefix. -/
lemma take_succ_filterMap {n : ℕ} (W : Fin (n + 1) → KWork g₀) (head : Fin (n + 1)) :
    ((List.ofFn W).take (head.val + 1)).filterMap id
      = ((List.ofFn W).take head.val).filterMap id ++ ([W head].filterMap id) := by
  rw [← List.take_concat_get' (List.ofFn W) head.val (by rw [List.length_ofFn]; exact head.isLt),
    List.filterMap_append, List.getElem_ofFn, Fin.eta]

/-- The decoded form splits at the head into prefix, head cell, and suffix. -/
lemma decodeForm_split_head {n : ℕ} (W : Fin (n + 1) → KWork g₀) (head : Fin (n + 1))
    (pre : List (symbol T g₀.nt))
    (hp : ((List.ofFn W).take head.val).filterMap id = pre) :
    formW g₀ W = pre ++ ([W head].filterMap id)
      ++ ((List.ofFn W).drop (head.val + 1)).filterMap id := by
  have hdc : ((List.ofFn W).drop head.val).filterMap id
      = ([W head].filterMap id) ++ ((List.ofFn W).drop (head.val + 1)).filterMap id := by
    have hlen : head.val < (List.ofFn W).length := by rw [List.length_ofFn]; exact head.isLt
    rw [List.drop_eq_getElem_cons hlen, List.getElem_ofFn, Fin.eta, ← List.singleton_append,
      List.filterMap_append]
  conv_lhs => rw [formW, ← List.take_append_drop head.val (List.ofFn W), List.filterMap_append]
  rw [hp, hdc, ← List.append_assoc]

/-- The head-moved tape after an *echo* write at `head` (cell value re-written) with `head.val < n`
is the same canonical tape with the head advanced one cell. -/
lemma echo_moveHead_right {n : ℕ} (W : Fin (n + 1) → KWork g₀) (head : Fin (n + 1))
    (a : KCell g₀) (ha : a = (fun k => mkCell g₀ k (W k)) head) (hlt : head.val < n) :
    (DLBA.BoundedTape.write (⟨fun k => mkCell g₀ k (W k), head⟩ : DLBA.BoundedTape (KCell g₀) n)
        a).moveHead DLBA.Dir.right
      = ⟨fun k => mkCell g₀ k (W k), ⟨head.val + 1, by omega⟩⟩ := by
  simp only [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead, dif_pos hlt, ha,
    Function.update_eq_self]

/-- **Soundness of the accept check** (reverse of `check_sweep`): if a `check` sweep whose verified
prefix spells `[S]` iff `seen` reaches an accepting configuration, the whole track spells `[S]`. -/
lemma check_sound {n : ℕ} {cfgacc : DLBA.Cfg (KCell g₀) (KState g₀) n}
    (hacc : cfgacc.state = KState.accept) (W : Fin (n + 1) → KWork g₀) :
    ∀ d : ℕ, ∀ (seen : Bool) (head : Fin (n + 1)), n - head.val = d →
      LBA.Reaches (kMachine g₀)
        ⟨KState.check seen, ⟨fun k => mkCell g₀ k (W k), head⟩⟩ cfgacc →
      ((List.ofFn W).take head.val).filterMap id
        = (if seen then [symbol.nonterminal g₀.initial] else []) →
      formW g₀ W = [symbol.nonterminal g₀.initial] := by
  intro d
  induction d with
  | zero =>
      intro seen head hd hreach hpre
      have hhn : head.val = n := by have := head.isLt; omega
      have hdrop : ((List.ofFn W).drop (head.val + 1)).filterMap id = [] := by
        rw [List.drop_eq_nil_of_le (by rw [List.length_ofFn]; omega), List.filterMap_nil]
      rcases hreach.cases_head with heq | ⟨mid, hstep, hrest⟩
      · exfalso; rw [← heq] at hacc; simp at hacc
      · obtain ⟨q', a, dir, hmem, rfl⟩ := hstep
        simp only [kMachine, DLBA.BoundedTape.read] at hmem
        rcases hwh : W head with _ | sym
        · -- blank at the right end: accept needs `seen`
          cases seen with
          | false => simp only [mkCell, hwh, hhn, kTransition] at hmem; simp at hmem
          | true => rw [decodeForm_split_head g₀ W head _ hpre, hdrop, hwh]; simp
        · rcases sym with t | N
          · -- terminal: stuck
            simp [mkCell, hwh, kTransition] at hmem
          · -- nonterminal
            cases seen with
            | true => simp only [mkCell, hwh, hhn, kTransition] at hmem; simp at hmem
            | false =>
                by_cases hN : N = g₀.initial
                · subst hN; rw [decodeForm_split_head g₀ W head _ hpre, hdrop, hwh]; simp
                · simp only [mkCell, hwh, hhn, kTransition] at hmem; simp [hN] at hmem
  | succ e ih =>
      intro seen head hd hreach hpre
      have hhn : head.val < n := by omega
      have hrn : decide (head.val = n) = false := decide_eq_false (by omega)
      rcases hreach.cases_head with heq | ⟨mid, hstep, hrest⟩
      · exfalso; rw [← heq] at hacc; simp at hacc
      · obtain ⟨q', a, dir, hmem, rfl⟩ := hstep
        simp only [kMachine, DLBA.BoundedTape.read] at hmem
        rcases hwh : W head with _ | sym
        · -- blank: move right, `seen` unchanged
          simp only [mkCell, hwh, kTransition] at hmem
          rw [if_neg (by simp [hrn])] at hmem
          simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          obtain ⟨rfl, rfl, rfl⟩ := hmem
          rw [echo_moveHead_right g₀ W head _ (by simp [mkCell, hwh]) hhn] at hrest
          refine ih seen ⟨head.val + 1, by omega⟩ (by show n - (head.val + 1) = e; omega) hrest ?_
          rw [take_succ_filterMap g₀, hpre, hwh]; simp
        · rcases sym with t | N
          · simp [mkCell, hwh, kTransition] at hmem
          · cases seen with
            | true => simp [mkCell, hwh, kTransition] at hmem
            | false =>
                by_cases hN : N = g₀.initial
                · subst hN
                  simp only [mkCell, hwh, kTransition] at hmem
                  rw [if_pos (by simp), if_neg (by simp [hrn])] at hmem
                  simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hmem
                  obtain ⟨rfl, rfl, rfl⟩ := hmem
                  rw [echo_moveHead_right g₀ W head _ (by simp [mkCell, hwh]) hhn] at hrest
                  refine ih true ⟨head.val + 1, by omega⟩ (by show n - (head.val + 1) = e; omega)
                    hrest ?_
                  rw [take_succ_filterMap g₀, hpre, hwh]; simp
                · simp only [mkCell, hwh, kTransition] at hmem; simp [hN] at hmem

/-- **Soundness of the `gotoLeft` + accept-check phase.** If `gotoLeft` (from any head) reaches an
accepting configuration, the work track spells `[S]`. -/
lemma gotoLeft_check_sound {n : ℕ} {cfgacc : DLBA.Cfg (KCell g₀) (KState g₀) n}
    (hacc : cfgacc.state = KState.accept) (W : Fin (n + 1) → KWork g₀) :
    ∀ m : ℕ, ∀ head : Fin (n + 1), head.val = m →
      LBA.Reaches (kMachine g₀) ⟨KState.gotoLeft, ⟨fun k => mkCell g₀ k (W k), head⟩⟩ cfgacc →
      formW g₀ W = [symbol.nonterminal g₀.initial] := by
  intro m
  induction m with
  | zero =>
      intro head hm hreach
      have h0 : head.val = 0 := hm
      rcases hreach.cases_head with heq | ⟨mid, hstep, hrest⟩
      · exfalso; rw [← heq] at hacc; simp at hacc
      · obtain ⟨q', a, dir, hmem, rfl⟩ := hstep
        simp only [kMachine, DLBA.BoundedTape.read, mkCell, kTransition] at hmem
        rw [if_pos (show decide (head.val = 0) = true by simp [h0])] at hmem
        simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        obtain ⟨rfl, rfl, rfl⟩ := hmem
        have htape : (DLBA.BoundedTape.write
            (⟨fun k => mkCell g₀ k (W k), head⟩ : DLBA.BoundedTape (KCell g₀) n)
            (some (Sum.inr (decide (head.val = 0), decide (head.val = n), W head)))).moveHead
            DLBA.Dir.stay
            = (⟨fun k => mkCell g₀ k (W k), head⟩ : DLBA.BoundedTape (KCell g₀) n) := by
          simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write]
          congr 1
          funext k; rw [Function.update_apply]; by_cases hk : k = head
          · subst hk; simp [mkCell]
          · rw [if_neg hk]
        rw [htape] at hrest
        exact check_sound g₀ hacc W (n - head.val) false head rfl hrest (by simp [h0])
  | succ e ih =>
      intro head hm hreach
      have hpos : 0 < head.val := by omega
      rcases hreach.cases_head with heq | ⟨mid, hstep, hrest⟩
      · exfalso; rw [← heq] at hacc; simp at hacc
      · obtain ⟨q', a, dir, hmem, rfl⟩ := hstep
        simp only [kMachine, DLBA.BoundedTape.read, mkCell, kTransition] at hmem
        rw [if_neg (show ¬ (decide (head.val = 0) = true) by
          simp only [decide_eq_true_eq]; omega)] at hmem
        simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        obtain ⟨rfl, rfl, rfl⟩ := hmem
        have htape : (DLBA.BoundedTape.write
            (⟨fun k => mkCell g₀ k (W k), head⟩ : DLBA.BoundedTape (KCell g₀) n)
            (some (Sum.inr (decide (head.val = 0), decide (head.val = n), W head)))).moveHead
            DLBA.Dir.left
            = (⟨fun k => mkCell g₀ k (W k), ⟨head.val - 1, by omega⟩⟩ :
                DLBA.BoundedTape (KCell g₀) n) := by
          simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, dif_pos hpos]
          congr 1
          funext k; rw [Function.update_apply]; by_cases hk : k = head
          · subst hk; simp [mkCell]
          · rw [if_neg hk]
        rw [htape] at hrest
        exact ih ⟨head.val - 1, by omega⟩ (by show head.val - 1 = e; omega) hrest

/-- The phase-indexed soundness invariant maintained FORWARD along a run from the initial
configuration. The simulator reduces the working form toward `[S]` by reverse rule applications,
so at every reachable configuration the current form derives (forward) to the target `w·terminal`.
The structure (`cAt`/`mkCell`) flows forward from init, which is why the induction is forward. -/
def SoundClaim {n : ℕ} (g₀ : grammar T) [Fintype g₀.nt] [DecidableEq g₀.nt]
    (input : Fin (n + 1) → T) (cfg : DLBA.Cfg (KCell g₀) (KState g₀) n) : Prop :=
  (cfg.state = KState.init0 ∧ cfg.tape.contents = cAt g₀ input 0 ∧ cfg.tape.head.val = 0) ∨
  (cfg.state = KState.initSweep ∧ ∃ i : ℕ, cfg.tape.contents = cAt g₀ input i ∧ 1 ≤ i ∧
    (cfg.tape.head.val = i ∧ i ≤ n ∨ cfg.tape.head.val = n ∧ i = n + 1)) ∨
  (∃ W : Fin (n + 1) → KWork g₀, cfg.tape.contents = (fun k => mkCell g₀ k (W k)) ∧
    cfg.state = KState.sim ∧
    grammar_derives g₀ (formW g₀ W) (List.ofFn (fun k => symbol.terminal (input k)))) ∨
  (∃ W : Fin (n + 1) → KWork g₀, cfg.tape.contents = (fun k => mkCell g₀ k (W k)) ∧
    cfg.state = KState.gotoLeft ∧
    grammar_derives g₀ (formW g₀ W) (List.ofFn (fun k => symbol.terminal (input k)))) ∨
  (∃ (W : Fin (n + 1) → KWork g₀) (seen : Bool), cfg.tape.contents = (fun k => mkCell g₀ k (W k)) ∧
    cfg.state = KState.check seen ∧
    grammar_derives g₀ (formW g₀ W) (List.ofFn (fun k => symbol.terminal (input k))) ∧
    ((List.ofFn W).take cfg.tape.head.val).filterMap id
      = (if seen then [symbol.nonterminal g₀.initial] else [])) ∨
  (∃ (W W₀ : Fin (n + 1) → KWork g₀) (ri : Fin g₀.rules.length) (k : Fin (ruleBound g₀ + 1))
      (Aorig : List (symbol T g₀.nt)),
    cfg.tape.contents = (fun k => mkCell g₀ k (W k)) ∧ cfg.state = KState.applyRule ri k ∧
    k.val ≤ (g₀.rules[ri]).output_string.length ∧
    (patList g₀ g₀.rules[ri]).length ≤ (g₀.rules[ri]).output_string.length ∧
    (∀ p : Fin (n + 1), cfg.tape.head.val ≤ p.val → W p = W₀ p) ∧
    ((List.ofFn W).take cfg.tape.head.val).filterMap id
      = Aorig ++ (patList g₀ g₀.rules[ri]).take k.val ∧
    ((List.ofFn W₀).take cfg.tape.head.val).filterMap id
      = Aorig ++ (g₀.rules[ri]).output_string.take k.val ∧
    grammar_derives g₀ (formW g₀ W₀) (List.ofFn (fun k => symbol.terminal (input k)))) ∨
  (∃ W : Fin (n + 1) → KWork g₀, cfg.tape.contents = (fun k => mkCell g₀ k (W k)) ∧
    cfg.state = KState.accept ∧ formW g₀ W = [symbol.nonterminal g₀.initial] ∧
    grammar_derives g₀ (formW g₀ W) (List.ofFn (fun k => symbol.terminal (input k))))

/-- **Forward soundness invariant.** Every configuration reachable from the initial one satisfies
`SoundClaim`. -/
lemma sound_invariant {n : ℕ} (hnc : grammar_noncontracting g₀) (input : Fin (n + 1) → T)
    (cfg : DLBA.Cfg (KCell g₀) (KState g₀) n)
    (hreach : LBA.Reaches (kMachine g₀)
      ⟨KState.init0, ⟨cAt g₀ input 0, ⟨0, n.succ_pos⟩⟩⟩ cfg) :
    SoundClaim g₀ input cfg := by
  induction hreach with
  | refl => exact Or.inl ⟨rfl, rfl, rfl⟩
  | @tail b c hab hbc ih =>
      obtain ⟨q', sym, dir, hmem, rfl⟩ := hbc
      simp only [kMachine] at hmem
      rcases ih with ⟨hst, hc0, hh0⟩ | ⟨hst, i, hci, hi1, hcase⟩ |
        ⟨W, hcW, hst, hder⟩ | ⟨W, hcW, hst, hder⟩ | ⟨W, seen, hcW, hst, hder, hacm⟩ |
        ⟨W, W₀, ri, k, Aorig, hcW, hst, hk, hpat, hagree, htkW, htkW₀, hder⟩ |
        ⟨W, hcW, hst, hform, hder⟩
      · -- b = init0
        rw [hst] at hmem
        simp only [DLBA.BoundedTape.read, hc0, cAt, Nat.not_lt_zero, if_false, kTransition,
          Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        obtain ⟨rfl, rfl, rfl⟩ := hmem
        refine Or.inr (Or.inl ⟨rfl, 1, ?_, le_refl 1, ?_⟩)
        · simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, hc0]
          rw [show (some (Sum.inr (true, false, some (symbol.terminal (input b.tape.head))))
                  : KCell g₀) = tmpCell g₀ input b.tape.head from by simp [tmpCell, hh0],
            show cAt g₀ input 0 = cAt g₀ input b.tape.head.val from by rw [hh0], cAt_update, hh0]
        · simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write]
          split_ifs with hn0
          · left; exact ⟨by simp [hh0], by omega⟩
          · right; exact ⟨by omega, by omega⟩
      · -- b = initSweep
        rw [hst] at hmem
        simp only [DLBA.BoundedTape.read, hci] at hmem
        rcases hcase with ⟨hhi, hin⟩ | ⟨hhn, hin1⟩
        · -- convert cell `i` (raw), move right
          have hcell : cAt g₀ input i b.tape.head = some (Sum.inl (input b.tape.head)) := by
            simp only [cAt, if_neg (show ¬ b.tape.head.val < i by omega)]
          rw [hcell, kTransition] at hmem
          simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          obtain ⟨rfl, rfl, rfl⟩ := hmem
          refine Or.inr (Or.inl ⟨rfl, i + 1, ?_, by omega, ?_⟩)
          · funext k
            simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, hci,
              Function.update_apply]
            by_cases hk : k = b.tape.head
            · subst hk; rw [if_pos rfl]
              simp only [cAt, if_pos (show b.tape.head.val < i + 1 by omega), tmpCell,
                decide_eq_false (show ¬ b.tape.head.val = 0 by omega)]
            · rw [if_neg hk]
              have hki : k.val ≠ i := fun h => hk (Fin.ext (by rw [h, hhi]))
              simp only [cAt]
              by_cases h1 : k.val < i
              · rw [if_pos h1, if_pos (show k.val < i + 1 by omega)]
              · rw [if_neg h1, if_neg (show ¬ k.val < i + 1 by omega)]
          · simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write]
            split_ifs with hn0
            · left; exact ⟨by simp [hhi], by omega⟩
            · right; exact ⟨by omega, by omega⟩
        · -- clamp at the right end (cell already converted): enter `sim`
          have hcell : cAt g₀ input i b.tape.head
              = some (Sum.inr (decide (b.tape.head.val = 0), false,
                  some (symbol.terminal (input b.tape.head)))) := by
            simp only [cAt, if_pos (show b.tape.head.val < i by omega), tmpCell]
          rw [hcell, kTransition] at hmem
          simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          obtain ⟨rfl, rfl, rfl⟩ := hmem
          refine Or.inr (Or.inr (Or.inl
            ⟨fun k => some (symbol.terminal (input k)), ?_, rfl, ?_⟩))
          · funext k
            simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, hci, Function.update_apply]
            by_cases hk : k = b.tape.head
            · subst hk; rw [if_pos rfl]; simp [mkCell, hhn]
            · rw [if_neg hk]
              have hkn : k.val ≠ n := fun h => hk (Fin.ext (h.trans hhn.symm))
              simp only [cAt, if_pos (show k.val < i by omega), tmpCell, mkCell,
                decide_eq_false hkn]
          · rw [formW_of_forall_some g₀ _ (fun k => symbol.terminal (input k)) (fun _ => rfl)]
            exact Relation.ReflTransGen.refl
      · -- b = sim
        rw [hst] at hmem
        simp only [DLBA.BoundedTape.read, hcW] at hmem
        have hcon : ∀ (d : DLBA.Dir),
            ((DLBA.BoundedTape.write b.tape
                (mkCell g₀ b.tape.head (W b.tape.head))).moveHead d).contents
              = fun k => mkCell g₀ k (W k) := by
          intro d
          cases d <;>
          · simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, hcW]
            funext k; rw [Function.update_apply]; by_cases hk : k = b.tape.head
            · subst hk; simp [mkCell]
            · rw [if_neg hk]
        simp only [mkCell, kTransition, Set.mem_union, Set.mem_insert_iff,
          Set.mem_singleton_iff, Set.mem_setOf_eq] at hmem
        rcases hmem with (h | h | h) | ⟨ri, h⟩
        · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
          exact Or.inr (Or.inr (Or.inl ⟨W, hcon _, rfl, hder⟩))
        · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
          exact Or.inr (Or.inr (Or.inl ⟨W, hcon _, rfl, hder⟩))
        · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
          exact Or.inr (Or.inr (Or.inr (Or.inl ⟨W, hcon _, rfl, hder⟩)))
        · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
          have hpatlen : (patList g₀ g₀.rules[ri]).length
              ≤ (g₀.rules[ri]).output_string.length := by
            have h1 := hnc (g₀.rules[ri]) (List.getElem_mem _)
            simp only [patList, List.length_append, List.length_cons, List.length_nil]
            omega
          refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨W, W, ri, 0, ((List.ofFn W).take b.tape.head.val).filterMap id,
              hcon _, rfl, Nat.zero_le _, hpatlen, fun p _ => rfl, ?_, ?_, hder⟩)))))
          · simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, Fin.val_zero,
              List.take_zero, List.filterMap_nil, List.append_nil]
          · simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, Fin.val_zero,
              List.take_zero, List.filterMap_nil, List.append_nil]
      · -- b = gotoLeft
        rw [hst] at hmem
        simp only [DLBA.BoundedTape.read, hcW] at hmem
        set h := b.tape.head with hh
        by_cases hh0 : h.val = 0
        · -- at the left end: enter the check sweep
          simp only [mkCell, kTransition] at hmem
          rw [if_pos (show decide (h.val = 0) = true by simp [hh0])] at hmem
          simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          obtain ⟨rfl, rfl, rfl⟩ := hmem
          refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨W, false, ?_, rfl, hder, ?_⟩))))
          · simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, hcW]
            funext k; rw [Function.update_apply]; by_cases hk : k = h
            · subst hk; simp [mkCell]
            · rw [if_neg hk]
          · simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write]
            rw [show b.tape.head.val = 0 from hh0]; simp
        · -- move left, stay in gotoLeft
          simp only [mkCell, kTransition] at hmem
          rw [if_neg (show ¬ (decide (h.val = 0) = true) by
            simp only [decide_eq_true_eq]; exact hh0)] at hmem
          simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          obtain ⟨rfl, rfl, rfl⟩ := hmem
          refine Or.inr (Or.inr (Or.inr (Or.inl ⟨W, ?_, rfl, hder⟩)))
          simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, hcW]
          funext k; rw [Function.update_apply]; by_cases hk : k = h
          · subst hk; simp [mkCell]
          · rw [if_neg hk]
      · -- b = check seen
        rw [hst] at hmem
        simp only [DLBA.BoundedTape.read, hcW] at hmem
        have hcon : ∀ (x : KWork g₀),
            mkCell g₀ b.tape.head x = mkCell g₀ b.tape.head (W b.tape.head) →
            (DLBA.BoundedTape.write b.tape (mkCell g₀ b.tape.head x)).contents
              = fun k => mkCell g₀ k (W k) := by
          intro x hx
          simp only [DLBA.BoundedTape.write, hcW]
          funext k; rw [Function.update_apply]; by_cases hk : k = b.tape.head
          · subst hk; rw [if_pos rfl]; exact hx
          · rw [if_neg hk]
        have hdrop_nil : ∀ (_ : b.tape.head.val = n),
            ((List.ofFn W).drop (b.tape.head.val + 1)).filterMap id = [] := fun hrn => by
          rw [List.drop_eq_nil_of_le (by rw [List.length_ofFn]; omega), List.filterMap_nil]
        rcases hwh : W b.tape.head with _ | symb
        · -- blank cell
          by_cases hrn : b.tape.head.val = n
          · cases seen with
            | false =>
                simp only [mkCell, hwh, kTransition] at hmem
                rw [if_pos (show decide (b.tape.head.val = n) = true by simp [hrn])] at hmem
                simp at hmem
            | true =>
                simp only [mkCell, hwh, kTransition] at hmem
                rw [if_pos (show decide (b.tape.head.val = n) = true by simp [hrn])] at hmem
                simp only [if_true, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
                obtain ⟨rfl, rfl, rfl⟩ := hmem
                refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                  ⟨W, ?_, rfl, ?_, hder⟩)))))
                · simp only [DLBA.BoundedTape.moveHead]
                  exact hcon none (by rw [hwh])
                · rw [decodeForm_split_head g₀ W b.tape.head _ hacm, hdrop_nil hrn, hwh]; simp
          · -- h < n: move right, keep seen
            have hlt : b.tape.head.val < n := by have := b.tape.head.isLt; omega
            simp only [mkCell, hwh, kTransition] at hmem
            rw [if_neg (show ¬ (decide (b.tape.head.val = n) = true) by
              simp only [decide_eq_true_eq]; omega)] at hmem
            simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            obtain ⟨rfl, rfl, rfl⟩ := hmem
            refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨W, seen, ?_, rfl, hder, ?_⟩))))
            · simp only [DLBA.BoundedTape.moveHead, dif_pos hlt]
              exact hcon none (by rw [hwh])
            · simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write]
              rw [dif_pos (show b.tape.head.val < n from hlt)]
              show ((List.ofFn W).take (b.tape.head.val + 1)).filterMap id = _
              rw [take_succ_filterMap g₀ W b.tape.head, hacm, hwh]; simp
        · rcases symb with t | N
          · -- terminal: stuck
            simp [mkCell, hwh, kTransition] at hmem
          · -- nonterminal N
            by_cases hN : N = g₀.initial ∧ seen = false
            · obtain ⟨rfl, hsf⟩ := hN
              by_cases hrn : b.tape.head.val = n
              · simp only [mkCell, hwh, kTransition] at hmem
                rw [if_pos (show True ∧ ¬ (seen = true) from ⟨trivial, by simp [hsf]⟩),
                  if_pos (show decide (b.tape.head.val = n) = true by simp [hrn])] at hmem
                simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hmem
                obtain ⟨rfl, rfl, rfl⟩ := hmem
                refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                  ⟨W, ?_, rfl, ?_, hder⟩)))))
                · simp only [DLBA.BoundedTape.moveHead]
                  exact hcon _ (by rw [hwh])
                · rw [decodeForm_split_head g₀ W b.tape.head _ hacm, hdrop_nil hrn, hwh, hsf]; simp
              · have hlt : b.tape.head.val < n := by have := b.tape.head.isLt; omega
                simp only [mkCell, hwh, kTransition] at hmem
                rw [if_pos (show True ∧ ¬ (seen = true) from ⟨trivial, by simp [hsf]⟩),
                  if_neg (show ¬ (decide (b.tape.head.val = n) = true) by
                    simp only [decide_eq_true_eq]; omega)] at hmem
                simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hmem
                obtain ⟨rfl, rfl, rfl⟩ := hmem
                refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨W, true, ?_, rfl, hder, ?_⟩))))
                · simp only [DLBA.BoundedTape.moveHead, dif_pos hlt]
                  exact hcon _ (by rw [hwh])
                · simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write]
                  rw [dif_pos (show b.tape.head.val < n from hlt)]
                  show ((List.ofFn W).take (b.tape.head.val + 1)).filterMap id = _
                  rw [take_succ_filterMap g₀ W b.tape.head, hacm, hsf, hwh]; simp
            · -- condition fails: stuck
              rw [not_and_or] at hN
              simp only [mkCell, hwh, kTransition] at hmem
              rcases hN with hN | hN
              · rw [if_neg (by tauto)] at hmem; simp at hmem
              · simp only [Bool.not_eq_false] at hN
                rw [if_neg (by simp [hN])] at hmem; simp at hmem
      · -- b = applyRule ri k
        rw [hst] at hmem
        simp only [DLBA.BoundedTape.read, hcW] at hmem
        rcases hwh : W b.tape.head with _ | s
        · -- blank: skip (move right), same `k`
          by_cases hrn : b.tape.head.val = n
          · simp only [mkCell, hwh, kTransition] at hmem
            rw [if_pos (show decide (b.tape.head.val = n) = true by simp [hrn])] at hmem
            simp at hmem
          · have hlt : b.tape.head.val < n := by have := b.tape.head.isLt; omega
            simp only [mkCell, hwh, kTransition] at hmem
            rw [if_neg (show ¬ (decide (b.tape.head.val = n) = true) by
              simp only [decide_eq_true_eq]; omega)] at hmem
            simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            obtain ⟨rfl, rfl, rfl⟩ := hmem
            refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
              ⟨W, W₀, ri, k, Aorig, ?_, rfl, hk, hpat, ?_, ?_, ?_, hder⟩)))))
            · simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, dif_pos hlt, hcW]
              funext p; rw [Function.update_apply]; by_cases hp : p = b.tape.head
              · subst hp; simp [mkCell, hwh]
              · rw [if_neg hp]
            · intro p hp
              simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, dif_pos hlt] at hp
              exact hagree p (by omega)
            · simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, dif_pos hlt]
              show ((List.ofFn W).take (b.tape.head.val + 1)).filterMap id = _
              rw [take_succ_filterMap g₀ W b.tape.head, htkW, hwh]; simp
            · simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, dif_pos hlt]
              show ((List.ofFn W₀).take (b.tape.head.val + 1)).filterMap id = _
              rw [take_succ_filterMap g₀ W₀ b.tape.head, htkW₀,
                show W₀ b.tape.head = none from by
                  rw [← hagree b.tape.head (le_refl _)]; exact hwh]
              simp
        · -- symbol `s`: match `output[k]` and write the replacement
          simp only [mkCell, hwh, kTransition] at hmem
          by_cases hm : (g₀.rules[ri]).output_string[k.val]? = some s
          swap
          · rw [if_neg hm] at hmem; simp at hmem
          rw [if_pos hm] at hmem
          have hklt : k.val < (g₀.rules[ri]).output_string.length :=
            List.getElem?_eq_some_iff.mp hm |>.1
          have hval : ((k + 1 : Fin (ruleBound g₀ + 1))).val = k.val + 1 := by
            apply Fin.val_add_one_of_lt'
            have := output_length_le_ruleBound g₀ ri; omega
          have hW₀h : W₀ b.tape.head = some s := (hagree b.tape.head (le_refl _)).symm.trans hwh
          have peel : ∀ (l : List (symbol T g₀.nt)) (m : ℕ),
              l.take m ++ ([l[m]?].filterMap id) = l.take (m + 1) := by
            intro l m
            rcases lt_or_ge m l.length with hm' | hm'
            · simp only [List.getElem?_eq_getElem hm', List.filterMap_cons, id, List.filterMap_nil]
              exact List.take_concat_get' _ _ hm'
            · rw [List.getElem?_eq_none (by omega)]
              simp only [List.filterMap_cons, id, List.filterMap_nil, List.append_nil]
              rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
          -- `take head` of the updated tape is unchanged (the write is at `head`).
          have htkW'eq : ((List.ofFn (Function.update W b.tape.head
                ((patList g₀ g₀.rules[ri])[k.val]?))).take b.tape.head.val).filterMap id
              = Aorig ++ (patList g₀ g₀.rules[ri]).take k.val := by
            rw [show (List.ofFn (Function.update W b.tape.head
                  ((patList g₀ g₀.rules[ri])[k.val]?))).take b.tape.head.val
                = (List.ofFn W).take b.tape.head.val from by
              apply List.ext_getElem (by simp)
              intro j hj1 _
              have hjlt : j < b.tape.head.val := by
                rw [List.length_take, List.length_ofFn] at hj1; omega
              simp only [List.getElem_take, ofFn_update, List.getElem_ofFn,
                List.getElem_set_ne (show b.tape.head.val ≠ j from by omega)]]
            exact htkW
          by_cases hk1 : k.val + 1 < (g₀.rules[ri]).output_string.length
          · -- continue
            rw [if_pos hk1] at hmem
            by_cases hrn : b.tape.head.val = n
            · rw [if_pos (show decide (b.tape.head.val = n) = true by simp [hrn])] at hmem
              simp at hmem
            · have hlt : b.tape.head.val < n := by have := b.tape.head.isLt; omega
              rw [if_neg (show ¬ (decide (b.tape.head.val = n) = true) by
                simp only [decide_eq_true_eq]; omega)] at hmem
              simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hmem
              obtain ⟨rfl, rfl, rfl⟩ := hmem
              refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨Function.update W b.tape.head ((patList g₀ g₀.rules[ri])[k.val]?), W₀, ri, k + 1,
                  Aorig, ?_, rfl, ?_, hpat, ?_, ?_, ?_, hder⟩)))))
              · simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, dif_pos hlt, hcW]
                rw [show (some (Sum.inr (decide (b.tape.head.val = 0), decide (b.tape.head.val = n),
                      (patList g₀ g₀.rules[ri])[k.val]?)) : KCell g₀)
                    = mkCell g₀ b.tape.head ((patList g₀ g₀.rules[ri])[k.val]?) from rfl,
                  update_mkCell]
              · rw [hval]; omega
              · intro p hp
                simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, dif_pos hlt] at hp
                rw [Function.update_of_ne (fun he => by rw [he] at hp; omega)]
                exact hagree p (by omega)
              · simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, dif_pos hlt]
                show ((List.ofFn (Function.update W b.tape.head _)).take
                  (b.tape.head.val + 1)).filterMap id = _
                rw [take_succ_filterMap g₀ _ b.tape.head, Function.update_self, htkW'eq, hval,
                  List.append_assoc, peel]
              · simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, dif_pos hlt]
                show ((List.ofFn W₀).take (b.tape.head.val + 1)).filterMap id = _
                rw [take_succ_filterMap g₀ W₀ b.tape.head, htkW₀, hW₀h, hval, List.append_assoc]
                congr 1
                rw [show ([some s].filterMap id) = ([(g₀.rules[ri]).output_string[k.val]?].filterMap id)
                    from by rw [hm], peel]
          · by_cases hk2 : k.val + 1 = (g₀.rules[ri]).output_string.length
            · -- last symbol: return to `sim`
              rw [if_neg hk1, if_pos hk2] at hmem
              simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hmem
              obtain ⟨rfl, rfl, rfl⟩ := hmem
              refine Or.inr (Or.inr (Or.inl
                ⟨Function.update W b.tape.head ((patList g₀ g₀.rules[ri])[k.val]?), ?_, rfl, ?_⟩))
              · simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, hcW]
                rw [show (some (Sum.inr (decide (b.tape.head.val = 0), decide (b.tape.head.val = n),
                      (patList g₀ g₀.rules[ri])[k.val]?)) : KCell g₀)
                    = mkCell g₀ b.tape.head ((patList g₀ g₀.rules[ri])[k.val]?) from rfl, update_mkCell]
              · have hB : ((List.ofFn (Function.update W b.tape.head
                      ((patList g₀ g₀.rules[ri])[k.val]?))).drop (b.tape.head.val + 1)).filterMap id
                    = ((List.ofFn W₀).drop (b.tape.head.val + 1)).filterMap id := by
                  congr 1
                  apply List.ext_getElem (by simp)
                  intro j hj1 _
                  have hjb : b.tape.head.val + 1 + j < n + 1 := by
                    rw [List.length_drop, List.length_ofFn] at hj1; omega
                  rw [List.getElem_drop, List.getElem_drop, List.getElem_ofFn, List.getElem_ofFn,
                    Function.update_of_ne (show (⟨b.tape.head.val + 1 + j, hjb⟩ : Fin (n + 1))
                      ≠ b.tape.head from by rw [ne_eq, Fin.ext_iff]; simp only []; omega)]
                  exact hagree _ (by simp only []; omega)
                have hfW' : formW g₀ (Function.update W b.tape.head
                      ((patList g₀ g₀.rules[ri])[k.val]?))
                    = Aorig ++ patList g₀ g₀.rules[ri]
                      ++ ((List.ofFn W₀).drop (b.tape.head.val + 1)).filterMap id := by
                  rw [formW_split g₀ _ (b.tape.head.val + 1), hB]
                  congr 1
                  rw [take_succ_filterMap g₀ _ b.tape.head, Function.update_self, htkW'eq,
                    List.append_assoc, peel, List.take_of_length_le (by omega)]
                have hfW₀ : formW g₀ W₀ = Aorig ++ (g₀.rules[ri]).output_string
                    ++ ((List.ofFn W₀).drop (b.tape.head.val + 1)).filterMap id := by
                  rw [formW_split g₀ W₀ (b.tape.head.val + 1)]
                  congr 1
                  rw [take_succ_filterMap g₀ W₀ b.tape.head, htkW₀, hW₀h, List.append_assoc]
                  congr 1
                  rw [show ([some s].filterMap id)
                      = ([(g₀.rules[ri]).output_string[k.val]?].filterMap id) from by rw [hm], peel,
                    List.take_of_length_le (by omega)]
                rw [hfW']
                exact Relation.ReflTransGen.head
                  (grammar_transforms_patList g₀ (List.getElem_mem _) Aorig _) (hfW₀ ▸ hder)
            · rw [if_neg hk1, if_neg hk2] at hmem; simp at hmem
      · -- b = accept: no successor
        rw [hst] at hmem; simp [kTransition] at hmem

end Sound

/-- **Soundness of the simulator.** If the backward simulator accepts `w`, then the working
track passed through a valid (reverse) derivation, so `g₀` derives `w` from its start symbol. -/
theorem kMachine_sound [Fintype T] [DecidableEq T] (g₀ : grammar T)
    [Fintype g₀.nt] [DecidableEq g₀.nt] (hnc : grammar_noncontracting g₀) (w : List T) :
    LBA.LanguageViaEmbed (kMachine g₀) (fun t => some (Sum.inl t)) w → grammar_language g₀ w := by
  rintro ⟨hne, hAcc⟩
  set L := List.map (fun t => (some (Sum.inl t) : KCell g₀)) w with hL
  have hLlen : L.length = w.length := by rw [hL, List.length_map]
  have hLpos : 0 < L.length := List.length_pos_of_ne_nil hne
  set n := L.length - 1 with hn
  have hn1 : n + 1 = w.length := by omega
  have hbound : ∀ i : Fin (n + 1), i.val < w.length := fun i => by have := i.isLt; omega
  set input : Fin (n + 1) → T := fun i => w.get ⟨i.val, hbound i⟩ with hinput
  have htape : (LBA.loadList L hne).contents = cAt g₀ input 0 := by
    funext i
    simp only [LBA.loadList, cAt, Nat.not_lt_zero, if_false, hinput, hL,
      List.get_eq_getElem, List.getElem_map]
  have hbridge : LBA.initCfgList (kMachine g₀) L hne
      = (⟨KState.init0, ⟨cAt g₀ input 0, ⟨0, by omega⟩⟩⟩ : DLBA.Cfg (KCell g₀) (KState g₀) n) := by
    refine cfg_eq g₀ rfl htape (Fin.ext ?_)
    simp [LBA.loadList]
  obtain ⟨cfgacc, hreach, hacc⟩ := hAcc
  rw [hbridge] at hreach
  have hSC := sound_invariant g₀ hnc input cfgacc hreach
  have hst : cfgacc.state = KState.accept := by simpa [kMachine] using hacc
  have htgt : List.ofFn (fun k => (symbol.terminal (input k) : symbol T g₀.nt))
      = List.map symbol.terminal w := by
    apply List.ext_getElem
    · simp only [List.length_ofFn, List.length_map]; omega
    · intro j h1 _
      simp only [List.getElem_ofFn, List.getElem_map, hinput, List.get_eq_getElem]
  rcases hSC with ⟨h2, _, _⟩ | ⟨h2, _⟩ | ⟨_, _, h2, _⟩ | ⟨_, _, h2, _⟩ | ⟨_, _, _, h2, _, _⟩ |
    ⟨_, _, _, _, _, _, h2, _, _, _, _, _, _⟩ | ⟨W, _, _, hform, hder⟩
  · exact absurd (hst.symm.trans h2) (by simp)
  · exact absurd (hst.symm.trans h2) (by simp)
  · exact absurd (hst.symm.trans h2) (by simp)
  · exact absurd (hst.symm.trans h2) (by simp)
  · exact absurd (hst.symm.trans h2) (by simp)
  · exact absurd (hst.symm.trans h2) (by simp)
  · rw [hform, htgt] at hder; exact hder
end

end KurodaConstruction
