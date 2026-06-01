module

public import Langlib.Automata.LinearBounded.Equivalence.LBAToCSG
public import Langlib.Grammars.ContextSensitive.Toolbox
import Mathlib.Tactic
@[expose]
public section



/-!
# LBA → CS: configuration encoding and the run-induction skeleton

This file develops the **completeness** half of `myhill_language_eq`
(`Automata/LinearBounded/Equivalence/ContextSensitive.lean`): an accepting LBA run on `w`
is mirrored by a derivation `start ⇒* map terminal w` of the Myhill grammar.

The plan factors the derivation as

  `start  ⇒*  encode w₀ (initial cfg)`        -- `start_setup`
        `⇒*  encode w₀ cfg'`                   -- `CS_derives_of_reaches` + `step_sim`
        `⇒*  map terminal w`                   -- `cleanup`

where `encode` reifies an LBA configuration as a list of `cell` nonterminals (defined here),
and `CS_derives_of_reaches` (proved here) lifts the single-step simulation over an entire
reachable run by induction on `Relation.ReflTransGen`.

The three content lemmas `start_setup`, `step_sim`, `cleanup` (and the soundness direction)
are the remaining work; this file pins down the encoding and the glue they plug into.
-/

namespace MyhillConstruction

variable {T Γ Λ : Type} {n : ℕ}

/-- Encoding of an LBA configuration as a Myhill sentential form: one `cell` per tape
position, recording the boundary flags (`i = 0`, `i = n`), whether the head — and its
state — sits at that cell, the current tape symbol, and the frozen original terminal
`worig i`. -/
@[expose]
def encode (worig : Fin (n + 1) → T) (cfg : DLBA.Cfg Γ Λ n) :
    List (symbol T (MyhillNT T Γ Λ)) :=
  List.ofFn fun i => cellSym (decide (i.val = 0)) (decide (i.val = n))
    (if i = cfg.tape.head then some cfg.state else none)
    (cfg.tape.contents i) (worig i)

@[simp]
theorem encode_length (worig : Fin (n + 1) → T) (cfg : DLBA.Cfg Γ Λ n) :
    (encode worig cfg).length = n + 1 := by
  simp [encode]

/-- The `i`-th symbol of `encode` is the cell at position `i`. -/
theorem encode_getElem (worig : Fin (n + 1) → T) (cfg : DLBA.Cfg Γ Λ n)
    (i : ℕ) (hi : i < n + 1) :
    (encode worig cfg)[i]'(by simpa using hi) =
      cellSym (decide (i = 0)) (decide (i = n))
        (if (⟨i, hi⟩ : Fin (n + 1)) = cfg.tape.head then some cfg.state else none)
        (cfg.tape.contents ⟨i, hi⟩) (worig ⟨i, hi⟩) := by
  simp only [encode, List.getElem_ofFn]

/-- A head-stationary step (write `a'`, set state `q'`, head unchanged) updates exactly the
head cell of the encoding. -/
theorem encode_set_head (worig : Fin (n + 1) → T) (cfg : DLBA.Cfg Γ Λ n) (q' : Λ) (a' : Γ) :
    (encode worig cfg).set cfg.tape.head.val
        (cellSym (decide (cfg.tape.head.val = 0)) (decide (cfg.tape.head.val = n))
          (some q') a' (worig cfg.tape.head))
      = encode worig ⟨q', (cfg.tape.write a').moveHead DLBA.Dir.stay⟩ := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    have hin : i < n + 1 := by simpa using h2
    by_cases hi : cfg.tape.head.val = i
    · rw [List.getElem_set, if_pos hi, encode_getElem worig _ i hin]
      subst hi
      have hih : (⟨cfg.tape.head.val, hin⟩ : Fin (n + 1)) = cfg.tape.head := Fin.ext rfl
      simp [hih, DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead, Function.update_self]
    · rw [List.getElem_set, if_neg hi, encode_getElem worig cfg i hin,
        encode_getElem worig _ i hin]
      have hih : (⟨i, hin⟩ : Fin (n + 1)) ≠ cfg.tape.head := fun hc => hi (by rw [← hc])
      simp [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead,
        Function.update_of_ne hih, if_neg hih]

/-- **Run induction.** If a single LBA step is mirrored by a context-sensitive derivation of
the encodings, then so is any reachable run. Pure `ReflTransGen` induction — the engine that
turns the per-step simulation `step_sim` into the full `start ⇒* accepting` derivation. -/
theorem CS_derives_of_reaches (g : CS_grammar T) (M : LBA.Machine Γ Λ)
    (E : DLBA.Cfg Γ Λ n → List (symbol T g.nt))
    (hstep : ∀ c c', LBA.Step M c c' → CS_derives g (E c) (E c'))
    {c c' : DLBA.Cfg Γ Λ n} (h : LBA.Reaches M c c') :
    CS_derives g (E c) (E c') := by
  induction h with
  | refl => exact CS_deri_self
  | tail _ hlast ih => exact CS_deri_of_deri_deri ih (hstep _ _ hlast)

/-- Rewriting a single nonterminal `A` at position `k` to the output `[out]` of a
context-free-shaped rule `A → out` is one context-sensitive step (`List.set`). The engine
for the head-stationary cases of the step simulation. -/
theorem CS_transforms_of_set (g : CS_grammar T) (L : List (symbol T g.nt)) (k : ℕ)
    (hk : k < L.length) (A : g.nt) (out : symbol T g.nt)
    (hLk : L[k] = symbol.nonterminal A)
    (hrule : (⟨[], A, [], [out]⟩ : csrule T g.nt) ∈ g.rules) :
    CS_transforms g L (L.set k out) := by
  refine ⟨⟨[], A, [], [out]⟩, L.take k, L.drop (k + 1), hrule, ?_, ?_⟩
  · simp only [List.nil_append, List.append_nil]
    conv_lhs => rw [← List.take_append_drop k L, ← List.cons_getElem_drop_succ (h := hk)]
    rw [hLk]; simp
  · simp only [List.nil_append, List.append_nil]
    rw [List.set_eq_take_cons_drop out hk]; simp

/-- Split a list around two adjacent positions `k`, `k+1`. -/
theorem list_two_split {α : Type*} (L : List α) (k : ℕ) (hk : k + 1 < L.length) :
    L = L.take k ++ L[k] :: L[k + 1] :: L.drop (k + 2) := by
  conv_lhs => rw [← List.take_append_drop k L]
  congr 1
  rw [← List.cons_getElem_drop_succ (n := k) (h := by omega)]
  congr 1
  rw [← List.cons_getElem_drop_succ (n := k + 1) (h := hk)]

/-- Rewriting nonterminal `A` at position `k` to `[out]` with the *right neighbour* `L[k+1]`
as context is one context-sensitive step (`= L.set k out`). Drives interior step 1. -/
theorem CS_transforms_of_set_ctxR (g : CS_grammar T) (L : List (symbol T g.nt)) (k : ℕ)
    (hk : k + 1 < L.length) (A : g.nt) (out : symbol T g.nt)
    (hLk : L[k]'(by omega) = symbol.nonterminal A)
    (hrule : (⟨[], A, [L[k + 1]], [out]⟩ : csrule T g.nt) ∈ g.rules) :
    CS_transforms g L (L.set k out) := by
  refine ⟨⟨[], A, [L[k + 1]], [out]⟩, L.take k, L.drop (k + 2), hrule, ?_, ?_⟩
  · conv_lhs => rw [list_two_split L k hk, hLk]
    simp
  · rw [List.set_eq_take_cons_drop out (by omega : k < L.length)]
    conv_lhs => rw [show L.drop (k + 1) = L[k + 1] :: L.drop (k + 2) from
      (List.cons_getElem_drop_succ (n := k + 1) (h := hk)).symm]
    simp

/-- Rewriting nonterminal `A` at position `k+1` to `[out]` with the *left neighbour* `L[k]`
as context is one context-sensitive step (`= L.set (k+1) out`). Drives interior step 2. -/
theorem CS_transforms_of_set_ctxL (g : CS_grammar T) (L : List (symbol T g.nt)) (k : ℕ)
    (hk : k + 1 < L.length) (A : g.nt) (out : symbol T g.nt)
    (hLk1 : L[k + 1]'hk = symbol.nonterminal A)
    (hrule : (⟨[L[k]'(by omega)], A, [], [out]⟩ : csrule T g.nt) ∈ g.rules) :
    CS_transforms g L (L.set (k + 1) out) := by
  refine ⟨⟨[L[k]'(by omega)], A, [], [out]⟩, L.take k, L.drop (k + 2), hrule, ?_, ?_⟩
  · conv_lhs => rw [list_two_split L k hk, hLk1]
    simp only [List.singleton_append, List.nil_append, List.append_nil, List.append_assoc,
      List.cons_append]
  · rw [List.set_eq_take_cons_drop out hk, ← List.take_concat_get' L k (by omega)]
    simp only [List.singleton_append, List.nil_append, List.append_nil, List.append_assoc,
      List.cons_append]

/-- Two-sided context rewrite at position `j+1` (`= L.set (j+1) out`). -/
theorem CS_transforms_of_set_ctxLR (g : CS_grammar T) (L : List (symbol T g.nt)) (j : ℕ)
    (hj : j + 2 < L.length) (A : g.nt) (out : symbol T g.nt)
    (hLk : L[j + 1]'(by omega) = symbol.nonterminal A)
    (hrule : (⟨[L[j]'(by omega)], A, [L[j + 2]'hj], [out]⟩ : csrule T g.nt) ∈ g.rules) :
    CS_transforms g L (L.set (j + 1) out) := by
  refine ⟨⟨[L[j]'(by omega)], A, [L[j + 2]'hj], [out]⟩, L.take j, L.drop (j + 3), hrule, ?_, ?_⟩
  · conv_lhs => rw [list_two_split L j (by omega),
      show L.drop (j + 2) = L[j + 2] :: L.drop (j + 3) from
        (List.cons_getElem_drop_succ (n := j + 2) (h := hj)).symm, hLk]
    simp only [List.singleton_append, List.nil_append, List.append_nil, List.append_assoc,
      List.cons_append]
  · rw [List.set_eq_take_cons_drop out (by omega : j + 1 < L.length),
      ← List.take_concat_get' L j (by omega),
      show L.drop (j + 2) = L[j + 2] :: L.drop (j + 3) from
        (List.cons_getElem_drop_succ (n := j + 2) (h := hj)).symm]
    simp only [List.singleton_append, List.nil_append, List.append_nil, List.append_assoc,
      List.cons_append]

/-- Two-sided context rewrite at position `k ≥ 1` (`= L.set k out`); avoids `j+1` mismatch. -/
theorem CS_transforms_of_set_ctxLR_k (g : CS_grammar T) (L : List (symbol T g.nt)) (k : ℕ)
    (hk0 : 0 < k) (hk : k + 1 < L.length) (A : g.nt) (out : symbol T g.nt)
    (hLk : L[k]'(by omega) = symbol.nonterminal A)
    (hrule : (⟨[L[k - 1]'(by omega)], A, [L[k + 1]'hk], [out]⟩ : csrule T g.nt) ∈ g.rules) :
    CS_transforms g L (L.set k out) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hrule
  exact CS_transforms_of_set_ctxLR g L j (by omega) A out hLk hrule

theorem CS_tran_with_prefix {g : CS_grammar T} {p w₁ w₂ : List (symbol T g.nt)}
    (h : CS_transforms g w₁ w₂) : CS_transforms g (p ++ w₁) (p ++ w₂) := by
  obtain ⟨r, u, v, hr, hb, ha⟩ := h
  exact ⟨r, p ++ u, v, hr, by rw [hb]; simp [List.append_assoc],
    by rw [ha]; simp [List.append_assoc]⟩

theorem CS_deri_with_prefix {g : CS_grammar T} {p w₁ w₂ : List (symbol T g.nt)}
    (h : CS_derives g w₁ w₂) : CS_derives g (p ++ w₁) (p ++ w₂) := by
  induction h with
  | refl => exact CS_deri_self
  | tail _ step ih => exact CS_deri_of_deri_tran ih (CS_tran_with_prefix step)

theorem CS_tran_with_postfix {g : CS_grammar T} {s w₁ w₂ : List (symbol T g.nt)}
    (h : CS_transforms g w₁ w₂) : CS_transforms g (w₁ ++ s) (w₂ ++ s) := by
  obtain ⟨r, u, v, hr, hb, ha⟩ := h
  exact ⟨r, u, v ++ s, hr, by rw [hb]; simp [List.append_assoc],
    by rw [ha]; simp [List.append_assoc]⟩

theorem CS_deri_with_postfix {g : CS_grammar T} {s w₁ w₂ : List (symbol T g.nt)}
    (h : CS_derives g w₁ w₂) : CS_derives g (w₁ ++ s) (w₂ ++ s) := by
  induction h with
  | refl => exact CS_deri_self
  | tail _ step ih => exact CS_deri_of_deri_tran ih (CS_tran_with_postfix step)

/-! ### Start phase: the `startAux` nonterminal lays down the non-head cells -/

variable [Fintype T] [Fintype Γ] [Fintype Λ]
variable [DecidableEq T] [DecidableEq Γ] [DecidableEq Λ]

/-- The interior/last cells produced by the `startAux` rules for an input list: every cell
carries `lb = false` and `q = none`; only the final cell carries `rb = true`. -/
def auxCells (embed : T → Γ) : List T → List (symbol T (MyhillNT T Γ Λ))
  | [] => []
  | [t] => [cellSym false true none (embed t) t]
  | t :: t' :: rest => cellSym false false none (embed t) t :: auxCells embed (t' :: rest)

@[simp]
theorem auxCells_length (embed : T → Γ) (ts : List T) :
    (auxCells (Λ := Λ) embed ts).length = ts.length := by
  induction ts with
  | nil => rfl
  | cons t rest ih =>
      cases rest with
      | nil => rfl
      | cons t' rest' => simp [auxCells, ih]

/-- Unfolding `auxCells` on a cons whose tail is non-empty (`a :: l` matches clause 3). -/
theorem auxCells_cons (embed : T → Γ) (a : T) (l : List T) (hl : l ≠ []) :
    auxCells (Λ := Λ) embed (a :: l) = cellSym false false none (embed a) a :: auxCells embed l := by
  cases l with
  | nil => exact absurd rfl hl
  | cons t' rest => rfl

/-- `auxCells` of an `ofFn` list is the positional `ofFn` of the corresponding cells:
`lb = false`, `q = none`, `rb = (i = m)`. -/
theorem auxCells_ofFn (embed : T → Γ) :
    ∀ {m : ℕ} (worig : Fin (m + 1) → T),
      auxCells (Λ := Λ) embed (List.ofFn worig) =
        List.ofFn (fun i : Fin (m + 1) =>
          cellSym false (decide (i.val = m)) none (embed (worig i)) (worig i))
  | 0, worig => by simp [auxCells, List.ofFn_succ, List.ofFn_zero]
  | m + 1, worig => by
      have htail : List.ofFn (fun i : Fin (m + 1) => worig i.succ) ≠ [] :=
        List.ne_nil_of_length_pos (by simp)
      rw [List.ofFn_succ, auxCells_cons embed _ _ htail,
        auxCells_ofFn embed (fun i => worig i.succ)]
      conv_rhs => rw [List.ofFn_succ]
      refine congr_arg₂ List.cons ?_ ?_
      · simp
      · refine congrArg List.ofFn (funext fun i => ?_)
        have h : decide ((i.succ : Fin (m + 2)).val = m + 1) = decide ((i : Fin (m + 1)).val = m) := by
          rw [Fin.val_succ]; exact decide_eq_decide.mpr (by omega)
        rw [h]

/-- **Right-to-left middle build.** Starting from `startAux :: tail`, repeatedly applying the
middle-cell rule (`startAux → [startAux, cell]`) lays the `none` cells for `mids` immediately to
the right of `startAux`, in order. Applying the inductive hypothesis *first* (building `ts` to
the right) and the head step *last* keeps the cells in position order with no reversal. -/
theorem preRow (M : LBA.Machine Γ Λ) (embed : T ↪ Γ) (mids : List T)
    (tail : List (symbol T (MyhillNT T Γ Λ))) :
    CS_derives (myhillGrammar M embed)
      (symbol.nonterminal MyhillNT.startAux :: tail)
      (symbol.nonterminal MyhillNT.startAux ::
        mids.map (fun t => cellSym false false none (embed t) t) ++ tail) := by
  induction mids with
  | nil => simpa using Relation.ReflTransGen.refl
  | cons t ts ih =>
      refine Relation.ReflTransGen.tail ih ?_
      exact ⟨⟨[], MyhillNT.startAux, [],
          [symbol.nonterminal MyhillNT.startAux, cellSym false false none (embed t) t]⟩,
        [], ts.map (fun t => cellSym false false none (embed t) t) ++ tail,
        middle_cell_init_rule_mem M embed t, by simp, by simp⟩

/-- `auxCells` splits as the `none`-cells for all but the last input, followed by the single
`rb = true` cell for the last input. This is the shape produced by the right-to-left build:
the rightmost cell comes from the `start` rule, the middles from `preRow`. -/
theorem auxCells_split (embed : T → Γ) (tl : List T) (h : tl ≠ []) :
    auxCells (Λ := Λ) embed tl
      = (tl.dropLast).map (fun t => cellSym false false none (embed t) t)
        ++ [cellSym false true none (embed (tl.getLast h)) (tl.getLast h)] := by
  induction tl with
  | nil => exact absurd rfl h
  | cons a rest ih =>
      cases rest with
      | nil => simp [auxCells]
      | cons b rest' =>
          rw [auxCells_cons embed a (b :: rest') (by simp), ih (by simp)]
          simp [List.dropLast_cons₂, List.getLast_cons]

/-- The full initial sentential form: the head cell (`lb = true`, state `M.initial`) at
position 0, followed by `auxCells` for the rest of the input. -/
def startCells (M : LBA.Machine Γ Λ) (embed : T → Γ) :
    List T → List (symbol T (MyhillNT T Γ Λ))
  | [] => []
  | [t] => [cellSym true true (some M.initial) (embed t) t]
  | t :: t' :: rest =>
      cellSym true false (some M.initial) (embed t) t :: auxCells embed (t' :: rest)

@[simp]
theorem startCells_length (M : LBA.Machine Γ Λ) (embed : T → Γ) (ts : List T) :
    (startCells M embed ts).length = ts.length := by
  cases ts with
  | nil => rfl
  | cons t rest =>
      cases rest with
      | nil => rfl
      | cons t' rest' => simp [startCells, auxCells_length]

/-- **Start phase.** `start ⇒* startCells ts` for any non-empty input list `ts`; this is the
initial sentential form encoding the LBA's initial configuration on `ts`. -/
theorem start_phase (M : LBA.Machine Γ Λ) (embed : T ↪ Γ) (ts : List T) (h : ts ≠ []) :
    CS_derives (myhillGrammar M embed)
      [symbol.nonterminal MyhillNT.start] (startCells M embed ts) := by
  cases ts with
  | nil => exact absurd rfl h
  | cons t rest =>
      cases rest with
      | nil =>
          -- single cell: one `start → [head cell]` step
          apply CS_deri_of_tran
          exact ⟨⟨[], MyhillNT.start, [], [cellSym true true (some M.initial) (embed t) t]⟩,
            [], [], single_cell_init_rule_mem M embed t, by simp, by simp [startCells]⟩
      | cons t' rest' =>
          -- multi-cell: lay the rightmost cell, build the middles, then lay the head cell.
          have htlne : (t' :: rest') ≠ [] := by simp
          set last := (t' :: rest').getLast htlne with hlastdef
          -- `start ⇒ [startAux, rightCell]`
          refine CS_deri_of_tran_deri
            (v := [symbol.nonterminal MyhillNT.startAux,
                   cellSym false true none (embed last) last])
            ⟨⟨[], MyhillNT.start, [],
                [symbol.nonterminal MyhillNT.startAux,
                 cellSym false true none (embed last) last]⟩,
              [], [], right_cell_init_rule_mem M embed last, by simp, by simp⟩ ?_
          -- `[startAux, rightCell] ⇒* [startAux] ++ mids.map ++ [rightCell] ⇒ headCell :: …`
          refine Relation.ReflTransGen.tail
            (preRow M embed ((t' :: rest').dropLast)
              [cellSym false true none (embed last) last]) ?_
          refine ⟨⟨[], MyhillNT.startAux, [],
              [cellSym true false (some M.initial) (embed t) t]⟩,
            [], ((t' :: rest').dropLast).map (fun t => cellSym false false none (embed t) t)
                ++ [cellSym false true none (embed last) last],
            left_cell_init_rule_mem M embed t, by simp, ?_⟩
          -- the result equals `startCells (t :: t' :: rest')`
          simp only [startCells, List.nil_append, List.singleton_append, List.cons_append]
          rw [auxCells_split (Λ := Λ) embed (t' :: rest') htlne, ← hlastdef]

/-- Unfolding `startCells` on a cons whose tail is non-empty (`a :: l` matches clause 3). -/
theorem startCells_cons (M : LBA.Machine Γ Λ) (embed : T → Γ) (a : T) (l : List T)
    (hl : l ≠ []) :
    startCells M embed (a :: l)
      = cellSym true false (some M.initial) (embed a) a :: auxCells embed l := by
  cases l with
  | nil => exact absurd rfl hl
  | cons t' rest => rfl

/-- **Start-phase bridge.** The cons-list `startCells` equals the positional `encode` of the
initial configuration (head at `0`, state `M.initial`, tape `embed ∘ worig`). This connects
`start_phase` to the `encode`-based run simulation. -/
theorem startCells_eq_encode (M : LBA.Machine Γ Λ) (embed : T → Γ) {m : ℕ}
    (worig : Fin (m + 1) → T) :
    startCells M embed (List.ofFn worig)
      = encode worig ⟨M.initial, ⟨fun i => embed (worig i), ⟨0, Nat.succ_pos m⟩⟩⟩ := by
  unfold encode
  cases m with
  | zero => simp [startCells, List.ofFn_succ, List.ofFn_zero]
  | succ k =>
      have htail : List.ofFn (fun i : Fin (k + 1) => worig i.succ) ≠ [] :=
        List.ne_nil_of_length_pos (by simp)
      rw [List.ofFn_succ, startCells_cons M embed _ _ htail,
        auxCells_ofFn embed (fun i => worig i.succ)]
      conv_rhs => rw [List.ofFn_succ]
      refine congr_arg₂ List.cons ?_ ?_
      · simp
      · refine congrArg List.ofFn (funext fun i => ?_)
        have e1 : decide ((i.succ : Fin (k + 2)).val = 0) = false := by
          rw [Fin.val_succ]; exact decide_eq_false (by omega)
        have e2 : decide ((i.succ : Fin (k + 2)).val = k + 1)
            = decide ((i : Fin (k + 1)).val = k) := by
          rw [Fin.val_succ]; exact decide_eq_decide.mpr (by omega)
        have e3 : (if (i.succ : Fin (k + 2)) = ⟨0, Nat.succ_pos (k + 1)⟩
            then some M.initial else none) = none := by
          apply if_neg
          intro hc
          have hv : (i.succ : Fin (k + 2)).val = 0 := congrArg Fin.val hc
          rw [Fin.val_succ] at hv
          omega
        rw [e1, e2, e3]

/-! ### Step simulation: the `stay` case -/

/-- **`step_sim`, stay case.** A `stay` transition of the LBA is mirrored by a single
context-sensitive derivation step on the encodings (rewrite the head cell in place). -/
theorem step_sim_stay (M : LBA.Machine Γ Λ) (embed : T ↪ Γ) (worig : Fin (n + 1) → T)
    (cfg : DLBA.Cfg Γ Λ n) (q' : Λ) (a' : Γ)
    (htrans : (q', a', DLBA.Dir.stay) ∈ M.transition cfg.state cfg.tape.read) :
    CS_derives (myhillGrammar M embed) (encode worig cfg)
      (encode worig ⟨q', (cfg.tape.write a').moveHead DLBA.Dir.stay⟩) := by
  rw [← encode_set_head worig cfg q' a']
  apply CS_deri_of_tran
  have hk : cfg.tape.head.val < (encode worig cfg).length := by
    rw [encode_length]; exact cfg.tape.head.isLt
  have hLk : (encode worig cfg)[cfg.tape.head.val]'hk
      = symbol.nonterminal (MyhillNT.cell (decide (cfg.tape.head.val = 0))
          (decide (cfg.tape.head.val = n)) (some cfg.state) cfg.tape.read
          (worig cfg.tape.head)) := by
    rw [encode_getElem worig cfg cfg.tape.head.val cfg.tape.head.isLt]
    have he : (⟨cfg.tape.head.val, cfg.tape.head.isLt⟩ : Fin (n + 1)) = cfg.tape.head :=
      Fin.ext rfl
    rw [he, if_pos rfl]; rfl
  exact CS_transforms_of_set (myhillGrammar M embed) (encode worig cfg) cfg.tape.head.val hk
    _ _ hLk (sim_stay_rule_mem M embed cfg.state q' cfg.tape.read a' (worig cfg.tape.head)
      (decide (cfg.tape.head.val = 0)) (decide (cfg.tape.head.val = n)) htrans)

/-- Moving right at the right boundary is clamped (no movement). -/
theorem moveHead_right_at_right (t : DLBA.BoundedTape Γ n) (hb : t.head.val = n) :
    t.moveHead DLBA.Dir.right = t := by
  simp [DLBA.BoundedTape.moveHead, hb]

/-- Moving left at the left boundary is clamped (no movement). -/
theorem moveHead_left_at_left (t : DLBA.BoundedTape Γ n) (hb : t.head.val = 0) :
    t.moveHead DLBA.Dir.left = t := by
  simp [DLBA.BoundedTape.moveHead, hb]

/-- A `stay` move leaves the tape unchanged. -/
theorem moveHead_stay (t : DLBA.BoundedTape Γ n) : t.moveHead DLBA.Dir.stay = t := by
  simp [DLBA.BoundedTape.moveHead]

/-- `moveHead` never changes the tape contents. -/
theorem moveHead_contents (t : DLBA.BoundedTape Γ n) (d : DLBA.Dir) :
    (t.moveHead d).contents = t.contents := by
  cases d <;> rfl

/-- An interior `right` move increments the head position. -/
theorem moveHead_right_head_lt (t : DLBA.BoundedTape Γ n) (h : t.head.val < n) :
    (t.moveHead DLBA.Dir.right).head.val = t.head.val + 1 := by
  simp [DLBA.BoundedTape.moveHead, h]

/-- An interior `left` move decrements the head position. -/
theorem moveHead_left_head_pos (t : DLBA.BoundedTape Γ n) (h : 0 < t.head.val) :
    (t.moveHead DLBA.Dir.left).head.val = t.head.val - 1 := by
  simp [DLBA.BoundedTape.moveHead, h]

/-- An interior `right` step changes exactly the head cell (head leaves, symbol `a'` written)
and its right neighbour (head arrives with state `q'`). -/
theorem encode_right_interior (worig : Fin (n + 1) → T) (cfg : DLBA.Cfg Γ Λ n) (q' : Λ) (a' : Γ)
    (hlt : cfg.tape.head.val < n) :
    encode worig ⟨q', (cfg.tape.write a').moveHead DLBA.Dir.right⟩
      = ((encode worig cfg).set cfg.tape.head.val
          (cellSym (decide (cfg.tape.head.val = 0)) false none a' (worig cfg.tape.head))).set
          (cfg.tape.head.val + 1)
          (cellSym false (decide (cfg.tape.head.val + 1 = n)) (some q')
            (cfg.tape.contents ⟨cfg.tape.head.val + 1, by omega⟩)
            (worig ⟨cfg.tape.head.val + 1, by omega⟩)) := by
  have hwh : (cfg.tape.write a').head = cfg.tape.head := rfl
  have hheadeq : ((cfg.tape.write a').moveHead DLBA.Dir.right).head
      = (⟨cfg.tape.head.val + 1, by omega⟩ : Fin (n + 1)) := by
    apply Fin.ext
    rw [moveHead_right_head_lt (cfg.tape.write a') (by rw [hwh]; exact hlt), hwh]
  have hcont : ((cfg.tape.write a').moveHead DLBA.Dir.right).contents
      = Function.update cfg.tape.contents cfg.tape.head a' := by
    rw [moveHead_contents]; rfl
  apply List.ext_getElem
  · simp
  · intro i hi1 _
    have hin : i < n + 1 := by simpa using hi1
    rw [encode_getElem worig _ i hin, List.getElem_set, List.getElem_set,
      encode_getElem worig cfg i hin, hheadeq, hcont, Function.update_apply]
    simp only [Fin.ext_iff]
    rcases eq_or_ne i (cfg.tape.head.val + 1) with rfl | e1
    · simp [show cfg.tape.head.val + 1 ≠ cfg.tape.head.val from by omega]
    · rcases eq_or_ne i cfg.tape.head.val with rfl | e2
      · simp [show cfg.tape.head.val ≠ cfg.tape.head.val + 1 from by omega,
          show ¬ cfg.tape.head.val = n from by omega]
      · simp [e1, e2, Ne.symm e1, Ne.symm e2]

/-- An interior `left` step changes exactly the head cell (at `m+1`; head leaves, symbol `a'`
written) and its left neighbour (at `m`; head arrives with state `q'`). Stated with
`head = m + 1` so the indices `m`, `m+1` match the three-step assembly. -/
theorem encode_left_interior (worig : Fin (n + 1) → T) (cfg : DLBA.Cfg Γ Λ n) (q' : Λ) (a' : Γ)
    (m : ℕ) (hm : cfg.tape.head.val = m + 1) :
    encode worig ⟨q', (cfg.tape.write a').moveHead DLBA.Dir.left⟩
      = ((encode worig cfg).set (m + 1)
          (cellSym false (decide (m + 1 = n)) none a' (worig cfg.tape.head))).set m
          (cellSym (decide (m = 0)) false (some q')
            (cfg.tape.contents ⟨m, by omega⟩) (worig ⟨m, by omega⟩)) := by
  have hle : cfg.tape.head.val < n + 1 := cfg.tape.head.isLt
  have hwh : (cfg.tape.write a').head = cfg.tape.head := rfl
  have hheadeq : ((cfg.tape.write a').moveHead DLBA.Dir.left).head
      = (⟨m, by omega⟩ : Fin (n + 1)) := by
    apply Fin.ext
    show ((cfg.tape.write a').moveHead DLBA.Dir.left).head.val = m
    rw [moveHead_left_head_pos (cfg.tape.write a') (by rw [hwh]; omega), hwh]
    omega
  have hcont : ((cfg.tape.write a').moveHead DLBA.Dir.left).contents
      = Function.update cfg.tape.contents cfg.tape.head a' := by
    rw [moveHead_contents]; rfl
  apply List.ext_getElem
  · simp
  · intro i hi1 _
    have hin : i < n + 1 := by simpa using hi1
    rw [encode_getElem worig _ i hin, List.getElem_set, List.getElem_set,
      encode_getElem worig cfg i hin, hheadeq, hcont, Function.update_apply]
    simp only [Fin.ext_iff, hm]
    by_cases h1 : i = m
    · simp [h1, show m ≠ m + 1 from by omega, show ¬ m = n from by omega]
    · by_cases h2 : i = m + 1
      · simp [h2, show m + 1 ≠ m from by omega,
          show (⟨m + 1, by omega⟩ : Fin (n + 1)) = cfg.tape.head from Fin.ext (by simp [hm])]
      · simp [h1, h2, Ne.symm h1, Ne.symm h2]

/-- **`step_sim`, right-interior case.** An interior `right` transition is mirrored by the
three-step `cellPending` protocol: park the head as a `cellPending`, place the new state on
the right neighbour, then resolve the pending cell. -/
theorem step_sim_right_interior (M : LBA.Machine Γ Λ) (embed : T ↪ Γ) (worig : Fin (n + 1) → T)
    (cfg : DLBA.Cfg Γ Λ n) (q' : Λ) (a' : Γ) (hlt : cfg.tape.head.val < n)
    (htrans : (q', a', DLBA.Dir.right) ∈ M.transition cfg.state cfg.tape.read) :
    CS_derives (myhillGrammar M embed) (encode worig cfg)
      (encode worig ⟨q', (cfg.tape.write a').moveHead DLBA.Dir.right⟩) := by
  have hk1 : cfg.tape.head.val + 1 < (encode worig cfg).length := by rw [encode_length]; omega
  have hk0 : cfg.tape.head.val < (encode worig cfg).length := by rw [encode_length]; omega
  have hne : cfg.tape.head.val ≠ cfg.tape.head.val + 1 := by omega
  -- the head cell and its right neighbour
  have hEh : (encode worig cfg)[cfg.tape.head.val]'hk0
      = symbol.nonterminal (MyhillNT.cell (decide (cfg.tape.head.val = 0)) false
          (some cfg.state) cfg.tape.read (worig cfg.tape.head)) := by
    rw [encode_getElem worig cfg cfg.tape.head.val cfg.tape.head.isLt,
      show (⟨cfg.tape.head.val, cfg.tape.head.isLt⟩ : Fin (n + 1)) = cfg.tape.head from Fin.ext rfl,
      if_pos rfl, decide_eq_false (show ¬ cfg.tape.head.val = n by omega)]
    rfl
  have hEh1 : (encode worig cfg)[cfg.tape.head.val + 1]'hk1
      = cellSym false (decide (cfg.tape.head.val + 1 = n)) none
          (cfg.tape.contents ⟨cfg.tape.head.val + 1, by omega⟩)
          (worig ⟨cfg.tape.head.val + 1, by omega⟩) := by
    rw [encode_getElem worig cfg (cfg.tape.head.val + 1) (by omega),
      if_neg (show (⟨cfg.tape.head.val + 1, by omega⟩ : Fin (n + 1)) ≠ cfg.tape.head by
        rw [Ne, Fin.ext_iff]; simp)]
    rfl
  -- Step 1: park the head into a `cellPending`; gated rules block `cellPending` stacking.
  have step1 : CS_transforms (myhillGrammar M embed) (encode worig cfg)
      ((encode worig cfg).set cfg.tape.head.val
        (cellPendingSym (decide (cfg.tape.head.val = 0)) false true q' a' (worig cfg.tape.head))) := by
    rcases Nat.eq_zero_or_pos cfg.tape.head.val with h0 | hpos
    · -- head at left boundary: no left context
      have hd0 : decide (cfg.tape.head.val = 0) = true := by simp [h0]
      have hEhb : (encode worig cfg)[cfg.tape.head.val]'hk0
          = symbol.nonterminal (MyhillNT.cell true false (some cfg.state) cfg.tape.read
              (worig cfg.tape.head)) := by rw [hEh, hd0]
      have hrule1 := sim_right_interior_step1_boundary_mem M embed cfg.state q' cfg.tape.read a'
        (worig cfg.tape.head) (worig ⟨cfg.tape.head.val + 1, by omega⟩)
        (decide (cfg.tape.head.val + 1 = n)) none
        (cfg.tape.contents ⟨cfg.tape.head.val + 1, by omega⟩) htrans
      rw [← hEh1] at hrule1
      rw [hd0]
      exact CS_transforms_of_set_ctxR (myhillGrammar M embed) (encode worig cfg)
        cfg.tape.head.val hk1 _ _ hEhb hrule1
    · -- interior head: left neighbour as context
      have hd0 : decide (cfg.tape.head.val = 0) = false := decide_eq_false (by omega)
      have hEhi : (encode worig cfg)[cfg.tape.head.val]'hk0
          = symbol.nonterminal (MyhillNT.cell false false (some cfg.state) cfg.tape.read
              (worig cfg.tape.head)) := by rw [hEh, hd0]
      have hEhm1 : (encode worig cfg)[cfg.tape.head.val - 1]'(by rw [encode_length]; omega)
          = cellSym (decide (cfg.tape.head.val - 1 = 0)) false none
              (cfg.tape.contents ⟨cfg.tape.head.val - 1, by omega⟩)
              (worig ⟨cfg.tape.head.val - 1, by omega⟩) := by
        rw [encode_getElem worig cfg (cfg.tape.head.val - 1) (by omega),
          if_neg (show (⟨cfg.tape.head.val - 1, by omega⟩ : Fin (n + 1)) ≠ cfg.tape.head by
            simp only [Ne, Fin.ext_iff]; omega),
          decide_eq_false (show ¬ cfg.tape.head.val - 1 = n by omega)]
      have hrule1 := sim_right_interior_step1_interior_mem M embed cfg.state q' cfg.tape.read a'
        (worig cfg.tape.head) (worig ⟨cfg.tape.head.val + 1, by omega⟩)
        (decide (cfg.tape.head.val + 1 = n)) none
        (cfg.tape.contents ⟨cfg.tape.head.val + 1, by omega⟩)
        (decide (cfg.tape.head.val - 1 = 0))
        (cfg.tape.contents ⟨cfg.tape.head.val - 1, by omega⟩)
        (worig ⟨cfg.tape.head.val - 1, by omega⟩) htrans
      rw [← hEh1, ← hEhm1] at hrule1
      rw [hd0]
      exact CS_transforms_of_set_ctxLR_k (myhillGrammar M embed) (encode worig cfg)
        cfg.tape.head.val hpos hk1 _ _ hEhi hrule1
  -- Step 2: place the new state on the right neighbour (pending cell as left context).
  have hL2h : ((encode worig cfg).set cfg.tape.head.val
      (cellPendingSym (decide (cfg.tape.head.val = 0)) false true q' a' (worig cfg.tape.head)))[
        cfg.tape.head.val]'(by rw [List.length_set]; exact hk0)
      = cellPendingSym (decide (cfg.tape.head.val = 0)) false true q' a' (worig cfg.tape.head) :=
    List.getElem_set_self ..
  have hL2h1 : ((encode worig cfg).set cfg.tape.head.val
      (cellPendingSym (decide (cfg.tape.head.val = 0)) false true q' a' (worig cfg.tape.head)))[
        cfg.tape.head.val + 1]'(by rw [List.length_set]; exact hk1)
      = symbol.nonterminal (MyhillNT.cell false (decide (cfg.tape.head.val + 1 = n)) none
          (cfg.tape.contents ⟨cfg.tape.head.val + 1, by omega⟩)
          (worig ⟨cfg.tape.head.val + 1, by omega⟩)) := by
    rw [List.getElem_set_ne (by omega), hEh1]
  have hrule2 := sim_right_interior_step2_mem M embed q' a' (worig cfg.tape.head)
    (worig ⟨cfg.tape.head.val + 1, by omega⟩) (decide (cfg.tape.head.val = 0))
    (decide (cfg.tape.head.val + 1 = n))
    (cfg.tape.contents ⟨cfg.tape.head.val + 1, by omega⟩)
  rw [← hL2h] at hrule2
  have step2 := CS_transforms_of_set_ctxL (myhillGrammar M embed)
    ((encode worig cfg).set cfg.tape.head.val
      (cellPendingSym (decide (cfg.tape.head.val = 0)) false true q' a' (worig cfg.tape.head)))
    cfg.tape.head.val (by rw [List.length_set]; exact hk1) _ _ hL2h1 hrule2
  -- Step 3: resolve the pending cell.
  have hL3h : (((encode worig cfg).set cfg.tape.head.val
        (cellPendingSym (decide (cfg.tape.head.val = 0)) false true q' a' (worig cfg.tape.head))).set
        (cfg.tape.head.val + 1)
        (cellSym false (decide (cfg.tape.head.val + 1 = n)) (some q')
          (cfg.tape.contents ⟨cfg.tape.head.val + 1, by omega⟩)
          (worig ⟨cfg.tape.head.val + 1, by omega⟩)))[cfg.tape.head.val]'(by
        rw [List.length_set, List.length_set]; exact hk0)
      = symbol.nonterminal (MyhillNT.cellPending (decide (cfg.tape.head.val = 0)) false true q' a'
          (worig cfg.tape.head)) := by
    rw [List.getElem_set_ne (by omega), List.getElem_set_self]
  have step3 := CS_transforms_of_set (myhillGrammar M embed)
    (((encode worig cfg).set cfg.tape.head.val
        (cellPendingSym (decide (cfg.tape.head.val = 0)) false true q' a' (worig cfg.tape.head))).set
        (cfg.tape.head.val + 1)
        (cellSym false (decide (cfg.tape.head.val + 1 = n)) (some q')
          (cfg.tape.contents ⟨cfg.tape.head.val + 1, by omega⟩)
          (worig ⟨cfg.tape.head.val + 1, by omega⟩)))
    cfg.tape.head.val (by rw [List.length_set, List.length_set]; exact hk0) _ _ hL3h
    (pending_resolution_rule_mem M embed q' a' (worig cfg.tape.head)
      (decide (cfg.tape.head.val = 0)) false true)
  -- Assemble the chain and match `encode_right_interior`.
  rw [encode_right_interior worig cfg q' a' hlt]
  have key : (((encode worig cfg).set cfg.tape.head.val
        (cellPendingSym (decide (cfg.tape.head.val = 0)) false true q' a' (worig cfg.tape.head))).set
        (cfg.tape.head.val + 1)
        (cellSym false (decide (cfg.tape.head.val + 1 = n)) (some q')
          (cfg.tape.contents ⟨cfg.tape.head.val + 1, by omega⟩)
          (worig ⟨cfg.tape.head.val + 1, by omega⟩))).set cfg.tape.head.val
        (cellSym (decide (cfg.tape.head.val = 0)) false none a' (worig cfg.tape.head))
      = ((encode worig cfg).set cfg.tape.head.val
          (cellSym (decide (cfg.tape.head.val = 0)) false none a' (worig cfg.tape.head))).set
          (cfg.tape.head.val + 1)
          (cellSym false (decide (cfg.tape.head.val + 1 = n)) (some q')
            (cfg.tape.contents ⟨cfg.tape.head.val + 1, by omega⟩)
            (worig ⟨cfg.tape.head.val + 1, by omega⟩)) := by
    rw [List.set_comm _ _ (by omega : cfg.tape.head.val + 1 ≠ cfg.tape.head.val), List.set_set]
  rw [← key]
  exact CS_deri_of_deri_deri (CS_deri_of_tran step1)
    (CS_deri_of_deri_deri (CS_deri_of_tran step2) (CS_deri_of_tran step3))

/-- **`step_sim`, left-interior case.** Mirror of the right-interior case. -/
theorem step_sim_left_interior (M : LBA.Machine Γ Λ) (embed : T ↪ Γ) (worig : Fin (n + 1) → T)
    (cfg : DLBA.Cfg Γ Λ n) (q' : Λ) (a' : Γ) (hpos : 0 < cfg.tape.head.val)
    (htrans : (q', a', DLBA.Dir.left) ∈ M.transition cfg.state cfg.tape.read) :
    CS_derives (myhillGrammar M embed) (encode worig cfg)
      (encode worig ⟨q', (cfg.tape.write a').moveHead DLBA.Dir.left⟩) := by
  obtain ⟨m, hm⟩ : ∃ m, cfg.tape.head.val = m + 1 := ⟨cfg.tape.head.val - 1, by omega⟩
  have hle : cfg.tape.head.val < n + 1 := cfg.tape.head.isLt
  have hkm : m < (encode worig cfg).length := by rw [encode_length]; omega
  have hkh : m + 1 < (encode worig cfg).length := by rw [encode_length]; omega
  have hne : m + 1 ≠ m := by omega
  -- the head cell (at `m+1`) and its left neighbour (at `m`)
  have hEh : (encode worig cfg)[m + 1]'hkh
      = symbol.nonterminal (MyhillNT.cell false (decide (m + 1 = n))
          (some cfg.state) cfg.tape.read (worig cfg.tape.head)) := by
    rw [encode_getElem worig cfg (m + 1) (by omega),
      if_pos (show (⟨m + 1, by omega⟩ : Fin (n + 1)) = cfg.tape.head from Fin.ext (by simp [hm])),
      show cfg.tape.contents ⟨m + 1, by omega⟩ = cfg.tape.read from by
        rw [DLBA.BoundedTape.read,
          show (⟨m + 1, by omega⟩ : Fin (n + 1)) = cfg.tape.head from Fin.ext (by simp [hm])],
      show worig ⟨m + 1, by omega⟩ = worig cfg.tape.head from
        congrArg worig (Fin.ext (by simp [hm]))]
    rfl
  have hEhm : (encode worig cfg)[m]'hkm
      = cellSym (decide (m = 0)) false none
          (cfg.tape.contents ⟨m, by omega⟩) (worig ⟨m, by omega⟩) := by
    rw [encode_getElem worig cfg m (by omega),
      if_neg (show (⟨m, by omega⟩ : Fin (n + 1)) ≠ cfg.tape.head by rw [Ne, Fin.ext_iff]; simp [hm]),
      decide_eq_false (show ¬ m = n by omega)]
  -- Step 1: park the head into a `cellPending`; gated rules block `cellPending` stacking.
  have step1 : CS_transforms (myhillGrammar M embed) (encode worig cfg)
      ((encode worig cfg).set (m + 1)
        (cellPendingSym false (decide (m + 1 = n)) false q' a' (worig cfg.tape.head))) := by
    rcases Nat.lt_or_ge (m + 1) n with hlt | hge
    · -- interior: right neighbour blocks stacking
      have hdn : decide (m + 1 = n) = false := decide_eq_false (by omega)
      have hEhi : (encode worig cfg)[m + 1]'hkh
          = symbol.nonterminal (MyhillNT.cell false false (some cfg.state) cfg.tape.read
              (worig cfg.tape.head)) := by rw [hEh, hdn]
      have hEhp1 : (encode worig cfg)[m + 2]'(by rw [encode_length]; omega)
          = cellSym false (decide (m + 2 = n)) none
              (cfg.tape.contents ⟨m + 2, by omega⟩) (worig ⟨m + 2, by omega⟩) := by
        rw [encode_getElem worig cfg (m + 2) (by omega),
          if_neg (show (⟨m + 2, by omega⟩ : Fin (n + 1)) ≠ cfg.tape.head by
            simp only [Ne, Fin.ext_iff]; omega),
          decide_eq_false (show ¬ (m + 2 = 0) by omega)]
      have hrule1 := sim_left_interior_step1_interior_mem M embed cfg.state q' cfg.tape.read a'
        (worig ⟨m, by omega⟩) (worig cfg.tape.head) (decide (m = 0)) none
        (cfg.tape.contents ⟨m, by omega⟩) (decide (m + 2 = n))
        (cfg.tape.contents ⟨m + 2, by omega⟩) (worig ⟨m + 2, by omega⟩) htrans
      rw [← hEhm, ← hEhp1] at hrule1
      rw [hdn]
      exact CS_transforms_of_set_ctxLR (myhillGrammar M embed) (encode worig cfg) m
        (by rw [encode_length]; omega) _ _ hEhi hrule1
    · -- boundary: head at right end (m + 1 = n)
      have hmn : m + 1 = n := by omega
      have hdn : decide (m + 1 = n) = true := by simp [hmn]
      have hEhb : (encode worig cfg)[m + 1]'hkh
          = symbol.nonterminal (MyhillNT.cell false true (some cfg.state) cfg.tape.read
              (worig cfg.tape.head)) := by rw [hEh, hdn]
      have hrule1 := sim_left_interior_step1_boundary_mem M embed cfg.state q' cfg.tape.read a'
        (worig ⟨m, by omega⟩) (worig cfg.tape.head) (decide (m = 0)) none
        (cfg.tape.contents ⟨m, by omega⟩) htrans
      rw [← hEhm] at hrule1
      rw [hdn]
      exact CS_transforms_of_set_ctxL (myhillGrammar M embed) (encode worig cfg) m hkh _ _
        hEhb hrule1
  -- Step 2: place the new state on the left neighbour (pending cell as right context).
  have hL2h : ((encode worig cfg).set (m + 1)
      (cellPendingSym false (decide (m + 1 = n)) false q' a' (worig cfg.tape.head)))[m + 1]'(by
        rw [List.length_set]; exact hkh)
      = cellPendingSym false (decide (m + 1 = n)) false q' a' (worig cfg.tape.head) :=
    List.getElem_set_self ..
  have hL2m : ((encode worig cfg).set (m + 1)
      (cellPendingSym false (decide (m + 1 = n)) false q' a' (worig cfg.tape.head)))[m]'(by
        rw [List.length_set]; exact hkm)
      = symbol.nonterminal (MyhillNT.cell (decide (m = 0)) false none
          (cfg.tape.contents ⟨m, by omega⟩) (worig ⟨m, by omega⟩)) := by
    rw [List.getElem_set_ne (by omega), hEhm]
  have hrule2 := sim_left_interior_step2_mem M embed q' a' (worig ⟨m, by omega⟩)
    (worig cfg.tape.head) (decide (m = 0)) (decide (m + 1 = n))
    (cfg.tape.contents ⟨m, by omega⟩)
  rw [← hL2h] at hrule2
  have step2 := CS_transforms_of_set_ctxR (myhillGrammar M embed)
    ((encode worig cfg).set (m + 1)
      (cellPendingSym false (decide (m + 1 = n)) false q' a' (worig cfg.tape.head)))
    m (by rw [List.length_set]; exact hkh) _ _ hL2m hrule2
  -- Step 3: resolve the pending cell.
  have hL3h : (((encode worig cfg).set (m + 1)
        (cellPendingSym false (decide (m + 1 = n)) false q' a' (worig cfg.tape.head))).set m
        (cellSym (decide (m = 0)) false (some q') (cfg.tape.contents ⟨m, by omega⟩)
          (worig ⟨m, by omega⟩)))[m + 1]'(by rw [List.length_set, List.length_set]; exact hkh)
      = symbol.nonterminal (MyhillNT.cellPending false (decide (m + 1 = n)) false q' a'
          (worig cfg.tape.head)) := by
    rw [List.getElem_set_ne (by omega), List.getElem_set_self]
  have step3 := CS_transforms_of_set (myhillGrammar M embed)
    (((encode worig cfg).set (m + 1)
        (cellPendingSym false (decide (m + 1 = n)) false q' a' (worig cfg.tape.head))).set m
        (cellSym (decide (m = 0)) false (some q') (cfg.tape.contents ⟨m, by omega⟩)
          (worig ⟨m, by omega⟩)))
    (m + 1) (by rw [List.length_set, List.length_set]; exact hkh) _ _ hL3h
    (pending_resolution_rule_mem M embed q' a' (worig cfg.tape.head) false (decide (m + 1 = n)) false)
  -- Assemble and match `encode_left_interior`.
  rw [encode_left_interior worig cfg q' a' m hm]
  have key : (((encode worig cfg).set (m + 1)
        (cellPendingSym false (decide (m + 1 = n)) false q' a' (worig cfg.tape.head))).set m
        (cellSym (decide (m = 0)) false (some q') (cfg.tape.contents ⟨m, by omega⟩)
          (worig ⟨m, by omega⟩))).set (m + 1)
        (cellSym false (decide (m + 1 = n)) none a' (worig cfg.tape.head))
      = ((encode worig cfg).set (m + 1)
          (cellSym false (decide (m + 1 = n)) none a' (worig cfg.tape.head))).set m
          (cellSym (decide (m = 0)) false (some q') (cfg.tape.contents ⟨m, by omega⟩)
            (worig ⟨m, by omega⟩)) := by
    rw [List.set_comm _ _ (by omega : m ≠ m + 1), List.set_set]
  rw [← key]
  exact CS_deri_of_deri_deri (CS_deri_of_tran step1)
    (CS_deri_of_deri_deri (CS_deri_of_tran step2) (CS_deri_of_tran step3))

/-- **`step_sim`, right-boundary case.** A `right` transition with the head at the right end
is clamped, so it is mirrored by a single in-place rewrite (using the boundary rule). -/
theorem step_sim_right_boundary (M : LBA.Machine Γ Λ) (embed : T ↪ Γ) (worig : Fin (n + 1) → T)
    (cfg : DLBA.Cfg Γ Λ n) (q' : Λ) (a' : Γ) (hb : cfg.tape.head.val = n)
    (htrans : (q', a', DLBA.Dir.right) ∈ M.transition cfg.state cfg.tape.read) :
    CS_derives (myhillGrammar M embed) (encode worig cfg)
      (encode worig ⟨q', (cfg.tape.write a').moveHead DLBA.Dir.right⟩) := by
  have hb' : (cfg.tape.write a').head.val = n := by
    simp only [DLBA.BoundedTape.write]; exact hb
  have hrs : (cfg.tape.write a').moveHead DLBA.Dir.right
      = (cfg.tape.write a').moveHead DLBA.Dir.stay := by
    rw [moveHead_right_at_right _ hb', moveHead_stay]
  rw [hrs, ← encode_set_head worig cfg q' a']
  apply CS_deri_of_tran
  have hk : cfg.tape.head.val < (encode worig cfg).length := by
    rw [encode_length]; exact cfg.tape.head.isLt
  have hrbtrue : decide (cfg.tape.head.val = n) = true := by simp [hb]
  have hLk : (encode worig cfg)[cfg.tape.head.val]'hk
      = symbol.nonterminal (MyhillNT.cell (decide (cfg.tape.head.val = 0))
          (decide (cfg.tape.head.val = n)) (some cfg.state) cfg.tape.read
          (worig cfg.tape.head)) := by
    rw [encode_getElem worig cfg cfg.tape.head.val cfg.tape.head.isLt]
    have he : (⟨cfg.tape.head.val, cfg.tape.head.isLt⟩ : Fin (n + 1)) = cfg.tape.head :=
      Fin.ext rfl
    rw [he, if_pos rfl]; rfl
  have hrule := sim_right_boundary_rule_mem M embed cfg.state q' cfg.tape.read a'
    (worig cfg.tape.head) (decide (cfg.tape.head.val = 0)) htrans
  rw [← hrbtrue] at hrule
  exact CS_transforms_of_set (myhillGrammar M embed) (encode worig cfg) cfg.tape.head.val hk
    _ _ hLk hrule

/-- **`step_sim`, left-boundary case.** A `left` transition with the head at the left end is
clamped, so it is mirrored by a single in-place rewrite (using the boundary rule). -/
theorem step_sim_left_boundary (M : LBA.Machine Γ Λ) (embed : T ↪ Γ) (worig : Fin (n + 1) → T)
    (cfg : DLBA.Cfg Γ Λ n) (q' : Λ) (a' : Γ) (hb : cfg.tape.head.val = 0)
    (htrans : (q', a', DLBA.Dir.left) ∈ M.transition cfg.state cfg.tape.read) :
    CS_derives (myhillGrammar M embed) (encode worig cfg)
      (encode worig ⟨q', (cfg.tape.write a').moveHead DLBA.Dir.left⟩) := by
  have hb' : (cfg.tape.write a').head.val = 0 := by
    simp only [DLBA.BoundedTape.write]; exact hb
  have hrs : (cfg.tape.write a').moveHead DLBA.Dir.left
      = (cfg.tape.write a').moveHead DLBA.Dir.stay := by
    rw [moveHead_left_at_left _ hb', moveHead_stay]
  rw [hrs, ← encode_set_head worig cfg q' a']
  apply CS_deri_of_tran
  have hk : cfg.tape.head.val < (encode worig cfg).length := by
    rw [encode_length]; exact cfg.tape.head.isLt
  have hlbtrue : decide (cfg.tape.head.val = 0) = true := by simp [hb]
  have hLk : (encode worig cfg)[cfg.tape.head.val]'hk
      = symbol.nonterminal (MyhillNT.cell (decide (cfg.tape.head.val = 0))
          (decide (cfg.tape.head.val = n)) (some cfg.state) cfg.tape.read
          (worig cfg.tape.head)) := by
    rw [encode_getElem worig cfg cfg.tape.head.val cfg.tape.head.isLt]
    have he : (⟨cfg.tape.head.val, cfg.tape.head.isLt⟩ : Fin (n + 1)) = cfg.tape.head :=
      Fin.ext rfl
    rw [he, if_pos rfl]; rfl
  have hrule := sim_left_boundary_rule_mem M embed cfg.state q' cfg.tape.read a'
    (worig cfg.tape.head) (decide (cfg.tape.head.val = n)) htrans
  rw [← hlbtrue] at hrule
  exact CS_transforms_of_set (myhillGrammar M embed) (encode worig cfg) cfg.tape.head.val hk
    _ _ hLk hrule

/-- **Step simulation.** Every single LBA step is mirrored by a context-sensitive derivation
of the cell encodings — combining the stay, boundary, and interior cases. -/
theorem step_sim (M : LBA.Machine Γ Λ) (embed : T ↪ Γ) (worig : Fin (n + 1) → T)
    {cfg cfg' : DLBA.Cfg Γ Λ n} (h : LBA.Step M cfg cfg') :
    CS_derives (myhillGrammar M embed) (encode worig cfg) (encode worig cfg') := by
  obtain ⟨q', a', d, htrans, rfl⟩ := h
  have hlt := cfg.tape.head.isLt
  cases d with
  | stay => exact step_sim_stay M embed worig cfg q' a' htrans
  | left =>
      by_cases hb : cfg.tape.head.val = 0
      · exact step_sim_left_boundary M embed worig cfg q' a' hb htrans
      · exact step_sim_left_interior M embed worig cfg q' a' (by omega) htrans
  | right =>
      by_cases hb : cfg.tape.head.val = n
      · exact step_sim_right_boundary M embed worig cfg q' a' hb htrans
      · exact step_sim_right_interior M embed worig cfg q' a' (by omega) htrans

/-! ### Cleanup: an accepting configuration's encoding derives the terminal word -/

/-- A list of (head-free) cells, as grammar symbols, given their `(lb, rb, a, t)` data. -/
def cleanupCells (cs : List (Bool × Bool × Γ × T)) : List (symbol T (MyhillNT T Γ Λ)) :=
  cs.map fun c => cellSym c.1 c.2.1 none c.2.2.1 c.2.2.2

/-- The corresponding list of terminals. -/
def cleanupTerms (cs : List (Bool × Bool × Γ × T)) : List (symbol T (MyhillNT T Γ Λ)) :=
  cs.map fun c => symbol.terminal c.2.2.2

/-- **Rightward propagation.** A terminal followed by head-free cells derives to all
terminals (each cell is converted by the left-propagation rule using the terminal on its
left). -/
theorem cleanup_right (M : LBA.Machine Γ Λ) (embed : T ↪ Γ) (t₀ : T)
    (cs : List (Bool × Bool × Γ × T)) :
    CS_derives (myhillGrammar M embed)
      (symbol.terminal t₀ :: cleanupCells cs) (symbol.terminal t₀ :: cleanupTerms cs) := by
  induction cs generalizing t₀ with
  | nil => exact CS_deri_self
  | cons c cs' ih =>
      apply CS_deri_of_tran_deri
        (v := symbol.terminal t₀ :: symbol.terminal c.2.2.2 :: cleanupCells cs')
      · exact ⟨⟨[symbol.terminal t₀], MyhillNT.cell c.1 c.2.1 none c.2.2.1 c.2.2.2, [],
          [symbol.terminal c.2.2.2]⟩, [], cleanupCells cs',
          left_propagation_rule_mem M embed t₀ c.2.2.1 c.2.2.2 c.1 c.2.1,
          by simp [cleanupCells], by simp [cleanupCells]⟩
      · have hp := CS_deri_with_prefix (p := [symbol.terminal t₀]) (ih c.2.2.2)
        simpa [cleanupTerms, cleanupCells] using hp

/-- **Leftward propagation.** Head-free cells followed by a terminal derive to all terminals
(each cell is converted by the right-propagation rule using the terminal on its right). -/
theorem cleanup_left (M : LBA.Machine Γ Λ) (embed : T ↪ Γ) (t₀ : T)
    (cs : List (Bool × Bool × Γ × T)) :
    CS_derives (myhillGrammar M embed)
      (cleanupCells cs ++ [symbol.terminal t₀]) (cleanupTerms cs ++ [symbol.terminal t₀]) := by
  induction cs with
  | nil => exact CS_deri_self
  | cons c cs' ih =>
      obtain ⟨t₂, rest, hrest⟩ : ∃ t₂ rest,
          cleanupTerms cs' ++ [symbol.terminal t₀] = symbol.terminal t₂ :: rest := by
        cases cs' with
        | nil => exact ⟨t₀, [], rfl⟩
        | cons c' cs'' =>
            exact ⟨c'.2.2.2, cleanupTerms cs'' ++ [symbol.terminal t₀], by simp [cleanupTerms]⟩
      have hpref := CS_deri_with_prefix
        (p := [cellSym c.1 c.2.1 none c.2.2.1 c.2.2.2]) ih
      have h1 : CS_derives (myhillGrammar M embed) (cleanupCells (c :: cs') ++ [symbol.terminal t₀])
          (cellSym c.1 c.2.1 none c.2.2.1 c.2.2.2 :: (cleanupTerms cs' ++ [symbol.terminal t₀])) := by
        simpa [cleanupCells] using hpref
      have h2 : CS_derives (myhillGrammar M embed)
          (cellSym c.1 c.2.1 none c.2.2.1 c.2.2.2 :: (cleanupTerms cs' ++ [symbol.terminal t₀]))
          (cleanupTerms (c :: cs') ++ [symbol.terminal t₀]) := by
        rw [show cleanupTerms (c :: cs') = symbol.terminal c.2.2.2 :: cleanupTerms cs' from rfl,
          List.cons_append, hrest]
        apply CS_deri_of_tran
        exact ⟨⟨[], MyhillNT.cell c.1 c.2.1 none c.2.2.1 c.2.2.2, [symbol.terminal t₂],
            [symbol.terminal c.2.2.2]⟩, [], rest,
          right_propagation_rule_mem M embed c.2.2.1 c.2.2.2 t₂ c.1 c.2.1, by simp, by simp⟩
      exact CS_deri_of_deri_deri h1 h2

/-- **Two-sided propagation.** A terminal flanked by head-free cells derives to all
terminals. -/
theorem cleanup_mid (M : LBA.Machine Γ Λ) (embed : T ↪ Γ)
    (before after : List (Bool × Bool × Γ × T)) (t₀ : T) :
    CS_derives (myhillGrammar M embed)
      (cleanupCells before ++ symbol.terminal t₀ :: cleanupCells after)
      (cleanupTerms before ++ symbol.terminal t₀ :: cleanupTerms after) := by
  have h1 := CS_deri_with_prefix (p := cleanupCells before) (cleanup_right M embed t₀ after)
  have h2 := CS_deri_with_postfix (s := cleanupTerms after) (cleanup_left M embed t₀ before)
  refine CS_deri_of_deri_deri h1 ?_
  rw [show cleanupCells before ++ symbol.terminal t₀ :: cleanupTerms after
        = (cleanupCells before ++ [symbol.terminal t₀]) ++ cleanupTerms after from by simp,
    show cleanupTerms before ++ symbol.terminal t₀ :: cleanupTerms after
        = (cleanupTerms before ++ [symbol.terminal t₀]) ++ cleanupTerms after from by simp]
  exact h2

/-- **Cleanup (list form).** A list of head-free cells with one accepting `(some q)` cell at
position `k` derives to the list of terminals. -/
theorem cleanup_full (M : LBA.Machine Γ Λ) (embed : T ↪ Γ)
    (cs : List (Bool × Bool × Γ × T)) (k : ℕ) (hk : k < cs.length) (q : Λ)
    (hq : M.accept q = true) :
    CS_derives (myhillGrammar M embed)
      ((cleanupCells cs).set k
        (cellSym (cs[k]'hk).1 (cs[k]'hk).2.1 (some q) (cs[k]'hk).2.2.1 (cs[k]'hk).2.2.2))
      (cleanupTerms cs) := by
  have hkc : k < (cleanupCells (Λ := Λ) cs).length := by simpa [cleanupCells] using hk
  rw [List.set_eq_take_cons_drop _ hkc,
    show (cleanupCells cs).take k = cleanupCells (cs.take k) from by simp [cleanupCells],
    show (cleanupCells cs).drop (k + 1) = cleanupCells (cs.drop (k + 1)) from by simp [cleanupCells]]
  have hstep : CS_transforms (myhillGrammar M embed)
      (cleanupCells (cs.take k) ++ cellSym (cs[k]'hk).1 (cs[k]'hk).2.1 (some q) (cs[k]'hk).2.2.1
        (cs[k]'hk).2.2.2 :: cleanupCells (cs.drop (k + 1)))
      (cleanupCells (cs.take k) ++ symbol.terminal (cs[k]'hk).2.2.2 ::
        cleanupCells (cs.drop (k + 1))) :=
    ⟨⟨[], MyhillNT.cell (cs[k]'hk).1 (cs[k]'hk).2.1 (some q) (cs[k]'hk).2.2.1 (cs[k]'hk).2.2.2, [],
      [symbol.terminal (cs[k]'hk).2.2.2]⟩, cleanupCells (cs.take k), cleanupCells (cs.drop (k + 1)),
      accept_rule_mem M embed q hq (cs[k]'hk).2.2.1 (cs[k]'hk).2.2.2 (cs[k]'hk).1 (cs[k]'hk).2.1,
      by simp, by simp⟩
  refine CS_deri_of_tran_deri hstep ?_
  have hsplit : cs = cs.take k ++ cs[k]'hk :: cs.drop (k + 1) := by
    rw [List.cons_getElem_drop_succ, List.take_append_drop]
  have hterms : cleanupTerms (Λ := Λ) cs = cleanupTerms (Λ := Λ) (cs.take k)
      ++ (symbol.terminal (cs[k]'hk).2.2.2 : symbol T (MyhillNT T Γ Λ))
        :: cleanupTerms (Λ := Λ) (cs.drop (k + 1)) := by
    conv_lhs => rw [hsplit]
    simp only [cleanupTerms, List.map_append, List.map_cons]
  rw [hterms]
  exact cleanup_mid M embed (cs.take k) (cs.drop (k + 1)) (cs[k]'hk).2.2.2

/-- The per-position cell data `(lb, rb, a, t)` of a configuration. -/
def dataOf (worig : Fin (n + 1) → T) (cfg : DLBA.Cfg Γ Λ n) : List (Bool × Bool × Γ × T) :=
  List.ofFn fun i => (decide (i.val = 0), decide (i.val = n), cfg.tape.contents i, worig i)

@[simp]
theorem dataOf_length (worig : Fin (n + 1) → T) (cfg : DLBA.Cfg Γ Λ n) :
    (dataOf worig cfg).length = n + 1 := by simp [dataOf]

theorem dataOf_getElem (worig : Fin (n + 1) → T) (cfg : DLBA.Cfg Γ Λ n) (i : ℕ) (hi : i < n + 1) :
    (dataOf worig cfg)[i]'(by simpa using hi)
      = (decide (i = 0), decide (i = n), cfg.tape.contents ⟨i, hi⟩, worig ⟨i, hi⟩) := by
  simp only [dataOf, List.getElem_ofFn]

/-- **Cleanup.** The encoding of an accepting configuration derives the terminal word. -/
theorem cleanup (M : LBA.Machine Γ Λ) (embed : T ↪ Γ) (worig : Fin (n + 1) → T)
    (cfg' : DLBA.Cfg Γ Λ n) (hq : M.accept cfg'.state = true) :
    CS_derives (myhillGrammar M embed) (encode worig cfg')
      (List.ofFn fun i => symbol.terminal (worig i)) := by
  have hk : cfg'.tape.head.val < (dataOf worig cfg').length := by
    rw [dataOf_length]; exact cfg'.tape.head.isLt
  have htarget : (List.ofFn fun i : Fin (n + 1) => symbol.terminal (worig i))
      = cleanupTerms (Λ := Λ) (dataOf worig cfg') := by
    unfold cleanupTerms dataOf
    rw [List.map_ofFn]
    rfl
  have hbridge : encode worig cfg'
      = (cleanupCells (Λ := Λ) (dataOf worig cfg')).set cfg'.tape.head.val
          (cellSym (decide (cfg'.tape.head.val = 0)) (decide (cfg'.tape.head.val = n))
            (some cfg'.state) cfg'.tape.read (worig cfg'.tape.head)) := by
    apply List.ext_getElem
    · simp [encode, cleanupCells]
    · intro i hi1 _
      have hin : i < n + 1 := by simpa [encode] using hi1
      have hcc : (cleanupCells (Λ := Λ) (dataOf worig cfg'))[i]'(by
            unfold cleanupCells; rw [List.length_map, dataOf_length]; exact hin)
          = cellSym (decide (i = 0)) (decide (i = n)) none
              (cfg'.tape.contents ⟨i, hin⟩) (worig ⟨i, hin⟩) := by
        unfold cleanupCells
        rw [List.getElem_map, dataOf_getElem worig cfg' i hin]
      rw [encode_getElem worig cfg' i hin, List.getElem_set]
      by_cases hih : cfg'.tape.head.val = i
      · subst hih
        rw [if_pos rfl,
          show (⟨cfg'.tape.head.val, hin⟩ : Fin (n + 1)) = cfg'.tape.head from Fin.ext rfl,
          if_pos rfl]
        rfl
      · rw [if_neg hih, hcc, if_neg (Fin.ne_of_val_ne (by simp; omega))]
  rw [hbridge, htarget]
  have hfull := cleanup_full M embed (dataOf worig cfg') cfg'.tape.head.val hk cfg'.state hq
  rw [dataOf_getElem worig cfg' cfg'.tape.head.val cfg'.tape.head.isLt] at hfull
  exact hfull

/-- **Completeness (Fin-indexed).** If the LBA, started on the configuration encoding `worig`,
reaches an accepting configuration, then the Myhill grammar derives the terminal word
`map terminal worig`. Assembles the start phase, the run simulation, and the cleanup. -/
theorem myhill_complete_fin (M : LBA.Machine Γ Λ) (embed : T ↪ Γ) (worig : Fin (n + 1) → T)
    (cfg' : DLBA.Cfg Γ Λ n)
    (hreach : LBA.Reaches M
      ⟨M.initial, ⟨fun i => embed (worig i), ⟨0, Nat.succ_pos n⟩⟩⟩ cfg')
    (hacc : M.accept cfg'.state = true) :
    CS_derives (myhillGrammar M embed) [symbol.nonterminal MyhillNT.start]
      (List.ofFn fun i => symbol.terminal (worig i)) := by
  have h1 := start_phase M embed (List.ofFn worig) (List.ne_nil_of_length_pos (by simp))
  rw [startCells_eq_encode M embed worig] at h1
  have h2 := CS_derives_of_reaches (myhillGrammar M embed) M (encode worig)
    (fun c c' hc => step_sim M embed worig hc) hreach
  have h3 := cleanup M embed worig cfg' hacc
  exact CS_deri_of_deri_deri h1 (CS_deri_of_deri_deri h2 h3)

/-- **Completeness.** Every word accepted by the LBA is generated by the Myhill grammar. -/
theorem myhill_complete (M : LBA.Machine Γ Λ) (embed : T ↪ Γ) (w : List T)
    (h : LBA.LanguageViaEmbed M embed w) :
    CS_derives (myhillGrammar M embed) [symbol.nonterminal MyhillNT.start]
      (w.map symbol.terminal) := by
  obtain ⟨hw, cfg', hreach, hacc⟩ := h
  have hwl : 0 < w.length := by
    rcases w with _ | ⟨a, w⟩
    · simp at hw
    · simp
  have hn1 : (w.map embed).length - 1 + 1 = w.length := by rw [List.length_map]; omega
  set worig : Fin ((w.map embed).length - 1 + 1) → T := fun i => w.get (i.cast hn1) with hworig
  have hcfg : (⟨M.initial, ⟨fun i => embed (worig i), ⟨0, Nat.succ_pos _⟩⟩⟩ :
        DLBA.Cfg Γ Λ ((w.map embed).length - 1)) = LBA.initCfgList M (w.map embed) hw := by
    unfold LBA.initCfgList LBA.loadList
    congr 1
    congr 1
    funext i
    rw [hworig]
    simp [Fin.cast, List.get_eq_getElem, List.getElem_map]
  have htgt : (List.ofFn fun i => (symbol.terminal (worig i) : symbol T (MyhillNT T Γ Λ)))
      = w.map symbol.terminal := by
    apply List.ext_getElem
    · simp only [List.length_ofFn, List.length_map]; omega
    · intro j hj1 hj2
      rw [List.getElem_ofFn, List.getElem_map]
      simp [hworig, Fin.cast, List.get_eq_getElem]
  rw [← htgt]
  exact myhill_complete_fin M embed worig cfg' (hcfg ▸ hreach) hacc

end MyhillConstruction
