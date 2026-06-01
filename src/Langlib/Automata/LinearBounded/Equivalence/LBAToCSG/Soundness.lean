module

public import Langlib.Automata.LinearBounded.Equivalence.LBAToCSG.Completeness
import Mathlib.Tactic
@[expose]
public section

/-!
# LBA → CS: soundness of the Myhill grammar

This file develops the **soundness** half of `myhill_language_eq`
(`Automata/LinearBounded/Equivalence/ContextSensitive.lean`): every terminal word derivable
from the Myhill grammar's start symbol is accepted by the automaton,

  `CS_derives g [start] (map terminal w)  →  LanguageViaEmbed M embed w`.

## Proof strategy

The argument is an induction on the derivation establishing a structural **invariant** on
sentential forms. Writing `g = myhillGrammar M embed`, every form `s` with
`CS_derives g [start] s` falls into one of the phases of the construction, and each phase
carries the semantic guarantee that ties it back to an actual computation of `M`:

* **start phase** — `s` is a (possibly partial) row of `cell`s, optionally terminated by the
  `startAux` nonterminal. The cells laid down so far fix a prefix of a word `worig`, the first
  carries `(some M.initial)`, and completing the row yields `encode worig (initCfg worig)`.
* **simulation phase** — `s = encode worig cfg` for some configuration `cfg` with
  `Reaches M (initCfg worig) cfg`; exactly one cell carries the head state.
* **pending phase** — `s` is a simulation row in the middle of the 3-step interior-move
  protocol: it contains exactly one `cellPending`, and resolving the protocol lands on a row
  `encode worig cfg'` with `Reaches M (initCfg worig) cfg'`.
* **cleanup phase** — an accepting state has appeared (so `M` accepts from `initCfg worig`);
  `s` is a mixture of leading/trailing `terminal`s and stateless `cell none`s, all carrying
  the frozen `worig`.

The frozen terminal component `worig` of every `cell`/`cellPending` is invariant under every
rule (start lays it down; simulation, pending and accept rules all preserve it; cleanup emits
exactly it), so an all-terminal form must be `worig.map terminal`, i.e. `w = worig`. Reaching
an all-terminal form requires the accept rule to have fired, which is gated on
`M.accept q = true` for a reachable state `q`; that is precisely `Accepts M (initCfg worig)`,
hence `LanguageViaEmbed M embed w`.

This is the genuine content of the soundness direction and the remaining open work of the
LBA ⊆ CS inclusion.
-/

namespace MyhillConstruction

variable {T Γ Λ : Type} {n : ℕ}
variable [Fintype T] [Fintype Γ] [Fintype Λ]
variable [DecidableEq T] [DecidableEq Γ] [DecidableEq Λ]

set_option maxHeartbeats 2000000 in
/-- **Rule inversion.** Every rule of the Myhill grammar is one of the seventeen shapes laid
down in `myhillAllRules`. This is the backbone of the soundness closure step: given a single
transformation `s ⇒ s'`, knowing the rule's exact form pins down how `s'` relates to `s`.

The disjuncts, in order, mirror the rule families of `myhillAllRules`:
start (single / first / middle / last), simulation (stay / right-boundary / left-boundary),
right-interior (step1-boundary / step1-interior / step2), left-interior
(step1-boundary / step1-interior / step2), pending resolution, accept, and propagation
(left / right). The interior step-1 families are split into a *boundary* variant (head cell at
the very end/start, no blocking neighbour) and an *interior* variant (a stateless neighbour is
required as context, blocking `cellPending` stacking). -/
theorem myhill_rule_inv (M : LBA.Machine Γ Λ) (embed : T ↪ Γ)
    (r : csrule T (MyhillNT T Γ Λ)) (hr : r ∈ myhillAllRules M embed) :
    (∃ t, r = ⟨[], .start, [], [cellSym true true (some M.initial) (embed t) t]⟩) ∨
    (∃ t, r = ⟨[], .start, [], [symbol.nonterminal .startAux,
                                cellSym false true none (embed t) t]⟩) ∨
    (∃ t, r = ⟨[], .startAux, [], [symbol.nonterminal .startAux,
                                   cellSym false false none (embed t) t]⟩) ∨
    (∃ t, r = ⟨[], .startAux, [], [cellSym true false (some M.initial) (embed t) t]⟩) ∨
    (∃ q q' a a' t lb rb, (q', a', DLBA.Dir.stay) ∈ M.transition q a ∧
      r = ⟨[], .cell lb rb (some q) a t, [], [cellSym lb rb (some q') a' t]⟩) ∨
    (∃ q q' a a' t lb, (q', a', DLBA.Dir.right) ∈ M.transition q a ∧
      r = ⟨[], .cell lb true (some q) a t, [], [cellSym lb true (some q') a' t]⟩) ∨
    (∃ q q' a a' t rb, (q', a', DLBA.Dir.left) ∈ M.transition q a ∧
      r = ⟨[], .cell true rb (some q) a t, [], [cellSym true rb (some q') a' t]⟩) ∨
    (∃ q q' a a' t₁ t₂ rb₂ hi b, (q', a', DLBA.Dir.right) ∈ M.transition q a ∧
      r = ⟨[], .cell true false (some q) a t₁, [cellSym false rb₂ hi b t₂],
            [cellPendingSym true false true q' a' t₁]⟩) ∨
    (∃ q q' a a' t₁ t₂ rb₂ hi b lb₀ a₀ t₀, (q', a', DLBA.Dir.right) ∈ M.transition q a ∧
      r = ⟨[cellSym lb₀ false none a₀ t₀], .cell false false (some q) a t₁,
            [cellSym false rb₂ hi b t₂], [cellPendingSym false false true q' a' t₁]⟩) ∨
    (∃ q' a' t₁ t₂ lb₁ rb₂ b,
      r = ⟨[cellPendingSym lb₁ false true q' a' t₁], .cell false rb₂ none b t₂, [],
            [cellSym false rb₂ (some q') b t₂]⟩) ∨
    (∃ q q' a a' t₁ t₂ lb₁ hi b, (q', a', DLBA.Dir.left) ∈ M.transition q a ∧
      r = ⟨[cellSym lb₁ false hi b t₁], .cell false true (some q) a t₂, [],
            [cellPendingSym false true false q' a' t₂]⟩) ∨
    (∃ q q' a a' t₁ t₂ lb₁ hi b rb₀ a₀ t₀, (q', a', DLBA.Dir.left) ∈ M.transition q a ∧
      r = ⟨[cellSym lb₁ false hi b t₁], .cell false false (some q) a t₂,
            [cellSym false rb₀ none a₀ t₀], [cellPendingSym false false false q' a' t₂]⟩) ∨
    (∃ q' a' t₁ t₂ lb₁ rb₂ b,
      r = ⟨[], .cell lb₁ false none b t₁, [cellPendingSym false rb₂ false q' a' t₂],
            [cellSym lb₁ false (some q') b t₁]⟩) ∨
    (∃ q' a' t lb rb dir,
      r = ⟨[], .cellPending lb rb dir q' a' t, [], [cellSym lb rb none a' t]⟩) ∨
    (∃ q a t lb rb, M.accept q = true ∧
      r = ⟨[], .cell lb rb (some q) a t, [], [symbol.terminal t]⟩) ∨
    (∃ t₁ a t₂ lb rb,
      r = ⟨[symbol.terminal t₁], .cell lb rb none a t₂, [], [symbol.terminal t₂]⟩) ∨
    (∃ a t₁ t₂ lb rb,
      r = ⟨[], .cell lb rb none a t₁, [symbol.terminal t₂], [symbol.terminal t₁]⟩) := by
  unfold myhillAllRules at hr
  simp only [List.mem_append, or_assoc] at hr
  rcases hr with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;>
    (simp +decide only [List.mem_flatMap, List.mem_map, Finset.mem_toList, Finset.mem_univ,
        true_and, List.bind_eq_flatMap, bind, List.mem_ite_nil_right,
        List.mem_dite_nil_right, List.mem_cons, List.mem_singleton, List.not_mem_nil,
        or_false] at h <;> aesop)

/-- **Config-conversion bridge.** The list-loaded initial configuration `initCfgList` equals
the canonical positional initial configuration `⟨M.initial, embed ∘ worig, head 0⟩`, when the
frozen word `worig` reads off the (length-derived) input positions. This is the plumbing
`myhill_complete` used inline (its `hcfg`); factoring it out lets the soundness extraction step
turn an abstract `Accepts (canonical …)` into the list-level `LanguageViaEmbed`. The
length-derived domain of `worig` makes both sides share the tape length `(w.map embed).length-1`
definitionally, so this is a homogeneous equality (no transport). -/
theorem initCfgList_eq_canonical (M : LBA.Machine Γ Λ) (embed : T ↪ Γ)
    (w : List T) (hw : w.map embed ≠ [])
    (hlen : (w.map embed).length - 1 + 1 = w.length) :
    LBA.initCfgList M (w.map embed) hw
      = ⟨M.initial, ⟨fun i => embed (w.get (i.cast hlen)), ⟨0, Nat.succ_pos _⟩⟩⟩ := by
  unfold LBA.initCfgList LBA.loadList
  congr 1
  congr 1
  funext i
  simp [Fin.cast, List.get_eq_getElem, List.getElem_map]

/-! ### The soundness invariant

We prove soundness by induction on the derivation `[start] ⇒* s`, maintaining a structural
invariant `SoundInv s` that classifies every reachable sentential form into one of the
construction's phases. With the right-to-left start grammar there are no head-states until the
row is complete, so the start phase is purely structural (`startAux` followed by stateless
cells); the simulation phase is exactly an `encode` of a reachable configuration; the cleanup
phase directly carries the target `LanguageViaEmbed` fact (keyed on the frozen word), so the
final extraction needs no configuration cast. -/

/-- The frozen terminal carried by a symbol: the original input letter recorded in every cell
and recovered verbatim by the cleanup rules. -/
def frozenSym : symbol T (MyhillNT T Γ Λ) → Option T
  | symbol.terminal t => some t
  | symbol.nonterminal (MyhillNT.cell _ _ _ _ t) => some t
  | symbol.nonterminal (MyhillNT.cellPending _ _ _ _ _ t) => some t
  | _ => none

/-- The frozen word read off a sentential form. On a fully-cleaned form `w.map terminal` it is
exactly `w`. -/
def frozenWord (s : List (symbol T (MyhillNT T Γ Λ))) : List T := s.filterMap frozenSym

@[simp] theorem frozenWord_map_terminal (w : List T) :
    frozenWord (w.map (symbol.terminal (N := MyhillNT T Γ Λ))) = w := by
  unfold frozenWord
  rw [List.filterMap_map]
  simp only [Function.comp_def, frozenSym, List.filterMap_some]

/-- Start phase: `startAux` followed by the stateless `none`-cells laid so far (`auxCells` of
some nonempty input). No cell carries a head state yet. -/
def SP_start (embed : T → Γ) (s : List (symbol T (MyhillNT T Γ Λ))) : Prop :=
  ∃ tl : List T, tl ≠ [] ∧ s = symbol.nonterminal MyhillNT.startAux :: auxCells embed tl

/-- Simulation phase: `s` encodes a configuration reachable from the initial one. -/
def SP_sim (M : LBA.Machine Γ Λ) (embed : T ↪ Γ)
    (s : List (symbol T (MyhillNT T Γ Λ))) : Prop :=
  ∃ (m : ℕ) (worig : Fin (m + 1) → T) (cfg : DLBA.Cfg Γ Λ m),
    LBA.Reaches M ⟨M.initial, ⟨fun i => embed (worig i), ⟨0, Nat.succ_pos m⟩⟩⟩ cfg ∧
    s = encode worig cfg

/-- Dead phase: a complete row of stateless `none`-cells — no head, no `cellPending`, no
terminal. The form left when an interior-move `cellPending` is resolved before `step2` hands off
its state. `soundInv_step_stuck` shows no rule fires on it, and it is never all-terminal. -/
def SP_stuck (s : List (symbol T (MyhillNT T Γ Λ))) : Prop :=
  ∀ x ∈ s, ∃ lb rb a t, x = cellSym lb rb none a t

/-- Cleanup phase: an accepting state has appeared (so `M` accepts the frozen word `worig`),
and every position is either the recovered terminal `worig i` or a still-stateless cell
carrying `worig i`. The remaining rules (propagation) only convert cells to their terminals. -/
def SP_cleanup (M : LBA.Machine Γ Λ) (embed : T ↪ Γ)
    (s : List (symbol T (MyhillNT T Γ Λ))) : Prop :=
  ∃ (m : ℕ) (worig : Fin (m + 1) → T),
    LBA.Accepts M (⟨M.initial, ⟨fun i => embed (worig i), ⟨0, Nat.succ_pos m⟩⟩⟩ :
      DLBA.Cfg Γ Λ m) ∧
    s.length = m + 1 ∧
    ∀ i : Fin (m + 1), s[i.val]? = some (symbol.terminal (worig i)) ∨
      ∃ lb rb a, s[i.val]? = some (cellSym lb rb none a (worig i))

/-- Pending phase: mid an interior-move protocol, three sub-cases each with one `cellPending` at
the old head index. **P1** (`s = (encode cfg).set head …`, no head state); **GEN**
(`s = (encode cur).set k …`, head pinned at the neighbour `k±1`); **CLEANUP** (a cleanup row
with one position replaced by a pending whose hand-off neighbour is already a terminal). -/
def SP_pending (M : LBA.Machine Γ Λ) (embed : T ↪ Γ)
    (s : List (symbol T (MyhillNT T Γ Λ))) : Prop :=
  (∃ (m : ℕ) (worig : Fin (m + 1) → T) (cfg : DLBA.Cfg Γ Λ m) (q' : Λ) (a' : Γ) (dir : Bool),
      LBA.Reaches M ⟨M.initial, ⟨fun i => embed (worig i), ⟨0, Nat.succ_pos m⟩⟩⟩ cfg ∧
      (q', a', if dir then DLBA.Dir.right else DLBA.Dir.left)
        ∈ M.transition cfg.state cfg.tape.read ∧
      (dir = true → cfg.tape.head.val < m) ∧ (dir = false → 0 < cfg.tape.head.val) ∧
      s = (encode worig cfg).set cfg.tape.head.val
          (cellPendingSym (decide (cfg.tape.head.val = 0)) (decide (cfg.tape.head.val = m)) dir
            q' a' (worig cfg.tape.head)))
  ∨ (∃ (m : ℕ) (worig : Fin (m + 1) → T) (cur : DLBA.Cfg Γ Λ m) (k : Fin (m + 1)) (q' : Λ)
        (dir : Bool),
      LBA.Reaches M ⟨M.initial, ⟨fun i => embed (worig i), ⟨0, Nat.succ_pos m⟩⟩⟩ cur ∧
      ((dir = true ∧ cur.tape.head.val = k.val + 1) ∨
        (dir = false ∧ k.val = cur.tape.head.val + 1)) ∧
      s = (encode worig cur).set k.val
          (cellPendingSym (decide (k.val = 0)) (decide (k.val = m)) dir q'
            (cur.tape.contents k) (worig k)))
  ∨ (∃ (m : ℕ) (worig : Fin (m + 1) → T) (base : List (symbol T (MyhillNT T Γ Λ)))
        (k : Fin (m + 1)) (nb : Fin (m + 1)) (q' : Λ) (a' : Γ) (dir : Bool),
      LBA.Accepts M (⟨M.initial, ⟨fun i => embed (worig i), ⟨0, Nat.succ_pos m⟩⟩⟩ :
        DLBA.Cfg Γ Λ m) ∧
      base.length = m + 1 ∧
      (∀ i : Fin (m + 1), base[i.val]? = some (symbol.terminal (worig i)) ∨
        ∃ lb rb a, base[i.val]? = some (cellSym lb rb none a (worig i))) ∧
      base[k.val]? = some (cellSym (decide (k.val = 0)) (decide (k.val = m)) none a' (worig k)) ∧
      ((dir = true ∧ nb.val = k.val + 1) ∨ (dir = false ∧ k.val = nb.val + 1)) ∧
      (∃ t, base[nb.val]? = some (symbol.terminal t)) ∧
      s = base.set k.val
          (cellPendingSym (decide (k.val = 0)) (decide (k.val = m)) dir q' a' (worig k)))

/-- The soundness invariant: every form reachable from `[start]` is in one of the phases. -/
def SoundInv (M : LBA.Machine Γ Λ) (embed : T ↪ Γ)
    (s : List (symbol T (MyhillNT T Γ Λ))) : Prop :=
  s = [symbol.nonterminal MyhillNT.start]
  ∨ SP_start embed s ∨ SP_sim M embed s ∨ SP_pending M embed s ∨ SP_cleanup M embed s
  ∨ SP_stuck s

/-- The invariant holds at the start. -/
theorem soundInv_base (M : LBA.Machine Γ Λ) (embed : T ↪ Γ) :
    SoundInv M embed [symbol.nonterminal MyhillNT.start] := Or.inl rfl

/-- A symbol from `w.map terminal` is a terminal, never a nonterminal. -/
theorem terminal_of_mem_map {x : symbol T (MyhillNT T Γ Λ)} {w : List T}
    (hx : x ∈ w.map symbol.terminal) : ∃ t, x = symbol.terminal t := by
  simp only [List.mem_map] at hx
  obtain ⟨t, _, rfl⟩ := hx
  exact ⟨t, rfl⟩

/-- If `M` accepts the canonical initial configuration loaded with `worig`, the word
`List.ofFn worig` is in the embedded language. Bridges the abstract `Accepts` recovered when
the accept rule fires (simulation → cleanup) back to `LanguageViaEmbed`. -/
theorem accepts_initCfgOf_to_lve (M : LBA.Machine Γ Λ) (embed : T ↪ Γ) {k : ℕ}
    (worig : Fin (k + 1) → T)
    (h : LBA.Accepts M (⟨M.initial, ⟨fun i => embed (worig i), ⟨0, Nat.succ_pos k⟩⟩⟩ :
      DLBA.Cfg Γ Λ k)) :
    LBA.LanguageViaEmbed M embed (List.ofFn worig) := by
  have hw : (List.ofFn worig).map embed ≠ [] := by apply List.ne_nil_of_length_pos; simp
  have hlen : ((List.ofFn worig).map embed).length - 1 + 1 = (List.ofFn worig).length := by simp
  refine ⟨hw, ?_⟩
  rw [initCfgList_eq_canonical M embed (List.ofFn worig) hw hlen]
  have e : ((List.ofFn worig).map embed).length - 1 = k := by simp
  convert h using 3
  · rw [Fin.heq_fun_iff (by rw [e])]
    intro i
    rw [List.get_ofFn]
    exact congrArg (fun j => embed (worig j)) (Fin.ext rfl)
  · rw [Fin.heq_ext_iff (by rw [e])]

/-- A non-contracting step does not shorten the form (outputs are non-empty). -/
theorem cs_transforms_length_le (g : CS_grammar T) {w₁ w₂ : List (symbol T g.nt)}
    (h : CS_transforms g w₁ w₂) : w₁.length ≤ w₂.length := by
  obtain ⟨r, u, v, hr, rfl, rfl⟩ := h
  simp [List.length_append]
  exact List.length_pos_of_ne_nil (g.output_nonempty r hr)

/-- A derivation does not shorten the form; reachable forms are non-empty. -/
theorem cs_derives_length_le (g : CS_grammar T) {w₁ w₂ : List (symbol T g.nt)}
    (h : CS_derives g w₁ w₂) : w₁.length ≤ w₂.length := by
  induction h with
  | refl => exact le_refl _
  | tail _ h₂ ih => exact le_trans ih (cs_transforms_length_le g h₂)

/-- **Extraction.** A fully-terminal form satisfying the invariant must be in the cleanup phase,
which directly yields the language membership. -/
theorem soundInv_extract (M : LBA.Machine Γ Λ) (embed : T ↪ Γ) (w : List T) (hne : w ≠ [])
    (hinv : SoundInv M embed (w.map symbol.terminal)) :
    LBA.LanguageViaEmbed M embed w := by
  rcases hinv with h | h | h | h | h | h
  · -- `[start]`: a single nonterminal cannot be an all-terminal word
    rcases w with _ | ⟨a, w'⟩ <;> simp at h
  · -- start phase: head is `startAux`, a nonterminal
    obtain ⟨tl, _, heq⟩ := h
    have hmem : symbol.nonterminal MyhillNT.startAux
        ∈ w.map (symbol.terminal (N := MyhillNT T Γ Λ)) := by
      rw [heq]; simp
    obtain ⟨t, ht⟩ := terminal_of_mem_map hmem
    simp at ht
  · -- simulation phase: `encode` begins with a cell nonterminal
    obtain ⟨m, worig, cfg, _, heq⟩ := h
    have hwne : w ≠ [] := by
      rintro rfl
      have hl := congrArg List.length heq
      rw [encode_length] at hl
      simp at hl
    obtain ⟨a, w', rfl⟩ := List.exists_cons_of_ne_nil hwne
    rw [List.map_cons, encode, List.ofFn_succ] at heq
    injection heq with h1 _
    simp [cellSym] at h1
  · -- pending phase: some position holds a `cellPending`, never a terminal
    have mem_set_self : ∀ (l : List (symbol T (MyhillNT T Γ Λ))) (i : ℕ) (x), i < l.length →
        x ∈ l.set i x := by
      intro l i x hi
      have h1 : i < (l.set i x).length := by rw [List.length_set]; exact hi
      have hmm := List.getElem_mem h1
      rwa [List.getElem_set_self] at hmm
    have hmem : ∃ lb rb dir q' a' t,
        cellPendingSym lb rb dir q' a' t ∈ w.map (symbol.terminal (N := MyhillNT T Γ Λ)) := by
      rcases h with ⟨m, worig, cfg, q', a', dir, _, _, _, _, hs⟩
        | ⟨m, worig, cur, k, q', dir, _, _, hs⟩
        | ⟨m, worig, base, k, nb, q', a', dir, _, hbl, _, _, _, _, hs⟩
      · exact ⟨_, _, _, _, _, _, hs ▸ mem_set_self _ _ _
          (by rw [encode_length]; exact cfg.tape.head.isLt)⟩
      · exact ⟨_, _, _, _, _, _, hs ▸ mem_set_self _ _ _
          (by rw [encode_length]; exact k.isLt)⟩
      · exact ⟨_, _, _, _, _, _, hs ▸ mem_set_self _ _ _ (by rw [hbl]; exact k.isLt)⟩
    obtain ⟨lb, rb, dir, q', a', t, hm⟩ := hmem
    obtain ⟨t', ht'⟩ := terminal_of_mem_map hm
    simp [cellPendingSym] at ht'
  · -- cleanup phase: a fully-terminal cleanup row forces `w = ofFn worig`, which `M` accepts
    obtain ⟨m, worig, hacc, hlen, hcells⟩ := h
    have hwm : w.length = m + 1 := by simpa using hlen
    have hweq : w = List.ofFn worig := by
      apply List.ext_getElem
      · simp [hwm]
      · intro i hi1 hi2
        have hci := hcells ⟨i, by omega⟩
        have hmap : (w.map (symbol.terminal (N := MyhillNT T Γ Λ)))[i]?
            = some (symbol.terminal w[i]) := by
          rw [List.getElem?_map, List.getElem?_eq_getElem hi1]; rfl
        rcases hci with hc | ⟨lb, rb, a, hc⟩
        · rw [List.getElem_ofFn]; rw [hmap] at hc; simpa using hc
        · rw [hmap] at hc; simp [cellSym] at hc
    rw [hweq]
    exact accepts_initCfgOf_to_lve M embed worig hacc
  · -- dead phase: a non-empty all-terminal row cannot be all stateless cells
    obtain ⟨a, w', rfl⟩ := List.exists_cons_of_ne_nil hne
    obtain ⟨lb, rb, a', t, hc⟩ := h (symbol.terminal a) (by simp)
    simp [cellSym] at hc

/-- Every cell produced in the start phase (`auxCells`) is stateless with `lb = false`. -/
theorem mem_auxCells (embed : T → Γ) {x : symbol T (MyhillNT T Γ Λ)} {tl : List T}
    (hx : x ∈ auxCells embed tl) : ∃ rb a t, x = cellSym false rb none a t := by
  induction tl with
  | nil => simp [auxCells] at hx
  | cons a rest ih =>
      cases rest with
      | nil =>
          rw [auxCells] at hx
          rw [List.mem_singleton] at hx
          exact ⟨true, embed a, a, hx⟩
      | cons b rest' =>
          rw [auxCells_cons embed a (b :: rest') (by simp)] at hx
          rcases List.mem_cons.mp hx with h | h
          · exact ⟨false, embed a, a, h⟩
          · exact ih h

/-- List surgery: if `x` occurs uniquely as the head of `x :: rest`, any decomposition
`u ++ [x] ++ v = x :: rest` must have `u = []` and `v = rest`. -/
theorem decomp_head {α : Type} {x : α} {u v rest : List α}
    (h : u ++ [x] ++ v = x :: rest) (hx : x ∉ rest) : u = [] ∧ v = rest := by
  cases u with
  | nil => simpa using h
  | cons y u' =>
      exfalso
      rw [List.cons_append, List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, h2⟩ := h
      exact hx (by rw [← h2]; simp)

/-- Setting at the join index `u.length` of `u ++ x :: v` replaces the cons head `x`. -/
theorem set_at_length {α : Type} (u : List α) (x y : α) (v : List α) :
    (u ++ x :: v).set u.length y = u ++ y :: v := by
  induction u with
  | nil => rfl
  | cons a u' ih => simp only [List.cons_append, List.length_cons, List.set_cons_succ, ih]

/-- Every symbol of an `encode`d configuration is a `cell` nonterminal. -/
theorem mem_encode (worig : Fin (n + 1) → T) (cfg : DLBA.Cfg Γ Λ n)
    {x : symbol T (MyhillNT T Γ Λ)} (hx : x ∈ encode worig cfg) :
    ∃ lb rb st a t, x = symbol.nonterminal (MyhillNT.cell lb rb st a t) := by
  rw [encode, List.mem_ofFn] at hx
  obtain ⟨i, rfl⟩ := hx
  exact ⟨_, _, _, _, _, rfl⟩

/-- In an `encode` of a configuration, the only cell carrying a head state `(some q)` sits at
the head position. Hence any decomposition exposing such a cell pins its index to the head. -/
theorem encode_some_pos (worig : Fin (n + 1) → T) (cfg : DLBA.Cfg Γ Λ n)
    {u v : List (symbol T (MyhillNT T Γ Λ))} {lb rb : Bool} {q : Λ} {a : Γ} {t : T}
    (h : encode worig cfg = u ++ cellSym lb rb (some q) a t :: v) :
    u.length = cfg.tape.head.val := by
  have hlt : u.length < n + 1 := by
    have hh := congrArg List.length h
    rw [encode_length, List.length_append, List.length_cons] at hh
    omega
  have hget : (encode worig cfg)[u.length]'(by simpa using hlt)
      = cellSym lb rb (some q) a t := by
    have h1 : (encode worig cfg)[u.length]? = some (cellSym lb rb (some q) a t) := by
      rw [h, List.getElem?_append_right (Nat.le_refl _)]; simp
    rw [List.getElem?_eq_getElem (by simpa using hlt)] at h1
    exact Option.some.inj h1
  rw [encode_getElem worig cfg u.length hlt] at hget
  by_contra hne
  have hni : (⟨u.length, hlt⟩ : Fin (n + 1)) ≠ cfg.tape.head :=
    fun he => hne (congrArg Fin.val he)
  rw [if_neg hni] at hget
  simp [cellSym] at hget

/-- The frozen word of an `encode`d configuration is the original input `worig`. -/
theorem frozenWord_encode (worig : Fin (n + 1) → T) (cfg : DLBA.Cfg Γ Λ n) :
    frozenWord (encode worig cfg) = List.ofFn worig := by
  rw [frozenWord]
  have hfm : (encode worig cfg).filterMap frozenSym
      = (encode worig cfg).map (fun x => (frozenSym x).getD (worig ⟨0, Nat.succ_pos n⟩)) := by
    apply List.filterMap_eq_map_iff_forall_eq_some.mpr
    intro x hx
    obtain ⟨lb, rb, st, a, t, rfl⟩ := mem_encode worig cfg hx
    simp [frozenSym]
  rw [hfm, encode, List.map_ofFn]
  apply congrArg
  funext i
  simp [frozenSym, cellSym]

/-- From a head-cell decomposition of `encode`, recover every parameter of the cell. -/
theorem encode_head_cell (worig : Fin (n + 1) → T) (cfg : DLBA.Cfg Γ Λ n)
    {u v : List (symbol T (MyhillNT T Γ Λ))} {lb rb : Bool} {q : Λ} {a : Γ} {t : T}
    (h : encode worig cfg = u ++ cellSym lb rb (some q) a t :: v) :
    u.length = cfg.tape.head.val ∧ lb = decide (cfg.tape.head.val = 0) ∧
      rb = decide (cfg.tape.head.val = n) ∧ q = cfg.state ∧
      a = cfg.tape.contents cfg.tape.head ∧ t = worig cfg.tape.head := by
  have hpos := encode_some_pos worig cfg h
  have hidx : (encode worig cfg)[cfg.tape.head.val]'(by simpa using cfg.tape.head.isLt)
      = cellSym lb rb (some q) a t := by
    have h1 : (encode worig cfg)[cfg.tape.head.val]? = some (cellSym lb rb (some q) a t) := by
      rw [h, ← hpos, List.getElem?_append_right (Nat.le_refl _)]; simp
    rw [List.getElem?_eq_getElem (by simpa using cfg.tape.head.isLt)] at h1
    exact Option.some.inj h1
  rw [encode_getElem worig cfg cfg.tape.head.val cfg.tape.head.isLt,
    if_pos (Fin.ext rfl)] at hidx
  simp only [cellSym, symbol.nonterminal.injEq, MyhillNT.cell.injEq] at hidx
  obtain ⟨e1, e2, e3, e4, e5⟩ := hidx
  exact ⟨hpos, e1.symm, e2.symm, (Option.some.inj e3).symm, e4.symm, e5.symm⟩

/-- **Closure, start phase.** From a start-phase form, only the middle-cell and head-cell rules
apply: the former stays in the start phase, the latter completes the row to the (reachable)
initial configuration, entering the simulation phase. All other rules are vacuous because their
input/context symbols (a `start` symbol, a head-state cell, a `cellPending`, or a terminal) do
not occur in a start-phase form. -/
theorem soundInv_step_start (M : LBA.Machine Γ Λ) (embed : T ↪ Γ)
    {b c : List (symbol T (MyhillNT T Γ Λ))}
    (hb : SP_start embed b) (hstep : CS_transforms (myhillGrammar M embed) b c) :
    SoundInv M embed c := by
  obtain ⟨tl, htl, hbeq⟩ := hb
  obtain ⟨r, u, v, hr, hb2, hc⟩ := hstep
  rw [hbeq] at hb2
  have key : ∀ y : symbol T (MyhillNT T Γ Λ),
      y ∈ symbol.nonterminal MyhillNT.startAux :: auxCells embed tl →
      y = symbol.nonterminal MyhillNT.startAux ∨ ∃ rb a t, y = cellSym false rb none a t := by
    intro y hy
    rcases List.mem_cons.mp hy with h | h
    · exact Or.inl h
    · exact Or.inr (mem_auxCells embed h)
  have hstartAux_notmem :
      (symbol.nonterminal MyhillNT.startAux : symbol T (MyhillNT T Γ Λ)) ∉ auxCells embed tl := by
    intro hm; obtain ⟨rb, a, t, he⟩ := mem_auxCells embed hm; simp [cellSym] at he
  have hinput' := key (symbol.nonterminal r.input_nonterminal) (by rw [hb2]; simp)
  rcases myhill_rule_inv M embed r hr with
    h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
  · obtain ⟨t, rfl⟩ := h; simp [cellSym] at hinput'
  · obtain ⟨t, rfl⟩ := h; simp [cellSym] at hinput'
  · -- block3 (middle cell): stays in the start phase (start)
    obtain ⟨t, rfl⟩ := h
    simp only [List.nil_append, List.append_nil] at hb2
    obtain ⟨rfl, rfl⟩ := decomp_head hb2.symm hstartAux_notmem
    refine Or.inr (Or.inl ⟨t :: tl, by simp, ?_⟩)
    rw [hc]; simp [auxCells_cons embed t tl htl]
  · -- block4 (head cell): completes to the initial configuration → simulation phase
    obtain ⟨t, rfl⟩ := h
    simp only [List.nil_append, List.append_nil] at hb2
    obtain ⟨rfl, rfl⟩ := decomp_head hb2.symm hstartAux_notmem
    refine Or.inr (Or.inr (Or.inl ⟨tl.length, (t :: tl).get,
      ⟨M.initial, ⟨fun i => embed ((t :: tl).get i), ⟨0, Nat.succ_pos _⟩⟩⟩,
      Relation.ReflTransGen.refl, ?_⟩))
    rw [hc]; simp only [List.nil_append, List.append_nil, List.singleton_append]
    rw [← startCells_cons M embed t tl htl]
    conv_lhs => rw [← List.ofFn_get (t :: tl)]
    rw [startCells_eq_encode]
  · obtain ⟨q, q', a, a', t, lb, rb, htrans, rfl⟩ := h; simp [cellSym] at hinput'
  · obtain ⟨q, q', a, a', t, lb, htrans, rfl⟩ := h; simp [cellSym] at hinput'
  · obtain ⟨q, q', a, a', t, rb, htrans, rfl⟩ := h; simp [cellSym] at hinput'
  · obtain ⟨q, q', a, a', t1, t2, rb2, hi, bb, htrans, rfl⟩ := h; simp [cellSym] at hinput'
  · obtain ⟨q, q', a, a', t1, t2, rb2, hi, bb, lb0, a0, t0, htrans, rfl⟩ := h
    simp [cellSym] at hinput'
  · -- r-interior step2: needs a `cellPending` left context, absent here
    obtain ⟨q', a', t1, t2, lb1, rb2, bb, rfl⟩ := h
    rcases key (cellPendingSym lb1 false true q' a' t1) (by rw [hb2]; simp) with h' | ⟨rb, a, t, h'⟩ <;>
      simp [cellSym, cellPendingSym] at h'
  · obtain ⟨q, q', a, a', t1, t2, lb1, hi, bb, htrans, rfl⟩ := h; simp [cellSym] at hinput'
  · obtain ⟨q, q', a, a', t1, t2, lb1, hi, bb, rb0, a0, t0, htrans, rfl⟩ := h
    simp [cellSym] at hinput'
  · -- l-interior step2: needs a `cellPending` right context, absent here
    obtain ⟨q', a', t1, t2, lb1, rb2, bb, rfl⟩ := h
    rcases key (cellPendingSym false rb2 false q' a' t2) (by rw [hb2]; simp) with h' | ⟨rb, a, t, h'⟩ <;>
      simp [cellSym, cellPendingSym] at h'
  · obtain ⟨q', a', t, lb, rb, dir, rfl⟩ := h; simp [cellSym, cellPendingSym] at hinput'
  · obtain ⟨q, a, t, lb, rb, hacc, rfl⟩ := h; simp [cellSym] at hinput'
  · -- left propagation: needs a terminal left context, absent here
    obtain ⟨t1, a, t2, lb, rb, rfl⟩ := h
    rcases key (symbol.terminal t1) (by rw [hb2]; simp) with h' | ⟨rb', a', t', h'⟩ <;>
      simp [cellSym] at h'
  · -- right propagation: needs a terminal right context, absent here
    obtain ⟨a, t1, t2, lb, rb, rfl⟩ := h
    rcases key (symbol.terminal t2) (by rw [hb2]; simp) with h' | ⟨rb', a', t', h'⟩ <;>
      simp [cellSym] at h'

/-- **Closure, simulation phase.** A rule applied to `encode worig cfg` must act on the unique
head-state cell (all others are stateless `none` cells, and no `start`/`startAux`/`cellPending`/
terminal symbols occur). The head-stationary moves give the next `encode` (simulation), the
interior step-1 moves introduce a `cellPending` (pending phase), and the accept rule turns the
head cell into a terminal — at which point `M` accepts, entering the cleanup phase. -/
theorem soundInv_step_sim (M : LBA.Machine Γ Λ) (embed : T ↪ Γ)
    {b c : List (symbol T (MyhillNT T Γ Λ))}
    (hb : SP_sim M embed b) (hstep : CS_transforms (myhillGrammar M embed) b c) :
    SoundInv M embed c := by
  obtain ⟨m, worig, cfg, hreach, hbeq⟩ := hb
  obtain ⟨r, u, v, hr, hb2, hc⟩ := hstep
  rw [hbeq] at hb2
  have key : ∀ y : symbol T (MyhillNT T Γ Λ), y ∈ encode worig cfg →
      ∃ lb rb st a t, y = symbol.nonterminal (MyhillNT.cell lb rb st a t) :=
    fun y hy => mem_encode worig cfg hy
  have hinput := key (symbol.nonterminal r.input_nonterminal) (by rw [hb2]; simp)
  rcases myhill_rule_inv M embed r hr with
    h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
  · obtain ⟨t, rfl⟩ := h; simp at hinput
  · obtain ⟨t, rfl⟩ := h; simp at hinput
  · obtain ⟨t, rfl⟩ := h; simp at hinput
  · obtain ⟨t, rfl⟩ := h; simp at hinput -- (sim)
  · -- sim stay → simulation phase
    obtain ⟨q, q', a, a', t, lb, rb, htrans, rfl⟩ := h
    simp only [List.nil_append, List.append_nil, List.append_assoc, List.singleton_append] at hb2 hc
    obtain ⟨hpos, hlb, hrb, hq, ha, ht⟩ := encode_head_cell worig cfg hb2
    refine Or.inr (Or.inr (Or.inl
      ⟨m, worig, ⟨q', (cfg.tape.write a').moveHead DLBA.Dir.stay⟩, ?_, ?_⟩))
    · refine hreach.tail ⟨q', a', DLBA.Dir.stay, ?_, rfl⟩
      rw [DLBA.BoundedTape.read, ← ha, ← hq]; exact htrans
    · rw [hc, show cellSym lb rb (some q') a' t = cellSym (decide (cfg.tape.head.val = 0))
          (decide (cfg.tape.head.val = m)) (some q') a' (worig cfg.tape.head) by rw [hlb, hrb, ht],
        ← set_at_length u (cellSym lb rb (some q) a t) _ v, ← hb2, hpos]
      exact encode_set_head worig cfg q' a'
  · -- sim right-boundary → simulation phase
    obtain ⟨q, q', a, a', t, lb, htrans, rfl⟩ := h
    simp only [List.nil_append, List.append_nil, List.append_assoc, List.singleton_append] at hb2 hc
    obtain ⟨hpos, hlb, hrb, hq, ha, ht⟩ := encode_head_cell worig cfg hb2
    have hbn : cfg.tape.head.val = m := of_decide_eq_true hrb.symm
    refine Or.inr (Or.inr (Or.inl
      ⟨m, worig, ⟨q', (cfg.tape.write a').moveHead DLBA.Dir.right⟩, ?_, ?_⟩))
    · refine hreach.tail ⟨q', a', DLBA.Dir.right, ?_, rfl⟩
      rw [DLBA.BoundedTape.read, ← ha, ← hq]; exact htrans
    · rw [moveHead_right_at_right _ (by rw [DLBA.BoundedTape.write]; exact hbn)]
      rw [hc, show cellSym lb true (some q') a' t = cellSym (decide (cfg.tape.head.val = 0))
          (decide (cfg.tape.head.val = m)) (some q') a' (worig cfg.tape.head) by
            rw [hlb, ht]; simp [hbn],
        ← set_at_length u (cellSym lb true (some q) a t) _ v, ← hb2, hpos]
      have := encode_set_head worig cfg q' a'
      rwa [moveHead_stay] at this
  · -- sim left-boundary → simulation phase
    obtain ⟨q, q', a, a', t, rb, htrans, rfl⟩ := h
    simp only [List.nil_append, List.append_nil, List.append_assoc, List.singleton_append] at hb2 hc
    obtain ⟨hpos, hlb, hrb, hq, ha, ht⟩ := encode_head_cell worig cfg hb2
    have hb0 : cfg.tape.head.val = 0 := of_decide_eq_true hlb.symm
    refine Or.inr (Or.inr (Or.inl
      ⟨m, worig, ⟨q', (cfg.tape.write a').moveHead DLBA.Dir.left⟩, ?_, ?_⟩))
    · refine hreach.tail ⟨q', a', DLBA.Dir.left, ?_, rfl⟩
      rw [DLBA.BoundedTape.read, ← ha, ← hq]; exact htrans
    · rw [moveHead_left_at_left _ (by rw [DLBA.BoundedTape.write]; exact hb0)]
      rw [hc, show cellSym true rb (some q') a' t = cellSym (decide (cfg.tape.head.val = 0))
          (decide (cfg.tape.head.val = m)) (some q') a' (worig cfg.tape.head) by
            rw [hrb, ht]; simp [hb0],
        ← set_at_length u (cellSym true rb (some q) a t) _ v, ← hb2, hpos]
      have := encode_set_head worig cfg q' a'
      rwa [moveHead_stay] at this
  · -- r-interior step1 boundary → pending phase (P1, head at left end)
    obtain ⟨q, q', a, a', t1, t2, rb2, hi, bb, htrans, rfl⟩ := h
    simp only [List.nil_append, List.append_nil, List.append_assoc, List.singleton_append]
      at hb2 hc
    obtain ⟨hpos, hlb, hrb, hq, ha, ht⟩ := encode_head_cell worig cfg hb2
    have hpe : cellPendingSym (decide (cfg.tape.head.val = 0)) (decide (cfg.tape.head.val = m))
        true q' a' (worig cfg.tape.head) = cellPendingSym true false true q' a' t1 := by
      rw [← hlb, ← hrb, ← ht]
    refine Or.inr (Or.inr (Or.inr (Or.inl (Or.inl
      ⟨m, worig, cfg, q', a', true, hreach, ?_, ?_, ?_, ?_⟩))))
    · rw [hq, ha] at htrans; exact htrans
    · intro _
      have hnem : cfg.tape.head.val ≠ m := by intro he; rw [he] at hrb; simp at hrb
      have := cfg.tape.head.isLt; omega
    · intro he; simp at he
    · rw [hc, hpe, ← hpos, hb2]
      exact (set_at_length u (cellSym true false (some q) a t1)
        (cellPendingSym true false true q' a' t1) (cellSym false rb2 hi bb t2 :: v)).symm
  · -- r-interior step1 interior → pending phase (P1)
    obtain ⟨q, q', a, a', t1, t2, rb2, hi, bb, lb0, a0, t0, htrans, rfl⟩ := h
    simp only [List.nil_append, List.append_nil, List.append_assoc, List.singleton_append]
      at hb2 hc
    have hb2' := hb2.trans (List.append_cons u (cellSym lb0 false none a0 t0)
      (cellSym false false (some q) a t1 :: cellSym false rb2 hi bb t2 :: v))
    have hc' := hc.trans (List.append_cons u (cellSym lb0 false none a0 t0)
      (cellPendingSym false false true q' a' t1 :: cellSym false rb2 hi bb t2 :: v))
    obtain ⟨hpos, hlb, hrb, hq, ha, ht⟩ := encode_head_cell worig cfg hb2'
    have hpe : cellPendingSym (decide (cfg.tape.head.val = 0)) (decide (cfg.tape.head.val = m))
        true q' a' (worig cfg.tape.head) = cellPendingSym false false true q' a' t1 := by
      rw [← hlb, ← hrb, ← ht]
    refine Or.inr (Or.inr (Or.inr (Or.inl (Or.inl
      ⟨m, worig, cfg, q', a', true, hreach, ?_, ?_, ?_, ?_⟩))))
    · rw [hq, ha] at htrans; exact htrans
    · intro _
      have hnem : cfg.tape.head.val ≠ m := by intro he; rw [he] at hrb; simp at hrb
      have := cfg.tape.head.isLt; omega
    · intro he; simp at he
    · rw [hc', hpe, ← hpos, hb2']
      exact (set_at_length _ _ _ _).symm
  · obtain ⟨q', a', t1, t2, lb1, rb2, bb, rfl⟩ := h
    rcases key (cellPendingSym lb1 false true q' a' t1) (by rw [hb2]; simp) with ⟨_, _, _, _, _, he⟩
    simp [cellPendingSym, cellSym] at he
  · -- l-interior step1 boundary → pending phase (P1, head at right end)
    obtain ⟨q, q', a, a', t1, t2, lb1, hi, bb, htrans, rfl⟩ := h
    simp only [List.nil_append, List.append_nil, List.append_assoc, List.singleton_append]
      at hb2 hc
    have hb2' := hb2.trans (List.append_cons u (cellSym lb1 false hi bb t1)
      (cellSym false true (some q) a t2 :: v))
    have hc' := hc.trans (List.append_cons u (cellSym lb1 false hi bb t1)
      (cellPendingSym false true false q' a' t2 :: v))
    obtain ⟨hpos, hlb, hrb, hq, ha, ht⟩ := encode_head_cell worig cfg hb2'
    have hpe : cellPendingSym (decide (cfg.tape.head.val = 0)) (decide (cfg.tape.head.val = m))
        false q' a' (worig cfg.tape.head) = cellPendingSym false true false q' a' t2 := by
      rw [← hlb, ← hrb, ← ht]
    refine Or.inr (Or.inr (Or.inr (Or.inl (Or.inl
      ⟨m, worig, cfg, q', a', false, hreach, ?_, ?_, ?_, ?_⟩))))
    · rw [hq, ha] at htrans; exact htrans
    · intro he; simp at he
    · intro _
      have hne0 : cfg.tape.head.val ≠ 0 := by intro he; rw [he] at hlb; simp at hlb
      omega
    · rw [hc', hpe, ← hpos, hb2']
      exact (set_at_length _ _ _ _).symm
  · -- l-interior step1 interior → pending phase (P1)
    obtain ⟨q, q', a, a', t1, t2, lb1, hi, bb, rb0, a0, t0, htrans, rfl⟩ := h
    simp only [List.nil_append, List.append_nil, List.append_assoc, List.singleton_append]
      at hb2 hc
    have hb2' := hb2.trans (List.append_cons u (cellSym lb1 false hi bb t1)
      (cellSym false false (some q) a t2 :: cellSym false rb0 none a0 t0 :: v))
    have hc' := hc.trans (List.append_cons u (cellSym lb1 false hi bb t1)
      (cellPendingSym false false false q' a' t2 :: cellSym false rb0 none a0 t0 :: v))
    obtain ⟨hpos, hlb, hrb, hq, ha, ht⟩ := encode_head_cell worig cfg hb2'
    have hpe : cellPendingSym (decide (cfg.tape.head.val = 0)) (decide (cfg.tape.head.val = m))
        false q' a' (worig cfg.tape.head) = cellPendingSym false false false q' a' t2 := by
      rw [← hlb, ← hrb, ← ht]
    refine Or.inr (Or.inr (Or.inr (Or.inl (Or.inl
      ⟨m, worig, cfg, q', a', false, hreach, ?_, ?_, ?_, ?_⟩))))
    · rw [hq, ha] at htrans; exact htrans
    · intro he; simp at he
    · intro _
      have hne0 : cfg.tape.head.val ≠ 0 := by intro he; rw [he] at hlb; simp at hlb
      omega
    · rw [hc', hpe, ← hpos, hb2']
      exact (set_at_length _ _ _ _).symm
  · obtain ⟨q', a', t1, t2, lb1, rb2, bb, rfl⟩ := h
    rcases key (cellPendingSym false rb2 false q' a' t2) (by rw [hb2]; simp) with ⟨_, _, _, _, _, he⟩
    simp [cellPendingSym, cellSym] at he
  · obtain ⟨q', a', t, lb, rb, dir, rfl⟩ := h; simp [cellPendingSym, cellSym] at hinput
  · -- accept → cleanup phase
    obtain ⟨q, a, t, lb, rb, hacc, rfl⟩ := h
    simp only [List.nil_append, List.append_nil, List.append_assoc, List.singleton_append] at hb2 hc
    obtain ⟨hpos, hlb, hrb, hq, ha, ht⟩ := encode_head_cell worig cfg hb2
    have hcset : c = (encode worig cfg).set cfg.tape.head.val
        (symbol.terminal (worig cfg.tape.head)) := by
      rw [hc, ht, ← set_at_length u (cellSym lb rb (some q) a t) _ v, ← hb2, hpos]
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨m, worig, ⟨cfg, hreach, by rw [← hq]; exact hacc⟩, ?_, ?_⟩))))
    · rw [hcset, List.length_set, encode_length]
    · intro i
      rw [hcset, List.getElem?_set]
      by_cases hih : cfg.tape.head.val = i.val
      · left
        rw [if_pos hih, if_pos (by rw [encode_length]; exact cfg.tape.head.isLt)]
        congr 2
        exact congrArg worig (Fin.ext hih)
      · right
        rw [if_neg hih, List.getElem?_eq_getElem (by rw [encode_length]; exact i.isLt),
          encode_getElem worig cfg i.val i.isLt,
          if_neg (fun he => hih (congrArg Fin.val he).symm)]
        exact ⟨_, _, _, rfl⟩
  · -- left propagation: needs a terminal context, absent in `encode`
    obtain ⟨t1, a, t2, lb, rb, rfl⟩ := h
    rcases key (symbol.terminal t1) (by rw [hb2]; simp) with ⟨_, _, _, _, _, he⟩
    simp [cellSym] at he
  · -- right propagation: needs a terminal context, absent in `encode`
    obtain ⟨a, t1, t2, lb, rb, rfl⟩ := h
    rcases key (symbol.terminal t2) (by rw [hb2]; simp) with ⟨_, _, _, _, _, he⟩
    simp [cellSym] at he

set_option maxHeartbeats 1200000 in
/-- **Closure, cleanup phase.** From a cleanup row only the propagation rules apply (all
symbols are terminals or stateless cells, so no `start`/`startAux`/`cellPending`/head-state
cell occurs). Each propagation turns a stateless cell into its frozen terminal, keeping the
cleanup row (and the accepted word) intact. -/
theorem soundInv_step_cleanup (M : LBA.Machine Γ Λ) (embed : T ↪ Γ)
    {b c : List (symbol T (MyhillNT T Γ Λ))}
    (hb : SP_cleanup M embed b) (hstep : CS_transforms (myhillGrammar M embed) b c) :
    SoundInv M embed c := by
  obtain ⟨m, worig, hacc, hlen, hcells⟩ := hb
  obtain ⟨r, u, v, hr, hb2, hc⟩ := hstep
  have key : ∀ x ∈ b, (∃ t, x = symbol.terminal t) ∨
      ∃ lb rb a t, x = cellSym lb rb none a t := by
    intro x hx
    obtain ⟨i, hi, hbi⟩ := List.getElem_of_mem hx
    have hc2 := hcells ⟨i, by rw [← hlen]; exact hi⟩
    rw [List.getElem?_eq_getElem hi, hbi] at hc2
    rcases hc2 with hh | ⟨lb, rb, a, hh⟩
    · exact Or.inl ⟨_, Option.some.inj hh⟩
    · exact Or.inr ⟨lb, rb, a, _, Option.some.inj hh⟩
  have hin := key (symbol.nonterminal r.input_nonterminal) (by rw [hb2]; simp)
  -- A cleanup row's length and the propagation-target rebuilds.
  have hbl : b.length = m + 1 := hlen
  rcases myhill_rule_inv M embed r hr with
    h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
  · obtain ⟨t, rfl⟩ := h; rcases hin with ⟨_, hh⟩ | ⟨_, _, _, _, hh⟩ <;> simp [cellSym] at hh
  · obtain ⟨t, rfl⟩ := h; rcases hin with ⟨_, hh⟩ | ⟨_, _, _, _, hh⟩ <;> simp [cellSym] at hh
  · obtain ⟨t, rfl⟩ := h; rcases hin with ⟨_, hh⟩ | ⟨_, _, _, _, hh⟩ <;> simp [cellSym] at hh
  · obtain ⟨t, rfl⟩ := h; rcases hin with ⟨_, hh⟩ | ⟨_, _, _, _, hh⟩ <;> simp [cellSym] at hh
  · obtain ⟨q, q', a, a', t, lb, rb, htrans, rfl⟩ := h
    rcases hin with ⟨_, hh⟩ | ⟨_, _, _, _, hh⟩ <;> simp [cellSym] at hh
  · obtain ⟨q, q', a, a', t, lb, htrans, rfl⟩ := h
    rcases hin with ⟨_, hh⟩ | ⟨_, _, _, _, hh⟩ <;> simp [cellSym] at hh
  · obtain ⟨q, q', a, a', t, rb, htrans, rfl⟩ := h
    rcases hin with ⟨_, hh⟩ | ⟨_, _, _, _, hh⟩ <;> simp [cellSym] at hh
  · obtain ⟨q, q', a, a', t1, t2, rb2, hi, bb, htrans, rfl⟩ := h
    rcases hin with ⟨_, hh⟩ | ⟨_, _, _, _, hh⟩ <;> simp [cellSym] at hh
  · obtain ⟨q, q', a, a', t1, t2, rb2, hi, bb, lb0, a0, t0, htrans, rfl⟩ := h
    rcases hin with ⟨_, hh⟩ | ⟨_, _, _, _, hh⟩ <;> simp [cellSym] at hh
  · obtain ⟨q', a', t1, t2, lb1, rb2, bb, rfl⟩ := h
    rcases key (cellPendingSym lb1 false true q' a' t1) (by rw [hb2]; simp) with
      ⟨_, hh⟩ | ⟨_, _, _, _, hh⟩ <;> simp [cellPendingSym, cellSym] at hh
  · obtain ⟨q, q', a, a', t1, t2, lb1, hi, bb, htrans, rfl⟩ := h
    rcases hin with ⟨_, hh⟩ | ⟨_, _, _, _, hh⟩ <;> simp [cellSym] at hh
  · obtain ⟨q, q', a, a', t1, t2, lb1, hi, bb, rb0, a0, t0, htrans, rfl⟩ := h
    rcases hin with ⟨_, hh⟩ | ⟨_, _, _, _, hh⟩ <;> simp [cellSym] at hh
  · obtain ⟨q', a', t1, t2, lb1, rb2, bb, rfl⟩ := h
    rcases key (cellPendingSym false rb2 false q' a' t2) (by rw [hb2]; simp) with
      ⟨_, hh⟩ | ⟨_, _, _, _, hh⟩ <;> simp [cellPendingSym, cellSym] at hh
  · obtain ⟨q', a', t, lb, rb, dir, rfl⟩ := h
    rcases hin with ⟨_, hh⟩ | ⟨_, _, _, _, hh⟩ <;> simp [cellPendingSym, cellSym] at hh
  · obtain ⟨q, a, t, lb, rb, hacc2, rfl⟩ := h
    rcases hin with ⟨_, hh⟩ | ⟨_, _, _, _, hh⟩ <;> simp [cellSym] at hh
  · -- left propagation: a stateless cell adjacent to a terminal becomes its terminal
    obtain ⟨t1, a, t2, lb, rb, rfl⟩ := h
    simp only [List.nil_append, List.append_nil, List.append_assoc] at hb2 hc
    have hk : u.length + 1 < m + 1 := by
      have hh := congrArg List.length hb2
      simp only [List.length_append, List.length_cons, hbl] at hh; omega
    have hcellk : b[u.length + 1]? = some (cellSym lb rb none a t2) := by
      rw [hb2]; simp [List.getElem?_append_right]
    have ht2 : t2 = worig ⟨u.length + 1, hk⟩ := by
      rcases hcells ⟨u.length + 1, hk⟩ with h2 | ⟨lb', rb', a', h2⟩
      · exact absurd (hcellk.symm.trans h2) (by simp [cellSym])
      · have h3 := hcellk.symm.trans h2
        simp only [Option.some.injEq, cellSym, symbol.nonterminal.injEq, MyhillNT.cell.injEq] at h3
        tauto
    have hcset : c = b.set (u.length + 1) (symbol.terminal t2) := by
      rw [hc, hb2]; simp [List.set_append_right]
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨m, worig, hacc, ?_, ?_⟩))))
    · rw [hcset, List.length_set]; exact hbl
    · intro i
      rw [hcset, List.getElem?_set]
      by_cases hik : u.length + 1 = i.val
      · left; rw [if_pos hik, if_pos (by rw [hbl]; omega), ht2]
        exact congrArg (fun j => some (symbol.terminal (worig j))) (Fin.ext hik)
      · rw [if_neg hik]; exact hcells i
  · -- right propagation: symmetric
    obtain ⟨a, t1, t2, lb, rb, rfl⟩ := h
    simp only [List.nil_append, List.append_nil, List.append_assoc] at hb2 hc
    have hk : u.length < m + 1 := by
      have hh := congrArg List.length hb2
      simp only [List.length_append, List.length_cons, hbl] at hh; omega
    have hcellk : b[u.length]? = some (cellSym lb rb none a t1) := by
      rw [hb2]; simp [List.getElem?_append_right]
    have ht1 : t1 = worig ⟨u.length, hk⟩ := by
      rcases hcells ⟨u.length, hk⟩ with h2 | ⟨lb', rb', a', h2⟩
      · exact absurd (hcellk.symm.trans h2) (by simp [cellSym])
      · have h3 := hcellk.symm.trans h2
        simp only [Option.some.injEq, cellSym, symbol.nonterminal.injEq, MyhillNT.cell.injEq] at h3
        tauto
    have hcset : c = b.set u.length (symbol.terminal t1) := by
      rw [hc, hb2]; simp [List.set_append_right]
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨m, worig, hacc, ?_, ?_⟩))))
    · rw [hcset, List.length_set]; exact hbl
    · intro i
      rw [hcset, List.getElem?_set]
      by_cases hik : u.length = i.val
      · left; rw [if_pos hik, if_pos (by rw [hbl]; omega), ht1]
        exact congrArg (fun j => some (symbol.terminal (worig j))) (Fin.ext hik)
      · rw [if_neg hik]; exact hcells i

/-- **No rule fires on a dead (all-stateless) row.** If every symbol of `b` is a stateless
`cell … none …`, then no grammar rule applies: every rule needs a head-state cell, a
`cellPending`, a terminal, or a `start`/`startAux` symbol as its input or context, none of which
occur. This is the closure of the "stuck" phase reached when an interior-move `cellPending` is
resolved before `step2` hands off its state. A building block for the `SP_pending` closure. -/
theorem soundInv_step_stuck (M : LBA.Machine Γ Λ) (embed : T ↪ Γ)
    {b c : List (symbol T (MyhillNT T Γ Λ))}
    (hb : ∀ x ∈ b, ∃ lb rb a t, x = cellSym lb rb none a t)
    (hstep : CS_transforms (myhillGrammar M embed) b c) : False := by
  obtain ⟨r, u, v, hr, hb2, hc⟩ := hstep
  have hin := hb (symbol.nonterminal r.input_nonterminal) (by rw [hb2]; simp)
  rcases myhill_rule_inv M embed r hr with
    h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
  · obtain ⟨t, rfl⟩ := h; obtain ⟨_, _, _, _, hh⟩ := hin; simp [cellSym] at hh
  · obtain ⟨t, rfl⟩ := h; obtain ⟨_, _, _, _, hh⟩ := hin; simp [cellSym] at hh
  · obtain ⟨t, rfl⟩ := h; obtain ⟨_, _, _, _, hh⟩ := hin; simp [cellSym] at hh
  · obtain ⟨t, rfl⟩ := h; obtain ⟨_, _, _, _, hh⟩ := hin; simp [cellSym] at hh
  · obtain ⟨q, q', a, a', t, lb, rb, _, rfl⟩ := h; obtain ⟨_, _, _, _, hh⟩ := hin
    simp [cellSym] at hh
  · obtain ⟨q, q', a, a', t, lb, _, rfl⟩ := h; obtain ⟨_, _, _, _, hh⟩ := hin; simp [cellSym] at hh
  · obtain ⟨q, q', a, a', t, rb, _, rfl⟩ := h; obtain ⟨_, _, _, _, hh⟩ := hin; simp [cellSym] at hh
  · obtain ⟨q, q', a, a', t1, t2, rb2, hi, bb, _, rfl⟩ := h; obtain ⟨_, _, _, _, hh⟩ := hin
    simp [cellSym] at hh
  · obtain ⟨q, q', a, a', t1, t2, rb2, hi, bb, lb0, a0, t0, _, rfl⟩ := h
    obtain ⟨_, _, _, _, hh⟩ := hin; simp [cellSym] at hh
  · -- r-interior step2: input is a stateless cell (consistent), but its `cellPending` context isn't
    obtain ⟨q', a', t1, t2, lb1, rb2, bb, rfl⟩ := h
    obtain ⟨_, _, _, _, hh⟩ := hb (cellPendingSym lb1 false true q' a' t1) (by rw [hb2]; simp)
    simp [cellSym, cellPendingSym] at hh
  · obtain ⟨q, q', a, a', t1, t2, lb1, hi, bb, _, rfl⟩ := h; obtain ⟨_, _, _, _, hh⟩ := hin
    simp [cellSym] at hh
  · obtain ⟨q, q', a, a', t1, t2, lb1, hi, bb, rb0, a0, t0, _, rfl⟩ := h
    obtain ⟨_, _, _, _, hh⟩ := hin; simp [cellSym] at hh
  · -- l-interior step2: `cellPending` context absent
    obtain ⟨q', a', t1, t2, lb1, rb2, bb, rfl⟩ := h
    obtain ⟨_, _, _, _, hh⟩ := hb (cellPendingSym false rb2 false q' a' t2) (by rw [hb2]; simp)
    simp [cellSym, cellPendingSym] at hh
  · -- resolution: input is a `cellPending`
    obtain ⟨q', a', t, lb, rb, dir, rfl⟩ := h; obtain ⟨_, _, _, _, hh⟩ := hin
    simp [cellSym, cellPendingSym] at hh
  · -- accept: input is a head-state cell
    obtain ⟨q, a, t, lb, rb, _, rfl⟩ := h; obtain ⟨_, _, _, _, hh⟩ := hin; simp [cellSym] at hh
  · -- left propagation: terminal left-context absent
    obtain ⟨t1, a, t2, lb, rb, rfl⟩ := h
    obtain ⟨_, _, _, _, hh⟩ := hb (symbol.terminal t1) (by rw [hb2]; simp); simp [cellSym] at hh
  · -- right propagation: terminal right-context absent
    obtain ⟨a, t1, t2, lb, rb, rfl⟩ := h
    obtain ⟨_, _, _, _, hh⟩ := hb (symbol.terminal t2) (by rw [hb2]; simp); simp [cellSym] at hh

/-- **Closure, pending phase.** From a `SP_pending` form (P1 / GEN / CLEANUP), one rule step keeps
the soundness invariant. In **P1** only resolution (→ `SP_stuck`) and the matching `step2`
(→ GEN) fire; in **GEN** the pinned head can stay/clamp (→ GEN), accept (→ CLEANUP), or have the
pending resolved (→ `SP_sim`); in **CLEANUP** only propagation (→ CLEANUP) and resolution
(→ `SP_cleanup`) fire. The producers (`soundInv_step_sim`'s `step1` arms) build P1; the rest of
the protocol is closed here. -/
theorem soundInv_step_pending (M : LBA.Machine Γ Λ) (embed : T ↪ Γ)
    {b c : List (symbol T (MyhillNT T Γ Λ))}
    (hb : SP_pending M embed b) (hstep : CS_transforms (myhillGrammar M embed) b c) :
    SoundInv M embed c := by
  obtain ⟨r, u, v, hr, hb2, hc⟩ := hstep
  rcases hb with ⟨m, worig, cfg, q', a', dir, hreach, htrans, _, _, hbeq⟩ | hGEN | hCLEAN
  · -- **P1.** `b = (encode cfg).set head pend`: a stateless row with one pending at the head.
    have hbel : ∀ x ∈ b, x = cellPendingSym (decide (cfg.tape.head.val = 0))
        (decide (cfg.tape.head.val = m)) dir q' a' (worig cfg.tape.head)
        ∨ ∃ lb rb aa t, x = cellSym lb rb none aa t := by
      intro x hx
      obtain ⟨i, hi0, hbi⟩ := List.getElem_of_mem hx
      have hi : i < m + 1 := by
        rw [hbeq, List.length_set, encode_length] at hi0; exact hi0
      have hbi' : b[i]? = some x := by rw [List.getElem?_eq_getElem hi0, hbi]
      rw [hbeq, List.getElem?_set] at hbi'
      by_cases hik : cfg.tape.head.val = i
      · left
        rw [if_pos hik, if_pos (by rw [encode_length]; exact cfg.tape.head.isLt)] at hbi'
        exact (Option.some.inj hbi').symm
      · right
        rw [if_neg hik, List.getElem?_eq_getElem (by rw [encode_length]; exact hi),
          encode_getElem worig cfg i hi,
          if_neg (fun he => hik (congrArg Fin.val he).symm)] at hbi'
        exact ⟨_, _, _, _, (Option.some.inj hbi').symm⟩
    have hin := hbel (symbol.nonterminal r.input_nonterminal) (by rw [hb2]; simp)
    rcases myhill_rule_inv M embed r hr with
      h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
    · obtain ⟨t, rfl⟩ := h
      simp [cellPendingSym, cellSym] at hin
    · obtain ⟨t, rfl⟩ := h
      simp [cellPendingSym, cellSym] at hin
    · obtain ⟨t, rfl⟩ := h
      simp [cellPendingSym, cellSym] at hin
    · obtain ⟨t, rfl⟩ := h
      simp [cellPendingSym, cellSym] at hin
    · obtain ⟨q, q'', a, a'', t, lb, rb, _, rfl⟩ := h
      simp [cellPendingSym, cellSym] at hin
    · obtain ⟨q, q'', a, a'', t, lb, _, rfl⟩ := h
      simp [cellPendingSym, cellSym] at hin
    · obtain ⟨q, q'', a, a'', t, rb, _, rfl⟩ := h
      simp [cellPendingSym, cellSym] at hin
    · obtain ⟨q, q'', a, a'', t1, t2, rb2, hi, bb, _, rfl⟩ := h
      simp [cellPendingSym, cellSym] at hin
    · obtain ⟨q, q'', a, a'', t1, t2, rb2, hi, bb, lb0, a0, t0, _, rfl⟩ := h
      simp [cellPendingSym, cellSym] at hin
    · -- r-interior step2 (matching dir → GEN)
      sorry
    · obtain ⟨q, q'', a, a'', t1, t2, lb1, hi, bb, _, rfl⟩ := h
      simp [cellPendingSym, cellSym] at hin
    · obtain ⟨q, q'', a, a'', t1, t2, lb1, hi, bb, rb0, a0, t0, _, rfl⟩ := h
      simp [cellPendingSym, cellSym] at hin
    · -- l-interior step2 (matching dir → GEN)
      sorry
    · -- resolution → dead phase (SP_stuck)
      obtain ⟨q'2, a'2, t, lb, rb, dir2, rfl⟩ := h
      simp only [List.nil_append, List.append_nil, List.append_assoc, List.singleton_append]
        at hb2 hc
      have hblen : b.length = m + 1 := by rw [hbeq, List.length_set, encode_length]
      have hul_lt : u.length < m + 1 := by
        have hh := congrArg List.length hb2
        rw [hblen, List.length_append, List.length_cons] at hh; omega
      have hul : u.length = cfg.tape.head.val := by
        by_contra hne
        have h1 : b[u.length]? = some (cellPendingSym lb rb dir2 q'2 a'2 t) := by rw [hb2]; simp
        rw [hbeq, List.getElem?_set, if_neg (Ne.symm hne),
          List.getElem?_eq_getElem (by rw [encode_length]; exact hul_lt),
          encode_getElem worig cfg u.length hul_lt] at h1
        simp [cellPendingSym, cellSym] at h1
      have hcset : c = (encode worig cfg).set cfg.tape.head.val (cellSym lb rb none a'2 t) := by
        have e1 : c = b.set u.length (cellSym lb rb none a'2 t) := by
          rw [hc, hb2]; exact (set_at_length _ _ _ _).symm
        rw [e1, hul, hbeq, List.set_set]
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))
      intro x hx
      obtain ⟨i, hi0, hxi⟩ := List.getElem_of_mem hx
      have hi : i < m + 1 := by rw [hcset, List.length_set, encode_length] at hi0; exact hi0
      have hxi' : c[i]? = some x := by rw [List.getElem?_eq_getElem hi0, hxi]
      rw [hcset, List.getElem?_set] at hxi'
      by_cases hik : cfg.tape.head.val = i
      · rw [if_pos hik, if_pos (by rw [encode_length]; exact cfg.tape.head.isLt)] at hxi'
        exact ⟨lb, rb, a'2, t, (Option.some.inj hxi').symm⟩
      · rw [if_neg hik, List.getElem?_eq_getElem (by rw [encode_length]; exact hi),
          encode_getElem worig cfg i hi, if_neg (fun he => hik (congrArg Fin.val he).symm)] at hxi'
        exact ⟨_, _, _, _, (Option.some.inj hxi').symm⟩
    · obtain ⟨q, a, t, lb, rb, _, rfl⟩ := h
      simp [cellPendingSym, cellSym] at hin
    · -- left propagation: needs a terminal context, absent in a stateless+pending row
      obtain ⟨t1, a, t2, lb, rb, rfl⟩ := h
      have hc2 := hbel (symbol.terminal t1) (by rw [hb2]; simp)
      simp [cellPendingSym, cellSym] at hc2
    · -- right propagation: symmetric
      obtain ⟨a, t1, t2, lb, rb, rfl⟩ := h
      have hc2 := hbel (symbol.terminal t2) (by rw [hb2]; simp)
      simp [cellPendingSym, cellSym] at hc2
  · -- **GEN.** remaining work
    sorry
  · -- **CLEANUP.** remaining work
    sorry

/-- **Soundness.** Every terminal word derived by the Myhill grammar is accepted by the LBA.

The converse of `myhill_complete`; together they give `myhill_language_eq`. The proof is an
induction on the derivation establishing `SoundInv`, then `soundInv_extract`. -/
theorem myhill_sound (M : LBA.Machine Γ Λ) (embed : T ↪ Γ) (w : List T)
    (h : CS_derives (myhillGrammar M embed) [symbol.nonterminal MyhillNT.start]
      (w.map symbol.terminal)) :
    LBA.LanguageViaEmbed M embed w := by
  have hwne : w ≠ [] := by
    rintro rfl
    have hl := cs_derives_length_le (myhillGrammar M embed) h
    simp at hl
  refine soundInv_extract M embed w hwne ?_
  -- Generalise the endpoint so the derivation can be inducted on.
  have key : ∀ s, CS_derives (myhillGrammar M embed)
      [symbol.nonterminal MyhillNT.start] s → SoundInv M embed s := by
    intro s hs
    induction hs with
    | refl => exact soundInv_base M embed
    | @tail b c _ hbc ih =>
        rcases ih with hb | hb | hb | hb | hb | hb
        · -- b = [start]: only the start rules apply (input must be `start`)
          subst hb
          obtain ⟨r, u, v, hr, hb2, hc⟩ := hbc
          have hin : symbol.nonterminal r.input_nonterminal
              ∈ ([symbol.nonterminal MyhillNT.start] : List (symbol T (MyhillNT T Γ Λ))) := by
            rw [hb2]; simp
          rcases myhill_rule_inv M embed r hr with
            h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
          · -- block1 (single cell) → simulation phase (initial config)
            obtain ⟨t, rfl⟩ := h
            simp only [List.nil_append, List.append_nil] at hb2 hc
            obtain ⟨rfl, rfl⟩ := decomp_head hb2.symm (by simp)
            refine Or.inr (Or.inr (Or.inl
              ⟨0, fun _ => t, ⟨M.initial, ⟨fun _ => embed t, ⟨0, Nat.succ_pos 0⟩⟩⟩,
                Relation.ReflTransGen.refl, ?_⟩))
            rw [hc, encode]; simp [List.ofFn_succ, List.ofFn_zero, cellSym]
          · -- block2 (rightmost cell + startAux) → start phase
            obtain ⟨t, rfl⟩ := h
            simp only [List.nil_append, List.append_nil] at hb2 hc
            obtain ⟨rfl, rfl⟩ := decomp_head hb2.symm (by simp)
            refine Or.inr (Or.inl ⟨[t], by simp, ?_⟩)
            rw [hc]; simp [auxCells]
          · obtain ⟨t, rfl⟩ := h; simp at hin
          · obtain ⟨t, rfl⟩ := h; simp at hin
          · obtain ⟨q, q', a, a', t, lb, rb, _, rfl⟩ := h; simp at hin
          · obtain ⟨q, q', a, a', t, lb, _, rfl⟩ := h; simp at hin
          · obtain ⟨q, q', a, a', t, rb, _, rfl⟩ := h; simp at hin
          · obtain ⟨q, q', a, a', t1, t2, rb2, hi, bb, _, rfl⟩ := h; simp at hin
          · obtain ⟨q, q', a, a', t1, t2, rb2, hi, bb, lb0, a0, t0, _, rfl⟩ := h; simp at hin
          · obtain ⟨q', a', t1, t2, lb1, rb2, bb, rfl⟩ := h; simp at hin
          · obtain ⟨q, q', a, a', t1, t2, lb1, hi, bb, _, rfl⟩ := h; simp at hin
          · obtain ⟨q, q', a, a', t1, t2, lb1, hi, bb, rb0, a0, t0, _, rfl⟩ := h; simp at hin
          · obtain ⟨q', a', t1, t2, lb1, rb2, bb, rfl⟩ := h; simp at hin
          · obtain ⟨q', a', t, lb, rb, dir, rfl⟩ := h; simp at hin
          · obtain ⟨q, a, t, lb, rb, _, rfl⟩ := h; simp at hin
          · obtain ⟨t1, a, t2, lb, rb, rfl⟩ := h; simp at hin
          · obtain ⟨a, t1, t2, lb, rb, rfl⟩ := h; simp at hin
        · exact soundInv_step_start M embed hb hbc
        · exact soundInv_step_sim M embed hb hbc
        · exact soundInv_step_pending M embed hb hbc
        · exact soundInv_step_cleanup M embed hb hbc
        · exact (soundInv_step_stuck M embed hb hbc).elim
  exact key _ h

end MyhillConstruction
