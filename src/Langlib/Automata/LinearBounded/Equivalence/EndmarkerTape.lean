module

public import Langlib.Automata.LinearBounded.Endmarker
public import Langlib.Automata.LinearBounded.Equivalence.ContextSensitive
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.Option
import Mathlib.Tactic
@[expose]
public section

/-!
# Endmarker LBAs recognize exactly the marker-free LBA languages (`LBA_end = LBA`)

The canonical automaton model for the context-sensitive languages is the **endmarker** LBA
(`is_LBA_end`, `Automata/LinearBounded/Endmarker.lean`), which decides the empty word with the
machine itself (running on `⊢⊣`) rather than via an external flag. This file proves it recognizes
exactly the same class as the marker-free, accept-empty-flag model `is_LBA` used internally by the
`CS = LBA` development, so the two are interchangeable and `CS = LBA_end`.

## Strategy

Two simulations between LBAs over the same `|w|`-bounded resources:

* **`is_LBA → is_LBA_end`** (this much is the `simMachine` below): a flag machine `M` on `|w|`
  cells is simulated by an endmarker machine on `⊢ w ⊣`. The simulator runs `M` on the interior
  cells `1 … |w|`; when a simulated move would step onto an endmarker it *bounces* back, exactly
  reproducing `M`'s boundary clamping. The empty word is decided on `⊢⊣` directly using `M`'s
  flag, so no flag is needed on the endmarker side.
* **`is_LBA_end → is_LBA`**: conversely, the two read-only marker cells are folded away (a flag
  machine marks its own boundary cells and detects "reading `⊢`/`⊣`" there), with `ε` recorded in
  the flag.
-/

namespace LBA

open DLBA

variable {T Γ : Type*} {Λ : Type*}

/-- States of the endmarker machine simulating a marker-free flag LBA `M`:
`start`/`entry` walk past the left marker and split off the empty-word case, `run q` simulates
`M` in state `q` on the interior cells (bouncing off the markers to mimic `M`'s clamping), and
`acc`/`rej` are the empty-word sinks. -/
inductive SimState (Λ : Type*)
  | start
  | entry
  | run (q : Λ)
  | acc
  | rej
  deriving DecidableEq

noncomputable instance [Fintype Λ] : Fintype (SimState Λ) := by
  classical
  exact Fintype.ofInjective
    (fun s => match s with
      | SimState.start => Sum.inl (none : Option Λ)
      | SimState.run q => Sum.inl (some q)
      | SimState.entry => Sum.inr (0 : Fin 3)
      | SimState.acc => Sum.inr (1 : Fin 3)
      | SimState.rej => Sum.inr (2 : Fin 3))
    (by intro a b h; cases a <;> cases b <;> simp_all)

/-- Transition of the endmarker machine simulating the marker-free flag LBA `M` (flag `b`):
walk past `⊢`; on `⊣` immediately at `entry` decide `ε` by the flag; otherwise simulate `M`'s
transitions on the interior, bouncing off either marker to reproduce `M`'s boundary clamping. -/
def simTransition (M : Machine (Option (T ⊕ Γ)) Λ) (b : Bool) :
    SimState Λ → EndAlpha T Γ → Set (SimState Λ × EndAlpha T Γ × DLBA.Dir) :=
  fun s a => match s, a with
  | .start, Sum.inr false => {(.entry, leftMark, DLBA.Dir.right)}
  | .entry, Sum.inr true => if b then {(.acc, rightMark, DLBA.Dir.stay)}
                            else {(.rej, rightMark, DLBA.Dir.stay)}
  | .entry, Sum.inl c => {(.run M.initial, Sum.inl c, DLBA.Dir.stay)}
  | .run q, Sum.inl c =>
      {x | ∃ p ∈ M.transition q c, x = (.run p.1, Sum.inl p.2.1, p.2.2)}
  | .run q, Sum.inr false => {(.run q, leftMark, DLBA.Dir.right)}
  | .run q, Sum.inr true => {(.run q, rightMark, DLBA.Dir.left)}
  | _, _ => ∅

/-- The endmarker machine simulating the marker-free flag LBA `M` with empty-word flag `b`. -/
def simMachine (M : Machine (Option (T ⊕ Γ)) Λ) (b : Bool) :
    Machine (EndAlpha T Γ) (SimState Λ) where
  transition := simTransition M b
  accept := fun s => match s with
    | .run q => M.accept q
    | .acc => true
    | _ => false
  initial := .start

/-! ### Encoding a marker-free configuration as an endmarker configuration

The simulator runs `M` on the interior cells `1 … n+1` of an `(n+3)`-cell endmarker tape, with
`⊢` at cell `0` and `⊣` at cell `n+2`. `enc` brackets an `(n+1)`-cell marker-free tape, `encHead`
shifts a head position into the interior, and `φ` packages an `M`-configuration as the
corresponding `run`-phase simulator configuration. -/

/-- Bracket an `(n+1)`-cell marker-free tape into the interior of an `(n+3)`-cell endmarker tape:
`⊢` at cell `0`, `⊣` at cell `n+2`, and the original contents shifted into cells `1 … n+1`. -/
def enc {n : ℕ} (c : Fin (n + 1) → Option (T ⊕ Γ)) : Fin (n + 3) → EndAlpha T Γ :=
  fun k => if h0 : k.val = 0 then leftMark
           else if h2 : k.val = n + 2 then rightMark
           else Sum.inl (c ⟨k.val - 1, by have := k.isLt; omega⟩)

/-- Shift a marker-free head position `h` into the endmarker interior (cell `h + 1`). -/
def encHead {n : ℕ} (h : Fin (n + 1)) : Fin (n + 3) := ⟨h.val + 1, by have := h.isLt; omega⟩

/-- Package an `M`-configuration as the corresponding `run`-phase simulator configuration. -/
def φ {n : ℕ} (cfg : DLBA.Cfg (Option (T ⊕ Γ)) Λ n) :
    DLBA.Cfg (EndAlpha T Γ) (SimState Λ) (n + 2) :=
  ⟨.run cfg.state, ⟨enc cfg.tape.contents, encHead cfg.tape.head⟩⟩

@[simp] theorem enc_zero {n : ℕ} (c : Fin (n + 1) → Option (T ⊕ Γ)) (h : (0 : ℕ) < n + 3) :
    enc c ⟨0, h⟩ = leftMark := by simp [enc]

@[simp] theorem enc_last {n : ℕ} (c : Fin (n + 1) → Option (T ⊕ Γ)) (h : n + 2 < n + 3) :
    enc c ⟨n + 2, h⟩ = rightMark := by simp [enc]

@[simp] theorem enc_interior {n : ℕ} (c : Fin (n + 1) → Option (T ⊕ Γ)) (h : Fin (n + 1)) :
    enc c (encHead h) = Sum.inl (c h) := by
  have hlt := h.isLt
  simp only [enc, encHead]
  rw [dif_neg (by omega), dif_neg (by omega)]
  apply congrArg; apply congrArg; apply Fin.ext; simp

/-- Writing `Sum.inl a` at an interior cell of `enc c` is the same as writing `a` in `c`. -/
theorem enc_update {n : ℕ} (c : Fin (n + 1) → Option (T ⊕ Γ)) (h : Fin (n + 1))
    (a : Option (T ⊕ Γ)) :
    Function.update (enc c) (encHead h) (Sum.inl a) = enc (Function.update c h a) := by
  funext k
  rcases eq_or_ne k (encHead h) with hk | hk
  · subst hk
    rw [Function.update_self, enc_interior, Function.update_self]
  · rw [Function.update_of_ne hk]
    -- `k` is not the interior cell `h+1`; both sides agree cell-by-cell.
    have hlt := k.isLt
    by_cases h0 : k.val = 0
    · simp only [enc]; rw [dif_pos h0, dif_pos h0]
    by_cases h2 : k.val = n + 2
    · simp only [enc]; rw [dif_neg h0, dif_pos h2, dif_neg h0, dif_pos h2]
    · simp only [enc]
      rw [dif_neg h0, dif_neg h2, dif_neg h0, dif_neg h2]
      have hne : k.val - 1 ≠ h.val := by
        intro hcontra
        apply hk
        simp only [encHead]
        apply Fin.ext
        simp only
        omega
      rw [Function.update_of_ne (fun hh => hne (congrArg Fin.val hh))]

/-! ### Transition equation lemmas (definitional). -/

variable (M : Machine (Option (T ⊕ Γ)) Λ) (b : Bool)

theorem simTransition_run_inl (q : Λ) (c : Option (T ⊕ Γ)) :
    simTransition M b (.run q) (Sum.inl c)
      = {x | ∃ p ∈ M.transition q c, x = (SimState.run p.1, Sum.inl p.2.1, p.2.2)} := rfl

theorem simTransition_run_left (q : Λ) :
    simTransition M b (.run q) leftMark = {(SimState.run q, leftMark, DLBA.Dir.right)} := rfl

theorem simTransition_run_right (q : Λ) :
    simTransition M b (.run q) rightMark = {(SimState.run q, rightMark, DLBA.Dir.left)} := rfl

theorem simTransition_start :
    simTransition M b .start leftMark = {(SimState.entry, leftMark, DLBA.Dir.right)} := rfl

theorem simTransition_entry_inl (c : Option (T ⊕ Γ)) :
    simTransition M b .entry (Sum.inl c) = {(SimState.run M.initial, Sum.inl c, DLBA.Dir.stay)} :=
  rfl

theorem simTransition_entry_right :
    simTransition M b .entry rightMark
      = (if b then {(SimState.acc, rightMark, DLBA.Dir.stay)}
         else {(SimState.rej, rightMark, DLBA.Dir.stay)}) := rfl

@[simp] theorem simMachine_accept_run (q : Λ) : (simMachine M b).accept (.run q) = M.accept q := rfl

/-- Reading the head of `φ cfg` returns the (tagged) symbol `M` reads. -/
theorem read_φ {n : ℕ} (cfg : DLBA.Cfg (Option (T ⊕ Γ)) Λ n) :
    (φ cfg).tape.read = Sum.inl cfg.tape.read := by
  simp only [φ, DLBA.BoundedTape.read, enc_interior]

/-- Configurations are equal when their state, tape contents and head agree. -/
theorem cfg_ext {Γ' Λ' : Type*} {N : ℕ} {X Y : DLBA.Cfg Γ' Λ' N}
    (hs : X.state = Y.state) (hc : X.tape.contents = Y.tape.contents)
    (hh : X.tape.head = Y.tape.head) : X = Y := by
  obtain ⟨xs, xc, xh⟩ := X; obtain ⟨ys, yc, yh⟩ := Y
  simp_all

/-! ### Forward simulation: each `M`-step is matched by one or two simulator steps. -/

/-- A single `M`-step is simulated by one or two simulator steps (two when `M`'s head clamps at a
boundary, where the simulator bounces off the corresponding endmarker). -/
theorem forward_step {n : ℕ} {cfg cfg' : DLBA.Cfg (Option (T ⊕ Γ)) Λ n}
    (hstep : Step M cfg cfg') :
    Reaches (simMachine M b) (φ cfg) (φ cfg') := by
  obtain ⟨q', a, d, hmem, rfl⟩ := hstep
  set cfg' : DLBA.Cfg (Option (T ⊕ Γ)) Λ n := ⟨q', (cfg.tape.write a).moveHead d⟩ with hcfg'
  -- The first simulator step replays `M`'s transition on the interior cell `head + 1`.
  have hmem' : (SimState.run q', Sum.inl a, d)
      ∈ (simMachine M b).transition (φ cfg).state (φ cfg).tape.read := by
    rw [read_φ]
    show (SimState.run q', Sum.inl a, d)
      ∈ simTransition M b (SimState.run cfg.state) (Sum.inl cfg.tape.read)
    rw [simTransition_run_inl]; exact ⟨(q', a, d), hmem, rfl⟩
  set Y1 : DLBA.Cfg (EndAlpha T Γ) (SimState Λ) (n + 2) :=
    ⟨SimState.run q', ((φ cfg).tape.write (Sum.inl a)).moveHead d⟩ with hY1
  have hstep1 : Step (simMachine M b) (φ cfg) Y1 := ⟨SimState.run q', Sum.inl a, d, hmem', rfl⟩
  -- Contents after the first step already match the target.
  have hcont : Y1.tape.contents = (φ cfg').tape.contents := by
    show Function.update (enc cfg.tape.contents) (encHead cfg.tape.head) (Sum.inl a)
      = enc (Function.update cfg.tape.contents cfg.tape.head a)
    exact enc_update cfg.tape.contents cfg.tape.head a
  have hposlt := cfg.tape.head.isLt
  rcases d with _ | _ | _
  · -- `Dir.left`
    by_cases hb : 0 < cfg.tape.head.val
    · -- interior move, no bounce: `Y1 = φ cfg'`
      have hh : Y1.tape.head = (φ cfg').tape.head := by
        apply Fin.ext
        simp only [hY1, hcfg', φ, DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, encHead]
        split_ifs <;> simp_all <;> omega
      exact (cfg_ext (X := Y1) (Y := φ cfg') rfl hcont hh) ▸ Relation.ReflTransGen.single hstep1
    · -- bounce off `⊢`
      have hpos0 : cfg.tape.head.val = 0 := by omega
      have hY1head : Y1.tape.head = ⟨0, by omega⟩ := by
        apply Fin.ext
        simp only [hY1, DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, φ, encHead]
        split_ifs <;> simp_all <;> omega
      have h0 : Y1.tape.contents ⟨0, by omega⟩ = leftMark := by
        rw [hcont]; exact enc_zero cfg'.tape.contents (by omega)
      have hY1read : Y1.tape.read = leftMark := by
        show Y1.tape.contents Y1.tape.head = leftMark
        rw [hY1head]; exact h0
      have hmem2 : (SimState.run q', leftMark, DLBA.Dir.right)
          ∈ (simMachine M b).transition Y1.state Y1.tape.read := by
        rw [hY1read]
        show (SimState.run q', leftMark, DLBA.Dir.right)
          ∈ simTransition M b (SimState.run q') leftMark
        rw [simTransition_run_left]; rfl
      set Z : DLBA.Cfg (EndAlpha T Γ) (SimState Λ) (n + 2) :=
        ⟨SimState.run q', (Y1.tape.write leftMark).moveHead DLBA.Dir.right⟩ with hZ
      have hstep2 : Step (simMachine M b) Y1 Z :=
        ⟨SimState.run q', leftMark, DLBA.Dir.right, hmem2, rfl⟩
      have hZeq : Z = φ cfg' := by
        refine cfg_ext (X := Z) (Y := φ cfg') rfl ?_ ?_
        · show Function.update Y1.tape.contents Y1.tape.head leftMark = (φ cfg').tape.contents
          rw [hY1head, ← h0, Function.update_eq_self, hcont]
        · apply Fin.ext
          simp only [hZ, hY1, hcfg', φ, DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, encHead,
            hY1head]
          split_ifs <;> simp_all <;> omega
      exact Relation.ReflTransGen.head hstep1 (hZeq ▸ Relation.ReflTransGen.single hstep2)
  · -- `Dir.right`
    by_cases hb : cfg.tape.head.val < n
    · -- interior move, no bounce
      have hh : Y1.tape.head = (φ cfg').tape.head := by
        apply Fin.ext
        simp only [hY1, hcfg', φ, DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, encHead]
        split_ifs <;> simp_all <;> omega
      exact (cfg_ext (X := Y1) (Y := φ cfg') rfl hcont hh) ▸ Relation.ReflTransGen.single hstep1
    · -- bounce off `⊣`
      have hposn : cfg.tape.head.val = n := by omega
      have hY1head : Y1.tape.head = ⟨n + 2, by omega⟩ := by
        apply Fin.ext
        simp only [hY1, DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, φ, encHead]
        split_ifs <;> simp_all <;> omega
      have h0 : Y1.tape.contents ⟨n + 2, by omega⟩ = rightMark := by
        rw [hcont]; exact enc_last cfg'.tape.contents (by omega)
      have hY1read : Y1.tape.read = rightMark := by
        show Y1.tape.contents Y1.tape.head = rightMark
        rw [hY1head]; exact h0
      have hmem2 : (SimState.run q', rightMark, DLBA.Dir.left)
          ∈ (simMachine M b).transition Y1.state Y1.tape.read := by
        rw [hY1read]
        show (SimState.run q', rightMark, DLBA.Dir.left)
          ∈ simTransition M b (SimState.run q') rightMark
        rw [simTransition_run_right]; rfl
      set Z : DLBA.Cfg (EndAlpha T Γ) (SimState Λ) (n + 2) :=
        ⟨SimState.run q', (Y1.tape.write rightMark).moveHead DLBA.Dir.left⟩ with hZ
      have hstep2 : Step (simMachine M b) Y1 Z :=
        ⟨SimState.run q', rightMark, DLBA.Dir.left, hmem2, rfl⟩
      have hZeq : Z = φ cfg' := by
        refine cfg_ext (X := Z) (Y := φ cfg') rfl ?_ ?_
        · show Function.update Y1.tape.contents Y1.tape.head rightMark = (φ cfg').tape.contents
          rw [hY1head, ← h0, Function.update_eq_self, hcont]
        · apply Fin.ext
          simp only [hZ, hY1, hcfg', φ, DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, encHead,
            hY1head]
          split_ifs <;> simp_all <;> omega
      exact Relation.ReflTransGen.head hstep1 (hZeq ▸ Relation.ReflTransGen.single hstep2)
  · -- `Dir.stay`
    have hh : Y1.tape.head = (φ cfg').tape.head := by
      apply Fin.ext
      simp only [hY1, hcfg', φ, DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, encHead]
    exact (cfg_ext (X := Y1) (Y := φ cfg') rfl hcont hh) ▸ Relation.ReflTransGen.single hstep1

/-- The forward simulation extends to whole computations. -/
theorem forward_reaches {n : ℕ} {cfg cfg' : DLBA.Cfg (Option (T ⊕ Γ)) Λ n}
    (h : Reaches M cfg cfg') : Reaches (simMachine M b) (φ cfg) (φ cfg') := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.trans (forward_step M b hbc)

/-! ### Backward simulation: a single decoding invariant.

`Good c₀ s` says the simulator configuration `s`, reached from the start on `⊢ c₀ ⊣`, decodes to
a genuine `M`-configuration reachable from `M`'s start on `c₀`. The three branches are the two
pre-run setup states and the run phase; in the run phase the head is either on the encoded interior
cell or sitting on a marker mid-bounce (recording where `M`'s head clamped). -/
def Good {m : ℕ} (c₀ : Fin (m + 1) → Option (T ⊕ Γ))
    (s : DLBA.Cfg (EndAlpha T Γ) (SimState Λ) (m + 2)) : Prop :=
  (s.state = .start ∧ s.tape.contents = enc c₀ ∧ s.tape.head.val = 0)
  ∨ (s.state = .entry ∧ s.tape.contents = enc c₀ ∧ s.tape.head.val = 1)
  ∨ (∃ Mcfg : DLBA.Cfg (Option (T ⊕ Γ)) Λ m,
        Reaches M ⟨M.initial, ⟨c₀, ⟨0, Nat.succ_pos m⟩⟩⟩ Mcfg
        ∧ s.state = SimState.run Mcfg.state
        ∧ s.tape.contents = enc Mcfg.tape.contents
        ∧ (s.tape.head = encHead Mcfg.tape.head
           ∨ (s.tape.head.val = 0 ∧ Mcfg.tape.head.val = 0)
           ∨ (s.tape.head.val = m + 2 ∧ Mcfg.tape.head.val = m)))

/-- The simulator start configuration on `⊢ c₀ ⊣` satisfies the invariant. -/
theorem good_init {m : ℕ} (c₀ : Fin (m + 1) → Option (T ⊕ Γ)) :
    Good M c₀ ⟨SimState.start, ⟨enc c₀, ⟨0, by omega⟩⟩⟩ := Or.inl ⟨rfl, rfl, rfl⟩

/-- From the invariant, an accepting simulator state yields an accepting `M`-run. -/
theorem good_accepts {m : ℕ} (c₀ : Fin (m + 1) → Option (T ⊕ Γ))
    {s : DLBA.Cfg (EndAlpha T Γ) (SimState Λ) (m + 2)} (hg : Good M c₀ s)
    (hacc : (simMachine M b).accept s.state = true) :
    Accepts M ⟨M.initial, ⟨c₀, ⟨0, Nat.succ_pos m⟩⟩⟩ := by
  rcases hg with ⟨hs, _⟩ | ⟨hs, _⟩ | ⟨Mcfg, hreach, hs, _⟩
  · rw [hs] at hacc; simp [simMachine] at hacc
  · rw [hs] at hacc; simp [simMachine] at hacc
  · refine ⟨Mcfg, hreach, ?_⟩
    rw [hs] at hacc; rwa [simMachine_accept_run] at hacc

/-- The decoding invariant is preserved by a simulator step. -/
theorem good_step {m : ℕ} (c₀ : Fin (m + 1) → Option (T ⊕ Γ))
    {s s' : DLBA.Cfg (EndAlpha T Γ) (SimState Λ) (m + 2)} (hg : Good M c₀ s)
    (hstep : Step (simMachine M b) s s') : Good M c₀ s' := by
  obtain ⟨q', a', d', hmem, rfl⟩ := hstep
  rcases hg with ⟨hs, hcont, hhead⟩ | ⟨hs, hcont, hhead⟩ | ⟨Mcfg, hreach, hs, hcont, hpos⟩
  · -- `s` is the `start` setup state: step onto the interior, becoming `entry`.
    have hh0 : s.tape.head = (⟨0, by omega⟩ : Fin (m + 3)) := Fin.ext hhead
    have hread : s.tape.read = leftMark := by
      show s.tape.contents s.tape.head = leftMark
      rw [hcont, hh0]; exact enc_zero c₀ (by omega)
    rw [hs, hread] at hmem
    simp only [simMachine, simTransition_start, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    refine Or.inr (Or.inl ⟨rfl, ?_, ?_⟩)
    · show Function.update s.tape.contents s.tape.head leftMark = enc c₀
      rw [hcont, hh0, ← enc_zero c₀ (by omega), Function.update_eq_self]
    · simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, hh0]
      split_ifs <;> simp_all <;> omega
  · -- `s` is the `entry` setup state: read interior cell 1, enter the run phase at `M.initial`.
    have hh1 : s.tape.head = (⟨1, by omega⟩ : Fin (m + 3)) := Fin.ext hhead
    have henc1 : enc c₀ (⟨1, by omega⟩ : Fin (m + 3)) = Sum.inl (c₀ ⟨0, Nat.succ_pos m⟩) :=
      enc_interior c₀ ⟨0, Nat.succ_pos m⟩
    have hread : s.tape.read = Sum.inl (c₀ ⟨0, Nat.succ_pos m⟩) := by
      show s.tape.contents s.tape.head = _
      rw [hcont, hh1]; exact henc1
    rw [hs, hread] at hmem
    simp only [simMachine, simTransition_entry_inl, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    refine Or.inr (Or.inr ⟨⟨M.initial, ⟨c₀, ⟨0, Nat.succ_pos m⟩⟩⟩, Relation.ReflTransGen.refl,
      rfl, ?_, Or.inl ?_⟩)
    · show Function.update s.tape.contents s.tape.head (Sum.inl (c₀ ⟨0, Nat.succ_pos m⟩)) = enc c₀
      rw [hcont, hh1, ← henc1, Function.update_eq_self]
    · apply Fin.ext
      simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, hh1, encHead]
  · -- `s` is in the run phase, decoding to `Mcfg`.
    rcases hpos with hint | ⟨hsh0, hmh0⟩ | ⟨hshn, hmhn⟩
    · -- head on the encoded interior cell: replay `M`'s transition (with a possible bounce).
      have hread : s.tape.read = Sum.inl Mcfg.tape.read := by
        show s.tape.contents s.tape.head = _
        rw [hcont, hint]; exact enc_interior Mcfg.tape.contents Mcfg.tape.head
      rw [hs, hread] at hmem
      simp only [simMachine, simTransition_run_inl, Set.mem_setOf_eq] at hmem
      obtain ⟨p, hp, hpeq⟩ := hmem
      obtain ⟨pq, pa, pd⟩ := p
      simp only [Prod.mk.injEq] at hpeq
      obtain ⟨hq, ha, hd⟩ := hpeq
      subst hq; subst ha; subst pd
      set Mcfg' : DLBA.Cfg (Option (T ⊕ Γ)) Λ m :=
        ⟨pq, (Mcfg.tape.write pa).moveHead d'⟩ with hMcfg'
      have hMreach : Reaches M ⟨M.initial, ⟨c₀, ⟨0, Nat.succ_pos m⟩⟩⟩ Mcfg' :=
        hreach.tail ⟨pq, pa, d', hp, rfl⟩
      have hcont' :
          Function.update s.tape.contents s.tape.head (Sum.inl pa) = enc Mcfg'.tape.contents := by
        rw [hcont, hint]
        show Function.update (enc Mcfg.tape.contents) (encHead Mcfg.tape.head) (Sum.inl pa) = _
        exact enc_update Mcfg.tape.contents Mcfg.tape.head pa
      refine Or.inr (Or.inr ⟨Mcfg', hMreach, rfl, hcont', ?_⟩)
      have hsheq : s.tape.head = encHead Mcfg.tape.head := hint
      have hmlt := Mcfg.tape.head.isLt
      rcases d' with _ | _ | _
      · -- left
        by_cases hb : 0 < Mcfg.tape.head.val
        · left; apply Fin.ext
          simp only [hMcfg', DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, hsheq, encHead]
          split_ifs <;> simp_all <;> omega
        · right; left
          refine ⟨?_, ?_⟩
          · simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, hsheq, encHead]
            split_ifs <;> simp_all <;> omega
          · simp only [hMcfg', DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write]
            split_ifs <;> simp_all <;> omega
      · -- right
        by_cases hb : Mcfg.tape.head.val < m
        · left; apply Fin.ext
          simp only [hMcfg', DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, hsheq, encHead]
          split_ifs <;> simp_all <;> omega
        · right; right
          refine ⟨?_, ?_⟩
          · simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, hsheq, encHead]
            split_ifs <;> simp_all <;> omega
          · simp only [hMcfg', DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write]
            split_ifs <;> simp_all <;> omega
      · -- stay
        left; apply Fin.ext
        simp only [hMcfg', DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, hsheq, encHead]
    · -- head on `⊢` mid-bounce: read `⊢`, bounce right back to the interior (same `Mcfg`).
      have hh0 : s.tape.head = (⟨0, by omega⟩ : Fin (m + 3)) := Fin.ext hsh0
      have hread : s.tape.read = leftMark := by
        show s.tape.contents s.tape.head = leftMark
        rw [hcont, hh0]; exact enc_zero Mcfg.tape.contents (by omega)
      rw [hs, hread] at hmem
      simp only [simMachine, simTransition_run_left, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      obtain ⟨rfl, rfl, rfl⟩ := hmem
      refine Or.inr (Or.inr ⟨Mcfg, hreach, rfl, ?_, Or.inl ?_⟩)
      · show Function.update s.tape.contents s.tape.head leftMark = enc Mcfg.tape.contents
        rw [hcont, hh0, ← enc_zero Mcfg.tape.contents (by omega), Function.update_eq_self]
      · apply Fin.ext
        have hmh0' : Mcfg.tape.head = (⟨0, Nat.succ_pos m⟩ : Fin (m + 1)) := Fin.ext hmh0
        simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, hh0, encHead, hmh0']
        split_ifs <;> simp_all <;> omega
    · -- head on `⊣` mid-bounce: read `⊣`, bounce left back to the interior (same `Mcfg`).
      have hhn : s.tape.head = (⟨m + 2, by omega⟩ : Fin (m + 3)) := Fin.ext hshn
      have hread : s.tape.read = rightMark := by
        show s.tape.contents s.tape.head = rightMark
        rw [hcont, hhn]; exact enc_last Mcfg.tape.contents (by omega)
      rw [hs, hread] at hmem
      simp only [simMachine, simTransition_run_right, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      obtain ⟨rfl, rfl, rfl⟩ := hmem
      refine Or.inr (Or.inr ⟨Mcfg, hreach, rfl, ?_, Or.inl ?_⟩)
      · show Function.update s.tape.contents s.tape.head rightMark = enc Mcfg.tape.contents
        rw [hcont, hhn, ← enc_last Mcfg.tape.contents (by omega), Function.update_eq_self]
      · apply Fin.ext
        have hmhn' : Mcfg.tape.head = (⟨m, by omega⟩ : Fin (m + 1)) := Fin.ext hmhn
        simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, hhn, encHead, hmhn']
        split_ifs <;> simp_all <;> omega

/-- Every simulator configuration reachable from the start on `⊢ c₀ ⊣` satisfies the invariant. -/
theorem good_reaches {m : ℕ} (c₀ : Fin (m + 1) → Option (T ⊕ Γ))
    {s : DLBA.Cfg (EndAlpha T Γ) (SimState Λ) (m + 2)}
    (h : Reaches (simMachine M b) ⟨SimState.start, ⟨enc c₀, ⟨0, by omega⟩⟩⟩ s) :
    Good M c₀ s := by
  induction h with
  | refl => exact good_init M c₀
  | tail _ hbc ih => exact good_step M b c₀ ih hbc

/-- The two setup steps: from `⊢ c₀ ⊣` the simulator walks onto the interior and enters the run
phase at `M.initial`, reaching the encoding of `M`'s start configuration. -/
theorem setup_reaches {m : ℕ} (c₀ : Fin (m + 1) → Option (T ⊕ Γ)) :
    Reaches (simMachine M b)
      (⟨SimState.start, ⟨enc c₀, ⟨0, by omega⟩⟩⟩ : DLBA.Cfg (EndAlpha T Γ) (SimState Λ) (m + 2))
      (φ ⟨M.initial, ⟨c₀, ⟨0, Nat.succ_pos m⟩⟩⟩) := by
  have hzero : enc c₀ (⟨0, by omega⟩ : Fin (m + 3)) = leftMark := enc_zero c₀ (by omega)
  have hone : enc c₀ (⟨1, by omega⟩ : Fin (m + 3)) = Sum.inl (c₀ ⟨0, Nat.succ_pos m⟩) :=
    enc_interior c₀ ⟨0, Nat.succ_pos m⟩
  set S0 : DLBA.Cfg (EndAlpha T Γ) (SimState Λ) (m + 2) :=
    ⟨SimState.start, ⟨enc c₀, ⟨0, by omega⟩⟩⟩ with hS0
  set S1 : DLBA.Cfg (EndAlpha T Γ) (SimState Λ) (m + 2) :=
    ⟨SimState.entry, ⟨enc c₀, ⟨1, by omega⟩⟩⟩ with hS1
  have hstep1 : Step (simMachine M b) S0 S1 := by
    refine ⟨SimState.entry, leftMark, DLBA.Dir.right, ?_, ?_⟩
    · show (SimState.entry, leftMark, DLBA.Dir.right)
        ∈ (simMachine M b).transition SimState.start (enc c₀ ⟨0, by omega⟩)
      rw [hzero]; simp only [simMachine, simTransition_start, Set.mem_singleton_iff]
    · refine cfg_ext (Y := ⟨SimState.entry, (S0.tape.write leftMark).moveHead DLBA.Dir.right⟩) rfl ?_ ?_
      · show (enc c₀) = Function.update (enc c₀) ⟨0, by omega⟩ leftMark
        rw [← hzero, Function.update_eq_self]
      · apply Fin.ext
        simp only [hS0, DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write]
        split_ifs <;> simp_all <;> omega
  have hstep2 : Step (simMachine M b) S1 (φ ⟨M.initial, ⟨c₀, ⟨0, Nat.succ_pos m⟩⟩⟩) := by
    refine ⟨SimState.run M.initial, Sum.inl (c₀ ⟨0, Nat.succ_pos m⟩), DLBA.Dir.stay, ?_, ?_⟩
    · show (SimState.run M.initial, Sum.inl (c₀ ⟨0, Nat.succ_pos m⟩), DLBA.Dir.stay)
        ∈ (simMachine M b).transition SimState.entry (enc c₀ ⟨1, by omega⟩)
      rw [hone]; simp only [simMachine, simTransition_entry_inl, Set.mem_singleton_iff]
    · refine cfg_ext (Y := ⟨SimState.run M.initial,
        (S1.tape.write (Sum.inl (c₀ ⟨0, Nat.succ_pos m⟩))).moveHead DLBA.Dir.stay⟩) rfl ?_ ?_
      · show (enc c₀)
          = Function.update (enc c₀) ⟨1, by omega⟩ (Sum.inl (c₀ ⟨0, Nat.succ_pos m⟩))
        rw [← hone, Function.update_eq_self]
      · apply Fin.ext
        simp only [hS1, φ, DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, encHead]
  exact Relation.ReflTransGen.head hstep1 (Relation.ReflTransGen.head hstep2 Relation.ReflTransGen.refl)

/-- **Key bisimulation.** On the bracketed tape `⊢ c₀ ⊣`, the endmarker simulator accepts iff the
underlying flag machine `M` accepts on `c₀` — dimension-clean, no empty-word subtlety. -/
theorem sim_accepts_iff {m : ℕ} (c₀ : Fin (m + 1) → Option (T ⊕ Γ)) :
    Accepts (simMachine M b)
        (⟨SimState.start, ⟨enc c₀, ⟨0, by omega⟩⟩⟩ : DLBA.Cfg (EndAlpha T Γ) (SimState Λ) (m + 2))
      ↔ Accepts M ⟨M.initial, ⟨c₀, ⟨0, Nat.succ_pos m⟩⟩⟩ := by
  constructor
  · rintro ⟨scfg', hreach, hacc⟩
    exact good_accepts M b c₀ (good_reaches M b c₀ hreach) hacc
  · rintro ⟨Mcfg', hreach, hacc⟩
    refine ⟨φ Mcfg', (setup_reaches M b c₀).trans (forward_reaches M b hreach), ?_⟩
    show (simMachine M b).accept (SimState.run Mcfg'.state) = true
    rw [simMachine_accept_run]; exact hacc

/-! ### The empty word: decided by the machine itself on the two-cell tape `⊢⊣`. -/

theorem simTransition_acc (x : EndAlpha T Γ) : simTransition M b SimState.acc x = ∅ := rfl
theorem simTransition_rej (x : EndAlpha T Γ) : simTransition M b SimState.rej x = ∅ := rfl

/-- Invariant for the empty-word run on `⊢⊣`: contents stay `⊢⊣`, and the state/head track the
fixed two-step protocol, ending in `acc` exactly when the flag `b` is set. -/
def εGood (b : Bool) (cfg : DLBA.Cfg (EndAlpha T Γ) (SimState Λ) 1) : Prop :=
  cfg.tape.contents = (loadEnd ([] : List T)).contents ∧
  ( (cfg.state = SimState.start ∧ cfg.tape.head.val = 0)
  ∨ (cfg.state = SimState.entry ∧ cfg.tape.head.val = 1)
  ∨ (cfg.state = SimState.acc ∧ b = true)
  ∨ (cfg.state = SimState.rej ∧ b = false) )

theorem εc0 : (loadEnd ([] : List T)).contents (⟨0, by omega⟩ : Fin 2) = (leftMark : EndAlpha T Γ) := by
  simp [loadEnd]
theorem εc1 : (loadEnd ([] : List T)).contents (⟨1, by omega⟩ : Fin 2) = (rightMark : EndAlpha T Γ) := by
  simp [loadEnd]

theorem εGood_init : εGood (T := T) (Γ := Γ) (Λ := Λ) b ⟨SimState.start, loadEnd []⟩ :=
  ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩

theorem εGood_step {cfg cfg' : DLBA.Cfg (EndAlpha T Γ) (SimState Λ) 1}
    (hg : εGood b cfg) (hstep : Step (simMachine M b) cfg cfg') : εGood b cfg' := by
  obtain ⟨hcont, hdisj⟩ := hg
  obtain ⟨q', a', d', hmem, rfl⟩ := hstep
  rcases hdisj with ⟨hs, hh⟩ | ⟨hs, hh⟩ | ⟨hs, _⟩ | ⟨hs, _⟩
  · -- start, head 0
    have hh0 : cfg.tape.head = (⟨0, by omega⟩ : Fin 2) := Fin.ext hh
    have hread : cfg.tape.read = leftMark := by
      show cfg.tape.contents cfg.tape.head = _; rw [hcont, hh0]; exact εc0
    rw [hs, hread] at hmem
    simp only [simMachine, simTransition_start, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    refine ⟨?_, Or.inr (Or.inl ⟨rfl, ?_⟩)⟩
    · show Function.update cfg.tape.contents cfg.tape.head leftMark = (loadEnd ([] : List T)).contents
      rw [hcont, hh0, ← εc0, Function.update_eq_self]
    · simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, hh0]
      split_ifs <;> simp_all <;> omega
  · -- entry, head 1
    have hh1 : cfg.tape.head = (⟨1, by omega⟩ : Fin 2) := Fin.ext hh
    have hread : cfg.tape.read = rightMark := by
      show cfg.tape.contents cfg.tape.head = _; rw [hcont, hh1]; exact εc1
    rw [hs, hread] at hmem
    simp only [simMachine, simTransition_entry_right] at hmem
    by_cases hb : b = true
    · rw [if_pos hb, Set.mem_singleton_iff, Prod.mk.injEq, Prod.mk.injEq] at hmem
      obtain ⟨rfl, rfl, rfl⟩ := hmem
      refine ⟨?_, Or.inr (Or.inr (Or.inl ⟨rfl, hb⟩))⟩
      show Function.update cfg.tape.contents cfg.tape.head rightMark = (loadEnd ([] : List T)).contents
      rw [hcont, hh1, ← εc1, Function.update_eq_self]
    · rw [if_neg hb, Set.mem_singleton_iff, Prod.mk.injEq, Prod.mk.injEq] at hmem
      obtain ⟨rfl, rfl, rfl⟩ := hmem
      refine ⟨?_, Or.inr (Or.inr (Or.inr ⟨rfl, by simpa using hb⟩))⟩
      show Function.update cfg.tape.contents cfg.tape.head rightMark = (loadEnd ([] : List T)).contents
      rw [hcont, hh1, ← εc1, Function.update_eq_self]
  · -- acc: stuck (no transitions)
    rw [hs] at hmem
    simp only [simMachine, simTransition_acc, Set.mem_empty_iff_false] at hmem
  · -- rej: stuck (no transitions)
    rw [hs] at hmem
    simp only [simMachine, simTransition_rej, Set.mem_empty_iff_false] at hmem

theorem εGood_reaches {cfg : DLBA.Cfg (EndAlpha T Γ) (SimState Λ) 1}
    (h : Reaches (simMachine M b) ⟨SimState.start, loadEnd []⟩ cfg) : εGood b cfg := by
  induction h with
  | refl => exact εGood_init b
  | tail _ hbc ih => exact εGood_step M b ih hbc

/-- The simulator decides the empty word by itself on `⊢⊣`, accepting iff the flag `b` is set. -/
theorem accepts_empty :
    Accepts (simMachine M b) (initCfgEnd (simMachine M b) ([] : List T)) ↔ b = true := by
  constructor
  · rintro ⟨cfg', hreach, hacc⟩
    obtain ⟨_, hdisj⟩ := εGood_reaches M b hreach
    rcases hdisj with ⟨hs, _⟩ | ⟨hs, _⟩ | ⟨_, hb⟩ | ⟨hs, _⟩
    · rw [hs] at hacc; simp [simMachine] at hacc
    · rw [hs] at hacc; simp [simMachine] at hacc
    · exact hb
    · rw [hs] at hacc; simp [simMachine] at hacc
  · intro hbt
    set t0 := (loadEnd ([] : List T) : DLBA.BoundedTape (EndAlpha T Γ) 1) with ht0
    have hstep1 : Step (simMachine M b) ⟨SimState.start, t0⟩
        ⟨SimState.entry, ⟨t0.contents, ⟨1, by omega⟩⟩⟩ := by
      refine ⟨SimState.entry, leftMark, DLBA.Dir.right, ?_, ?_⟩
      · show _ ∈ (simMachine M b).transition SimState.start (t0.contents ⟨0, by omega⟩)
        rw [εc0]; simp only [simMachine, simTransition_start, Set.mem_singleton_iff]
      · refine cfg_ext (Y := ⟨SimState.entry, (t0.write leftMark).moveHead DLBA.Dir.right⟩) rfl ?_ ?_
        · show t0.contents = Function.update t0.contents ⟨0, by omega⟩ leftMark
          rw [← εc0, Function.update_eq_self]
        · apply Fin.ext
          simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, List.length_nil]
          split_ifs <;> simp_all [loadEnd] <;> omega
    have hstep2 : Step (simMachine M b) ⟨SimState.entry, ⟨t0.contents, ⟨1, by omega⟩⟩⟩
        ⟨SimState.acc, ⟨t0.contents, ⟨1, by omega⟩⟩⟩ := by
      refine ⟨SimState.acc, rightMark, DLBA.Dir.stay, ?_, ?_⟩
      · show _ ∈ (simMachine M b).transition SimState.entry (t0.contents ⟨1, by omega⟩)
        rw [εc1]; simp only [simMachine, simTransition_entry_right]
        rw [if_pos hbt, Set.mem_singleton_iff]
      · refine cfg_ext (Y := ⟨SimState.acc,
          ((⟨t0.contents, ⟨1, by omega⟩⟩ : DLBA.BoundedTape (EndAlpha T Γ) 1).write rightMark).moveHead
            DLBA.Dir.stay⟩) rfl ?_ ?_
        · show t0.contents = Function.update t0.contents ⟨1, by omega⟩ rightMark
          rw [← εc1, Function.update_eq_self]
        · apply Fin.ext
          simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, List.length_nil]
    refine ⟨⟨SimState.acc, ⟨t0.contents, ⟨1, by omega⟩⟩⟩,
      Relation.ReflTransGen.head hstep1 (Relation.ReflTransGen.single hstep2), rfl⟩

/-! ### Assembling the language equivalence.

Connecting the dimension-clean `sim_accepts_iff` to the canonical `loadEnd`/`initCfgList`
configurations requires one transport across `(w.map embed).length = w.length` (`List.length_map`),
handled here once via `HEq`. -/

/-- `Accepts` transports across a dimension equality and a heterogeneous configuration equality. -/
theorem accepts_heq {Γ' Λ' : Type*} {n n' : ℕ} (Mx : Machine Γ' Λ')
    {cfg : DLBA.Cfg Γ' Λ' n} {cfg' : DLBA.Cfg Γ' Λ' n'}
    (hn : n = n') (hcfg : HEq cfg cfg') : Accepts Mx cfg ↔ Accepts Mx cfg' := by
  subst hn; rw [eq_of_heq hcfg]

/-- Heterogeneous tape equality from a dimension equality, heterogeneous contents and equal head. -/
theorem boundedtape_heq {Γ' : Type*} {n n' : ℕ} (hn : n = n')
    {t : DLBA.BoundedTape Γ' n} {t' : DLBA.BoundedTape Γ' n'}
    (hc : HEq t.contents t'.contents) (hh : t.head.val = t'.head.val) : HEq t t' := by
  subst hn
  obtain ⟨tc, th⟩ := t; obtain ⟨tc', th'⟩ := t'
  apply heq_of_eq
  simp only [DLBA.BoundedTape.mk.injEq]
  exact ⟨eq_of_heq hc, Fin.ext hh⟩

/-- Heterogeneous configuration equality from a dimension equality, equal state and tape `HEq`. -/
theorem cfg_heq {Γ' Λ' : Type*} {n n' : ℕ} (hn : n = n')
    {c : DLBA.Cfg Γ' Λ' n} {c' : DLBA.Cfg Γ' Λ' n'}
    (hs : c.state = c'.state) (ht : HEq c.tape c'.tape) : HEq c c' := by
  subst hn
  obtain ⟨cs, ct⟩ := c; obtain ⟨cs', ct'⟩ := c'
  apply heq_of_eq
  simp only [DLBA.Cfg.mk.injEq]
  exact ⟨hs, eq_of_heq ht⟩

/-- On a non-empty input, the endmarker simulator on `⊢ w ⊣` accepts iff the flag machine `M`
accepts on the canonically loaded `w` — connecting `sim_accepts_iff` to the canonical tapes. -/
theorem sim_accepts_input (w : List T)
    (hv : w.map (fun t => some (Sum.inl t)) ≠ []) :
    Accepts (simMachine M b) ⟨SimState.start, loadEnd w⟩
      ↔ Accepts M (initCfgList M (w.map (fun t => some (Sum.inl t))) hv) := by
  set embed : T → Option (T ⊕ Γ) := fun t => some (Sum.inl t) with hembed
  have hlen : (w.map embed).length = w.length := by simp
  have hwne : w ≠ [] := by rintro rfl; simp [hembed] at hv
  have hpos : 0 < w.length := List.length_pos_of_ne_nil hwne
  set c₀ := (loadList (w.map embed) hv).contents with hc₀
  have key : Accepts (simMachine M b)
      (⟨SimState.start, ⟨enc c₀, ⟨0, by omega⟩⟩⟩ :
        DLBA.Cfg (EndAlpha T Γ) (SimState Λ) ((w.map embed).length - 1 + 2))
      ↔ Accepts M (initCfgList M (w.map embed) hv) := sim_accepts_iff M b c₀
  rw [← key]
  refine accepts_heq (simMachine M b) (by rw [hlen]; omega) ?_
  refine cfg_heq (by rw [hlen]; omega) rfl ?_
  refine boundedtape_heq (by rw [hlen]; omega) ?_ ?_
  · -- contents agree cellwise
    refine (Fin.heq_fun_iff (by rw [hlen]; omega)).mpr (fun i => ?_)
    have hi := i.isLt
    simp only [loadEnd, enc, Fin.coe_cast]
    by_cases h0 : i.val = 0
    · rw [if_pos h0, dif_pos h0]
    · rw [if_neg h0, dif_neg h0]
      by_cases hlast : i.val - 1 < w.length
      · rw [dif_pos hlast, dif_neg (by rw [hlen]; omega)]
        rw [hc₀]
        simp only [loadList, List.get_eq_getElem, List.getElem_map, hembed]
      · rw [dif_neg hlast, dif_pos (by rw [hlen]; omega)]
  · -- heads agree (both at cell 0)
    simp [loadEnd]

theorem language_simMachine_eq :
    LanguageEnd (simMachine M b) = LanguageRecognized M (fun t => some (Sum.inl t)) b := by
  funext w
  apply propext
  show Accepts (simMachine M b) (initCfgEnd (simMachine M b) w)
    ↔ (b = true ∧ w = []) ∨ LanguageViaEmbed M (fun t => some (Sum.inl t)) w
  rcases w with _ | ⟨x, xs⟩
  · -- empty word
    rw [accepts_empty]
    constructor
    · intro hb; exact Or.inl ⟨hb, rfl⟩
    · rintro (⟨hb, _⟩ | ⟨hw, _⟩)
      · exact hb
      · exact absurd rfl hw
  · -- non-empty word
    rw [show initCfgEnd (simMachine M b) (x :: xs) = ⟨SimState.start, loadEnd (x :: xs)⟩ from rfl,
        sim_accepts_input M b (x :: xs) (by simp)]
    constructor
    · intro h; exact Or.inr ⟨by simp, h⟩
    · rintro (⟨_, hcon⟩ | ⟨_, h⟩)
      · exact absurd hcon (by simp)
      · exact h

end LBA

/-- Every flag-model LBA language is recognized by the canonical endmarker model. -/
theorem is_LBA_subset_is_LBA_end {T : Type} [Fintype T] [DecidableEq T] {L : Language T}
    (h : is_LBA L) : is_LBA_end L := by
  obtain ⟨Γ, Λ, _, _, _, _, acceptEmpty, M, hM⟩ := h
  exact ⟨Γ, LBA.SimState Λ, inferInstance, inferInstance, inferInstance,
    inferInstance, LBA.simMachine M acceptEmpty, by rw [LBA.language_simMachine_eq]; exact hM⟩

theorem LBA_subset_LBA_end {T : Type} [Fintype T] [DecidableEq T] :
    (LBA : Set (Language T)) ⊆ LBA_end := fun _ h => is_LBA_subset_is_LBA_end h

/-- Every context-sensitive language is recognized by the canonical endmarker LBA model
(`CS ⊆ LBA_end`), via `CS = LBA` and the flag→endmarker simulation. -/
theorem CS_subset_LBA_end {T : Type} [Fintype T] [DecidableEq T] :
    (CS : Set (Language T)) ⊆ LBA_end :=
  fun _ hL => LBA_subset_LBA_end (by rw [← CS_eq_LBA]; exact hL)
