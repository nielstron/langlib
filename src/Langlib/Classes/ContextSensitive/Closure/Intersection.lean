module

public import Langlib.Automata.LinearBounded.Equivalence.ContextSensitive
public import Langlib.Utilities.ClosurePredicates
import Mathlib.Tactic

@[expose]
public section

/-!
# Context-Sensitive Languages Are Closed Under Intersection

We run two nondeterministic endmarker LBAs sequentially.  The product machine stores, in each
tape cell, one symbol for each source tape.  While the first machine runs it changes only the
first component.  Once it reaches an accepting state, the product machine rewinds and runs the
second machine on the still-untouched second component.

The construction is uniform in the finite input alphabet: it does not choose or require any
distinguished input letters.
-/

namespace CSIntersection

open LBA Classical

variable {T Γ₁ Γ₂ Λ₁ Λ₂ : Type*}

private abbrev PairWork (T Γ₁ Γ₂ : Type*) :=
  LBA.EndAlpha T Γ₁ × LBA.EndAlpha T Γ₂

private abbrev PairAlpha (T Γ₁ Γ₂ : Type*) :=
  LBA.EndAlpha T (PairWork T Γ₁ Γ₂)

/-- Read a product-machine cell as a cell of the first source machine.  Canonical input cells
and endmarkers are shared; an encoded work cell contains the two independent source cells. -/
private def view₁ : PairAlpha T Γ₁ Γ₂ → LBA.EndAlpha T Γ₁
  | .inl none => .inl none
  | .inl (some (.inl t)) => .inl (some (.inl t))
  | .inl (some (.inr p)) => p.1
  | .inr b => .inr b

/-- Read a product-machine cell as a cell of the second source machine. -/
private def view₂ : PairAlpha T Γ₁ Γ₂ → LBA.EndAlpha T Γ₂
  | .inl none => .inl none
  | .inl (some (.inl t)) => .inl (some (.inl t))
  | .inl (some (.inr p)) => p.2
  | .inr b => .inr b

/-- Store a pair of independently mutable source-tape cells in one product-tape cell. -/
private def pack (a₁ : LBA.EndAlpha T Γ₁) (a₂ : LBA.EndAlpha T Γ₂) :
    PairAlpha T Γ₁ Γ₂ :=
  .inl (some (.inr (a₁, a₂)))

@[simp] private lemma view₁_pack (a₁ : LBA.EndAlpha T Γ₁)
    (a₂ : LBA.EndAlpha T Γ₂) : view₁ (pack a₁ a₂) = a₁ := rfl

@[simp] private lemma view₂_pack (a₁ : LBA.EndAlpha T Γ₁)
    (a₂ : LBA.EndAlpha T Γ₂) : view₂ (pack a₁ a₂) = a₂ := rfl

private inductive InterState (Λ₁ Λ₂ : Type*) where
  | run₁ : Λ₁ → InterState Λ₁ Λ₂
  | rewind : InterState Λ₁ Λ₂
  | run₂ : Λ₂ → InterState Λ₁ Λ₂
deriving Fintype, DecidableEq

private noncomputable def interTransition
    (M₁ : LBA.Machine (LBA.EndAlpha T Γ₁) Λ₁)
    (M₂ : LBA.Machine (LBA.EndAlpha T Γ₂) Λ₂) :
    InterState Λ₁ Λ₂ → PairAlpha T Γ₁ Γ₂ →
      Set (InterState Λ₁ Λ₂ × PairAlpha T Γ₁ Γ₂ × DLBA.Dir)
  | .run₁ q, a =>
      {x | (∃ p ∈ M₁.transition q (view₁ a),
              x = (.run₁ p.1, pack p.2.1 (view₂ a), p.2.2)) ∨
            (M₁.accept q = true ∧ x = (.rewind, a, .stay))}
  | .rewind, a =>
      if view₂ a = LBA.leftMark then {(.run₂ M₂.initial, a, .stay)}
      else {(.rewind, a, .left)}
  | .run₂ q, a =>
      {x | ∃ p ∈ M₂.transition q (view₂ a),
        x = (.run₂ p.1, pack (view₁ a) p.2.1, p.2.2)}

private noncomputable def interMachine
    (M₁ : LBA.Machine (LBA.EndAlpha T Γ₁) Λ₁)
    (M₂ : LBA.Machine (LBA.EndAlpha T Γ₂) Λ₂) :
    LBA.Machine (PairAlpha T Γ₁ Γ₂) (InterState Λ₁ Λ₂) where
  transition := interTransition M₁ M₂
  accept
    | .run₂ q => M₂.accept q
    | _ => false
  initial := .run₁ M₁.initial

private def projectTape₁ {n : ℕ} (t : DLBA.BoundedTape (PairAlpha T Γ₁ Γ₂) n) :
    DLBA.BoundedTape (LBA.EndAlpha T Γ₁) n :=
  ⟨fun i => view₁ (t.contents i), t.head⟩

private def projectTape₂ {n : ℕ} (t : DLBA.BoundedTape (PairAlpha T Γ₁ Γ₂) n) :
    DLBA.BoundedTape (LBA.EndAlpha T Γ₂) n :=
  ⟨fun i => view₂ (t.contents i), t.head⟩

private def projectCfg₁ {n : ℕ} (q : Λ₁)
    (c : DLBA.Cfg (PairAlpha T Γ₁ Γ₂) (InterState Λ₁ Λ₂) n) :
    DLBA.Cfg (LBA.EndAlpha T Γ₁) Λ₁ n :=
  ⟨q, projectTape₁ c.tape⟩

private def projectCfg₂ {n : ℕ} (q : Λ₂)
    (c : DLBA.Cfg (PairAlpha T Γ₁ Γ₂) (InterState Λ₁ Λ₂) n) :
    DLBA.Cfg (LBA.EndAlpha T Γ₂) Λ₂ n :=
  ⟨q, projectTape₂ c.tape⟩

private lemma cfg_ext {A S : Type*} {n : ℕ} {x y : DLBA.Cfg A S n}
    (hs : x.state = y.state) (hc : x.tape.contents = y.tape.contents)
    (hh : x.tape.head = y.tape.head) : x = y := by
  rcases x with ⟨xs, xc, xh⟩
  rcases y with ⟨ys, yc, yh⟩
  simp_all

private lemma tape_ext {A : Type*} {n : ℕ} {x y : DLBA.BoundedTape A n}
    (hc : x.contents = y.contents) (hh : x.head = y.head) : x = y := by
  rcases x with ⟨xc, xh⟩
  rcases y with ⟨yc, yh⟩
  simp_all

private lemma projectTape₁_write_pack {n : ℕ}
    (t : DLBA.BoundedTape (PairAlpha T Γ₁ Γ₂) n)
    (a₁ : LBA.EndAlpha T Γ₁) :
    projectTape₁ (t.write (pack a₁ (view₂ t.read))) = (projectTape₁ t).write a₁ := by
  cases t with
  | mk contents head =>
      apply tape_ext
      · funext i
        simp only [projectTape₁, DLBA.BoundedTape.write, Function.update_apply,
          DLBA.BoundedTape.read]
        split <;> simp_all
      · rfl

private lemma projectTape₂_write_pack_left {n : ℕ}
    (t : DLBA.BoundedTape (PairAlpha T Γ₁ Γ₂) n)
    (a₁ : LBA.EndAlpha T Γ₁) :
    projectTape₂ (t.write (pack a₁ (view₂ t.read))) = projectTape₂ t := by
  cases t with
  | mk contents head =>
      apply tape_ext
      · funext i
        simp only [projectTape₂, DLBA.BoundedTape.write, Function.update_apply,
          DLBA.BoundedTape.read]
        split <;> simp_all
      · rfl

private lemma projectTape₂_write_pack {n : ℕ}
    (t : DLBA.BoundedTape (PairAlpha T Γ₁ Γ₂) n)
    (a₂ : LBA.EndAlpha T Γ₂) :
    projectTape₂ (t.write (pack (view₁ t.read) a₂)) = (projectTape₂ t).write a₂ := by
  cases t with
  | mk contents head =>
      apply tape_ext
      · funext i
        simp only [projectTape₂, DLBA.BoundedTape.write, Function.update_apply,
          DLBA.BoundedTape.read]
        split <;> simp_all
      · rfl

private lemma projectTape₁_write_pack_right {n : ℕ}
    (t : DLBA.BoundedTape (PairAlpha T Γ₁ Γ₂) n)
    (a₂ : LBA.EndAlpha T Γ₂) :
    projectTape₁ (t.write (pack (view₁ t.read) a₂)) = projectTape₁ t := by
  cases t with
  | mk contents head =>
      apply tape_ext
      · funext i
        simp only [projectTape₁, DLBA.BoundedTape.write, Function.update_apply,
          DLBA.BoundedTape.read]
        split <;> simp_all
      · rfl

private lemma projectTape₁_moveHead {n : ℕ}
    (t : DLBA.BoundedTape (PairAlpha T Γ₁ Γ₂) n) (d : DLBA.Dir) :
    projectTape₁ (t.moveHead d) = (projectTape₁ t).moveHead d := by
  cases t <;> (cases d <;> rfl)

private lemma projectTape₂_moveHead {n : ℕ}
    (t : DLBA.BoundedTape (PairAlpha T Γ₁ Γ₂) n) (d : DLBA.Dir) :
    projectTape₂ (t.moveHead d) = (projectTape₂ t).moveHead d := by
  cases t <;> (cases d <;> rfl)

private lemma initial_projects₁
    (M₁ : LBA.Machine (LBA.EndAlpha T Γ₁) Λ₁)
    (M₂ : LBA.Machine (LBA.EndAlpha T Γ₂) Λ₂) (w : List T) :
    projectCfg₁ M₁.initial (LBA.initCfgEnd (interMachine M₁ M₂) w) =
      LBA.initCfgEnd M₁ w := by
  apply cfg_ext
  · rfl
  · funext i
    simp only [projectCfg₁, projectTape₁, LBA.initCfgEnd, LBA.loadEnd]
    split <;> rename_i hzero
    · simp [view₁]
    · split <;> simp [view₁]
  · rfl

private lemma initial_projects₂
    (M₁ : LBA.Machine (LBA.EndAlpha T Γ₁) Λ₁)
    (M₂ : LBA.Machine (LBA.EndAlpha T Γ₂) Λ₂) (w : List T) :
    projectCfg₂ M₂.initial (LBA.initCfgEnd (interMachine M₁ M₂) w) =
      LBA.initCfgEnd M₂ w := by
  apply cfg_ext
  · rfl
  · funext i
    simp only [projectCfg₂, projectTape₂, LBA.initCfgEnd, LBA.loadEnd]
    split <;> rename_i hzero
    · simp [view₂]
    · split <;> simp [view₂]
  · rfl

private lemma write_read_same {A : Type*} {n : ℕ} (t : DLBA.BoundedTape A n) :
    t.write t.read = t := by
  apply tape_ext
  · simp only [DLBA.BoundedTape.write, DLBA.BoundedTape.read]
    exact Function.update_eq_self _ _
  · rfl

private lemma run₁_step
    (M₁ : LBA.Machine (LBA.EndAlpha T Γ₁) Λ₁)
    (M₂ : LBA.Machine (LBA.EndAlpha T Γ₂) Λ₂)
    {n : ℕ} (q : Λ₁)
    (c : DLBA.Cfg (PairAlpha T Γ₁ Γ₂) (InterState Λ₁ Λ₂) n)
    {c₁' : DLBA.Cfg (LBA.EndAlpha T Γ₁) Λ₁ n}
    (hs : c.state = .run₁ q) (h : LBA.Step M₁ (projectCfg₁ q c) c₁') :
    ∃ c', LBA.Step (interMachine M₁ M₂) c c' ∧
      c'.state = .run₁ c₁'.state ∧ projectCfg₁ c₁'.state c' = c₁' ∧
      (projectTape₂ c'.tape).contents = (projectTape₂ c.tape).contents := by
  rcases h with ⟨q', a, d, hmem, rfl⟩
  let c' : DLBA.Cfg (PairAlpha T Γ₁ Γ₂) (InterState Λ₁ Λ₂) n :=
    ⟨.run₁ q', (c.tape.write (pack a (view₂ c.tape.read))).moveHead d⟩
  refine ⟨c', ?_, rfl, ?_, ?_⟩
  · refine ⟨.run₁ q', pack a (view₂ c.tape.read), d, ?_, rfl⟩
    rw [hs]
    exact Or.inl ⟨(q', a, d), hmem, rfl⟩
  · apply cfg_ext
    · rfl
    · simp only [c', projectCfg₁, projectTape₁_moveHead, projectTape₁_write_pack]
    · simp only [c', projectCfg₁, projectTape₁_moveHead, projectTape₁_write_pack]
  · simp only [c', projectTape₂_moveHead, projectTape₂_write_pack_left]
    cases d <;> rfl

private lemma run₂_step
    (M₁ : LBA.Machine (LBA.EndAlpha T Γ₁) Λ₁)
    (M₂ : LBA.Machine (LBA.EndAlpha T Γ₂) Λ₂)
    {n : ℕ} (q : Λ₂)
    (c : DLBA.Cfg (PairAlpha T Γ₁ Γ₂) (InterState Λ₁ Λ₂) n)
    {c₂' : DLBA.Cfg (LBA.EndAlpha T Γ₂) Λ₂ n}
    (hs : c.state = .run₂ q) (h : LBA.Step M₂ (projectCfg₂ q c) c₂') :
    ∃ c', LBA.Step (interMachine M₁ M₂) c c' ∧
      c'.state = .run₂ c₂'.state ∧ projectCfg₂ c₂'.state c' = c₂' := by
  rcases h with ⟨q', a, d, hmem, rfl⟩
  let c' : DLBA.Cfg (PairAlpha T Γ₁ Γ₂) (InterState Λ₁ Λ₂) n :=
    ⟨.run₂ q', (c.tape.write (pack (view₁ c.tape.read) a)).moveHead d⟩
  refine ⟨c', ?_, rfl, ?_⟩
  · refine ⟨.run₂ q', pack (view₁ c.tape.read) a, d, ?_, rfl⟩
    rw [hs]
    exact ⟨(q', a, d), hmem, rfl⟩
  · apply cfg_ext
    · rfl
    · simp only [c', projectCfg₂, projectTape₂_moveHead, projectTape₂_write_pack]
    · simp only [c', projectCfg₂, projectTape₂_moveHead, projectTape₂_write_pack]

private lemma run₁_step_inv
    (M₁ : LBA.Machine (LBA.EndAlpha T Γ₁) Λ₁)
    (M₂ : LBA.Machine (LBA.EndAlpha T Γ₂) Λ₂)
    {n : ℕ} {q : Λ₁}
    {c c' : DLBA.Cfg (PairAlpha T Γ₁ Γ₂) (InterState Λ₁ Λ₂) n}
    (hs : c.state = .run₁ q) (h : LBA.Step (interMachine M₁ M₂) c c') :
    (∃ q', c'.state = .run₁ q' ∧
      LBA.Step M₁ (projectCfg₁ q c) (projectCfg₁ q' c') ∧
      (projectTape₂ c'.tape).contents = (projectTape₂ c.tape).contents) ∨
    (c'.state = .rewind ∧ c'.tape = c.tape ∧ M₁.accept q = true) := by
  rcases h with ⟨s', a, d, hmem, rfl⟩
  rw [hs] at hmem
  change (s', a, d) ∈ interTransition M₁ M₂ (.run₁ q) c.tape.read at hmem
  rcases hmem with hrun | hswitch
  · rcases hrun with ⟨⟨q', b, e⟩, hb, heq⟩
    simp only [Prod.mk.injEq] at heq
    rcases heq with ⟨rfl, rfl, rfl⟩
    left
    refine ⟨q', rfl, ?_, ?_⟩
    · refine ⟨q', b, d, ?_, ?_⟩
      · simpa [projectCfg₁, projectTape₁, DLBA.BoundedTape.read] using hb
      · apply cfg_ext
        · rfl
        · simp only [projectCfg₁, projectTape₁_moveHead, projectTape₁_write_pack]
        · simp only [projectCfg₁, projectTape₁_moveHead, projectTape₁_write_pack]
    · simp only [projectTape₂_moveHead, projectTape₂_write_pack_left]
      cases d <;> rfl
  · rcases hswitch with ⟨hacc, heq⟩
    simp only [Prod.mk.injEq] at heq
    rcases heq with ⟨rfl, rfl, rfl⟩
    right
    refine ⟨rfl, ?_, hacc⟩
    simp only [DLBA.BoundedTape.moveHead]
    exact write_read_same c.tape

private lemma run₂_step_inv
    (M₁ : LBA.Machine (LBA.EndAlpha T Γ₁) Λ₁)
    (M₂ : LBA.Machine (LBA.EndAlpha T Γ₂) Λ₂)
    {n : ℕ} {q : Λ₂}
    {c c' : DLBA.Cfg (PairAlpha T Γ₁ Γ₂) (InterState Λ₁ Λ₂) n}
    (hs : c.state = .run₂ q) (h : LBA.Step (interMachine M₁ M₂) c c') :
    ∃ q', c'.state = .run₂ q' ∧
      LBA.Step M₂ (projectCfg₂ q c) (projectCfg₂ q' c') := by
  rcases h with ⟨s', a, d, hmem, rfl⟩
  rw [hs] at hmem
  change (s', a, d) ∈ interTransition M₁ M₂ (.run₂ q) c.tape.read at hmem
  rcases hmem with ⟨⟨q', b, e⟩, hb, heq⟩
  simp only [Prod.mk.injEq] at heq
  rcases heq with ⟨rfl, rfl, rfl⟩
  refine ⟨q', rfl, ?_⟩
  refine ⟨q', b, d, ?_, ?_⟩
  · simpa [projectCfg₂, projectTape₂, DLBA.BoundedTape.read] using hb
  · apply cfg_ext
    · rfl
    · simp only [projectCfg₂, projectTape₂_moveHead, projectTape₂_write_pack]
    · simp only [projectCfg₂, projectTape₂_moveHead, projectTape₂_write_pack]

private lemma run₁_reaches
    (M₁ : LBA.Machine (LBA.EndAlpha T Γ₁) Λ₁)
    (M₂ : LBA.Machine (LBA.EndAlpha T Γ₂) Λ₂)
    {n : ℕ} {c₁ c₁' : DLBA.Cfg (LBA.EndAlpha T Γ₁) Λ₁ n}
    (h : LBA.Reaches M₁ c₁ c₁')
    (c : DLBA.Cfg (PairAlpha T Γ₁ Γ₂) (InterState Λ₁ Λ₂) n)
    (hs : c.state = .run₁ c₁.state) (hp : projectCfg₁ c₁.state c = c₁) :
    ∃ c', LBA.Reaches (interMachine M₁ M₂) c c' ∧
      c'.state = .run₁ c₁'.state ∧ projectCfg₁ c₁'.state c' = c₁' ∧
      (projectTape₂ c'.tape).contents = (projectTape₂ c.tape).contents := by
  induction h generalizing c with
  | refl => exact ⟨c, Relation.ReflTransGen.refl, hs, hp, rfl⟩
  | tail hxy hyz ih =>
      obtain ⟨cm, hcm, hsm, hpm, hkeep⟩ := ih c hs hp
      obtain ⟨cf, hstep, hsf, hpf, hkeep'⟩ :=
        run₁_step M₁ M₂ _ cm hsm (hpm.symm ▸ hyz)
      exact ⟨cf, hcm.tail hstep, hsf, hpf, hkeep'.trans hkeep⟩

private lemma run₂_reaches
    (M₁ : LBA.Machine (LBA.EndAlpha T Γ₁) Λ₁)
    (M₂ : LBA.Machine (LBA.EndAlpha T Γ₂) Λ₂)
    {n : ℕ} {c₂ c₂' : DLBA.Cfg (LBA.EndAlpha T Γ₂) Λ₂ n}
    (h : LBA.Reaches M₂ c₂ c₂')
    (c : DLBA.Cfg (PairAlpha T Γ₁ Γ₂) (InterState Λ₁ Λ₂) n)
    (hs : c.state = .run₂ c₂.state) (hp : projectCfg₂ c₂.state c = c₂) :
    ∃ c', LBA.Reaches (interMachine M₁ M₂) c c' ∧
      c'.state = .run₂ c₂'.state ∧ projectCfg₂ c₂'.state c' = c₂' := by
  induction h generalizing c with
  | refl => exact ⟨c, Relation.ReflTransGen.refl, hs, hp⟩
  | tail hxy hyz ih =>
      obtain ⟨cm, hcm, hsm, hpm⟩ := ih c hs hp
      obtain ⟨cf, hstep, hsf, hpf⟩ :=
        run₂_step M₁ M₂ _ cm hsm (hpm.symm ▸ hyz)
      exact ⟨cf, hcm.tail hstep, hsf, hpf⟩

private lemma loadEnd_left_iff_zero (w : List T) (i : Fin (w.length + 2)) :
    (LBA.loadEnd (T := T) (Γ := Γ₂) w).contents i = LBA.leftMark ↔ i.val = 0 := by
  simp only [LBA.loadEnd]
  split
  · simp_all
  · split <;> simp_all

private def atHead {A : Type*} {n : ℕ} (t : DLBA.BoundedTape A n) (i : Fin (n + 1)) :
    DLBA.BoundedTape A n := ⟨t.contents, i⟩

private def rewindCfg {n : ℕ}
    (t : DLBA.BoundedTape (PairAlpha T Γ₁ Γ₂) n) (i : Fin (n + 1)) :
    DLBA.Cfg (PairAlpha T Γ₁ Γ₂) (InterState Λ₁ Λ₂) n :=
  ⟨.rewind, atHead t i⟩

private lemma switch_step
    (M₁ : LBA.Machine (LBA.EndAlpha T Γ₁) Λ₁)
    (M₂ : LBA.Machine (LBA.EndAlpha T Γ₂) Λ₂)
    {n : ℕ} {q : Λ₁}
    (c : DLBA.Cfg (PairAlpha T Γ₁ Γ₂) (InterState Λ₁ Λ₂) n)
    (hs : c.state = .run₁ q) (hacc : M₁.accept q = true) :
    LBA.Step (interMachine M₁ M₂) c (rewindCfg c.tape c.tape.head) := by
  refine ⟨.rewind, c.tape.read, .stay, ?_, ?_⟩
  · rw [hs]
    exact Or.inr ⟨hacc, rfl⟩
  · apply cfg_ext
    · rfl
    · exact (congrArg DLBA.BoundedTape.contents (write_read_same c.tape)).symm
    · exact (congrArg DLBA.BoundedTape.head (write_read_same c.tape)).symm

private lemma rewind_left_step
    (M₁ : LBA.Machine (LBA.EndAlpha T Γ₁) Λ₁)
    (M₂ : LBA.Machine (LBA.EndAlpha T Γ₂) Λ₂)
    (w : List T) (t : DLBA.BoundedTape (PairAlpha T Γ₁ Γ₂) (w.length + 1))
    (hcontents : (projectTape₂ t).contents =
      (LBA.loadEnd (T := T) (Γ := Γ₂) w).contents)
    (i : ℕ) (hi : i + 1 < w.length + 2) :
    LBA.Step (interMachine M₁ M₂)
      (rewindCfg t ⟨i + 1, hi⟩) (rewindCfg t ⟨i, by omega⟩) := by
  let p : Fin (w.length + 2) := ⟨i + 1, hi⟩
  have hnot : view₂ (t.contents p) ≠ LBA.leftMark := by
    have hcell := congrFun hcontents p
    change view₂ (t.contents p) =
      (LBA.loadEnd (T := T) (Γ := Γ₂) w).contents p at hcell
    intro hbad
    have hload : (LBA.loadEnd (T := T) (Γ := Γ₂) w).contents p = LBA.leftMark := by
      rw [← hcell, hbad]
    have := (loadEnd_left_iff_zero (T := T) (Γ₂ := Γ₂) w p).mp hload
    change i + 1 = 0 at this
    omega
  refine ⟨.rewind, t.contents p, .left, ?_, ?_⟩
  · change _ ∈ interTransition M₁ M₂ .rewind (t.contents p)
    simp [interTransition, hnot]
  · apply cfg_ext
    · rfl
    · simp only [rewindCfg, atHead, DLBA.BoundedTape.write,
        DLBA.BoundedTape.moveHead]
      exact (Function.update_eq_self _ _).symm
    · apply Fin.ext
      simp [rewindCfg, atHead, DLBA.BoundedTape.write,
        DLBA.BoundedTape.moveHead, p]

private lemma rewind_reaches_zero
    (M₁ : LBA.Machine (LBA.EndAlpha T Γ₁) Λ₁)
    (M₂ : LBA.Machine (LBA.EndAlpha T Γ₂) Λ₂)
    (w : List T) (t : DLBA.BoundedTape (PairAlpha T Γ₁ Γ₂) (w.length + 1))
    (hcontents : (projectTape₂ t).contents =
      (LBA.loadEnd (T := T) (Γ := Γ₂) w).contents)
    (i : ℕ) (hi : i < w.length + 2) :
    LBA.Reaches (interMachine M₁ M₂)
      (rewindCfg t ⟨i, hi⟩) (rewindCfg t ⟨0, by omega⟩) := by
  induction i with
  | zero => exact Relation.ReflTransGen.refl
  | succ i ih =>
      exact Relation.ReflTransGen.head
        (rewind_left_step M₁ M₂ w t hcontents i hi) (ih (by omega))

private lemma rewind_zero_step
    (M₁ : LBA.Machine (LBA.EndAlpha T Γ₁) Λ₁)
    (M₂ : LBA.Machine (LBA.EndAlpha T Γ₂) Λ₂)
    (w : List T) (t : DLBA.BoundedTape (PairAlpha T Γ₁ Γ₂) (w.length + 1))
    (hcontents : (projectTape₂ t).contents =
      (LBA.loadEnd (T := T) (Γ := Γ₂) w).contents) :
    LBA.Step (interMachine M₁ M₂) (rewindCfg t ⟨0, by omega⟩)
      ⟨.run₂ M₂.initial, atHead t ⟨0, by omega⟩⟩ := by
  have hleft : view₂ (t.contents ⟨0, by omega⟩) = LBA.leftMark := by
    have hcell := congrFun hcontents ⟨0, by omega⟩
    change view₂ (t.contents ⟨0, by omega⟩) =
      (LBA.loadEnd (T := T) (Γ := Γ₂) w).contents ⟨0, by omega⟩ at hcell
    simpa [loadEnd_left_iff_zero] using hcell
  refine ⟨.run₂ M₂.initial, t.contents ⟨0, by omega⟩, .stay, ?_, ?_⟩
  · change _ ∈ interTransition M₁ M₂ .rewind (t.contents ⟨0, by omega⟩)
    simp only [interTransition]
    rw [if_pos hleft]
    simp
  · apply cfg_ext
    · rfl
    · simp only [rewindCfg, atHead, DLBA.BoundedTape.write,
        DLBA.BoundedTape.moveHead]
      exact (Function.update_eq_self _ _).symm
    · rfl

private lemma after_rewind_projects₂
    (M₂ : LBA.Machine (LBA.EndAlpha T Γ₂) Λ₂)
    (w : List T) (t : DLBA.BoundedTape (PairAlpha T Γ₁ Γ₂) (w.length + 1))
    (hcontents : (projectTape₂ t).contents =
      (LBA.loadEnd (T := T) (Γ := Γ₂) w).contents) :
    projectCfg₂ M₂.initial
      (⟨.run₂ M₂.initial, atHead t ⟨0, by omega⟩⟩ :
        DLBA.Cfg (PairAlpha T Γ₁ Γ₂) (InterState Λ₁ Λ₂) (w.length + 1)) =
      LBA.initCfgEnd M₂ w := by
  apply cfg_ext
  · rfl
  · exact hcontents
  · rfl

private def InterInv
    (M₁ : LBA.Machine (LBA.EndAlpha T Γ₁) Λ₁)
    (M₂ : LBA.Machine (LBA.EndAlpha T Γ₂) Λ₂) (w : List T)
    (c : DLBA.Cfg (PairAlpha T Γ₁ Γ₂) (InterState Λ₁ Λ₂) (w.length + 1)) : Prop :=
  (∃ c₁, LBA.Reaches M₁ (LBA.initCfgEnd M₁ w) c₁ ∧
      c.state = .run₁ c₁.state ∧ projectCfg₁ c₁.state c = c₁ ∧
      (projectTape₂ c.tape).contents =
        (LBA.loadEnd (T := T) (Γ := Γ₂) w).contents) ∨
  (LBA.Accepts M₁ (LBA.initCfgEnd M₁ w) ∧ c.state = .rewind ∧
      (projectTape₂ c.tape).contents =
        (LBA.loadEnd (T := T) (Γ := Γ₂) w).contents) ∨
  (LBA.Accepts M₁ (LBA.initCfgEnd M₁ w) ∧
    ∃ c₂, LBA.Reaches M₂ (LBA.initCfgEnd M₂ w) c₂ ∧
      c.state = .run₂ c₂.state ∧ projectCfg₂ c₂.state c = c₂)

private lemma interInv_initial
    (M₁ : LBA.Machine (LBA.EndAlpha T Γ₁) Λ₁)
    (M₂ : LBA.Machine (LBA.EndAlpha T Γ₂) Λ₂) (w : List T) :
    InterInv M₁ M₂ w (LBA.initCfgEnd (interMachine M₁ M₂) w) := by
  left
  refine ⟨LBA.initCfgEnd M₁ w, Relation.ReflTransGen.refl, rfl,
    initial_projects₁ M₁ M₂ w, ?_⟩
  have h := congrArg (fun c => c.tape.contents) (initial_projects₂ M₁ M₂ w)
  exact h

private lemma interInv_step
    (M₁ : LBA.Machine (LBA.EndAlpha T Γ₁) Λ₁)
    (M₂ : LBA.Machine (LBA.EndAlpha T Γ₂) Λ₂) (w : List T)
    {c c' : DLBA.Cfg (PairAlpha T Γ₁ Γ₂) (InterState Λ₁ Λ₂) (w.length + 1)}
    (hinv : InterInv M₁ M₂ w c) (hstep : LBA.Step (interMachine M₁ M₂) c c') :
    InterInv M₁ M₂ w c' := by
  rcases hinv with hrun₁ | hrewind | hrun₂
  · rcases hrun₁ with ⟨c₁, hreach₁, hs, hp, hcontents⟩
    rcases run₁_step_inv M₁ M₂ hs hstep with hnext | hswitch
    · rcases hnext with ⟨q', hs', hsource, hkeep⟩
      left
      refine ⟨projectCfg₁ q' c', hreach₁.tail (hp.symm ▸ hsource), hs', rfl, ?_⟩
      exact hkeep.trans hcontents
    · rcases hswitch with ⟨hs', htape, hacc⟩
      right; left
      refine ⟨⟨c₁, hreach₁, hacc⟩, hs', ?_⟩
      rw [htape]
      exact hcontents
  · rcases hrewind with ⟨hacc₁, hs, hcontents⟩
    rcases hstep with ⟨s', a, d, hmem, rfl⟩
    rw [hs] at hmem
    change (s', a, d) ∈ interTransition M₁ M₂ .rewind c.tape.read at hmem
    by_cases hleft : view₂ c.tape.read = LBA.leftMark
    · simp only [interTransition, if_pos hleft, Set.mem_singleton_iff] at hmem
      rcases hmem with ⟨rfl, rfl, rfl⟩
      right; right
      refine ⟨hacc₁, LBA.initCfgEnd M₂ w, Relation.ReflTransGen.refl, rfl, ?_⟩
      have hhead : c.tape.head.val = 0 := by
        have hcell := congrFun hcontents c.tape.head
        change view₂ (c.tape.contents c.tape.head) =
          (LBA.loadEnd (T := T) (Γ := Γ₂) w).contents c.tape.head at hcell
        have hload : (LBA.loadEnd (T := T) (Γ := Γ₂) w).contents c.tape.head =
            LBA.leftMark := by rw [← hcell]; exact hleft
        exact (loadEnd_left_iff_zero (T := T) (Γ₂ := Γ₂) w c.tape.head).mp hload
      apply cfg_ext
      · rfl
      · change (projectTape₂ ((c.tape.write c.tape.read).moveHead .stay)).contents = _
        rw [show (c.tape.write c.tape.read).moveHead .stay = c.tape by
          simpa only [DLBA.BoundedTape.moveHead] using write_read_same c.tape]
        exact hcontents
      · apply Fin.ext
        change ((c.tape.write c.tape.read).moveHead .stay).head.val = 0
        simpa only [DLBA.BoundedTape.moveHead] using hhead
    · simp only [interTransition, if_neg hleft, Set.mem_singleton_iff] at hmem
      rcases hmem with ⟨rfl, rfl, rfl⟩
      right; left
      refine ⟨hacc₁, rfl, ?_⟩
      simp only [projectTape₂_moveHead]
      have hwrite : projectTape₂ (c.tape.write c.tape.read) = projectTape₂ c.tape := by
        rw [write_read_same]
      rw [hwrite]
      cases DLBA.Dir.left <;> exact hcontents
  · rcases hrun₂ with ⟨hacc₁, c₂, hreach₂, hs, hp⟩
    obtain ⟨q', hs', hsource⟩ := run₂_step_inv M₁ M₂ hs hstep
    right; right
    exact ⟨hacc₁, projectCfg₂ q' c', hreach₂.tail (hp.symm ▸ hsource), hs', rfl⟩

private lemma interInv_reaches
    (M₁ : LBA.Machine (LBA.EndAlpha T Γ₁) Λ₁)
    (M₂ : LBA.Machine (LBA.EndAlpha T Γ₂) Λ₂) (w : List T)
    {c : DLBA.Cfg (PairAlpha T Γ₁ Γ₂) (InterState Λ₁ Λ₂) (w.length + 1)}
    (h : LBA.Reaches (interMachine M₁ M₂)
      (LBA.initCfgEnd (interMachine M₁ M₂) w) c) : InterInv M₁ M₂ w c := by
  induction h with
  | refl => exact interInv_initial M₁ M₂ w
  | tail _ hstep ih => exact interInv_step M₁ M₂ w ih hstep

private theorem inter_accepts_iff
    (M₁ : LBA.Machine (LBA.EndAlpha T Γ₁) Λ₁)
    (M₂ : LBA.Machine (LBA.EndAlpha T Γ₂) Λ₂) (w : List T) :
    LBA.Accepts (interMachine M₁ M₂) (LBA.initCfgEnd (interMachine M₁ M₂) w) ↔
      LBA.Accepts M₁ (LBA.initCfgEnd M₁ w) ∧
        LBA.Accepts M₂ (LBA.initCfgEnd M₂ w) := by
  constructor
  · rintro ⟨c, hreach, hacc⟩
    rcases interInv_reaches M₁ M₂ w hreach with hrun₁ | hrewind | hrun₂
    · rcases hrun₁ with ⟨c₁, _, hs, _⟩
      rw [hs] at hacc
      simp [interMachine] at hacc
    · rcases hrewind with ⟨_, hs, _⟩
      rw [hs] at hacc
      simp [interMachine] at hacc
    · rcases hrun₂ with ⟨hacc₁, c₂, hreach₂, hs, _hp⟩
      rw [hs] at hacc
      exact ⟨hacc₁, ⟨c₂, hreach₂, hacc⟩⟩
  · rintro ⟨⟨c₁, hreach₁, hacc₁⟩, ⟨c₂, hreach₂, hacc₂⟩⟩
    let c₀ := LBA.initCfgEnd (interMachine M₁ M₂) w
    obtain ⟨c₁', hrun₁, hs₁', hp₁', hkeep⟩ :=
      run₁_reaches M₁ M₂ hreach₁ c₀ rfl (initial_projects₁ M₁ M₂ w)
    have hinit₂ : (projectTape₂ c₀.tape).contents =
        (LBA.loadEnd (T := T) (Γ := Γ₂) w).contents := by
      exact congrArg (fun c => c.tape.contents) (initial_projects₂ M₁ M₂ w)
    have hcontents : (projectTape₂ c₁'.tape).contents =
        (LBA.loadEnd (T := T) (Γ := Γ₂) w).contents := hkeep.trans hinit₂
    have hswitch := switch_step M₁ M₂ c₁' hs₁' hacc₁
    have hrewind := rewind_reaches_zero M₁ M₂ w c₁'.tape hcontents
      c₁'.tape.head.val c₁'.tape.head.isLt
    let cstart₂ : DLBA.Cfg (PairAlpha T Γ₁ Γ₂) (InterState Λ₁ Λ₂)
        (w.length + 1) := ⟨.run₂ M₂.initial, atHead c₁'.tape ⟨0, by omega⟩⟩
    have hstart₂ : LBA.Step (interMachine M₁ M₂)
        (rewindCfg c₁'.tape ⟨0, by omega⟩) cstart₂ :=
      rewind_zero_step M₁ M₂ w c₁'.tape hcontents
    have hpstart₂ : projectCfg₂ M₂.initial cstart₂ = LBA.initCfgEnd M₂ w :=
      after_rewind_projects₂ M₂ w c₁'.tape hcontents
    obtain ⟨c₂', hrun₂, hs₂', hp₂'⟩ :=
      run₂_reaches M₁ M₂ hreach₂ cstart₂ rfl hpstart₂
    refine ⟨c₂', ?_, ?_⟩
    · exact hrun₁.trans ((Relation.ReflTransGen.single hswitch).trans
        (hrewind.trans ((Relation.ReflTransGen.single hstart₂).trans hrun₂)))
    · rw [hs₂']
      exact hacc₂

private theorem interMachine_language
    (M₁ : LBA.Machine (LBA.EndAlpha T Γ₁) Λ₁)
    (M₂ : LBA.Machine (LBA.EndAlpha T Γ₂) Λ₂) :
    LBA.LanguageEnd (interMachine M₁ M₂) =
      LBA.LanguageEnd M₁ ⊓ LBA.LanguageEnd M₂ := by
  ext w
  exact inter_accepts_iff M₁ M₂ w

end CSIntersection

open CSIntersection

variable {T : Type} [Fintype T] [DecidableEq T]

/-- Context-sensitive languages are closed under intersection over every finite terminal
alphabet.  In particular, the theorem has no lower-bound or distinguished-letter hypothesis on
the alphabet. -/
public theorem CS_closedUnderIntersection : ClosedUnderIntersection (α := T) is_CS := by
  intro L₁ L₂ hL₁ hL₂
  classical
  obtain ⟨Γ₁, Λ₁, hΓ₁, hΛ₁, hdΓ₁, hdΛ₁, M₁, hM₁⟩ := CS_subset_LBA hL₁
  obtain ⟨Γ₂, Λ₂, hΓ₂, hΛ₂, hdΓ₂, hdΛ₂, M₂, hM₂⟩ := CS_subset_LBA hL₂
  letI : Fintype Γ₁ := hΓ₁
  letI : Fintype Λ₁ := hΛ₁
  letI : DecidableEq Γ₁ := hdΓ₁
  letI : DecidableEq Λ₁ := hdΛ₁
  letI : Fintype Γ₂ := hΓ₂
  letI : Fintype Λ₂ := hΛ₂
  letI : DecidableEq Γ₂ := hdΓ₂
  letI : DecidableEq Λ₂ := hdΛ₂
  have hinter : is_LBA (L₁ ⊓ L₂) := by
    refine ⟨PairWork T Γ₁ Γ₂, InterState Λ₁ Λ₂,
      inferInstance, inferInstance, inferInstance, inferInstance, interMachine M₁ M₂, ?_⟩
    rw [interMachine_language, hM₁, hM₂]
  exact LBA_subset_CS hinter

end
