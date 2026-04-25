import Mathlib
import Langlib.Automata.Turing.DSL.TM0Compose

/-! # TM0 Building Blocks

This file provides TM0 machines for basic operations on blank-free lists.
These are used as building blocks for the tape converter in `TapeConvert.lean`.

## Main results

- `TM0BB.tm0_map_blankfree` — a TM0 that applies a function to each cell of a
  blank-free list, producing `Tape.mk₁ (l.map f)` as the output tape.
-/

open Turing

namespace TM0BB

/-! ### States for the map machine -/

inductive MState where
  | start
  | readNext
  | advance
  | rewind
  | done
  deriving DecidableEq, Repr

instance : Inhabited MState := ⟨MState.start⟩

instance : Fintype MState where
  elems := {MState.start, MState.readNext, MState.advance, MState.rewind, MState.done}
  complete := by intro x; cases x <;> simp

/-! ### Machine Definition -/

noncomputable def mapM {Γ : Type} [Inhabited Γ] [DecidableEq Γ]
    (f : Γ → Γ) : @TM0.Machine Γ MState ⟨MState.start⟩ :=
  fun q a =>
    match q with
    | MState.start =>
      if a = default then none
      else some (MState.advance, TM0.Stmt.write (f a))
    | MState.readNext =>
      if a = default then some (MState.rewind, TM0.Stmt.move Dir.left)
      else some (MState.advance, TM0.Stmt.write (f a))
    | MState.advance => some (MState.readNext, TM0.Stmt.move Dir.right)
    | MState.rewind =>
      if a = default then some (MState.done, TM0.Stmt.move Dir.right)
      else some (MState.rewind, TM0.Stmt.move Dir.left)
    | MState.done => none

/-! ### Step lemmas -/

@[simp] theorem mapM_start_nondefault {Γ : Type} [Inhabited Γ] [DecidableEq Γ]
    (f : Γ → Γ) (a : Γ) (ha : a ≠ default) :
    mapM f MState.start a = some (MState.advance, TM0.Stmt.write (f a)) := by
  simp [mapM, ha]

@[simp] theorem mapM_start_default {Γ : Type} [Inhabited Γ] [DecidableEq Γ]
    (f : Γ → Γ) : mapM f MState.start (default : Γ) = none := by
  simp [mapM]

@[simp] theorem mapM_readNext_nondefault {Γ : Type} [Inhabited Γ] [DecidableEq Γ]
    (f : Γ → Γ) (a : Γ) (ha : a ≠ default) :
    mapM f MState.readNext a = some (MState.advance, TM0.Stmt.write (f a)) := by
  simp [mapM, ha]

@[simp] theorem mapM_readNext_default {Γ : Type} [Inhabited Γ] [DecidableEq Γ]
    (f : Γ → Γ) : mapM f MState.readNext (default : Γ) =
      some (MState.rewind, TM0.Stmt.move Dir.left) := by
  simp [mapM]

@[simp] theorem mapM_advance {Γ : Type} [Inhabited Γ] [DecidableEq Γ]
    (f : Γ → Γ) (a : Γ) :
    mapM f MState.advance a = some (MState.readNext, TM0.Stmt.move Dir.right) := by
  simp [mapM]

@[simp] theorem mapM_rewind_nondefault {Γ : Type} [Inhabited Γ] [DecidableEq Γ]
    (f : Γ → Γ) (a : Γ) (ha : a ≠ default) :
    mapM f MState.rewind a = some (MState.rewind, TM0.Stmt.move Dir.left) := by
  simp [mapM, ha]

@[simp] theorem mapM_rewind_default {Γ : Type} [Inhabited Γ] [DecidableEq Γ]
    (f : Γ → Γ) : mapM f MState.rewind (default : Γ) =
      some (MState.done, TM0.Stmt.move Dir.right) := by
  simp [mapM]

@[simp] theorem mapM_done {Γ : Type} [Inhabited Γ] [DecidableEq Γ]
    (f : Γ → Γ) (a : Γ) : mapM f MState.done a = none := by
  simp [mapM]

/-! ### Forward phase helper -/

/-
Two-step forward processing of one element from `readNext` state:
write f(a), then move right.
-/
theorem readNext_process_one {Γ : Type} [Inhabited Γ] [DecidableEq Γ]
    (f : Γ → Γ) (a : Γ) (ha : a ≠ default) (L R : ListBlank Γ) :
    Reaches (TM0.step (mapM f))
      ⟨MState.readNext, ⟨a, L, R⟩⟩
      ⟨MState.readNext, ⟨R.head, L.cons (f a), R.tail⟩⟩ := by
  -- Apply the `step` relation twice to show the two-step transition.
  have h_step : TM0.step (mapM f) ⟨MState.readNext, ⟨a, L, R⟩⟩ = some ⟨MState.advance, ⟨f a, L, R⟩⟩ ∧ TM0.step (mapM f) ⟨MState.advance, ⟨f a, L, R⟩⟩ = some ⟨MState.readNext, ⟨R.head, ListBlank.cons (f a) L, R.tail⟩⟩ := by
    simp +decide [ TM0.step, mapM ];
    exact ⟨ ⟨ _, if_neg ha, rfl ⟩, rfl ⟩;
  -- Apply the step relation twice to show the two-step transition.
  apply Relation.ReflTransGen.tail;
  exact .single ( by tauto );
  aesop

/-
The forward phase on a non-empty blank-free list.
-/
theorem forward_phase_cons {Γ : Type} [Inhabited Γ] [DecidableEq Γ]
    (f : Γ → Γ) (a : Γ) (rest : List Γ)
    (ha : a ≠ default) (hrest : ∀ x ∈ rest, x ≠ default) :
    Reaches (TM0.step (mapM f)) (TM0.init (a :: rest))
      ⟨MState.readNext,
       Tape.mk' (ListBlank.mk ((a :: rest).map f).reverse) (ListBlank.mk [])⟩ := by
  unfold Reaches at *; simp_all +decide [ List.repr ] ;
  -- Apply the `readNext_process_one` lemma repeatedly to process each element in `rest`.
  have h_process_rest : ∀ (rest : List Γ), (∀ x ∈ rest, x ≠ default) → ∀ (l : List Γ), Relation.ReflTransGen (fun a b => TM0.step (mapM f) a = some b) ⟨MState.readNext, ⟨rest.headI, ListBlank.mk l, ListBlank.mk rest.tail⟩⟩ ⟨MState.readNext, ⟨List.headI [], ListBlank.mk (List.reverse (List.map f rest) ++ l), ListBlank.mk []⟩⟩ := by
    intro rest hrest l; induction' rest with x rest ih generalizing l <;> simp_all +decide [ List.map ] ;
    · rfl;
    · have := readNext_process_one f x hrest.1 ( ListBlank.mk l ) ( ListBlank.mk rest ) ; simp_all +decide [ ListBlank.mk ] ;
      convert this.trans ( ih _ ) using 1;
  convert Relation.ReflTransGen.trans _ ( h_process_rest rest hrest [ f a ] ) using 1;
  convert Relation.ReflTransGen.head _ _ using 1;
  exact ⟨ MState.advance, ⟨ f a, ListBlank.mk [], ListBlank.mk rest ⟩ ⟩;
  · simp +decide [ TM0.step, TM0.init, mapM ];
    exact ⟨ ha, rfl ⟩;
  · convert Relation.ReflTransGen.single _ using 1;
    cases rest <;> aesop

/-! ### ListBlank helpers -/

@[simp] theorem listBlank_cons_default_nil {Γ : Type} [Inhabited Γ] :
    (ListBlank.mk ([] : List Γ)).cons default = ListBlank.mk [] := by
  -- By definition of `ListBlank.mk`, we know that `ListBlank.mk [] = ListBlank.cons default []`.
  apply Quot.sound;
  exact Or.inr ⟨ 1, by simp +decide ⟩

theorem tape_mk'_eq_mk₁ {Γ : Type} [Inhabited Γ] (l : List Γ) :
    Tape.mk' (ListBlank.mk ([] : List Γ)) (ListBlank.mk l) = Tape.mk₁ l := by
  simp [Tape.mk₁, Tape.mk₂]

/-! ### Rewind phase -/

/-
Core rewind loop with accumulator: from `rewind` state, moves left
through a blank-free list, pushing each element onto the right accumulator.

Induction on L: each non-default element moves from left to right.
-/
theorem rewind_loop {Γ : Type} [Inhabited Γ] [DecidableEq Γ]
    (f : Γ → Γ) (L : List Γ) (hL : ∀ x ∈ L, x ≠ default) (acc : List Γ) :
    Reaches (TM0.step (mapM f))
      ⟨MState.rewind, ⟨L.headI, ListBlank.mk L.tail, ListBlank.mk acc⟩⟩
      ⟨MState.rewind, ⟨default, ListBlank.mk [], ListBlank.mk (L.reverse ++ acc)⟩⟩ := by
  induction' L with a L ih generalizing acc;
  · constructor;
  · simp +zetaDelta at *;
    convert Relation.ReflTransGen.head _ ( ih hL.2 ( a :: acc ) ) using 1;
    unfold TM0.step;
    unfold mapM; aesop;

/-
The rewind phase: from readNext with default head, rewinds through
a blank-free list on the left side, ending at done with the correct tape.
-/
theorem rewind_phase {Γ : Type} [Inhabited Γ] [DecidableEq Γ]
    (f : Γ → Γ) (rev_list : List Γ) (hm : ∀ x ∈ rev_list, x ≠ default) :
    Reaches (TM0.step (mapM f))
      ⟨MState.readNext,
       Tape.mk' (ListBlank.mk rev_list) (ListBlank.mk [])⟩
      ⟨MState.done, Tape.mk₁ rev_list.reverse⟩ := by
  have phase3 : TM0.step (mapM f) ⟨MState.rewind, ⟨default, ListBlank.mk [], ListBlank.mk rev_list.reverse⟩⟩ = some ⟨MState.done, Tape.mk' (ListBlank.mk []) (ListBlank.mk rev_list.reverse)⟩ := by
    unfold TM0.step;
    simp +decide [ Tape.mk', Tape.move ];
    ext i; simp [ListBlank.mk];
    cases i <;> simp +decide [ ListBlank.nth ];
  have phase1 : TM0.step (mapM f) ⟨MState.readNext, ⟨default, ListBlank.mk rev_list, ListBlank.mk []⟩⟩ = some ⟨MState.rewind, ⟨rev_list.headI, ListBlank.mk rev_list.tail, ListBlank.mk []⟩⟩ := by
    simp +decide [ TM0.step ];
    unfold Tape.move; simp +decide [ ListBlank.mk ] ;
    exact ⟨ rfl, rfl, listBlank_cons_default_nil ⟩;
  have phase2 : Reaches (TM0.step (mapM f)) ⟨MState.rewind, ⟨rev_list.headI, ListBlank.mk rev_list.tail, ListBlank.mk []⟩⟩ ⟨MState.rewind, ⟨default, ListBlank.mk [], ListBlank.mk rev_list.reverse⟩⟩ := by
    convert rewind_loop f rev_list hm [] using 1;
    simp +decide [ ListBlank.mk ];
  exact Relation.ReflTransGen.trans ( Relation.ReflTransGen.single phase1 ) ( phase2.trans ( Relation.ReflTransGen.single phase3 ) )

/-! ### Main theorem -/

theorem tm0_map_blankfree {Γ : Type} [Inhabited Γ] [DecidableEq Γ] [Fintype Γ]
    (f : Γ → Γ) (_hf : f default = default)
    (hf_noblank : ∀ a, a ≠ default → f a ≠ default) :
    ∃ (Λ : Type) (_ : Inhabited Λ) (_ : Fintype Λ)
      (M : TM0.Machine Γ Λ),
      ∀ l : List Γ, (∀ x ∈ l, x ≠ default) →
        (TM0Seq.evalCfg M l).Dom ∧
        ∀ (h : (TM0Seq.evalCfg M l).Dom),
          ((TM0Seq.evalCfg M l).get h).Tape = Tape.mk₁ (l.map f) := by
  refine ⟨MState, inferInstance, inferInstance, mapM f, fun l hl => ?_⟩
  -- Helper: the machine reaches a config with the correct tape and halts there
  suffices hreach : ∃ cfg : TM0.Cfg Γ MState,
      cfg.Tape = Tape.mk₁ (l.map f) ∧
      cfg ∈ eval (TM0.step (mapM f)) (TM0.init l) by
    obtain ⟨cfg, htape, hmem⟩ := hreach
    exact ⟨Part.dom_iff_mem.mpr ⟨_, hmem⟩,
      fun h => by rw [(Part.mem_unique (Part.get_mem h) hmem)]; exact htape⟩
  cases l with
  | nil =>
    -- Empty list: machine halts immediately at start state
    refine ⟨⟨MState.start, Tape.mk₁ []⟩, rfl, mem_eval.mpr ⟨Relation.ReflTransGen.refl, ?_⟩⟩
    simp [TM0.step, mapM, Tape.mk₁, Tape.mk₂, Tape.mk']
  | cons a rest =>
    have ha : a ≠ default := hl a (List.mem_cons_self ..)
    have hrest : ∀ x ∈ rest, x ≠ default := fun x hx => hl x (List.mem_cons_of_mem a hx)
    have hmap_bf : ∀ x ∈ ((a :: rest).map f).reverse, x ≠ default := by
      simp only [List.mem_reverse, List.mem_map]
      rintro _ ⟨y, hy, rfl⟩; exact hf_noblank y (hl y hy)
    have hfwd := forward_phase_cons f a rest ha hrest
    have hrwd := rewind_phase f ((a :: rest).map f).reverse hmap_bf
    rw [List.reverse_reverse] at hrwd
    exact ⟨⟨MState.done, Tape.mk₁ ((a :: rest).map f)⟩, rfl,
      mem_eval.mpr ⟨hfwd.trans hrwd, by simp [TM0.step, mapM]⟩⟩

end TM0BB