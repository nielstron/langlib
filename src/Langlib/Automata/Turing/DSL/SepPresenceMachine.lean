import Mathlib
import Langlib.Automata.Turing.DSL.SplitAtSep
import Langlib.Automata.Turing.DSL.TM0Compose

/-! # Separator Presence Scanner

This file provides a small tape-preserving scanner that decides whether the
default-delimited active block contains `chainConsBottom`.
-/

open Turing PartrecToTM2 TM2to1

inductive SepPresenceSt where
  | scan
  | rewind (found : Bool)
  | done (found : Bool)
  deriving DecidableEq, Fintype

instance : Inhabited SepPresenceSt := ⟨.scan⟩

noncomputable def sepPresenceMachine : TM0.Machine ChainΓ SepPresenceSt :=
  fun q a =>
    match q with
    | .scan =>
      if a = (default : ChainΓ) then
        some (.rewind false, TM0.Stmt.move Dir.left)
      else if a = chainConsBottom then
        some (.rewind true, TM0.Stmt.move Dir.left)
      else
        some (.scan, TM0.Stmt.move Dir.right)
    | .rewind found =>
      if a = (default : ChainΓ) then
        some (.done found, TM0.Stmt.move Dir.right)
      else
        some (.rewind found, TM0.Stmt.move Dir.left)
    | .done _ => none

theorem sepPresence_scan_nonstop (a : ChainΓ)
    (ha_default : a ≠ (default : ChainΓ)) (ha_sep : a ≠ chainConsBottom)
    (L R : ListBlank ChainΓ) :
    TM0.step sepPresenceMachine ⟨SepPresenceSt.scan, ⟨a, L, R⟩⟩ =
      some ⟨SepPresenceSt.scan, Tape.move Dir.right ⟨a, L, R⟩⟩ := by
  simp [TM0.step, sepPresenceMachine, ha_default, ha_sep]

theorem sepPresence_scan_default (L R : ListBlank ChainΓ) :
    TM0.step sepPresenceMachine ⟨SepPresenceSt.scan, ⟨default, L, R⟩⟩ =
      some ⟨SepPresenceSt.rewind false, Tape.move Dir.left ⟨default, L, R⟩⟩ := by
  simp [TM0.step, sepPresenceMachine]

theorem sepPresence_scan_sep (L R : ListBlank ChainΓ) :
    TM0.step sepPresenceMachine ⟨SepPresenceSt.scan, ⟨chainConsBottom, L, R⟩⟩ =
      some ⟨SepPresenceSt.rewind true, Tape.move Dir.left ⟨chainConsBottom, L, R⟩⟩ := by
  simp [TM0.step, sepPresenceMachine, chainConsBottom_ne_default]

theorem sepPresence_rewind_nondefault (found : Bool) (a : ChainΓ)
    (ha : a ≠ (default : ChainΓ)) (L R : ListBlank ChainΓ) :
    TM0.step sepPresenceMachine ⟨SepPresenceSt.rewind found, ⟨a, L, R⟩⟩ =
      some ⟨SepPresenceSt.rewind found, Tape.move Dir.left ⟨a, L, R⟩⟩ := by
  simp [TM0.step, sepPresenceMachine, ha]

theorem sepPresence_rewind_default (found : Bool) (L R : ListBlank ChainΓ) :
    TM0.step sepPresenceMachine ⟨SepPresenceSt.rewind found, ⟨default, L, R⟩⟩ =
      some ⟨SepPresenceSt.done found, Tape.move Dir.right ⟨default, L, R⟩⟩ := by
  simp [TM0.step, sepPresenceMachine]

theorem sepPresence_done_halt (found : Bool) (T : Tape ChainΓ) :
    TM0.step sepPresenceMachine ⟨SepPresenceSt.done found, T⟩ = none := by
  simp [TM0.step, sepPresenceMachine]

theorem listBlank_mk_singleton_default_chainΓ :
    ListBlank.mk ([default] : List ChainΓ) = ListBlank.mk [] := by
  apply Quot.sound
  exact Or.inr ⟨1, by simp⟩

theorem listBlank_mk_headI_tail_chainΓ (R : List ChainΓ) :
    ListBlank.mk (R.headI :: R.tail) = ListBlank.mk R := by
  apply ListBlank.ext
  intro i
  simp only [ListBlank.nth_mk]
  cases R with
  | nil => cases i <;> simp [List.getI, List.getD, List.headI]
  | cons _ _ => rfl

theorem tape_mk₂_nil_eq_headI_tail_chainΓ (R : List ChainΓ) :
    ({ head := R.headI, left := ListBlank.mk [], right := ListBlank.mk R.tail } : Tape ChainΓ) =
      Tape.mk₂ [] R := by
  cases R <;> simp [Tape.mk₂, Tape.mk', List.headI]

theorem sepPresence_scan_gen (remaining processed_rev tail : List ChainΓ)
    (hremaining_default : ∀ x ∈ remaining, x ≠ (default : ChainΓ))
    (hremaining_sep : ∀ x ∈ remaining, x ≠ chainConsBottom) :
    Reaches (TM0.step sepPresenceMachine)
      ⟨SepPresenceSt.scan,
        Tape.mk' (ListBlank.mk processed_rev) (ListBlank.mk (remaining ++ tail))⟩
      ⟨SepPresenceSt.scan,
        Tape.mk' (ListBlank.mk (remaining.reverse ++ processed_rev)) (ListBlank.mk tail)⟩ := by
  induction remaining generalizing processed_rev with
  | nil => exact Relation.ReflTransGen.refl
  | cons a remaining ih =>
      have ha_default : a ≠ (default : ChainΓ) := hremaining_default a (by simp)
      have ha_sep : a ≠ chainConsBottom := hremaining_sep a (by simp)
      have hrest_default : ∀ x ∈ remaining, x ≠ (default : ChainΓ) := by
        intro x hx
        exact hremaining_default x (List.mem_cons_of_mem a hx)
      have hrest_sep : ∀ x ∈ remaining, x ≠ chainConsBottom := by
        intro x hx
        exact hremaining_sep x (List.mem_cons_of_mem a hx)
      let mid : TM0.Cfg ChainΓ SepPresenceSt :=
        ⟨SepPresenceSt.scan,
          Tape.mk' (ListBlank.mk (a :: processed_rev)) (ListBlank.mk (remaining ++ tail))⟩
      refine Relation.ReflTransGen.trans (b := mid) ?_ ?_
      · apply Relation.ReflTransGen.single
        simp [Tape.mk', TM0.step, sepPresenceMachine, ha_default, ha_sep, mid, Tape.move]
      · convert ih (a :: processed_rev) hrest_default hrest_sep using 1
        simp [List.reverse_cons, List.append_assoc]

theorem sepPresence_rewind_loop (found : Bool) (revBlock acc : List ChainΓ)
    (hrevBlock : ∀ x ∈ revBlock, x ≠ (default : ChainΓ)) :
    Reaches (TM0.step sepPresenceMachine)
      ⟨SepPresenceSt.rewind found,
        ⟨revBlock.headI, ListBlank.mk revBlock.tail, ListBlank.mk acc⟩⟩
      ⟨SepPresenceSt.rewind found,
        ⟨default, ListBlank.mk [], ListBlank.mk (revBlock.reverse ++ acc)⟩⟩ := by
  induction revBlock generalizing acc with
  | nil => exact Relation.ReflTransGen.refl
  | cons a revBlock ih =>
      have ha : a ≠ (default : ChainΓ) := hrevBlock a (by simp)
      have hrest : ∀ x ∈ revBlock, x ≠ (default : ChainΓ) := by
        intro x hx
        exact hrevBlock x (List.mem_cons_of_mem a hx)
      let mid : TM0.Cfg ChainΓ SepPresenceSt :=
        ⟨SepPresenceSt.rewind found,
          Tape.move Dir.left ⟨a, ListBlank.mk revBlock, ListBlank.mk acc⟩⟩
      refine Relation.ReflTransGen.trans (b := mid) ?_ ?_
      · apply Relation.ReflTransGen.single
        simp [TM0.step, sepPresenceMachine, ha, mid, Tape.move]
      · convert ih (a :: acc) hrest using 1
        simp [List.reverse_cons, List.append_assoc]

theorem splitAtConsBottom_reconstruct_of_mem (block : List ChainΓ)
    (h : chainConsBottom ∈ block) :
    block = (splitAtConsBottom block).1 ++ chainConsBottom :: (splitAtConsBottom block).2 := by
  induction block with
  | nil => simp at h
  | cons c rest ih =>
      by_cases hc : c = chainConsBottom
      · simp [splitAtConsBottom, hc]
      · have hrest : chainConsBottom ∈ rest := by
          simp at h
          rcases h with h' | h'
          · exact absurd h'.symm hc
          · exact h'
        simp only [splitAtConsBottom, hc, if_false]
        exact congrArg (List.cons c) (ih hrest)

theorem sepPresenceMachine_correct (block suffix : List ChainΓ)
    (hblock : ∀ x ∈ block, x ≠ (default : ChainΓ))
    (_hsuffix : ∀ x ∈ suffix, x ≠ (default : ChainΓ)) :
    (TM0Seq.evalCfg sepPresenceMachine (block ++ default :: suffix)).Dom ∧
    ∀ (h : (TM0Seq.evalCfg sepPresenceMachine (block ++ default :: suffix)).Dom),
      ((TM0Seq.evalCfg sepPresenceMachine (block ++ default :: suffix)).get h).Tape =
          Tape.mk₁ (block ++ default :: suffix) ∧
      (chainConsBottom ∈ block →
        ((TM0Seq.evalCfg sepPresenceMachine (block ++ default :: suffix)).get h).q =
          SepPresenceSt.done true) ∧
      (chainConsBottom ∉ block →
        ((TM0Seq.evalCfg sepPresenceMachine (block ++ default :: suffix)).get h).q =
          SepPresenceSt.done false) := by
  by_cases hsep : chainConsBottom ∈ block
  · set left := (splitAtConsBottom block).1
    set right := (splitAtConsBottom block).2
    have hblock_eq : block = left ++ chainConsBottom :: right := by
      simpa [left, right] using splitAtConsBottom_reconstruct_of_mem block hsep
    have hleft_default : ∀ x ∈ left, x ≠ (default : ChainΓ) := by
      intro x hx
      exact hblock x (by rw [hblock_eq]; simp [hx])
    have hleft_sep : ∀ x ∈ left, x ≠ chainConsBottom := by
      intro x hx
      exact splitAtConsBottom_fst_no_sep block x (by simpa [left] using hx)
    have hleft_rev_default : ∀ x ∈ left.reverse, x ≠ (default : ChainΓ) := by
      intro x hx
      exact hleft_default x (List.mem_reverse.mp hx)
    have h_scan := sepPresence_scan_gen left [] (chainConsBottom :: right ++ default :: suffix)
      hleft_default hleft_sep
    have h_trans := sepPresence_scan_sep (ListBlank.mk left.reverse)
      (ListBlank.mk (right ++ default :: suffix))
    have h_rewind := sepPresence_rewind_loop true left.reverse
      (chainConsBottom :: right ++ default :: suffix) hleft_rev_default
    have h_done := sepPresence_rewind_default true (ListBlank.mk [])
      (ListBlank.mk (left ++ chainConsBottom :: right ++ default :: suffix))
    have h_chain : Reaches (TM0.step sepPresenceMachine)
        (TM0.init (block ++ default :: suffix))
        ⟨SepPresenceSt.done true, Tape.mk₁ (block ++ default :: suffix)⟩ := by
      have h_chain' : Reaches (TM0.step sepPresenceMachine)
          ⟨SepPresenceSt.scan,
            Tape.mk' (ListBlank.mk [])
              (ListBlank.mk (left ++ chainConsBottom :: right ++ default :: suffix))⟩
          ⟨SepPresenceSt.done true,
            Tape.mk₁ (left ++ chainConsBottom :: right ++ default :: suffix)⟩ := by
        have h_scan' : Reaches (TM0.step sepPresenceMachine)
            ⟨SepPresenceSt.scan,
              Tape.mk' (ListBlank.mk [])
                (ListBlank.mk (left ++ chainConsBottom :: right ++ default :: suffix))⟩
            ⟨SepPresenceSt.scan,
              Tape.mk' (ListBlank.mk left.reverse)
                (ListBlank.mk (chainConsBottom :: right ++ default :: suffix))⟩ := by
          convert h_scan using 1 <;> simp
        refine h_scan'.trans ?_
        refine Relation.ReflTransGen.trans
          (b := ⟨SepPresenceSt.rewind true,
            ⟨left.reverse.headI, ListBlank.mk left.reverse.tail,
              ListBlank.mk (chainConsBottom :: right ++ default :: suffix)⟩⟩) ?_ ?_
        · apply Relation.ReflTransGen.single
          simp [Tape.mk', TM0.step, sepPresenceMachine, chainConsBottom_ne_default,
            Tape.move]
        refine h_rewind.trans ?_
        apply Relation.ReflTransGen.single
        simp [TM0.step, sepPresenceMachine, Tape.move, Tape.mk₁, List.append_assoc,
          listBlank_mk_singleton_default_chainΓ, tape_mk₂_nil_eq_headI_tail_chainΓ]
      simpa [TM0.init, hblock_eq, List.append_assoc] using h_chain'
    have hhalt : TM0.step sepPresenceMachine
        ⟨SepPresenceSt.done true, Tape.mk₁ (block ++ default :: suffix)⟩ = none :=
      sepPresence_done_halt true _
    have hmem :
        ⟨SepPresenceSt.done true, Tape.mk₁ (block ++ default :: suffix)⟩ ∈
          TM0Seq.evalCfg sepPresenceMachine (block ++ default :: suffix) := by
      exact Turing.mem_eval.mpr ⟨h_chain, hhalt⟩
    refine ⟨Part.dom_iff_mem.mpr ⟨_, hmem⟩, ?_⟩
    intro h
    have hget :
        (TM0Seq.evalCfg sepPresenceMachine (block ++ default :: suffix)).get h =
          ⟨SepPresenceSt.done true, Tape.mk₁ (block ++ default :: suffix)⟩ :=
      Part.get_eq_of_mem hmem h
    rw [hget]
    simp [hsep]
  · have hblock_nsep : ∀ x ∈ block, x ≠ chainConsBottom := by
      intro x hx hxeq
      exact hsep (by rw [← hxeq]; exact hx)
    have h_scan := sepPresence_scan_gen block [] (default :: suffix) hblock hblock_nsep
    have h_trans := sepPresence_scan_default (ListBlank.mk block.reverse)
      (ListBlank.mk suffix)
    have hblock_rev : ∀ x ∈ block.reverse, x ≠ (default : ChainΓ) := by
      intro x hx
      exact hblock x (List.mem_reverse.mp hx)
    have h_rewind := sepPresence_rewind_loop false block.reverse (default :: suffix)
      hblock_rev
    have h_done := sepPresence_rewind_default false (ListBlank.mk [])
      (ListBlank.mk (block ++ default :: suffix))
    have h_chain : Reaches (TM0.step sepPresenceMachine)
        (TM0.init (block ++ default :: suffix))
        ⟨SepPresenceSt.done false, Tape.mk₁ (block ++ default :: suffix)⟩ := by
      have h_chain' : Reaches (TM0.step sepPresenceMachine)
          ⟨SepPresenceSt.scan,
            Tape.mk' (ListBlank.mk []) (ListBlank.mk (block ++ default :: suffix))⟩
          ⟨SepPresenceSt.done false, Tape.mk₁ (block ++ default :: suffix)⟩ := by
        have h_scan' : Reaches (TM0.step sepPresenceMachine)
            ⟨SepPresenceSt.scan,
              Tape.mk' (ListBlank.mk []) (ListBlank.mk (block ++ default :: suffix))⟩
            ⟨SepPresenceSt.scan,
              Tape.mk' (ListBlank.mk block.reverse) (ListBlank.mk (default :: suffix))⟩ := by
          convert h_scan using 1
          simp
        refine h_scan'.trans ?_
        refine Relation.ReflTransGen.trans
          (b := ⟨SepPresenceSt.rewind false,
            ⟨block.reverse.headI, ListBlank.mk block.reverse.tail,
              ListBlank.mk (default :: suffix)⟩⟩) ?_ ?_
        · apply Relation.ReflTransGen.single
          simp [Tape.mk', TM0.step, sepPresenceMachine, Tape.move]
        refine h_rewind.trans ?_
        apply Relation.ReflTransGen.single
        simp [TM0.step, sepPresenceMachine, Tape.move, Tape.mk₁,
          listBlank_mk_singleton_default_chainΓ, tape_mk₂_nil_eq_headI_tail_chainΓ]
      simpa [TM0.init, List.append_assoc] using h_chain'
    have hhalt : TM0.step sepPresenceMachine
        ⟨SepPresenceSt.done false, Tape.mk₁ (block ++ default :: suffix)⟩ = none :=
      sepPresence_done_halt false _
    have hmem :
        ⟨SepPresenceSt.done false, Tape.mk₁ (block ++ default :: suffix)⟩ ∈
          TM0Seq.evalCfg sepPresenceMachine (block ++ default :: suffix) := by
      exact Turing.mem_eval.mpr ⟨h_chain, hhalt⟩
    refine ⟨Part.dom_iff_mem.mpr ⟨_, hmem⟩, ?_⟩
    intro h
    have hget :
        (TM0Seq.evalCfg sepPresenceMachine (block ++ default :: suffix)).get h =
          ⟨SepPresenceSt.done false, Tape.mk₁ (block ++ default :: suffix)⟩ :=
      Part.get_eq_of_mem hmem h
    rw [hget]
    simp [hsep]

/-- Public conditional-decider shape for `chainConsBottom ∈ block`. -/
theorem tm0_hasConsBottom_decidable :
    ∃ (Λ : Type) (_ : Inhabited Λ) (_ : Fintype Λ)
      (M : TM0.Machine ChainΓ Λ) (q_true q_false : Λ),
      q_true ≠ q_false ∧
      ∀ (block suffix : List ChainΓ),
        (∀ x ∈ block, x ≠ default) → (∀ x ∈ suffix, x ≠ default) →
        (TM0Seq.evalCfg M (block ++ default :: suffix)).Dom ∧
        ∀ (h : (TM0Seq.evalCfg M (block ++ default :: suffix)).Dom),
          ((TM0Seq.evalCfg M (block ++ default :: suffix)).get h).Tape =
            Tape.mk₁ (block ++ default :: suffix) ∧
          (chainConsBottom ∈ block →
            ((TM0Seq.evalCfg M (block ++ default :: suffix)).get h).q = q_true) ∧
          (chainConsBottom ∉ block →
            ((TM0Seq.evalCfg M (block ++ default :: suffix)).get h).q = q_false) := by
  refine ⟨SepPresenceSt, inferInstance, inferInstance, sepPresenceMachine,
    SepPresenceSt.done true, SepPresenceSt.done false, by simp, ?_⟩
  intro block suffix hblock hsuffix
  exact sepPresenceMachine_correct block suffix hblock hsuffix
