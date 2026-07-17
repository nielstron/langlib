module

public import Langlib.Automata.LinearBounded.BoundedDegree
public import Langlib.Automata.LinearBounded.CertifiedRowSystem.StrictAcyclicize
public import Langlib.Automata.LinearBounded.CertifiedRowSystem.Determinize
import Mathlib.Tactic

@[expose]
public section

/-!
# Directed degree bounds for the LBA row presentation

The semantic row relation of `LBA.certifiedRowSystem` has one extra kind of edge besides machine
steps: a raw input row enters the canonical initial configuration.  Thus a global
configuration-indegree-two bound alone would only give a row-indegree-three bound.

Incoming-edge serialization is sharper at exactly the required phase.  Every `.base`
configuration has at most one machine predecessor.  The raw initialization edge targets the
initial `.base` configuration and, for an injective input embedding, contributes at most one
additional predecessor.  All other configuration rows inherit the ordinary degree-two bound.
-/

open Classical

namespace LBA

variable {I Γ Λ : Type*}

/-- Every configuration in the canonical initial control state has at most one predecessor. -/
public def Machine.InitialConfigurationIndegreeAtMostOne
    (M : Machine Γ Λ) : Prop :=
  ∀ (n : ℕ) (tape : DLBA.BoundedTape Γ n),
    Set.encard {cfg | Step M cfg ⟨M.initial, tape⟩} ≤ 1

/-- The initial state of an incoming-edge serializer is a base phase, whose predecessor is
uniquely the final node of its merge chain. -/
public theorem Machine.serializeIncoming_initialConfigurationIndegreeAtMostOne
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) :
    M.serializeIncoming.InitialConfigurationIndegreeAtMostOne := by
  intro n tape
  exact M.serializeIncoming_configurationIndegreeBaseAtMostOne M.initial tape

/-- In particular, the simultaneous degree serializer has the sharper one-predecessor bound at
its canonical initial state. -/
public theorem Machine.boundedDegree_initialConfigurationIndegreeAtMostOne
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) :
    M.boundedDegree.InitialConfigurationIndegreeAtMostOne :=
  M.binaryBranch.serializeIncoming_initialConfigurationIndegreeAtMostOne

namespace CertifiedRows

/-- The configuration with the specified state, tape split, scanned symbol, and head position. -/
private noncomputable def cfgOfSplit (q : Λ) (left : List Γ) (a : Γ)
    (right : List Γ) :
    DLBA.Cfg Γ Λ (left.length + right.length) :=
  { state := q
    tape :=
      { contents := fun i =>
          (left ++ a :: right).get ⟨i.val, by simp; omega⟩
        head := ⟨left.length, by simp⟩ } }

private theorem tapeList_cfgOfSplit (q : Λ) (left : List Γ) (a : Γ)
    (right : List Γ) :
    tapeList (cfgOfSplit q left a right) = left ++ a :: right := by
  unfold tapeList cfgOfSplit
  have hlen :
      left.length + right.length + 1 = (left ++ a :: right).length := by
    simp
    omega
  rw [List.ofFn_congr hlen]
  simpa using List.ofFn_get (left ++ a :: right)

private theorem leftSymbols_cfgOfSplit (q : Λ) (left : List Γ) (a : Γ)
    (right : List Γ) :
    leftSymbols (cfgOfSplit q left a right) = left := by
  change List.take left.length (tapeList (cfgOfSplit q left a right)) = left
  rw [tapeList_cfgOfSplit]
  simp

private theorem rightSymbols_cfgOfSplit (q : Λ) (left : List Γ) (a : Γ)
    (right : List Γ) :
    rightSymbols (cfgOfSplit q left a right) = right := by
  change List.drop (left.length + 1) (tapeList (cfgOfSplit q left a right)) = right
  rw [tapeList_cfgOfSplit]
  simp

private theorem read_cfgOfSplit (q : Λ) (left : List Γ) (a : Γ)
    (right : List Γ) :
    (cfgOfSplit q left a right).tape.read = a := by
  simp [cfgOfSplit, DLBA.BoundedTape.read, List.get_eq_getElem]

private theorem configRow_cfgOfSplit (q : Λ) (left : List Γ) (a : Γ)
    (right : List Γ) :
    configRow (I := I) (cfgOfSplit q left a right) =
      configCells q left a right := by
  unfold configRow
  rw [leftSymbols_cfgOfSplit, rightSymbols_cfgOfSplit, read_cfgOfSplit]
  rfl

private theorem noHeadCells_eq_iff (q : Λ) (xs ys : List Γ) :
    noHeadCells (I := I) q xs = noHeadCells q ys ↔ xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [noHeadCells]
  | cons x xs ih =>
      cases ys with
      | nil => simp [noHeadCells]
      | cons y ys =>
          constructor
          · intro h
            rcases List.cons.inj h with ⟨hxy, htail⟩
            have hxy' : x = y := by simpa using hxy
            exact congrArg₂ List.cons hxy' ((ih ys).1 htail)
          · intro h
            rcases List.cons.inj h with ⟨hxy, htail⟩
            subst y
            exact congrArg (List.cons (.cfg x false q)) ((ih ys).2 htail)

private theorem configCells_eq_iff (q q' : Λ) (left left' : List Γ) (a a' : Γ)
    (right right' : List Γ) :
    configCells (I := I) q left a right = configCells q' left' a' right' ↔
      q = q' ∧ left = left' ∧ a = a' ∧ right = right' := by
  induction left generalizing q q' left' a a' right right' with
  | nil =>
      cases left' with
      | nil =>
          constructor
          · intro h
            rcases List.cons.inj h with ⟨hhead, htail⟩
            have hhead' : a = a' ∧ q = q' := by simpa using hhead
            rcases hhead' with ⟨rfl, rfl⟩
            exact ⟨rfl, rfl, rfl, (noHeadCells_eq_iff q right right').1 htail⟩
          · rintro ⟨hq, _, ha, hright⟩
            subst q'
            subst a'
            subst right'
            rfl
      | cons y ys => simp [configCells, noHeadCells]
  | cons x left ih =>
      cases left' with
      | nil => simp [configCells, noHeadCells]
      | cons y ys =>
          constructor
          · intro h
            rcases List.cons.inj h with ⟨hhead, htail⟩
            have hhead' : x = y ∧ q = q' := by simpa using hhead
            rcases hhead' with ⟨rfl, rfl⟩
            rcases (ih q q ys a a' right right').1 htail with
              ⟨_, hleft, ha, hright⟩
            exact ⟨rfl, congrArg (List.cons x) hleft, ha, hright⟩
          · rintro ⟨hq, hleft, ha, hright⟩
            subst q'
            rcases List.cons.inj hleft with ⟨hxy, htail⟩
            subst y
            subst ys
            subst a'
            subst right'
            rfl

private theorem tapeList_eq_parts {n : Nat} (cfg : DLBA.Cfg Γ Λ n) :
    tapeList cfg = leftSymbols cfg ++ cfg.tape.read :: rightSymbols cfg := by
  rw [← List.take_append_drop cfg.tape.head.val (tapeList cfg)]
  congr 1
  rw [← List.cons_getElem_drop_succ (n := cfg.tape.head.val)
    (h := by simp [tapeList]; omega)]
  congr 1
  unfold tapeList DLBA.BoundedTape.read
  rw [List.getElem_ofFn]

private theorem boundedTape_eq_of_list_head {n : Nat}
    (x y : DLBA.BoundedTape Γ n)
    (hl : List.ofFn x.contents = List.ofFn y.contents)
    (hh : x.head.val = y.head.val) :
    x = y := by
  cases x with
  | mk xc xh =>
      cases y with
      | mk yc yh =>
          simp only [DLBA.BoundedTape.mk.injEq]
          exact ⟨List.ofFn_injective hl, Fin.ext hh⟩

/-- Canonical configuration-row encoding is injective at every fixed width. -/
public theorem configRow_injective {n : Nat} :
    Function.Injective
      (configRow (I := I) : DLBA.Cfg Γ Λ n → List (RowCell I Γ Λ)) := by
  intro cfg cfg' hrow
  have hparts := (configCells_eq_iff cfg.state cfg'.state
    (leftSymbols cfg) (leftSymbols cfg') cfg.tape.read cfg'.tape.read
    (rightSymbols cfg) (rightSymbols cfg')).1 hrow
  rcases hparts with ⟨hstate, hleft, hread, hright⟩
  have htape : cfg.tape = cfg'.tape := by
    apply boundedTape_eq_of_list_head
    · change tapeList cfg = tapeList cfg'
      rw [tapeList_eq_parts, tapeList_eq_parts]
      simp only [hleft, hread, hright]
    · have hlength := congrArg List.length hleft
      simpa [leftSymbols, tapeList] using hlength
  cases cfg
  cases cfg'
  simp_all

/-- Every source of a semantic row move is either a raw input row or a configuration row. -/
private theorem source_shape
    (M : Machine Γ Λ) (embed : I → Γ)
    {old new : List (RowCell I Γ Λ)}
    (hmove : RowMove M embed old new) :
    (∃ input : List I, old = input.map .raw) ∨
      ∃ n, ∃ cfg : DLBA.Cfg Γ Λ n, old = configRow cfg := by
  cases hmove with
  | init i is =>
      exact Or.inl ⟨i :: is, rfl⟩
  | stay q q' a b left right hstep =>
      refine Or.inr ⟨_, cfgOfSplit q left a right, ?_⟩
      rw [configRow_cfgOfSplit]
      simp [configCells]
  | leftClamp q q' a b right hstep =>
      refine Or.inr ⟨_, cfgOfSplit q [] a right, ?_⟩
      rw [configRow_cfgOfSplit]
      simp [configCells, noHeadCells]
  | rightClamp q q' a b left hstep =>
      refine Or.inr ⟨_, cfgOfSplit q left a [], ?_⟩
      rw [configRow_cfgOfSplit]
      simp [configCells, noHeadCells]
  | left q q' x a b left right hstep =>
      refine Or.inr ⟨(left ++ [x]).length + right.length,
        cfgOfSplit q (left ++ [x]) a right, ?_⟩
      rw [configRow_cfgOfSplit]
      simp [configCells, noHeadCells]
  | right q q' a b x left right hstep =>
      refine Or.inr ⟨left.length + (x :: right).length,
        cfgOfSplit q left a (x :: right), ?_⟩
      rw [configRow_cfgOfSplit]
      rfl

/-- Every target of a semantic row move is a configuration row. -/
private theorem target_shape
    (M : Machine Γ Λ) (embed : I → Γ)
    {old new : List (RowCell I Γ Λ)}
    (hmove : RowMove M embed old new) :
    ∃ n, ∃ cfg : DLBA.Cfg Γ Λ n, new = configRow cfg := by
  cases hmove with
  | init i is =>
      refine ⟨_, cfgOfSplit M.initial [] (embed i) (is.map embed), ?_⟩
      rw [configRow_cfgOfSplit]
      simp [configCells, noHeadCells]
  | stay q q' a b left right hstep =>
      refine ⟨_, cfgOfSplit q' left b right, ?_⟩
      rw [configRow_cfgOfSplit]
      simp [configCells]
  | leftClamp q q' a b right hstep =>
      refine ⟨_, cfgOfSplit q' [] b right, ?_⟩
      rw [configRow_cfgOfSplit]
      simp [configCells, noHeadCells]
  | rightClamp q q' a b left hstep =>
      refine ⟨_, cfgOfSplit q' left b [], ?_⟩
      rw [configRow_cfgOfSplit]
      simp [configCells, noHeadCells]
  | left q q' x a b left right hstep =>
      refine ⟨left.length + (b :: right).length,
        cfgOfSplit q' left x (b :: right), ?_⟩
      rw [configRow_cfgOfSplit]
      rfl
  | right q q' a b x left right hstep =>
      refine ⟨(left ++ [b]).length + right.length,
        cfgOfSplit q' (left ++ [b]) x right, ?_⟩
      rw [configRow_cfgOfSplit]
      simp [configCells, noHeadCells]

private theorem rowMove_raw_target
    [DecidableEq I] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) (embed : I → Γ) (i : I) (is : List I)
    {new : List (RowCell I Γ Λ)}
    (h : RowMove M embed ((i :: is).map .raw) new) :
    new = .cfg (embed i) true M.initial ::
      noHeadCells M.initial (is.map embed) := by
  generalize hold :
      (i :: is).map (RowCell.raw (Γ := Γ) (Λ := Λ)) = old at h
  cases h with
  | init j js =>
      have hinput : i :: is = j :: js :=
        (Function.Injective.list_map (fun _ _ h => RowCell.raw.inj h)) hold
      cases hinput
      rfl
  | stay q q' a b left right hstep =>
      cases left <;> simp [noHeadCells] at hold
  | leftClamp q q' a b right hstep =>
      simp [noHeadCells] at hold
  | rightClamp q q' a b left hstep =>
      cases left <;> simp [noHeadCells] at hold
  | left q q' x a b left right hstep =>
      cases left <;> simp [noHeadCells] at hold
  | right q q' a b x left right hstep =>
      cases left <;> simp [noHeadCells] at hold

private theorem raw_source_unique
    [DecidableEq I] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) (embed : I → Γ) (input : List I)
    {new₁ new₂ : List (RowCell I Γ Λ)}
    (h₁ : RowMove M embed (input.map .raw) new₁)
    (h₂ : RowMove M embed (input.map .raw) new₂) :
    new₁ = new₂ := by
  cases input with
  | nil =>
      generalize hold : ([] : List I).map
        (RowCell.raw (Γ := Γ) (Λ := Λ)) = old at h₁
      cases h₁ <;> simp [noHeadCells] at hold
  | cons i is =>
      rw [rowMove_raw_target M embed i is h₁,
        rowMove_raw_target M embed i is h₂]

private theorem raw_predecessor_unique
    [DecidableEq I] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) (embed : I → Γ) (hinjective : Function.Injective embed)
    {input₁ input₂ : List I} {new : List (RowCell I Γ Λ)}
    (h₁ : RowMove M embed (input₁.map .raw) new)
    (h₂ : RowMove M embed (input₂.map .raw) new) :
    input₁ = input₂ := by
  cases input₁ with
  | nil =>
      generalize hold : ([] : List I).map
        (RowCell.raw (Γ := Γ) (Λ := Λ)) = old at h₁
      cases h₁ <;> simp [noHeadCells] at hold
  | cons i is =>
      cases input₂ with
      | nil =>
          generalize hold : ([] : List I).map
            (RowCell.raw (Γ := Γ) (Λ := Λ)) = old at h₂
          cases h₂ <;> simp [noHeadCells] at hold
      | cons j js =>
          have htarget :
              (.cfg (embed i) true M.initial ::
                  noHeadCells M.initial (is.map embed) :
                List (RowCell I Γ Λ)) =
                .cfg (embed j) true M.initial ::
                  noHeadCells M.initial (js.map embed) := by
            rw [← rowMove_raw_target M embed i is h₁,
              ← rowMove_raw_target M embed j js h₂]
          have hembed : (i :: is).map embed = (j :: js).map embed := by
            rcases List.cons.inj htarget with ⟨hhead, htail⟩
            have hi : embed i = embed j := by simpa using hhead
            have ht : is.map embed = js.map embed :=
              (noHeadCells_eq_iff M.initial _ _).1 htail
            exact congrArg₂ List.cons hi ht
          exact Function.Injective.list_map hinjective hembed

/-- Under a machine outdegree-two bound, the certified row presentation also has row
outdegree at most two. -/
public theorem certifiedRowSystem_rowOutdegreeAtMostTwo
    [DecidableEq I] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) (embed : I → Γ)
    (hout : M.ConfigurationOutdegreeAtMostTwo) :
    CertifiedRowSystem.RowOutdegreeAtMost 2 (certifiedRowSystem M embed) := by
  intro old
  classical
  by_cases hempty :
      {new | (certifiedRowSystem M embed).RowStep old new} = ∅
  · rw [hempty]
    simp
  · obtain ⟨new₀, hnew₀⟩ := Set.nonempty_iff_ne_empty.mpr hempty
    have hmove₀ :=
      (certifiedRowSystem_rowStep_iff M embed old new₀).1 hnew₀
    rcases source_shape M embed hmove₀ with ⟨input, hraw⟩ |
        ⟨n, cfg, hcfg⟩
    · subst old
      calc
        Set.encard
            {new | (certifiedRowSystem M embed).RowStep
              (input.map .raw) new} ≤
            Set.encard ({new₀} : Set (List (RowCell I Γ Λ))) := by
          apply Set.encard_le_encard
          intro new hnew
          simp only [Set.mem_singleton_iff]
          exact raw_source_unique M embed input
            ((certifiedRowSystem_rowStep_iff M embed _ _).1 hnew) hmove₀
        _ ≤ 2 := by simp
    · subst old
      let nextCfg (new : List (RowCell I Γ Λ)) : DLBA.Cfg Γ Λ n :=
        if hnew : (certifiedRowSystem M embed).RowStep (configRow cfg) new then
          Classical.choose
            (step_of_rowMove_configRow M embed cfg
              ((certifiedRowSystem_rowStep_iff M embed _ _).1 hnew))
        else cfg
      have nextCfg_spec (new : List (RowCell I Γ Λ))
          (hnew : (certifiedRowSystem M embed).RowStep (configRow cfg) new) :
          Step M cfg (nextCfg new) ∧ new = configRow (nextCfg new) := by
        dsimp only [nextCfg]
        rw [dif_pos hnew]
        exact Classical.choose_spec
          (step_of_rowMove_configRow M embed cfg
            ((certifiedRowSystem_rowStep_iff M embed _ _).1 hnew))
      calc
        Set.encard
            {new | (certifiedRowSystem M embed).RowStep
              (configRow cfg) new} ≤
            Set.encard {cfg' | Step M cfg cfg'} := by
          apply Set.encard_le_encard_of_injOn (f := nextCfg)
          · intro new hnew
            exact (nextCfg_spec new hnew).1
          · intro left hleft right hright heq
            rw [(nextCfg_spec left hleft).2,
              (nextCfg_spec right hright).2, heq]
        _ ≤ 2 := hout n cfg

private theorem config_predecessor_of_not_raw
    [DecidableEq I] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) (embed : I → Γ) {n : Nat}
    (target : DLBA.Cfg Γ Λ n) {old : List (RowCell I Γ Λ)}
    (hmove : RowMove M embed old (configRow target))
    (hnoraw : ¬ ∃ input : List I, old = input.map .raw) :
    ∃ cfg : DLBA.Cfg Γ Λ n,
      Step M cfg target ∧ old = configRow cfg := by
  rcases source_shape M embed hmove with hraw | ⟨m, cfg, hcfg⟩
  · exact (hnoraw hraw).elim
  · have hrowStep :
        (certifiedRowSystem M embed).RowStep old (configRow target) :=
      (certifiedRowSystem_rowStep_iff M embed _ _).2 hmove
    have hlength := (certifiedRowSystem M embed).rowStep_length hrowStep
    have hm : m = n := by
      rw [hcfg] at hlength
      simp only [configRow_length] at hlength
      omega
    subst m
    have hmove' : RowMove M embed (configRow cfg) (configRow target) := by
      simpa [hcfg] using hmove
    obtain ⟨next, hstep, hnext⟩ :=
      step_of_rowMove_configRow M embed cfg hmove'
    have hnextEq : next = target := by
      apply configRow_injective
      exact hnext.symm
    subst next
    exact ⟨cfg, hstep, hcfg⟩

private theorem target_initial_of_raw_predecessor
    [DecidableEq I] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) (embed : I → Γ) {n : Nat}
    (target : DLBA.Cfg Γ Λ n) {input : List I}
    (hmove : RowMove M embed (input.map .raw) (configRow target)) :
    target.state = M.initial := by
  cases input with
  | nil =>
      have hstep :
          (certifiedRowSystem M embed).RowStep
            (([] : List I).map .raw) (configRow target) :=
        (certifiedRowSystem_rowStep_iff M embed _ _).2 hmove
      have hlength := (certifiedRowSystem M embed).rowStep_length hstep
      simp at hlength
  | cons i is =>
      have htarget := rowMove_raw_target M embed i is hmove
      have hcells :
          configCells (I := I) target.state (leftSymbols target)
              target.tape.read (rightSymbols target) =
            configCells M.initial [] (embed i) (is.map embed) := by
        simpa [configRow, configCells, noHeadCells] using htarget
      exact (configCells_eq_iff target.state M.initial
        (leftSymbols target) [] target.tape.read (embed i)
        (rightSymbols target) (is.map embed)).1 hcells |>.1

/-- If initial-state configurations have at most one machine predecessor, then the raw
initialization edge uses the only additional predecessor slot and every row has indegree at
most two. -/
public theorem certifiedRowSystem_rowIndegreeAtMostTwo
    [DecidableEq I] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) (embed : I → Γ)
    (hinjective : Function.Injective embed)
    (hin : M.ConfigurationIndegreeAtMostTwo)
    (hinit : M.InitialConfigurationIndegreeAtMostOne) :
    CertifiedRowSystem.RowIndegreeAtMost 2 (certifiedRowSystem M embed) := by
  intro new
  classical
  by_cases hempty :
      {old | (certifiedRowSystem M embed).RowStep old new} = ∅
  · rw [hempty]
    simp
  · obtain ⟨old₀, hold₀⟩ := Set.nonempty_iff_ne_empty.mpr hempty
    have hmove₀ :=
      (certifiedRowSystem_rowStep_iff M embed old₀ new).1 hold₀
    obtain ⟨n, target, htarget⟩ := target_shape M embed hmove₀
    subst new
    by_cases hrawTarget :
        ∃ input : List I,
          RowMove M embed (input.map .raw) (configRow target)
    · obtain ⟨rawInput, hrawMove⟩ := hrawTarget
      have htargetState :
          target.state = M.initial :=
        target_initial_of_raw_predecessor M embed target hrawMove
      let machinePred : Set (DLBA.Cfg Γ Λ n) :=
        {cfg | Step M cfg target}
      let encodedPred : Set (Unit ⊕ DLBA.Cfg Γ Λ n) :=
        insert (.inl ()) (.inr '' machinePred)
      let chosenPred (old : List (RowCell I Γ Λ))
          (hstep :
            (certifiedRowSystem M embed).RowStep old (configRow target))
          (hraw : ¬ ∃ input : List I, old = input.map .raw) :
          DLBA.Cfg Γ Λ n :=
        Classical.choose
          (config_predecessor_of_not_raw M embed target
            ((certifiedRowSystem_rowStep_iff M embed _ _).1 hstep) hraw)
      have chosenPred_spec (old : List (RowCell I Γ Λ))
          (hstep :
            (certifiedRowSystem M embed).RowStep old (configRow target))
          (hraw : ¬ ∃ input : List I, old = input.map .raw) :
          Step M (chosenPred old hstep hraw) target ∧
            old = configRow (chosenPred old hstep hraw) :=
        Classical.choose_spec
          (config_predecessor_of_not_raw M embed target
            ((certifiedRowSystem_rowStep_iff M embed _ _).1 hstep) hraw)
      let predecessorCode
          (old : List (RowCell I Γ Λ)) : Unit ⊕ DLBA.Cfg Γ Λ n :=
        if hstep :
            (certifiedRowSystem M embed).RowStep old (configRow target) then
          if hraw : ∃ input : List I, old = input.map .raw then
            .inl ()
          else
            .inr (chosenPred old hstep hraw)
        else .inl ()
      calc
        Set.encard
            {old | (certifiedRowSystem M embed).RowStep
              old (configRow target)} ≤ Set.encard encodedPred := by
          apply Set.encard_le_encard_of_injOn (f := predecessorCode)
          · intro old hold
            change (certifiedRowSystem M embed).RowStep
              old (configRow target) at hold
            by_cases hraw :
                ∃ input : List I, old = input.map .raw
            · simp [predecessorCode, hold, hraw, encodedPred]
            · have hspec := chosenPred_spec old hold hraw
              refine Set.mem_insert_iff.mpr (Or.inr ?_)
              exact ⟨chosenPred old hold hraw, hspec.1, by
                simp [predecessorCode, chosenPred, hold, hraw]⟩
          · intro left hleft right hright heq
            change (certifiedRowSystem M embed).RowStep
              left (configRow target) at hleft
            change (certifiedRowSystem M embed).RowStep
              right (configRow target) at hright
            by_cases hrawLeft :
                ∃ input : List I, left = input.map .raw
            · by_cases hrawRight :
                  ∃ input : List I, right = input.map .raw
              · obtain ⟨inputLeft, rfl⟩ := hrawLeft
                obtain ⟨inputRight, rfl⟩ := hrawRight
                have hleftMove :=
                  (certifiedRowSystem_rowStep_iff M embed _ _).1 hleft
                have hrightMove :=
                  (certifiedRowSystem_rowStep_iff M embed _ _).1 hright
                rw [raw_predecessor_unique M embed hinjective
                  hleftMove hrightMove]
              · simp [predecessorCode, hleft, hright,
                  hrawLeft, hrawRight] at heq
            · by_cases hrawRight :
                  ∃ input : List I, right = input.map .raw
              · simp [predecessorCode, hleft, hright,
                  hrawLeft, hrawRight] at heq
              · have hleftSpec := chosenPred_spec left hleft hrawLeft
                have hrightSpec := chosenPred_spec right hright hrawRight
                have hcfg :
                    chosenPred left hleft hrawLeft =
                      chosenPred right hright hrawRight := by
                  simpa [predecessorCode, hleft, hright,
                    hrawLeft, hrawRight] using heq
                rw [hleftSpec.2, hrightSpec.2, hcfg]
        _ ≤ Set.encard machinePred + 1 := by
          calc
            Set.encard encodedPred ≤
                Set.encard
                    ((Sum.inr : DLBA.Cfg Γ Λ n →
                      Unit ⊕ DLBA.Cfg Γ Λ n) '' machinePred) + 1 := by
              exact Set.encard_insert_le _ _
            _ ≤ Set.encard machinePred + 1 := by
              exact add_le_add (Set.encard_image_le _ _) (le_refl 1)
        _ ≤ 1 + 1 := by
          have htargetEq :
              target =
                (⟨M.initial, target.tape⟩ : DLBA.Cfg Γ Λ n) := by
            cases target
            simp_all
          have hpred : Set.encard machinePred ≤ 1 := by
            have hmset :
                machinePred =
                  {cfg |
                    Step M cfg
                      (⟨M.initial, target.tape⟩ :
                        DLBA.Cfg Γ Λ n)} := by
              ext cfg
              change Step M cfg target ↔
                Step M cfg
                  (⟨M.initial, target.tape⟩ :
                    DLBA.Cfg Γ Λ n)
              rw [htargetEq]
            rw [hmset]
            exact hinit n target.tape
          exact add_le_add hpred (le_refl 1)
        _ = 2 := by norm_num
    · let predecessorCfg
          (old : List (RowCell I Γ Λ)) : DLBA.Cfg Γ Λ n :=
        if hstep :
            (certifiedRowSystem M embed).RowStep old (configRow target) then
          Classical.choose
            (config_predecessor_of_not_raw M embed target
              ((certifiedRowSystem_rowStep_iff M embed _ _).1 hstep)
              (by
                intro hraw
                rcases hraw with ⟨input, hinput⟩
                apply hrawTarget
                subst old
                exact ⟨input,
                  (certifiedRowSystem_rowStep_iff M embed _ _).1 hstep⟩))
        else target
      have predecessorCfg_spec (old : List (RowCell I Γ Λ))
          (hstep :
            (certifiedRowSystem M embed).RowStep old (configRow target)) :
          Step M (predecessorCfg old) target ∧
            old = configRow (predecessorCfg old) := by
        dsimp only [predecessorCfg]
        rw [dif_pos hstep]
        exact Classical.choose_spec
          (config_predecessor_of_not_raw M embed target
            ((certifiedRowSystem_rowStep_iff M embed _ _).1 hstep)
            (by
              intro hraw
              rcases hraw with ⟨input, hinput⟩
              apply hrawTarget
              subst old
              exact ⟨input,
                (certifiedRowSystem_rowStep_iff M embed _ _).1 hstep⟩))
      calc
        Set.encard
            {old | (certifiedRowSystem M embed).RowStep
              old (configRow target)} ≤
            Set.encard {cfg | Step M cfg target} := by
          apply Set.encard_le_encard_of_injOn (f := predecessorCfg)
          · intro old hold
            exact (predecessorCfg_spec old hold).1
          · intro left hleft right hright heq
            rw [(predecessorCfg_spec left hleft).2,
              (predecessorCfg_spec right hright).2, heq]
        _ ≤ 2 := hin n target

/-- The two row-degree estimates combine. -/
public theorem certifiedRowSystem_rowDirectedDegreeAtMostTwo
    [DecidableEq I] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) (embed : I → Γ)
    (hinjective : Function.Injective embed)
    (hdegree : M.ConfigurationDegreeAtMostTwo)
    (hinit : M.InitialConfigurationIndegreeAtMostOne) :
    CertifiedRowSystem.RowDirectedDegreeAtMost 2
      (certifiedRowSystem M embed) :=
  ⟨certifiedRowSystem_rowOutdegreeAtMostTwo M embed hdegree.1,
    certifiedRowSystem_rowIndegreeAtMostTwo M embed hinjective hdegree.2 hinit⟩

end CertifiedRows

end LBA

end
