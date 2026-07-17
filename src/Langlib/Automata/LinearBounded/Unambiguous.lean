module

public import Langlib.Automata.LinearBounded.Functional

@[expose]
public section

/-!
# Unambiguous linearly bounded automata

An accepting computation is data, not a proof of a reachability proposition.  This matters
because proof irrelevance would otherwise identify every two proofs of `LBA.Reaches`.

The generic `RelationalRun` API records finite vertex sequences and proves that their mere
existence is equivalent to reflexive-transitive reachability.  Its terminal-final theorem is a
reusable graph fact: a right-unique relation has at most one accepting path once final vertices
have no outgoing edges.

The LBA-facing API is more precise than a configuration path.  `LBA.Machine.Move` retains the
chosen transition triple `(state, symbol, direction)` as data, and `MovePath` retains every move.
Thus two different moves which happen to produce the same configuration at a clamped boundary
remain different computation branches.  Conversely, identical moves are elements of a `Set`, so
their membership proofs are propositionally irrelevant and do not create spurious branches.

`AcceptingRun` uses **first-final normalization**: a recorded run stops as soon as its first
accepting configuration is reached.  Consequently an accepting state may have outgoing machine
transitions without creating several accepting prefixes along one trajectory.  Loops remain
visible in `MovePath` data, including their number of traversals.

The public language class uses the repository's canonical endmarker model.  In particular, the
empty word is processed by an actual run on `⊢⊣`; there is no external empty-word bit in
`is_ULBA`.

## Main results

* `RelationalRun.nonempty_pathTo_iff_reaches`
* `RelationalRun.nonempty_stopAtFinal_acceptingRun_iff`
* `RelationalRun.acceptingRun_subsingleton`
* `LBA.Machine.nonempty_movePathTo_iff_reaches`
* `LBA.Machine.nonempty_acceptingRun_iff`
* `LBA.Machine.acceptingRun_subsingleton_of_functional`
* `DLBA_subset_ULBA` and `ULBA_subset_LBA`
* `lba_eq_dlba_iff_lba_subset_ulba_and_ulba_subset_dlba`
-/

universe u

/-! ## Finite relational run data -/

namespace RelationalRun

variable {V : Type u}

/-- A concrete finite relational run from `source`.  `visits = []` is the zero-step run. -/
structure PathData (edge : V → V → Prop) (source : V) where
  visits : List V
  isChain : List.IsChain edge (source :: visits)

/-- A positive-length relational path. -/
structure GenuinePathData (edge : V → V → Prop) (source : V) where
  toPath : PathData edge source
  genuine : toPath.visits ≠ []

namespace PathData

variable {edge : V → V → Prop} {source : V}

/-- The final vertex of a concrete relational run. -/
def endpoint (path : PathData edge source) : V :=
  (source :: path.visits).getLast (by simp)

@[simp]
theorem endpoint_nil (h : List.IsChain edge [source]) :
    endpoint ({ visits := [], isChain := h } : PathData edge source) = source := rfl

@[simp]
theorem endpoint_cons (next : V) (rest : List V)
    (h : List.IsChain edge (source :: next :: rest)) :
    endpoint ({ visits := next :: rest, isChain := h } : PathData edge source) =
      (next :: rest).getLast (by simp) := by
  simp [endpoint]

/-- Forgetting the concrete vertex sequence gives reflexive-transitive reachability. -/
theorem reaches (path : PathData edge source) :
    Relation.ReflTransGen edge source path.endpoint := by
  exact List.relationReflTransGen_of_exists_isChain_cons
    path.visits path.isChain rfl

@[ext]
theorem ext (left right : PathData edge source)
    (hvisits : left.visits = right.visits) : left = right := by
  cases left
  cases right
  simp_all

end PathData

/-- A concrete relational run with a specified endpoint. -/
abbrev PathTo (edge : V → V → Prop) (source target : V) :=
  {path : PathData edge source // path.endpoint = target}

/-- Concrete path data is a faithful Type-valued presentation of reflexive-transitive
reachability.  `Nonempty` keeps mere existence in `Prop`, while its witness contains the actual
vertex sequence. -/
theorem nonempty_pathTo_iff_reaches {edge : V → V → Prop} {source target : V} :
    Nonempty (PathTo edge source target) ↔ Relation.ReflTransGen edge source target := by
  constructor
  · rintro ⟨⟨path, hend⟩⟩
    simpa [hend] using path.reaches
  · intro hreach
    obtain ⟨visits, hchain, hlast⟩ :=
      List.exists_isChain_cons_of_relationReflTransGen hreach
    refine ⟨⟨⟨visits, hchain⟩, ?_⟩⟩
    simpa [PathData.endpoint] using hlast

/-- A concrete relational run whose endpoint satisfies `final`. -/
structure AcceptingRun (edge : V → V → Prop) (final : V → Prop) (source : V) where
  path : PathData edge source
  isFinal : final path.endpoint

namespace AcceptingRun

variable {edge : V → V → Prop} {final : V → Prop} {source : V}

@[ext]
theorem ext (left right : AcceptingRun edge final source)
    (hvisits : left.path.visits = right.path.visits) : left = right := by
  cases left with
  | mk leftPath leftFinal =>
    cases right with
    | mk rightPath rightFinal =>
      have hpath : leftPath = rightPath := PathData.ext _ _ hvisits
      subst rightPath
      rfl

/-- Forgetting the concrete sequence gives ordinary existential acceptance. -/
theorem accepts (run : AcceptingRun edge final source) :
    ∃ target, Relation.ReflTransGen edge source target ∧ final target :=
  ⟨run.path.endpoint, run.path.reaches, run.isFinal⟩

end AcceptingRun

/-- Suppress every edge whose source is already final. -/
def StopAtFinal (edge : V → V → Prop) (final : V → Prop) : V → V → Prop :=
  fun source target ↦ ¬ final source ∧ edge source target

/-- Every final vertex is terminal for `edge`. -/
def FinalsTerminal (edge : V → V → Prop) (final : V → Prop) : Prop :=
  ∀ ⦃source target⦄, final source → ¬ edge source target

theorem stopAtFinal_finalsTerminal (edge : V → V → Prop) (final : V → Prop) :
    FinalsTerminal (StopAtFinal edge final) final := by
  intro source target hfinal hstep
  exact hstep.1 hfinal

theorem stopAtFinal_rightUnique {edge : V → V → Prop} {final : V → Prop}
    (hunique : Relator.RightUnique edge) :
    Relator.RightUnique (StopAtFinal edge final) := by
  intro source left right hleft hright
  exact hunique hleft.2 hright.2

private theorem uniqueVisitLists
    {edge : V → V → Prop} {final : V → Prop}
    (hunique : Relator.RightUnique edge) (hterminal : FinalsTerminal edge final) :
    ∀ (source : V) (left right : List V),
      List.IsChain edge (source :: left) →
      List.IsChain edge (source :: right) →
      final ((source :: left).getLast (by simp)) →
      final ((source :: right).getLast (by simp)) →
      left = right := by
  intro source left
  induction left generalizing source with
  | nil =>
      intro right hleft hright hleftFinal hrightFinal
      cases right with
      | nil => rfl
      | cons next rest =>
          have hstep : edge source next := (List.isChain_cons_cons.mp hright).1
          have hfinal : final source := by simpa using hleftFinal
          exact False.elim (hterminal hfinal hstep)
  | cons next rest ih =>
      intro right hleft hright hleftFinal hrightFinal
      cases right with
      | nil =>
          have hstep : edge source next := (List.isChain_cons_cons.mp hleft).1
          have hfinal : final source := by simpa using hrightFinal
          exact False.elim (hterminal hfinal hstep)
      | cons next' rest' =>
          have hleftStep : edge source next := (List.isChain_cons_cons.mp hleft).1
          have hrightStep : edge source next' := (List.isChain_cons_cons.mp hright).1
          have hnext : next = next' := hunique hleftStep hrightStep
          subst next'
          have hleftTail : List.IsChain edge (next :: rest) :=
            (List.isChain_cons_cons.mp hleft).2
          have hrightTail : List.IsChain edge (next :: rest') :=
            (List.isChain_cons_cons.mp hright).2
          have hleftFinal' : final ((next :: rest).getLast (by simp)) := by
            simpa using hleftFinal
          have hrightFinal' : final ((next :: rest').getLast (by simp)) := by
            simpa using hrightFinal
          have hrest : rest = rest' :=
            ih next rest' hleftTail hrightTail hleftFinal' hrightFinal'
          simp [hrest]

/-- A right-unique relation with terminal finals has at most one concrete accepting run.  This
remains true in the presence of nonfinal loops. -/
theorem acceptingRun_subsingleton
    {edge : V → V → Prop} {final : V → Prop}
    (hunique : Relator.RightUnique edge) (hterminal : FinalsTerminal edge final)
    (source : V) : Subsingleton (AcceptingRun edge final source) := by
  constructor
  intro left right
  apply AcceptingRun.ext
  exact uniqueVisitLists hunique hterminal source left.path.visits right.path.visits
    left.path.isChain right.path.isChain left.isFinal right.isFinal

/-- Stopping a right-unique relation at its first final vertex gives at most one accepting run. -/
theorem stopAtFinal_acceptingRun_subsingleton
    {edge : V → V → Prop} {final : V → Prop}
    (hunique : Relator.RightUnique edge) (source : V) :
    Subsingleton (AcceptingRun (StopAtFinal edge final) final source) :=
  acceptingRun_subsingleton (stopAtFinal_rightUnique hunique)
    (stopAtFinal_finalsTerminal edge final) source

private theorem existsFirstFinalRun
    {edge : V → V → Prop} {final : V → Prop} :
    ∀ (source : V) (visits : List V),
      List.IsChain edge (source :: visits) →
      final ((source :: visits).getLast (by simp)) →
      Nonempty (AcceptingRun (StopAtFinal edge final) final source) := by
  classical
  intro source visits
  induction visits generalizing source with
  | nil =>
      intro hchain hfinal
      exact ⟨⟨⟨[], by simp⟩, by simpa using hfinal⟩⟩
  | cons next rest ih =>
      intro hchain hfinal
      by_cases hsource : final source
      · exact ⟨⟨⟨[], by simp⟩, by simpa using hsource⟩⟩
      · have hstep : edge source next := (List.isChain_cons_cons.mp hchain).1
        have htail : List.IsChain edge (next :: rest) :=
          (List.isChain_cons_cons.mp hchain).2
        have htailFinal : final ((next :: rest).getLast (by simp)) := by
          simpa using hfinal
        obtain ⟨tailRun⟩ := ih next htail htailFinal
        refine ⟨⟨⟨next :: tailRun.path.visits, ?_⟩, ?_⟩⟩
        · exact List.IsChain.cons_cons ⟨hsource, hstep⟩ tailRun.path.isChain
        · simpa [PathData.endpoint] using tailRun.isFinal

/-- Reachability of a final vertex is equivalent to a concrete accepting run after first-final
normalization. -/
theorem nonempty_stopAtFinal_acceptingRun_iff :
    Nonempty (AcceptingRun (StopAtFinal edge final) final source) ↔
      ∃ target, Relation.ReflTransGen edge source target ∧ final target := by
  constructor
  · rintro ⟨run⟩
    exact ⟨run.path.endpoint,
      run.path.reaches.mono (fun _ _ h ↦ h.2), run.isFinal⟩
  · rintro ⟨target, hreach, hfinal⟩
    obtain ⟨visits, hchain, hlast⟩ :=
      List.exists_isChain_cons_of_relationReflTransGen hreach
    apply existsFirstFinalRun source visits hchain
    simpa [hlast] using hfinal

end RelationalRun

/-! ## Labeled LBA computations -/

namespace LBA

variable {Γ Λ : Type*}

/-- One enabled operational move, retaining the transition triple as data. -/
structure Machine.Move {n : ℕ} (M : Machine Γ Λ) (source : DLBA.Cfg Γ Λ n) where
  nextState : Λ
  write : Γ
  dir : DLBA.Dir
  enabled : (nextState, write, dir) ∈ M.transition source.state source.tape.read

namespace Machine.Move

variable {M : Machine Γ Λ} {n : ℕ} {source : DLBA.Cfg Γ Λ n}

/-- The successor configuration determined by an enabled move. -/
def target (move : M.Move source) : DLBA.Cfg Γ Λ n :=
  ⟨move.nextState, (source.tape.write move.write).moveHead move.dir⟩

/-- An enabled move witnesses the existing propositional step relation. -/
theorem step (move : M.Move source) : Step M source move.target :=
  ⟨move.nextState, move.write, move.dir, move.enabled, rfl⟩

/-- A functional transition set contains at most one move record. -/
theorem eq_of_functional (hfunctional : M.Functional)
    (left right : M.Move source) : left = right := by
  cases left with
  | mk leftState leftWrite leftDir leftEnabled =>
    cases right with
    | mk rightState rightWrite rightDir rightEnabled =>
      have hmove : (leftState, leftWrite, leftDir) =
          (rightState, rightWrite, rightDir) :=
        hfunctional source.state source.tape.read leftEnabled rightEnabled
      cases hmove
      rfl

end Machine.Move

/-- A concrete finite sequence of enabled moves. -/
inductive Machine.MovePath {n : ℕ} (M : Machine Γ Λ) : DLBA.Cfg Γ Λ n → Type _
  | nil (source : DLBA.Cfg Γ Λ n) : M.MovePath source
  | cons {source : DLBA.Cfg Γ Λ n} (move : M.Move source)
      (rest : M.MovePath move.target) : M.MovePath source

namespace Machine.MovePath

variable {M : Machine Γ Λ} {n : ℕ} {source : DLBA.Cfg Γ Λ n}

/-- Endpoint after executing all recorded moves. -/
def endpoint : {source : DLBA.Cfg Γ Λ n} → M.MovePath source → DLBA.Cfg Γ Λ n
  | source, .nil _ => source
  | _, .cons _ rest => endpoint rest

@[simp]
theorem endpoint_nil : endpoint (.nil source : M.MovePath source) = source := rfl

@[simp]
theorem endpoint_cons (move : M.Move source) (rest : M.MovePath move.target) :
    endpoint (.cons move rest) = rest.endpoint := rfl

/-- Forgetting move labels gives reflexive-transitive configuration reachability. -/
theorem reaches : ∀ {source : DLBA.Cfg Γ Λ n} (path : M.MovePath source),
    Reaches M source path.endpoint
  | _, .nil _ => .refl
  | _, .cons move rest => .head move.step (reaches rest)

/-- Every recorded move starts strictly before the first accepting configuration. -/
def BeforeFinal : ∀ {source : DLBA.Cfg Γ Λ n}, M.MovePath source → Prop
  | _, .nil _ => True
  | source, .cons _ rest => M.accept source.state ≠ true ∧ rest.BeforeFinal

@[simp]
theorem beforeFinal_nil : BeforeFinal (.nil source : M.MovePath source) := trivial

@[simp]
theorem beforeFinal_cons (move : M.Move source) (rest : M.MovePath move.target) :
    BeforeFinal (.cons move rest) ↔
      M.accept source.state ≠ true ∧ rest.BeforeFinal := Iff.rfl

end Machine.MovePath

/-- A labeled move path stopped at its first accepting configuration. -/
structure Machine.AcceptingRun {n : ℕ} (M : Machine Γ Λ)
    (source : DLBA.Cfg Γ Λ n) where
  path : M.MovePath source
  beforeFinal : path.BeforeFinal
  isFinal : M.accept path.endpoint.state = true

namespace Machine

variable {M : Machine Γ Λ} {n : ℕ} {source target : DLBA.Cfg Γ Λ n}

/-- One labeled move with a specified target. -/
abbrev MoveTo (M : Machine Γ Λ) (source target : DLBA.Cfg Γ Λ n) :=
  {move : M.Move source // move.target = target}

/-- Move records are a Type-valued presentation of the propositional `Step` relation. -/
theorem nonempty_moveTo_iff_step :
    Nonempty (M.MoveTo source target) ↔ Step M source target := by
  constructor
  · rintro ⟨⟨move, rfl⟩⟩
    exact move.step
  · rintro ⟨nextState, write, dir, enabled, rfl⟩
    exact ⟨⟨⟨nextState, write, dir, enabled⟩, rfl⟩⟩

/-- A labeled move path with a specified endpoint. -/
abbrev MovePathTo (M : Machine Γ Λ) (source target : DLBA.Cfg Γ Λ n) :=
  {path : M.MovePath source // path.endpoint = target}

/-- Labeled finite paths exist exactly for ordinary reflexive-transitive reachability. -/
theorem nonempty_movePathTo_iff_reaches :
    Nonempty (M.MovePathTo source target) ↔ Reaches M source target := by
  constructor
  · rintro ⟨⟨path, rfl⟩⟩
    exact path.reaches
  · intro hreach
    induction hreach using Relation.ReflTransGen.head_induction_on with
    | refl => exact ⟨⟨.nil target, rfl⟩⟩
    | @head start middle hstep _ ih =>
        obtain ⟨⟨move, hmoveTarget⟩⟩ :=
          (nonempty_moveTo_iff_step (M := M)).2 hstep
        obtain ⟨⟨rest, hrestTarget⟩⟩ := ih
        subst middle
        exact ⟨⟨.cons move rest, hrestTarget⟩⟩

private theorem exists_acceptingRun_of_path :
    ∀ {source : DLBA.Cfg Γ Λ n} (path : M.MovePath source),
      M.accept path.endpoint.state = true → Nonempty (M.AcceptingRun source)
  | source, .nil _, hfinal => ⟨⟨.nil source, trivial, hfinal⟩⟩
  | source, .cons move rest, hfinal => by
      by_cases hsource : M.accept source.state = true
      · exact ⟨⟨.nil source, trivial, hsource⟩⟩
      · obtain ⟨tailRun⟩ := exists_acceptingRun_of_path rest hfinal
        exact ⟨⟨.cons move tailRun.path, ⟨hsource, tailRun.beforeFinal⟩, tailRun.isFinal⟩⟩

/-- First-final labeled accepting-run existence exactly matches existing LBA acceptance. -/
theorem nonempty_acceptingRun_iff :
    Nonempty (M.AcceptingRun source) ↔ Accepts M source := by
  constructor
  · rintro ⟨run⟩
    exact ⟨run.path.endpoint, run.path.reaches, run.isFinal⟩
  · rintro ⟨target, hreach, hfinal⟩
    obtain ⟨⟨path, htarget⟩⟩ :=
      (nonempty_movePathTo_iff_reaches (M := M)).2 hreach
    subst target
    exact exists_acceptingRun_of_path path hfinal

private theorem movePaths_eq_of_functional (hfunctional : M.Functional) :
    ∀ {source : DLBA.Cfg Γ Λ n} (left right : M.MovePath source),
      left.BeforeFinal → right.BeforeFinal →
      M.accept left.endpoint.state = true →
      M.accept right.endpoint.state = true →
      left = right := by
  intro source left
  induction left with
  | nil source =>
      intro right hleftBefore hrightBefore hleftFinal hrightFinal
      cases right with
      | nil => rfl
      | cons move rest =>
          exact False.elim (hrightBefore.1 (by simpa using hleftFinal))
  | @cons source move rest ih =>
      intro right hleftBefore hrightBefore hleftFinal hrightFinal
      cases right with
      | nil =>
          exact False.elim (hleftBefore.1 (by simpa using hrightFinal))
      | cons rightMove rightRest =>
          have hmove : move = rightMove := move.eq_of_functional hfunctional rightMove
          subst rightMove
          have hrest : rest = rightRest :=
            ih rightRest hleftBefore.2 hrightBefore.2 hleftFinal hrightFinal
          subst rightRest
          rfl

/-- A functional transition table has at most one labeled first-final accepting run. -/
theorem acceptingRun_subsingleton_of_functional
    (hfunctional : M.Functional) (source : DLBA.Cfg Γ Λ n) :
    Subsingleton (M.AcceptingRun source) := by
  constructor
  intro left right
  cases left with
  | mk leftPath leftBefore leftFinal =>
    cases right with
    | mk rightPath rightBefore rightFinal =>
      have hpath : leftPath = rightPath :=
        movePaths_eq_of_functional hfunctional leftPath rightPath
          leftBefore rightBefore leftFinal rightFinal
      subst rightPath
      rfl

/-- Unambiguity from one bounded configuration. -/
def UnambiguousFrom (M : Machine Γ Λ) {n : ℕ} (source : DLBA.Cfg Γ Λ n) : Prop :=
  Subsingleton (M.AcceptingRun source)

/-- A strong machine invariant, useful for deterministic presentations. -/
def Unambiguous (M : Machine Γ Λ) : Prop :=
  ∀ (n : ℕ) (source : DLBA.Cfg Γ Λ n), M.UnambiguousFrom source

/-- Input-level unambiguity for the canonical endmarker presentation, including `ε`. -/
def UnambiguousEnd {T : Type*} (M : Machine (EndAlpha T Γ) Λ) : Prop :=
  ∀ word : List T, M.UnambiguousFrom (initCfgEnd M word)

/-- Functional machines are unambiguous from every bounded configuration. -/
theorem unambiguous_of_functional (hfunctional : M.Functional) : M.Unambiguous := by
  intro width cfg
  exact acceptingRun_subsingleton_of_functional hfunctional cfg

/-- The endmarker simulator preserves functionality. -/
theorem simMachine_functional {T : Type*}
    (M : Machine (Option (T ⊕ Γ)) Λ) (hfunctional : M.Functional) (acceptEmpty : Bool) :
    (simMachine M acceptEmpty).Functional := by
  intro state symbol left hleft right hright
  cases state with
  | start =>
      cases symbol with
      | inl interior => simp [simMachine, simTransition] at hleft
      | inr marker =>
          cases marker <;> simp [simMachine, simTransition] at hleft hright
          exact hleft.trans hright.symm
  | entry =>
      cases symbol with
      | inl interior =>
          simp [simMachine, simTransition] at hleft hright
          exact hleft.trans hright.symm
      | inr marker =>
          cases marker <;> simp [simMachine, simTransition] at hleft hright
          split at hleft <;> simp_all
  | run state =>
      cases symbol with
      | inl interior =>
          simp only [simMachine, simTransition, Set.mem_setOf_eq] at hleft hright
          obtain ⟨leftMove, hleftMove, rfl⟩ := hleft
          obtain ⟨rightMove, hrightMove, rfl⟩ := hright
          have hmove : leftMove = rightMove :=
            hfunctional state interior hleftMove hrightMove
          subst rightMove
          rfl
      | inr marker =>
          cases marker <;> simp [simMachine, simTransition] at hleft hright
          · exact hleft.trans hright.symm
          · exact hleft.trans hright.symm
  | acc =>
      cases symbol <;> simp [simMachine, simTransition] at hleft
  | rej =>
      cases symbol <;> simp [simMachine, simTransition] at hleft

end Machine

end LBA

/-! ## The canonical unambiguous-LBA language class -/

/-- A language is recognized by an unambiguous LBA when a finite canonical endmarker machine
recognizes it and has at most one labeled first-final accepting run on every input. -/
@[expose]
def is_ULBA {T : Type} [Fintype T] [DecidableEq T] (L : Language T) : Prop :=
  ∃ (Γ Λ : Type) (_ : Fintype Γ) (_ : Fintype Λ)
    (_ : DecidableEq Γ) (_ : DecidableEq Λ)
    (M : LBA.Machine (LBA.EndAlpha T Γ) Λ),
    M.UnambiguousEnd ∧ LBA.LanguageEnd M = L

/-- The class of languages recognized by unambiguous LBAs. -/
@[expose]
def ULBA {T : Type} [Fintype T] [DecidableEq T] : Set (Language T) := setOf is_ULBA

/-- Every deterministic LBA language has an unambiguous canonical endmarker presentation. -/
theorem is_DLBA_imp_is_ULBA {T : Type} [Fintype T] [DecidableEq T]
    {L : Language T} (hL : is_DLBA L) : is_ULBA L := by
  rcases hL with
    ⟨Γ, Λ, hΓ, hΛ, hdecΓ, hdecΛ, acceptEmpty, M, hlanguage⟩
  letI := hΓ
  letI := hΛ
  letI := hdecΓ
  letI := hdecΛ
  let markerFree : LBA.Machine (Option (T ⊕ Γ)) (Option Λ) := DLBA.toLBA' M
  let endmarked := LBA.simMachine markerFree acceptEmpty
  have hmarkerFree : markerFree.Functional := DLBA.toLBA'_functional M
  have hendmarked : endmarked.Functional :=
    markerFree.simMachine_functional hmarkerFree acceptEmpty
  refine ⟨Γ, LBA.SimState (Option Λ), inferInstance, inferInstance,
    inferInstance, inferInstance, endmarked, ?_, ?_⟩
  · intro word
    exact endmarked.unambiguous_of_functional hendmarked _ _
  · dsimp only [endmarked, markerFree]
    rw [LBA.language_simMachine_eq, ← hlanguage]
    have key :
        DLBA.LanguageViaEmbed M (fun t ↦ some (Sum.inl t)) =
          LBA.LanguageViaEmbed (DLBA.toLBA' M) (fun t ↦ some (Sum.inl t)) :=
      dlba_language_eq_lba_language M (fun t ↦ some (Sum.inl t))
    funext word
    apply propext
    simp only [DLBA.LanguageRecognized, LBA.LanguageRecognized, key]

/-- Forgetting the run-subsingleton field gives an ordinary LBA presentation verbatim. -/
theorem is_ULBA_imp_is_LBA {T : Type} [Fintype T] [DecidableEq T]
    {L : Language T} (hL : is_ULBA L) : is_LBA L := by
  rcases hL with ⟨Γ, Λ, hΓ, hΛ, hdecΓ, hdecΛ, M, _hunambiguous, hlanguage⟩
  exact ⟨Γ, Λ, hΓ, hΛ, hdecΓ, hdecΛ, M, hlanguage⟩

/-- Deterministic LBA languages are unambiguous LBA languages. -/
theorem DLBA_subset_ULBA {T : Type} [Fintype T] [DecidableEq T] :
    (DLBA : Set (Language T)) ⊆ ULBA := by
  intro L hL
  exact is_DLBA_imp_is_ULBA hL

/-- Unambiguous LBA languages are LBA languages. -/
theorem ULBA_subset_LBA {T : Type} [Fintype T] [DecidableEq T] :
    (ULBA : Set (Language T)) ⊆ LBA := by
  intro L hL
  exact is_ULBA_imp_is_LBA hL

/-- Exact order-theoretic factorization of the LBA-versus-DLBA equality through `ULBA`. -/
theorem lba_eq_dlba_iff_lba_subset_ulba_and_ulba_subset_dlba
    {T : Type} [Fintype T] [DecidableEq T] :
    (LBA : Set (Language T)) = DLBA ↔
      (LBA : Set (Language T)) ⊆ ULBA ∧
        (ULBA : Set (Language T)) ⊆ DLBA := by
  constructor
  · intro heq
    constructor
    · rw [heq]
      exact DLBA_subset_ULBA
    · rw [← heq]
      exact ULBA_subset_LBA
  · rintro ⟨hlbaUlba, hulbaDlba⟩
    apply Set.Subset.antisymm
    · exact Set.Subset.trans hlbaUlba hulbaDlba
    · exact DLBA_subset_LBA

/-- If the nondeterministic class is already known to be unambiguous, the remaining equality
question is exactly whether every unambiguous LBA can be determinized. -/
theorem lba_eq_dlba_iff_ulba_subset_dlba_of_lba_subset_ulba
    {T : Type} [Fintype T] [DecidableEq T]
    (hlbaUlba : (LBA : Set (Language T)) ⊆ ULBA) :
    (LBA : Set (Language T)) = DLBA ↔ (ULBA : Set (Language T)) ⊆ DLBA := by
  rw [lba_eq_dlba_iff_lba_subset_ulba_and_ulba_subset_dlba]
  simp [hlbaUlba]
