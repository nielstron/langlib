import Mathlib
import Langlib.Classes.RecursivelyEnumerable.Definition
import Langlib.Grammars.Unrestricted.Toolbox
import Langlib.Automata.Turing.Equivalence.TMToGrammar.Construction

/-! # Helper Lemmas for TM → Grammar Construction

This file contains the detailed helper lemmas needed to prove the correctness
of the `tmToGrammar` construction.

## Encoding TM configurations as sentential forms

A TM0 configuration `⟨q, tape⟩` together with an "original input track" is encoded
as a sentential form of the grammar. The encoding represents a finite window of the
tape as a sequence of `cell`/`headCell` nonterminals flanked by boundary markers.
-/

open Turing TMtoGrammarNT

variable {T : Type} [DecidableEq T] [Fintype T]
         {Λ : Type} [Inhabited Λ] [DecidableEq Λ] [Fintype Λ]

/-- A "two-track tape segment" encodes a finite portion of the TM tape
along with the original input at each position.

`leftCells` are the cells to the left of the head (in order from left to right).
`headState` is the TM state at the head position.
`headOrig` is the original input at the head position.
`headCur` is the current tape content at the head position.
`rightCells` are the cells to the right of the head (in order from left to right).

Each cell is a pair `(original, current)`. -/
structure TwoTrackConfig where
  leftCells  : List (Option T × Option T)
  headState  : Λ
  headOrig   : Option T
  headCur    : Option T
  rightCells : List (Option T × Option T)

/-- Encode a `TwoTrackConfig` as a sentential form of the grammar. -/
def encodeTwoTrack (cfg : @TwoTrackConfig T Λ) :
    List (symbol T (TMtoGrammarNT T Λ)) :=
  [.nonterminal leftBound] ++
  (cfg.leftCells.map fun ⟨orig, cur⟩ => .nonterminal (cell orig cur)) ++
  [.nonterminal (headCell cfg.headState cfg.headOrig cfg.headCur)] ++
  (cfg.rightCells.map fun ⟨orig, cur⟩ => .nonterminal (cell orig cur)) ++
  [.nonterminal rightBound]

/-- The initial two-track configuration for input `w`. The head is at the leftmost
position (or on blank for empty input). -/
def initTwoTrack (w : List T) : @TwoTrackConfig T Λ :=
  match w with
  | [] => ⟨[], default, none, none, []⟩
  | t :: ts => ⟨[], default, some t, some t,
                ts.map fun t' => (some t', some t')⟩

/-! ### Phase 1: Generation

The grammar derives the encoding of the initial configuration from [start]:
1. S → leftBound · genMore · rightBound
2. Repeatedly: genMore → genMore · cell(tᵢ) (adding cells right-to-left)
3. genMore → headCell(q₀, t₁) (or headCell(q₀, none, none) for empty input)
-/

/-
The grammar can derive the encoding of the initial configuration from [start].
-/
theorem generation_derives (M : Turing.TM0.Machine (Option T) Λ) (w : List T) :
    grammar_derives (tmToGrammar T Λ M)
      [.nonterminal start]
      (encodeTwoTrack (initTwoTrack w : @TwoTrackConfig T Λ)) := by
  revert w M;
  intro M w
  by_cases hw : w = [];
  · subst hw;
    -- Apply the first rule of the generationRules to get [leftBound, genMore, rightBound].
    have h1 : grammar_transforms (tmToGrammar T Λ M) [symbol.nonterminal start] [symbol.nonterminal leftBound, symbol.nonterminal genMore, symbol.nonterminal rightBound] := by
      use ⟨ [ ], start, [ ], [ symbol.nonterminal leftBound, symbol.nonterminal genMore, symbol.nonterminal rightBound ] ⟩ ; simp +decide [ tmToGrammar ] ;
      exact ⟨ Or.inl <| List.mem_cons_self, [ ], [ ], rfl, rfl ⟩;
    exact .single h1 |> Relation.ReflTransGen.trans <| .single <| by
      use ⟨[], genMore, [.nonterminal rightBound], [.nonterminal (headCell (default : Λ) none none), .nonterminal rightBound]⟩; simp +decide [ encodeTwoTrack, initTwoTrack ] ;
      exact ⟨ by unfold tmToGrammar; simp +decide [ generationRules ], [ symbol.nonterminal leftBound ], [], by simp, by simp ⟩;
  · -- Apply the induction hypothesis to the tail of the list.
    have h_ind : ∀ (ts : List T), grammar_derives (tmToGrammar T Λ M) [symbol.nonterminal start] ([symbol.nonterminal leftBound, symbol.nonterminal genMore] ++ ts.map (fun t => symbol.nonterminal (cell (some t) (some t))) ++ [symbol.nonterminal rightBound]) := by
      intro ts
      induction' ts with t ts ih
      generalize_proofs at *; (
      apply Relation.ReflTransGen.single
      simp [generationRules];
      use ⟨[], start, [], [symbol.nonterminal leftBound, symbol.nonterminal genMore, symbol.nonterminal rightBound]⟩
      simp [tmToGrammar, generationRules];
      exact ⟨ [ ], [ ], rfl, rfl ⟩);
      apply grammar_deri_of_deri_tran ih
      generalize_proofs at *; (
      use ⟨[], genMore, [], [.nonterminal genMore, .nonterminal (cell (some t) (some t))]⟩; simp +decide [ tmToGrammar ] ; (
      exact ⟨ Or.inl <| by unfold generationRules; aesop, [ symbol.nonterminal leftBound ], ( List.map ( fun t => symbol.nonterminal ( cell ( some t ) ( some t ) ) ) ts ++ [ symbol.nonterminal rightBound ] ), by aesop ⟩ ;););
    rcases w with ( _ | ⟨ t, ts ⟩ ) <;> simp_all +decide [ encodeTwoTrack, initTwoTrack ];
    have h_genMore : grammar_transforms (tmToGrammar T Λ M) (symbol.nonterminal leftBound :: symbol.nonterminal genMore :: (List.map (fun t => symbol.nonterminal (cell (some t) (some t))) ts ++ [symbol.nonterminal rightBound])) (symbol.nonterminal leftBound :: symbol.nonterminal (headCell default (some t) (some t)) :: (List.map (fun t => symbol.nonterminal (cell (some t) (some t))) ts ++ [symbol.nonterminal rightBound])) := by
      use ⟨[], genMore, [], [.nonterminal (headCell default (some t) (some t))]⟩; simp +decide [ tmToGrammar ] ; (
      exact ⟨ Or.inl <| by unfold generationRules; aesop, [ symbol.nonterminal leftBound ], List.map ( fun t => symbol.nonterminal ( cell ( some t ) ( some t ) ) ) ts ++ [ symbol.nonterminal rightBound ], rfl, rfl ⟩);
    exact Relation.ReflTransGen.trans ( h_ind ts ) ( Relation.ReflTransGen.single h_genMore )

/-! ### Phase 3: Cleanup

After the TM halts, the grammar converts all nonterminals to terminals. -/

/-- Encode the "halted" configuration: all cells converted to haltCells. -/
def encodeHalted (originals : List (Option T)) :
    List (symbol T (TMtoGrammarNT T Λ)) :=
  [.nonterminal leftBound] ++
  (originals.map fun orig => .nonterminal (haltCell orig)) ++
  [.nonterminal rightBound]

/-- Extract the original input from a list of originals (keep only `some` values). -/
def extractInput (originals : List (Option T)) : List T :=
  originals.filterMap id

/-
From a halted encoding, the grammar can derive the original input terminals.

Convert a bare list of haltCells to terminals (no boundary markers).
-/
theorem haltCells_to_terminals (M : Turing.TM0.Machine (Option T) Λ)
    (originals : List (Option T)) :
    grammar_derives (tmToGrammar T Λ M)
      (originals.map fun orig => symbol.nonterminal (haltCell orig))
      ((originals.filterMap id).map symbol.terminal) := by
  induction' originals with orig originals ih;
  · constructor;
  · cases' orig with t t <;> simp_all +decide [ List.filterMap_cons ];
    · -- Apply the rule for `haltCell none` to remove the nonterminal.
      have h_halt_none : grammar_transforms (tmToGrammar T Λ M) (symbol.nonterminal (haltCell none) :: List.map (fun orig => symbol.nonterminal (haltCell orig)) originals) (List.map (fun orig => symbol.nonterminal (haltCell orig)) originals) := by
        use ⟨[], haltCell none, [], []⟩;
        simp +decide [ tmToGrammar, generationRules, simulationRules, cleanupRules ];
        exact ⟨ [ ], _, rfl, rfl ⟩;
      exact grammar_deri_of_tran_deri h_halt_none ih;
    · convert grammar_deri_of_deri_deri _ _ using 1;
      exact [ symbol.terminal t ] ++ List.map ( fun orig => symbol.nonterminal ( haltCell orig ) ) originals;
      · convert grammar_deri_of_tran _ using 1;
        use ⟨[], haltCell (some t), [], [symbol.terminal t]⟩; simp +decide [ tmToGrammar ] ;
        refine' ⟨ _, [ ], _, rfl, rfl ⟩;
        unfold cleanupRules; aesop;
      · convert grammar_deri_with_prefix _ ih using 1

/-
Remove LB from [LB] ++ haltCells ++ [RB], producing haltCells ++ [RB] (non-empty case)
    or [] (empty case).
-/
theorem remove_boundaries (M : Turing.TM0.Machine (Option T) Λ)
    (originals : List (Option T)) :
    grammar_derives (tmToGrammar T Λ M)
      (encodeHalted originals)
      (originals.map fun orig => symbol.nonterminal (haltCell orig)) := by
  unfold encodeHalted;
  induction' originals with orig rest ih;
  · -- Apply the rule that removes the leftBound and rightBound.
    apply Relation.ReflTransGen.single
    use ⟨[], leftBound, [.nonterminal rightBound], []⟩
    simp [cleanupRules];
    unfold tmToGrammar; simp +decide [ cleanupRules ] ;
  · have h_transform : grammar_transforms (tmToGrammar T Λ M) ([symbol.nonterminal leftBound] ++ [symbol.nonterminal (haltCell orig)] ++ List.map (fun orig => symbol.nonterminal (haltCell orig)) rest ++ [symbol.nonterminal rightBound]) ([symbol.nonterminal (haltCell orig)] ++ List.map (fun orig => symbol.nonterminal (haltCell orig)) rest ++ [symbol.nonterminal rightBound]) := by
      -- Apply the rule that removes the left bound.
      use ⟨[], leftBound, [symbol.nonterminal (haltCell orig)], [symbol.nonterminal (haltCell orig)]⟩;
      simp +decide [ tmToGrammar ];
      refine' ⟨ _, [ ], List.map ( fun orig => symbol.nonterminal ( haltCell orig ) ) rest ++ [ symbol.nonterminal rightBound ], rfl, rfl ⟩;
      unfold cleanupRules; simp +decide [ allOptT ] ;
      cases orig <;> tauto;
    have h_transform : grammar_transforms (tmToGrammar T Λ M) ([symbol.nonterminal (haltCell orig)] ++ List.map (fun orig => symbol.nonterminal (haltCell orig)) rest ++ [symbol.nonterminal rightBound]) ([symbol.nonterminal (haltCell orig)] ++ List.map (fun orig => symbol.nonterminal (haltCell orig)) rest) := by
      use ⟨[.nonterminal (haltCell (List.getLast! (orig :: rest)))] , rightBound, [], [.nonterminal (haltCell (List.getLast! (orig :: rest)))]⟩; simp_all +decide [ List.getLast! ] ;
      constructor;
      · apply_rules [ List.mem_append_right ];
        simp +decide [ allOptT ];
        cases h : ( orig :: rest ).getLast ( by simp +decide ) <;> aesop;
      · induction rest using List.reverseRecOn <;> simp_all +decide [ List.getLast ];
        · exact ⟨ [ ], [ ], rfl, rfl ⟩;
        · exact ⟨ [ symbol.nonterminal ( haltCell orig ) ] ++ List.map ( fun orig => symbol.nonterminal ( haltCell orig ) ) ‹_›, [ ], by simp +decide ⟩;
    exact Relation.ReflTransGen.single ‹_› |> Relation.ReflTransGen.trans <| Relation.ReflTransGen.single ‹_›

theorem cleanup_derives (M : Turing.TM0.Machine (Option T) Λ)
    (originals : List (Option T)) :
    grammar_derives (tmToGrammar T Λ M)
      (encodeHalted originals)
      (List.map symbol.terminal (extractInput originals)) := by
  exact grammar_deri_of_deri_deri (remove_boundaries M originals) (haltCells_to_terminals M originals)

/-! ### Rule membership helpers -/

/-- A rule from the generation rules is in the grammar. -/

theorem gen_rule_mem (M : Turing.TM0.Machine (Option T) Λ)
    (r : grule T (TMtoGrammarNT T Λ)) (hr : r ∈ generationRules T Λ M) :
    r ∈ (tmToGrammar T Λ M).rules := by
  simp only [tmToGrammar]
  exact List.mem_append_left _ (List.mem_append_left _ hr)

/-- A rule from the simulation rules is in the grammar. -/

theorem sim_rule_mem (M : Turing.TM0.Machine (Option T) Λ)
    (r : grule T (TMtoGrammarNT T Λ)) (hr : r ∈ simulationRules T Λ M) :
    r ∈ (tmToGrammar T Λ M).rules := by
  simp only [tmToGrammar]
  exact List.mem_append_left _ (List.mem_append_right _ hr)

/-- A rule from the cleanup rules is in the grammar. -/

theorem cleanup_rule_mem (M : Turing.TM0.Machine (Option T) Λ)
    (r : grule T (TMtoGrammarNT T Λ)) (hr : r ∈ cleanupRules T Λ M) :
    r ∈ (tmToGrammar T Λ M).rules := by
  simp only [tmToGrammar]
  exact List.mem_append_right _ hr

/-- Get the originals from a TwoTrackConfig. -/
def twoTrackOriginals (cfg : @TwoTrackConfig T Λ) : List (Option T) :=
  (cfg.leftCells.map Prod.fst) ++ [cfg.headOrig] ++ (cfg.rightCells.map Prod.fst)

/-! ### Phase 2: Simulation

The simulation phase shows that each TM0 step can be mirrored by a grammar
derivation step on the encoded sentential form. -/

/-- Compute the next TwoTrackConfig after one TM0 step. Returns `none` if the TM halts. -/
noncomputable def stepTwoTrack
    (M : Turing.TM0.Machine (Option T) Λ)
    (cfg : @TwoTrackConfig T Λ) : Option (@TwoTrackConfig T Λ) :=
  match M cfg.headState cfg.headCur with
  | none => none
  | some (q', Turing.TM0.Stmt.write γ') =>
    some ⟨cfg.leftCells, q', cfg.headOrig, γ', cfg.rightCells⟩
  | some (q', Turing.TM0.Stmt.move Dir.right) =>
    match cfg.rightCells with
    | [] => some ⟨cfg.leftCells ++ [(cfg.headOrig, cfg.headCur)], q', none, none, []⟩
    | (ro, rc) :: rest =>
      some ⟨cfg.leftCells ++ [(cfg.headOrig, cfg.headCur)], q', ro, rc, rest⟩
  | some (q', Turing.TM0.Stmt.move Dir.left) =>
    match cfg.leftCells.reverse with
    | [] => some ⟨[], q', none, none, (cfg.headOrig, cfg.headCur) :: cfg.rightCells⟩
    | (lo, lc) :: rest =>
      some ⟨rest.reverse, q', lo, lc,
            (cfg.headOrig, cfg.headCur) :: cfg.rightCells⟩

/-
The original input (modulo blank extension) is preserved by `stepTwoTrack`.
-/
theorem stepTwoTrack_preserves_extractInput
    (M : Turing.TM0.Machine (Option T) Λ)
    (cfg cfg' : @TwoTrackConfig T Λ)
    (hstep : stepTwoTrack M cfg = some cfg') :
    extractInput (twoTrackOriginals cfg') = extractInput (twoTrackOriginals cfg) := by
  unfold stepTwoTrack at hstep;
  rcases h : M cfg.headState cfg.headCur with ( _ | ⟨ q', _ ⟩ ) <;> simp_all +decide;
  rename_i h';
  rcases h' with ( _ | Dir ) <;> norm_num at *;
  · cases ‹Dir› <;> cases h' : cfg.rightCells <;> cases h'' : cfg.leftCells.reverse <;> simp_all +decide [ twoTrackOriginals ];
    all_goals subst_vars; simp +decide [ extractInput ] ;
    · cases cfg.headOrig <;> rfl;
    · cases ‹Option T × Option T› ; aesop;
  · unfold twoTrackOriginals; aesop;

/-
Any element of `Option T` is in `allOptT`.
-/
theorem mem_allOptT (x : Option T) : x ∈ allOptT T := by
  unfold allOptT; cases x <;> simp +decide [ * ] ;

/-
Any element of `Λ` is in `allΛ`.
-/
theorem mem_allΛ (q : Λ) : q ∈ allΛ Λ := by
  convert Finset.mem_toList.mpr ( Finset.mem_univ q ) using 1

/-
Simulation: write case.
-/
theorem sim_write
    (M : Turing.TM0.Machine (Option T) Λ)
    (q q' : Λ) (orig γ γ' : Option T)
    (hM : M q γ = some (q', Turing.TM0.Stmt.write γ'))
    (prefix_ suffix_ : List (symbol T (TMtoGrammarNT T Λ))) :
    grammar_transforms (tmToGrammar T Λ M)
      (prefix_ ++ [.nonterminal (headCell q orig γ)] ++ suffix_)
      (prefix_ ++ [.nonterminal (headCell q' orig γ')] ++ suffix_) := by
  refine' ⟨ ⟨ [], headCell q orig γ, [], [ symbol.nonterminal ( headCell q' orig γ' ) ] ⟩, _, _ ⟩;
  · apply sim_rule_mem;
    unfold simulationRules;
    rw [ List.mem_flatMap ];
    use q;
    rw [ List.mem_flatMap ];
    use mem_allΛ q, γ, mem_allOptT γ, by
      rw [ hM ];
      exact List.mem_map.mpr ⟨ orig, mem_allOptT orig, rfl ⟩;
  · grind

/-
Simulation: move right with neighbor.
-/
theorem sim_move_right
    (M : Turing.TM0.Machine (Option T) Λ)
    (q q' : Λ) (orig γ orig' γ' : Option T)
    (hM : M q γ = some (q', Turing.TM0.Stmt.move Dir.right))
    (prefix_ suffix_ : List (symbol T (TMtoGrammarNT T Λ))) :
    grammar_transforms (tmToGrammar T Λ M)
      (prefix_ ++ [.nonterminal (headCell q orig γ), .nonterminal (cell orig' γ')] ++ suffix_)
      (prefix_ ++ [.nonterminal (cell orig γ), .nonterminal (headCell q' orig' γ')] ++ suffix_) := by
  constructor;
  constructor;
  apply sim_rule_mem;
  convert List.mem_flatMap.mpr _;
  exact ⟨ [ ], headCell q orig γ, [ symbol.nonterminal ( cell orig' γ' ) ], [ symbol.nonterminal ( cell orig γ ), symbol.nonterminal ( headCell q' orig' γ' ) ] ⟩;
  · refine' ⟨ q, _, _ ⟩ <;> simp +decide [ hM, allΛ ];
    use γ; simp [hM];
    exact ⟨ mem_allOptT γ, mem_allOptT orig, mem_allOptT orig', mem_allOptT γ' ⟩;
  · grind

/-
Simulation: move right at right boundary.
-/
theorem sim_move_right_boundary
    (M : Turing.TM0.Machine (Option T) Λ)
    (q q' : Λ) (orig γ : Option T)
    (hM : M q γ = some (q', Turing.TM0.Stmt.move Dir.right))
    (prefix_ suffix_ : List (symbol T (TMtoGrammarNT T Λ))) :
    grammar_transforms (tmToGrammar T Λ M)
      (prefix_ ++ [.nonterminal (headCell q orig γ), .nonterminal rightBound] ++ suffix_)
      (prefix_ ++ [.nonterminal (cell orig γ), .nonterminal (headCell q' none none), .nonterminal rightBound] ++ suffix_) := by
  use (⟨[], headCell q orig γ, [symbol.nonterminal rightBound], [symbol.nonterminal (cell orig γ), symbol.nonterminal (headCell q' none none), symbol.nonterminal rightBound]⟩);
  constructor;
  · apply sim_rule_mem;
    unfold simulationRules; simp +decide [ hM ] ;
    use q, by
      exact?, γ, by
      exact?
    generalize_proofs at *;
    rw [ hM ] ; simp +decide [ allOptT ] ;
    cases orig <;> aesop;
  · grind

/-
Simulation: move left with neighbor.
-/
theorem sim_move_left
    (M : Turing.TM0.Machine (Option T) Λ)
    (q q' : Λ) (orig γ orig'' γ'' : Option T)
    (hM : M q γ = some (q', Turing.TM0.Stmt.move Dir.left))
    (prefix_ suffix_ : List (symbol T (TMtoGrammarNT T Λ))) :
    grammar_transforms (tmToGrammar T Λ M)
      (prefix_ ++ [.nonterminal (cell orig'' γ''), .nonterminal (headCell q orig γ)] ++ suffix_)
      (prefix_ ++ [.nonterminal (headCell q' orig'' γ''), .nonterminal (cell orig γ)] ++ suffix_) := by
  refine' ⟨ _, _, _, _ ⟩;
  exact ⟨ [ .nonterminal ( cell orig'' γ'' ) ], headCell q orig γ, [ ], [ .nonterminal ( headCell q' orig'' γ'' ), .nonterminal ( cell orig γ ) ] ⟩;
  convert sim_rule_mem M _ _ using 1;
  all_goals norm_num [ simulationRules ];
  use q, mem_allΛ q, γ, mem_allOptT γ;
  all_goals norm_num [ hM ];
  exact ⟨ orig, mem_allOptT orig, orig'', mem_allOptT orig'', γ'', mem_allOptT γ'', by tauto ⟩;
  exacts [ prefix_, ⟨ suffix_, rfl, rfl ⟩ ]

/-
Simulation: move left at left boundary.
-/
theorem sim_move_left_boundary
    (M : Turing.TM0.Machine (Option T) Λ)
    (q q' : Λ) (orig γ : Option T)
    (hM : M q γ = some (q', Turing.TM0.Stmt.move Dir.left))
    (prefix_ suffix_ : List (symbol T (TMtoGrammarNT T Λ))) :
    grammar_transforms (tmToGrammar T Λ M)
      (prefix_ ++ [.nonterminal leftBound, .nonterminal (headCell q orig γ)] ++ suffix_)
      (prefix_ ++ [.nonterminal leftBound, .nonterminal (headCell q' none none), .nonterminal (cell orig γ)] ++ suffix_) := by
  refine' ⟨ _, _, _, _ ⟩;
  exact ⟨ [ .nonterminal leftBound ], headCell q orig γ, [ ], [ .nonterminal leftBound, .nonterminal ( headCell q' none none ), .nonterminal ( cell orig γ ) ] ⟩;
  any_goals exact prefix_;
  · apply sim_rule_mem;
    unfold simulationRules;
    simp +decide [ List.mem_flatMap, List.mem_append, List.mem_map, hM ];
    refine' ⟨ q, _, γ, _, _ ⟩ <;> simp +decide [ hM, allΛ, allOptT ];
    · cases γ <;> tauto;
    · cases orig <;> aesop;
  · grind +revert

/-
One step of `stepTwoTrack` can be simulated by the grammar.
-/
theorem simulation_one_step
    (M : Turing.TM0.Machine (Option T) Λ)
    (cfg cfg' : @TwoTrackConfig T Λ)
    (hstep : stepTwoTrack M cfg = some cfg') :
    grammar_derives (tmToGrammar T Λ M)
      (encodeTwoTrack cfg)
      (encodeTwoTrack cfg') := by
  unfold stepTwoTrack at hstep;
  rcases h : M cfg.headState cfg.headCur with ( _ | ⟨ q', _ ⟩ ) <;> simp_all +decide;
  cases' ‹TM0.Stmt ( Option T ) › with γ' hγ';
  · cases' γ' with γ' hγ';
    · rcases h' : cfg.leftCells.reverse with ( _ | ⟨ lo, lc ⟩ ) <;> simp_all +decide [ encodeTwoTrack ];
      · convert grammar_deri_of_tran _ using 1;
        convert sim_move_left_boundary M cfg.headState q' cfg.headOrig cfg.headCur h [ ] ( List.map ( fun x => symbol.nonterminal ( cell x.1 x.2 ) ) cfg.rightCells ++ [ symbol.nonterminal rightBound ] ) using 1 ; aesop ( simp_config := { singlePass := true } ) ;
      · convert grammar_deri_of_tran _ using 1;
        convert sim_move_left M cfg.headState q' cfg.headOrig cfg.headCur lo.1 lo.2 h ( [ symbol.nonterminal leftBound ] ++ List.map ( fun x => symbol.nonterminal ( cell x.1 x.2 ) ) lc.reverse ) ( List.map ( fun x => symbol.nonterminal ( cell x.1 x.2 ) ) cfg.rightCells ++ [ symbol.nonterminal rightBound ] ) using 1;
        · simp +decide [ List.map_reverse ];
        · aesop;
    · rcases cfg with ⟨ leftCells, headState, headOrig, headCur, rightCells ⟩ ; rcases rightCells with ( _ | ⟨ ro, rc ⟩ ) <;> simp_all +decide ;
      · convert grammar_deri_of_tran _ using 1;
        convert sim_move_right_boundary M headState q' headOrig headCur h _ _ using 1;
        rotate_left;
        rotate_left;
        exact [ symbol.nonterminal leftBound ] ++ List.map ( fun x => symbol.nonterminal ( cell x.1 x.2 ) ) leftCells;
        exact [ ];
        · unfold encodeTwoTrack; aesop;
        · unfold encodeTwoTrack; aesop;
      · refine' Relation.ReflTransGen.single _;
        convert sim_move_right M headState q' headOrig headCur ro.1 ro.2 h ( [ .nonterminal leftBound ] ++ leftCells.map ( fun x => .nonterminal ( cell x.1 x.2 ) ) ) ( rc.map ( fun x => .nonterminal ( cell x.1 x.2 ) ) ++ [ .nonterminal rightBound ] ) using 1;
        · unfold encodeTwoTrack; aesop;
        · unfold encodeTwoTrack; aesop;
  · unfold encodeTwoTrack at *;
    apply Relation.ReflTransGen.single;
    convert sim_write M cfg.headState q' cfg.headOrig cfg.headCur hγ' h _ _ using 1;
    rotate_left;
    rotate_left;
    exact [ symbol.nonterminal leftBound ] ++ List.map ( fun x => symbol.nonterminal ( cell x.1 x.2 ) ) cfg.leftCells;
    exact List.map ( fun x => symbol.nonterminal ( cell x.1 x.2 ) ) cfg.rightCells ++ [ symbol.nonterminal rightBound ];
    · simp +decide [ List.append_assoc ];
    · grind

/-
Multiple steps of `stepTwoTrack` can be simulated by the grammar.
-/
theorem simulation_multi_step
    (M : Turing.TM0.Machine (Option T) Λ)
    (cfg : @TwoTrackConfig T Λ)
    (n : ℕ)
    (cfg' : @TwoTrackConfig T Λ)
    (hsteps : (Nat.iterate (fun c => c >>= stepTwoTrack M) n (some cfg)) = some cfg') :
    grammar_derives (tmToGrammar T Λ M)
      (encodeTwoTrack cfg)
      (encodeTwoTrack cfg') := by
  induction' n with n ih generalizing cfg cfg' <;> simp_all +decide [ Function.iterate_succ_apply' ];
  · exact?;
  · cases h' : ( fun c : Option ( TwoTrackConfig ) => c.bind ( stepTwoTrack M ) ) ^[ n ] ( some cfg ) <;> simp_all +decide [ Function.iterate_succ_apply' ];
    exact grammar_deri_of_deri_deri ( ih _ _ h' ) ( simulation_one_step _ _ _ hsteps )

/-! ### Phase 2.5: Halt conversion

When the TM halts, convert the two-track encoding to the halted encoding. -/

/-
Step 1 of halt-to-halted: convert headCell to haltCell when TM halts.
-/
theorem halt_headCell_to_haltCell
    (M : Turing.TM0.Machine (Option T) Λ)
    (q : Λ) (orig cur : Option T)
    (h_halts : M q cur = none)
    (prefix_ suffix_ : List (symbol T (TMtoGrammarNT T Λ))) :
    grammar_transforms (tmToGrammar T Λ M)
      (prefix_ ++ [.nonterminal (headCell q orig cur)] ++ suffix_)
      (prefix_ ++ [.nonterminal (haltCell orig)] ++ suffix_) := by
  refine' ⟨ _, _, prefix_, suffix_, _, _ ⟩ <;> norm_num [ h_halts ];
  exact ⟨ [ ], headCell q orig cur, [ ], [ symbol.nonterminal ( haltCell orig ) ] ⟩
  all_goals generalize_proofs at *; simp_all +decide [ tmToGrammar ] ;
  unfold cleanupRules; simp +decide [ h_halts ] ;
  refine' Or.inr ( Or.inr ⟨ q, _, cur, _, _ ⟩ );
  · exact Finset.mem_toList.mpr ( Finset.mem_univ q );
  · cases cur <;> [ exact List.mem_cons_self; exact List.mem_cons_of_mem _ ( List.mem_map.mpr ⟨ _, Finset.mem_toList.mpr ( Finset.mem_univ _ ), rfl ⟩ ) ] ;
  · cases orig <;> simp +decide [ h_halts ];
    · exact List.mem_cons_self;
    · exact List.mem_cons_of_mem _ ( List.mem_map.mpr ⟨ _, Finset.mem_toList.mpr ( Finset.mem_univ _ ), rfl ⟩ )

/-
Step 2: propagate halt to right cells.
-/
theorem propagate_halt_right
    (M : Turing.TM0.Machine (Option T) Λ)
    (cells : List (Option T × Option T))
    (orig : Option T)
    (prefix_ suffix_ : List (symbol T (TMtoGrammarNT T Λ))) :
    grammar_derives (tmToGrammar T Λ M)
      (prefix_ ++ [.nonterminal (haltCell orig)] ++
        cells.map (fun ⟨o, c⟩ => .nonterminal (cell o c)) ++ suffix_)
      (prefix_ ++ [.nonterminal (haltCell orig)] ++
        cells.map (fun ⟨o, _⟩ => .nonterminal (haltCell o)) ++ suffix_) := by
  induction' cells with cells_head cells_tail ih generalizing orig prefix_ suffix_ <;> simp_all +decide [ List.map ];
  · constructor;
  · -- Apply theتحديث rule to replace `cell cells_head.1 cells_head.2` with `haltCell cells_head.1`.
    have h_replace : grammar_transforms (tmToGrammar T Λ M) (prefix_ ++ [symbol.nonterminal (haltCell orig), symbol.nonterminal (cell cells_head.1 cells_head.2)] ++ (List.map (fun x => symbol.nonterminal (cell x.1 x.2)) cells_tail ++ suffix_)) (prefix_ ++ [symbol.nonterminal (haltCell orig), symbol.nonterminal (haltCell cells_head.1)] ++ (List.map (fun x => symbol.nonterminal (cell x.1 x.2)) cells_tail ++ suffix_)) := by
      refine' ⟨ ⟨ [ ], haltCell orig, [ .nonterminal ( cell cells_head.1 cells_head.2 ) ], [ .nonterminal ( haltCell orig ), .nonterminal ( haltCell cells_head.1 ) ] ⟩, _, _ ⟩ <;> simp +decide [ tmToGrammar ];
      · unfold cleanupRules; simp +decide [ List.mem_append, List.mem_map ] ;
        refine' Or.inr <| Or.inr <| Or.inr ⟨ _, _, _ ⟩;
        · exact List.mem_cons.mpr ( by cases orig <;> simp +decide );
        · -- Since `cells_head.1` is an `Option T`, it must be either `none` or `some t` for some `t`. In either case, it is included in the list `allOptT`.
          cases' cells_head.1 with t ht;
          · exact List.mem_cons_self;
          · exact List.mem_cons_of_mem _ ( List.mem_map.mpr ⟨ t, Finset.mem_toList.mpr ( Finset.mem_univ _ ), rfl ⟩ );
        · exact List.mem_cons.mpr ( by cases cells_head.2 <;> simp +decide );
      · exact ⟨ prefix_, List.map ( fun x => symbol.nonterminal ( cell x.1 x.2 ) ) cells_tail ++ suffix_, rfl, rfl ⟩;
    specialize ih cells_head.1 ( prefix_ ++ [ symbol.nonterminal ( haltCell orig ) ] ) suffix_ ; simp_all +decide [ Relation.ReflTransGen ] ; (
    exact Relation.ReflTransGen.trans ( Relation.ReflTransGen.single h_replace ) ih;)

/-
Single left-propagation step: convert one cell immediately left of a haltCell.
-/
theorem propagate_halt_left_one_step
    (M : Turing.TM0.Machine (Option T) Λ)
    (o c : Option T) (anchor_orig : Option T)
    (prefix_ suffix_ : List (symbol T (TMtoGrammarNT T Λ))) :
    grammar_transforms (tmToGrammar T Λ M)
      (prefix_ ++ [.nonterminal (cell o c), .nonterminal (haltCell anchor_orig)] ++ suffix_)
      (prefix_ ++ [.nonterminal (haltCell o), .nonterminal (haltCell anchor_orig)] ++ suffix_) := by
  unfold tmToGrammar
  generalize_proofs at *;
  use ⟨ [ .nonterminal ( cell o c ) ], haltCell anchor_orig, [ ], [ .nonterminal ( haltCell o ), .nonterminal ( haltCell anchor_orig ) ] ⟩
  simp [cleanupRules];
  refine' ⟨ Or.inr <| Or.inr <| Or.inr _, _, _, rfl, rfl ⟩;
  -- Since `allOptT` is defined as `none :: (Finset.univ.val.toList.map some)`, any element of `Option T` is either `none` or `some t` for some `t` in `T`.
  have h_allOptT : ∀ x : Option T, x ∈ none :: (Finset.univ.val.toList.map some) := by
    rintro ( _ | x ) <;> simp +decide;
  exact ⟨ h_allOptT anchor_orig, h_allOptT o, h_allOptT c ⟩

/-
Step 3: propagate halt to left cells, using a haltCell anchor on the right.

The cleanup rule `cell(o'', c'') · haltCell(orig) → haltCell(o'') · haltCell(orig)` converts
cells from right to left, using the rightmost haltCell as an anchor.
-/
theorem propagate_halt_left
    (M : Turing.TM0.Machine (Option T) Λ)
    (cells : List (Option T × Option T))
    (anchor_orig : Option T)
    (prefix_ suffix_ : List (symbol T (TMtoGrammarNT T Λ))) :
    grammar_derives (tmToGrammar T Λ M)
      (prefix_ ++ cells.map (fun ⟨o, c⟩ => .nonterminal (cell o c)) ++
        [.nonterminal (haltCell anchor_orig)] ++ suffix_)
      (prefix_ ++ cells.map (fun ⟨o, _⟩ => .nonterminal (haltCell o)) ++
        [.nonterminal (haltCell anchor_orig)] ++ suffix_) := by
  -- By the definition of `grammar_transforms`, we can apply the cleanup rule `cell(o'', c'') · haltCell(orig) → haltCell(o'') · haltCell(orig)` to each cell in `cells`.
  have h_transforms : ∀ (o c : Option T) (anchor_orig : Option T) (prefix_ suffix_ : List (symbol T (TMtoGrammarNT T Λ))),
    grammar_transforms (tmToGrammar T Λ M)
      (prefix_ ++ [symbol.nonterminal (cell o c), symbol.nonterminal (haltCell anchor_orig)] ++ suffix_)
      (prefix_ ++ [symbol.nonterminal (haltCell o), symbol.nonterminal (haltCell anchor_orig)] ++ suffix_) := by
        grind +suggestions;
  induction' cells using List.reverseRecOn with cells ih generalizing anchor_orig prefix_ suffix_;
  · constructor;
  · rename_i h;
    specialize h_transforms ih.1 ih.2 anchor_orig ( prefix_ ++ List.map ( fun x => match x with | ( o, c ) => symbol.nonterminal ( cell o c ) ) cells ) ( suffix_ ) ; simp_all +decide [ List.map_append ] ;
    exact Relation.ReflTransGen.trans ( Relation.ReflTransGen.single h_transforms ) ( h _ _ _ ) |> fun h => by simpa [ List.append_assoc ] using h;

/-
From a halting two-track config, the grammar derives the halted encoding.

Composition of halt_headCell_to_haltCell, propagate_halt_right, and propagate_halt_left.
-/
theorem halt_to_halted
    (M : Turing.TM0.Machine (Option T) Λ)
    (cfg : @TwoTrackConfig T Λ)
    (h_halts : M cfg.headState cfg.headCur = none) :
    grammar_derives (tmToGrammar T Λ M)
      (encodeTwoTrack cfg)
      (encodeHalted (twoTrackOriginals cfg)) := by
  convert grammar_deri_of_deri_deri _ _ using 1;
  exact ( [ .nonterminal leftBound ] ++ cfg.leftCells.map ( fun ⟨ o, c ⟩ => .nonterminal ( cell o c ) ) ++ [ .nonterminal ( haltCell cfg.headOrig ) ] ++ cfg.rightCells.map ( fun ⟨ o, c ⟩ => .nonterminal ( cell o c ) ) ++ [ .nonterminal rightBound ] );
  · convert grammar_deri_of_tran_deri ( halt_headCell_to_haltCell M cfg.headState cfg.headOrig cfg.headCur h_halts _ _ ) _ using 1;
    rotate_left;
    exact [ symbol.nonterminal leftBound ] ++ cfg.leftCells.map ( fun ⟨ o, c ⟩ => symbol.nonterminal ( cell o c ) );
    exact cfg.rightCells.map ( fun ⟨ o, c ⟩ => symbol.nonterminal ( cell o c ) ) ++ [ symbol.nonterminal rightBound ];
    · simp +decide [ List.append_assoc ];
      constructor;
    · unfold encodeTwoTrack; aesop;
  · convert grammar_deri_of_deri_deri _ _ using 1;
    exact [ symbol.nonterminal leftBound ] ++ cfg.leftCells.map ( fun ⟨ o, c ⟩ => symbol.nonterminal ( cell o c ) ) ++ [ symbol.nonterminal ( haltCell cfg.headOrig ) ] ++ cfg.rightCells.map ( fun ⟨ o, c ⟩ => symbol.nonterminal ( haltCell o ) ) ++ [ symbol.nonterminal rightBound ];
    · convert propagate_halt_right M cfg.rightCells cfg.headOrig _ _ using 1;
    · convert grammar_deri_of_deri_deri _ _ using 1;
      exact [ symbol.nonterminal leftBound ] ++ cfg.leftCells.map ( fun ⟨ o, c ⟩ => symbol.nonterminal ( haltCell o ) ) ++ [ symbol.nonterminal ( haltCell cfg.headOrig ) ] ++ cfg.rightCells.map ( fun ⟨ o, c ⟩ => symbol.nonterminal ( haltCell o ) ) ++ [ symbol.nonterminal rightBound ];
      · convert propagate_halt_left M cfg.leftCells cfg.headOrig [ symbol.nonterminal leftBound ] ( cfg.rightCells.map ( fun ⟨ o, c ⟩ => symbol.nonterminal ( haltCell o ) ) ++ [ symbol.nonterminal rightBound ] ) using 1;
        · grind;
        · simp +decide [ List.append_assoc ];
      · convert grammar_deri_self using 1;
        unfold encodeHalted twoTrackOriginals; aesop;

/-! ### Composing all phases -/

/-
The original input stored in the initial two-track config for word `w` is exactly `w.map some`.
That is, `extractInput (twoTrackOriginals (initTwoTrack w)) = w`.
-/
theorem extractInput_initTwoTrack (w : List T) :
    extractInput (twoTrackOriginals (initTwoTrack w : @TwoTrackConfig T Λ)) = w := by
  unfold twoTrackOriginals extractInput initTwoTrack; induction w <;> aesop;

/-! ### Correspondence between TM0.Cfg and TwoTrackConfig -/

/-- A TwoTrackConfig corresponds to a TM0.Cfg if the head state, head symbol,
and tape contents match (with the tape being blank beyond the TwoTrackConfig window). -/
structure TMCorresponds
    (tc : @TwoTrackConfig T Λ)
    (tmCfg : Turing.TM0.Cfg (Option T) Λ) : Prop where
  state_eq : tc.headState = tmCfg.q
  head_eq : tc.headCur = tmCfg.Tape.head
  left_match : ∀ i,
    (tc.leftCells.reverse.map Prod.snd).getI i = tmCfg.Tape.left.nth i
  right_match : ∀ i,
    (tc.rightCells.map Prod.snd).getI i = tmCfg.Tape.right.nth i

/-
The initial TwoTrackConfig corresponds to the initial TM0 config.
-/
theorem initCorresponds (w : List T) :
    TMCorresponds
      (initTwoTrack w : @TwoTrackConfig T Λ)
      (Turing.TM0.init (w.map Option.some)) := by
  constructor;
  · cases w <;> aesop;
  · cases w <;> aesop;
  · cases w <;> aesop;
  · unfold initTwoTrack TM0.init; aesop;

/-
If tc corresponds to tmCfg and the TM halts, then stepTwoTrack also returns none.
-/
theorem corresponds_step_none
    (M : Turing.TM0.Machine (Option T) Λ)
    (tc : @TwoTrackConfig T Λ)
    (tmCfg : Turing.TM0.Cfg (Option T) Λ)
    (hcorr : TMCorresponds tc tmCfg)
    (hhalt : Turing.TM0.step M tmCfg = none) :
    stepTwoTrack M tc = none := by
  -- By definition of `stepTwoTrack`, we know that if `M tc.headState tc.headCur = none`, then `stepTwoTrack M tc = none`.
  simp [stepTwoTrack, hhalt];
  rw [ show M tc.headState tc.headCur = none from ?_ ];
  rw [ hcorr.state_eq, hcorr.head_eq ];
  convert hhalt using 1;
  unfold TM0.step; aesop;

/-
If tc corresponds to tmCfg and the TM steps to tmCfg', then stepTwoTrack
produces a tc' that corresponds to tmCfg'.
-/
theorem corresponds_step_some
    (M : Turing.TM0.Machine (Option T) Λ)
    (tc : @TwoTrackConfig T Λ)
    (tmCfg tmCfg' : Turing.TM0.Cfg (Option T) Λ)
    (hcorr : TMCorresponds tc tmCfg)
    (hstep : Turing.TM0.step M tmCfg = some tmCfg') :
    ∃ tc', stepTwoTrack M tc = some tc' ∧ TMCorresponds tc' tmCfg' := by
  unfold TM0.step at hstep;
  rcases hcorr with ⟨ hq, hhead, hleft, hright ⟩;
  obtain ⟨q', a, hq', ha⟩ : ∃ q' a, M tc.headState tc.headCur = some (q', a) ∧ tmCfg' = (match a with | TM0.Stmt.move d => { q := q', Tape := Tape.move d tmCfg.Tape } | TM0.Stmt.write a => { q := q', Tape := Tape.write a tmCfg.Tape }) := by
                                                                                                                                                                                                cases h : M tc.headState tc.headCur <;> aesop;
  rcases a with ( _ | _ ) <;> simp_all +decide [ TMCorresponds ];
  · rename_i d; unfold stepTwoTrack; rcases d with ( _ | _ ) <;> simp_all +decide [ TMCorresponds ] ;
    · rcases h : tc.leftCells.reverse with ( _ | ⟨ ⟨ lo, lc ⟩, rest ⟩ ) <;> simp_all +decide [ TMCorresponds ];
      · constructor <;> simp_all +decide [ TMCorresponds ];
        · specialize hleft 0 ; aesop;
        · intro i; specialize hleft ( i + 1 ) ; aesop;
        · intro i; rcases i with ( _ | i ) <;> simp_all +decide [ Tape.move ] ;
      · constructor <;> simp_all +decide [ TMCorresponds ];
        · specialize hleft 0 ; aesop;
        · intro i; specialize hleft ( i + 1 ) ; aesop;
        · intro i; rcases i with ( _ | i ) <;> simp_all +decide [ Tape.move ] ;
    · rcases tc with ⟨ leftCells, headState, headOrig, headCur, rightCells ⟩ ; rcases rightCells with ( _ | ⟨ ro, rc ⟩ ) <;> simp_all +decide [ TMCorresponds ] ;
      · constructor <;> simp +decide [ *, Tape.move ];
        · specialize hright 0 ; aesop;
        · intro i; rcases i with ( _ | i ) <;> simp_all +decide [ List.getI ] ;
        · intro i; specialize hright ( i + 1 ) ; aesop;
      · constructor <;> simp_all +decide [ Tape.move ];
        · specialize hright 0 ; aesop;
        · intro i; rcases i with ( _ | i ) <;> simp_all +decide [ List.getI ] ;
        · intro i; specialize hright ( i + 1 ) ; aesop;
  · unfold stepTwoTrack;
    simp_all +decide [ TMCorresponds ];
    constructor <;> aesop

/-! ### Main Correctness Theorems -/

/-
If tc corresponds to tmCfg, and the TM reaches a halting config from tmCfg,
then the grammar can derive from tc's encoding to some halting tc_final's encoding,
with the original track preserved.
-/
theorem sim_reaches_halts
    (M : Turing.TM0.Machine (Option T) Λ)
    (tc : @TwoTrackConfig T Λ) (tmCfg : Turing.TM0.Cfg (Option T) Λ)
    (hcorr : TMCorresponds tc tmCfg)
    (tmCfg_halt : Turing.TM0.Cfg (Option T) Λ)
    (hreaches : Turing.Reaches (Turing.TM0.step M) tmCfg tmCfg_halt)
    (hhalt : Turing.TM0.step M tmCfg_halt = none) :
    ∃ tc_final : @TwoTrackConfig T Λ,
      grammar_derives (tmToGrammar T Λ M) (encodeTwoTrack tc) (encodeTwoTrack tc_final) ∧
      M tc_final.headState tc_final.headCur = none ∧
      extractInput (twoTrackOriginals tc_final) = extractInput (twoTrackOriginals tc) := by
  by_contra h_contra;
  apply_mod_cast absurd _ h_contra;
  have h_ind : ∀ tmCfg tmCfg', Reaches (TM0.step M) tmCfg tmCfg' → ∀ tc, TMCorresponds tc tmCfg → ∃ tc', grammar_derives (tmToGrammar T Λ M) (encodeTwoTrack tc) (encodeTwoTrack tc') ∧ TMCorresponds tc' tmCfg' ∧ extractInput (twoTrackOriginals tc') = extractInput (twoTrackOriginals tc) := by
    intros tmCfg tmCfg' hreaches tc hcorr
    induction' hreaches with tmCfg_mid hmid hreaches_mid ih generalizing tc
    <;> simp_all +decide [ Reaches ];
    · exact ⟨ tc, by tauto, by tauto, by tauto ⟩;
    · obtain ⟨ tc', h₁, h₂, h₃ ⟩ := ‹∀ ( tc : TwoTrackConfig ), TMCorresponds tc tmCfg → ∃ tc', grammar_derives ( tmToGrammar T Λ M ) ( encodeTwoTrack tc ) ( encodeTwoTrack tc' ) ∧ TMCorresponds tc' tmCfg_mid ∧ extractInput ( twoTrackOriginals tc' ) = extractInput ( twoTrackOriginals tc ) › tc hcorr;
      obtain ⟨ tc'', h₄, h₅ ⟩ := corresponds_step_some M tc' tmCfg_mid hmid h₂ ih;
      exact ⟨ tc'', grammar_deri_of_deri_deri h₁ ( simulation_one_step M tc' tc'' h₄ ), h₅, stepTwoTrack_preserves_extractInput M tc' tc'' h₄ ▸ h₃ ⟩;
  obtain ⟨tc_final, htc_final⟩ := h_ind tmCfg tmCfg_halt hreaches tc hcorr;
  refine' ⟨ tc_final, htc_final.1, _, htc_final.2.2 ⟩;
  convert hhalt using 1;
  simp +decide [ TM0.step, htc_final.2.1.state_eq, htc_final.2.1.head_eq ]

/-
If the TM halts on input `w`, then the grammar derives `w`.
-/
theorem tmToGrammar_generates_of_halts
    (M : Turing.TM0.Machine (Option T) Λ) (w : List T)
    (h : (Turing.TM0.eval M (w.map Option.some)).Dom) :
    grammar_generates (tmToGrammar T Λ M) w := by
  -- By definition of `TM0.eval`, there exists a configuration `cfg` such that `cfg` is reachable from the initial configuration and `cfg` halts.
  obtain ⟨cfg, hcfg⟩ : ∃ cfg : Turing.TM0.Cfg (Option T) Λ, Turing.Reaches (Turing.TM0.step M) (Turing.TM0.init (w.map some)) cfg ∧ Turing.TM0.step M cfg = none := by
    -- By definition of `TM0.eval`, there exists a configuration `cfg` such that `cfg` is reachable from the initial configuration and `cfg` halts. Use this fact to conclude the proof.
    have h_eval_dom : (Turing.eval (TM0.step M) (TM0.init (w.map some))).Dom := by
      convert h using 1;
    grind +suggestions;
  -- Apply `sim_reaches_halts` to obtain the final configuration `tc_final`.
  obtain ⟨tc_final, htc_final⟩ : ∃ tc_final : @TwoTrackConfig T Λ,
    grammar_derives (tmToGrammar T Λ M) (encodeTwoTrack (initTwoTrack w)) (encodeTwoTrack tc_final) ∧
    M tc_final.headState tc_final.headCur = none ∧
    extractInput (twoTrackOriginals tc_final) = w := by
      convert sim_reaches_halts M (initTwoTrack w) (Turing.TM0.init (w.map some)) (initCorresponds w) cfg hcfg.1 hcfg.2 using 1;
      rw [ extractInput_initTwoTrack ];
  -- Apply `halt_to_halted` and `cleanup_derives` to conclude the proof.
  have h_final : grammar_derives (tmToGrammar T Λ M) (encodeTwoTrack tc_final) (List.map symbol.terminal (extractInput (twoTrackOriginals tc_final))) := by
    exact Relation.ReflTransGen.trans ( halt_to_halted M tc_final htc_final.2.1 ) ( cleanup_derives M _ );
  exact Relation.ReflTransGen.trans ( generation_derives M w ) ( Relation.ReflTransGen.trans htc_final.1 h_final ) |> fun h => h |> fun h => h |> fun h => by simpa [ htc_final.2.2 ] using h;

-- The theorems `tmToGrammar_halts_of_generates`, `tmToGrammar_correct`,
-- `tm_recognizable_implies_re`, and `re_iff_tm_recognizable` have been moved to
-- `Langlib.Classes.RecursivelyEnumerable.Equivalence.TMtoGrammarSoundness` where the
-- corrected soundness proof is located.
