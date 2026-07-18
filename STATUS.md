# Project status

Last updated: 18 July 2026.

## First LBA problem

The question

$$
\mathrm{LBA} \stackrel{?}{=} \mathrm{DLBA},
$$

equivalently

$$
\mathrm{NSPACE}(O(n)) \stackrel{?}{=} \mathrm{DSPACE}(O(n)),
$$

remains open. This repository proves neither equality nor separation. Current
references still list the problem as open; in particular, see Carayol and
Meyer's [*Linearly Bounded Infinite
Graphs*](https://monge.univ-eiffel.fr/~carayol/Papers/5dba301a855ca01.pdf)
and Viola's [2026 complexity
manuscript](https://www.khoury.northeastern.edu/home/viola/papers/moti.pdf).

The separation claimed in Lin's
[arXiv v22](https://arxiv.org/abs/2110.05942v22) does not establish the
result. Its construction provides a separate machine for each finite stage,
but does not provide one uniform LBA for the union of all stages. In logical
form, the unsupported step is

$$
(\forall i,\ \exists M_i,\ L(M_i)=L_d^i)
\quad\Longrightarrow\quad
(\exists M,\ L(M)=\bigcup_i L_d^i).
$$

[Preu's analysis](https://arxiv.org/abs/2110.12421) documents related defects
in earlier versions.

## What is machine-checked

The repository now establishes the following boundaries without assuming a
solution to the open problem:

- `DLBA_subset_LBA` proves the unconditional deterministic-to-nondeterministic
  inclusion.
- `SweepingLBA_pos_eq_LBA_pos`
  [🔗](src/Langlib/Automata/LinearBounded/SweepingCharacterization.lean)
  and `SweepingLBA_eq_LBA`
  [🔗](src/Langlib/Automata/LinearBounded/SweepingEndmarkerCharacterization.lean)
  prove exact marker-free and canonical-endmarker sweeping normal forms.
  The underlying strong predicate
  [🔗](src/Langlib/Automata/LinearBounded/Sweeping.lean) quantifies over
  every finite trace from every canonical input in the relevant model to every
  target (nonempty inputs in the marker-free model), not just a selected
  accepting run.  A change between genuine physical movement
  directions is allowed only when the source head is at cell `0` or the right
  endpoint; explicit `stay` steps and outward moves clamped at an endpoint are
  ignored and retain the previous genuine direction.  Thus rejecting branches
  and arbitrary finite prefixes satisfy the promise too.  The endmarker
  theorem includes `epsilon` through its actual two-cell `⊢⊣` tape.
  Neither equality assumes `Nonempty` nor a
  cardinality lower bound on the finite terminal, work, or state types.
- `SweepingDLBA_eq_DLBA`
  [🔗](src/Langlib/Automata/LinearBounded/DeterministicSweeping/Characterization.lean)
  proves the corresponding exact deterministic normal form by a direct
  same-width compiler.  An initialization pass installs immutable physical
  endpoint bits and one simulated source-head tag.  Thereafter rightward and
  leftward scans simulate each deterministic source transition; an interior
  source-left move is delayed until the returning scan, while a left move
  from the physical right endpoint is performed immediately so that its
  request is not skipped.  Width one, both clamped source directions, source
  `stay`, rejecting halts, and the stationary accepting bridge in `toLBA'`
  are included.  The theorem retains the original `acceptEmpty` bit and its
  strong promise covers every finite prefix from every canonical nonempty
  input.  It normalizes machines already in `DLBA`; it does not determinize
  an LBA or change the first LBA problem.
- `SweepingEndDLBA_eq_DLBA`
  [🔗](src/Langlib/Automata/LinearBounded/DeterministicSweeping/EndmarkerCharacterization.lean)
  gives the same exact deterministic normal form on actual canonical
  endmarker tapes.  Here there is no external empty-word bit: the compiled
  deterministic machine decides `epsilon` while running on the genuine
  two-cell tape `⊢⊣`.  Like the marker-free theorem, it is uniform over every
  finite terminal type and imposes no nonemptiness or cardinality hypothesis
  on the terminal, work, or state types.
- `BinaryBranchingLBA_eq_LBA` and `BoundedDegreeLBA_eq_LBA` show that every
  LBA language has a same-width presentation with configuration indegree and
  outdegree at most two.
- `AcyclicLBA_eq_LBA` and `AcyclicBoundedDegreeLBA_eq_LBA` show that every LBA
  language has an equivalent same-width LBA whose complete configuration
  graph is acyclic; acyclicity also holds at malformed configurations and at
  every tape width. The bounded-degree and acyclic restrictions can be
  imposed simultaneously.
- `boundedDegreeStepLayer_partition` and
  `boundedDegreeStepLayer_biUnique` prove that the actual degree serializer
  has one syntactic two-layer partition, uniform over all tape widths.
  `AcyclicDegreeTwoBiUniqueLBA_eq_LBA` shows that global acyclicity, both
  degree bounds, and those two partial-bijection layers can all be required
  simultaneously without weakening `LBA`.
- `AcyclicDegreeTwoShortBiUniqueLBA_eq_LBA` strengthens the same machine
  normal form so that neither supplied layer contains a path of three edges.
  The local four-phase compiler expands a color-`c` edge with the word
  `c, opposite(c), 0, 1`; it preserves the source tape alphabet and width and
  is sound on every raw configuration.
- `AcyclicDegreeTwoThreeMatchingLBA_eq_LBA` gives an alternative sharp form:
  every LBA language has a globally acyclic degree-two presentation whose
  complete configuration relation is covered exactly by three directed
  matchings.  Its input/output phase split also preserves tape width.
- `twoMatchingLBA_subset_DLBA` proves the complementary positive theorem:
  every LBA presentation whose complete step relation at every width is
  exactly the union of two directed matchings recognizes a `DLBA` language.
  No source acyclicity promise is needed.  The construction pins the only
  possible genuine choice, applies the guarded clock to each resulting
  functional branch, runs the finitely many clocked branches sequentially
  while restoring an immutable input track, and finally folds the functional
  endmarker machine into the marker-free DLBA model.  The explicit empty-word
  bit is computed by the bounded finite simulation `DLBA.acceptsBoundedBool`;
  it is not selected from a semantic language-membership query.
- `not_cofunctional_of_mem_transition_left` and its right-moving analogue
  identify a model-specific obstruction that the earlier reversible route
  must respect.  In the complete raw clamped configuration graph, every
  enabled directional rule has two distinct predecessors of one width-two
  target.  Consequently global configuration cofunctionality forces every
  enabled direction to be `stay`.
  `Machine.languageEnd_iff_of_cofunctional` turns this into the exact
  input-independence theorem: any two canonical endmarker inputs have the same
  acceptance answer, without finiteness or nonemptiness assumptions on the
  component types.  At class level,
  `cofunctionalLBA_eq_trivial_languages` proves that globally cofunctional
  endmarker LBAs recognize exactly `{∅, Set.univ}`, and
  `cofunctionalLBA_subset_DLBA` gives the direct deterministic inclusion.
  The converse and inclusion use the explicit transition-free witnesses
  `Machine.trivialCofunctional` and `DLBA.Machine.trivialHalt`, with their
  rejecting and accepting bits.  These class theorems hold over every finite
  terminal type, including the empty type, with no cardinality lower bound,
  and concern the repository's complete raw clamped relation rather than a
  well-formed-only or unclamped promise.
  Thus this actual global raw `Cofunctional` class does not require a nested
  target/predecessor sweep:
  the separate exhaustive-backtracking semantics and same-width capacity
  lemmas describe an abstract finite unique-predecessor relation, useful for
  a possible well-formed subgraph promise, rather than a nontrivial moving
  class under this raw predicate.
- `reversibleLBA_eq_trivial_languages` therefore characterizes the currently
  defined all-raw-configuration `ReversibleLBA` class exactly as
  `{∅, Set.univ}`.  The structural phase-split theorem
  `reversibleLBA_subset_twoMatchingLBA` remains correct, but this source class
  is not the standard marked-tape reversible-TM class and cannot serve as the
  target of a moving reversible compiler in the clamped model.
- `is_AcyclicTwoMatchingLBA_firstSymbol` supplies the complementary positive
  example: over every chosen terminal it gives a globally acyclic exact-two-
  matching machine recognizing precisely the words that begin with that
  terminal.  Its clamped collision uses both colors and is terminal, whereas
  its ordinary nonclamped move continues.  Thus, for every inhabited finite
  alphabet, `reversibleLBA_strict_subset_twoMatchingLBA` proves
  `ReversibleLBA ⊂ TwoMatchingLBA`.
- `CanonicalPortSystem.eulerAccepts_iff_reaches` formalizes the finite-graph
  core of the Lange--McKenzie--Tapp route.  For any finite functional relation
  and terminal target, the single permutation obtained by cyclically rotating
  incident edge ends and then swapping across the selected edge reaches that
  target exactly when the original forward computation does.  The stronger
  `euler_singleOrbit_on_basin` puts every port in the terminal backward basin
  in one Euler orbit, while
  `exists_eulerReaches_accepting_iff_exists_reaches` handles an arbitrary set
  of terminal accepting vertices.  Cyclic rejecting components are allowed,
  and one complete Euler orbit is bounded by the finite permutation order.
- `exists_two_directedMatching_partition_of_alternating` gives the general
  graph-theoretic output criterion.  Over an arbitrary vertex type with
  decidable equality, a right-unique relation of indegree at most two is an
  exact union of two directed matchings whenever every double-predecessor
  target is a sink and every edge flips a supplied two-valued phase.  Directed
  even cycles are allowed; isolated antiparallel pairs are handled explicitly.
  `Machine.hasTwoMatchingStepPartition_of_alternating` packages this uniformly
  over every raw tape width.  Strict-rank and finite-acyclic forms are
  corollaries, not hidden premises of the cyclic theorem.
- `Machine.boundaryShuttle_hasTwoMatchingStepPartition` is the first concrete
  machine-level use of that criterion.  It expands every enabled directional
  source instruction into a four-step departure/neighbor-tag shuttle.  On all
  raw tapes and at all widths the compiled relation is functional, has
  indegree at most two, flips a two-valued phase at every step, and makes every
  genuine double-predecessor target terminal.  A nonclamped semantic move is
  simulated in exactly four steps with the tape restored to its intended
  result.  The theorem deliberately requires
  `DirectionalTargetInjective`, a sufficient condition preventing several
  malformed predecessors of its final tag-erasure edge, and it deliberately
  ignores source `stay` instructions; it is not yet a whole-language compiler.
- `Machine.stationaryShuttle_hasTwoMatchingStepPartition` supplies the
  complementary two-step compiler for `stay` instructions.  Its exact
  canonical simulation needs no boundary premise, and its complete raw graph
  is cofunctional precisely when the target state and visible final written
  symbol determine the enabled stationary instruction
  (`stationaryShuttle_cofunctional_iff`).
- `Machine.combinedBoundaryShuttle_hasTwoMatchingStepPartition` combines all
  enabled left, right, and stay instructions over one shared plain/normal
  representation.  It has an exact six-case raw-edge inversion, simulates stay
  moves in two steps and nonclamped directional moves in four, and proves the
  uniform indegree-two/terminal-double-merge/alternating-phase obligations on
  malformed tapes and at widths zero and one.  Its sufficient source
  hypotheses are stated rather than hidden: directional target-instruction
  injectivity, stationary target-and-written-symbol injectivity, and
  directional/stationary target-kind separation.
- `Machine.reaches_of_reaches_combinedBoundaryShuttle` proves unconditional
  reflection between plain/normal endpoints.  More strongly, every raw run
  from a plain/normal configuration stays in one of the canonical protocol
  shapes and represents a source-reachable configuration; a clamped first
  directional landing is terminal and cannot fabricate a later normal state.
  No functionality, injectivity, finiteness, nonclamping, or width premise is
  used for reflection.
- `Machine.combinedBoundaryShuttleLanguageEnd_eq_languageEnd` composes that
  reflection with the endmarker guard invariant.  Every guarded run from
  `loadEnd`, including the empty input's two-cell tape, is nonclamping and is
  therefore simulated forward.  `combinedShuttleEndEquiv` transports the
  tagged alphabet to a canonical `EndAlpha` while fixing input symbols,
  blank, and both markers.  Thus
  `languageEnd_combinedBoundaryShuttleEndmarker_eq_source` is an exact
  whole-language theorem; matching still needs the separately stated local
  injectivity hypotheses.
- `directionLift_localEuler_iff_reaches` replaces the nonlocal canonical port
  order by a uniform finite-control construction for deterministic
  graph-walking machines.  Its slots are only `anchor`, `outgoing`, and one
  `incoming` candidate per finite source state.  Incoming validation executes
  one named opposite memory operation, observes that neighboring memory
  configuration, and checks one finite transition; it neither enumerates nor
  compares memory vertices.  Fixed invalid candidates become swap-fixed
  stubs, and the generalized contour theorem proves exact terminal
  reachability.  The accepting-set form
  `directionLift_localEuler_accepting_iff` is the checked local reversible
  core.  Its remaining abstraction boundary is explicit: a named
  `MemoryGraph.move` is still atomic and must be refined into raw clamped LBA
  microsteps while preserving the out-of-sync incoming probe.
- `phaseDoubledEuler_explicitTwoMatchingPartition` removes the odd-orbit
  obstruction without invoking the general coloring theorem: double every
  port with one bit, flip it on each Euler edge, and color by the source bit.
  For any bi-unique relation over an arbitrary vertex type, with no finiteness
  or decidable-equality assumption, the two explicit layers are bi-unique and
  contain no composable pair of edges.  Projected terminal reachability and
  accepting-set reachability are unchanged.
- `BoundedTapeMemory.graph` now instantiates that abstract memory interface on
  every `(n+1)`-cell tape.  Its finite operation names are stationary
  rewrites, nonclamping departures, and their move-first arrival inverses;
  `move_departure_reverse` proves exact executable inversion.  The
  `BoundedTapeController` translates an ordinary deterministic transition
  table and proves one-step equivalence under the exact nonclamping premise,
  plus whole-run soundness without it.  This closes the abstract bounded-tape
  instantiation, but not the raw-LBA refinement: an arrival operation is still
  one atomic graph move even though its implementation must physically probe
  the neighboring cell and either finish there or restore and return.
- `move_arrival_eq_raw_probe_success` and
  `rawArrivalProbe_invalid_returns` isolate that tape algebra.  Away from a
  boundary, a successful reverse probe restores the predecessor cell exactly,
  while a failed finite test returns to the original target without changing
  the tape.  `rawArrivalCandidate_eq_self_of_previousHead_eq_none` records the
  remaining hazard: at a boundary the first raw reverse move clamps to the
  identity, so a continuing compiler path must detect and dispatch the blocked
  case before executing that directional move.  The marked compiler below
  implements exactly this dispatch with an immutable boundary track.
- `sourceLanguage_iff_phaseDoubledLocalEuler` composes every semantic bridge
  for the deterministic side.  For an arbitrary finite `(machine,
  acceptEmpty)` presentation and every word, membership is equivalent to an
  accepting phase-doubled Euler orbit on the concrete bounded tape.  The proof
  includes exact two-sided controller/simulator reachability from canonical
  inputs, terminal acceptance, direction lifting, and the existing
  marker-free/endmarker language equivalences.  At this abstraction layer it
  is a semantic graph-walking criterion; the following marked refinement is
  its concrete raw LBA implementation.
- `MarkedEulerProbe.rawMachine` is now a concrete raw clamped-LBA transition
  table for the out-of-sync Euler probe.  Every cell retains a finite
  immutable physical-boundary code; outgoing and incoming probes restore both
  touched cells.  A hostile complete-graph audit exposed and eliminated two
  forgeable tag-erasure designs.  The current table validates the departure
  cell before its valid and invalid return branches share one target-tag
  state, so no arbitrary candidate is forgotten by an edge into a continuing
  canonical configuration.
- `MarkedEulerProbe.RawTransitionCase` exhaustively classifies all 25 entries
  of that table.  `rawMachine_functional` and
  `rawMachine_step_rightUnique` hold at every raw width, every edge flips the
  explicit Boolean phase, and
  `no_step_of_clamped_moving_transition` proves that every genuinely moving
  microstep which physically clamps lands in a sink, including on malformed
  tapes and at width zero.
- `MarkedMachineSimulation` checks the independent semantic representation
  layer for every tape width.  Logical projection commutes exactly with a
  marked write-and-normalized-move, boundary correctness is invariant,
  marked/source runs lift and project in both directions, and terminal
  acceptance agrees.  On `plainLoadEnd`, including `epsilon`, this composes
  with the bounded-tape controller and the repository's marker-free
  deterministic simulator to give the undoubled marked-Euler acceptance
  criterion.  Macro parity is intentionally projected away rather than
  confused with the raw microstep phase.
- `exists_phase_transGen_euler` gives the exact finite raw microstep path for
  every one-step undoubled Euler macro from a well-boundary-coded canonical
  port, for all branch families and every tape width.
  `rawReaches_canonical_reflects_euler` proves the converse: every raw run from
  such a source to a canonical-core endpoint segments into genuine Euler
  macros and has an encoded plain endpoint.  Boundary correctness is
  propagated both forward and backward, and the initial encoding theorem
  includes the genuine two-cell `epsilon` tape.
- `rawMachine_configurationIndegreeAtMostTwo` completes the exhaustive
  all-width predecessor audit.  Exact canonical targets have at most one
  predecessor; every other one of the 14 control families has at most two.
  `sink_of_two_distinct_predecessors_rawMachine` proves, without a tape
  well-formedness promise, that every genuine double merge is terminal.
  Together with raw functionality and the explicit flipping microphase,
  `rawMachine_hasTwoMatchingStepPartition` partitions the complete raw step
  relation at every width into two directed matchings.
- `languageEnd_rawMachine_deterministicSimMachine_eq` composes raw
  simulation/reflection with the marked source semantics for every word,
  including `epsilon`.  At the class level,
  `is_TwoMatchingLBA_of_is_DLBA` and `DLBA_subset_twoMatchingLBA` give the
  direct boundary-safe deterministic compiler.  Combined with the existing
  `twoMatchingLBA_subset_DLBA`, `TwoMatchingLBA_eq_DLBA` identifies exact
  two-matching LBA languages precisely with deterministic linear space.  All
  of these theorems are uniform over arbitrary finite terminal, work, and
  state types; there is no cardinality lower bound.
- `hasLinearAcceptingChoiceBound_one_of_twoMatchings` and
  `acceptsWithChoiceEventsSearch_one_eq_true_iff` expose the corresponding
  width-independent semantic bound: one genuine branch event suffices, and
  budget-one finite search decides acceptance from every bounded
  configuration.
- `lba_eq_dlba_iff_acyclicDegreeTwoShortBiUniqueLBA_subset` and
  `lba_eq_dlba_iff_acyclicDegreeTwoThreeMatchingLBA_subset` show that
  determinizing either restricted machine class is exactly the full first
  LBA problem.
- `lba_eq_dlba_iff_certifiedRowReach`,
  `lba_eq_dlba_iff_unitCertificateRowReach`, and
  `lba_eq_dlba_iff_acyclicDegreeTwoUnitCertificateRowReach` reduce the full
  problem exactly to increasingly restricted certified-row reachability
  systems.
- `rowReachLanguage_complementSystem_twice` shows that the checked
  Immerman--Szelepcsényi row compiler is involutive on certified-row
  languages with a finite inhabited row alphabet: every certified-row
  language excludes `epsilon`, so positive complementation twice recovers it
  exactly under that hypothesis.  Consequently
  `lba_eq_dlba_iff_everyComplementSystemRowReachLanguageIsDLBA` shows that
  determinizing only outputs of this complement compiler is already the full
  first LBA problem.  Its direct matching form,
  `lba_eq_dlba_iff_everyComplementSystemRowReachLanguageIsTwoMatchingLBA`,
  says exactly the same for compiling only those outputs to exact
  two-matching presentations.  The statements handle an empty source-row
  alphabet separately and impose no cardinality condition on the finite
  terminal alphabet.
- `lba_eq_dlba_iff_clockCompiledLanguages` and
  `lba_eq_dlba_iff_clockDegreeSerializedLanguages` show that determinizing
  the literal image of the concrete clock compiler is already equivalent to
  solving the full problem. The normalization therefore does not silently
  perform the missing determinization.
- `Machine.reaches_boundedDegreeLift_iff` strengthens the degree-serializer
  interface from language preservation to exact fixed-width all-pairs
  reachability between canonical base/Ready lifts.  The global projection
  theorem `Machine.reaches_boundedDegreeProjectCfg` also reflects every raw
  serializer run, including runs whose endpoints are intermediate or
  malformed protocol configurations.  Composing this with the operational
  clock simulation and checkpoint reflection gives
  `reaches_iff_exists_concreteClockBoundedDegreeCheckpoint`: a prescribed
  source configuration reaches a prescribed target exactly when the literal
  clock-and-degree pipeline reaches some serializer lift of a checkpoint
  representing that same target.  These statements include tape parameter
  zero and impose no artificial alphabet-cardinality or positive-width
  premise.
- `LBA.StepTrace` retains the finite configurations of a run rather than
  forgetting them into propositional `Reaches`.  `StepTrace.append` and
  `StepTrace.crossingCount_append` make trace concatenation and the number of
  crossings of each boundary `b : Fin n` additive, while
  `StepTrace.nonempty_iff_reaches` connects the Type-valued witness back to
  reachability.  `StepTrace.crossingCount_le_liftByReach` proves that replacing
  each step by a head-preserving simulator run cannot erase a crossing;
  `Machine.crossingCount_le_boundedDegreeLiftTrace` specializes this to both
  actual degree serializers.
- `rightBoundaryCfg` is now a public exact normalization milestone with its
  physical head at `Fin.last n`.  The pair
  `reaches_rightBoundary_checkpoint_of_step` and
  `reaches_carry_of_rightBoundary` factors every operational source macro
  through that milestone.  Consequently
  `exists_incremented_checkpoint_stepTrace_crosses_every_boundary` and its
  semantic specialization prove that a complete nonoverflowing macro whose
  represented source head starts at cell zero has one concrete trace crossing
  every physical boundary at least once.
- `exists_selfLoop_fullClock_stepTrace_crosses` iterates that construction
  generically for every finite input/work alphabet and state type, every
  source machine over the canonical endmarked alphabet, and every fixed-width
  configuration with a head-zero self-loop.  It returns one
  bottom-to-top operational trace crossing each boundary at least
  `|Cfg|` times.  The deterministic one-state specialization
  `IdentityCrossing.identitySource` has exact configuration count
  `6^(n+1)*(n+1)` by `card_identityCfgSpace`.
  `exists_finalMachine_stepTrace_crosses_exact` lifts the resulting run
  through both serializers without losing crossings, and
  `exists_finalMachine_stepTrace_crosses_twoPow` gives the simpler
  `2^(n+1)` lower bound.  The very same fixed final machine is globally raw
  acyclic, has both directed degrees at most two, and has the width-uniform
  two-biunique partition, as packaged by
  `IdentityCrossing.finalMachine_globalProperties`.  This proves existence of
  one explicit structural run, not that acceptance or every run is forced to
  cross often, and not a language or determinization lower bound.  At `n=0`
  the bottom-to-top trace still exists, but the crossing assertion is
  vacuous because there is no `b : Fin 0`.
- `exists_boundedDegreeMachine_stepTrace_crosses_exact` applies the same
  generic construction to the already-certified locality witness, not to a
  third machine.  Thus the exact fixed `boundedDegreeMachine` whose width-`n`
  raw graph contains the `(n+1)`-cube also has one actual trace crossing every
  physical boundary at least `2 * 6^(n+1) * (n+1)` times.  Its simpler
  `2^(n+1)` corollary is
  `exists_boundedDegreeMachine_stepTrace_crosses_twoPow`.  Consequently one
  fixed final machine simultaneously has the cube minors, the exponential
  crossing witness, global raw acyclicity, both degree-two bounds, and the
  uniform two-biunique partition.  The locality source is nondeterministic,
  so this synthesis still asserts existence of one selected self-loop run,
  not a lower bound on all or accepting runs.
- `StepTrace.length_add_one_le_card_mul_totalCrossingCount_add_one` gives the
  general upper bound for every simple width-`n + 1` trace:
  `length + 1 ≤ (card State * card TapeSymbol) * (totalCrossingCount + 1)`.
  A physically moving step crosses exactly one boundary; `stay` and outward
  clamped endpoint moves cross none.  The proof partitions the run into
  constant-head blocks and injects each block into the finite local views
  `(state, read symbol)`.  Its per-boundary-cap corollary is
  `length + 1 ≤ (card State * card TapeSymbol) * (n * c + 1)`, including
  `n = 0` and with no inhabitedness or cardinality-lower-bound assumption.
  `StepTrace.eraseLoops` strengthens the result from already-simple traces to
  arbitrary concrete traces: it retains both endpoints while never
  increasing length or any individual boundary count.
  Independently of crossings, `length_add_one_le_card_cfg` bounds every simple
  trace by the full finite configuration space, and
  `exists_simple_acceptingTrace_of_accepts` packages loop erasure for ordinary
  nondeterministic LBA acceptance.  The expanded bound is
  `|State| * |TapeAlphabet|^(n+1) * (n+1)` for a tape with `n+1` cells,
  including `n = 0` and with no cardinality lower bound.
- `BoundedCrossing.HasUniformAcceptingBound` formalizes the intended weak
  quantifier order: one constant `c` works for every accepted word, and each
  such word merely has to possess one accepting trace meeting the cap.  Other
  accepting and rejecting runs are unrestricted.
  `hasLinearAcceptingStepBound_of_hasUniformAcceptingBound` derives an
  accepting trace of linear length, with per-cell constant
  `card State * card TapeAlphabet * max c 1`.
  `hasLinearAcceptingChoiceBound_of_hasUniformAcceptingBound` further derives
  the existing semantic `HasLinearAcceptingChoiceBound` promise for genuine
  branch events.  The stronger crossing-profile route is now complete:
  `terminalProfileNFA_accepts_eq_languageEnd_of_hasUniformAcceptingBound`
  constructs a profile NFA and proves exact language equality; when the
  source alphabet, work alphabet, and state types are finite, its state type
  is finite as well.
  `CellRun` checks writes, stationary and physically clamped moves, genuine
  left/right crossings, and an accepting event at an arbitrary final head;
  neighboring cells share the same chronological bounded profile.
  `accepts_of_active_row` synchronizes those local histories into a genuine
  global run by a decreasing sum of constructor sizes.  Both directions
  include the one-cell tape and make no cardinality-lower-bound assumption.
  The strengthened theorem
  `mem_profileNFA_iff_acceptsWithBound_initialCfgFn` reconstructs an actual
  `StepTrace` and proves that each boundary is crossed no more often than the
  shared profile length, so NFA soundness preserves the advertised cap rather
  than merely ordinary acceptance.
  The local checks now also have a relative executable presentation.
  `LBA.Machine.TransitionTable` supplies, for each control state and scanned
  symbol, an explicit `Finset` of moves together with `mem_next_iff`, which
  proves that this finite table contains exactly the moves in the machine's
  semantic transition set.  `HasCheckedRun` saturates the resulting finite
  one-cell graph; its vertices retain the local phase and suffixes of the two
  fixed profiles.  `hasCheckedRun_iff_nonempty_cellRun` proves this search
  exact, and `cellRunBool_eq_true_iff` and
  `cellCompatibleBool_eq_true_iff` expose Boolean correctness.  Finally,
  `profileStartBool_eq_true_iff`, `profileStepBool_eq_true_iff`, and
  `profileAcceptBool_eq_true_iff` give executable membership tests for all
  three semantic fields of `profileNFA`.  These procedures receive no input
  word or language-membership oracle.  This is deliberately a relative API:
  the caller supplies the finite local table and its exactness proof; the
  layer itself does not synthesize finite syntax from an arbitrary semantic
  `Set` transition.
  `LBA.Machine.FiniteCode` separately supplies the missing code-and-word
  interface for every fixed choice of finite terminal, work, and state types,
  with chosen `Primcodable` presentations for the terminal and work types.  It
  stores only an initial state, accepting bits, and finite local move sets.
  For each fixed cap, `boundedSliceMembershipBool_eq_true_iff` identifies its
  Boolean answer exactly with `LanguageWithBound`, while
  `boundedSliceMembershipBool_computable` proves joint computability in the
  pair `(code, word)`.  The unbounded word is traversed explicitly by
  `Primrec.list_foldl`; it is not hidden in a finite-domain argument.
  `fixedSignatureBoundedSlice_computableMembership` packages the result as
  genuine `ComputableMembership` for the exact range of these fixed-signature,
  fixed-cap codes, with no nonempty-type or cardinality-lower-bound premise.
  This fixed-signature layer alone does not encode the whole varying-signature
  class: its component types and cap remain outside the code, and its
  `Primcodable` instance uses a noncanonical `Fintype.equivFin` serialization
  local to those fixed types.
  `BoundedCrossingVaryingEncodedMembership` closes that remaining gap with one
  primitive-codable raw code whose internal signatures and cap are numeric.
  Its six finite local fields are the runtime work and state counts,
  initial-state index, crossing cap, accepting-state list, and transition-row
  list; the unbounded query word is supplied separately.
  Invalid rows are ignored, zero states denote the empty language, and zero
  work symbols and an empty terminal type are supported.  The schedule replay
  and its finite enumeration are primitive recursive jointly in `(code, word)`.
  `membershipBool_eq_true_iff` proves exact total raw-code semantics (the
  positive-state case is `LanguageWithBound`, while zero states denote the
  empty language).  For a finite ambient terminal type with a chosen
  primitive-codable presentation,
  `varyingBoundedCrossing_computableMembership` packages the exact range as
  DFA; direct NFA and Mathlib-regular forms are also stated.
  `LBA.EncodedMembership` then uses a separate five-field code containing only
  ordinary local automaton data: it omits both the cap and the word.  From that
  code and the query word, the evaluator computes the full finite configuration
  count, invokes the bounded checker at that auxiliary cap, and uses loop
  erasure for completeness.  `LBA_computableMembership` proves that this
  presentation characterizes exactly `LBA` and has jointly decidable
  membership, again under a chosen primitive-codable presentation of the
  finite ambient terminal alphabet.  The adequacy compilers noncomputably
  enumerate arbitrary finite semantic signatures, accepting sets, and
  `Set`-valued transition relations; the actual evaluators inspect only the
  resulting raw finite rows.  This external exhaustive bounded-schedule search
  is justified by the finite configuration graph but has no linear-space
  guarantee and is not an LBA-to-DLBA compiler.
  The exact finite-state sizes are also checked.  `Profile.card` gives
  `|Profile State c| = sum_{i=0}^c |State|^i`, and `card_scanState` gives
  `|ScanState Gamma State c| = 1 + |Gamma| +
  2 * |Gamma| * |Profile State c|`; `card_scanState_expanded` substitutes the
  geometric sum.  At `c = 0`, the counts specialize to `1` profile and
  `1 + 3 * |Gamma|` scan states.  The formulas hold for arbitrary finite
  types, including empty types, and require neither a positive cap nor a
  cardinality lower bound.
  The direct class theorems
  `is_NFA_languageEnd_of_hasUniformAcceptingBound`,
  `is_DFA_languageEnd_of_hasUniformAcceptingBound`, and
  `is_DLBA_languageEnd_of_hasUniformAcceptingBound` therefore show that this
  weak selected-run crossing promise actually forces regularity, hence a
  DLBA presentation.  The last implication uses the explicit one-way
  endmarker scanner behind `is_DLBA_of_is_NFA`, including `epsilon`; it does
  not query source-language membership.
  The converse is now equally explicit.  `DFA.endmarkerTrace` is the
  scanner's concrete `StepTrace`, and `DFA.crossingCount_endmarkerTrace`
  proves that it crosses every physical boundary exactly once, including the
  empty word's sole boundary.  Consequently
  `BoundedCrossingSlice_eq_DFA` and `BoundedCrossingSlice_eq_NFA` identify
  every positive fixed at-most-crossing-cap slice class with the regular
  languages, while `UniformBoundedCrossingLBA_eq_DFA` and its NFA/Mathlib
  forms identify the existential-uniform-cap presentation class exactly.
  These class equalities assume only a finite terminal type, including the
  empty type; the presentation witnesses carry arbitrary finite work and
  state types with no lower bounds.
  Weak linear accepting time alone
  remains insufficient, and the separate bounded-choice development still
  stops before a generic same-width schedule enumerator/replayer.
- `LBA.HeadTurns.physicalDirection` measures actual head displacement, so
  explicit stationary moves and outward moves clamped at an endpoint are
  erased.  `crossingCount_le_headTurnCount_add_indicator` proves, for every
  concrete trace and boundary, that the crossing count is at most the number
  of physical direction changes plus one, with the additive term improved to
  zero when the trace never moves.  No finiteness, nonemptiness, or
  cardinality assumption enters this trace theorem, and width zero is
  included.  The weak promise
  `HasUniformAcceptingHeadTurnBound M r` again selects only one accepting
  trace per accepted word; all other runs are unrestricted.  It implies
  `HasUniformAcceptingBound M (r + 1)`.  Conversely the explicit DFA scanner
  has exactly zero head turns.  Thus, for every natural `r`,
  `HeadTurnBoundedLBA_eq_DFA`, `HeadTurnBoundedLBA_eq_NFA`, and
  `HeadTurnBoundedLBA_eq_isRegular` characterize the entire fixed-`r` class
  exactly, and `HeadTurnBoundedLBA_subset_DLBA` gives the deterministic-LBA
  inclusion.  This is a constant-turn theorem; it makes no claim about a
  reversal bound growing with the input length.
- `LanguageWithBound M c` is the fixed-cap slice of one LBA language.
  `languageWithBound_mono` makes the slices increasing, while
  `languageEnd_eq_iUnion_languageWithBound` proves that every accepted word
  lies in some finite slice.  The exact theorem
  `terminalProfileNFA_accepts_eq_languageWithBound` and its class corollaries
  `is_NFA_languageWithBound`, `is_DFA_languageWithBound`, and
  `is_DLBA_languageWithBound` prove that every fixed slice is regular and has
  a deterministic-LBA presentation.  This countable increasing union of
  regular slices deliberately does not produce one uniform `c`; allowing the
  bound to depend on the word is therefore still vacuous for the whole-language
  regularity theorem.
  `languageWithBound_eq_languageEnd_iff_hasUniformAcceptingBound` states the
  exact missing stabilization condition.  Its exact contrapositives
  `every_crossingCap_misses_of_not_is_NFA` (and the direct DFA/Mathlib-regular
  forms) show that for a nonregular finite LBA language every cap omits some
  accepted word; equivalently every fixed slice is a proper subset of the
  whole language.  The generic trace equivalence
  `not_acceptsWithBound_iff_every_acceptingTrace_exceeds` and the direct
  `every_crossingCap_exceeded_on_all_acceptingTraces_of_not_is_NFA` family
  strengthen the omitted-word statement: on the selected word, every
  accepting trace exceeds the cap at some physical boundary.  The generic
  equivalence includes the zero-boundary tape.  Moreover,
  `every_crossingCap_has_strict_larger_slice_of_not_is_NFA` and its direct
  DFA/Mathlib-regular forms show genuine non-stabilization: above every cap
  `c` there is a `d > c` with `LanguageWithBound M c < LanguageWithBound M d`.
  The exceptional cap zero is classified separately and more tightly.
  `acceptsWithBound_zero_initCfgEnd_iff` replays a zero-crossing trace across
  arbitrary tape widths: since even `epsilon` has the boundary immediately
  right of `⊢`, the head can never leave cell zero.  Hence
  `languageWithBound_zero_eq_empty_or_univ` proves input independence without
  any finiteness assumption, and
  `BoundedCrossingSlice_zero_eq_trivial_languages` identifies the whole
  cap-zero slice class with `{∅, Set.univ}` over every terminal type,
  including the empty type.  Together with the positive-cap equalities, this
  gives the complete fixed-cap taxonomy.
  `BoundedCrossingCapHierarchy` states the remaining pairs directly.  Cap
  zero is contained in every positive slice and directly in the DFA, NFA,
  Mathlib-regular, existential-uniform-crossing, and every fixed-head-turn
  class.  Each inclusion is strict exactly under `Nonempty T`; the witness is
  `{epsilon}`, so the finite-cardinality criterion is exactly
  `1 <= Fintype.card T`.  Under `IsEmpty T`, every word is `epsilon`, every
  language is empty or universal, and cap zero is directly equal to all of
  those named classes.  The positive-cap, uniform-crossing, and head-turn
  classes also have direct pairwise equality theorems.  These sharp statements
  introduce no two-symbol convention and no hidden finiteness assumption in
  the arbitrary-terminal inclusions.
- The development also contains checked results about bounded
  nondeterminism, cofunctional reachability, acyclic layering, degree-two
  diamond paths, schedule capacity, unary regular languages, monotone
  countable unions, and direct configuration encoding.  In particular,
  `exists_two_biUnique_partition` proves the optimal combinatorial bound over
  an arbitrary vertex type: every relation of indegree and outdegree at most
  two is exactly partitioned into two partial bijections.  The fixed-width LBA
  corollary is `Machine.exists_two_biUnique_step_partition`.
- `canReach_iff_twoLayers` and `not_canReach_iff_twoLayers` expose the exact
  reachability and nonreachability recurrences over two partial functions.
  `first_successful_child_decides` shows that choosing the first successful
  branch already decides arbitrary reachability; the ordered-fork witness
  preserves acyclicity, degree two, and exact two-biunique layers under the
  necessary no-incoming-source hypothesis.
- `generator_reaches_symmetric` proves the positive total-permutation
  frontier.  The auxiliary-vertex theorem
  `no_reachability_preserving_permutation_encoding_of_oneWay` proves that a
  genuinely one-way partial bijection cannot be totalized into finite
  permutations while preserving and reflecting its directed reachability.
- `exists_twoBiUnique_strictLayering` packages the finite-graph restricted
  reduction from degree-two reachability to acyclic degree-two reachability
  with exact two-biunique layers.  Its target ranges over clock copies, so it
  is explicitly a multi-target result.
- `finiteReachability_singleTarget_twoBiUnique` removes both restrictions at
  the finite relational level.  It sends arbitrary finite directed
  reachability to reachability between one designated source and one
  designated target in an acyclic graph of directed degree at most two, with
  an exact supplied partition into two partial bijections.  The underlying
  serializer preserves core-to-core reachability and acyclicity exactly;
  `acyclic_iff` records the latter equivalence.  The arbitrary-type numbering
  uses `Fintype.equivFin`, so this checked theorem is structural rather than a
  formalized logspace reduction.
- `finiteReachability_twoLinearTwoDiforests` checks a fixed-slot version of
  the complementary Bhadra--Tewari reduction on numbered finite graphs.  It
  has exactly `6n²` vertices, preserves reachability exactly, and supplies a
  unique two-layer cover whose first layer has path components of length at
  most one and whose second has length at most two.  `positiveCycle` proves
  that every nonempty vertex gadget is cyclic, so this theorem does not add
  the global DAG promise from the preceding normal form.
- `finiteReachability_singleTarget_twoLinearTwoDiforests` closes that gap by
  composing the designated-target acyclic serializer with a generic
  three-edge recoloring.  Arbitrary finite reachability is thereby preserved
  in one globally acyclic degree-two graph with an exact supplied cover by two
  partial bijections, and every monochromatic path has length at most two.
  The construction exposes a strict natural rank and has
  `K + 2K²` vertices when the input serializer has `K` vertices.
- `finiteReachability_designated_threeMatchings` gives a second acyclic
  boundary: arbitrary finite reachability is preserved after splitting every
  serialized vertex into input/output copies, with all edges partitioned into
  three directed matchings.  Conversely, `successor_eq_of_incoming` and
  `not_branches_of_reaches_of_ne_source` prove that an exact union of only two
  directed matchings cannot branch anywhere along a path except at its initial
  vertex.
- `EdgePathPartition` gives the exact finite-DAG path-decomposition minimum in
  a successor-link representation on edge occurrences.  Each link joins
  adjacent edges, no edge has two linked predecessors, and the link relation
  is acyclic; `existsUnique_start_reaches` verifies that every edge occurrence
  lies on a successor chain from exactly one predecessor-free start, and paths
  are counted by those starts.
  `card_edges_sub_sum_min_le_pathCount` proves the universal lower bound, and
  `canonicalPathPartition_pathCount_eq_minimumPathCount` proves that the
  canonical local incoming/outgoing pairing attains it.  Consequently
  `minimumPathCount_eq_card_edges_sub_sum_min` and
  `minimumPathCount_eq_sum_outdegree_sub_indegree` establish
  `min p = |E| - sum_v min(d^-(v), d^+(v)) =
  sum_v (d^+(v) - d^-(v))` for every finite acyclic relation.  The result
  includes empty vertex types and imposes no cardinality lower bound.  It is
  a finite combinatorial theorem, not a construction of a same-width DLBA or
  a uniform enumerator for the canonical paths.
- `exactThreeMatching_relevantBranch_obstruction` makes the contrast uniform
  over every natural `k`, including zero.  One finite DAG of exactly `6*k+2`
  vertices has an exact unique cover by three directed matchings, exactly `k`
  genuine branch vertices, and one designated source-to-target path region in
  which all `k` branches are relevant and ordered by reachability.
  `exists_k_relevant_branches` supplies their injective enumeration.  Thus the
  constant-one branch-event proof for two matching layers cannot extend to
  three merely by changing the number of colors.  This witness is not a
  deterministic-space lower bound and does not exclude recomputing choices.
- `choiceGraph_edge_iff` presents that same split-diamond relation as a
  `FiniteChoiceGraph` whose three choice names are exactly the matching
  colors.  The progress theorems `branchTrace_length_eq` and
  `replayTrace_length_eq` prove that every designated source-to-target trace
  consumes exactly `k` genuine choices, and
  `acceptsWithChoices_acceptTarget_iff` gives the exact target-only budget
  threshold `k ≤ budget`, including `k = 0`.  This is a lower bound for that
  presentation, not for algorithms which recompute or aggregate choices.
- `succinct_exactThreeMatching_relevantBranch_obstruction` strengthens the
  structural witness to the LBA scale.  At every row width `w`, including
  zero, the `k = 2^w` split-diamond DAG has `6*2^w+2` vertices and `2^w`
  ordered relevant branches, while `encodeVertex` injects every vertex into
  `Fin 8 × (Fin w → Bool)`.  The encoder is an explicit composition of the
  canonical sum/product/function numeral equivalences, not an arbitrary
  finite-type numbering, but it supplies only succinct vertex names: no local
  encoded edge test or same-width automaton compiler is claimed.
- A separate fixed local witness closes that presentation gap without changing
  the open class question.  `OdometerDiamondRowSystem.system` is one
  finite-state certified row verifier, independent of the width.  For every
  positive `w`, `rowStep_iff_exists_encoded_edge` proves that its complete
  width-`w` relation is exactly an encoded chain of `2^w` sequential
  diamonds; `not_fixedWidthActive_iff_isolated` makes explicit that malformed
  rows have no incident step.  The semantic relation has
  an exact unique three-matching cover, is acyclic, and has exactly `2^w`
  ordered source-to-target-relevant branches.  The pulled-back theorem
  `complete_nonempty_width_threeMatching` states these properties directly
  on the complete type of rows of width `n+1`, so no artificial lower bound on
  the physical width parameter remains; the row alphabet is explicitly fixed.
  `rowReachLanguage_is_LBA_pos` gives this one row system an input-sized LBA
  presentation.  It does not say that the compiler's administrative raw
  configuration graph retains the matching cover, and the two choices in
  each diamond immediately merge.
- `card_succinctDiamondPaths`, `card_targetBranchSchedules`,
  `card_targetReplaySchedules`, and
  `card_targetBoundedReplaySchedules` make the resulting scale exact: the
  `k = 2^w` witness has precisely `2^(2^w)` explicit source-to-target paths,
  valid target-reaching choice lists, replay lists, and actual budget-exact
  schedule records.  Every such trace consumes exactly `2^w` choices.  For
  every finite row alphabet `A` and every fixed cell factor, including empty
  or singleton `A`, factor zero, and width zero,
  `exists_no_injective_targetBoundedReplaySchedules_fixedLinear` supplies an
  explicit width at which those valid records cannot inject into the
  fixed-linear row family.  This blocks literal injective schedule
  materialization for this presentation, not recomputation, aggregation, or
  a language-level deterministic simulation.
- `card_items_lt_card_of_firstSatisfying_emission` supplies the corresponding
  temporal statement: if a deterministic finite-state orbit first halts after
  `t` steps and emits at most one item per state, complete pre-halt coverage
  forces `|Item| ≤ t < |State|`.  Skipped and repeated emissions, the empty
  item type, and `t=0` are included.  At the explicit diamond obstruction
  width, `no_firstSatisfying_emits_all_targetSchedules_fixedLinear` proves
  that no orbit whose complete state injects into a fixed-linear row can emit
  every valid target-reaching schedule before its first halt.  The state
  encoding includes finite control, head position, and all retained data.
  This blocks literal one-schedule-per-state enumeration, not states which
  aggregate many schedules or a different reachability algorithm.
- `reaches_comparable_of_incoming` strengthens that obstruction from one step
  to the complete forward cone: after a vertex has any incoming edge, every
  two descendants are comparable by reachability.  The explicit four-vertex
  `ThreeForkEdge` has an incoming binary fork, is covered exactly by three
  directed matchings, and
  `threeFork_no_injective_allPairs_encoding_into_twoMatchings` proves that it
  has no injective vertexwise encoding into any exact two-matching graph that
  preserves and reflects reachability for all represented pairs, even when
  the target may use arbitrary auxiliary vertices.  This is an obstruction
  to all-pairs state expansions, not to a source-specific language compiler.
- `weakReaches_root_iff_reaches` identifies the corresponding positive
  source-sensitive case.  In any cofunctional relation, if the designated
  root has no predecessor, its weakly connected component is exactly its
  directed forward cone; no finiteness or acyclicity premise is needed.
  `accepts_iff_reaches_of_cofunctional_root` packages this as exact target
  reachability under the finite exhaustive reversible port schedule, without
  requiring the target to be terminal.
  `reaches_iff_exists_history` now checks the source-sensitive repair itself:
  every finite directed walk, even in a cyclic relation, can be loop-erased
  to a duplicate-free rooted `History`; one-vertex `History.Extension` is
  cofunctional, its empty root has no predecessor, and endpoint projection
  preserves and reflects designated-source reachability.  Over a finite base
  type the history type is finite, and `visits_length_add_one_le_card` bounds
  each stored simple history by the number of base vertices.  No lower bound
  on the finite base type is assumed.
- `sourceReachability_exact_twoMatching_phasePresentation` composes that
  unfolding with the exhaustive canonical port schedule.  For every finite
  directed graph, source, and accepting predicate, the resulting finite phase
  line encounters an accepting endpoint exactly when the source graph does;
  its edges have an explicit exact parity partition into two directed
  matchings.  `phaseLine_biUnique_acyclic_terminating` also records that this
  line is bi-unique, acyclic, reaches its last phase, and has no edge out of
  that phase.
  This is deliberately a nonuniform semantic finite presentation.  The phase
  type and its `portAt` labeling encode one precomputed exhaustive trace and
  depend on the complete instance; finite choice selects the schedule.  It is
  not a vertexwise source-graph embedding, an automaton construction, an
  effective reduction, or a same-width LBA compiler.  For an LBA instance,
  this dependence includes the input word, so the construction is not one
  fixed recognizer for the language.
  The size cost of this particular presentation is now checked on its actual
  phase type.  `phaseOfHistory_injective` chooses a distinct visited phase for
  every rooted history, and `card_history_le_actions_length_add_one` bounds
  the history count by the number of phases in the generated line.  On the
  `k`-diamond chain, `twoPow_le_card_historyPhase` and
  `twoPow_sub_one_le_historyActions_length` therefore force at least `2^k`
  phases and `2^k - 1` scheduled actions.  This is an exponential-size lower
  bound for the concrete exhaustive history-port presentation, not for every
  source-sensitive reduction.
  The whole branch history has moved into the represented vertex.  In
  particular, `historyOfPath_injective` embeds all explicit paths through a
  `k`-diamond chain into the actual rooted `History` type, and
  `twoPow_le_card_history` proves that this type has at least `2^k` elements.
  `histories_le_rowCapacity_of_injective` therefore forces the necessary
  bound `2^k ≤ |A|^W` for injectively storing every such history in one
  width-`W` row over `A`; `not_injective_histories_of_capacity_lt` gives the
  contrapositive.  These statements include zero parameters and empty row
  alphabets.  This is a capacity barrier to literal history materialization,
  not to recomputation or a general deterministic simulation.
  `historyPhases_le_rowCapacity_of_injective` gives the corresponding bound
  for injectively representing every actual phase of the exhaustive schedule
  in one row; it likewise ranges over arbitrary finite row alphabets and all
  widths, including zero.
- The separate Savitch boundary is now machine-checked at both storage and
  execution interfaces, after first checking the recurrence itself.
  `savitchReach_iff_paddedPath` proves that midpoint recursion at depth `d`
  is exactly reachability by at most `2^d` genuine steps, and
  `reaches_iff_savitchReach_clog` proves that depth
  `clog 2 (|V|)` captures all reachability on an arbitrary finite type.  This
  is propositional semantics, not an executable search.
  `row_reaches_iff_savitchReach_clog` specializes uniformly to rows over any
  finite cell type, while `bitRows_reaches_iff_savitchReach` records the exact
  depth-`n` form for all `n`-bit row types, including `n = 0`.
  `finiteSavitchBool_clog_eq_true_iff` now implements the midpoint recurrence
  as a finite short-circuiting Boolean search and proves its answer correct.
  Its instrumented evaluator counts recursive calls actually executed, not a
  fully expanded recurrence tree.  On the empty relation with distinct
  endpoints, `savitchEval_empty_false_calls_ge_pow` proves the
  order-independent lower bound `|V|^d` at depth `d`; the concrete family
  `concrete_empty_evaluation_superpolynomial` uses `|V| = 2^n`, depth `n`,
  and endpoints zero and one to force at least `2^(n*n)` calls and more than
  every fixed `|V|^degree` once `degree < n`.  This is a worst case for this
  evaluator, not a lower bound for directed reachability algorithms.
  `frameStacks_le_rowCapacity_of_injective` then gives the
  exact necessary inequality `|Frame|^depth ≤ |Cell|^width` for injectively
  storing all independent continuation stacks.  Its configuration
  specialization has exponent `n*n`, and
  `binarySquare_exceeds_fixedLinearRowCapacity` supplies the explicit failing
  width `n = |WorkCell|*factor+1` for every finite work alphabet and fixed
  linear cell factor; `exists_no_injective_binarySquareStacks_fixedLinear`
  packages the resulting nonexistence statement.  Independently,
  `orbitPrefix_injective_of_firstSatisfying` proves that every deterministic
  state through the first visit to an arbitrary accepting set is distinct;
  `firstSatisfying_steps_lt_card` and
  `firstSatisfying_steps_lt_rowCapacity_of_injective` bound that time by the
  finite state or row capacity.  The singleton-target `firstHit` results are
  direct corollaries.  Finally,
  `exists_no_binarySquare_firstHit_fixedLinear` supplies a width at which no
  literal fixed-linear-row orbit first reaches one designated target only
  after all `2^(n*n)` traversal indices.  These conditional capacity results
  block materializing arbitrary Savitch stacks or replaying that full
  traversal; they do not rule out an algorithm which aggregates or
  reorganizes the search.
- `hypercubeBranchSetMinor` packages the one-tape locality example as a
  genuine branch-set certificate.  For every positive cube dimension, one
  fixed two-state binary LBA has nonempty, pairwise-disjoint configuration
  fibers, paths connecting each fiber internally, and a raw transition for
  every Boolean-cube edge between the corresponding fibers.  The generic
  `Relation.BranchSetMinorModel` states exactly the usual branch-set data for
  the underlying undirected relation.  This checks the contraction itself;
  standard minor-monotonicity, treewidth, and genus bounds remain external
  graph-theory corollaries and do not become reachability lower bounds.
- `BranchSetMinorModel.trans` and `mapLargeEmbedding` make the next semantic
  contraction compositional.  After adding one explicit identity `stay`
  instruction at every state/symbol pair of that same fixed machine,
  `strictClockHypercubeBranchSetMinor` proves that every positive-dimensional
  Boolean cube remains a branch-set minor of its full semantic strict-clock
  graph.  `strictClock_reflexiveMachine_acyclic` proves that complete clock
  graph is acyclic.  The construction is uniform in the tape parameter and
  uses the canonical first-two-layer embedding.
- `concreteClockBranchSetMinorModel` now performs the corresponding
  contraction through the actual one-tape clock protocol.  For every
  endmarker-alphabet source machine whose fixed-width raw relation is
  reflexive, stopped non-Ready predecessor cones of clean carry entries form
  pairwise-disjoint connected branch sets representing the symmetrized source
  graph.  `endmarkedReflexiveMachine` supplies the exact alphabet bridge for
  the fixed locality witness, and
  `concreteClockHypercubeBranchSetMinor` composes the certificates: every
  positive-dimensional cube is a minor of the complete raw graph of one fixed
  concrete acyclic-clock machine.  That complete raw graph is globally
  acyclic, including malformed protocol configurations.
- `binaryBranchStepBranchSetMinorModel` and
  `IncomingSerializer.branchSetMinorModel` now contract the two actual degree
  serializers separately at every tape width.  The outgoing branch set owns
  its Ready configuration and every well-formed scan set; all scans drain to
  the empty scan, while a singleton scan supplies the represented apply edge.
  The incoming branch set owns only valid source-side written configurations,
  but owns every projected target-side arrival and merge configuration.  This
  makes clamped predecessor collisions target-owned and leaves malformed
  written configurations outside all branch sets.  The tape parameter zero
  (the one-cell graph) is covered, with no lower-cardinality assumptions on
  the finite types.
- `boundedDegreeStepBranchSetMinorModel` composes those two contractions for
  the complete raw `boundedDegree` machine, and
  `concreteClockBoundedDegreeBranchSetMinorModel` proves the general full
  pipeline theorem for every fixed-width reflexive source graph.  Finally,
  `boundedDegreeHypercubeBranchSetMinor` proves that every
  positive-dimensional Boolean cube is a branch-set minor of one fixed
  concrete clock-and-degree-serialized machine.  The *same* final machine is
  globally acyclic on all raw configurations, has indegree and outdegree at
  most two at every width, and has the serializer's single width-uniform
  partition into two partial bijections, as packaged by
  `boundedDegreeMachine_globalProperties`.  The two layers are not directed
  matchings.  This closes the structural clock-plus-serializer contraction;
  it remains a graph obstruction rather than a reachability lower bound or a
  determinization.
- `DLBA_subset_ULBA` and `ULBA_subset_LBA` formalize the sandwich through
  unambiguous linear space using labeled, first-final accepting runs.
  `lba_eq_dlba_iff_lba_subset_ulba_and_ulba_subset_dlba` factors the first LBA
  problem exactly into the two still-open inclusions `LBA ⊆ ULBA` and
  `ULBA ⊆ DLBA`.  The run type retains transition triples as data, including
  distinct moves that reach the same clamped-boundary configuration; it does
  not misuse proof identity as computation identity.

The strongest two-layer normal-form result is thus:

> Every LBA language is accepted by a same-width, globally acyclic LBA whose
> configuration graph has indegree and outdegree at most two and whose entire
> step relation is partitioned by two width-uniform partial-bijection layers,
> with no monochromatic path containing three edges.

Equivalently rigid in a different parameter, three width-uniform matching
layers suffice.  Both remain nondeterministic normal forms. Showing that all
machines in either restricted class can be simulated by DLBAs would solve the
original open problem.

The word "matching" is crucial here.  The two layers in the strongest
two-layer normal form above are partial bijections whose monochromatic paths
may contain two edges; they are not directed matchings.  Under the more
restrictive machine promise of two actual matching layers, the two checked
compilers now prove `TwoMatchingLBA = DLBA`.  Together with the three-matching
normal form this gives a checked structural boundary:

> Two exact directed-matching layers characterize deterministic linear space,
> whereas three exact directed-matching layers already suffice to present
> every LBA language.

This is not a separation of `DLBA` from `LBA`: the repository does not reduce
the universal three-matching presentation to two matchings.  The new theorem
`lba_eq_dlba_iff_acyclicDegreeTwoThreeMatchingLBA_subset_twoMatchingLBA`
states exactly that this remaining class inclusion is equivalent to the first
LBA problem; its equality form states the same frontier as three matching
layers versus two.

The reversible route is now isolated more precisely.  Over every inhabited
finite terminal alphabet, the formally true chain

> `ReversibleLBA ⊂ TwoMatchingLBA = DLBA`

uses the repository's unusually strong all-raw-configuration definition on
the left, so it is not an implementation of the standard theorem that
deterministic space has reversible simulations.  The marked Euler compiler
supplies the needed direct same-width route into exact two matchings.  A
merely functional machine is insufficient: a configuration
with two predecessors and one successor has three incident edges, which two
directed matchings cannot cover.  Global cofunctionality is also impossible
for any compiler that physically moves its head under clamping.  The viable
local protocol must make each unavoidable clamped two-predecessor target a
sink while allowing the nonclamped canonical move to continue, and it must
flip a finite-control phase at every microstep.  The checked first-symbol
machine demonstrates the terminal-collision escape.  The alternating-
matching theorem gives the general output criterion.  The local graph-walking
Euler construction supplies a finite-control reversible semantic core, and
the directional, stationary, and combined shuttles discharge their complete
raw-graph obligations under explicit source hypotheses.  The bounded-tape
memory graph and deterministic-controller correspondence are also checked.
The synchronized compiler's whole-run reflection, endmarker nonclamping, and
canonical alphabet/language transport are now checked as reusable theorems.
The specialized marked refinement closes every one of those obligations:
exact macro simulation and reflection, all-width raw indegree two, terminal
double merges, the exact two-matching partition, and whole-language
composition are checked.  This completes the deterministic-to-two-matching
frontier.  It does not choose a branch of a nondeterministic LBA; the remaining
unrestricted problem is precisely the three-matching-to-two-matching class
inclusion above.

## What is not claimed

- No general LBA-to-DLBA compiler is constructed.
- The `SweepingLBA` equalities are nondeterministic normal forms.  Their
  certified-row construction can choose a successor row and may perform an
  unbounded number of endpoint-to-endpoint passes.  The separate checked
  equalities `SweepingDLBA = DLBA` and `SweepingEndDLBA = DLBA` start from an
  already deterministic machine; none of these sweeping results establishes
  `LBA ⊆ DLBA` or otherwise changes the first LBA problem.
- The affine configuration-capacity theorems rule out a particular direct,
  fixed-alphabet encoding strategy; they are not language-class lower bounds.
- The locality hypercube contraction for the fixed machine, its semantic
  strict clock, the actual one-tape acyclic-clock protocol, and both actual
  degree serializers are formalized
  by `hypercubeBranchSetMinor`, `strictClockHypercubeBranchSetMinor`, and
  `boundedDegreeHypercubeBranchSetMinor`.  Standard numerical treewidth,
  pathwidth, and genus consequences of the certified cube minor remain
  external graph-theory corollaries; none is a directed-reachability lower
  bound.
- The generic optimal two-layer theorem chooses a spanning forest separately
  for each relation. The degree serializer now has a separate local,
  width-uniform coloring theorem, but choosing between its two layers remains
  nondeterministic and gives no LBA-to-DLBA compiler.
- The bounded-nondeterminism development proves semantic and resource lemmas;
  it does not hide a completed low-level DLBA compiler.  Likewise, the
  exhaustive-backtracking and same-width resource lemmas for a finite
  unique-predecessor relation are abstract.  For the repository's actual
  all-raw-configuration `Cofunctional` predicate,
  `Machine.languageEnd_iff_of_cofunctional` and
  `cofunctionalLBA_eq_trivial_languages` prove exact input independence and
  collapse to `{∅, Set.univ}`.  Nested enumeration sweeps are therefore
  neither necessary nor a missing compiler for that class.  This uses raw
  clamping and says nothing about a well-formed-only cofunctionality promise.
- Acyclicity, degree two, local deterministic edge checking, and unit
  certificates do not by themselves remove the global nondeterministic path
  choice.
- The two-layer recurrence, ordered-fork obstruction, and permutation-orbit
  results are relational theorems. They do not formalize Reingold's algorithm
  or turn the partial-bijection hard core into a deterministic LBA.
- The finite designated-target serializer is also a relational theorem.  Its
  exact coloring and graph properties do not provide a deterministic
  reachability algorithm, and its noncomputable arbitrary-type numbering is
  not claimed to be an effective complexity reduction.
- The original fixed-slot linear-`2`-diforest theorem is an effective formula
  on numbered finite graphs, but its short layer components coexist with
  forced cycles in their union.  The later generic subdivision removes that
  cyclicity restriction structurally; its arbitrary-type wrapper inherits a
  noncomputable `Fintype.equivFin` numbering and is still not a same-width
  LBA-to-DLBA compiler or a formalized logspace reduction.
- The machine-level short-layer compilers are genuine finite-control,
  same-width LBA transformations, but they retain the original global path
  choice.  Short monochromatic components or three matching colors do not
  make the union relation functional.
- `TwoMatchingLBA = DLBA` does not imply `LBA ⊆ DLBA`: the checked all-LBA
  normal form uses three matching layers, and no language-preserving reduction
  from three layers to two is claimed.
- The name `ReversibleLBA` refers to global biuniqueness of the repository's
  complete clamped raw relation.  The checked collapse of that definition to
  `{∅, Set.univ}` is not a claim that standard marked-tape reversible machines
  recognize only trivial languages.  A standard reversible simulation must
  be adapted directly to exact two matching layers rather than routed through
  this raw cofunctionality predicate.
- The canonical finite Euler port system by itself is a semantic theorem whose
  arbitrary fiber order is selected from the whole configuration graph.  It
  is not treated as an effective LBA program.  The separate `LocalPort` and
  marked-Euler development removes that nonlocality and implements the
  resulting fixed finite-control ring as a concrete raw LBA compiler.
- The exact-two-matching history phase line is likewise a semantic,
  source-and-input-specific finite trace.  Its checked exponential capacity
  obstruction concerns injectively materializing every history as one row;
  neither the positive phase presentation nor that obstruction supplies a
  uniform LBA determinization or a language-class separation.
- No unconditional `LBA ⊆ ULBA` or `ULBA ⊆ DLBA` theorem is claimed.
  Current linear-space disambiguation results cited in the research ledger
  either use superlinear space or require explicit circuit-hardness
  hypotheses; even conditional disambiguation leaves unambiguous
  determinization open.

## Verification

The current integrated result was checked by the full build/test gates:

- `lake build`: 9,005 jobs completed successfully;
- `lake test`: passed (3,115 jobs);
- the ordinary encoded-membership target built successfully (3,318 jobs),
  and its warning-as-error direct compile completed without diagnostics;
- all five deterministic-sweeping modules compile directly with warnings as
  errors and no diagnostics;
- generated import-hub check: passed;
- theorem-link check: passed;
- diff and proof-hole scans: passed;
- axiom audits for the varying-cap and ordinary encoded-membership headline
  theorems, as well as deterministic-sweeping language preservation,
  all-prefix sweeping, and both deterministic-sweeping class equalities,
  report only `propext`, `Classical.choice`, and `Quot.sound`.

The detailed mathematical and literature ledger is in
[docs/results/first-lba-problem-boundaries.md](docs/results/first-lba-problem-boundaries.md).
