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
- `exactThreeMatching_relevantBranch_obstruction` makes the contrast uniform
  over every natural `k`, including zero.  One finite DAG of exactly `6*k+2`
  vertices has an exact unique cover by three directed matchings, exactly `k`
  genuine branch vertices, and one designated source-to-target path region in
  which all `k` branches are relevant and ordered by reachability.
  `exists_k_relevant_branches` supplies their injective enumeration.  Thus the
  constant-one branch-event proof for two matching layers cannot extend to
  three merely by changing the number of colors.  This witness is not a
  deterministic-space lower bound and does not exclude recomputing choices.
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
- The affine configuration-capacity theorems rule out a particular direct,
  fixed-alphabet encoding strategy; they are not language-class lower bounds.
- The locality hypercube and finite-DAG developments formalize their stated
  combinatorial components, but the graph-minor contraction discussed in the
  report remains paper-level.
- The generic optimal two-layer theorem chooses a spanning forest separately
  for each relation. The degree serializer now has a separate local,
  width-uniform coloring theorem, but choosing between its two layers remains
  nondeterministic and gives no LBA-to-DLBA compiler.
- The bounded-nondeterminism and cofunctional developments prove semantic and
  resource lemmas. They do not hide a completed low-level DLBA compiler.
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

- `lake build`: 8,945 jobs completed successfully;
- `lake test`: passed;
- generated import-hub check: passed;
- theorem-link check: passed;
- staged-diff and proof-hole scans: passed.

The detailed mathematical and literature ledger is in
[docs/results/first-lba-problem-boundaries.md](docs/results/first-lba-problem-boundaries.md).
