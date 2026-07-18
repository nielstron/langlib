---
title: "The first LBA problem: exact boundaries"
description: "Formal equivalent formulations, uniformity obstructions, and sharp restricted cases around the open LBA versus DLBA problem."
parent: "Context-sensitive"
nav_order: 7
---

# The first LBA problem: exact boundaries

## Status

As of July 2026, the question

$$
\mathrm{LBA}\stackrel{?}{=}\mathrm{DLBA}
$$

remains open.  Equivalently, it asks whether

$$
\mathrm{NSPACE}(O(n))=\mathrm{DSPACE}(O(n)).
$$

Carayol and Meyer explicitly record the deterministic/nondeterministic
context-sensitive equality as open in [*Linearly Bounded Infinite
Graphs*](https://monge.univ-eiffel.fr/~carayol/Papers/5dba301a855ca01.pdf).
A 2026 complexity text likewise records that the first LBA problem
[remains open](https://www.khoury.northeastern.edu/home/viola/papers/moti.pdf).
The recent arXiv claim of a separation does not change that status:
[Preu's analysis](https://arxiv.org/abs/2110.12421) identifies the failed
uniform simulation strategy, and the later staged reformulation retains the
unsupported countable-union inference analyzed below.

The work recorded here does not assert either equality or separation.  It
formalizes exact reformulations and concrete obstructions, and it identifies
restricted cases in which nondeterminism can be removed.

The strongest checked deterministic characterization is
`TwoMatchingLBA = DLBA`: no acyclicity premise is needed when the complete
raw step relation at every tape width is exactly partitioned into two directed
matchings, and every deterministic LBA has such a boundary-safe presentation.
Separately, `AcyclicDegreeTwoThreeMatchingLBA = LBA`: three matching layers
already suffice for every LBA language.  The remaining inclusion from the
three-matching class to the two-matching class is equivalent to `LBA = DLBA`;
this two-versus-three structural boundary does not decide that equality.

There is a useful one-way connection with the smaller `L` versus `NL`
question.  If `L = NL`, the standard exponential-padding translation lifts
the equality to every constructible space bound at least logarithmic, in
particular to linear space.  Consequently a separation `LBA ≠ DLBA` would
also prove `L ≠ NL`.  The converse implication is not known: proving the LBA
classes equal would not by itself settle `L` versus `NL`.

There is a precise graph-theoretic reason for this asymmetry.  Hartmanis,
Chang, Kadin, and Mitchell characterize linear-space equality by deterministic
logspace reachability only for graphs that have exponentially shorter,
logspace-computable descriptions.  In their notation,

$$
\mathrm{DSPACE}(n)=\mathrm{NSPACE}(n)
\quad\Longleftrightarrow\quad
\mathrm{GAP}\cap KS[\log m,\log m]\in L.
$$

By contrast, `L = NL` asks for `GAP ∈ L` on every explicitly supplied graph.
A separation on random or incompressible graph instances could therefore
separate `L` from `NL` without touching the compressed configuration graphs
relevant to the first LBA problem.  See Lemma 7 and the discussion following
it in [*Some Observations about Relativization of Space Bounded
Computations*](https://userpages.cs.umbc.edu/chang/papers/log/l-book.pdf).

## Exact formal reachability formulation

A finite `CertifiedRowSystem` describes a graph whose vertices are rows of the
same width as the input.  A finite-state left-to-right verifier checks whether
one row is a successor of another, while a second finite-state scan recognizes
final rows.

The theorems `lba_eq_dlba_iff_certifiedRowReach` and
`lba_eq_dlba_iff_unitCertificateRowReach` prove both of the following
equivalences over every finite input alphabet:

- all LBA languages are DLBA languages if and only if every finite
  certified-row reachability language is a DLBA language;
- the same equivalence already holds when the local row verifier has
  certificate alphabet `Unit`.

The second statement is important.  Ordinary subset construction removes all
nondeterminism from checking one proposed edge.  What remains is the global
choice of a path through an exponentially large directed graph.

Subset-oriented variants are also provided.  The `Unit` theorem deliberately
refers only to the certificate rather than calling the whole row system
deterministic: only local edge checking has been determinized.

The restriction remains exact even when the row graph is acyclic.  The
same-width construction underlying
`lba_eq_dlba_iff_acyclicUnitCertificateRowReach` adds an `Option A` clock
track.  Every simulated edge either advances the source row or stutters while
the clock increases, and a clock of width `n` has strictly more values than
the `|A|^n` possible source rows when `n > 0`.
The row language rejects the empty input, which is restored separately in the
outer class theorem.  Consequently the transformed graph has no directed
cycle, preserves its reachability language exactly, and still has a `Unit`
certificate alphabet.  The theorem
`lba_eq_dlba_iff_acyclicUnitCertificateRowReach` says that determinizing all
such acyclic systems is equivalent to the full first LBA problem.

The restrictions can be imposed simultaneously.  The strict clock formalized
by `rowDirectedDegreeAtMost_strictAcyclicize` increments only on genuine
source edges, accepts a final source row at any clock value, and preserves
arbitrary uniform predecessor and successor degree bounds.  The
row-presentation theorem
`certifiedRowSystem_rowDirectedDegreeAtMostTwo` then handles its one extra
edge: an injectively encoded raw input row has a fixed initialization target
with at most one raw-row predecessor, and that target is a base-phase
configuration having at most one machine predecessor.
Certificate determinization preserves the row relation exactly.  Consequently
`lba_eq_dlba_iff_acyclicDegreeTwoUnitCertificateRowReach` proves that the full
first LBA problem already occurs for acyclic, `Unit`-certified row systems
whose entire row graph has both indegree and outdegree at most two.

For an input of length `n`, an LBA configuration takes `O(n)` bits, and its
configuration space has at most

$$
N=2^{O(n)}
$$

vertices; the canonical endmarker model has `2^{Theta(n)}` configurations in
the nondegenerate case.  A successful deterministic linear-space method would
therefore solve the relevant directed reachability instances with
`O(log N)` space.  Savitch recursion gives an `O(log² N) = O(n²)` upper bound:
it stores logarithmically many recursion frames, each containing logarithmic
size vertex data.  Recomputing frames does not remove the need to identify
their continuation points.

There is a matching obstacle to compiling Savitch's procedure literally.
A fixed DLBA on width `n` has only `2^{O(n)} = N^{O(1)}` configurations, so
any accepting run can be shortened to that many steps by deleting a repeated
configuration.  The standard recursive Savitch search instead takes worst-case
`N^{O(log N)} = 2^{O(n²)}` time.  Thus a successful linear-space
determinization must reorganize the search enough to obtain both
`O(log N)` storage and a polynomial-in-`N` accepting computation; merely
encoding its recursion stack more compactly would not suffice.  This is a
barrier to that particular simulation, not a time or space lower bound for
all possible algorithms.

The recurrence itself is now checked before applying those resource
observations.  `savitchReach_iff_paddedPath` proves that the depth-`d`
midpoint predicate is exactly a padded path with `2^d` verifier steps, hence
at most `2^d` genuine edges.  `PaddedPath.append`, `PaddedPath.split`, and
`PaddedPath.mono` discharge the exact composition, bisection, and stuttering
steps.  For every finite vertex type,
`reaches_iff_savitchReach_clog` proves that depth
`clog 2 (|V|)` captures the entire reflexive-transitive closure.  The source
and target terms already imply inhabitation, so no artificial cardinality
lower bound is present.  This remains a propositional equivalence: its
existential midpoints are not an executable search or a space analysis.
The row form `row_reaches_iff_savitchReach_clog` quantifies over every finite
cell type and width.  For Boolean rows, `clog_card_bitRows` computes the depth
exactly and `bitRows_reaches_iff_savitchReach` states the resulting depth-`n`
equivalence, including `n = 0`.

The midpoint search is now executable as well as propositional.
`finiteSavitchBool_clog_eq_true_iff` enumerates the finite midpoint type,
short-circuits the two recursive halves and the midpoint disjunction, and
proves that the returned Boolean decides directed reachability at saturated
depth.  `savitchEval` instruments exactly the depth-recursive calls which this
control flow actually demands; it does not charge calls hidden in skipped
branches or count a merely syntactic expansion of the recurrence.

That concrete evaluator has a checked worst case.  On the empty edge relation
and distinct endpoints, every midpoint must be considered.  At a midpoint
different from the source the left query is false; at the source midpoint the
left query is true and the right query repeats the original false pair.
`savitchEval_empty_false_calls_ge_pow` therefore proves, independently of the
enumeration order, at least `|V|^d` recursive calls at depth `d`.  The fully
specified theorem `concrete_empty_evaluation_superpolynomial` takes
`V = Fin (2^n)`, depth `n`, and endpoints zero and one.  It forces at least
`2^(n*n)` calls and exceeds `|V|^degree` whenever `degree < n`.  This proves a
superpolynomial worst case for this implementation, not a time lower bound
for directed reachability or for every possible reorganization of Savitch's
recurrence.

The two elementary resource interfaces are checked independently in
`SavitchRecomputationBarrier`.  For arbitrary finite frame and row types,
`frameStacks_le_rowCapacity_of_injective` proves the exact necessary
inequality

$$
|\mathit{Frame}|^d \leq |\mathit{Cell}|^W
$$

for injectively materializing every depth-`d` stack in one width-`W` row.
`squareConfigurationStacks_le_rowCapacity_of_injective` specializes this to
the quadratic exponent for depth-`n` stacks of width-`n` configurations, and
`binarySquare_exceeds_fixedLinearRowCapacity` gives the explicit failing
width `n = |WorkCell|*factor+1` for every finite work alphabet and fixed
linear cell factor.  `exists_no_injective_binarySquareStacks_fixedLinear`
packages the resulting existential nonencoding theorem.
This premise deliberately concerns arbitrary independent frame values; it is
not a claim that every possible search method must materialize that family.

At the execution interface,
`orbitPrefix_injective_of_firstSatisfying` proves that all deterministic
states through the first visit to an arbitrary accepting set are distinct.
Hence `firstSatisfying_steps_lt_card` bounds that first-acceptance time by the
state-space cardinality; accepting states need not be terminal or fixed.
`firstSatisfying_steps_lt_rowCapacity_of_injective` folds arbitrary finite
control into any supplied injective row encoding.  The singleton-target
`firstHit` theorems are direct corollaries.  The explicit result
`exists_no_binarySquare_firstHit_fixedLinear` gives, for each fixed alphabet
and linear cell allowance, a width at which no row orbit first hits one target
only after all `2^{n^2}` putative traversal indices.  A successful
recomputation route must skip, aggregate, or reorganize those indices; these
theorems do not exclude such a route.

Reversible pebbling does not improve this literal stack accounting.  A pebble
on the Savitch dependency tree must still name the represented midpoint
subproblem.  Complete binary trees of height `h` require `Theta(h)`
simultaneous pebbles in this model, so `h = Theta(log N)` full vertex labels
again occupy `Theta(log^2 N)` bits; see [Komarath, Sarma, and
Sawlani](https://arxiv.org/abs/1604.05510).  This is deliberately only a
pebbling-model observation.  Lange--McKenzie--Tapp bypass Bennett pebbling for
an already deterministic computation, but preserves that computation's
asymptotic space.  Applied after Savitch it therefore preserves
`O(log^2 N)`, while applying it before Savitch would require the missing
deterministic branch schedule.

The 2026 catalytic-space advances for directed reachability do not remove this
obstruction in the ordinary LBA model.  Edenhofer's parameterized algorithm on
an `N`-vertex graph uses

$$
O(\log N\log k+\log N)
$$

ordinary workspace together with

$$
O((N/k)\log^2 N)
$$

bits of catalytic memory.  Keeping the ordinary workspace at `O(log N)`
forces `k` to be at most a constant, leaving an
`O(N log² N)`-bit catalyst.  Chmel, Dudeja, Koucký, Mertz, and Rajgopal give
the stronger logarithmic-workspace bound

$$
N/2^{\Theta(\sqrt{\log N})}
$$

on catalytic bits.  For the full configuration universe of a worst-case LBA
family with `N = 2^{Theta(n)}`, this is still

$$
N/2^{\Theta(\sqrt{\log N})}=2^{\Theta(n)},
$$

exponential in the input length.  The requirement that catalytic memory be
restored does not make that memory available on an ordinary linear-bounded
tape.  Likewise, the 2025 collapse `CL = CNL` is a collapse *inside the
catalytic model*: the supplied simulation permits a
`N^{O(1)} = 2^{O(n)}`-bit catalyst on an LBA configuration universe.  Its
quantitative catalytic Savitch theorem likewise retains a catalyst while
raising ordinary workspace quadratically.  Neither theorem gives a
catalyst-free `O(log N)`-space simulation; discarding the catalyst leaves
ordinary Savitch's `O(log² N)`-space bound.

The later robust/lossy catalytic variants also do not expose an ordinary
workspace simulation.  They retain catalytic memory or explicitly relax its
restoration, and some of their broader collapses require a derandomization
assumption.  These are results about augmented catalytic models, not a way to
fit their extra memory on an LBA tape; see [Koucký, Mertz, and
Sami](https://arxiv.org/abs/2605.09648).

Hartmanis and Hunt gave earlier complete formulations of the same obstacle.
They construct a tape-hardest context-sensitive language whose deterministic
context-sensitivity is equivalent to the full collapse.  They also show that,
under their fixed encoding, equivalence of regular expressions is decidable by
a deterministic LBA if and only if LBA and DLBA coincide.  The corresponding
nondeterministic-LBA algorithm is equivalent to complement closure of
context-sensitive languages, which is now known.  These historical reductions
are not yet formalized in Langlib because the repository has no encoded
regular-expression decision layer.

Sudborough gave a finite-automaton formulation: the same collapse holds if
and only if every language of a nondeterministic one-way two-head finite
automaton is accepted by some deterministic two-way `k`-head finite automaton,
where `k` may depend on the machine.  See [*On tape-bounded complexity classes
and multi-head finite automata*](https://doi.org/10.1109/SWAT.1973.20).

## Branching and depth boundaries

Large local fan-out is not necessary for the open problem.  The machine-level
serialization proved by `BinaryBranchingLBA_eq_LBA` replaces every finite LBA
by an equivalent one in which every state/symbol pair has at most two moves.
It uses a finite scanner state to offer one
transition at a time, with a mandatory skip edge and an optional apply edge.
The forward and backward simulation is exact, including clamped boundary
moves.  The class theorem `BinaryBranchingLBA_eq_LBA` and the equivalence
`lba_eq_dlba_iff_binaryBranchingLBA_subset` show that binary local branching
already retains the full first LBA problem.

Even bounding both directed degrees simultaneously does not weaken the class.
The construction behind `BoundedDegreeLBA_eq_LBA` first applies the outgoing
serializer, then splits every transition into a tagged write, a tagged move,
and a finite incoming merge chain.  The source
symbol is kept in the tag, so overwriting does not merge unrelated
predecessors.  A clamped left or right move can have two inverse head
positions at a boundary, but never more; the formal proof treats the one-cell
tape and both sharp two-predecessor boundary cases explicitly.  The resulting
machine keeps the same tape alphabet and tape width, and every configuration
has at most two distinct successors and at most two distinct predecessors.
The exact class results are `BoundedDegreeLBA_eq_LBA` and
`lba_eq_dlba_iff_boundedDegreeLBA_subset`.

The serializer has more structure than the cardinality bound alone records.
`boundedDegreeStepColor` is one definition, independent of tape width, that
colors every serialized edge with `Fin 2`.  Scan and apply targets receive
different colors, the two possible inverse clamped moves are separated by
whether the head position changed, and arrival and merge predecessors receive
opposite colors.  `boundedDegreeStepLayer_biUnique` proves that each color is
both functional and cofunctional, while
`boundedDegreeStepLayer_partition` proves exact unique coverage and excludes
nonedges.  Consequently `TwoBiUniqueLBA_eq_LBA` shows that requiring a
two-partial-bijection configuration relation still recognizes all of `LBA`.

Here `Relator.BiUnique` alone does not make a layer a directed matching:
consecutive edges of the same color may still occur.  A directed matching
additionally has no monochromatic path of two edges.  That stronger promise
is the positive two-layer case treated below.

These two restrictions can also be imposed simultaneously at the finite
reachability-instance level.  The strict clock construction used by
`reaches_iff_exists_strictLayer_reaches` replaces an edge `u → v` by

$$
(u,i)\longrightarrow(v,i+1).
$$

It is acyclic, and projection to the first coordinate injects every successor
set and every predecessor set into the corresponding set in the original
graph.  The formal theorem `strictEdge_directedDegreeAtMost` therefore
preserves an arbitrary common degree bound, not only the bound two.
Reachability of `t` becomes reachability of `(t,i)` at some layer
`i ≤ |V|`, as proved by `reaches_iff_exists_strictLayer_reaches`.  Applied
after the bounded-degree serializer, every individual bounded configuration
reachability instance is thus equivalent to an acyclic *multi-target*
instance of directed indegree and outdegree at most two, where the target
predicate accepts every clocked copy of `t`.

A second checked construction removes that multi-target qualification at the
finite-graph level.  First use padded clock edges

$$
(u,i)\longrightarrow(v,i+1)
\quad\text{when}\quad u=v\ \text{or}\ u\longrightarrow v.
$$

This reaches the one fixed top copy of `t`.  Padding can raise the local
degree, so `clockSerializedEdge` then applies an explicit pair of finite
scans.  A source core scans all possible targets, traverses a private bridge
only for an enabled old edge, and enters the corresponding position of the
target's incoming merge scan.  Scan edges have color zero and the two bridge
edges have color one.  Theorems `reaches_iff_clockSerialized`,
`clockSerialized_acyclic`, and
`clockSerialized_directedDegreeAtMostTwo` prove exact designated-endpoint
reachability, global acyclicity, and both degree bounds.  The exact unique
coloring and its two partial-bijection properties are
`clockSerialized_edge_iff_existsUnique_layer`,
`clockSerialized_layer_sub_edge`, and
`clockSerialized_layer_biUnique`.  The single packaged result is
`finiteReachability_singleTarget_twoBiUnique`.

The endpoints are designated vertices, not the graph's only source and sink.
Moreover, the arbitrary-finite-type statement chooses a numbering with
`Fintype.equivFin`; it is a structural theorem and does not claim that this
numbering is computed in logspace.  This finite relational construction is
separate from the uniform same-width LBA compiler described below.

At the machine level, the serializers themselves do preserve global
acyclicity.  The theorem `configurationAcyclic_boundedDegree` combines an
ancestor rank of the source configuration graph with explicit
phase ranks for the outgoing scan and incoming merge gadgets.  It proves that
neither serializer introduces a hidden microcycle and establishes
`is_AcyclicLBA_iff_is_AcyclicBoundedDegreeLBA`.

The source presentation is supplied by a concrete globally acyclic one-tape
compiler.  For a source machine with tape alphabet `Gamma`, state
set `Q`, and `W` physical cells, use a product tape track containing the
source symbol and one base-`B` clock digit, where

$$
B=2|\Gamma||Q|.
$$

Each work cell also carries a simulated-head mark, left/right delimiter
bits, and finitely many reusable phase-specific guard flags.  The physical
head is recovered after each clock sweep by searching for the marked source
cell.

After every simulated source transition, guarded sweeps increment the clock
without wraparound before returning to a `Ready` source state.  Before every
carry, the two normalization sweeps clear all scratch left by the preceding
macro.  The return/search phases may leave `post` and `scan` trails at the
next `Ready` checkpoint; those trails are semantically inert and the following
normalization erases them.  If a malformed tape makes a sweep miss its
delimiter, revisiting a flagged physically clamped cell halts rather than
loops.  Every transition between two consecutive `Ready` configurations
strictly raises the numeric value of the whole physical clock row.  If the
increment acts only on the interval from physical cell `ell` through cell
`k`, its net change is still

$$
B^k-(B-1)\sum_{i=\ell}^{k-1}B^i=B^\ell>0.
$$

Inside a macrostep, a finite phase order together with the number of one-shot
flags already crossed gives a strictly increasing rank.  Initialization is
separately acyclic because it only converts raw cells and then performs one
guarded return sweep.  Thus the argument covers the entire configuration
graph, not only canonical-input runs.

The clock has enough capacity because

$$
B^W>|Q|\,W\,|\Gamma|^W,
$$

the number of source configurations.  A shortest accepting source path is
simple and therefore fits before overflow.  The formal theorems
`AcyclicLBA_eq_LBA`, `AcyclicBoundedDegreeLBA_eq_LBA`, and
`AcyclicDegreeTwoBiUniqueLBA_eq_LBA` give the resulting class equalities.  The
last combines global acyclicity, both degree-two bounds, and the explicit
two-biunique-layer family.  This is only a normalization of nondeterministic
runs: it does not choose a path through the resulting acyclic graph and
therefore does not imply `LBA = DLBA`.

The layers can now be made short **at the machine level**, without an
all-pairs configuration encoding.  The literal finite subdivision described
later has `N + 2N²` vertices at a fixed width and therefore cannot be
represented by a constant-factor extension of finite control over the same
tape alphabet.  `Machine.shortLayers` instead uses the local four-phase
quotient

```text
core u → chosen(u, move) → landed v → pad v → core v
 colors       c                opposite(c)       0       1.
```

`chosen` retains only one finite transition triple; `landed` and `pad` are
canonical for the target configuration.  The three dummy steps rewrite the
currently read symbol and use the model's stay direction, so the tape alphabet
and tape width do not change.  Malformed `chosen` states are gated by both the
saved read symbol and membership of the saved move in the source transition
table.

Retaining a transition triple exposes one subtlety that an unlabeled edge
relation hides: two different triples can occasionally produce the same
clamped-boundary successor.  `Machine.StepLabelInjective` states that every
source/target configuration edge has at most one such operational label.
`serializeIncoming_stepLabelInjective` proves this globally for the incoming
degree serializer—its written state stores the complete move tag—and hence
`boundedDegree_stepLabelInjective` supplies the property for the simultaneous
degree serializer.  This is used exactly where the compiled layer proofs must
identify two `chosen` labels; proof identity is not being treated as an
operational label.

The color word `c, opposite(c), 0, 1` has no monochromatic run of three edges,
including across macro boundaries.  `step_iff_existsUnique_stepLayer`,
`stepLayer_biUnique`, and `stepLayer_pathLengthAtMostTwo` prove exact cover,
both partial-bijection directions, and the short-path property on the whole
raw configuration graph.  A source rank `r` lifts to phase potentials
`4r+3`, `4r+4`, `4r'+1`, and `4r'+2`; the genuine middle step raises `r`, so
`shortLayers_configurationAcyclic` preserves global acyclicity.

The resulting class theorem
`AcyclicDegreeTwoShortBiUniqueLBA_eq_LBA` says that globally acyclic,
degree-two LBAs with two width-uniform linear-`2`-diforest layers still
recognize exactly `LBA`.  The exact frontier statement
`lba_eq_dlba_iff_acyclicDegreeTwoShortBiUniqueLBA_subset` says that
determinizing just this short-layer class would solve the first LBA problem.

There is a still simpler three-color alternative.  `Machine.threeMatchings`
replaces every state by input/output copies.  The symbol-preserving stay edge
`input(q) → output(q)` receives fresh color `2`, and each genuine old edge
`output(u) → input(v)` retains old color `0` or `1`.  Every color is therefore
a directed matching, while projection preserves runs exactly and the rank
lift `2r, 2r+1` preserves global acyclicity.  The final theorems
`AcyclicDegreeTwoThreeMatchingLBA_eq_LBA` and
`lba_eq_dlba_iff_acyclicDegreeTwoThreeMatchingLBA_subset` establish the
corresponding full-power normal form and exact determinization frontier.
This does not conflict with the positive exact-two-matching theorem below:
the two partial-bijection layers in the other full-power normal form may each
contain paths of two edges, while the universal matching form uses three
colors.

The valid-start clock idea is classical for space bounds at least logarithmic.
Sipser explicitly credits Hopcroft and Ullman with the extra-track counter
construction; his own exact-space theorem is deterministic and uses backward
predecessor-tree traversal.  Neither result by itself proves that the whole
configuration graph of a nondeterministic one-tape compiler is acyclic on
malformed tapes.  That stronger all-configurations property is the reason for
the delimiter guards and phase ranks here.  See [*Halting Space-Bounded
Computations*](https://doi.org/10.1016/0304-3975(80)90053-5).

The semantic development proves the exact fixed-width acceptance statement,
global acyclicity, arbitrary directed-degree preservation, and the displayed
capacity inequality in `accepts_iff_exists_clocked_accept`,
`clockedStep_acyclic`, `clockedStep_directedDegreeAtMost`, and
`card_cfg_lt_clockCapacity`, respectively.  It also gives a concrete
`RowNumeral` encoding of all clock layers into one same-width digit row.
Along every semantic clock edge,
`increment_encodeSemanticLayer_of_clockedStep` verifies that the next row is
the nonoverflowing odometer successor, and
`checkSucc_encodeSemanticLayer_of_clockedStep` verifies that the synchronous
finite-state successor checker accepts the pair.  The separate definition
`LBA.AcyclicClock.machine`
formalizes the concrete endmarker-to-endmarker work alphabet and guarded
one-tape transition table.

The operational proof covers both directions.  The theorem
`reaches_canonicalCfg_init` verifies the complete input-conversion sweep.
`nonready_step_phasePotential_lt` proves the phase-rank increase for every raw
non-Ready step.  A second effective-clock rank treats an in-progress carry as
the old row plus its pending positional weight; even malformed clamped carries
are nondecreasing.  Every nonempty Ready-to-Ready path contains a strict carry
entry, so `ready_transGen_clockValue_lt` proves strict whole-row growth.
Combining the two ranks, `machine_configurationAcyclic` proves that the entire
configuration graph of the concrete compiler is acyclic at every tape width,
including malformed configurations.

For valid checkpoints, `reaches_incremented_checkpoint_of_step` proves the
full source-step, normalization, nonoverflowing carry, return, and mark-search
macro with arbitrary incoming and existential outgoing `post`/`scan` trails.
The adapter `machine_simulatesClockedSteps` lifts this to the exact semantic
clock.  Conversely, `first_ready_after_checkpoint` uses non-Ready
right-uniqueness and the strict clock rank to identify every first return as
the exact incremented encoding of one genuine source transition.
`machine_reflectsCheckpointPaths` iterates that result for arbitrary
Ready-to-Ready paths, while `reaches_from_canonicalCfg_of_reaches_ready_init`
shows that every Ready path from a raw canonical target input first passes
through the exact initialized zero-clock checkpoint.  The final theorem
`languageEnd_machine_eq` proves exact language preservation.

The degree serializers and the complete pipeline now have exact reachability
interfaces as well.  `boundedDegreeLiftCfg` is the canonical base/Ready lift,
and `Machine.reaches_boundedDegreeLift_iff` says, at every fixed tape width,

$$
  \operatorname{Reach}_{M.\mathrm{boundedDegree}}
    (\widehat s,\widehat t)
  \quad\Longleftrightarrow\quad
  \operatorname{Reach}_M(s,t).
$$

The reverse direction is not confined to canonical configurations:
`Machine.reaches_boundedDegreeProjectCfg` projects any raw serialized run,
including one beginning or ending in an intermediate or malformed protocol
state, to a source run.  Combining this with the operational clock simulation
and checkpoint uniqueness yields
`reaches_iff_exists_concreteClockBoundedDegreeCheckpoint`.  For prescribed
source configurations `s,t`, it proves that `s` reaches `t` exactly when the
literal machine `(AcyclicClock.machine M).boundedDegree` reaches, from the
canonical zero-clock lift of `s`, some canonical serializer lift of a Ready
checkpoint representing that exact `t`.  Only the clock digits and harmless
Ready trails are existential.  The theorem is uniform at tape parameter zero
and has no positive-width or alphabet-cardinality lower-bound premise beyond
the stated finiteness assumptions.

Finite runs can now be retained rather than immediately truncated to the
proposition `Reaches`.  `LBA.StepTrace` records every intermediate
configuration; `StepTrace.nonempty_iff_reaches` relates it exactly to
reachability, while `StepTrace.append` concatenates witnesses.  For
`b : Fin n`, the quantity `StepTrace.crossingCount b` counts crossings of the
boundary between cells `b` and `b+1`, in either direction, and
`StepTrace.crossingCount_append` proves additivity.  The generic simulation
theorem `StepTrace.crossingCount_le_liftByReach` says that replacing each
source edge by any finite target run cannot erase a crossing when the
configuration embedding preserves head positions.  Its two-serializer
specialization is `Machine.crossingCount_le_boundedDegreeLiftTrace`.

The operational macro proof now exposes its exact right-boundary milestone.
`rightBoundaryCfg` has the physical head at `Fin.last n` after the rightward
normalization sweep.  `reaches_rightBoundary_checkpoint_of_step` reaches it
from every Ready checkpoint after a genuine source step, with arbitrary clock
digits and incoming trails; `reaches_carry_of_rightBoundary` continues from
there through the leftward cleanup to clean carry entry.  Therefore
`exists_incremented_checkpoint_stepTrace_crosses_every_boundary` produces a
concrete full macro trace which, whenever the represented source head starts
at cell zero, crosses every physical boundary at least once.  The theorem
`exists_semanticCheckpoint_stepTrace_crosses_every_boundary` states the same
fact for every exact semantic strict-clock edge.

The stronger structural theorem
`firstReadyMacroStep_represents_iff_strictSourceClockStep` contracts each
deterministic non-Ready protocol corridor and quotients only the harmless
outgoing `ReadyTrails`.  The resulting Ready-checkpoint edge exists exactly
when the source makes one genuine step and the clock makes one
nonoverflowing increment.  Moreover,
`FirstReadyMacroStep.clockValue_eq_add_one` proves that every such returned
edge raises the physical rank by exactly one.  Thus, after the stated trail
quotient and first-Ready observation, the operational macro relation is
formally exactly strict time-unrolling; it does not erase or resolve a source
branch.  This is a relational characterization, not a formal graph-minor or
subdivision theorem for the unquotiented configuration graph.

Consequently
`lba_eq_dlba_iff_acyclicDegreeTwoShortBiUniqueLBA_subset` states the remaining
open problem in the strongest two-layer machine normal form here:
determinizing all globally acyclic LBAs of configuration indegree and
outdegree at most two whose edges are already partitioned into two explicit
linear `2`-diforests is equivalent to determinizing all LBAs.  The independent
three-matching equivalence gives the same boundary with three linear
`1`-diforests instead.  Requiring only two linear `1`-diforest layers is a
more restrictive machine promise and lies on the checked positive side:
`twoMatchingLBA_subset_DLBA` supplies its deterministic simulation.  No
strict separation between the resulting language classes is asserted.

The restriction can be made syntactic rather than merely semantic.
`lba_eq_dlba_iff_clockDegreeSerializedLanguages` quantifies only over machines
literally produced by the fixed pipeline

$$
M\longmapsto
  \operatorname{boundedDegree}(\operatorname{acyclicClock}(M)).
$$

Every output of this pipeline is globally acyclic and degree two, and its
language is exactly that of `M`.  Determinizing just this compiler image is
therefore already equivalent to the full first LBA problem.  This also rules
out the possibility that the clock protocol itself secretly removes the hard
branching: the exact Ready-skeleton theorem above identifies the surviving
source choice one macrostep at a time.

As independent corroboration that degree two is not a soft graph-theoretic
case, [Bhadra and Tewari](https://doi.org/10.1016/j.ipl.2025.106611) prove
that explicit directed reachability remains
`NL`-hard even when the graph is supplied as the union of two linear
`2`-diforests.  Here the `2` bounds the length of every component path; it
does not bound the number of components.  Each supplied layer is therefore a
partial bijection, and can still have linearly many separate components.  Such
graphs have directed indegree and outdegree at most two.
They also prove `NL`-hardness when the supplied partition consists of three
linear `1`-diforests, exactly three directed matching layers.  Their theorem
does not additionally promise a global DAG; Langlib's separate clock and
serializer construction is what supplies acyclicity in the checked
three-matching normal form.

## The synchronized rational-graph interface

A result about rational graphs can look like a shortcut here but uses a
different input interface.  Theorem 4.14 of [Carayol and
Meyer](https://doi.org/10.2168/LMCS-2(2:6)2006) says that a synchronized
rational graph of bounded outdegree, read from one fixed initial vertex, has a
deterministic context-sensitive *path-label language*.  In an LBA
presentation, by contrast, the word is stored in a different initial
configuration for every input and the computation edges do not spell that
word.

Two neighboring results in the same paper sharpen this boundary.  If
synchronization is dropped, Proposition 4.5 and Theorem 4.6 preserve the
unpadded language: every context-sensitive language is the path language from
one fixed vertex of a rational graph of finite, though not necessarily
uniformly bounded, outdegree.  Its growth relation contains the unary map
`#^m -> #^(km)` and can make a reachable vertex exponentially longer in the
visible path length.  For `k > 1` that finite-valued relation is not
synchronized: a finite-valued synchronized relation can increase word length
by only a fixed additive amount.

Conversely, Propositions 4.7 and 4.9 and Theorem 4.10 identify fixed-start
synchronized finite-outdegree path languages with square-picture tiling
languages, equivalently with the context-sensitive languages recognized by
nondeterministic LBAs making only a linear number of tape-head reversals.
The square picture is also a polynomial-size accepting certificate, so this
class lies in `NP`.  Thus an exact synchronized fixed-start encoding of
arbitrary LBAs would already establish both that stronger linear-reversal
normal form and the unproved containment `CS ⊆ NP`.  The latter is equivalent
to `NP = PSPACE`: quantified Boolean formula is `PSPACE`-complete and
decidable in deterministic linear space, while `CS ⊆ PSPACE` holds
unconditionally.  Imposing the uniform outdegree bound needed by Theorem
4.14 would additionally give deterministic context sensitivity.

The reversal characterization also gives a near-linear, but not linear,
generic deterministic upper bound.  In the standard model without stationary
moves, an accepting run with `R` reversals on a width-`O(n)` tape has
`O(n(R + 1))` steps; stationary moves can instead be shortened between head
moves by deleting a repeated local state-and-symbol pair.  For `R = O(n)`,
Loui's one-tape nondeterministic-time simulation therefore gives deterministic
space `O(n sqrt(log n))`.  It still misses the `O(n)` target required for a
deterministic LBA.

There is an exact way to expose the mismatch.  Fix an LBA `M` over input
alphabet $\Sigma$, and add fresh path labels `#` and $\tau$.  A synchronized
rational graph of constant outdegree can do the following from one fixed
vertex:

1. an edge labeled `a` appends `a` to a build-phase copy of the input;
2. one `#` edge changes the completed word `w` into the canonical initial
   configuration of `M` on `w`;
3. every $\tau$ edge performs one transition of `M`;
4. a rational final set recognizes accepting configurations.

Appending a letter and forming the canonical initial configuration are
synchronized rational relations.  A one-tape local transition is synchronous,
and the fixed machine has constant branching.  With disjoint build and
configuration tags, the path language is exactly

$$
K_M=\{w\#\tau^t\mid
  M\text{ has an accepting run of exactly }t\text{ steps on }w\}.
$$

Theorem 4.14 therefore proves that `K_M` is deterministic
context-sensitive.  This is a genuine padded-language consequence, but the
original language is obtained only after existentially deleting the whole
computation suffix:

$$
L(M)
 =\{w\mid\exists t\;w\#\tau^t\in K_M\}
 =K_M/(\#\tau^*).
$$

Equivalently, it is the image of `K_M` under the erasing homomorphism that
fixes input letters and sends `#` and $\tau$ to the empty word.  Neither
operation occurs in the proof of Theorem 4.14.  Its final projection is the
explicit length-preserving map `pi(a_i) = a`: it forgets which of finitely many
uniformized edges was used, but it retains one output letter for every graph
edge.

This erasing step is not a general closure property of deterministic
context-sensitive languages.  Indeed, let `T` be a deterministic Turing
machine recognizing an arbitrary recursively enumerable language `U`, and
put

$$
P_T=\{w\#\tau^t\mid T\text{ accepts }w\text{ within }t\text{ steps}\}.
$$

The language `P_T` is deterministic context-sensitive: on its padded input,
a deterministic machine simulates at most `t` steps using
`O(|w| + t)` space.  But $P_T/(\#\tau^*)=U$, and the corresponding erasing
image is also `U`.  Choosing an undecidable recursively enumerable `U` shows
that deterministic context-sensitive languages cannot be closed under either
of these unbounded deletion operations.  For the restricted family `K_M`
coming from LBAs, proving that this particular deletion always stays
deterministic context-sensitive would prove `LBA = DLBA`; it is the original
problem, not a routine closure lemma.  A shortest accepting LBA run can still
have exponential length, so the `O(|w| + t)` bound for the padded word does not
become `O(|w|)` after deletion.

The other natural encodings meet the same interface boundary:

- computation edges labeled by the empty word are outside the graph model of
  Theorem 4.14.  A naive epsilon-edge extension would be false: the preceding
  input-building construction followed by silent steps of an arbitrary
  deterministic Turing machine would give every recursively enumerable
  language as a fixed-start bounded-outdegree path language;
- making one visible edge perform the whole run requires the reachability
  relation `Step*` as a synchronized rational relation.  Such a relation is
  not rational in general: otherwise composing it with the rational initial
  encoding and rational accepting set would make every LBA language regular;
- allowing a rational set of input-dependent starts does fit the usual
  rational-graph characterization, and the standard tableau construction uses
  such a set.  Carayol and Meyer's Lemma 4.1 converts that set to one vertex by
  adding all its possible first images as outgoing edges.  The paper explicitly
  notes that this construction relies on infinite outdegree, so it cannot
  precede Theorem 4.14;
- a tableau stored explicitly in a vertex has the same problem.  Lemma 4.8 in
  the paper bounds the relevant vertex lengths by the visible path-label
  length from a fixed start.  An exponentially tall LBA tableau therefore
  cannot simply be supplied while the path label remains the unpadded input;
- complementing the padded language does not discharge the suffix either.
  It changes the existential condition on `t` into an unbounded universal
  condition; it does not reduce membership of `w` to one query about a word of
  length `O(|w|)`.

The two elementary orientations of a computation tableau display the tradeoff
particularly clearly.  Reading its columns can retain the `|w|` input labels,
but a vertex then has to hold a column of computation-height length; the
rational initial set can guess that length, whereas a synchronized graph from
a fixed vertex cannot grow it in `|w|` edges.  Reading its rows keeps vertices
of length `O(|w|)`, but it needs one path edge per time step and produces the
`tau` suffix in `K_M`.  Theorem 4.14 permits either resource only when it is
visible in the length of the path word on which its deterministic space bound
is measured.

These are barriers to these adaptations of the rational-graph theorem, not a
proof that no different determinization argument can exist.  In particular,
finding a fixed-start bounded-outdegree synchronized graph whose path-label
language is `L(M)` itself, without an erasable computation suffix or hidden
reachability relation, would already be a solution of the first LBA problem.

One-tape locality also gives no polynomial-in-`d` generic separator-size or
width bound.  For `d` physical cells, the fixed machine
`LBA.LocalityHypercube.machine` has `2d·2^d` configurations.
The generic structure `Relation.BranchSetMinorModel` records the usual
nonempty, pairwise-disjoint connected branch sets and the edge joining each
adjacent pair, after taking the underlying undirected relation.
`hypercubeBranchSetMinor` supplies those data for every positive `d`:
`fixedContents_connectedWithinFiber` keeps each connecting path inside its
fixed-tape fiber, `fiber_disjoint` separates distinct Boolean contents, and
`step_flip` supplies every cube edge between fibers.  Thus the contraction to
the Boolean cube `Q_d` is now machine-checked for this fixed machine.  Standard
minor monotonicity and the known cube bounds, which are not formalized here,
then give

$$
\operatorname{tw},\operatorname{pw}
  =\Omega(2^d/\sqrt d)
  =\Omega(N/d^{3/2}),
\qquad
\operatorname{genus}=\Omega(d2^d)=\Omega(N).
$$

See [Chandran and
Kavitha](https://doi.org/10.1016/j.disc.2005.12.011) and [Beineke and
Harary](https://doi.org/10.4153/CJM-1965-048-6).  The formal machine accepts
nothing, so this is deliberately a structural counterexample, not a
reachability lower bound.  It rules out deriving polynomial width, planar
structure, or small genus solely from one-tape local updates.

The semantic strict-clock part of the same obstruction is now checked rather
than paper-level.  `reflexiveMachine` adds an identity stay move at every state
and symbol of the preceding fixed machine;
`step_reflexiveMachine_self` proves reflexivity on every raw bounded
configuration.  `BranchSetMinorModel.trans` composes branch-set certificates,
while `mapLargeEmbedding` transports one along an injective edge-preserving
map.  Consequently `twoLevelClockHypercubeBranchSetMinor` contracts the two
time copies of every source configuration in the exact two-level unrolling,
and `strictClockHypercubeBranchSetMinor` transports the resulting `Q_d`
certificate into the first two layers of the full semantic strict clock.
`strictClock_reflexiveMachine_acyclic` proves that the complete full clock
graph is acyclic.  These statements cover every positive dimension and are
still semantic relation theorems, not a contraction through the concrete
one-tape compiler.

The corresponding contraction through the concrete one-tape clock protocol
is now checked as well.  `concreteClockBranchSetMinorModel` applies to every
fixed-width endmarker-alphabet source machine whose complete source relation
has a self-loop at every configuration.  The branch set for a source vertex
`v` contains its bottom-clock Ready checkpoint and the complete stopped
non-Ready predecessor cone of the clean carry entry for `v`.
`bottomCheckpoint_to_cleanCarry_beforeReady_of_step` proves that, after the
first raw protocol edge for any source step, the remaining corridor lies in
the target's cone.  Right uniqueness of the stopped protocol makes two clean
carry endpoints comparable if their cones intersect; their equal phase
potential then forces equality, and `cleanCarry_injective` recovers equality
of represented source configurations.  Ready/carry phase separation handles
checkpoint--cone intersections.  These facts give nonempty, connected,
pairwise-disjoint branch sets and a correctly oriented raw edge for every
symmetrized source edge.

`endmarkedReflexiveMachine` embeds the fixed Boolean locality machine into the
compiler's `EndAlpha Unit Bool` source alphabet and inserts a self-loop on
every state/symbol pair.  The configuration embedding is injective and
preserves every locality transition.  Composing its transported cube
certificate with the generic concrete corridor theorem gives
`concreteClockHypercubeBranchSetMinor`: for every positive dimension, `Q_d`
is a branch-set minor of the complete raw graph of one fixed concrete
`AcyclicClock.machine`.  `concreteClock_endmarkedReflexiveMachine_acyclic`
simultaneously records global acyclicity on all raw configurations, including
malformed protocol configurations.

The serializer contractions are now checked too.
`binaryBranchStepBranchSetMinorModel` assigns the outgoing serializer's Ready
configuration and every well-formed `scan` configuration over the same source
state and tape to one branch set.  Every remaining-move set drains to the
empty set through skip edges, and the singleton containing a chosen move
supplies the apply edge between the source and target branch sets.
`IncomingSerializer.branchSetMinorModel` assigns only genuinely adjacent
`written` configurations to their source, while every `arrived` and `merge`
configuration belongs to the fiber of its projected target.  The latter
ownership is what keeps clamped predecessor collisions disjoint; malformed
written configurations are unused.  Both theorems quantify over every tape
parameter, including parameter zero (the one-cell graph), and over the
complete raw target graphs.

`boundedDegreeStepBranchSetMinorModel` composes the two corridor models for
the literal `Machine.boundedDegree` implementation, and
`concreteClockBoundedDegreeBranchSetMinorModel` gives the general full
pipeline contraction for every reflexive fixed-width source graph.  Applying
that theorem to the concrete-clock certificate gives
`boundedDegreeHypercubeBranchSetMinor`: for every positive `d`, `Q_d` is a
branch-set minor of the complete raw graph of one fixed actual
clock-and-degree-serialized machine.  `boundedDegreeMachine_globalProperties`
proves that this exact same final machine is globally acyclic on all raw
configurations, has both directed degrees at most two at every width, and has
one width-uniform exact partition into two partial bijections.  The layers are
not directed matchings.  This closes the structural contraction that was
previously paper-level, but it is still neither a directed-reachability lower
bound nor a language separation.

Acyclicity does not by itself force short crossing sequences either, and this
witness is now fully formal rather than paper-level.
`exists_selfLoop_stepTrace_to_semanticLayer_crosses` works for arbitrary
finite input/work alphabets and state types, any source machine, and any
fixed-width source configuration whose head is at cell zero and which has a
self-loop.  For every `k <= |Cfg|` it concatenates the first `k` concrete
semantic macros and returns one trace crossing each boundary at least `k`
times.  Its full-clock form
`exists_selfLoop_fullClock_stepTrace_crosses` reaches exact layer `|Cfg|`.

The fixed specialization uses the one-state deterministic machine
`IdentityCrossing.identitySource`, whose only move writes back the symbol it
reads and stays in place; `identitySource_step_iff` proves that its complete
step relation is exactly identity.  Over
`AcyclicClock.SourceAlpha Unit Bool`, the source alphabet has six elements and
`card_identityCfgSpace` computes the exact width-`n` configuration count

$$
N=6^{n+1}(n+1).
$$

The single machine `IdentityCrossing.finalMachine` is
`(AcyclicClock.machine identitySource).boundedDegree`, independent of `n`.
`exists_finalMachine_stepTrace_crosses_exact` gives an actual bottom-to-top
width-`n` run of this machine with at least `N` crossings at every physical
boundary; `exists_finalMachine_stepTrace_crosses_twoPow` records the immediate
lower bound `2^(n+1)`.  Degree serialization cannot remove these crossings by
`Machine.crossingCount_le_boundedDegreeLiftTrace`.  For this exact same
machine, `IdentityCrossing.finalMachine_globalProperties` packages global
acyclicity of every complete raw configuration graph, both directed degree-two
bounds, and the serializer's one width-uniform exact two-partial-bijection
partition.

The crossing witness can also be placed in the exact locality machine from
the preceding cube-minor theorem.  Its endmarked reflexive source has two
states and six tape symbols, so `card_crossingSourceCfgSpace` gives

$$
N_{\mathrm{loc}}=2\cdot 6^{n+1}(n+1).
$$

`exists_boundedDegreeMachine_stepTrace_crosses_exact` proves that the same
definition `LocalityHypercube.ConcreteClock.boundedDegreeMachine` whose raw
graph contains the `(n+1)`-cube has one directed trace with at least
`N_loc` crossings at every boundary;
`exists_boundedDegreeMachine_stepTrace_crosses_twoPow` gives its
`2^(n+1)` corollary.  Hence a single fixed machine simultaneously carries the
undirected cube minors, an exponential directed crossing witness, global raw
acyclicity, both degree-two bounds, and the width-uniform two-biunique
partition.  Unlike the one-state identity source, this locality source is
nondeterministic; the theorem selects its inserted self-loop and still makes
no assertion about all runs or accepting runs.

For the identity specialization, the existential order matters at tape
parameter `n=0`: the theorem still constructs a genuine six-macro
bottom-to-top trace on the one-cell tape, while the statement about every
`b : Fin 0` is vacuous because there is no physical boundary.  Both
specializations establish existence of one deliberately constructed run;
neither says that acceptance, rejection, or every run forces long crossing
sequences.  They are not language lower bounds, nondeterministic time lower
bounds, or determinizations.  They only block a lemma asserting that global
raw acyclicity, even together with degree two and two partial-bijection
layers, makes all literal crossing sequences short.  Loui's general
crossing-sequence
simulation gives
`(T log T)^{D/(D+1)}` deterministic space for a nondeterministic
`D`-dimensional one-tape computation of time `T`; in dimension one and at
exponential LBA time, the bound remains exponential in the tape width.  See
[*A Space Bound for One-Tape Multidimensional Turing
Machines*](https://doi.org/10.1016/0304-3975(81)90084-0).

### Uniformly bounded accepting crossings

The complementary positive hypothesis is a single constant bound on every
boundary of one selected accepting run.  The quantifier order is essential:
for one fixed machine there must be a `c` such that every accepted word has
some accepting trace crossing each physical boundary at most `c` times.
Other accepting runs and every rejecting run may behave arbitrarily.  Allowing
`c` to depend on the word would be vacuous.

The local combinatorial bound is now checked directly for the repository's
clamped bounded-tape model.  For a simple trace of length `L`, put

$$
H=\sum_b c_b,
\qquad
K=|Q|\,|\Gamma|,
$$

where `c_b` is the crossing count at boundary `b`.  Every physical head move
crosses exactly one boundary, while `stay` and outward endpoint moves that
clamp in place cross none.  The `H` moving steps split the trace into `H+1`
constant-head blocks.  Inside one block all off-head cells are frozen, so a
configuration is determined by `(state, scanned symbol)` and the block has at
most `K` configurations.  The machine-checked theorem
`StepTrace.length_add_one_le_card_mul_totalCrossingCount_add_one` is therefore

$$
L+1\le K(H+1).
$$

If a width-`n+1` trace has `c_b <= c` at every one of its `n` boundaries,
`StepTrace.length_add_one_le_card_mul_boundaryCap_add_one` gives the
subtraction-free form

$$
L+1\le K(nc+1).
$$

This includes the one-cell case `n=0`, where there is no boundary and a
simple stationary trace contains at most `K` local views.  No inhabitedness or
alphabet-cardinality lower bound is assumed.  `StepTrace.eraseLoops` removes
configuration cycles from an arbitrary concrete trace, preserves both
endpoints, and can only decrease its length and every individual crossing
count, so the bound does not hide a shortest-run assumption.

`BoundedCrossing.HasUniformAcceptingBound` packages the weak existential
promise on canonical endmarker inputs.  Its checked consequences currently
include a simple accepting witness via
`exists_simple_acceptingTrace_of_acceptsWithBound`, a selected accepting
witness of linear length via
`hasLinearAcceptingStepBound_of_hasUniformAcceptingBound`, and the existing
`BoundedNondeterminism.HasLinearAcceptingChoiceBound`.  The two quantitative
whole-language bounds use the per-cell constant

$$
|Q|\,|\Gamma|\max(c,1).
$$

The stronger classical consequence is regularity.  Pighizzini's
[Theorem 1](https://arxiv.org/abs/0905.1271) constructs an NFA whose states
are bounded crossing sequences and proves this for the same weak measure.
That route is now checked for Langlib's concrete clamped LBA model.
`StepTrace.crossingSequence` records the target control states in literal
chronological order.  A bounded `Profile State c` packages every such list of
length at most `c`, and `CellRun` checks a complete one-cell history including
writes, genuine exits and entries, `stay`, outward endpoint moves that clamp,
and an accepting event at an arbitrary final head.  Equality of bare state
lists alone would not have been sufficient.

`profileNFA` scans the physical cells from left to right.  It guesses one
shared profile at every internal boundary and verifies a `CellRun` on both
sides.  Its delayed final-cell state is what distinguishes a genuine right
exit from a physically clamped right move.  The path theorem
`mem_profileNFA_iff_nonempty_cellCertificate` is exact for every nonempty
width, including one cell.  In the forward semantic direction,
`nonempty_cellCertificate_of_accepting_trace` projects one concrete accepting
trace to those shared profiles and proves that exactly one cell contains the
terminal event.  In the converse direction, `accepts_of_active_row`
synchronizes all local histories into one global computation.  A stationary
or clamped step consumes one local constructor; a genuine crossing consumes
the matching exit and entry constructors in two adjacent cells.  The sum of
all constructor counts strictly decreases, so the recursion is well founded.
The strengthened recursion retains the concrete `StepTrace`: at every
boundary its crossing count is at most the length of that boundary's initial
shared profile.  Thus
`mem_profileNFA_iff_acceptsWithBound_initialCfgFn` is an exact equivalence at
the same cap, not merely a soundness implication to ordinary acceptance.

The fixed prefix/suffix construction `terminalProfileNFA` supplies `⊢`,
embeds the input word, and supplies `⊣`.  The exact
theorem
`terminalProfileNFA_accepts_eq_languageEnd_of_hasUniformAcceptingBound` says
that, under one uniform selected-accepting cap, this NFA recognizes the
source LBA language.  Consequently
`is_NFA_languageEnd_of_hasUniformAcceptingBound` and
`is_DFA_languageEnd_of_hasUniformAcceptingBound` prove regularity directly,
and `is_DLBA_languageEnd_of_hasUniformAcceptingBound` supplies the requested
deterministic-LBA consequence.  The latter uses the separate explicit
one-way endmarker machine behind `is_DLBA_of_is_NFA`; its empty input is the
genuine two-cell tape `⊢⊣`, and no language-membership
oracle is used.  All machine-level stitching theorems are polymorphic in the
tape-symbol and state types; the class wrappers assume the library's ordinary
finiteness hypotheses, and the DLBA wrappers additionally expose
`DecidableEq Terminal`.  None assumes a minimum cardinality or positive cap.

The local profile test now also has an explicit executable presentation,
relative to finite local transition data.  `LBA.Machine.TransitionTable`
contains a function

$$
Q\mathbin{\to}\Gamma\mathbin{\to}
  \operatorname{Finset}(Q\mathbin{\times}\Gamma\mathbin{\times}\mathrm{Dir})
$$

and its `mem_next_iff` field proves that each such finite set contains exactly
the moves in the source machine's semantic transition set.  For two fixed
profiles, `LocalVertex` remembers an encoded local phase and a suffix of each
profile.  `LocalStep` is the finite graph of stationary moves, exits, and
entries, and `HasCheckedRun` uses `FiniteReachabilityCounting.reached` to
saturate that graph through its full vertex cardinality.
`hasCheckedRun_iff_nonempty_cellRun` proves that this search is equivalent to
the semantic `CellRun` type.  The exposed Boolean correctness theorems are
`cellRunBool_eq_true_iff` and `cellCompatibleBool_eq_true_iff`.

The same effective interface reaches the profile automaton itself.
`profileStartBool_eq_true_iff`, `profileStepBool_eq_true_iff`, and
`profileAcceptBool_eq_true_iff` prove Boolean membership equivalent to the
start, transition, and accepting sets of `profileNFA`; existential profile
choices are enumerated over their finite types.  No checker receives the
input word or asks whether it belongs to `LanguageEnd M`, so there is no
language-membership oracle in this construction.  This is a relative
executable API, not yet a uniformly encoded compiler: the caller supplies an
explicit `TransitionTable` and its exactness proof.  In particular, these
local-checker definitions do not synthesize a table from an arbitrary semantic
`Set`-valued transition field.

The separate fixed-signature layer `LBA.Machine.FiniteCode` closes the
code-and-word gap at a fixed crossing cap.  A code contains only an initial
state, one accepting bit per state, and finite move sets for each state and
tape symbol.  `boundedSliceMembershipBool_eq_true_iff` proves that its Boolean
profile-NFA evaluation accepts exactly `LanguageWithBound code.toMachine c`.
More importantly, `boundedSliceMembershipBool_computable` treats
`(code, word)` as the input of one computation.  Local queries use finite
domains, while the unbounded input word is processed by the explicit
`Primrec.list_foldl` evaluation of the subset automaton.
`boundedSliceMembership_computablePred` and
`fixedSignatureBoundedSlice_computableMembership` therefore give a genuine
joint decidability predicate and `ComputableMembership` package for the exact
range of fixed-signature, fixed-cap codes.  The theorem assumes chosen
`Primcodable` presentations for the fixed terminal and work types; the state
type is internal to the finite code domain.  No word or semantic
language-membership oracle is present, and no nonempty-type or cardinality
lower bound is assumed.

This is deliberately not an encoding of the whole varying-signature LBA
class.  The terminal, work, and state types and the cap `c` are parameters of
the theorem, not fields of the code.  The finite code type is serialized by a
noncanonical `Fintype.equivFin` chosen after those component types are fixed;
the construction neither makes their cardinalities part of one universal
machine code nor compiles arbitrary semantic `Set` transitions.

The finite-state cost is exact.  `Profile.card` proves

$$
|\operatorname{Profile}(Q,c)|
  = \sum_{i=0}^{c}|Q|^i,
$$

while `card_scanState` and `card_scanState_expanded` prove

$$
|\operatorname{ScanState}(\Gamma,Q,c)|
  = 1+|\Gamma|+2|\Gamma|\,|\operatorname{Profile}(Q,c)|
  = 1+|\Gamma|+2|\Gamma|\sum_{i=0}^{c}|Q|^i.
$$

For `c = 0`, `Profile.card_zero` gives one profile and
`card_scanState_zero` gives `1 + 3|Gamma|` scan states.  These identities hold
for arbitrary finite state and tape-symbol types, including empty types, and
make no positive-bound or cardinality-lower-bound assumption.

For a fixed source machine, `LanguageWithBound M c` names the words with one
accepting trace meeting cap `c`.
`terminalProfileNFA_accepts_eq_languageWithBound` identifies that slice
exactly with the bounded-profile automaton, and `is_NFA_languageWithBound` /
`is_DFA_languageWithBound` prove that every fixed slice is regular;
`is_DLBA_languageWithBound` gives its deterministic-LBA presentation.  The
slices are increasing, and `languageEnd_eq_iUnion_languageWithBound` proves

$$
L(M)=\bigcup_{c\in\mathbb N} L_c(M).
$$

This does not supply a uniform cap: every finite accepting trace belongs to
some word-dependent slice.  The uniform hypothesis is precisely the stronger
assertion that one fixed slice already equals the whole language, as stated
exactly by
`languageWithBound_eq_languageEnd_iff_hasUniformAcceptingBound`.
Conversely, `every_crossingCap_misses_of_not_is_NFA`,
`every_crossingCap_misses_of_not_is_DFA`, and
`every_crossingCap_misses_of_not_isRegular` state the exact obstruction:
if the whole language is nonregular, then for every `c` there is an accepted
word outside `L_c(M)`.  The corresponding `every_languageWithBound_ssubset_*`
theorems say directly that every fixed slice is a proper subset of the whole
language.  These statements require only finiteness of the terminal, work,
and state types, with no nonemptiness or cardinality lower bound.
At trace level,
`not_acceptsWithBound_iff_every_acceptingTrace_exceeds` identifies failure of
bounded acceptance exactly with every accepting trace exceeding the cap at
some boundary.  This equivalence is valid even for a zero-boundary tape, where
the existential boundary forces the absence of accepting traces.  Its direct
NFA, DFA, and Mathlib-regular corollaries are the
`every_crossingCap_exceeded_on_all_acceptingTraces_of_not_is*` theorems.
The exact non-stabilization is stronger still:
`every_crossingCap_has_strict_larger_slice_of_not_is_NFA` and its direct
DFA/Mathlib-regular forms prove that for every `c` there is a `d > c` with
`L_c(M) < L_d(M)`.  The generic construction chooses an accepted word outside
`L_c(M)`, obtains a finite accepting cap `e`, and takes
`d = max (c + 1) e`.

Weak linear accepting time by itself is a false shortcut: nondeterministic
one-tape machines can accept nonregular, even suitably padded NP-complete,
languages in linear time under the weak measure.  The constant *maximum
crossing-sequence* bound is the stronger finite-state lever.

Nor does the explicit clock rank make a one-pass topological sweep
space-efficient.  An elementary `INDEX` family gives a sharp obstruction.
Take a complete binary tree with `m` leaves, include the final edge into leaf
`u_j` exactly when bit `x_j` is one, and reveal only after that prefix the
single edge `u_k → t`.  All edges advance one known layer and both directed
degrees are at most two, but `s` reaches `t` exactly when `x_k = 1`.  Two of
the `2^m` possible prefixes cannot share a streaming state: a suffix selecting
a differing coordinate distinguishes them.  Thus a deterministic one-pass
rank-ordered sweep can require `m = Theta(N)` bits.  This is only a streaming
lower bound—random access or another pass can reread the prefix—but it rules
out the literal “scan each layer once” use of the clock.

The matching positive parameter is layer width.  Storing the reachable
frontier of every layer takes `O(W + log N)` bits when each layer has at most
`W` vertices, so width `W = O(log N)` gives deterministic logarithmic space
and polynomial time.  The clock normal form supplies no such bound: its
layers may have `Theta(N)` vertices.  More generally, strict time-unrolling
reduces arbitrary directed reachability to rank-explicit DAG reachability
with only polynomially many more vertices, so a random-access logarithmic
space method based on rank alone would already settle ordinary directed
reachability.

Forgetting the directions after layering does not expose Reingold's
connectivity algorithm either.  Use the padded `N`-layer construction behind
`reaches_iff_layered_reaches`, and regard every layered edge as undirected.
The bottom source and top target are `N` layers apart, so every undirected path
between them has at least `N` edges.  They have undirected distance exactly
`N` if and only if the original target is reachable: a directed padded path
gives the forward implication, while a length-`N` undirected path must raise
the layer on every edge and therefore is a directed layered path.  This is
itself a logspace reduction from directed reachability to exact unweighted
undirected distance on a layered graph.  Connectivity forgets the crucial
monotonicity; recovering it through distance is already `NL`-hard.
The exact relational statement is formalized by
`reaches_iff_undirectedPaddedPath_card`: a length-`|V|` walk in the
symmetrized layered relation exists exactly when the original target is
directedly reachable, and `paddedUndirectedPath_of_maximal_layer` proves that
every step of such a walk is forced forward.
`no_undirectedPaddedPath_bottom_top_of_lt_card` supplies the complementary
no-shorter statement.

At the other extreme, every fixed path depth collapses much further.  For a
fixed natural number `k`, the construction used by
`rowReachExactlyLanguage_isRegular` places the `k + 1` proposed rows and their
certificates in vertical columns and checks all adjacent row pairs in
parallel with one finite automaton.
Therefore both the exactly-`k` and at-most-`k` row-reachability languages are
regular (`rowReachExactlyLanguage_isRegular` and
`rowReachAtMostLanguage_isRegular`).  The automaton depends on the fixed `k`;
this does not extend to a depth growing with the input.

There is also a positive frontier at a linear number of *genuine branch
events*.  Call a configuration a branch only when it has at least two distinct
successor configurations; duplicate transition descriptions leading to the
same successor do not count.  Suppose a fixed LBA `M` and constant `c` have
the following semantic property: every accepted input of physical width `W`
has an accepting run taking at most `cW` choices out of such branch
configurations (genuine branch events).  Then `L(M)` is a DLBA language.

The deterministic proof enumerates all schedules of at most `cW` choices.
For each schedule it restores the initial configuration and follows every
single-successor stretch without consuming a choice.  A stretch can be
abandoned after one configuration-space traversal: if a configuration repeats
before acceptance, a branch, or a dead end, the unique orbit is trapped in
that cycle.  The schedule, current configuration, schedule cursor, and a
counter through the exponentially many configurations all require only
`O(W)` bits.  They are a constant number of width-`W` tracks and hence pack
into one fixed product alphabet.  To match Langlib's marker-free DLBA
presentation on a nonempty input of length `n`, additionally pack the
`W = n + 2` logical endmarker columns into the `n` physical cells.  The fixed
inequality `n + 2 ≤ 3n` supplies three logical slots per cell, including the
one-letter case; the DLBA's explicit empty-word bit handles `n = 0`.

The theorem `acceptsWithChoiceEventsSearch_linear_eq_true_iff` formalizes the
finite-choice graph decomposition and exact bounded replay, including a
noncomputable exhaustive-search specification and its semantic correctness.
The definitions `packLinearSchedule` and `exists_segmentFuelRow` record
schedule packing and same-width counter capacity.  The development
intentionally stops short of defining the operational replay procedure or the
low-level `DLBA.Machine` that performs all enumeration and replay sweeps; the
preceding machine construction is the accompanying paper proof.  Thus any
counterexample to LBA = DLBA would need, for every LBA presentation of its
language, an unbounded ratio between the minimum number of genuine branch
events on an accepting run and the input length.

The threshold is exact for fixed-length bit vectors and asymptotically sharp
for Boolean schedules of length at most `k`.  The theorem
`bitVectors_le_rowCapacity_of_injective` proves that an injective encoding of
all `k`-bit schedules into width-`W` rows over alphabet `A` requires

$$
2^k\le |A|^W.
$$

`schedules_le_rowCapacity_of_injective` generalizes this to

$$
|\mathrm{Choice}|^k\le |A|^W
$$

for the bounded-schedule type used by the replay construction, and
`not_injective_diamondPaths_of_capacity_lt` transfers it to the explicit
diamond paths.  Hence, for any fixed choice alphabet with at least two
symbols, a fixed row alphabet can injectively hold all schedules only while
`k=O(W)`.  This rules out literal schedule materialization beyond the stated
frontier; it is not a lower bound on simulations that recompute choices or
avoid representing paths individually.

The succinct three-matching family makes the next scale exact on the actual
replay interfaces.  With `k=2^w`, `card_succinctDiamondPaths` gives exactly
`2^(2^w)` explicit source-to-target paths.  The equivalences behind
`card_targetBranchSchedules`, `card_targetReplaySchedules`, and
`card_targetBoundedReplaySchedules` show that there are exactly as many valid
target-reaching choice lists, bounded replay lists, and records in the
repository's budget-`2^w` `Schedule (Fin 3)` type.  These subtypes count the
choice-list data, not proofs of one propositional reachability fact, and every
represented target trace has length exactly `2^w`.

For every finite row alphabet `A` and fixed linear factor `c`, the explicit
width

$$
w=2(|A|c)
$$

satisfies `|A|^(cw) < 2^(2^w)`.  The theorem
`exists_no_injective_targetBoundedReplaySchedules_fixedLinear` therefore
rules out an injective encoding of even the valid target-reaching schedule
records into `cw` cells.  The proof includes empty and singleton alphabets,
`c=0`, and `w=0`; no artificial alphabet lower bound is hidden.  As before,
this is a capacity theorem for literal path-by-path representation, not a
lower bound against recomputation or collective reasoning.

Literal enumeration now has a matching formal time statement.
`card_items_le_steps_of_emitted_before` allows a deterministic orbit state to
emit either one item or nothing; skipped emissions and repeated items are
allowed.  If every item occurs strictly before time `t`, then `|Item| ≤ t`.
When time `t` is the first visit to a halting predicate,
`card_items_add_one_le_card_of_firstSatisfying_emission` combines that bound
with first-hit prefix injectivity to obtain

$$
|Item| + 1 \le |State|.
$$

The theorem includes an empty item type and `t=0`; the halt-time output is not
counted.  Its designated-target forms make no terminal or fixed-point
assumption about the target.

At the same explicit width `w=2(|A|c)`, the specialization
`no_firstSatisfying_emits_all_targetSchedules_fixedLinear` combines that
orbit bound with the exact target-schedule count.  No deterministic
computation whose **complete** state injects into `cw` cells over `A` can emit
all valid target-reaching schedules, one optional item per pre-halt state,
before its first halt.  The encoding covers finite control, head position,
and all other retained data.  A successful simulation may still aggregate
many schedules in one state, prune them, or reason about reachability without
enumerating them.  The result is therefore a barrier to literal temporal
enumeration, not a deterministic-space or language-class lower bound.

## A path-decomposition frontier

A constant number of unrestricted functional/cofunctional *colors*, with no
bound on monochromatic path length, is not enough.  The
theorem `exists_four_biUnique_decomposition` proves, without assuming a finite
ambient vertex type, that every relation with at most two successors and at
most two predecessors is exactly the union of four `Relator.BiUnique`
relations.  The stronger `exists_four_biUnique_partition` assigns every edge
exactly one color by independently choosing two-valued ports at its source and
target.

The checked optimal bound is two even without a finite ambient vertex type.
`edgeConflictGraph_isCycle_even` proves that every simple cycle in the
edge-conflict graph is even; `edgeConflictGraph_colorable_two` converts this
to a proper two-coloring; and `exists_two_biUnique_partition` turns that
coloring into an exact partition of the original relation into two
`Relator.BiUnique` layers.  The theorem
`Machine.exists_two_biUnique_step_partition` applies this to every fixed-width
configuration graph of a finite-alphabet `ConfigurationDegreeAtMostTwo` LBA.
On an acyclic directed graph every layer is consequently a disjoint union of
directed paths, but the number of path components can grow with the graph.
Thus the degree-two hard core already has an optimal constant
partial-bijection decomposition; the unresolved information lies in
unbounded switching among its components.  This generic construction is
structural: its classically chosen spanning forest and coloring may depend on
the tape width and it does not provide a uniform component enumerator.

The distinction from matching layers is decisive.  A partial-bijection layer
may enter and leave the same vertex, so after an incoming edge both colors can
again offer outgoing edges.  With only two directed-matching colors, the
incoming color is unavailable and functionality of the other color leaves at
most one successor.  The resulting one-choice property is what the concrete
two-matching scheduler exploits.

The actual LBA degree serializer avoids that nonuniformity.
`Machine.boundedDegree_hasTwoBiUniqueStepPartition` supplies the concrete
width-independent layer definition described above, and
`AcyclicDegreeTwoBiUniqueLBA_eq_LBA` shows that this same syntactic partition
survives the strongest acyclic normal form.  This still leaves a choice
between the two partial functions after every step; it does not select the
successful color sequence.

The logical recurrence is now isolated without any machine encoding.
`TwoPartialFunctionPartition.of_existsUnique_biUnique` adapts an exact
two-biunique partition to the recurrence interface.
`canReach_iff_twoLayers` says that reachability is the current final test or
success through either colored successor, while
`not_canReach_iff_twoLayers` says that nonreachability is the current
nonfinal test and failure through both colors.  These are propositional
fixed-point unfoldings, not a deterministic evaluation procedure; the latter
conjunction can still have exponential recursion depth on an implicit LBA
graph.

Nor can one hide the same work in a canonical branch selector.
`first_successful_child_decides` adjoins an ordered fork whose left child is
the original source and whose right child accepts immediately.  The left
child is first successful exactly on positive reachability instances, and the
fallback is first exactly on negative instances.  The construction preserves
acyclicity.  More sharply, `fork_preserves_acyclic_two_biUnique` and
`forkEdge_directedDegreeAtMostTwo` keep an exact two-biunique partition and
both degree-two bounds when the old source has no incoming edge.  Thus even
inside the restricted hard core, computing the first successful child already
contains the reachability question it was meant to resolve.

At the generic finite-graph level,
`exists_twoBiUnique_strictLayering` packages a checked restricted reduction:
if the input relation already has both directed degrees at most two, strict
clocking makes it acyclic, preserves both bounds, and admits an exact
two-biunique partition.  Its target is any clock copy of the original target,
so this is a multi-target theorem rather than the single-target reduction
described next.

In fact, arbitrary finite reachability already has this **acyclic,
single-designated-target, two-partial-bijection** normal form.  The checked
theorem `finiteReachability_singleTarget_twoBiUnique` packages the complete
construction.  On an explicitly numbered `N`-vertex graph, padded clocking
first produces `N(N+1)` vertices.  If this number is `K`, the scan serializer
has exactly `3K²+3K` vertices by
`ExplicitDegreeTwoReachability.card_vertex`, still polynomial in `N`.
Every edge and its color are determined directly from its endpoint phases and
at most one query to the old edge relation.  The rank theorem
`liftedRank_lt_of_edge` proves acyclicity, while `acyclic_iff` more strongly
shows that the scan serializer itself preserves and reflects directed cycles.

Langlib's arbitrary-type wrapper deliberately uses the noncomputable
equivalence `Fintype.equivFin`, so the machine-checked theorem establishes the
finite relational normal form, not the logspace uniformity of a reduction.
For already numbered explicit graphs, the displayed clock and scan formulas
give the corresponding effective polynomial-size construction.  Independently,
Bhadra and Tewari prove the complementary complexity result that reachability is
`NL`-hard even when the input is supplied as the union of two linear
`2`-diforests.  In particular, every supplied layer is a partial bijection and
all of its path components have length at most two.  Their theorem does not
add a global DAG promise, so it is stronger in its layer-local restriction and
weaker in that separate respect.  A deterministic logspace algorithm for the
promised linear-`2`-diforest instances would imply `L = NL`.  This is an
explicit-input hardness barrier, not a separation of the compressed LBA
language classes.

The fixed-slot version of that reduction is now checked in
`LinearTwoDiforestReachability`.  For an `N`-vertex numbered graph it gives
every original vertex `N` outgoing ports, `N` incoming ports, and three phases
per port, for exactly `6N²` vertices.  An original edge uses its dedicated
outgoing and incoming ports.  The remaining edges rotate through the ports of
one original vertex.  The packaged theorem
`finiteReachability_twoLinearTwoDiforests` proves exact reachability between
canonical representatives, both directed degree bounds, a unique two-color
cover, biuniqueness of both colors, path-component length at most one in the
first color and at most two in the second.  Fixed ports also make isolated
vertices total; the literal incidence-count presentation has no `v₀₀`
representative when a vertex has degree zero.

The fixed-slot gadget itself deliberately does not merge with the acyclic
normal form.  `positiveCycle` proves that every original vertex in that gadget
lies on a nonempty directed cycle, independently of the input edges, and
`not_acyclic_of_neZero` packages the resulting failure of global acyclicity.
This is a property of that particular port-rotation construction, not a
general incompatibility between acyclicity and short supplied layers.

Indeed, `ShortLayerSubdivision` now gives a generic three-edge repair.  If an
old edge of color `c` is `u → v`, it is replaced by

```text
core u -c→ enter(u,v) -opposite(c)→ exit(u,v) -c→ core v.
```

The two auxiliary vertices are allocated for every ordered pair, so no
decidable-adjacency assumption is needed.  Exact color coverage is retained,
both colors remain partial bijections, and the only possible two-edge
monochromatic chain is `exit → core → enter`; it cannot extend to a third
edge.  Projection commits the represented old edge only on the middle step.
Ranks `3r`, `3r+1`, and `3r+2` therefore preserve acyclicity whenever `r`
strictly ranks the input relation.

Composing this repair with the designated-target clock serializer yields the
checked theorem
`finiteReachability_singleTarget_twoLinearTwoDiforests`.  It simultaneously
provides exact source-to-target reachability, a global DAG, both directed
degree bounds at two, an exact supplied two-color cover, biuniqueness of both
colors, and monochromatic path length at most two.  If the clock serializer
has `K` vertices, the all-pairs subdivision has exactly `K + 2K²` vertices.
The arbitrary finite-type wrapper remains structural and noncomputable for
the same `Fintype.equivFin` reason as the serializer it uses.

There is also a sharp matching-layer comparison.  In
`ThreeMatchingReachability`, every old vertex `v` is replaced by
`input(v) → output(v)` in a fresh third color, while an old color-`c` edge
becomes `output(u) → input(v)` in color `c`.  The theorem
`finiteReachability_designated_threeMatchings` proves that arbitrary finite
reachability still has a designated-source/target, globally acyclic,
degree-two presentation whose three supplied layers are all directed
matchings.  The construction uses only twice as many vertices as its input.

With only **two** matching layers, however, an incoming edge consumes one
color and the matching condition forbids an outgoing edge of that color.  All
outgoing edges must use the sole remaining color, whose functionality makes
the successor unique.  This is formalized by
`successor_eq_of_incoming`, `no_predecessor_of_branches`, and
`not_branches_of_reaches_of_ne_source`: along a path rooted at `s`, a genuine
branch can occur only at `s` itself.

The contrast is quantitatively sharp for three colors.
`exactThreeMatching_relevantBranch_obstruction` gives, for every natural
`k`, one acyclic graph with exactly `6k+2` vertices, an exact unique
three-matching cover, exactly `k` genuine branch vertices, and designated
source-to-target reachability.  `exists_k_relevant_branches` injectively names
all `k` branches, proves each is reachable from the source and can still reach
the target, and orders them by directed reachability.  All statements include
`k=0`.  Therefore the constant-one branch-event argument used below is a
genuine two-matching phenomenon; merely allowing a third matching permits a
linearly growing number of relevant choices.  The family is a structural
witness, not a lower bound against algorithms that recompute or collectively
resolve those choices.

The same graph now has an exact finite-choice accounting.
`choiceGraph_edge_iff` uses the three matching colors as choice names and
proves that they generate precisely the existing split-diamond relation.
The generic progress invariant
`FiniteChoiceGraph.BranchTrace.length_add_progress_eq` charges nothing on
each deterministic stretch and one on each genuine branch.  Its
specializations `branchTrace_length_eq` and `replayTrace_length_eq` show that
every designated source-to-target trace consumes exactly `k` choices, while
`acceptsWithChoices_acceptTarget_iff` proves that target-only bounded replay
succeeds exactly when `k ≤ budget`.  These statements include `k=0`; they are
exact for this presentation and do not exclude a different presentation or
collective recomputation.

Nor is a linear number of branch events an artifact of using a linearly large
vertex name.  `succinct_exactThreeMatching_relevantBranch_obstruction`
instantiates `k = 2^w`.  The resulting DAG has exactly `6*2^w+2` vertices and
`2^w` ordered, source-to-target-relevant branches, yet the explicit
canonical-numeral map `encodeVertex` injects every vertex into
`Fin 8 × (Fin w → Bool)`.  This includes `w=0`.  The theorem supplies succinct
names only: it neither implements the encoded edge relation by local tape
moves nor gives an effective machine-description reduction or an LBA
compiler.

A separate witness now supplies the missing local presentation rather than
merely naming the same asymptotic scale.  The single finite-state verifier
`OdometerDiamondRowSystem.system`, independent of `w`, stores one binary
odometer digit and a repeated finite-control phase in each row cell.  At every
positive width, `rowStep_iff_exists_encoded_edge` characterizes **all** of its
accepted width-`w` row steps as exactly the edges of a chain of `2^w`
diamonds.  Thus noncanonical rows in the ambient fixed-width row type are
isolated, as stated directly by `not_fixedWidthActive_iff_isolated`.
`edge_iff_existsUnique_layer`, `layer_biUnique`, and
`layer_pathLengthAtMostOne` give an exact unique cover by three directed
matchings; the explicit rank proves acyclicity; and
`exists_twoPow_relevant_branches` orders all `2^w` source-to-target-relevant
branch junctions.

`complete_nonempty_width_threeMatching` pulls that cover back to the complete
row type at width `n+1`, including all malformed rows, so the user-facing
statement ranges over every physical nonempty width without an extra lower
bound on `n`.  `rowReachLanguage_is_LBA_pos` gives the fixed row system's
reachability language an input-sized LBA presentation.  This does not assert
that the compiler's initialization and verification sweeps retain the
three-matching cover.  Nor is the example computationally hard: its two
Boolean choices merge immediately.  It is a locally verified presentation
with exponentially many sequential branch events, not a deterministic-space
lower bound.

The machine-level development now turns that obstruction into a genuine
restricted determinization theorem.  `Machine.HasTwoMatchingStepPartition`
requires one exact, width-uniform two-matching cover of the complete raw step
relation.  `Machine.accepts_iff_exists_accepts_pinFirst` shows that acceptance
is exactly the finite union obtained by pinning one possible first transition
triple.  Each pinned machine is locally functional.  To prevent a rejecting
branch from looping forever and blocking later trials, the construction
applies the guarded acyclic clock separately to every pinned machine;
`AcyclicClock.machine_functional` proves that this clocking preserves
functionality.  `ClockedBranchUnion.machine` packages the resulting finite
family over one common alphabet and state type and is globally acyclic on all
raw configurations.

The functional machine `MachineTwoMatchings.sequentialUnion` then tries the
clocked branches in a fixed finite order.  Every physical cell carries a
mutable simulated symbol and an immutable copy of the canonical input.
After a rejecting branch reaches its acyclic sink, deterministic left/right
sweeps restore the mutable track before launching the next branch.  The
soundness proof compares the unique scheduler run with the terminal exhausted
run; it does not claim that the scheduler itself is globally acyclic on
malformed tapes.  Canonical initialization includes the empty word's genuine
two-cell endmarker tape.

Finally, the deterministic endmarker-folding construction transfers the
functional scheduler to the repository's marker-free DLBA model.  The
explicit empty-word bit is computed by `DLBA.acceptsBoundedBool`, which runs
the resulting deterministic finite configuration system up to its cardinality
bound; it is not obtained by asking whether the source language contains
`ε`.  One class-facing result is `twoMatchingLBA_subset_DLBA`:

```text
TwoMatchingLBA ⊆ DLBA
```

No acyclicity premise is present in this inclusion.  In contrast,
`AcyclicDegreeTwoThreeMatchingLBA_eq_LBA` says that three exact matching
layers already suffice for every LBA language.

The reverse deterministic inclusion is now checked by the marked Euler
compiler described below.  `DLBA_subset_twoMatchingLBA` is stated directly
for those two language classes, and `TwoMatchingLBA_eq_DLBA` combines both
directions:

```text
TwoMatchingLBA = DLBA ⊆ LBA.
```

This is a checked structural two-versus-three boundary, not a solution of the
first LBA problem: no language-preserving reduction from the universal
three-matching class to two matching layers is known or claimed.  Theorems
`lba_eq_dlba_iff_acyclicDegreeTwoThreeMatchingLBA_subset_twoMatchingLBA` and
`lba_eq_dlba_iff_acyclicDegreeTwoThreeMatchingLBA_eq_twoMatchingLBA` state
exactly that the missing three-to-two class reduction is equivalent to the
open problem.

There is also an older checked structural bridge whose source class is known
to be far more restrictive than the successful marked compiler.
`Machine.ConfigurationBiUnique` says that the complete raw step relation is a
partial bijection at every width.  For such a machine,
`threeMatchings_hasTwoMatchingStepPartition_of_configurationBiUnique` reuses
the input/output phase split with only two colors: internal copy edges have
color zero and lifted source edges have color one.  Each color is a directed
matching, and the language and tape width are unchanged.  At class level,
`reversibleLBA_subset_twoMatchingLBA` gives

```text
ReversibleLBA ⊂ TwoMatchingLBA = DLBA
```

The strictness holds over every inhabited finite input alphabet.  The reason
is stronger than a mere gap between two definitions.  On a raw two-cell tape,
every enabled right-moving rule sends suitably chosen sources at the two right
positions to the same clamped target; the left-moving case is mirrored.
Therefore global cofunctionality forces every enabled direction to be
`stay`.  `Machine.languageEnd_iff_of_cofunctional` proves the resulting
input independence exactly: for any two canonical endmarker words, one is
accepted if and only if the other is, with no finiteness or nonemptiness
assumption on the machine's component types.

The class theorem `cofunctionalLBA_eq_trivial_languages` consequently
identifies globally cofunctional endmarker-LBA languages with
`{∅, Set.univ}`.  The reverse direction is not inferred from the collapse:
`Machine.trivialCofunctional` is an explicit transition-free one-state LBA,
and its false and true accepting bits recognize the empty and universal
languages.  `DLBA.Machine.trivialHalt` supplies the corresponding
transition-free deterministic witnesses, so
`cofunctionalLBA_subset_DLBA` proves the direct inclusion.  All three class
statements quantify over arbitrary finite terminal types, including the empty
type, and impose no cardinality lower bound.  They concern the repository's
literal complete raw clamped relation; they do not apply to cofunctionality
restricted to well-formed configurations or to an unclamped model.

Since `ReversibleLBA` additionally requires functionality, the checked theorem
`reversibleLBA_eq_trivial_languages` identifies that raw class with the same
two languages.

This does **not** say that the standard marked-tape notion of reversible
computation is trivial.  It says that the marked-tape theorem cannot be
inserted unchanged into a model whose structural promise quantifies over all
malformed clamped configurations.  Nor does the clamping collision collapse
`TwoMatchingLBA`: `is_AcyclicTwoMatchingLBA_firstSymbol` gives an exact raw
two-color presentation of the language “the first terminal is `chosen`.”  Its
two clamped incoming edges consume both colors and their common target is a
sink; the nonclamped target reads the first terminal and continues.  This is
the local pattern a general compiler must reproduce.

Two abstract ingredients of the completed deterministic route are useful in
their own right.  First,
`CanonicalPortSystem.euler_singleOrbit_on_basin` formalizes the Euler contour
theorem for every finite functional graph: cyclic rotation of incident edge
ends followed by the edge-end swap has one orbit on the backward basin of a
terminal vertex.  `eulerAccepts_iff_reaches` gives exact directed acceptance,
including sound rejection on components containing directed cycles, and the
accepting-set corollary does not require a preselected final configuration.
Second, `exists_two_directedMatching_partition_of_alternating` proves over an
arbitrary decidable vertex type that right uniqueness, indegree at most two,
terminal double merges, and a phase flipped by every edge suffice for an exact
two-directed-matching partition.  The theorem permits even cycles and handles
antiparallel pairs explicitly; its machine wrapper quantifies uniformly over
all raw tape widths.

The first concrete connection between those graph conditions and clamped head
movement is also checked.  `Machine.boundaryShuttle` expands an enabled
directional instruction into four microsteps: tag the departure cell, tag the
neighbor and return, restore the departure cell and move again, then restore
the neighbor.  `boundaryShuttle_configurationIndegreeAtMostTwo` and
`sink_of_two_distinct_predecessors_boundaryShuttle` quantify over every raw
tape.  At a clamped landing the state rereads the tag it just wrote, which is a
disjoint constructor from the symbol its row accepts, so the double merge is
terminal.  Every microstep flips the explicit phase, and
`boundaryShuttle_hasTwoMatchingStepPartition` consequently supplies the exact
two matching layers.  On a nonclamped semantic tape,
`reaches_boundaryShuttle_of_move` proves the intended four-step simulation and
exact final tape restoration.

Stationary instructions now have their own checked two-step protocol.
`stationaryShuttle_exact_two_steps_of_move` saves the complete stay
instruction in a private cell tag and then performs the write, with no head
movement or boundary premise.  Its raw relation is cofunctional exactly when
the target state together with the visible written symbol determines the
enabled stay instruction (`stationaryShuttle_cofunctional_iff`), and
`stationaryShuttle_hasTwoMatchingStepPartition` gives the resulting exact two
layers.  This theorem is deliberately standalone.  A shared-normal-state sum
must additionally prevent a directional final edge and a stationary final
edge from meeting at the same continuing target; `ShuttleTargetKindDisjoint`
records a sufficient source condition.

That sum is now checked as `Machine.combinedBoundaryShuttle`.  Its six raw
edge forms cover every enabled left, right, and stay instruction while keeping
all protocol tags disjoint.  Under source functionality,
`DirectionalTargetInjective`, `StationaryTargetWrittenInjective`, and
`ShuttleTargetKindDisjoint`, it has indegree at most two at every width and
every genuine double merge is terminal.  Every edge flips the shared phase,
so `combinedBoundaryShuttle_hasTwoMatchingStepPartition` supplies the exact
two layers.  The canonical theorems simulate stay instructions in two steps
without a boundary premise and directional instructions in four steps when
the physical move does not clamp.  These are sufficient normal-form
hypotheses for this synchronized protocol, not a claim that an arbitrary
reversible controller already has them.

The synchronized protocol now has a complete semantic theorem as well.
`CombinedShuttleRepresents` is an invariant of every raw run from a
plain/normal embedding.  Its first microedge already represents the source
successor; later microedges preserve that represented configuration.  If the
first directional edge clamps, the landing rereads its own departure tag and
cannot continue.  Hence `reaches_of_reaches_combinedBoundaryShuttle` reflects
normal-to-normal reachability with no functionality, injectivity, finiteness,
nonclamping, or width assumption.

Forward language simulation is supplied by the independent endmarker
invariant.  `EndmarkersIntact` holds for `loadEnd`, including the empty word,
and an `EndmarkerGuarded` table preserves both endpoints and points inward
there.  Thus every transition on a canonical-reachable tape is nonclamping,
and each source edge expands through the combined shuttle.  The theorem
`combinedBoundaryShuttleLanguageEnd_eq_languageEnd` combines this direction
with unconditional reflection.  Finally, `combinedShuttleEndEquiv` sends the
plain blank, terminals, old work symbols, and both markers to their canonical
`EndAlpha` constructors and sends every protocol tag to a disjoint work
constructor.  The transported theorem
`languageEnd_combinedBoundaryShuttleEndmarker_eq_source` is therefore exact
whole-language equivalence.  This semantic result does not remove the three
separate source-table hypotheses used for the raw two-matching proof.

The global finite-graph ordering in the first Euler theorem is no longer the
only checked port construction.  `LocalPort.ofMachine` gives every
direction-determinate graph walker the same finite ring
`{anchor, outgoing, incoming sourceState}` at every configuration.  An actual
incoming candidate is validated with exactly one opposite named memory move,
one neighboring observation, and one finite transition comparison.  Missing
candidates are fixed stubs, and `FixedStubRankedTree.eulerReaches_swap_parent`
proves that they do not disturb the contour induction.  After the standard
arrival-direction state lift, `directionLift_localEuler_iff_reaches` and
`directionLift_localEuler_accepting_iff` give exact terminal reachability and
acceptance for every finite memory graph.  The cyclic order is now only over a
fixed finite state/slot type, not over the input-dependent configuration
graph.

An Euler permutation can have odd cycles, so its own edges need not admit an
alternating two-coloring.  `PhaseDouble` adds one bit and flips it on every
edge.  The direct theorem
`phaseDoubledEuler_explicitTwoMatchingPartition` colors by the source bit and
partitions the doubled Euler relation into exactly two directed matchings.
It works for every bi-unique relation over an arbitrary vertex type, without
finiteness or decidable equality; each color is bi-unique and has no two
composable edges.  The projected terminal and accepting-set reachability
theorems show that this repair changes no semantic acceptance question.

The named tape operations are concrete as well.
`BoundedTapeMemory.graph` uses partial left/right successor positions instead
of `BoundedTape.moveHead`'s clamp.  A departure checks and rewrites the
current cell before moving; its named arrival inverse first returns to the
departure cell, checks the written symbol, and restores the old one.
`move_departure_reverse` proves their exact equivalence, and stationary
rewrites are paired by swapping their two symbols.
`BoundedTapeController.machine` translates an ordinary deterministic table
to these operations.  `step_iff_dlba_step_of_transitionNonclamping` is exact
when the enabled physical move stays inside the tape, while `reaches_sound`
holds without that premise.  Terminal acceptance is preserved under an
explicit source-table hypothesis; it is not silently imposed.

The whole semantic chain is now composed in `BoundedEulerBridge`.
`controller_reaches_iff_simulator_reaches` is two-sided from every canonical
input and has an arbitrary target: soundness projects controller steps, while
the converse uses the endmarker invariant at every deterministic prefix.
Terminal acceptance passes through the controller and the direction lift.
The final theorem `sourceLanguage_iff_phaseDoubledLocalEuler` states, for each
finite marker-free `(machine, acceptEmpty)` presentation and every word, that
language membership is equivalent to visiting an accepting endpoint in the
phase-doubled local Euler orbit.  This supplies the semantic specification
later implemented by the raw marked-Euler compiler.

The decisive raw tape calculation for refining an arrival operation is
isolated separately.  If the partial predecessor head exists,
`move_arrival_eq_raw_probe_success` proves that moving there and restoring the
old symbol is exactly the atomic arrival operation, while
`rawArrivalProbe_invalid_returns` proves that a failed local test can move
back to the target without changing any cell.  At a physical boundary,
however, `rawArrivalCandidate_eq_self_of_previousHead_eq_none` proves that the
first raw reverse move clamps to the identity.  Therefore the low-level
compiler has to detect and dispatch this blocked case before executing that
directional move; discovering it after the clamped step is too late.  The
marked compiler below uses an immutable boundary track for exactly this
dispatch.

`MarkedEulerProbe.rawMachine` now supplies that direct same-width boundary-safe
implementation without the synchronized shuttle's
`DirectionalTargetInjective` premise.  Every ordinary cell carries immutable
physical-boundary information.  A blocked direction is dispatched before a
physical move, an outgoing probe saves both touched cells, and an incoming
candidate either finishes at the genuine predecessor or restores the failed
candidate and returns to the target.  The final design retains every value
needed by a continuing tag-erasure edge; a hostile complete-raw-graph audit
found and eliminated two earlier forgeable erasures.

`RawTransitionCase` classifies all 25 nonempty table forms.  From a
well-boundary-coded canonical port, canonical simulation gives the exact
finite microstep path for each Euler branch,
including stationary, allowed departure, blocked departure, arrival, valid
incoming, invalid incoming, and anchor cases.  `FirstCanonicalReturn` and
`rawReaches_canonical_reflects_euler` prove that arbitrary raw runs between
canonical endpoints segment only into those genuine macros.  Boundary
correctness is invariant in both traversal directions, and initialization is
proved uniformly for all words, including the empty word's two-cell tape.

The complete structural audit does not rely on that canonical invariant.
`rawMachine_configurationIndegreeAtMostTwo` covers every one of the 14 raw
control families, every width (including width zero), and arbitrary malformed
tapes.  Exact canonical targets have at most one predecessor.  If any target
has two distinct predecessors,
`sink_of_two_distinct_predecessors_rawMachine` shows that one physical inverse
candidate clamped and the common landing is terminal.  Every raw row is
functional and every edge flips the explicit Boolean microphase.  Therefore
`rawMachine_hasTwoMatchingStepPartition` applies the alternating matching
criterion to obtain an exact width-uniform two-matching cover.

Finally, `languageEnd_rawMachine_deterministicSimMachine_eq` composes raw
simulation/reflection with the marker-free deterministic source presentation.
It has no nonempty-word side condition or cardinality lower bound.
`is_TwoMatchingLBA_of_is_DLBA` packages the finite work alphabet and state
types, yielding `DLBA_subset_twoMatchingLBA` and hence
`TwoMatchingLBA_eq_DLBA`.

At the usual complexity-class level, this deterministic direction is
motivated by
Lange, McKenzie, and Tapp's theorem that deterministic space has a reversible
simulation with the same asymptotic space.  Their linear-space construction
walks the finite deterministic configuration component reversibly, at an
exponential time cost.  Kunc and Okhotin later factor the same idea through
graph-walking automata: elementary memory operations are made explicitly
invertible, then a local finite-state controller backtracks the deterministic
walk.  Their marked-space Turing-machine specialization has no tape-space or
work-alphabet overhead.  This factorization identifies the right formal
interface here.  Those marked-space theorems by themselves do not establish a
property of every malformed configuration in a clamped raw machine; the
Langlib refinement above separately discharges exactly that stronger local
obligation.  None of these deterministic simulations selects a branch of an
arbitrary nondeterministic LBA.

The four-color theorem remains useful because it needs neither a finite graph
nor a global component traversal.  The optimal generic theorem instead
uses a spanning forest of the conflict graph and is correspondingly
noncomputable as currently stated; the separate serializer theorem is local
and uniform because its gadget phases already encode a valid coloring.

There is a genuine algebraic positive frontier when the layers have no
endpoints.  `generator_reaches_symmetric` proves that forward reachability
generated by any family of total permutations of a finite type is symmetric:
the inverse of each generator is a finite positive power of that same
generator.  Consequently
`generator_reaches_iff_symmetrized_reaches` reduces the relational question
to connectivity after reverse edges are made explicit.  Partial bijections
cannot in general be completed this way.  The one-edge relation
`OneWayEdge` is already `Relator.BiUnique`, but
`no_reachability_preserving_permutation_encoding_of_oneWay` rules out every
finite total-permutation encoding that may use auxiliary vertices and
multi-step gadgets while reflecting reachability between the original
vertices.  Chain endpoints, not merely failure to name inverses, retain the
directed information.

There is now an analogous sharp obstruction at the exact two-matching
boundary.  `reaches_comparable_of_incoming` proves, over arbitrary vertex
types, that once a vertex in an exact union of two directed matchings has an
incoming edge, every two vertices in its complete forward cone are comparable
by directed reachability.  The four-vertex relation `ThreeForkEdge` consists
of an edge into a junction followed by two terminal children.  Its three
edges have an explicit exact partition into three directed matchings, but the
children are incomparable.  Therefore
`threeFork_no_injective_allPairs_encoding_into_twoMatchings` rules out every
injective vertexwise encoding of this fork into an exact two-matching graph
that preserves and reflects reachability between all represented pairs.  The
target is allowed arbitrary auxiliary vertices and multi-step paths.

This does not rule out the open compiler.  A language transformation may be
specialized to the designated input source, represent the same source
configuration differently in different search contexts, and preserve only
existence of a path to an accepting set.  In particular, the theorem is a
barrier to canonical all-pairs state expansions, not a language-class lower
bound.

The strongest direct source-sensitive repair is to unfold the configuration
graph into the tree of complete simple path histories.  It duplicates every
merge, so each nonroot history has a unique predecessor and an ordinary
deterministic contour can backtrack through all choices.  Cycles do not need
to be excluded: a finite accepting walk can be loop-erased before it is
represented.  The relational core of that observation is now checked
independently:
`weakReaches_root_iff_reaches` says that for any cofunctional relation whose
designated root has no predecessor, weak connectivity from the root is
exactly forward directed reachability.  It needs neither finiteness nor
acyclicity.  `accepts_iff_weakReaches` proves that the finite exhaustive
reversible port schedule visits exactly a weak component, and
`accepts_iff_reaches_of_cofunctional_root` therefore gives exact forward
target reachability in the rooted cofunctional case without requiring a
terminal target.

The history construction itself is also checked.  A `History` retains its
duplicate-free vertex sequence as data, not as a proof of reachability.
`History.extension_leftUnique` and `History.root_no_predecessor` give the
rooted cofunctional tree, while `History.edge_endpoint_of_extension` projects
each extension to a genuine source edge.  Conversely,
`exists_history_endpoint_of_reaches` performs directed loop erasure, so
`reaches_iff_exists_history` preserves and reflects reachability from the
designated source for an arbitrary relation, including a cyclic one.  No
finiteness premise is needed for that equivalence.  When the base vertex type
is finite, the type of simple histories is finite and
`visits_length_add_one_le_card` bounds each history length by the base
cardinality; there is no cardinality lower-bound hypothesis.

Finally, `sourceReachability_exact_twoMatching_phasePresentation` composes the
finite history tree with canonical edge-end ports and the exhaustive
reversible schedule.  For every finite graph, source, and accepting
predicate, its scheduled phase line visits an accepting endpoint exactly when
the original graph reaches one.  Coloring a line edge by the parity of its
source phase gives an exact two-layer partition; both layers are bi-unique
and contain no two composable edges.

The last relation is the unary phase line of one precomputed schedule, with
`portAt` labeling its phases.  It is not an injective embedding of source
vertices, and it preserves only the designated source's existential
acceptance question.  Its history type, canonical port order, phase type, and
schedule depend on the complete finite instance and use finite choice.  Thus
it is a nonuniform semantic finite presentation, not an effective graph
reduction, an automaton, or a same-width LBA compiler.  Applied to an LBA
configuration graph, this instance dependence includes the input word, so it
does not define one fixed machine recognizing the language.  This
source-sensitive duplication is also why it does not contradict the
all-pairs three-fork obstruction above.

The phase-line cost of this particular construction is not merely
qualitative.  `phaseOfHistory_injective` chooses, for every rooted history, a
visited phase whose represented port endpoint recovers that history; distinct
histories therefore require distinct phases.  The general bounds
`card_history_le_card_phase` and
`card_history_le_actions_length_add_one` apply to every finite base type
without a lower-cardinality premise.  On the `k`-diamond chain,
`twoPow_le_card_historyPhase` forces at least `2^k` phases and
`twoPow_sub_one_le_historyActions_length` forces at least `2^k-1` actions in
the actual exhaustive schedule.  If all those phases are injectively stored
as width-`W` rows over a finite alphabet `A`,
`historyPhases_le_rowCapacity_of_injective` further forces
`2^k ≤ |A|^W`.  These are lower bounds for the checked nonuniform history-port
presentation, not for every effective or recomputing reduction.

The cost is that the return stack has moved into the vertex representation.
The minimal merge leak for contouring the original graph is
`r -> m <- u -> a`: its undirected symmetrization is a tree connecting `r`
to `a`, while no directed path goes from `r` to `a`.  Remembering only the
last port can identify the current merge entry, but after descending below a
later merge it has overwritten the parent needed to resume the earlier fork.
At the end of a `k`-diamond chain, `card_stPaths` gives `2^k` distinct complete
path contexts even though all of them project to the same configuration.
`historyOfPath_injective` now connects those data to the construction above:
every explicit diamond path gives a distinct value of the actual rooted
`History` type.  Consequently `twoPow_le_card_history` proves that the history
type has at least `2^k` elements.  If a literal history unfolding represents
every such value by one width-`W` row over a fixed alphabet `A`,
`histories_le_rowCapacity_of_injective` forces
`2^k ≤ |A|^W`; `not_injective_histories_of_capacity_lt` formalizes the
contrapositive.  These statements also cover zero widths and empty row
alphabets.  Thus, whenever `2^k > |A|^W`, they block literal same-width
history materialization; they do not rule out recomputing context or a
different collective search algorithm.

Nor can the lost parent simply be selected by asking which continuation will
succeed.  `first_successful_child_decides` makes that circularity exact: the
first successful child characterizes reachability, while its ordered-fork
companion preserves acyclicity and the exact two-partial-bijection hard core.
Such pruning has performed the directed-reachability decision that the
compiler was supposed to implement.

These port theorems are semantic finite-graph results, not a new LBA-class
inclusion.  Langlib's global `Machine.Cofunctional` promise ranges over every
raw clamped configuration.  The exact theorems
`Machine.languageEnd_iff_of_cofunctional` and
`cofunctionalLBA_eq_trivial_languages` prove that such acceptance is
input-independent and that the finite-terminal language class is precisely
`{∅, Set.univ}`; `cofunctionalLBA_subset_DLBA` uses explicit transition-free
deterministic witnesses.  A useful nontrivial moving compiler would instead
need cofunctionality only on its well-formed rooted encodings, plus a raw
protocol whose malformed configurations satisfy the required two-matching
conditions.

There is a different positive frontier when the number of paths in a directed
edge decomposition is bounded.  Given an `N`-vertex graph whose edges are
supplied as the union of `p` directed paths, keep the earliest known reachable
position on each path.  Whenever a reachable suffix of one path intersects
another path, move the latter's marker to its earliest such intersection.
Every marker moves monotonically toward that path's source, expanding its
reachable suffix, and at the fixed point the marked suffixes are exactly the
reachable vertices.  This uses `O(p log N)` space and polynomial time, as in
Theorem 2.1 of [Bhadra and Tewari, *Trading Determinism for Time: The k-Reach
Problem* (version 2)](https://arxiv.org/pdf/2409.18469v2).

The parameter `p` here counts supplied whole paths, not partial-bijection
layers.  Splitting a linear forest into its connected components turns it into
such a path list, but `p` can then be linear in `N` even when the forest came
from one of only two or four layers.  Conversely, if the entire edge set is
actually supplied as a union of a constant number of whole paths, Theorem 2.1
does give deterministic `O(log N)` space.  This is fully consistent with the
two-linear-`2`-diforest hardness result: its two layers may contain linearly
many paths of length at most two.

For a finite DAG the minimum number of paths in an edge partition also has
the elementary formula

$$
p(G)=|E|-\sum_v\min(d^-(v),d^+(v))
    =\sum_v\max(d^+(v)-d^-(v),0).
$$

Pair the `j`-th incoming edge with the `j`-th outgoing edge at each vertex;
acyclicity makes the resulting components directed paths, and no decomposition
can make more than `min(d^-,d^+)` such continuations at a vertex.  This direct
argument is independent of the older arXiv version, whose minimal-DAG-path
statement is not present in version 2.

Langlib now formalizes the full minimization statement in a successor-link
representation.  An `EdgePathPartition edge` assigns each edge occurrence an
optional next edge.  A link must join adjacent occurrences, two occurrences
cannot link into the same successor, and the successor relation is acyclic;
`existsUnique_start_reaches` proves the representation adequate by placing
every occurrence on a successor chain from exactly one predecessor-free
start.  Its `pathCount` is the number of those starts.  For every such
partition,
`card_edges_sub_sum_min_le_pathCount` and
`sum_outdegree_sub_indegree_le_pathCount` prove the two lower bounds above.

For an acyclic relation, `canonicalPathPartition` turns the existing local
incoming/outgoing pairing into an `EdgePathPartition`.
`canonicalPathPartition_pathCount_eq_minimumPathCount` proves it optimal, and
`minimumPathCount_eq_card_edges_sub_sum_min` together with
`minimumPathCount_eq_sum_outdegree_sub_indegree` gives both displayed closed
forms for the actual minimum over every successor-link partition.  These
theorems quantify over arbitrary finite vertex types, including the empty
type, with no cardinality lower bound.  They remain finite combinatorics: no
uniform path enumerator or same-width `DLBA.Machine` compiler is claimed.

Consequently, a paper-level DLBA simulation follows under the exact global
promise that, for one fixed acyclic LBA, there is a constant `p` such that the
**entire** width-`W` configuration graph has `p(G) ≤ p` for every `W`, and
that its canonical paths can be enumerated uniformly in linear space.  The
`p` path markers then occupy a constant number of configuration tracks and
the polynomial-in-`N` relaxation terminates within exponential time in `W`.
This is not yet a concrete Langlib machine theorem.  A bound only on an
unknown reachable subgraph would be circular, and a decomposition into a
constant number of linear forests is weaker because each forest may have
unboundedly many components.  The frontier is nevertheless nontrivial: a
`k`-diamond chain with `k ≥ 1` has `p(G)=2` while retaining `2^k`
source-to-target paths.  Conversely, directed degree two gives no bound on
`p(G)`: for `k ≥ 1`, a full binary tree of depth `k` is acyclic with indegree
at most one and outdegree at most two, but the displayed imbalance formula
gives `p(G)=2^k`.  The root contributes two, and every nonroot internal
vertex contributes one.

## Two single-valued boundaries

The [functional LBA conversion](functional-lba-dlba.html) proves a full
machine-level determinization when each state/symbol pair has at most one
outgoing move.

The theorem `Machine.accepts_iff_exists_backtrack_le_card` studies the
abstract finite-graph restriction in which every bounded configuration has at
most one predecessor.  It proves that reachability is equivalent to following
this unique predecessor for at most the number of bounded configurations, and
`acceptsByExhaustiveBacktracking` packages exhaustive target enumeration and
bounded backtracking.  The accompanying resource argument preserves the input
and current configuration on fixed tracks, enumerates accepting targets, and
finds a predecessor by enumerating configurations.  A target configuration, a
predecessor candidate, and a counter up to

$$
|\Lambda|\,|\Gamma|^n n
$$

all use `O(n)` bits, so a constant number of packed tracks still occupies the
original linear bound.  As above, the two endmarker columns are folded into
the marker-free nonempty input using `n + 2 ≤ 3n`, and the empty word is set
by the explicit bit.  The formal development proves the finite-search
semantics; `card_cfg_lt_fuelCapacity` supplies the same-width configuration
and fuel-capacity inequality, and `sameWidthWitness_iff_accepts` joins these
facts into an exact same-width witness specification.

Those semantics and capacity lemmas are useful as an abstract
unique-predecessor interface, for example if a future compiler can enforce the
promise only on well-formed encodings.  They are not needed to decide the
repository's actual globally cofunctional raw-machine class.
`not_cofunctional_of_mem_transition_left` and its right-moving analogue show
that clamping gives every enabled directional instruction two predecessors of
one raw target; hence global raw `Machine.Cofunctional` forces every enabled
direction to be `stay`.  More than this structural inference is now checked:
`Machine.languageEnd_iff_of_cofunctional` proves exact input independence,
`cofunctionalLBA_eq_trivial_languages` identifies the class with
`{∅, Set.univ}`, and `cofunctionalLBA_subset_DLBA` uses explicit
transition-free witnesses for its deterministic inclusion.  These class
results hold for every finite terminal type, including the empty type, with no
cardinality lower bound.  Nested target/predecessor enumeration sweeps are
therefore unnecessary for that actual raw-clamped class, and the resource
lemmas do not claim a concrete `DLBA.Machine` implementing the more abstract
search.

These results isolate two different issues:

- functional machines have no forward path choice and directly become DLBAs;
- abstract finite unique-predecessor relations admit bounded target
  enumeration and backward-following semantics with same-width resource
  bounds; the repository's globally raw-cofunctional class is exactly
  `{∅, Set.univ}` by `cofunctionalLBA_eq_trivial_languages`;
- exact-two-matching machines may branch initially, but cannot branch again
  along the chosen path; the checked scheduler determinizes this finite union
  of pinned initial branches;
- allowing both multiple successors and multiple predecessors leaves the full
  directed-reachability problem.

This local unique-predecessor condition is different from a global
unambiguity promise.  For comparison, Allender and Lange's classical
algorithm for reach-unambiguous graphs uses

$$
O(\log^2 N/\log\log N)
$$

space on an `N`-vertex graph.  For an LBA configuration graph with
`N = 2^{Theta(n)}`, that is `O(n²/log n)`, still superlinear.  More recent
few-path results give quantum `O(log N)` space only under the stronger promise
that, for every vertex `v`, both the number of paths from `s` to `v` and the
number from `v` to `t` are polynomial in `N`.  This becomes quantum `O(n)`,
not deterministic `O(n)`.  Acyclicity and degree two do not imply the promise:
bounded-degree `N`-vertex DAGs can still contain exponentially many directed
paths.  The theorem `diamondChain_obstruction` formalizes the sharp elementary
witness: a `k`-diamond chain has `3k+1`
vertices, is acyclic with both directed degrees at most two, and has exactly
`2^k` explicit source-to-target paths.  Moreover `edgeLayer_exact` and
`edgeLayer_biUnique` give the chain an exact two-partial-bijection partition.
Thus exponentially many color sequences survive even in the newly isolated
normal form.  These layers are not directed matchings: every diamond creates
another branch later on the same path, which the exact two-matching promise
forbids.  The exact path count is separately exposed by `card_stPaths`.

One announced result cannot currently be used to improve that bound.  The
[STOC 2026 accepted-papers
page](https://acm-stoc.org/stoc2026/accepted-papers.html) lists *Reach
Unambiguous Logspace is almost in Logspace* by Arvind and Datta, but the item
does not appear in the conference's [final
program](https://acm-stoc.org/stoc2026/stoc26-program.html) or [published
proceedings](https://doi.org/10.1145/3798129), and the listing supplies neither
a manuscript nor a quantitative theorem statement.  Consequently this page
does not infer a space bound from its title.  Even a verified
`O(log N * f(N))` bound with a monotone unbounded factor `f` would become
`O(n * f(2^{Theta(n)}))`, not deterministic linear space, after the LBA
substitution.

A 2025 isolation preprint, revised in 2026, is also easy to overstate from an
older abstract.  In version 3, Arvind, Chakraborty, and Datta place `NL` in a
polynomial-time catalytic class with `O(log N)` base workspace and
`O(log^{2-alpha} N)` catalyst, but with an unambiguous polynomial-time oracle
using `O(log^{1+alpha} N)` space, for
`0 ≤ alpha ≤ 1/2`.  On LBA graphs these become `O(n)`,
`O(n^{2-alpha})`, and `O(n^{1+alpha})`; the theorem yields no choice of
`alpha` for which all three advertised bounds are linear.  The oracle is part
of what this theorem proves and cannot be dropped when citing the containment;
this is not a theorem that every possible catalytic approach needs such an
oracle.

## Why algebraic path counting stops short

The explicit clock makes the hard graph a DAG, so it is natural to try
counting instead of searching.  If `A` is the adjacency matrix of an
`N`-vertex DAG in topological order, then `A^N=0` and, over the integers,

$$
((I-A)^{-1})_{s,t}
  =\sum_{j=0}^{N-1}(A^j)_{s,t}
$$

is the number of directed paths from `s` to `t` (for distinct endpoints).
Put `B=I-A`.  Since `det(B)=1`, the same count is the transposed signed
cofactor

$$
C_{t,s}=(-1)^{s+t}\det(B_{\widehat t,\widehat s}),
$$

where row `t` and column `s` are deleted.  This identity does not make the
value small.  The formally verified
`card_stPaths` theorem gives `2^k` paths for the `3k+1`-vertex diamond chain,
so an exact count can require `Theta(N)` bits even with acyclicity and both
degrees at most two.  At
`N=2^{Theta(n)}`, that is exponentially many bits in the LBA input length.

Large integers are not the only obstruction.  In topological order, set the
source bit to one and each other reachability bit to the OR of its at most two
predecessor bits.  This is a bounded-fan-in monotone Boolean circuit, and the
arithmetic identity `a OR b = a + b - ab` keeps every intermediate value in
`{0,1}`.  Evaluating its target bit is nevertheless exactly the original
directed-reachability problem.  Thus bounding the numerical value removes the
path-count storage issue but not the exponentially wide dependency graph.

This is a storage obstruction to exact dynamic programming, not a lower
bound against modular arithmetic.  Counts below `2^{O(N)}` could in principle
be zero-tested modulo enough `O(log N)`-bit primes, reusing the same workspace.
The missing operation is even deciding in deterministic `O(log N)` space
whether each residue is nonzero.  For a fixed modulus, this decision problem
captures the corresponding `Mod_p L` class (and parity gives `⊕L`).  Here
the prime varies with the loop, so the method needs one uniform residue
procedure taking `p` as input.  Once those residues are available, standard
Chinese-remainder conversion to binary is itself logspace; it does not supply
the missing residue procedure.  Edenhofer's 2026 catalytic walk-counting
algorithm makes this distinction explicit: it performs the conversion in
logspace but retains `O(N log² N)` catalytic bits to compute the residues.
Layering and binary branch/merge gadgets do not remove that counting
difficulty.  See the
original modular-logspace developments of
[Damm](https://doi.org/10.1016/0020-0190(90)90150-V) and
[Buntrock, Damm, Hertrampf, and
Meinel](https://doi.org/10.1007/BF01374526), and
[Edenhofer](https://arxiv.org/abs/2602.21088).

Two February 2026 catalytic tradeoffs improve the explicit-graph frontier but
still miss the LBA resource target after substitution.  Edenhofer's general
parameter `k` uses

$$
O(\log N\log k+\log N)
\quad\text{ordinary bits and}\quad
O((N/k)\log^2 N)
\quad\text{catalytic bits}.
$$

At `k=N` both advertised quantities become `O(log² N)`; keeping the first at
`O(log N)` instead leaves an exponentially large catalyst when
`N=2^{Theta(n)}`.  Chmel, Dudeja, Koucký, Mertz, and Rajgopal give a
polynomial-time directed-connectivity algorithm with `O(log N)` ordinary
workspace and

$$
N/2^{\Theta(\sqrt{\log N})}
$$

catalytic bits.  On an LBA configuration graph this is
`2^{Theta(n)-Theta(sqrt(n))}`, still far above linear space.  Moreover a
catalyst is an additional initially arbitrary memory required to be restored;
it is not an ordinary `O(n)` DLBA tape.  Thus neither theorem supplies the
missing determinization.  See [*Frontier Space-Time Algorithms Using Only Full
Memory*](https://arxiv.org/abs/2602.21089).

Exact DAG path counting is `#L`-complete, while integer determinant is
complete for `GapL`.  Logspace-uniform `NC²` determinant and matrix-powering
methods give the familiar `O(log² N)` deterministic-space scale, not
`O(log N)`; on LBA graphs this is again quadratic rather than linear space.
Thus the cofactor formulation relocates the reachability information but does
not compress its computation.  See
[Álvarez and Jenner](https://doi.org/10.1016/0304-3975(93)90252-O) and
[Mahajan and Vinay](https://eccc.weizmann.ac.il/eccc-reports/1997/TR97-036/index.html).

Isolation has a related uniformity cost.  Reinhardt and Allender prove
`NL/poly = UL/poly`, but the advice is nonuniform and polynomial in the
explicit input length.  For a standard `N`-vertex graph encoding this allows
`N^{O(1)}` advice, which can be exponential in an LBA width.  Van Melkebeek
and Prakriya prove the precise containment
`NL ⊆ UTISP(poly(N), O(log^{3/2} N))`; after substitution its unambiguous
workspace becomes `O(n^{3/2})`, not deterministic linear space.  Even perfect
logspace isolation would first place the problem in `UL`; `UL = L` remains
open.  See [Reinhardt and
Allender](https://doi.org/10.1137/S0097539798339041) and [van Melkebeek and
Prakriya](https://doi.org/10.1137/17M1130538).

The linear-space version separates two still-unresolved tasks.  Writing

$$
D=\mathrm{DSPACE}(O(n)),\qquad
U=\mathrm{USPACE}(O(n)),\qquad
N=\mathrm{NSPACE}(O(n)),
$$

one always has `D ⊆ U ⊆ N`.  Disambiguation asks for `N ⊆ U`; removing
the remaining unique accepting choice asks for `U ⊆ D`.  Li, Pyne, and Tell
obtain `NSPACE(O(n)) = USPACE(O(n))` under their stated uniform exponential
circuit-hardness hypothesis ([Theorem
6.4](https://eccc.weizmann.ac.il/report/2024/139/download)).  Doron, Pyne,
Tell, and Williams replace this by a stated hardness hypothesis against
uniform polynomial-size oracle circuits ([Theorem
6.12](https://eccc.weizmann.ac.il/report/2025/077/download)).  These are
conditional disambiguation theorems, not unconditional simulations.  Even
granting either hypothesis settles only `N ⊆ U`; the inclusion `U ⊆ D`
remains the scaled-up analogue of the open `UL ⊆ L` problem.  The 2026
[low-space hardness-versus-randomness
survey](https://eccc.weizmann.ac.il/report/2026/045/) records a cleaned
combined conditional form and does not claim an unconditional linear-space
disambiguation.

The checked unambiguous-run development makes this factorization precise in
the canonical endmarker model.  `Machine.AcceptingRun` stores every chosen
transition triple as data; it does not try to distinguish proofs of the
propositional `Reaches` predicate.  This distinction also preserves two
different moves that happen to produce the same clamped-boundary
configuration.  Runs stop at their first accepting configuration, and
`nonempty_acceptingRun_iff` proves
that existence of such a run is exactly the repository's existing LBA
acceptance predicate.  Functional transition tables have a subsingleton type
of accepting runs by `acceptingRun_subsingleton_of_functional`.

The class theorems then prove, over every finite input alphabet,

$$
\mathrm{DLBA}\subseteq\mathrm{ULBA}\subseteq\mathrm{LBA}.
$$

The first inclusion is `DLBA_subset_ULBA`; the second is
`ULBA_subset_LBA`.  Finally,
`lba_eq_dlba_iff_lba_subset_ulba_and_ulba_subset_dlba` proves the
unconditional exact factorization of the first LBA problem into `LBA ⊆ ULBA`
and `ULBA ⊆ DLBA`.  Under a supplied disambiguation hypothesis, the
corollary `lba_eq_dlba_iff_ulba_subset_dlba_of_lba_subset_ulba` leaves exactly
the second inclusion.  Neither of these reverse inclusions is assumed or
inferred from the recent conditional literature in the checked development.

Immerman--Szelepcsényi counting avoids the large-output problem by counting
reachable *vertices*, a number at most `N` and therefore representable in
`O(log N)` bits.  Its inductive count is certified with nondeterministically
guessed reachability witnesses.  That is exactly why it proves
nondeterministic complement closure without providing deterministic
reachability.

## Why a countable-union diagonalization fails

A recurring separation attempt builds an increasing family

$$
L_3\subseteq L_4\subseteq\cdots
$$

and proves each fixed `L_i` lies in nondeterministic linear space by using a
stage-dependent compressed machine.  It then concludes that the union lies in
the same class.  That conclusion is invalid: a language class need not be
closed under countable increasing unions, and the stage machines do not by
themselves supply one uniform finite machine.

The theorem `CS_notClosedUnderMonotoneCountableUnion_of_card` formalizes a
particularly strong counterexample.  Over every nonempty finite alphabet
there is a monotone sequence `F n` such
that:

- every `F n` is finite, hence context-sensitive;
- the union is recursive;
- the union is not context-sensitive.

Take a recursive non-context-sensitive language `L` and let

$$
F_n=\{w\in L:|w|\le n\}.
$$

Then `F_n` is finite and increasing, but its union is exactly `L`.
The family is even uniform in the ordinary computability sense: one algorithm
decides `(n,w) ∈ F` by deciding `w ∈ L` and comparing `|w|` with `n`.

This is the unresolved uniformity defect in version 22 of Tianrong Lin's
preprint.  Its fixed stage `L_d^i` is compressed with an alphabet and state
space depending on `i`; Theorem 4.3 then passes from all fixed stages to their
union without constructing a single finite machine.  Packing an `i`-dependent
number of source cells into one target cell is legitimate for each fixed `i`,
but not uniformly for unbounded `i`.  See [Lin's current
preprint](https://arxiv.org/abs/2110.05942v22) and [Preu's analysis of the
earlier versions](https://arxiv.org/abs/2110.12421).

Precisely, the compression establishes
`∀ i, ∃ M_i, L(M_i) = L_d^i`.  Theorem 4.3 needs a single machine satisfying
`∃ M, L(M) = ⋃ i, L_d^i`.  The first statement does not imply the second, and
version 22 constructs no such uniform `M`.

The same nonuniform dependence is visible before the staged reformulation.  On an
input encoding a target machine with `t` tape symbols, Lin's universal
simulator explicitly allocates

$$
(1+\lceil\log t\rceil)S(n)
$$

cells for the simulated tape.  For each fixed target, `t` is a constant, but
over all encoded targets it is unbounded as a function of the simulator's
input.  Tape compression can replace that factor only by choosing a new tape
alphabet depending on the fixed bound on `t`; it does not construct one
finite-alphabet machine uniform over every `t`.

The static capacity obstruction remains even if one fixes an arbitrary positive
linear expansion factor `c`.  If the source and target tape alphabets are `A`
and `B`, respectively, and

$$
|B|^c<|A|,
$$

then `exists_length_no_injective_boundedTape_to_linearlyExpandedCfg` produces
a tape length at which no injection exists from source bounded tapes into
target configurations with `c` target cells per source cell and any one fixed
finite target state set.  The theorem
`exists_fin_no_uniform_affineExpansion_boundedTape_encoding` chooses such a
finite source alphabet for every fixed target alphabet, state set, `c`, and
fixed additive cell allowance.  Thus no fixed target alphabet together with
one affine cell bound yields a configuration-by-configuration universal
encoding over all source alphabets.
This is an information-capacity barrier for direct injective simulations, not
a lower bound against a semantic language simulation and not an LBA--DLBA
separation.

The deficit is not confined to unreachable source configurations.  For every
fixed finite nonempty digit alphabet `A`, a deterministic LBA can use its
width-`n` tape as a base-`|A|` odometer and visit all `|A|^n` digit rows on one
trajectory before overflow.  Hence any faithful step-by-step simulation that
uses a decodable target-configuration encoding at every checkpoint must be
injective on an orbit of that size.  The same inequality defeats a target
alphabet `B` with a fixed `c`-cell block whenever `|B|^c < |A|`.  A semantic
shortcut may decide the eventual acceptance bit without representing those
checkpoints, so this strengthening is still not a language lower bound.

The most direct attempts to replace a stored row by a semantic certificate
still encounter the same information at a different interface.  Streaming two
successive rows verifies one local edge in constant auxiliary space, but the
next edge must reuse exactly the row just emitted.  Re-guessing it permits
false splices between unrelated locally valid edges; retaining it is the
original per-cell cost.  A short modular fingerprint is not an exact
commitment, and checking many moduli sequentially has the wrong quantifiers:
the guesses can establish `forall p, exists row_p`, while sound path
composition needs `exists row, forall p`.  Keeping all residues at once
restores the missing information.  Savitch-style midpoint certificates have
the analogous sharing problem: the second recursive half must recover the
same full midpoint, and determinism of the source gives no generic compact
method to recompute its bits.  These observations rule out the literal
streamed-tableau, fingerprint, and midpoint adaptations; they do not exclude a
different semantic simulation.

The failure is sharp at every fixed alphabet bound.  Feldman and Owings
construct a universal LBA for each fixed bound on the simulated tape alphabet
and derive a proper alphabet hierarchy.  In modern terminology, for every
fixed `m`:

- some DLBA language is not recognized by any DLBA whose tape alphabet has at
  most `m` symbols;
- some LBA language is not recognized by any LBA whose tape alphabet has at
  most `m` symbols.

The second formulation uses the now-known closure of context-sensitive
languages under complement.  These are separate witnesses depending on `m`;
the theorem does not produce one language outside all finite alphabet bounds
and therefore does not separate LBA from DLBA.  See [Feldman and
Owings](https://doi.org/10.1016/0020-0255(73)90036-4).
Seiferas later proved corresponding fixed-work-alphabet hierarchies for
general fully constructible deterministic and nondeterministic space bounds;
see [*Techniques for separating space complexity
classes*](https://doi.org/10.1016/S0022-0000(77)80041-X).

Padding the same diagonal word does not uniformize this argument.  If one
source cell needs `k_M > 1` cells over a fixed universal alphabet, simulating
a candidate on the same diagonal word `z` requires `k_M |z|` cells.  Padding
`z` also lengthens the candidate's simulated input, leaving the same
impossible inequality `|z| ≥ k_M |z|`.  Running the candidate only on a
shorter payload inside a padded word avoids the capacity problem, but then the
diagonal comparison is with `M(payload)`, not with `M(padded-word)`; an
arbitrary candidate need not ignore the padding.

Making the proposed diagonal language padding-invariant does not close this
gap.  Under the assumption that `M` decides that language, equal language bits
would indeed imply equal outputs on a payload and its padding.  But the fixed
diagonal machine must also compute the bit on the shorter representative.
Deferring that computation to a still shorter representative eventually
reaches a base case that has not been diagonalized.  Closing the dependencies
in a finite cycle of nonempty representatives is arithmetically impossible
for a direct simulation: every edge that uses padding to absorb a factor
`k_i > 1` requires
`|z_i| ≥ k_i |z_{i+1}|`, and multiplying the inequalities around the cycle
would give $|z_i|\ge(\prod_j k_j)|z_i|$.  This rules out that literal
padding-invariance repair, not every possible semantic diagonalization.

Sparse diagonal lengths and self-reference do not change that arithmetic for
a direct simulation.  If the proposed diagonal machine carries `C` bits of
configuration information per input cell and candidate `M_i` carries `c_i`, a
same-word encoding needs

$$
C n_i \geq c_i n_i+O_i(1).
$$

Taking `n_i` very large absorbs the machine-specific additive term, but gives
no solution when `c_i>C`.  Restricting every work alphabet to binary merely
moves `c_i` into the machine-specific number of binary cells per simulated
cell.  A recursive padded wrapper has the same conservation law: if
`|z|=r|x|` and a wrapper on `x` directly packs the `z`-tape of a machine with
alphabet `Gamma`, its cell alphabet needs at least `|Gamma|^r` values.
Re-encoding that wrapper over alphabet `B` on the padded word costs
`r log_B|Gamma| |x| = log_B|Gamma| |z|` cells, so the padding ratio cancels.

Seiferas's resource-bounded recursion theorem does not evade this point.  His
Lemma 1 is explicitly internal to one fixed pair `(m,l)` of work-alphabet size
and head count.  Moreover, the recursive-padding separation in his Theorem 7
requires genuine space slack,

$$
S_0(n)-S(n+f(n)) \geq 4\log_m n.
$$

For the same linear bound `S_0(n)=S(n)=n`, the left side is `-f(n)`.  Thus the
theorem strengthens hierarchies between distinct resource bounds; it neither
uniformizes unbounded alphabet sizes nor separates nondeterministic and
deterministic linear space.  See [*Techniques for Separating Space Complexity
Classes*](https://doi.org/10.1016/S0022-0000(77)80041-X), Lemma 1 and Theorem
7.

All of these are direct-configuration or direct-step simulation barriers, not
a semantic lower bound.  The distinction is visible in Seiferas's companion
paper.  Its Theorems B-2-N and B-2-D give, at linear space, respectively
nondeterministic-to-nondeterministic and deterministic-to-deterministic
fixed-work-alphabet hierarchies.  The additional cross-type conclusion in
B-2-D—a deterministic language outside `NSPACE(S_0,m)`—is stated only under
`S_0(n)=o(log n)`, so it does **not** apply to `S_0(n)=n`.  Consequently the
classical hierarchy results do not rule out a genuinely semantic,
nondeterministic recomputation method for deterministic high-alphabet source
machines.  Constructing such a method uniformly enough to perform the
diagonalization would be a new missing theorem, while excluding it would
require more than the counting argument above.  See [*Relating Refined Space
Complexity Classes*](https://doi.org/10.1016/S0022-0000(77)80042-1), Theorems
B-2-N and B-2-D.

## What relativization does and does not show

Oracle evidence for space must be read with the query-tape convention made
explicit.  In the unrestricted Ladner--Lynch model, the query tape is not
charged to space and a nondeterministic machine may generate its query
nondeterministically.  They construct one computable oracle collapsing
`L`, `NL`, `P`, and `NP`.  Separately, for every fixed polynomial `p`, they
construct a possibly `p`-dependent computable oracle `A_p` such that

$$
NL^{A_p}\not\subseteq SPACE^{A_p}(p(n)).
$$

Taking `p(n)=n` already separates relativized linear space.  The unrestricted
query convention admits oracles violating relativized Savitch, and Hartmanis,
Chang, Kadin, and Mitchell show that it can also violate relativized
complement closure: exponentially many polynomial-length queries can be
chosen nondeterministically without being represented in charged workspace.
It is therefore not a clean black-box barrier for the ordinary LBA problem.
See [Ladner and Lynch](https://groups.csail.mit.edu/tds/papers/Lynch/mst76.pdf)
and [Hartmanis, Chang, Kadin, and
Mitchell](https://userpages.cs.umbc.edu/chang/papers/log/l-book.pdf).

Space-faithful oracle models behave differently.  If query length is bounded
by workspace, or if query generation must itself be deterministic, Hartmanis,
Chang, Kadin, and Mitchell prove that `L = NL` if and only if, for every
oracle `A` and every constructible `s(n) ≥ log n`, deterministic and
nondeterministic relativized `s(n)` space coincide.  For constructible
`s(n) ≥ n`, a separating oracle in either controlled model exists if and only
if `L ≠ NL`; a PSPACE-complete oracle supplies a collapse.  Thus producing a
controlled relativized linear-space separation would already solve `L`
versus `NL`, rather than merely demonstrate that a future proof must be
nonrelativizing.

## The unary two-way one-counter formulation

Monien proved a striking equivalent formulation.  The first LBA problem has a
positive answer if and only if every unary language accepted by a
nondeterministic two-way one-counter automaton, with a linearly bounded
accepting witness, is decidable in deterministic logarithmic space.
Restricting to the promised witnesses whose counter stays at most `n` gives a
finite graph with `Theta(n²)` vertices; the ordinary machine still has an
unbounded counter and an infinite full configuration graph.  Directed
reachability in that bounded witness graph retains the full difficulty of the
LBA question.  See [Monien's 1977
paper](https://digital.ub.uni-paderborn.de/hsx/download/pdf/42059).

The promise in this theorem is precise and easy to misread:

- the ordinary language of the automaton must be exactly `L`, so every
  accepting run counts;
- for every word in `L`, at least one accepting run keeps the counter at most
  the input length.

Acceptance is not redefined by discarding high-counter runs.  Monien first
identifies nondeterministic logarithmic space with a union of bounded
multi-counter models and then compresses those counters into one counter after
a polynomial, injective transformation of the unary input.

Three independent restrictions collapse this unary model all the way to
regular languages:

1. **A fixed number of counter reversals.** Ibarra, Jiang, Tran, and Wang prove
   that unary languages of two-way nondeterministic reversal-bounded
   multicounter machines are effectively regular, even without a counter
   height bound or an input-head reversal bound.  See the [journal
   version](https://doi.org/10.1137/S0097539792240625).
2. **No explicit counter-zero test.** For two-way one-counter *nets*,
   decrements are merely disabled at zero.  Almagor, Cadilhac, and Yeshurun
   prove that every unary language of such a machine is effectively
   semilinear, hence regular.  See [Theorem 9 and its unary
   consequence](https://drops.dagstuhl.de/storage/00lipics/lipics-vol326-csl2025/LIPIcs.CSL.2025.19/LIPIcs.CSL.2025.19.pdf).
3. **A fixed number of input-head reversals.** A direct Parikh-image argument
   gives regularity under Monien's ordinary-language promise.  Split a run
   into its finitely many monotone head phases.  A one-way one-counter
   automaton reads one phase letter per nonstationary move and simulates
   stationary moves by epsilon transitions.  Its phase-length vectors form
   an effectively semilinear set.  Whether such a vector fits on a unary tape
   of length `n` is expressed by linear equations for the phase endpoints and
   endmarker types.  Projection leaves an effectively semilinear set of input
   lengths.

For the first and third restrictions, the uniform bound may be an existential
accepting-witness promise rather than a bound on every run.  Given the fixed
bound, augment the finite control with the current direction and a reversal
counter, and kill a branch when it exceeds the bound.  This cannot introduce a
new accepted word, while the promised witness retains every old accepted word.
The resulting machine therefore recognizes exactly the same ordinary language
and now satisfies the syntactic all-runs bound to which the regularity argument
applies.

The third observation is not yet formalized in Langlib.  Its promise is
essential: the original machine recognizes exactly `L`, and every word of `L`
must have a bounded-head-reversal accepting run.  Neither this argument nor the
counter-reversal argument redefines acceptance by discarding high-counter runs.

Recent broader upper bounds still stop above logarithmic space.  Ibarra and
McQuillan show that two-way nondeterministic pushdown automata with
reversal-bounded counters and polynomially many input-head reversals lie in
`DSPACE(log² n)`.  Regard Monien's sole unrestricted counter as a unary
pushdown and use no auxiliary reversal-bounded counters.  The result then
covers his linearly bounded witnesses after deleting repeated configurations:
the bounded configuration graph has
`O(n²)` vertices, so a simple accepting path has only polynomially many head
reversals.  Their `R(n)`-reversal condition is existential over accepting
computations, exactly like Monien's witness promise; it does not require every
accepting run to meet the bound.  The result still does not reach the
`DSPACE(log n)` target needed here; see [*Language Acceptors with a Pushdown:
Characterizations and Complexity*](https://doi.org/10.1142/S0129054124430044).

Cycle deletion also does not make the crossing-section method for two-way
Parikh automata applicable.  A simple positive excursion has at most
`|Q|(n+2)(n+1)` distinct `(state, head, counter)` configurations, but one input
position is only bounded by `|Q|(n+1)` visits.  The crossing-section
conversion requires one fixed constant `k` bounding visits to every input
position on every accepting run; a bound growing with `n` does not give a
finite one-way automaton.

## Splitting computations at counter zero

After normalizing acceptance to counter zero, let

$$
V_n=Q\times\{0,\ldots,n+1\}
$$

be the zero-counter configurations on unary input of length `n`.  Write
`Z_n(u,v)` for a path that stays at counter zero and `E_n(u,v)` for a positive
excursion whose internal counter values are all nonzero, with no height bound.
Every zero-to-zero run factors into zero paths and positive excursions, so
ordinary acceptance, including acceptance by a high-counter run, is exactly
directed reachability in the semantic macrograph

$$
G_n=(V_n,Z_n\cup E_n).
$$

For promised membership, separately write `E_n^{\le n}(u,v)` when the whole
excursion stays at height at most `n`, and put

$$
G_n^{\le n}=(V_n,Z_n\cup E_n^{\le n}).
$$

Monien's promise says that every accepted `a^n` has one globally height-`n`
accepting run.  Consequently `a^n` is accepted iff the bounded macrograph has
an initial-to-accepting path.  This equivalence uses the promise globally; it
does **not** assert that an arbitrary high excursion or high accepting run has
a bounded replacement, and high accepting runs still count in the ordinary
language.

The zero-level relation `Z_n` is not the difficulty.  Mark the start and end
positions on a unary input and use an ordinary two-way finite automaton while
the counter remains zero.  Since two-way and one-way finite automata are
equivalent, the resulting joint marker relation is regular and its
`(n,i,j)`-length image is effectively semilinear.

This reduces the number of boundary vertices to `O(n)`, but it does not make
their directed transitive closure deterministic.  Even if every excursion
edge were Presburger-definable, unbounded transitive closure need not be:
`y = 2x` is Presburger, while its vertices reachable from `1` are the
non-ultimately-periodic set of powers of two.

There is also a concrete warning against applying the semilinearity theorem
for one-counter *nets* to exact positive excursions.  The following is the
finite-reset example of [Ibarra and
Su](https://doi.org/10.1007/978-3-642-60207-8_8), specialized to one positive
excursion.  A deterministic two-way one-counter machine can recognize

$$
\{0^a1^b2^c : a\ge1,\ b>c,\ (b-c)\mid a\}
$$

with one positive excursion and counter height at most `a+b+c`: load `a`,
then repeatedly add `c` while crossing the `2` block and subtract `b` while
crossing the `1` block.  It reaches zero exactly at the block boundary iff
`b-c` divides `a`.  This set is not semilinear.  Intersecting with `c=0`
would make the divisibility relation `{(a,b):b\mid a}` semilinear; but every
linear subset of that relation with unbounded `b` lies on one ray `a=kb`, and
finitely many such rays cannot cover all divisibility pairs.

That counterexample does not transfer directly to unary input.  Its repeated
sweeps rely on two persistent block boundaries; replacing them by guessed head
positions silently adds two pebbles.  Thus even the promise-focused joint unary
excursion relation

$$
\{(n,i,j):E_n^{\le n}((p,i),(q,j))\}
$$

remains a meaningful restricted target.  If all those relations were
effectively semilinear, then languages having a fixed bound on the number of
positive excursions would be effectively regular by finite Presburger
composition.  Semilinearity of the corresponding unrestricted `E_n` relation
would be a stronger statement.  In either case, an unbounded number of
excursions would still require transitive closure in the macrograph.

The height promise itself provides one limited guard, so mere absence of an
explicit zero test is not enough to settle this target.  Suppose the head is at
an endmarker and the positive counter value is `x`.  For `n >= 1`, a fixed
finite-control sweep can cross the tape while incrementing on exactly `n - 1`
steps (skip the first interior position), then return while decrementing on
exactly `n - 1` steps.  Its maximum counter value is `x+n-1`; since `x` is
positive, the segment remains between `1` and `n` exactly when `x = 1`, and it
restores both the head position and `x`.  Thus bounded-path
semantics can implement a shifted-zero guard at a physical endmarker even
though the machine has no transition that senses the upper bound.  The guard
does not by itself supply the missing unary pebble: moving an arbitrary
interior head position to the endmarker loses that position, while recording
it in the sole counter changes the baseline being tested.  No construction
preserving and recovering such an interior marker, and no proof that this is
impossible, is known from this investigation.

A close modern analogue helps locate the remaining gap, but its frontier needs
one correction.  Almagor, Hasson, Pilipczuk, and Zaslavski prove effective
semilinearity of the box-reachable set for [two-dimensional VAS and
one-dimensional VASS](https://arxiv.org/abs/2508.12853), and their version 1
explicitly leaves two-dimensional VASS open.  That particular open case is in
fact a corollary of the earlier geometric-dimension theorem of Fu, Yang, and
Zheng.  For a fixed 2-VASS `V`, replace every transition vector `(a,b)` by

$$
(a,b,-a,-b).
$$

Do **not** add loading loops.  Instead use the *binary* reachability relation
of this four-counter VASS.  A run of `V` from state `p` at `(0,0)` to state `q`
at `t=(t_1,t_2)` stays in the box `[0,t]` exactly when the doubled system has a
run

$$
p(0,0,t_1,t_2)\longrightarrow q(t_1,t_2,0,0).
$$

Every cycle effect of the doubled system lies in the two-dimensional subspace
`{(x,y,-x,-y)}`, so [Theorem 3.3 and its LPS characteristic
system](https://doi.org/10.4230/LIPIcs.ICALP.2024.136) make its binary
reachability relation effectively semilinear.  Intersecting that relation with
the displayed linear equalities and projecting therefore proves, as a derived
corollary, that the box-reachable target set of every fixed 2-VASS and fixed
pair of states is effectively semilinear.  This observation appears not to be
stated in either cited paper.

The useful embedding into excursions is nevertheless exact.  Given a fixed
2-VASS with initial and final states, normalize each fixed vector update into
unit moves through fresh states, taking negative units before positive units so
that an originally box-safe transition remains box-safe.  A first-coordinate
unit is a head move with zero counter effect, while a second-coordinate unit is
a stationary head move with counter effect `+1` or `-1`; Monien's transition
model permits head displacement zero.  On input length `n = m + 1`, add a
fresh entry move that increments the counter from zero and moves from the left
endmarker to the first interior cell.  Let interior head cells `1,...,n`
represent the first VASS coordinate `0,...,m`, and let positive counter value
`c = y + 1` represent the second coordinate.  A move outside the interior
cells enters a dead endmarker state; a move outside `1 <= c <= n` violates
positivity or the height promise.  From the simulated final state, guess that
the first coordinate is `m`, move right, and continue only if the next symbol
is the right endmarker.  Finally move back over the `n` interior cells,
decrementing when leaving each cell.  The counter reaches zero at the left
endmarker exactly when the second coordinate was also `m`.  This works also
for `m=0`.  With fresh check states and no other route to the exit, a fixed
diagonal run from `(0,0)` to `(m,m)` inside `[0,m]^2` exists if and only if
`E_{m+1}^{\le m+1}((p,0),(q,0))` holds.  The preceding corollary shows that
this diagonal subcase is effectively semilinear; it is no longer an
obstruction.

What remains outside that argument is exactly the input-boundary behavior of
a general excursion.  Away from the endmarkers, the shifted pair `(head,
counter-1)` is a 2-VASS in a parameterized box, so the doubled
geometric-dimension-two argument applies.  At the input boundaries, however,
Monien's model can test the head's endpoint position (equivalently, an
endmarker presentation may use distinct transitions).  In the doubled system
these become zero tests on `head` and on its complementary distance
`n+1-head`: two incomparable tested counters.  The effective-semilinearity
theorem for [2-VASS with one zero-tested
counter](https://doi.org/10.4230/LIPIcs.CONCUR.2020.37) does not cover this
four-counter doubled system with two tests.  Nor does decidability of
reachability or of the *question whether a given reachability set is
semilinear* for [nested-zero-test
VASS](https://arxiv.org/abs/2502.07660) help directly: the two singleton test
sets here are not nested, and decidability of the semilinearity question would
not imply that every relation is semilinear anyway.  Thus the VASS route proves
the marker-free interior case but still neither proves semilinearity of the
full `(n,i,j)` excursion relation nor provides a nonsemilinear unary example.

The 2025 one-counter-net theorem does not establish this premise.  Its
semilinearity result exposes only a one-dimensional morphic projection, such
as the total number of letters from a selected subset, rather than the joint
relation in `(n,i,j)` needed to compose excursions.  Full Parikh semilinearity
for bounded two-way one-counter-net languages remains conjectural there.
Moreover, a net accepts in a final state at an arbitrary counter value, while
an excursion must return to counter value exactly zero.  The positive-loop
shortcut used in the net reduction can discard counter effects and is
therefore not sound for that exact-zero endpoint.  At present, neither a proof
of height-bounded unary excursion semilinearity nor a unary counterexample is
known from this investigation.

Parametric bounded one-counter reachability does not fill this gap.  The
closest general results of Bundala and Ouaknine define bounded and
one-parameter reachability in existential Presburger arithmetic *with
divisibility*.  Divisibility already defines nonsemilinear relations, and
their model has one varying counter rather than the independently moving input
head and work counter of a positive excursion.

The classical binary-reachability theorem for ordinary [two-dimensional
VASS](https://www.doc.ic.ac.uk/concur2004/accepted/128.html) by itself does not
handle the direct encoding, because complementing both bounded coordinates
produces four counters.  The geometric-dimension theorem above is precisely
what makes that increase harmless for transitions which do not inspect a
boundary.  It does not absorb the two endmarker zero tests.  Suppressing the
complementary coordinates would merely hide the parameterized upper bounds,
while suppressing the tests would admit marker transitions at interior input
positions.

## A sharp nonregular witness for the restricted frontier

The deterministic unary language

$$
\mathrm{UPOWER}_2=\{a^{2^k}:k\ge0\}
$$

shows why the preceding restrictions are substantive.  A two-way
one-counter automaton can keep the current number in its counter, decrement it
in pairs while moving its input head once per pair, and then move back while
reconstructing the quotient in the counter.  It rejects an incomplete pair
and repeats until the quotient is one.  The counter never exceeds the input
length.

This computation uses zero tests, unboundedly many head sweeps, and
`Theta(log n)` counter reversals.  Its language is not regular because unary
regular length sets are ultimately periodic, whereas sufficiently separated
powers of two are not.  Langlib formalizes both the
unary regularity/ultimate-periodicity equivalence in
`isRegular_iff_lengthUltimatelyPeriodic` and the resulting nonregularity of
unary powers of two in `unaryPowersOfTwo_not_isRegular`.
The counter-automaton construction itself is not yet formalized.  The example
is deterministic, so it does not separate LBA from DLBA; it only shows that
the regular collapses above cannot extend to the unrestricted model.

## Resource ledger for unsuccessful general approaches

- **Savitch recursion:** `O(n²)` rather than linear space.  The exact
  midpoint semantics is checked by `reaches_iff_savitchReach_clog`; the
  independent-stack capacity and deterministic first-acceptance bounds are
  checked by `squareConfigurationStacks_le_rowCapacity_of_injective` and
  `firstSatisfying_steps_lt_rowCapacity_of_injective`.  The executable
  `finiteSavitchBool_clog_eq_true_iff` now checks the actual midpoint search,
  and `concrete_empty_evaluation_superpolynomial` gives it an explicit
  `2^(n*n)`-call empty-graph family under genuine short-circuit control flow.
  These results exclude literal stack materialization or this full recursive
  search/replay, not a reorganized reachability algorithm.
- **Immerman--Szelepcsényi counting:** counters fit in linear space, but
  reachability witnesses are still chosen nondeterministically.  The checked
  row compiler makes this failure exact: every certified-row language rejects
  the empty word, and, for an inhabited row alphabet,
  `rowReachLanguage_complementSystem_twice` proves that two applications of
  its positive complement construction recover the original language.  Hence
  `lba_eq_dlba_iff_everyComplementSystemRowReachLanguageIsDLBA` says that
  determinizing only complement-compiler outputs is already equivalent to
  `LBA = DLBA`.  Via `TwoMatchingLBA = DLBA`, the direct theorem
  `lba_eq_dlba_iff_everyComplementSystemRowReachLanguageIsTwoMatchingLBA`
  gives the same equivalence for compiling those outputs to exact two-matching
  presentations.  The class equivalence handles an empty source-row alphabet
  separately and imposes no lower-cardinality premise on the finite terminal
  alphabet.  The counting protocol is not a smaller determinization normal
  form.
- **Algebraic path counting:** exact counts on degree-two DAGs may require
  `Theta(N)` bits.  Cofactor and matrix-powering formulations live at the
  `#L`/`GapL` and `O(log² N)`-space scale.  Modular residues avoid the large
  integer, but computing them already captures modular-logspace counting; no
  deterministic `O(log N)` method is known.
- **Canonical or lexicographically first witnesses:** verifying that a
  candidate is first asks the original reachability question again.  The
  formal `first_successful_child_decides` fork makes this equivalence exact
  while preserving the acyclic degree-two two-biunique hard core.
- **Literal path schedules:** `2^k` distinct `k`-bit schedules require
  `2^k ≤ |A|^W` to inject into one width-`W` fixed-alphabet row, as formalized
  by `bitVectors_le_rowCapacity_of_injective`.
  `acceptsWithChoices_acceptTarget_iff` proves that the split `k`-diamond
  presentation really consumes exactly `k` choices on every target-reaching
  trace, and `encodeVertex` fits its `k=2^W` instance into constant control
  plus one `W`-bit row.  The latter is only a succinct structural naming
  theorem, not a local LBA implementation.  Together these obstruct literal
  exhaustive path replay, not collective or recomputing algorithms.
- **Reversible simulation:** Lange--McKenzie--Tapp removes irreversible merges
  from an already deterministic computation in the same asymptotic space; it
  does not choose a branch of an LBA.  It is therefore relevant to the reverse
  inclusion `DLBA ⊆ TwoMatchingLBA`, not to the open inclusion
  `LBA ⊆ DLBA`.  In this repository a moving raw clamped relation cannot be
  globally cofunctional at all; `cofunctionalLBA_eq_trivial_languages` proves
  the resulting class is exactly `{∅, Set.univ}`, and
  `cofunctionalLBA_subset_DLBA` uses transition-free witnesses rather than a
  simulation sweep.  The completed adaptation therefore targets exact two
  matching layers directly: the local-port marked Euler compiler
  makes unavoidable malformed-boundary merges terminal while preserving and
  reflecting the ordinary deterministic run.  This proves the stated reverse
  inclusion, but it supplies no nondeterministic branch-selection mechanism.
  Merely adding reverse edges to an LBA would still change directed
  reachability.
- **Undirected connectivity:** Reingold's theorem does not preserve directed
  acceptance paths.  In the padded layered graph, directed reachability is
  equivalent to the underlying undirected endpoints having distance exactly
  their layer gap, and that exact-distance problem remains `NL`-hard by the
  same reduction.
- **One-pass topological streaming:** the rank-ordered `INDEX` construction
  above forces `Theta(N)` state bits even for layered degree-two DAGs.
  Frontier propagation is logarithmic-space only under an additional
  `O(log N)` layer-width bound, which the clock compiler does not provide.
- **Acyclicity:** the generic clock-layer reduction is formalized in
  `reaches_iff_layered_reaches`, and the stronger same-width, unit-certified
  row-system reduction is formalized by
  `lba_eq_dlba_iff_acyclicUnitCertificateRowReach`.  The latter is equivalent
  to the full first LBA problem.  The strict generic construction
  simultaneously preserves arbitrary predecessor and successor degree bounds.
  `card_cfg_lt_clockCapacity` gives the strict capacity inequality for bounded
  LBA configurations; `card_exactLayers_le_clockRow` and
  `length_encodeSemanticLayer` then show that every exact clock layer fits in
  one constant-radix digit per physical tape cell.
  `LBA.AcyclicClock.machine` supplies the concrete local
  one-tape protocol.  Its initialization, bidirectional macro simulation,
  exact language preservation, and global malformed-configuration acyclicity
  are formalized by `reaches_canonicalCfg_init`,
  `machine_simulatesClockedSteps`, `machine_reflectsCheckpointPaths`,
  `languageEnd_machine_eq`, and `machine_configurationAcyclic`.
  `lba_eq_dlba_iff_clockDegreeSerializedLanguages` shows that determinizing
  only the literal clock-and-degree compiler image is still the full problem.
- **Small directed degree:** `BoundedDegreeLBA_eq_LBA` proves that
  configuration graphs with both indegree and outdegree at most two already
  recognize exactly `LBA`, without increasing the tape width.
  `configurationAcyclic_boundedDegree` additionally proves that both
  serializers preserve global acyclicity.
- **A constant number of partial-bijection layers:** this is automatic in the
  finite degree-two core: `exists_two_biUnique_partition` optimally partitions
  every such edge relation into two functional-and-cofunctional layers, and
  `Machine.exists_two_biUnique_step_partition` gives the fixed-width LBA
  corollary.  More strongly, `boundedDegreeStepLayer` gives the actual degree
  serializer one syntactic layer family uniform over all tape widths, and
  `AcyclicDegreeTwoBiUniqueLBA_eq_LBA` proves that the globally acyclic
  two-layer restriction still equals `LBA`.  At the explicit-graph level,
  `finiteReachability_singleTarget_twoBiUnique` gives a checked structural
  reduction of arbitrary reachability to an acyclic instance with one
  designated target and a supplied two-partial-bijection decomposition;
  Bhadra and Tewari's complementary effective result remains `NL`-hard under
  the stronger layer-local linear-`2`-diforest promise, but does not include a
  global DAG promise.  The formal `diamondChain_obstruction` also includes an
  exact two-biunique-layer partition while retaining `2^k` paths.  Thus a
  constant number of unrestricted partial-bijection layers is not enough.
  There are two distinct positive frontiers: a constant number of supplied
  whole paths admits the path-marker algorithm above, while an exact union of
  two directed matching layers admits the machine-level compiler
  `twoMatchingLBA_subset_DLBA`.  Three matching layers already recover all of
  `LBA`; no strict language-class separation is claimed.
- **One-tape locality:** it does not force a low-width configuration graph.  A
  single fixed two-state LBA over a binary tape alphabet (with local outdegree
  at most three) has disjoint connected fibers indexed by Boolean tape
  contents and realizes every hypercube edge between the fibers.
  `hypercubeBranchSetMinor` now formalizes the complete branch-set certificate,
  including connectivity paths restricted to each fiber and pairwise
  disjointness, for every positive dimension.  The resulting standard minor
  bounds allow exponential treewidth and linear genus, even though every step
  changes at most one tape cell; those numerical graph-parameter bounds remain
  external corollaries.  `strictClockHypercubeBranchSetMinor` carries the
  certificate through the full semantic acyclic strict clock, and
  `concreteClockHypercubeBranchSetMinor` carries it through the raw graph of
  the actual one-tape clock protocol.
  `boundedDegreeHypercubeBranchSetMinor` then carries it through both concrete
  degree serializers into the final complete raw graph, while
  `boundedDegreeMachine_globalProperties` checks global acyclicity, both
  directed degree-two bounds, and the uniform two-partial-bijection partition
  for that same machine.  The theorem
  `exists_boundedDegreeMachine_stepTrace_crosses_exact` now proves that this
  identical final machine also has a width-`n` directed trace crossing every
  physical boundary at least `2 * 6^(n+1) * (n+1)` times; the assertion is
  vacuous over boundaries at `n=0`, but the trace still exists.  This is one
  selected self-loop trace, not a bound forced on all or accepting runs.  The
  standard numerical
  treewidth/pathwidth/genus consequences remain external, and none of these
  undirected-minor facts decides directed reachability.
- **Linear genuine branch events:** the generic DLBA construction remains
  paper-level; its exhaustive-schedule replay semantics and same-width
  resources are formalized by
  `acceptsWithChoiceEventsSearch_linear_eq_true_iff` and `packLinearSchedule`.
  Exact two matching layers force the constant bound one, and this special
  case now has the fully checked low-level compiler
  `twoMatchingLBA_subset_DLBA`.
  Therefore a separating language would force an unbounded
  branch-events/input-length ratio for every one of its LBA presentations.
- **Isolation or unambiguity:** known isolation either uses advice exponential
  in the LBA width, exceeds linear space after substituting
  `N=2^{Theta(n)}`, or retains an oracle/catalyst.  Even an unambiguous target
  still asks the open question `UL = L`.
- **Universal diagonalization:** fixed-alphabet universal simulation incurs
  a source-alphabet-dependent encoding factor.  An unbounded state set or
  program description contributes additive code data and is not the same
  obstruction.  Padding absorbs that additive overhead but not the per-cell
  `log |Gamma|` information cost.
  `exists_fin_no_uniform_affineExpansion_boundedTape_encoding` formalizes
  this for every fixed direct affine configuration-encoding bound; it is not
  a lower bound on semantic simulations.
- **Countable staged simulation:** fixed-stage machines do not combine into
  one finite uniform machine.

The exact certified-row theorem makes this ledger concrete: any successful
general approach must deterministically choose reachability paths in
locally-verifiable, fixed-width row graphs while retaining only one row's
asymptotic storage.

## References

- S.-Y. Kuroda, [*Classes of Languages and Linear-Bounded
  Automata*](https://doi.org/10.1016/S0019-9958(64)90120-2), 1964.
- Lowell W. Beineke and Frank Harary, [*The Genus of the
  n-Cube*](https://doi.org/10.4153/CJM-1965-048-6), 1965.
- Walter J. Savitch, [*Relationships between nondeterministic and deterministic
  tape complexities*](https://doi.org/10.1016/S0022-0000(70)80006-X), 1970.
- Juris Hartmanis and Harry B. Hunt III, [*The LBA Problem and its Importance
  in the Theory of Computing*](https://hdl.handle.net/1813/6015), 1973.
- Ivan H. Sudborough, [*On tape-bounded complexity classes and multi-head
  finite automata*](https://doi.org/10.1109/SWAT.1973.20), 1973.
- Burkhard Monien, [*The LBA-Problem and the Deterministic Tape Complexity of
  Two-Way One-Counter Languages over a One-Letter
  Alphabet*](https://digital.ub.uni-paderborn.de/hsx/download/pdf/42059), 1977.
- Chandra M. R. Kintala and Patrick C. Fischer,
  [*Computations with a Restricted Number of Nondeterministic
  Steps*](https://doi.org/10.1145/800105.803407), 1977.
- Joel I. Seiferas, [*Techniques for Separating Space Complexity
  Classes*](https://doi.org/10.1016/S0022-0000(77)80041-X), 1977.
- Joel I. Seiferas, [*Relating Refined Space Complexity
  Classes*](https://doi.org/10.1016/S0022-0000(77)80042-1), 1977.
- Michael C. Loui, [*A Space Bound for One-Tape Multidimensional Turing
  Machines*](https://doi.org/10.1016/0304-3975(81)90084-0), 1981.
- Neil Immerman, [*Nondeterministic Space is Closed under
  Complementation*](https://doi.org/10.1137/0217058), 1988.
- Carsten Damm, [*Problems Complete for
  ⊕L*](https://doi.org/10.1016/0020-0190(90)90150-V), 1990.
- Gerhard Buntrock, Carsten Damm, Ulrich Hertrampf, and Christoph Meinel,
  [*Structure and Importance of Logspace-MOD
  Class*](https://doi.org/10.1007/BF01374526), 1992.
- Carme Àlvarez and Birgit Jenner, [*A Very Hard Log-Space Counting
  Class*](https://doi.org/10.1016/0304-3975(93)90252-O), 1993.
- Meena Mahajan and V. Vinay, [*Determinant: Combinatorics, Algorithms, and
  Complexity*](https://eccc.weizmann.ac.il/eccc-reports/1997/TR97-036/index.html),
  1997.
- Klaus-Jörn Lange, Pierre McKenzie, and Alain Tapp,
  [*Reversible Space Equals Deterministic
  Space*](https://doi.org/10.1006/jcss.1999.1672), 2000.
- Balagopal Komarath, Jayalal Sarma, and Saurabh Sawlani,
  [*Pebbling Meets Coloring: Reversible Pebble Game on
  Trees*](https://arxiv.org/abs/1604.05510), 2016.
- Michal Kunc and Alexander Okhotin,
  [*Reversibility of Computations in Graph-Walking
  Automata*](https://doi.org/10.1016/j.ic.2020.104631), 2020.
- Eric Allender and Klaus-Jörn Lange,
  [*RUSPACE(log n) is contained in
  DSPACE(log² n/log log n)*](https://doi.org/10.1007/s002240000102), 1998.
- Oscar H. Ibarra, Tao Jiang, Nicholas Tran, and Hui Wang, [*New Decidability
  Results Concerning Two-Way Counter
  Machines*](https://doi.org/10.1137/S0097539792240625), 1995.
- Klaus Reinhardt and Eric Allender, [*Making Nondeterminism
  Unambiguous*](https://doi.org/10.1137/S0097539798339041), 2000.
- Arnaud Carayol and Antoine Meyer, [*Context-Sensitive Languages, Rational
  Graphs and Determinism*](https://doi.org/10.2168/LMCS-2(2:6)2006), 2006.
- L. Sunil Chandran and T. Kavitha, [*The Treewidth and Pathwidth of
  Hypercubes*](https://doi.org/10.1016/j.disc.2005.12.011), 2006.
- Omer Reingold, [*Undirected Connectivity in Log-Space*](https://doi.org/10.1145/1391289.1391291),
  2008.
- Szymon Bundala and Joël Ouaknine, [*On Parametric Timed Automata and
  One-Counter Machines*](https://doi.org/10.1016/j.ic.2016.07.011), 2017.
- Emmanuel Filiot, Shibashis Guha, and Nicolas Mazzocchi, [*Two-Way Parikh
  Automata*](https://doi.org/10.4230/LIPIcs.FSTTCS.2019.40), 2019.
- Dieter van Melkebeek and Gautam Prakriya, [*Derandomizing Isolation in
  Space-Bounded Settings*](https://doi.org/10.1137/17M1130538), 2019.
- Jérôme Leroux and Grégoire Sutre, [*Reachability in Two-Dimensional Vector
  Addition Systems with States: One Test Is for
  Free*](https://doi.org/10.4230/LIPIcs.CONCUR.2020.37), 2020.
- Yuxi Fu, Qizhe Yang, and Yangluo Zheng, [*Improved Algorithm for
  Reachability in d-VASS*](https://doi.org/10.4230/LIPIcs.ICALP.2024.136),
  2024.
- Shaull Almagor, Michaël Cadilhac, and Asaf Yeshurun, [*Two-Way One-Counter
  Nets Revisited*](https://doi.org/10.4230/LIPIcs.CSL.2025.19), 2025.
- Roland Guttenberg, Wojciech Czerwiński, and Sławomir Lasota,
  [*Reachability and Related Problems in Vector Addition Systems with Nested
  Zero Tests*](https://arxiv.org/abs/2502.07660), 2025.
- Shaull Almagor, Itay Hasson, Michał Pilipczuk, and Michael Zaslavski,
  [*Box-Reachability in Vector Addition
  Systems*](https://arxiv.org/abs/2508.12853), 2025.
- Simon Apers and Roman Edenhofer, [*Directed st-Connectivity with Few Paths
  Is in Quantum Logspace*](https://doi.org/10.4230/LIPIcs.CCC.2025.18), 2025.
- Ronak Bhadra and Raghunath Tewari, [*Trading Determinism for Time: The
  k-Reach Problem*](https://arxiv.org/pdf/2409.18469v2), version 2, 2025.
- Michal Koucký, Ian Mertz, Edward Pyne, and Sasha Sami, [*Collapsing
  Catalytic Classes*](https://arxiv.org/abs/2504.08444), 2025.
- V. Arvind, Srijan Chakraborty, and Samir Datta, [*Derandomizing Isolation
  in Catalytic Logspace*](https://arxiv.org/abs/2512.09374v3), 2025; version 3
  revised 2026.
- Ronak Bhadra and Raghunath Tewari, [*Reachability in Graphs Having Linear
  2-Arboricity Two Is NL-Hard*](https://doi.org/10.1016/j.ipl.2025.106611),
  2026.
- Roman Edenhofer, [*A Space-space Trade-off for Directed
  st-Connectivity*](https://arxiv.org/abs/2602.21088), 2026.
- Petr Chmel, Aditi Dudeja, Michal Koucký, Ian Mertz, and Ninad Rajgopal,
  [*Frontier Space-Time Algorithms Using Only Full
  Memory*](https://arxiv.org/abs/2602.21089), 2026.
- Michal Koucký, Ian Mertz, and Sasha Sami, [*Understanding Robust Catalytic
  Computing*](https://arxiv.org/abs/2605.09648), 2026.
- Oscar H. Ibarra and Ian McQuillan, [*Language Acceptors with a Pushdown:
  Characterizations and Complexity*](https://doi.org/10.1142/S0129054124430044),
  2025.
