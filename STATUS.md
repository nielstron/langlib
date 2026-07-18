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
- `reversibleLBA_subset_twoMatchingLBA` proves that every presentation whose
  complete raw configuration step relation is a partial bijection at every
  width becomes an exact-two-matching presentation after the same-width
  input/output phase split.  Thus configuration-reversible LBAs lie on the
  checked positive side as well.
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
restrictive machine promise of two actual matching layers, the checked
compiler proves `TwoMatchingLBA ⊆ DLBA`.  Together with the three-matching
normal form this gives a checked structural boundary:

> Two exact directed-matching layers admit deterministic simulation, whereas
> three exact directed-matching layers already suffice to present every LBA
> language.

This is not a separation of `DLBA` from `LBA`: the repository neither reduces
the universal three-matching presentation to two matchings nor proves that
every DLBA language has a two-matching presentation.

The reverse route is now isolated more precisely.  The checked inclusion is

> `ReversibleLBA ⊆ TwoMatchingLBA ⊆ DLBA`.

The first step uses `Machine.threeMatchings` with only two phase colors.  What
is missing for `DLBA ⊆ TwoMatchingLBA` is a concrete same-width reversible
compiler.  A merely functional machine is insufficient: a configuration with
two predecessors and one successor has three incident edges, which two
directed matchings cannot cover.  Moreover, standard syntactic reversible-TM
rules do not automatically satisfy the repository's stronger promise on all
raw configurations, because a clamped boundary move can merge two head
positions.  Any future reversible compiler must guard those malformed-tape
boundary cases explicitly.

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
- `TwoMatchingLBA ⊆ DLBA` does not imply `LBA ⊆ DLBA`: the checked
  all-LBA normal form uses three matching layers, and no language-preserving
  reduction from three layers to two is claimed.  Nor is the reverse
  inclusion `DLBA ⊆ TwoMatchingLBA` claimed.
- No unconditional `LBA ⊆ ULBA` or `ULBA ⊆ DLBA` theorem is claimed.
  Current linear-space disambiguation results cited in the research ledger
  either use superlinear space or require explicit circuit-hardness
  hypotheses; even conditional disambiguation leaves unambiguous
  determinization open.

## Verification

The current integrated result was checked by the full build/test gates:

- `lake build`: 8,883 jobs completed successfully;
- `lake test`: passed;
- generated import-hub check: passed;
- theorem-link check: passed;
- staged-diff and proof-hole scans: passed.

The detailed mathematical and literature ledger is in
[docs/results/first-lba-problem-boundaries.md](docs/results/first-lba-problem-boundaries.md).
