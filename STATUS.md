# Project status

Last updated: 17 July 2026.

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

The strongest normal-form result is thus:

> Every LBA language is accepted by a same-width, globally acyclic LBA whose
> configuration graph has indegree and outdegree at most two and whose entire
> step relation is partitioned by two width-uniform partial-bijection layers.

This remains a nondeterministic normal form. Showing that all machines in
this restricted class can be simulated by DLBAs would solve the original
open problem.

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

## Verification

The result was checked from a clean build:

- `lake build`: 8,856 jobs completed successfully;
- `lake test`: passed;
- generated import-hub check: passed;
- theorem-link check: passed;
- staged-diff and proof-hole scans: passed.

The detailed mathematical and literature ledger is in
[docs/results/first-lba-problem-boundaries.md](docs/results/first-lba-problem-boundaries.md).
