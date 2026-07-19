# Project status

Last updated: 19 July 2026.

This is the high-level research map.  The proof-level construction history,
quantitative bounds, failed routes, and literature notes live in the
[detailed first-LBA-problem ledger](docs/results/first-lba-problem-boundaries.md).

## Open problem

The first LBA problem

$$
\mathrm{LBA} \stackrel{?}{=} \mathrm{DLBA},
$$

equivalently

$$
\mathrm{NSPACE}(O(n)) \stackrel{?}{=} \mathrm{DSPACE}(O(n)),
$$

remains open.  This repository proves neither equality nor separation.  Recent
references which still state the problem as open include Carayol and Meyer's
[*Linearly Bounded Infinite
Graphs*](https://monge.univ-eiffel.fr/~carayol/Papers/5dba301a855ca01.pdf)
and Viola's [2026 complexity
manuscript](https://www.khoury.northeastern.edu/home/viola/papers/moti.pdf).

Lin's claimed separation does not establish a uniform language recognizer: a
machine for every finite stage does not supply one machine for their union,

$$
(\forall i,\ \exists M_i) \not\Longrightarrow (\exists M).
$$

[Preu's analysis](https://arxiv.org/abs/2110.12421) records related defects in
earlier versions.

## Conventions shared by the results

- “Same-width” means that a compiler may enlarge finite control and the finite
  tape alphabet but does not add tape cells.
- A raw configuration-graph promise ranges over every tape width and every raw
  configuration, including malformed configurations, unless a theorem says
  otherwise.
- Tape parameter zero is the one-cell case.  Canonical endmarker semantics runs
  the empty word on the genuine two-cell tape `⊢⊣`.
- Physical turns ignore `stay` moves and outward moves clamped at an endpoint.
- Class theorems are stated for arbitrary finite terminal types.  No
  nonemptiness or cardinality lower bound is implicit; strict results state
  such a premise when it is necessary.

## Major checked class map

The principal identities and inclusions are:

| Level | Machine-checked identification |
|---|---|
| Trivial | For every `k ≤ 1`, `KMatchingLBA k`; the zero-crossing slice; complete-raw `CofunctionalLBA`; and complete-raw `ReversibleLBA` are exactly `{∅, Set.univ}`. |
| Regular | Every positive fixed crossing-cap class, the existential uniform-crossing class, and every fixed head-turn class equal DFA, NFA, and the regular languages. |
| Deterministic linear space | `KMatchingLBA 2 = TwoMatchingLBA = SweepingDLBA = SweepingEndDLBA = DLBA`. |
| Unambiguous linear space | `DLBA ⊆ ULBA ⊆ LBA`; neither reverse inclusion is proved. |
| Nondeterministic linear space | For every `k ≥ 3`, `KMatchingLBA k = LBA`; also `SweepingLBA = LBA` and all the acyclic/degree-two normal forms below equal `LBA`. |
| Context-sensitive | `CS = LBA`, and `CS` is closed under complement. |
| Decidable languages | Over every nonempty finite alphabet, `LBA ⊂ Recursive`; recursive languages are themselves strictly below RE. |

The headline proof links are:

- [`CS_eq_LBA`](src/Langlib/Automata/LinearBounded/Equivalence/ContextSensitive.lean)
  (the Myhill–Landweber–Kuroda equivalence).
- [`CS_closedUnderComplement`](src/Langlib/Classes/ContextSensitive/Closure/Complement.lean),
  together with `is_CS_complement` and `CS_complement_iff` (the
  Immerman–Szelepcsényi theorem in linear space).
- [`SweepingLBA_eq_LBA`](src/Langlib/Automata/LinearBounded/SweepingEndmarkerCharacterization.lean)
  and its marker-free positive-language form `SweepingLBA_pos_eq_LBA_pos`.
- [`SweepingDLBA_eq_DLBA`](src/Langlib/Automata/LinearBounded/DeterministicSweeping/Characterization.lean)
  and the genuine-endmarker form
  [`SweepingEndDLBA_eq_DLBA`](src/Langlib/Automata/LinearBounded/DeterministicSweeping/EndmarkerCharacterization.lean).
- [`TwoMatchingLBA_eq_DLBA`](src/Langlib/Automata/LinearBounded/GraphWalking/MarkedEulerProbe/ClassEquivalence.lean).
- [`KMatchingLBA_eq_trivial_languages_of_le_one`](src/Langlib/Automata/LinearBounded/MatchingLayerHierarchy.lean),
  `KMatchingLBA_two_eq_DLBA`, `KMatchingLBA_three_eq_LBA`, and
  `KMatchingLBA_eq_LBA_of_three_le`.

The sweeping equalities on both sides are strong all-finite-prefix normal
forms, not statements about one selected accepting run.  The deterministic
compiler starts with a DLBA, while the nondeterministic compiler retains its
branching.  Their similarity therefore does not prove `LBA ⊆ DLBA`.

## Same-width normal forms equal to LBA

Every LBA language has a same-width presentation satisfying progressively
stronger complete-raw-graph promises:

- `BinaryBranchingLBA_eq_LBA`;
- `BoundedDegreeLBA_eq_LBA`;
- `AcyclicLBA_eq_LBA` and `AcyclicBoundedDegreeLBA_eq_LBA`;
- `AcyclicDegreeTwoBiUniqueLBA_eq_LBA`;
- `AcyclicDegreeTwoShortBiUniqueLBA_eq_LBA`;
- `AcyclicDegreeTwoThreeMatchingLBA_eq_LBA`.

Thus global acyclicity, indegree and outdegree at most two, finite local edge
checking, and a width-uniform layer presentation do not remove the hard path
choice.  The two short layers are partial bijections whose monochromatic paths
may contain two edges; they are not directed matchings.  Splitting once more
produces three actual directed matchings.

The constructions reuse a small set of ideas:

1. finite extra tracks encode clocks, boundary bits, phases, and certificates;
2. a global clock makes the complete raw graph acyclic;
3. local serializers reduce both directed degrees to two;
4. phase splitting turns short partial bijections into matching colors;
5. certified row systems express local successor and complement certificates;
6. marker-free and actual-endmarker transports handle `epsilon` explicitly.

Under its explicit finite inhabited row-alphabet premise, the complement
compiler is exact and involutive on its certified-row positive languages
(`rowReachLanguage_complementSystem` and
`rowReachLanguage_complementSystem_twice`).  It remains nondeterministic:
closure under complement is not a determinization theorem.

## Exact two-versus-three frontier

The newly uniform matching hierarchy makes every level literal:

$$
\mathrm{KMatchingLBA}(k)=
\begin{cases}
\{\varnothing,\Sigma^*\},&k\le 1,\\
\mathrm{DLBA},&k=2,\\
\mathrm{LBA},&k\ge 3.
\end{cases}
$$

Adding unused colors is monotone.  Consequently
`lba_eq_dlba_iff_KMatchingLBA_three_eq_two` and
`lba_eq_dlba_iff_KMatchingLBA_three_subset_two` state that the first LBA
problem is exactly the possible collapse from three matching colors to two.

Why the existing two-color proof stops there:

- after a vertex of an exact two-matching graph has an incoming edge, its
  reachable descendants cannot contain a genuine incomparable fork;
- hence an accepting run needs at most one genuine branch event, and the
  checked compiler can try the finitely many first branches sequentially;
- exact three-matching DAGs can instead contain `2^w` ordered relevant forks at
  row width `w`, with `2^(2^w)` explicit source-to-target schedules;
- a three-edge fork has no injective all-pairs reachability embedding into an
  exact two-matching graph.

The last two facts block literal schedule materialization and vertexwise
all-pairs encodings.  They are not deterministic-space lower bounds: a
source-specific compiler may recompute, aggregate, or represent reachability
without storing every path.

Equivalent checked formulations of the same unresolved step include:

- determinizing `AcyclicDegreeTwoShortBiUniqueLBA` or
  `AcyclicDegreeTwoThreeMatchingLBA`;
- determinizing unit-certificate certified-row reachability;
- determinizing only outputs of the certified-row complement compiler;
- determinizing only outputs of the concrete clock/degree serializers;
- proving both `LBA ⊆ ULBA` and `ULBA ⊆ DLBA`.

## Other checked boundaries

- The deterministic-to-two-matching compiler is complete.  It locally
  implements an Euler graph walk, phase doubles it, refines every abstract tape
  operation to clamped one-tape microsteps, makes unavoidable boundary merges
  terminal, and proves exact simulation, reflection, matching, and language
  preservation.
- Complete-raw cofunctionality is too strong in this clamped model: every
  enabled directional move creates two predecessors of one target.  Therefore
  the named `CofunctionalLBA` and `ReversibleLBA` classes collapse to the
  trivial languages.  This is not the standard marked-tape reversible-machine
  model of Lange–McKenzie–Tapp.
- Uniform selected-run crossing bounds and constant head-turn bounds force
  regularity.  Every fixed crossing slice is regular, but their increasing
  union is the whole LBA language; for a nonregular language those slices
  never stabilize.
- Savitch midpoint reachability is formalized propositionally and as an
  executable finite Boolean search.  Literal continuation stacks require a
  quadratic number of bits, and the checked evaluator has a corresponding
  superpolynomial worst case.  This rules out that implementation strategy,
  not every deterministic reachability algorithm.
- One fixed globally acyclic, degree-two, two-partial-bijection machine has
  Boolean cubes of every dimension as undirected branch-set minors and has an
  exponentially crossing concrete run.  These are locality witnesses, not
  directed-reachability lower bounds.

## Effectivity and decision problems

`LBA_computableMembership` states the intended uniform membership problem:
given a finite automaton code and a separate query word, bounded exploration of
the finite configuration graph decides whether the encoded LBA accepts the
word.  The encoding stores transition data; it does not encode the membership
answer.  This external evaluator has no claimed linear-space bound and is not a
DLBA compiler.

For recursive languages, `RecursiveDeciderCode.recursive_computableMembership`
uses a raw program plus the semantic promise that it halts on every word.  The
same code-and-word evaluator is partial on arbitrary programs and total on that
promise.  There is no effective total numbering of all recursive languages
with uniformly decidable membership (`Recursive_notComputableMembership`).

Even under the always-halting promise, language-level properties remain
undecidable in general: `emptiness_undecidable`,
`universality_undecidable`, and `equivalence_undecidable`.  This does not
conflict with decidability of membership for one encoded language and one word.

## Proposed next variants

The following are research targets, not claimed theorems.  They are ordered by
how directly they reuse the checked infrastructure.

1. **Linear-choice LBA.**  Package one fixed finite presentation and the
   existing `HasLinearAcceptingChoiceBound`: one fixed constant `c` must give
   every accepted word an accepting labeled trace with at most
   `c · (|w| + 2)` genuine branch configurations.  Branching means two
   distinct successor configurations, while schedule entries retain the
   transition triples.  There is no promise on rejected words.  A functional
   presentation gives `DLBA ⊆ LinearChoiceLBA` with `c = 0`; the real target is
   `LinearChoiceLBA ⊆ DLBA`.  Its compiler must pack the input copy, current
   configuration, schedule and cursor, stretch counter, enumeration state,
   and the empty/endmarker cases.  The checked bounded search is the semantic
   specification, not yet that low-level one-tape enumerator/replayer.

2. **Linearly forked three-matching LBA.**  Make this a same-machine structural
   promise, not the vacuous language-class intersection with
   `ThreeMatchingLBA = LBA`.  For each canonical input, bound by
   `c · (|w| + 2)` the distinct branch configurations which are both reachable
   from the start and able to reach an accepting configuration.  Loop erasure
   then gives a simple accepting path with only that many branch events, hence
   an inclusion in `LinearChoiceLBA`.  Count configurations—not rules, colors,
   or head positions.  Proving that every LBA language has such a
   three-matching presentation, followed by the first compiler, would solve
   the full open problem.  The current odometer-diamond presentation cannot
   witness it because it has exponentially many sequential relevant forks.

3. **Canonical cofunctional LBA.**  Use a decidable well-formed region which
   contains the canonical inputs and is closed under forward steps; require
   each canonical target to have at most one canonical predecessor, require
   accepting configurations to be canonical, and use genuine endmarkers
   rather than clamped outward moves.  Do not require cofunctionality of
   malformed configurations.  A deterministic simulator
   can enumerate canonical accepting configurations and follow each unique
   canonical predecessor chain for at most the finite configuration count,
   while retaining the input on another track.  The first target is
   `CanonicalCofunctionalLBA ⊆ DLBA`, reusing the existing abstract exhaustive
   backtracker.  Morita's same-space result for his normalized reversible
   nondeterministic model motivates this boundary
   ([2014 paper](https://doi.org/10.1080/03081079.2014.920998)); its model
   conditions must be translated explicitly rather than attributed to the
   repository's stronger raw predicate.

4. **Accept-confluent acyclic LBA.**  Require accessible acyclicity, local
   joinability of every accessible fork, and every accessible accepting
   configuration to be terminal.  Newman's lemma then gives a unique normal
   form; a fixed priority selector which always takes an enabled transition
   terminates there, and reaches an accepting state exactly when the source
   machine can.  The selected machine is functional.  The useful formal split
   is first this finite-relation normalization theorem, then a same-width
   automaton class.  The hard step is compiling arbitrary existential
   acceptance into local confluence without already selecting its branch.

5. **Canonical symmetric LBA.**  Supply a decidable well-formed region which
   contains the canonical start, is closed under every incident transition,
   and whose internal step relation is symmetric.  Equivalently, state
   directly that directed and weak reachability from the start agree; symmetry
   merely on the forward-reachable induced graph is too weak.  Reingold's
   [undirected-connectivity theorem](https://doi.org/10.1145/1391289.1391291)
   suggests an `O(log |Cfg_w|) = O(w)` deterministic traversal.  Formalization
   needs an implicit bounded-degree neighbor interface and an LBA implementation
   of the traversal.  Blindly adding reverse edges is unsound because it can
   create new directed source-to-accept paths.

   Related positive graph promises are worth separating: deterministic
   logspace algorithms are known for
   [Eulerian directed graphs](https://doi.org/10.1145/1132516.1132583),
   [fixed treewidth with an effective decomposition](https://doi.org/10.4230/LIPIcs.STACS.2010.2456),
   and a [supplied constant number of whole directed
   paths](https://arxiv.org/abs/2409.18469).  None of these is the same as a
   constant number of matching colors, which may contain exponentially many
   path components.  [Planar directed
   reachability](https://doi.org/10.1145/1490270.1490274) currently gives an
   unambiguous rather than a deterministic target.

6. **Reach-few and stronger unambiguous LBAs.**  Count labeled move paths from
   the canonical start to every configuration, including distinct transition
   triples with the same endpoint.  Either stop paths at their first accepting
   configuration or normalize accepting configurations to be terminal.  Use
   an infinite-aware cardinal (or an acyclic clock) and a uniform exponent,
   for example at most `|Cfg_w|^k` paths for one fixed `k`; its logarithm is
   linear in tape width.  The general reach-few theorem gives
   reach-unambiguous space `O(s(n) + log a(n))`
   ([Garvin–Stolee–Tewari–Vinodchandran](https://doi.org/10.1007/s00037-012-0050-8)),
   but porting its hashing and layering to the repository's implicit
   exponential graphs is a substantial proof target, not an automatic
   corollary.  Known deterministic reach-unambiguous simulation scales here
   to `O(n² / log n)`, not `O(n)`.  Bounds only on accepting runs are weaker.
   Define `ReachULBA` to include ordinary first-final input unambiguity as well
   as at most one labeled path to every target; per-target uniqueness alone
   permits several accepting targets.  Precise checkpoints are
   `ReachFewLBA ⊆ ReachULBA`, then `ReachULBA ⊆ ULBA`; strong unambiguity must
   mean all-pairs labeled-path uniqueness.  Min-uniqueness and the self-dual
   language class `BiULBA = ULBA ∩ coULBA`, allowing separate witnesses, are
   related checkpoints, not deterministic selectors
   ([Pavan–Tewari–Vinodchandran](https://arxiv.org/abs/1001.2034)).

The first two variants attack the checked three-to-two frontier operationally;
the next three replace forward search by backward uniqueness, a canonical
normal form, or an undirected component; the last isolates disambiguation.
Each exposes a concrete theorem that can fail independently, avoiding another
reformulation that is silently equivalent to the full open problem from its
first lemma.

## What is not claimed

- There is no general LBA-to-DLBA compiler and no separation.
- No reduction from three matching layers to two is known.
- Sweeping, acyclicity, degree two, short layers, complement closure, and
  decidable encoded membership do not select a nondeterministic branch.
- Capacity, schedule, crossing, and graph-minor results rule out only the
  stated literal strategies; none is a general linear-space lower bound.
- The proposed variants above have not yet been promoted to checked language
  classes or inclusions.

## Verification

The integrated repository passes:

- `lake build`: 9,006 jobs;
- `lake test`: 3,115 jobs;
- warning-as-error direct compilation of the matching-hierarchy module;
- warning-as-error direct compilation of the ordinary encoded-membership target
  and all deterministic-sweeping modules;
- generated import-hub and theorem-link checks;
- diff and proof-hole scans;
- headline axiom audits, with only `propext`, `Classical.choice`, and
  `Quot.sound`.
