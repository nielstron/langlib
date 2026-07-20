---
title: "DLBA pumping and separation candidates"
description: "Checked pumping barriers, exact separator normal forms, and clearly marked research candidates for the open LBA versus DLBA problem."
parent: "Context-sensitive"
nav_order: 8
---

# DLBA pumping and separation candidates

## Status and scope

The first LBA problem asks whether

$$
\mathrm{LBA}=\mathrm{DLBA},
$$

equivalently, up to standard conventions, whether `NSPACE(O(n)) = DSPACE(O(n))`.
This page claims neither equality nor separation.  It separates three kinds:

1. checked Lean theorems that rule out naive pumping arguments;
2. checked equivalences describing exactly what a separator would have to do;
3. proposed explicit languages whose completeness framework is not formalized.

Kuroda introduced the problem; Hartmanis and Hunt emphasized its exact
linear-space importance.  Savitch's simulation is quadratic here.

## Proved: complete-configuration pumping is shared

[`FiniteConfigurationPumpingBarrier.lean`](../../src/Langlib/Automata/LinearBounded/FiniteConfigurationPumpingBarrier.lean)
formalizes direct run pumping for an arbitrary finite relation.

For a right-unique relation with terminal final vertices,
`functional_acceptingPath_nodup` proves that a terminal-accepting orbit has no
repetition; `functional_accepts_iff_exists_bounded_simple_orbit` bounds its
visited vertices by the cardinality of the whole vertex type.

This is not a deterministic advantage.  In an arbitrary relation,
`arbitrary_path_has_bounded_simple_cut` deletes loops while preserving both
endpoints, and `arbitrary_accepts_iff_exists_bounded_simple_path` gives the
same bound.  Its LBA specialization is
`LBA.accepts_has_fullConfiguration_cutoff`:

$$
|\text{trace}|+1\leq |\mathrm{Cfg}|.
$$

The expanded bound is

$$
|Q|\,|\Gamma|^{n+1}(n+1).
$$

Thus repetition of a **complete configuration** pumps down a run for both an
LBA and a DLBA.  It does not pump the input word, and the resulting witness may
still be exponentially long.

For corridor computations, deleting a band between identical rows is the same
generic theorem on the row graph.  The number of rows is exponential in the
width, and loop deletion does not remove nondeterministic choice.

## Proved: functionality does not bound arbitrary raw crossings

[`IdentityClockCrossing.lean`](../../src/Langlib/Automata/LinearBounded/IdentityClockCrossing.lean)
starts from a one-state functional identity source.  Its operational
clock machine is proved functional by `identityClockMachine_functional` and
globally acyclic by `identityClockMachine_configurationAcyclic`.  Nevertheless,
`exists_identity_fullClock_stepTrace_crosses` gives a raw trace with at least
`6^(n+1) * (n+1)` crossings at every existing boundary (vacuous at `n = 0`).

After degree serialization, `exists_finalMachine_stepTrace_crosses_twoPow`
retains at least `2^(n+1)` crossings at every boundary.  This separate
`finalMachine` has:

- global acyclicity;
- directed indegree and outdegree at most two;
- a uniform partition into two directed partial-bijection layers.

The last property is **not** an exact two-matching theorem, and `finalMachine`
is not claimed to be functional.  The functional raw-crossing witness is the
pre-serialization clock machine.

The traces are not claimed accepting, necessary, or shortest.  They refute
bounds on arbitrary runs derived merely from functionality, acyclicity, degree
two, or biunique layers—not a language-level DLBA invariant.  A language lower
bound must constrain every presentation or selected accepting runs.

Chytil's crossing-bounded analysis isolates related restricted targets, while
Monien gives an equivalent unary two-way one-counter formulation.  Neither
supplies the missing general linear-space determinization.

## Proved: a constant selected-run crossing cap implies regularity

`LBA.BoundedCrossing.HasUniformAcceptingBound M c` has the weak existential
quantifier order

$$
\forall w,\quad M\text{ accepts }w\Longrightarrow
\exists\text{ an accepting trace whose every boundary count is at most }c.
$$

Not every accepting trace must satisfy the cap.  The finite-profile
construction verifies full one-cell histories—writes, entries, exits,
stationary and clamped moves, and the terminal event—rather than trusting bare
lists of control states.

The checked consequences are:

- `is_NFA_languageEnd_of_hasUniformAcceptingBound`;
- `is_DFA_languageEnd_of_hasUniformAcceptingBound`;
- `is_DLBA_languageEnd_of_hasUniformAcceptingBound`.

Thus the language is regular.  Pighizzini proves the corresponding theorem for
nondeterministic one-tape machines under the same weak measure.  The
implication therefore applies beyond deterministic presentations and is far
too strong to characterize all DLBAs.

## Proved arithmetic barrier; conjectural DLBA application

[`WordPumpingBarrier.lean`](../../src/Langlib/Automata/LinearBounded/WordPumpingBarrier.lean)
defines `HasBoundedAdditiveLengthPump`: beyond one fixed threshold, each
accepted word must admit a positive bounded length increment whose every
multiple is again represented by an accepted word.  For any supplied letter,
`unaryPow2At_not_hasBoundedAdditiveLengthPump` proves that
`{a^(2^(k+1)) | k ∈ ℕ}` fails this property.  The Bool specialization is
`unaryPow2_not_hasBoundedAdditiveLengthPump`.

The arithmetic failure is checked, but neither `is_DLBA unaryPow2` nor the
necessity of this pump for DLBAs is proved.  If the conventional deterministic
logspace algorithm for unary powers of two is formalized as a DLBA, the result
will refute this naive property as a necessary DLBA invariant; currently it is
not a separator theorem.

## Proved: proof-carrying pumping invariants

[`SeparationCandidates.lean`](../../src/Langlib/Automata/LinearBounded/SeparationCandidates.lean)
prevents a conjectured pumping property from silently being treated as a
separation theorem.  A `DLBAPumpingInvariant T` contains both

```lean
property : Language T -> Prop
necessary_of_is_DLBA : forall {L}, is_DLBA L -> property L
```

The necessity proof is data.  The theorem
`DLBAPumpingInvariant.isLBADLBASeparator_of_is_LBA_of_not` says that an LBA
language refuting such a proved invariant is an LBA/DLBA separator.  The
structure supplies neither an invariant nor its refuting language.

## Proved: linear choice and its quantifier order

`is_LinearChoiceLBA L` chooses one finite endmarker presentation `M` of `L`
and one constant `c`; every accepted word then has **some** accepting trace
with at most `c(|w|+2)` genuine branch events:

$$
\exists M\,\exists c\,\forall w\in L\,\exists\rho,
\quad \rho\text{ accepts }w\ \land\
\operatorname{choices}(\rho)\leq c(|w|+2).
$$

`is_LinearChoiceLBA_of_is_DLBA` supplies such a presentation with constant
zero.  Hence `linearChoiceInvariant` is a checked invariant.

The proposed anti-pumping property is

```lean
RequiresSuperlinearChoice L := is_LBA L ∧ ¬ is_LinearChoiceLBA L
```

Its important content is the negated existential over presentations:

$$
\forall M\text{ presenting }L\,\forall c\,\exists w\in L,
\quad\text{no accepting run of }M\text{ on }w
\text{ uses at most }c(|w|+2)\text{ choices}.
$$

This order is proved in both directions by
`exists_choiceBound_counterexample_of_requiresSuperlinearChoice` and
`requiresSuperlinearChoice_of_presentation_counterexamples`.  One machine is
insufficient.  No such language is known here, and
`LinearChoiceLBA ⊆ DLBA` is not established.

## Proved: exact candidate families and normal forms

`IsLBADLBASeparator L` is `is_LBA L ∧ ¬ is_DLBA L`, and
`exists_lbaDLBASeparator_iff_ne` identifies existence of such a language with
class inequality.  Three more precise families are checked.

### The encoded `languageOf` family

Each numeric LBA `code` determines one
`LBA.EncodedMembership.languageOf code`.  Adequacy says exactly that these are
all the LBA languages.  Consequently:

- `isLBADLBASeparator_languageOf_iff` reduces the pointwise question to
  failure of DLBA recognizability;
- `exists_lbaDLBASeparator_iff_encodedLanguage` says a separator exists iff
  some individual code's language is not DLBA;
- `lba_eq_dlba_iff_every_encodedLanguage` says equality holds iff every member
  of the family has a DLBA presentation.

This is a **family indexed by codes**.  It is not a theorem that the joint
language of all pairs `(code, word)` is one LBA-complete universal language.

### Three matching layers versus two

The checked identities are

$$
K\mathrm{MatchingLBA}(3)=\mathrm{LBA},\qquad
K\mathrm{MatchingLBA}(2)=\mathrm{DLBA}.
$$

Thus `RequiresThreeMatchingLayers L` is equivalent to
`IsLBADLBASeparator L`.  One may restrict further to globally acyclic,
degree-two, exact-three-matching presentations.  This neither produces a
language requiring layer three nor removes that layer.

### Restricted certified-row systems

`exists_lbaDLBASeparator_iff_restrictedRowReach` restricts the search to
acyclic, degree-two row relations with `Unit` certificates.  Every such row
language is LBA, but the system and finite alphabets remain existential; no
explicit separator is claimed.

## Why two existing constructions are not separators

The odometer system has `2^w` sequential relevant branches at width `w`, but
only in that presentation.  `RequiresSuperlinearChoice` quantifies over
**every** equivalent finite presentation.  Another machine need not replay
those diamonds, so this is not a language separation.

Nor is the encoded-membership evaluator.  `membershipBool_eq_true_iff` and
`membershipBool_computable` give an unrestricted decision procedure for a code
and word, using the full finite-configuration bound.  There is no proved
deterministic `O(n)`-space bound; decidability alone says nothing about DLBA.

## Conjectural future work: one fixed binary candidate

The next useful milestone is not another existential normal form, but one
explicit language over `Bool` together with exact linear-space completeness.
Three natural choices are:

1. **Succinct directed reachability.**  A circuit `C` defines edges between
   `m`-bit vertices; ask if `s` reaches `t`.  Compare it with functional-circuit
   orbit reachability.  This follows Galperin–Wigderson's succinct graphs and
   Savitch's threadable-maze viewpoint.
2. **A fixed universal corridor system.**  Fix one finite row verifier, encode
   its boundary rows in binary, and simulate every LBA with linear width
   expansion.  Repeated-row deletion remains the shared graph cutoff.
3. **Bounded universal LBA acceptance.**  Encode `(M,x,1^s)` and ask for an
   accepting computation using `s` universal tape bits.  The unary bit budget
   avoids a hidden alphabet factor; deterministic code gives functional orbit
   reachability.

These encodings and completeness results are not yet proved in Langlib.

They first require a reduction notion that preserves the exact resource:

- the reduction is deterministic and computable in at most linear space
  (a logspace transducer would be stronger);
- its output length is at most `c|x|+d` for fixed constants;
- reduction composition and closure of `LBA` and `DLBA` under the reduction
  are proved.

Computable or polynomial-time reductions are too coarse.  With this framework,
putting an NSPACE-linear-complete fixed candidate in `DLBA` would be equivalent
to `LBA = DLBA`.

## References

- S.-Y. Kuroda, [*Classes of Languages and Linear-Bounded Automata*](https://doi.org/10.1016/S0019-9958(64)90120-2), 1964.
- Walter J. Savitch, [*Relationships between Nondeterministic and Deterministic Tape Complexities*](https://doi.org/10.1016/S0022-0000(70)80006-X), 1970.
- Juris Hartmanis and Harry B. Hunt III, [*The LBA Problem and its Importance in the Theory of Computing*](https://hdl.handle.net/1813/6015), 1973.
- Michal P. Chytil, [*Crossing-Bounded Computations and their Relation to the LBA-Problem*](https://www.kybernetika.cz/content/1976/2/76/paper.pdf), 1976.
- Burkhard Monien, [*The LBA-Problem and the Deterministic Tape Complexity of Two-Way One-Counter Languages over a One-Letter Alphabet*](https://digital.ub.uni-paderborn.de/hsx/download/pdf/42059), 1977.
- Giovanni Pighizzini, [*Nondeterministic One-Tape Off-Line Turing Machines and Their Time Complexity*](https://arxiv.org/abs/0905.1271), 2009.
- Hana Galperin and Avi Wigderson, [*Succinct Representation of Graphs*](https://www.math.ias.edu/avi/node/751), 1983.
