---
title: "Indexed ⊆ context-sensitive"
description: "A formal Lean 4 proof that every indexed language is context-sensitive, via Aho's finite compression, a linear-space scheduler, and a certified row system."
parent: "Context-sensitive"
nav_order: 3
---

# Every indexed language is context-sensitive

## Statement

Every indexed language is context-sensitive:

```lean
public theorem Indexed_subclass_CS :
    (Indexed : Set (Language T)) ⊆ (CS : Set (Language T))
```

The pointwise form is `is_CS_of_is_Indexed`. Both statements hold for an arbitrary
terminal type `T`: the final theorem assumes no finite alphabet, decidable equality,
inhabitedness, or epsilon-freeness.

The constructive core is `finite_normalForm_indexed_language_is_LBA_pos`. For a
finite normal-form indexed grammar, it constructs a marker-free positive-input linear
bounded automaton. The class-level reduction then removes the finiteness and normal-form
assumptions and handles the possible empty word.

## In Lean

The final declaration chain is:

1. `IndexedGrammar.Aho.complete_bounded` gives a uniformly bounded accepting run for
   every concrete normal-form parse.
2. `language_eq_paddedReachLanguage_of_bounded_complete` identifies the grammar
   language with semantic padded-row reachability.
3. `paddedReachLanguage_eq_rowReachLanguage` identifies semantic reachability with
   the language of an executable certified row system.
4. `is_LBA_pos_paddedReachLanguage` compiles that finite row system into a
   positive-input LBA.
5. `IndexedGrammar.Aho.is_LBA_pos_language` packages the finite normal-form core.
6. `finite_normalForm_indexed_language_is_LBA_pos`,
   `is_CS_of_is_Indexed`, and finally `Indexed_subclass_CS` lift the core to the
   language classes.

A useful separation of concerns is that completeness is parse-directed and uses normal
form, while `ahoMachine_sound` is unconditional once a composite-machine run has been
supplied.

## Proof pipeline

| Stage | Main object | Capstone |
| --- | --- | --- |
| Finite-support normalization | A finite normal-form grammar and a letter map for the nonempty part of the language | `is_Indexed_exists_fintype_normalForm_nonempty_image` |
| Compressed machine | Finite work symbols and fourteen finite composite certificates | `CompositeStep` |
| Parse-directed scheduler | A ghost-annotated run whose erasure is a machine run | `complete_bounded` |
| Fixed-width row encoding | Twenty-one logical work slots packed into each physical input cell | `paddedReachLanguage` |
| Certified checker | A finite synchronized row system checking adjacent padded rows | `ahoRowSystem_rowStep_iff_paddedRowStep` |
| LBA compilation | The generic certified-row-system compiler | `is_LBA_pos_paddedReachLanguage` |
| Class-level lift | Epsilon-free homomorphic image, optional epsilon restoration, and the empty-alphabet case | `Indexed_subclass_CS` |

In compact form:

```text
indexed language L
  → finite-support normal-form grammar g
  → normal-form parse
  → Aho run bounded by 21 · |w|
  → semantic padded-row reachability
  ↔ certified-row-system reachability
  → positive-input LBA
  → context-sensitive nonempty part
  → context-sensitive L
```

## Scope and placement

In this development, **Aho** names the finite normal-form indexed-grammar-to-LBA
construction, not a new general-purpose automaton model. Its work alphabet,
configurations, transition certificates, scheduler tasks, and row cells are all
parameterized by a concrete `IndexedGrammar`; parse-directed completeness additionally
uses the four constructors of `NFParse` supplied by indexed-grammar normal form.

The construction therefore lives under
`Langlib.Grammars.Indexed.NormalForm.Aho`. The genuinely reusable automata layer is
`CertifiedRowSystem`, which remains under `Langlib.Automata.LinearBounded`; `ahoRowSystem`
is the grammar-specific instance compiled through that abstraction. The class-level
principle for arbitrary indexed languages is `Indexed_subclass_CS`, kept separately under
`Langlib.Classes.Indexed.Inclusion` because it also performs finite-support normalization,
homomorphic transport, and empty-word restoration.

The source hierarchy mirrors the proof dependencies:

```text
Aho/
├── Compression, ParseCertificate
├── Machine/
├── Scheduler/
│   ├── Accounting, ParseRoutes, Invariant, Pop, Moves, Execution
│   ├── BoundedAccounting, GhostLayout, CompressedState
│   ├── EventCompatibility
│   ├── Ownership/
│   ├── Resources/
│   ├── Runners/{Plain, Protected, Overlay}/
│   └── Completeness
├── RowSystem/
├── Soundness/
└── Inclusion
```

## Aho's compressed machine

An indexed grammar carries an unbounded stack of flags, so a direct simulation would
not fit on a linearly bounded tape. The construction replaces a concrete flag block by
the finite relation it induces on nonterminals. This relation is `CFlag`; because the
grammar has finitely many nonterminals, the type of such Boolean relations is finite.

The finite logical work alphabet is `WorkSym`:

- `plain A` is an ordinary pending nonterminal;
- `live A` promises that expansion of `A` consumes a represented inherited
  occurrence;
- `index R d` is a compressed flag block with relation `R` and a finite mark `d`;
- terminal symbols are matched against the immutable input track;
- `dollar`, `close`, and `hash` delimit frames and the outer work word.

A configuration `Config` contains an input position and a zipper `WorkCursor`.
The initial word is `$ S #`; the accepting word is `$ #` with the input position at
the end of the word.

`CompositeCert` is a finite, fourteen-case certificate alphabet. Its cases cover
plain and live binary rules, pushes that skip, create, or extend a compressed block,
plain and live pops, terminal matching, index erasure, and frame return.
`CertStep` gives the exact cursor transformation selected by one certificate, and
`CompositeStep` existentially chooses a certificate.

The machine modules are deliberately layered:

- `Langlib.Grammars.Indexed.NormalForm.Aho.Machine.Alphabet` defines marks and the
  finite work alphabet.
- `Langlib.Grammars.Indexed.NormalForm.Aho.Machine.Transitions` defines cursors,
  configurations, certificates, and semantic steps.
- `Langlib.Grammars.Indexed.NormalForm.Aho.Machine.PaddedRows` defines the
  fixed-width encoding.
- `Langlib.Grammars.Indexed.NormalForm.Aho.Machine.BoundaryScans` and
  `Langlib.Grammars.Indexed.NormalForm.Aho.Machine.LocalEdits` give finite scans for
  boundary rows and local edits.
- `Langlib.Grammars.Indexed.NormalForm.Aho.Machine.Reachability`,
  `Langlib.Grammars.Indexed.NormalForm.Aho.Machine.InputSafety`, and
  `Langlib.Grammars.Indexed.NormalForm.Aho.Machine.PaddedReach` package the bounded
  semantic reachability relation.

## Parse-directed completeness

There are two completeness theorems.

`complete_of_nfparse` is the semantic theorem: every concrete `NFParse` has an
accepting reflexive-transitive composite-machine run. The final construction needs the
stronger `complete_bounded`, which proves that every intermediate logical work word
has length at most `21 * input.length`.

The bounded proof enriches the finite work word with ghost information:

- pending tasks remember their concrete parse and input interval;
- compressed indices carry concrete flag blocks and productive-event owners;
- open frames remember the persistent index that owns them;
- ticket ledgers make logical ownership injective across relabelling;
- primary and shadow provenance record which productive event justifies each block;
- a free-owner pool and a scalar credit record reusable capacity.

All of this data erases to the finite `WorkSym` machine. It is proof state, not part
of the compiled LBA alphabet.

### Ordinary and overlay execution

The bounded runner has two mutually constructed modes.

**Ordinary execution** handles plain tasks and tasks protected by an existing
represented block. Binary children may share the protected suffix after their
branch-local work has been sealed.

**Overlay execution** is copy-on-write. A branch may push or compress private blocks
without mutating the sibling-shared protected suffix. When an overlay is attached to a
parked base block, `OverlayRestoreData` carries the displaced nonparking ticket until
the last private block is erased. `OverlayParkingContext` distinguishes strict entry
from attached entry and makes restoration explicit.

`CompleteScheduleRuns` combines ordinary and overlay execution.
`completeScheduleRuns` constructs both simultaneously by strong recursion on parse
node count, and `complete_bounded` invokes the plain root projection.

### Why the bound is 21

For nonempty input of length `n`, `ScheduleInvariant` records:

- at most `n` task or terminal payloads;
- at most `6n` persistent compressed indices;
- at most one open frame per persistent index;
- the shape inequality
  `word.length ≤ tasks + indices + 2 * frames + 2`.

Therefore

```text
word.length ≤ n + 6n + 2(6n) + 2
            = 19n + 2
            ≤ 21n.
```

This is `ScheduleInvariant.word_length_le_twenty_one_mul`. The positivity needed for
the final inequality comes from the fact that every normal-form parse has a nonempty
yield.

The number 21 counts **logical work slots per input symbol**, not physical LBA tape
cells. `workWidth` packs those 21 slots into the finite alphabet of one physical row
cell, so an input of length `n` is still recognized on exactly `n` physical cells.
The source notes that Aho's paper has a sharper constant; 21 is the bound maintained by
the current persistent scheduler invariant.

## Semantic soundness

Soundness interprets every logical work configuration as an indexed-grammar
sentential form.

The block denotation distinguishes visible compressed blocks from hidden stack gaps.
A plain push may leave a hidden gap; a live nonterminal starts at a visible block.
Nested `dollar`/ `close` frames describe suspended control contexts, and the
whole-tape interpreter `ExecRep` reads the zipper in execution order.

The soundness layers are:

- `Langlib.Grammars.Indexed.NormalForm.Aho.Soundness.Denotation.Block` for visible
  blocks, hidden decorations, segments, and nested frames;
- `Langlib.Grammars.Indexed.NormalForm.Aho.Soundness.Denotation.Control` for the
  whole-tape control interpretation;
- `Langlib.Grammars.Indexed.NormalForm.Aho.Soundness.Block` and
  `Langlib.Grammars.Indexed.NormalForm.Aho.Soundness.Control` for the grammar effect
  of local and structural edits;
- `Langlib.Grammars.Indexed.NormalForm.Aho.Soundness.Certificates` for the
  certificate-by-certificate `StepEffect` theorem;
- `Langlib.Grammars.Indexed.NormalForm.Aho.Soundness.Acceptance` for the forward
  derivation invariant and accepting-run soundness.

The forward invariant says that the grammar start symbol derives the already consumed
input prefix followed by the sentential form represented by the remaining work tape.
At the accepting configuration the represented remainder is empty, so
`ahoMachine_sound` concludes that the grammar generates the input.

## The certified row checker

The semantic machine relation is not itself the final automaton. It is compiled through
a finite synchronized row checker.

Each physical input cell is either a raw input letter or a running cell containing:

- the same immutable input letter;
- a bit recording whether that position has been consumed;
- one `WorkBlock` of 21 optional logical work slots.

`ahoRowSystem` scans an old row, a new row, and a row of finite certificates from left
to right. Its work state remembers the current phase and two slots of lookbehind on
each row. Two slots suffice because every composite move changes the local word by at
most two positions. The scan also enforces canonical `some* none*` padding, so blanks
cannot hide a malformed suffix.

The row proof is split by direction:

- `Langlib.Grammars.Indexed.NormalForm.Aho.RowSystem.WorkCompleteness` constructs an
  accepting logical trace for every semantic certificate;
- `Langlib.Grammars.Indexed.NormalForm.Aho.RowSystem.Completeness` packs those traces
  and proves semantic step implies physical row step;
- `Langlib.Grammars.Indexed.NormalForm.Aho.Soundness.RowInput` decodes the immutable
  input track;
- the modules below
  `Langlib.Grammars.Indexed.NormalForm.Aho.Soundness.RowWork` invert replacement,
  shifting, pop, and frame-return scans;
- `Langlib.Grammars.Indexed.NormalForm.Aho.Soundness.RowSystem` proves physical row
  step implies semantic step.

The one-step equivalence is
`ahoRowSystem_rowStep_iff_paddedRowStep`. Its reachability corollary is
`paddedReachLanguage_eq_rowReachLanguage`. Finally the generic
`CertifiedRowSystem.is_LBA_pos_rowReachLanguage` compiler yields
`is_LBA_pos_paddedReachLanguage`.

## From the finite core to every indexed language

The Aho core assumes a finite terminal alphabet, finite nonterminals and flags,
decidable equality where the executable construction needs it, and a normal-form
grammar. The class theorem removes all of those assumptions.

For a nonempty terminal alphabet,
`is_Indexed_exists_fintype_normalForm_nonempty_image` supplies:

- a finite auxiliary terminal alphabet;
- a finite normal-form indexed grammar over that alphabet;
- a letter map whose non-erasing homomorphic image is the nonempty part of the original
  language.

The finite grammar is recognized by `is_LBA_pos_language`, hence its language is
context-sensitive. Context-sensitive languages are closed under epsilon-free
homomorphisms, so the nonempty part of the original language is context-sensitive.
`is_CS_of_diff_empty_of_is_CS` restores the optional empty word.

If the terminal type is empty, every word is empty and every language is finite, so the
result follows from finite-language context-sensitivity. This is why
`Indexed_subclass_CS` needs no `Inhabited T` or `Fintype T` assumption.

The positive-input LBA core and the empty-word lift should not be conflated:
`is_LBA_pos` has exactly `|w|` physical cells and therefore recognizes only
nonempty inputs; the class-level theorem separately handles epsilon.

## Reading and maintenance guide

A productive reading order is:

1. `Aho.Compression` and `Aho.ParseCertificate`;
2. `Machine.Alphabet` and `Machine.Transitions`;
3. `Scheduler.ParseRoutes`, `Scheduler.Invariant`, and
   `Scheduler.Resources.RunResources`;
4. `Scheduler.Runners.Plain` and the protected and overlay runner subtrees, ending at
   `Scheduler.Completeness`;
5. the block and control denotations;
6. certificate and acceptance soundness;
7. the row-system completeness and soundness directions;
8. `Aho.Inclusion` and the class-level capstone.

The central maintenance boundaries are:

- ghost scheduler state must erase to the finite composite machine;
- the bounded proof may strengthen ghost invariants but must not enlarge the finite
  executable alphabet;
- machine soundness is independent of the completeness scheduler;
- row-system completeness and soundness remain separate directional modules;
- the value of `workWidth` must agree with the scheduler's proved logical-word bound.

## Verification

The focused development and its class-level capstone can be checked with:

```sh
lake build Langlib.Grammars.Indexed.NormalForm.Aho.Inclusion
lake build Langlib.Classes.Indexed.Inclusion.ContextSensitive
```

The complete repository is checked with:

```sh
lake build
```

Tracked prose documentation is validated with:

```sh
python3 scripts/link_theorems.py --check
```

## Keywords / also known as

indexed languages are context-sensitive, Indexed subset CSL, Aho indexed grammar
simulation, indexed grammar to linear bounded automaton, finite compression of index
stacks, nested stack language inclusion, `Indexed_subclass_CS`.

Formalized in Lean 4 with Mathlib, in [Langlib](https://github.com/nielstron/langlib).
