import Langlib.Classes.DeterministicContextFree.Totalization.AnnotatedStack
import Langlib.Classes.DeterministicContextFree.Totalization.Construction
import Langlib.Classes.DeterministicContextFree.Totalization.Definition
import Langlib.Classes.DeterministicContextFree.Totalization.EpsilonPhase
import Langlib.Classes.DeterministicContextFree.Totalization.Presentation
import Langlib.Classes.DeterministicContextFree.Totalization.RegularAnalysis
import Langlib.Classes.DeterministicContextFree.Totalization.Saturation
import Langlib.Classes.DeterministicContextFree.Totalization.StackSummary

/-! # DPDA Totalization for Deterministic Context-Free Languages

This module is the public import point for the totalization construction used by
unconditional complement closure of deterministic context-free languages.

The implementation is split into:

* `Definition`: language-level deciding presentations;
* `EpsilonPhase`: semantic epsilon-only DPDA phases;
* `Saturation`: finite P-automata saturation for epsilon lookahead;
* `RegularAnalysis`: packaged regular epsilon analyses;
* `StackSummary`: finite stack-summary annotations;
* `AnnotatedStack`: annotated totalizer stack symbols and lookahead queries;
* `Construction`: the analyzed totalized DPDA and its correctness;
* `Presentation`: the language-level totalization theorem.
-/
