module

public import Langlib.Automata.DeterministicPushdown.Totalization.AnnotatedStack
public import Langlib.Automata.DeterministicPushdown.Totalization.Construction
public import Langlib.Automata.DeterministicPushdown.Totalization.Definition
public import Langlib.Automata.DeterministicPushdown.Totalization.EpsilonPhase
public import Langlib.Automata.DeterministicPushdown.Totalization.Presentation
public import Langlib.Automata.DeterministicPushdown.Totalization.RegularAnalysis
public import Langlib.Automata.DeterministicPushdown.Totalization.Saturation
public import Langlib.Automata.DeterministicPushdown.Totalization.StackSummary
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Height.Basic
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
@[expose]
public section



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
