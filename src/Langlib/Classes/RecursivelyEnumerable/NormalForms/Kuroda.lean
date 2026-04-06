import Langlib.Classes.RecursivelyEnumerable.Definition


/-! # Kuroda Normal Form Skeleton

This file defines Kuroda grammars and states existence of a Kuroda presentation for every recursively enumerable language.

## Main declarations

- `grule_of_kuroda_rule`
- `grammar_of_kuroda_grammar`
- `kuroda_grammar_always_exists`
-/

/-- Transformation rule for a grammar in the Kuroda normal form. -/
inductive kuroda_rule (T : Type) (N : Type) : Type where
  | two_two (A B C D : N)   : kuroda_rule T N
  | one_two (A B C : N)     : kuroda_rule T N
  | one_one (A : N) (t : T) : kuroda_rule T N
  | one_nil (A : N)         : kuroda_rule T N

/-- Grammar in the Kuroda normal form that generates words
    over the alphabet `T` (a type of terminals). -/
structure kuroda_grammar (T : Type) where
  nt : Type
  initial : nt
  rules : List (kuroda_rule T nt)


def grule_of_kuroda_rule {T : Type} {N : Type} : kuroda_rule T N → grule T N
| (kuroda_rule.two_two A B C D) => grule.mk [] A [symbol.nonterminal B] [symbol.nonterminal C, symbol.nonterminal D]
| (kuroda_rule.one_two A B C)   => grule.mk [] A [] [symbol.nonterminal B, symbol.nonterminal C]
| (kuroda_rule.one_one A t)     => grule.mk [] A [] [symbol.terminal t]
| (kuroda_rule.one_nil A)       => grule.mk [] A [] []

def grammar_of_kuroda_grammar {T : Type} (k : kuroda_grammar T) : grammar T :=
grammar.mk k.nt k.initial (List.map grule_of_kuroda_rule k.rules)
