import Langlib.Classes.ContextFree.Closure.Union
import Langlib.Classes.ContextFree.Closure.Reverse
import Langlib.Classes.ContextFree.Closure.Concatenation
import Langlib.Classes.ContextFree.Closure.Intersection
import Langlib.Classes.ContextFree.Closure.Complement

import Langlib.Classes.Regular.Closure.Complement
import Langlib.Classes.Regular.Closure.Intersection
import Langlib.Classes.Regular.Closure.Prefix
import Langlib.Classes.Regular.Closure.Suffix
import Langlib.Classes.Regular.Closure.Reverse
import Langlib.Classes.Regular.Closure.Union

import Langlib.Classes.RecursivelyEnumerable.Closure.Union
import Langlib.Classes.RecursivelyEnumerable.Closure.Reverse
import Langlib.Classes.RecursivelyEnumerable.Closure.Concatenation

import Langlib.Utilities.LanguageOperations
import Langlib.Utilities.WrittenByOthers.PrintSorries


/-! # Closure Theorem Checks

This file checks that the main closure and non-closure theorems elaborate.

## Main declarations

- `CF_of_CF_u_CF`
- `CF_of_reverse_CF`
- `CF_of_CF_c_CF`
- `nnyCF_of_CF_i_CF`
- `nnyCF_of_complement_CF`
- `RE_of_RE_u_RE`
- `RE_of_reverse_RE`
- `RE_of_RE_c_RE`
- `Language.prefixLang`
- `Language.suffixLang`
- `Language.IsRegular.prefixLang`
- `Language.IsRegular.suffixLang`
- `Language.IsRegular.add'`
- `Language.IsRegular.inf'`
- `Language.isRegular_compl_iff`
- `Language.isRegular_reverse_iff'`
-/

section language_operations

#check            Language.prefixLang
#check            Language.suffixLang
#check            Language.prefixLang_prefixLang
#check            Language.suffixLang_eq_reverse_prefixLang_reverse

end language_operations

section regular

#check            Language.IsRegular.prefixLang
#check            Language.IsRegular.suffixLang
#check            Language.isRegular_reverse_iff'
#check            Language.IsRegular.add'
#check            Language.IsRegular.inf'
#check            Language.isRegular_compl_iff

end regular

section context_free

#check            CF_of_CF_u_CF
#print_sorries_in CF_of_CF_u_CF

#check            CF_of_reverse_CF
#print_sorries_in CF_of_reverse_CF

#check            CF_of_CF_c_CF
#print_sorries_in CF_of_CF_c_CF

#check            nnyCF_of_CF_i_CF
#print_sorries_in nnyCF_of_CF_i_CF

#check            nnyCF_of_complement_CF
#print_sorries_in nnyCF_of_complement_CF

end context_free


section unrestricted

#check            RE_of_RE_u_RE
#print_sorries_in RE_of_RE_u_RE

#check            RE_of_reverse_RE
#print_sorries_in RE_of_reverse_RE

#check            RE_of_RE_c_RE
#print_sorries_in RE_of_RE_c_RE

end unrestricted
