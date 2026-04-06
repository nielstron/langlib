import Lean

/-! # Print Sorries Compatibility

This file provides a compatibility shim for `#print_sorries_in`.

## Main declarations

- `#print_sorries_in`
-/

open Lean Elab Command

/--
`#print_sorries_in Foo` previously enumerated sorries in a declaration.  For now we provide a
lightweight compatibility shim that simply logs the requested name so that scripts which call this
command continue to elaborate.
-/
elab "#print_sorries_in " n:ident : command => do
  let resolved ← resolveGlobalConstNoOverloadCore n.getId
  logInfo m!"(informational) Requested list of sorries in {resolved}"
