module

public import Langlib.Grammars.Indexed.NormalForm.AhoOwnerRelabel

@[expose]
public section

/-!
# Retired shadow-head sealing layer

Persistent compressed indices now draw owners exclusively from `genericOwnerRange`, which is
disjoint from both semantic event-owner windows.  The former sealing operation swapped a
generic pool owner with a semantic shadow ticket and therefore could not preserve
`IndexOwnerPool`.  Runner code now keeps its generic physical owner and classifies it directly as
outside both semantic windows, so no sealing operation is required.

This compatibility module intentionally exports no sealing API.  It remains as an import shim for
downstream developments while the valid cursor and layout relabelling lemmas continue to live in
`AhoOwnerRelabel`.
-/
