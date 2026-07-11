module

public import Langlib.Grammars.Indexed.NormalForm.AhoOverlayMode

@[expose]
public section

/-!
# Terminal leaves in copy-on-write overlay mode

A terminal leaf never consumes an inherited flag.  Since a nonempty overlay exposes at least
one visible flag, the overlay interface is vacuous for terminal parses.
-/

variable {T : Type}

namespace IndexedGrammar
namespace Aho

/-- A terminal parse cannot be entered with a nonempty private overlay. -/
public theorem overlayScheduleRun_terminal_false
    {g : IndexedGrammar T} [Fintype g.nt]
    {A : g.nt} {stack : List g.flag} {a : T}
    {r : IRule T g.nt g.flag}
    (hr : r ∈ g.rules) (hlhs : r.lhs = A) (hc : r.consume = none)
    (hrhs : r.rhs = [IRhsSymbol.terminal a]) :
    OverlayScheduleRun (NFParse.terminal (σ := stack) hr hlhs hc hrhs) := by
  intro input head overlayTail protectedFlags hidden blocks owners word used hstack
    baseLayout overlayLayout hall
  have htop := hall 0 overlayLayout.flags_length_pos
  exact False.elim (by simpa [NFParse.ConsumesAt] using htop)

end Aho
end IndexedGrammar

end
