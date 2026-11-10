module

public import Flapjack.Pancake.CrepToLoop.ContextExact

@[expose] public section

/-! Direct parity for `crep_to_loop$ocompile` (`crep_to_loopScript.sml:216`).
The expected shapes are copied from `scripts/hol-probes/ocompile_probe.out`;
the return case intentionally checks the right-associated `nested_seq` shape,
including the trailing `Skip` retained by CakeML's optimizer. -/

namespace Flapjack.Test.OCompileParity

def sourceContext : LoopContext Nat :=
  { vars := [(1, 5)], functions := [], maxVar := 0, target := .rv64i }

def ffiSourceContext : LoopContext Nat :=
  { vars := [(1, 5), (2, 6), (3, 7), (4, 8)], functions := [], maxVar := 4,
    target := .rv64i }

end Flapjack.Test.OCompileParity
