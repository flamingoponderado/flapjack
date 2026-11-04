import Flapjack.RiscV.Allocator

namespace Flapjack.RiscV

/-!
# Flatten Word expressions before allocation

Cake's `crep_to_loop` pass turns expression trees into assignments to fresh
Loop temporaries before the Word allocator sees them.  A few Word expressions
can nevertheless be reconstructed by the current Loop-to-Word boundary (for
example the address arithmetic in `topAddr`).  The old RISC-V lowering tried
to evaluate those trees directly with four reserved registers, which made
the result depend on accidental dead registers and rejected large real
functions such as `op_extcodecopy`.

The source-facing boundary now preserves the Word expression shape exactly as
Cake does.  The helper definitions below remain available for explicit
temporary-pool adapters, but `wordFlattenProgramFrom` is intentionally the
identity used by the production source pipeline.
The explicit helper below still models the Word-to-Stack expression compiler's
temporary pool: nested nodes consume reserved registers and `ror` nodes
consume two.  Callers that deliberately need a pool-safe materialisation can
use those helpers; the source-facing adapter does not apply them implicitly.
-/

/-! Pool consumption of the Word-to-Stack expression compiler.  Binary
    operators draw one pool entry for the right subtree and recurse with the
    remaining pool; rotate nodes draw two (a destination distinct from the
    scratch target plus the right subtree); wider operator applications draw
    one entry and recurse with the remainder for every argument; loads reuse
    their target and pool.  Pairs of atoms use fallback registers and consume
    nothing.  `wordProgFirstExpressionLoweringFailure` reports the first
    expression that needs more entries than the pool provides. -/

/-- The reserved pool holds the four scratch registers minus the lowering
    target.  Materialize exactly the expressions that could exceed it; free
    allocator registers can only enlarge the pool. -/
def wordFlattenBudgetLimit : Nat := 3

end Flapjack.RiscV
