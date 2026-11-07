import Flapjack.Compiler.Backend.BvlInline.TickInline
import Flapjack.Compiler.Backend.BvlInline.Recursion

/-! Total source-shaped BVL program inlining. -/
namespace Flapjack.Compiler.Backend.BvlInline
open Bvl

/-- Inline program entries in order, accumulating their transformed bodies. -/
@[hol "cakeml/compiler/backend/bvl_inlineScript.sml" "tick_inline_all_def"]
def tickInlineAll (limit : Nat) : Spt (Nat × Exp) → List (Nat × Nat × Exp) →
    List (Nat × Nat × Exp) → Spt (Nat × Exp) × List (Nat × Nat × Exp)
  | cache, [], acc => (cache, acc.reverse)
  | cache, (name, arity, body) :: rest, acc =>
    let body := tickInlineSing cache body
    let cache := if mustInline name limit body then sptInsert name (arity, body) cache else cache
    tickInlineAll limit cache rest ((name, arity, body) :: acc)

/-- Compile all entries with the supplied initial inlining cache. -/
@[hol "cakeml/compiler/backend/bvl_inlineScript.sml" "tick_compile_prog_def"]
def tickCompileProg (limit : Nat) (cache : Spt (Nat × Exp))
    (program : List (Nat × Nat × Exp)) : Spt (Nat × Exp) × List (Nat × Nat × Exp) :=
  tickInlineAll limit cache program []

end Flapjack.Compiler.Backend.BvlInline
