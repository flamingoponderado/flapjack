module

public import Flapjack.RiscV.PipelineDiagnostics
public import Flapjack.Compiler.Backend.WordToStack.ProductionFlatCodec
public import Flapjack.Compiler.Backend.RegAlloc.ProductionExtraction

@[expose] public section

/-! Actual move-domain infrastructure. There is no standalone HOL declaration
for the production colouring carrier. Bounds are derived from emitted moves
and the real allocator frame formula, rather than assumed for a caller.
Whole production routing and call/ABI producer coverage remain separate. -/
namespace Flapjack.ProductionMoveDomain
open RiscV RiscV.CakeRegAlloc

theorem registerArgument_index {α : Type} (arguments : List α) (k index : Nat)
    (member : index ∈ List.range (arguments.take k).length) : index < k := by
  have bound := List.mem_range.mp member
  rw [List.length_take] at bound
  omega

/-- The actual returning-call producer uses `take (k-1)` and ABI base one.
Every emitted destination is therefore below k, even with empty frames. -/
theorem valueArgument_index {α : Type} (arguments : List α) (k index : Nat)
    (member : index ∈ List.range (arguments.take (k - 1)).length) : 1 + index < k := by
  have bound := List.mem_range.mp member
  rw [List.length_take] at bound
  omega

end Flapjack.ProductionMoveDomain
