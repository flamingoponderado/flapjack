import Flapjack.Compiler.Backend.Semantics.ClosSem.Apply

/-! Memory observations from `scripts/hol-probes/clos_sem_memory_probe.out`.
The HOL byte-update capture retains an unreduced word-existence condition. -/
namespace Flapjack.Test.ClosSemMemoryParity
open Flapjack Flapjack.Compiler.Backend.ClosSem

private def array : HolFiniteMapExact Nat (Ref Value) :=
  HolFiniteMapExact.empty.updateEq (0, .valueArray [.number 4, .number 9])
private def bytes : HolFiniteMapExact Nat (Ref Value) :=
  HolFiniteMapExact.empty.updateEq (0, .byteArray [1, 2, 3, 4])

example {C F : Type} (s : State C F) :
    (applyMemory .el [.refPtr true 0, .number 1] { s with refs := array }).map Prod.fst =
      some (.number 9) := rfl
example {C F : Type} (s : State C F) :
    (applyMemory .el [.refPtr true 0, .number (-1)] { s with refs := array }).map Prod.fst = none := rfl
example {C F : Type} (s : State C F) :
    (applyMemory .updateByte [.refPtr true 0, .number 1, .number 7] { s with refs := bytes }).map
      (fun pair => pair.2.refs.lookup 0) = some (some (.byteArray [1, 7, 3, 4])) := rfl
example {C F : Type} (s : State C F) :
    (applyMemory (.copyByte false) [.refPtr true 0, .number 0, .number 3, .refPtr true 0, .number 1]
      { s with refs := bytes }).map (fun pair => pair.2.refs.lookup 0) = some (some (.byteArray [1, 1, 2, 3])) := rfl
example {C F : Type} (s : State C F) :
    (applyMemory (.boundsCheckByte true) [.byteVector [1, 2], .number 2] s).map Prod.fst = some (.block 1 []) := rfl
example {C F : Type} (s : State C F) :
    (applyMemory (.boundsCheckByte false) [.byteVector [1, 2], .number 2] s).map Prod.fst = some (.block 0 []) := rfl

example {C F : Type} (s : State C F) :
    doApp (.memOp .el) [.refPtr true 0, .number 1] { s with refs := array } =
      .val (.number 9, { s with refs := array }) := rfl
example {C F : Type} (s : State C F) :
    doApp (.memOp .el) [.refPtr true 0, .number (-1)] { s with refs := array } =
      .err (.abort .typeError) := rfl

end Flapjack.Test.ClosSemMemoryParity
