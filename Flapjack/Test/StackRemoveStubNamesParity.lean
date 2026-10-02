import Flapjack.Compiler.Backend.StackRemove.StubNames
namespace Flapjack.Test.StackRemoveStubNamesParity
open Flapjack.Compiler.Backend.StackRemove
open Flapjack.Basis.Pure.MlString
example : ((stubNames ()).map fun pair => (pair.1, pair.2.explode.map BitVec.toNat)) =
    [(0, [95,73,110,105,116]), (1, [95,72,97,108,116,48]),
     (2, [95,72,97,108,116,50])] := by decide
example : (stubNames ()).length = 3 := by decide
example : ((stubNames ()).map fun pair => (pair.1, toStringOfBytes pair.2)) =
    [(0, "_Init"), (1, "_Halt0"), (2, "_Halt2")] := by decide
example {width : Nat} [NeZero width] (generateGc : Bool) (heap pointer start : Nat) :
    (initStubs (width := width) generateGc heap pointer start).length + 2 =
      Flapjack.stackNumStubs := checkInitStubsLength generateGc heap pointer start
example : (initStubs (width := 8) false 0 0 0).length + 2 = 5 :=
  checkInitStubsLength false 0 0 0
example : (initStubs (width := 64) true 1024 7 99).length + 2 = 5 :=
  checkInitStubsLength true 1024 7 99
example : (initStubs (width := 1) true 1 2 3).length + 2 = 5 :=
  checkInitStubsLength true 1 2 3
end Flapjack.Test.StackRemoveStubNamesParity
