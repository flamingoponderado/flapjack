import Flapjack.Compiler.Backend.WordToStack.StubNames
import Flapjack.Compiler.Backend.StackAlloc.StubNames
namespace Flapjack.Test.BackendRuntimeStubNamesParity
open Flapjack.Basis.Pure.MlString
private def wordNames := Flapjack.Compiler.Backend.WordToStack.stubNames ()
private def gcNames := Flapjack.Compiler.Backend.StackAlloc.stubNames ()
example : wordNames.map (fun p => (p.1, p.2.explode.map BitVec.toNat)) =
    [(5,[95,82,97,105,115,101]), (6,[95,83,116,111,114,101,67,111,110,115,116,115])] := by decide
example : gcNames.map (fun p => (p.1, p.2.explode.map BitVec.toNat)) =
    [(4,[95,71,67])] := by decide
example : wordNames.map (fun p => (p.1, toStringOfBytes p.2)) =
    [(5,"_Raise"),(6,"_StoreConsts")] := by decide
example : gcNames.map (fun p => (p.1, toStringOfBytes p.2)) = [(4,"_GC")] := by decide
example : wordNames.length = 2 := by decide
example : gcNames.length = 1 := by decide
end Flapjack.Test.BackendRuntimeStubNamesParity
