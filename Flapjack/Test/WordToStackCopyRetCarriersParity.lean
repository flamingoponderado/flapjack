import Flapjack.Compiler.Backend.WordToStack.NativeReturn
import Flapjack.Compiler.Backend.WordToStack.Proofs.CodeLabels
import Flapjack.Compiler.Backend.StackProps.ForbiddenOperations

namespace Flapjack.Test.WordToStackCopyRetCarriersParity
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.StackProps
example : copyRetNative false false (9,0,true) [1,2] (.skip : HolProg 64) = .skip := rfl
example : copyRetNative false false (1,0,false) [1,2] (.skip : HolProg 64) =
    .seq (copyRetAuxNative 1 0 2) (seqStackFreeNative 2 .skip) := rfl
example : copyRetNative false true (1,7,[true,false]) [1,2] (.skip : HolProg 64) =
    .seq (copyRetAuxNative 1 10 2) (seqStackFreeNative 2 .skip) := rfl
example : copyRetNative true true (0,7,[true,false]) [true,false] (.skip : HolProg 1) =
    .seq (copyRetAuxNative 0 12 3) (seqStackFreeNative 3 .skip) := rfl
example : noInstall (copyRetNative true false (0,7,true) [true,false]
    (.install 0 1 2 3 4 : HolProg 1)) = false := by
  decide
example {width : Nat} [NeZero width] {β γ : Type}
    (perf b : Bool) (k f : Nat) (tail : γ) (vs : List β) (kont : HolProg width) (owner : Nat) :
    getCodeLabels (copyRetNative perf b (k,f,tail) vs kont) = getCodeLabels kont ∧
    stackGetHandlerLabels owner (copyRetNative perf b (k,f,tail) vs kont) =
      stackGetHandlerLabels owner kont := getCodeHandlerLabelsCopyRet perf b (k,f,tail) vs kont owner

end Flapjack.Test.WordToStackCopyRetCarriersParity
