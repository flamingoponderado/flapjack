import Flapjack.Compiler.Inference.InferT.Display

/-! Type rendering examples captured from the pinned HOL `infer_t` script. -/
namespace Flapjack.Test.CakeTypeDisplayParity
open Flapjack.Basis.Pure.MlString Flapjack.NamespaceHOL
open Flapjack.Compiler.Inference.Infer Flapjack.Compiler.Inference.InferTDisplay

private def names : TypeNames Unit := alistToNs []

#guard toStringOfBytes (inferTypeToString names (.app [.varDb 0, .varDb 0] 4)) == "'a -> 'a"
#guard toStringOfBytes (inferTypeToString names (.app [.app [] 5, .app [] 1] 9)) == "int * bool"
#guard toStringOfBytes (inferTypeToString names (.app [] 123)) == "123"

end Flapjack.Test.CakeTypeDisplayParity
