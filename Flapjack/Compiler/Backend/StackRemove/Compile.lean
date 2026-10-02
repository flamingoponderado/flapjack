import Flapjack.Compiler.Backend.StackRemove.InitStubs
import Flapjack.Compiler.Backend.StackRemove.ProgComp

namespace Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackLang

/-- Complete original initializer prefix followed by the pointwise source
section compiler. Production routing and whole-pass semantic correctness are
separate obligations; no successful compilation premise is assumed here. -/
@[hol "cakeml/compiler/backend/stack_removeScript.sml" "compile_def"
  (words_as_type_indexed_bitvec)]
def compileHOL {width : Nat} [NeZero width] (jump : Bool)
    (bounds : BitVec width × BitVec width) (generateGc : Bool)
    (maximumHeap pointer start : Nat) (program : List (Nat × HolProg width)) :
    List (Nat × HolProg width) :=
  initStubs generateGc maximumHeap pointer start ++ program.map (progComp jump bounds pointer)

end Flapjack.Compiler.Backend.StackRemove
