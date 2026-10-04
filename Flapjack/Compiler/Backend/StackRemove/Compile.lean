import Flapjack.Compiler.Backend.StackRemove.InitStubs
import Flapjack.Compiler.Backend.StackRemove.ProgComp

namespace Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackLang

/-- Complete original initializer prefix followed by the pointwise source
section compiler. Production routing and whole-pass semantic correctness are
separate obligations; no successful compilation premise is assumed here. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def compileHOL {width : Nat} [NeZero width] (jump : Bool)
    (bounds : BitVec width × BitVec width) (generateGc : Bool)
    (maximumHeap pointer start : Nat) (program : List (Nat × HolProg width)) :
    List (Nat × HolProg width) :=
  initStubs generateGc maximumHeap pointer start ++ program.map (progComp jump bounds pointer)

end Flapjack.Compiler.Backend.StackRemove
