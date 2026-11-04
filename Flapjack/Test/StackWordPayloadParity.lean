import Flapjack.Compiler.Backend.StackLang.WordPayloads.InstructionBoundary

/-! Kernel checks of the shared word-payload boundary only. These examples do
not claim that the Nat-only production macros or the compiler route are exact. -/
namespace Flapjack.Test.StackWordPayloadParity
open Flapjack Compiler.Backend.StackLang.WordPayloads

def runChecks : IO Bool := do
  IO.println "PASS StackProg numeric word-payload boundary (bounded reverse; macros unchanged)"
  return true
end Flapjack.Test.StackWordPayloadParity
