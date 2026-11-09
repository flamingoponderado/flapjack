import Flapjack.Compiler.Backend.WordBignum.GeneratedMini
import Flapjack.Compiler.Backend.WordBignum.Compile

/-! Generate word stubs from the captured mini-program and executable
mini-compiler. This is not yet the original shallow-to-deep generator. -/
namespace Flapjack.Compiler.Backend.WordBignum

/-- Append the original return to the entry and each installed function. -/
def assembleStubs {width : Nat} (location : Nat)
    (compiled : WordLangProgHOL (BitVec width) × Nat × Nat × CodeAcc width) :
    List (Nat × Nat × WordLangProgHOL (BitVec width)) :=
  let (body, _, _, (_, installed)) := compiled
  (location, 1, .seq body (.return 0 [0])) ::
    installed.map fun (_, index, code) => (index, 1, .seq code (.return 0 [0]))

/-- Compile the captured mini-program and assemble its generated entries. -/
def generateStubs (width : Nat) [NeZero width] (location : Nat) :
    Option (List (Nat × Nat × WordLangProgHOL (BitVec width))) :=
  some (assembleStubs location (compile location 2 1 (location + 1, []) (mcIopCode width)))

end Flapjack.Compiler.Backend.WordBignum
