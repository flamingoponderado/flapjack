import Flapjack.Compiler.Backend.WordBignum.GeneratedMini
import Flapjack.Compiler.Backend.WordBignum.Compile

/-! Generate word stubs from the captured mini-program and executable
mini-compiler. This is not yet the original shallow-to-deep generator. -/
namespace Flapjack.Compiler.Backend.WordBignum

/-- Compile the captured mini-program and append the original return to each
generated entry. -/
def generateStubs (width : Nat) [NeZero width] (location : Nat) :
    Option (List (Nat × Nat × WordLangProgHOL (BitVec width))) := do
  let (body, _, _, (_, installed)) ←
    compileBounded 0 location 2 1 (location + 1, []) (mcIopCode width)
  pure ((location, 1, .seq body (.return 0 [0])) ::
    installed.map fun (_, index, code) => (index, 1, .seq code (.return 0 [0])))

end Flapjack.Compiler.Backend.WordBignum
