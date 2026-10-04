import Flapjack.Pancake.WordLang

namespace Flapjack.WordAlloc

/-- Literal preference collection over the native program. Move priority and
pair order are retained and an arbitrary initial accumulator is preserved.
The exceptional handler precedes the returning handler in the output; calls
without a return contribute no preferences, even with a handler. This native
collector does not replace the executed allocator. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def getPrefs {width : Nat} [NeZero width] :
    WordLangProgHOL (BitVec width) → List (Nat × Nat × Nat) → List (Nat × Nat × Nat)
  | .move priority moves, accumulator =>
      moves.map (fun (x, y) => (priority, x, y)) ++ accumulator
  | .mustTerminate body, accumulator => getPrefs body accumulator
  | .seq first second, accumulator => getPrefs first (getPrefs second accumulator)
  | .ite _ _ _ first second, accumulator => getPrefs first (getPrefs second accumulator)
  | .call (some (_, _, returned, _, _)) _ _ handler, accumulator =>
      match handler with
      | none => getPrefs returned accumulator
      | some (_, body, _, _) => getPrefs body (getPrefs returned accumulator)
  | .loop _ body _, accumulator => getPrefs body accumulator
  | _, accumulator => accumulator

end Flapjack.WordAlloc
