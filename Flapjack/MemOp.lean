/-!
# The shared `asm$memop` carrier

`Flapjack.WordMemOp` is the Lean mirror of HOL `asm$memop`
(`cakeml/compiler/encoders/asm/asmScript.sml:125-128`), tagged through the
alias `Flapjack.Compiler.Encoders.Asm.HolMemop`.  HOL's crepLang, loopLang and
wordLang all reuse this one datatype (their theories have `asm` as an
ancestor), so it lives in this dependency-free module and the Crep, Loop and
Word carriers all use it directly (no separate Crep/Loop `memop` datatype).
-/

namespace Flapjack

inductive WordMemOp where
  | load
  | load8
  | load16
  | load32
  | store
  | store8
  | store16
  | store32
  deriving DecidableEq, Repr

end Flapjack
