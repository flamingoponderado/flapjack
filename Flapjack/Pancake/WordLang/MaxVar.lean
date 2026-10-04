import Flapjack.Pancake.WordLang.MaxVarInst
import Flapjack.Pancake.WordLang.MaxVarExp
import Flapjack.Pancake.WordLang.CutsetsMax

namespace Flapjack

/-- Complete source program maximum. A Call handler contributes only under
SOME return, as in HOL. All source operands, cut sets and recursive bodies
are retained; there is no well-formedness or successful compilation premise. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def maxVarHOL {width : Nat} [NeZero width] (program : WordLangProgHOL (BitVec width)) : Nat :=
  match program with
  | .skip => 0
  | .move _ moves => maxList (moves.map Prod.fst ++ moves.map Prod.snd)
  | .inst instruction => maxVarInstHOL instruction
  | .assign register expression => max register (maxVarExpHOL expression)
  | .get register _ => register
  | .store expression register => max register (maxVarExpHOL expression)
  | .call returns _ arguments handler =>
      let n := maxList arguments
      match returns with
      | none => n
      | some (values, cutsets, body, _, _) =>
          let cutsetMax := max n (cutsetsMaxHOL cutsets)
          let retMax := max3HOL (maxList values) cutsetMax (maxVarHOL body)
          match handler with
          | none => retMax
          | some (value, body, _, _) => max3HOL value retMax (maxVarHOL body)
  | .seq first second => max (maxVarHOL first) (maxVarHOL second)
  | .mustTerminate body => maxVarHOL body
  | .ite _ left right first second =>
      let r := match right with
        | .reg r => max r left
        | .imm _ => left
      max3HOL r (maxVarHOL first) (maxVarHOL second)
  | .alloc register cutsets => max register (cutsetsMaxHOL cutsets)
  | .storeConsts a b c d _ => maxList [a, b, c, d]
  | .install a b c d cutsets => maxList [a, b, c, d, cutsetsMaxHOL cutsets]
  | .codeBufferWrite a b => max a b
  | .dataBufferWrite a b => max a b
  | .ffi _ a b c d cutsets => maxList [a, b, c, d, cutsetsMaxHOL cutsets]
  | .raise register => register
  | .opCurrHeap _ a b => max a b
  | .return register values => maxList (register :: values)
  | .tick => 0
  | .locValue register _ => register
  | .set _ expression => maxVarExpHOL expression
  | .shareInst _ register expression => max register (maxVarExpHOL expression)
  | .loop liveIn body liveOut =>
      max3HOL (maxList ((sptToAList liveIn).map Prod.fst)) (maxVarHOL body)
        (maxList ((sptToAList liveOut).map Prod.fst))
  | _ => 0
termination_by sizeOf program

end Flapjack
