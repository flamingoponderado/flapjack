import Flapjack.Compiler.Backend.WordAlloc.HeuInst
import Flapjack.Compiler.Backend.WordAlloc.HeuMax
import Flapjack.Compiler.Backend.WordAlloc.HeuCall

namespace Flapjack.WordAlloc

/-- Literal program heuristic collection on the native word program and Spt
carriers. Both If branches start from the same incoming state. A returning
Call with no exception handler discards the return body's collected calls,
exactly as in the source. Tail calls ignore their handler. Catchall programs
retain the complete input state. This definition is an analysis prerequisite;
the executed allocator migration remains separate work. -/
@[hol "cakeml/compiler/backend/word_allocScript.sml" "get_heu_def"
  (words_as_type_indexed_bitvec)]
def getHeu {width : Nat} [NeZero width] (functionName : Nat) :
    WordLangProgHOL (BitVec width) → Spt HeuData × NumSet → Spt HeuData × NumSet
  | .move _ moves, (tracked, calls) =>
    ((moves.map Prod.fst).foldr add1LhsReg
      ((moves.map Prod.snd).foldr add1RhsReg tracked), calls)
  | .inst instruction, (tracked, calls) => (getHeuInst instruction tracked, calls)
  | .get name _, (tracked, calls) => (add1LhsMem name tracked, calls)
  | .set _ (.var name), (tracked, calls) => (add1RhsMem name tracked, calls)
  | .set _ _, state => state
  | .opCurrHeap _ destination source, (tracked, calls) =>
    (add1LhsReg destination (add1RhsReg source tracked), calls)
  | .locValue name _, (tracked, calls) => (add1LhsReg name tracked, calls)
  | .seq first second, state => getHeu functionName second (getHeu functionName first state)
  | .mustTerminate body, state => getHeu functionName body state
  | .ite _ condition right thenBranch elseBranch, state =>
    let (thenTracked, thenCalls) := getHeu functionName thenBranch state
    let (elseTracked, elseCalls) := getHeu functionName elseBranch state
    let tracked := heuMaxAll thenTracked elseTracked
    let calls := heuMergeCall thenCalls elseCalls
    match right with
    | .reg name => (add1RhsReg condition (add1RhsReg name tracked), calls)
    | .imm _ => (add1RhsReg condition tracked, calls)
  | .call none target _ _, (tracked, calls) =>
    match target with
    | none => (tracked, calls)
    | some name =>
      if name = functionName then (tracked, addCall tracked calls) else (tracked, calls)
  | .call (some (_, _, body, _, _)) target _ handler, (tracked, calls) =>
    let calls := match target with
      | none => calls
      | some name => if name = functionName then addCall tracked calls else calls
    let (bodyTracked, bodyCalls) := getHeu functionName body (tracked, calls)
    match handler with
    | none => (bodyTracked, calls)
    | some (_, exceptionBody, _, _) =>
      let (exceptionTracked, exceptionCalls) :=
        getHeu functionName exceptionBody (tracked, calls)
      (heuMaxAll bodyTracked exceptionTracked, heuMergeCall bodyCalls exceptionCalls)
  | .shareInst .load name _, (tracked, calls)
  | .shareInst .load8 name _, (tracked, calls)
  | .shareInst .load16 name _, (tracked, calls)
  | .shareInst .load32 name _, (tracked, calls) => (add1LhsMem name tracked, calls)
  | .shareInst .store name _, (tracked, calls)
  | .shareInst .store8 name _, (tracked, calls)
  | .shareInst .store16 name _, (tracked, calls)
  | .shareInst .store32 name _, (tracked, calls) => (add1RhsMem name tracked, calls)
  | .loop _ body _, state => getHeu functionName body state
  | _, state => state
termination_by program _ => sizeOf program
decreasing_by all_goals decreasing_trivial

end Flapjack.WordAlloc
