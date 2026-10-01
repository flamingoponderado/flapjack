import Flapjack.Compiler.Backend.WordAlloc.StackOnly
import Flapjack.Compiler.Backend.WordAlloc.MergeStackSets
import Flapjack.Compiler.Backend.WordAlloc.ClashTreeProg

namespace Flapjack.WordAlloc

/-- Literal recursive stack-only analysis. Sequential children run right to
left; branch and returning-call handlers start from the same initial trees.
A call without a return preserves those trees, irrespective of its handler.
The fallback removes temporary keys only when the actual clash tree is Delta. -/
@[hol "cakeml/compiler/backend/word_allocScript.sml" "get_stack_only_aux_def"
  (words_as_type_indexed_bitvec)]
def getStackOnlyAux {width : Nat} [NeZero width]
    (trees : Spt Unit × Spt Unit) : WordLangProgHOL (BitVec width) → Spt Unit × Spt Unit
  | .move _ moves => moves.foldr mergeStackOnly trees
  | .seq first second => getStackOnlyAux (getStackOnlyAux trees second) first
  | .ite _ condition right first second =>
      let leftTrees := getStackOnlyAux trees first
      let rightTrees := getStackOnlyAux trees second
      let joined := mergeStackSets trees leftTrees rightTrees
      match right with
      | .reg register => removeTempStack [condition, register] joined
      | .imm _ => removeTempStack [condition] joined
  | .mustTerminate body => getStackOnlyAux trees body
  | .call returns _ _ handler =>
      match returns with
      | none => trees
      | some (_, _, returnHandler, _, _) =>
          let returned := getStackOnlyAux trees returnHandler
          match handler with
          | none => returned
          | some (_, body, _, _) =>
              mergeStackSets trees returned (getStackOnlyAux trees body)
  | .loop _ body _ => getStackOnlyAux trees body
  | program =>
      match getClashTree program [] with
      | .delta writes reads => removeTempStack (writes ++ reads) trees
      | _ => trees

/-- Original entry point: discard the temporary component after analysing
from the two empty native trees. This does not replace the executed allocator. -/
@[hol "cakeml/compiler/backend/word_allocScript.sml" "get_stack_only_def"
  (words_as_type_indexed_bitvec)]
def getStackOnly {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width)) : Spt Unit :=
  (getStackOnlyAux (.ln, .ln) program).2

end Flapjack.WordAlloc
