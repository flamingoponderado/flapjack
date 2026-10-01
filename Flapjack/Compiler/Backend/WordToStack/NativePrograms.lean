import Flapjack.Compiler.Backend.WordToStack.NativeCompile
import Flapjack.Pancake.WordLang.MaxVar

namespace Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm

/-- Literal HOL frame sizing and native compilation of one program. The
argument and variable frame sizes use natural subtraction, including inputs
outside the calling convention's later correctness hypotheses. -/
@[hol "cakeml/compiler/backend/word_to_stackScript.sml" "compile_prog_def"
  (words_as_type_indexed_bitvec)]
def compileProgNative {width : Nat} [NeZero width] (conf : AsmConfigExact width)
    (perf : Bool) (program : WordLangProgHOL (BitVec width))
    (argumentCount registerCount : Nat) (bitmaps : AppList (BitVec width) × Nat) :
    HolProg width × Nat × (AppList (BitVec width) × Nat) :=
  let stackArgumentCount := argumentCount - registerCount
  let stackVariableCount := max ((maxVarHOL program / 2 + 1) - registerCount)
    stackArgumentCount
  let frame := if stackVariableCount = 0 then 0 else stackVariableCount + 1
  let (body, bitmaps) := compNative conf perf program bitmaps
    (registerCount, frame, stackVariableCount)
  (.seq (.stackAlloc (frame - stackArgumentCount)) body, frame, bitmaps)

/-- Literal left-to-right list traversal. HOL's identifier type is independent
of the word dimension; no equality or numeric restriction is imposed on it. -/
@[hol "cakeml/compiler/backend/word_to_stackScript.sml" "compile_word_to_stack_def"
  (words_as_type_indexed_bitvec)]
def compileWordToStackNative {width : Nat} [NeZero width] {β : Type}
    (conf : AsmConfigExact width) (perf : Bool) (registerCount : Nat)
    (programs : List (β × Nat × WordLangProgHOL (BitVec width)))
    (bitmaps : AppList (BitVec width) × Nat) :
    List (β × HolProg width) × List Nat × (AppList (BitVec width) × Nat) :=
  match programs with
  | [] => ([], [], bitmaps)
  | (identifier, argumentCount, program) :: programs =>
      let (body, frame, bitmaps) := compileProgNative conf perf program argumentCount
        registerCount bitmaps
      let (bodies, frames, bitmaps) := compileWordToStackNative conf perf registerCount
        programs bitmaps
      ((identifier, body) :: bodies, frame :: frames, bitmaps)

end Flapjack.Compiler.Backend.WordToStack.Native
