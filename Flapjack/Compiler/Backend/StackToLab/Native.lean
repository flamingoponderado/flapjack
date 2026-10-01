import Flapjack.Compiler.Backend.StackToLab
import Flapjack.Compiler.Backend.StackLang.Prog
import Flapjack.Compiler.Backend.LabSem.State

/-!
# Native Stack-to-Lab lowering

Counterpart of `stack_to_labScript.sml:19-136`. These definitions use the
single-width native Stack AST, native assembler payloads, faithful `MlString`,
and byte-word caches. The only carrier translation is positive-width `BitVec`.

The recursive result preserves HOL's actual `misc$app_list` tree: its locally
overloaded `++` retains listScript's left-associative fixity. The generic
callback-based `flattenApp` remains separate infrastructure and builds a
different, right-associated tree even where flattening yields equal lines.
`nextLab` is instantiated at the native carriers; its complete traversal and
label-seed clauses match `stack_allocScript.sml:649-662`.

This native definition group is a proof-side prerequisite. The executed
compiler still uses its existing lowering route; production replacement and
full encoding/initialization correctness remain open fleet work.
-/

namespace Flapjack.Compiler.Backend.StackToLab
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Encoders.Asm

/-- Optional list lookup with the original explicit out-of-range zero. -/
@[hol "cakeml/compiler/backend/stack_to_labScript.sml" "find_lab_def"]
def findLabHOL (index : Nat) (labels : List Nat) : Nat :=
  (labels[index]?).getD 0

/-- The eight native comparison-negation equations. -/
@[hol "cakeml/compiler/backend/stack_to_labScript.sml" "negate_def"]
def negateHOL : HolCmp → HolCmp
  | .less => .notLess
  | .equal => .notEqual
  | .lower => .notLower
  | .test => .notTest
  | .notLess => .less
  | .notEqual => .equal
  | .notLower => .lower
  | .notTest => .test

/-- The two native direct/indirect jump equations, including empty caches. -/
@[hol "cakeml/compiler/backend/stack_to_labScript.sml" "compile_jump_def"
  (words_as_type_indexed_bitvec)]
def compileJumpHOL {width : Nat} [NeZero width] (target : Sum Nat Nat) :
    Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) Flapjack.Basis.Pure.MlString.MlString)
      (BitVec width) :=
  match target with
  | .inl sectionId => .labAsm (.jump (.lab sectionId 0)) 0 [] 0
  | .inr register => .asm (.asmi (.jumpReg register)) [] 0

/-- The complete native recursive flatten quotation, including its fallback case. -/
@[hol "cakeml/compiler/backend/stack_to_labScript.sml" "flatten_def"
  (words_as_type_indexed_bitvec)]
def flattenHOL {width : Nat} [NeZero width]
    (tail : Bool) (program : HolProg width) (sectionId next : Nat)
    (conts breaks : List Nat) : AppList (LabLineHOL width) × Bool × Nat :=
    match program with
    | .tick => (.list [.asm (.asmi (.inst .skip)) [] 0], false, next)
    | .inst instruction => (.list [.asm (.asmi (.inst instruction)) [] 0], false, next)
    | .halt _ => (.list [.labAsm .halt 0 [] 0], true, next)
    | .seq first second =>
        let (xs, nr1, next) := flattenHOL false first sectionId next conts breaks
        let (ys, nr2, next) := flattenHOL false second sectionId next conts breaks
        ((if tail then .append (.append xs (.list [.label sectionId 1 0])) ys else .append xs ys),
          nr1 || nr2, next)
    | .ite condition register right thenBranch elseBranch =>
        let (xs, nr1, next) := flattenHOL false thenBranch sectionId next conts breaks
        let (ys, nr2, next) := flattenHOL false elseBranch sectionId next conts breaks
        if stackIsSkip thenBranch && stackIsSkip elseBranch then
          (.list [], false, next)
        else if stackIsSkip thenBranch then
          (.append (.append (.list [.labAsm (.jumpCmp condition register right (.lab sectionId next)) 0 [] 0])
            ys) (.list [.label sectionId next 0]), false, next + 1)
        else if stackIsSkip elseBranch then
          (.append (.append (.list [.labAsm (.jumpCmp (negateHOL condition) register right (.lab sectionId next)) 0 [] 0])
            xs) (.list [.label sectionId next 0]), false, next + 1)
        else if nr1 then
          (.append (.append (.append (.list [.labAsm (.jumpCmp (negateHOL condition) register right (.lab sectionId next)) 0 [] 0])
            xs) (.list [.label sectionId next 0])) ys, nr2, next + 1)
        else if nr2 then
          (.append (.append (.append (.list [.labAsm (.jumpCmp condition register right (.lab sectionId next)) 0 [] 0])
            ys) (.list [.label sectionId next 0])) xs, nr1, next + 1)
        else
          (.append (.append (.append (.append
            (.list [.labAsm (.jumpCmp condition register right (.lab sectionId next)) 0 [] 0]) ys)
            (.list [.labAsm (.jump (.lab sectionId (next + 1))) 0 [] 0,
                .label sectionId next 0])) xs) (.list [.label sectionId (next + 1) 0]), nr1 && nr2, next + 2)
    | .loop body =>
        let continueLabel := next
        let breakLabel := next + 1
        let (xs, _, nextAfterBody) := flattenHOL false body sectionId (next + 2)
          (continueLabel :: conts) (breakLabel :: breaks)
        (.append (.append (.list [.label sectionId continueLabel 0]) xs)
            (.list [.labAsm (.jump (.lab sectionId continueLabel)) 0 [] 0,
              .label sectionId breakLabel 0]), false, nextAfterBody)
    | .raise register => (.list [.asm (.asmi (.jumpReg register)) [] 0], true, next)
    | .ret register => (.list [.asm (.asmi (.jumpReg register)) [] 0], true, next)
    | .break index =>
        (.list [.labAsm (.jump (.lab sectionId (findLabHOL index breaks))) 0 [] 0], true, next)
    | .continue index =>
        (.list [.labAsm (.jump (.lab sectionId (findLabHOL index conts))) 0 [] 0], true, next)
    | .rawCall target => (.list [.labAsm (.jump (.lab target 1)) 0 [] 0], true, next)
    | .call none target _ => (.list [compileJumpHOL target], true, next)
    | .call (some (returnProgram, linkRegister, returnSection, returnLabel)) target handler =>
        let (xs, nr1, next) := flattenHOL false returnProgram sectionId next conts breaks
        let prelude := .append
          (.list [.labAsm (.locValue linkRegister (.lab returnSection returnLabel)) 0 [] 0,
            compileJumpHOL target, .label returnSection returnLabel 0]) xs
        match handler with
        | none => (prelude, nr1, next)
        | some (handlerProgram, handlerSection, handlerLabel) =>
            let (ys, nr2, next) := flattenHOL false handlerProgram sectionId next conts breaks
            (.append prelude
              (.append (.append (.list [.labAsm (.jump (.lab sectionId next)) 0 [] 0,
                  .label handlerSection handlerLabel 0]) ys)
                (.list [.label sectionId next 0])), nr1 && nr2, next + 1)
    | .jumpLower left right target =>
        (.list [.labAsm (.jumpCmp .lower left (.reg right) (.lab target 0)) 0 [] 0], false, next)
    | .ffi function _ _ _ _ returnAddress =>
        (.list [.labAsm (.locValue returnAddress (.lab sectionId next)) 0 [] 0,
          .labAsm (.callFFI function) 0 [] 0, .label sectionId next 0], false, next + 1)
    | .locValue register label entry =>
        (.list [.labAsm (.locValue register (.lab label entry)) 0 [] 0], false, next)
    | .install _ _ _ _ returnAddress =>
        (.list [.labAsm (.locValue returnAddress (.lab sectionId next)) 0 [] 0,
          .labAsm .install 0 [] 0, .label sectionId next 0], false, next + 1)
    | .shMemOp operator register address =>
        (.list [.asm (.shareMem operator register address) [] 0], false, next)
    | .codeBufferWrite left right => (.list [.asm (.cbw left right) [] 0], false, next)
    | _ => (.list [], false, next)
termination_by sizeOf program
decreasing_by all_goals decreasing_trivial

/-- The original root-constructor test; it does not inspect nested programs. -/
@[hol "cakeml/compiler/backend/stack_to_labScript.sml" "is_Seq_def"
  (words_as_type_indexed_bitvec)]
def isSeqHOL {width : Nat} [NeZero width] : HolProg width → Bool
  | .seq _ _ => true
  | _ => false

/-- The original pair-input section wrapper and final label choice. -/
@[hol "cakeml/compiler/backend/stack_to_labScript.sml" "prog_to_section_def"
  (words_as_type_indexed_bitvec)]
def progToSectionHOL {width : Nat} [NeZero width]
    (input : Nat × HolProg width) : Section (LabLineHOL width) :=
  let (sectionId, program) := input
  let (lines, _, next) := flattenHOL true program sectionId
    (Flapjack.Compiler.Backend.StackAlloc.nextLab program 2) [] []
  { sectionId := sectionId
    lines := appListAppend (.append lines
      (.list [.label sectionId (if isSeqHOL program then next else 1) 0])) }

end Flapjack.Compiler.Backend.StackToLab
