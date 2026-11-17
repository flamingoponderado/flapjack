module

public import Flapjack.Compiler.Backend.WordToStack.NativePrograms
public import Flapjack.Misc.Sptree.Mapi

@[expose] public section

/-! Stack-frame bounds used by the source backend's space-safety predicate. -/
namespace Flapjack.Compiler.Backend.BackendProof
open Flapjack Flapjack.Compiler.Encoders.Asm
  Flapjack.Compiler.Backend.WordToStack.Native

/-- Compute the exact stack-frame size for every entry in the word program. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "compute_stack_frame_sizes_def"
  (words_as_type_indexed_bitvec)]
def computeStackFrameSizes {asmWidth : Nat} {progWidth : Nat} [NeZero asmWidth] [NeZero progWidth]
    (c : AsmConfigExact asmWidth)
    (wordProg : List (Nat × Nat × WordLangProgHOL (BitVec progWidth))) : Spt Nat :=
  let regCount := c.regCount - c.avoidRegs.length - 5
  sptMapi (fun _ (argCount, prog) =>
    let stackArgCount := argCount - regCount
    let stackVarCount := max (maxVarHOL prog / 2 + 1 - regCount) stackArgCount
    if stackVarCount = 0 then 0 else stackVarCount + 1) (sptFromAList wordProg)

/-- The bound is the frame size returned by the original per-program compiler. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "compute_stack_frame_sizes_thm"
  (words_as_type_indexed_bitvec)]
theorem computeStackFrameSizesThm {width : Nat} [NeZero width] (c : AsmConfigExact width)
    (wordProg : List (Nat × Nat × WordLangProgHOL (BitVec width))) :
    computeStackFrameSizes c wordProg =
      let k := c.regCount - c.avoidRegs.length - 5
      sptMapi (fun _ (argCount, prog) =>
        (compileProgNative c false prog argCount k (.nil, 0)).2.1) (sptFromAList wordProg) := by
  simp [computeStackFrameSizes, compileProgNative]

end Flapjack.Compiler.Backend.BackendProof
