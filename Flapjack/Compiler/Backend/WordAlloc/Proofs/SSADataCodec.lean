import Flapjack.Compiler.Backend.WordAlloc.SSACcTrans
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAInstructionCodec

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Flapjack assembly partition, not a HOL declaration: native SSA data leaves
without recursive subprograms. Loop-control leaves are covered separately. -/
def ssaDataLeaf {α : Type} : WordLangProgHOL α → Prop
  | .mustTerminate _ | .call _ _ _ _ | .seq _ _ | .ite _ _ _ _ _
  | .loop _ _ _ | .break _ | .continue _ => False
  | _ => True

/-- Flapjack carrier-boundary infrastructure, with no independent HOL original.
Every native nonrecursive data case preserves decoder availability, including
complete generated move programs for allocation, installation and FFI. The
input premise restricts unsupported instructions at the existing production
boundary; output success is proved, not assumed. -/
theorem ssaCcTrans_data_decoderClosure {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width)) (ssa : Spt Nat) (next : Nat)
    (contexts : List (Spt Nat × Spt Unit × Spt Unit))
    (leaf : ssaDataLeaf program)
    (accepted : (wordLangProgFromHOL program).isSome = true) :
    (wordLangProgFromHOL (ssaCcTrans program ssa next contexts).1).isSome = true := by
  cases program <;> simp only [ssaDataLeaf] at leaf
  case inst instruction =>
    simpa only [ssaCcTrans] using ssaCcTransInst_decoderClosure instruction ssa next
      (by simpa [wordLangProgFromHOL] using accepted)
  all_goals simp [ssaCcTrans, nextVarRename, listNextVarRenameMove, wordLangProgFromHOL]
  all_goals split <;> simp [wordLangProgFromHOL]

end Flapjack.Compiler.Backend.WordAlloc
