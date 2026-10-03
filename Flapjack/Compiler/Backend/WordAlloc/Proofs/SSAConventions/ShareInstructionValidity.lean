import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAConventions.InstructionValidity
import Flapjack.Compiler.Backend.WordAlloc.SSACcTrans

namespace Flapjack.WordAlloc
open Flapjack Flapjack.Compiler.Backend.WordAlloc Flapjack.Compiler.Encoders.Asm

/-- Original complete ShareInst validity case. Source address extraction
supplies the offset, which the literal SSA expression translation preserves. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "ssa_cc_trans_full_inst_ok_less" (words_as_type_indexed_bitvec)]
theorem ssaCcTrans_fullInstShareInst {width : Nat} [NeZero width]
    (config : AsmConfigExact width) (operator : HolMemop) (name : Nat)
    (expression : WordLangExpHOL (BitVec width))
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : everyVarHOL (fun x => decide (x < next)) (.shareInst operator name expression) = true ∧
      isAllocVar next ∧ ssaMapOK next ssa ∧
        fullInstOkLessExact config (.shareInst operator name expression) = true) :
    fullInstOkLessExact config (ssaCcTrans (.shareInst operator name expression) ssa next tables).1 = true := by
  have valid := h.2.2.2
  simp only [fullInstOkLessExact, fullInstOkLessWith] at valid
  generalize address : expToAddrHOL expression = result at valid
  cases result with
  | none => simp at valid
  | some value =>
      cases value with
      | addr base offset =>
          rcases (expToAddr_shareInst expression base offset).mp address with ⟨rfl, rfl⟩ | rfl
          · cases operator <;>
              simpa [ssaCcTrans, nextVarRename, ssaCcTransExp, expToAddrHOL,
                fullInstOkLessExact, fullInstOkLessWith] using valid
          · cases operator <;>
              simpa [ssaCcTrans, nextVarRename, ssaCcTransExp, expToAddrHOL,
                fullInstOkLessExact, fullInstOkLessWith] using valid

end Flapjack.WordAlloc
