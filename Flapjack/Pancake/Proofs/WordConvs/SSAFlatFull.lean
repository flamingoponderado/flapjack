import Flapjack.Pancake.Proofs.WordConvs.SSAFlatProgram
import Flapjack.Compiler.Backend.WordAlloc.FullSSA

namespace Flapjack.WordAlloc
open Flapjack Flapjack.Compiler.Backend.WordAlloc

/-- Original full SSA flat-expression preservation, with the sole original
source premise and literal executed fullSSA producer. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "full_ssa_cc_trans_flat_exp_conventions" (words_as_type_indexed_bitvec)]
theorem fullSsaCcTrans_flatExpConventions {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width)) (count : Nat)
    (source : flatExpConventions program = true) :
    flatExpConventions (fullSsaCcTrans count program) = true := by
  generalize produced : setupSSA (outputWidth := width) count (limitVar program) program = result
  rcases result with ⟨move, ssa, next⟩
  have moveFlat : flatExpConventions move = true := by
    unfold setupSSA at produced
    generalize listNextVarRename (evenList count) .ln (limitVar program) = renamed at produced
    rcases renamed with ⟨names, tree, counter⟩
    cases produced
    rfl
  have bodyFlat := ssaCcTrans_flatExpConventions program ssa next [] source
  generalize bodyEq : ssaCcTrans program ssa next [] = bodyResult
  rcases bodyResult with ⟨body, finalMap, finalNext⟩
  rw [bodyEq] at bodyFlat
  simp only [fullSsaCcTrans, produced, bodyEq, flatExpConventions, moveFlat, bodyFlat]
  rfl

end Flapjack.WordAlloc
