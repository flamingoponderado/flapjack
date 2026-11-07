import Flapjack.HolRef
import Flapjack.Pancake.PanToCrep.CompileProg

/-!
Exact HOL `compile_prog_distinct_params`.
-/

namespace Flapjack


/-- Exact port of HOL `compile_prog_distinct_params`
    (`pan_to_crepProofScript.sml:4684-4691`): every parameter list in the
    `compile_prog` output is `Nodup`.  Follows from the `compile_to_crep` half
    (`compileToCrepExactHOLW_params_nodup`) and definitional parameter
    preservation by the reviewed exact inline pass. HOL EVERY is represented
    by List.all with the decidable Nodup predicate; no hypothesis is added.
    The word qualifier records only the standard positive-width translation. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "compile_prog_distinct_params"
  (words_as_type_indexed_bitvec)]
theorem compileProgDeclsHOLW_params_nodup {width : Nat} [NeZero width]
    (prog : List (Pancake.PanLang.DeclHOL width)) :
    (compileProgDeclsHOLW prog).all (fun triple => triple.2.1.Nodup) = true := by
  unfold compileProgDeclsHOLW
  simp only [CrepInlineCanonical.compileInlTopHOLExact,
    CrepInlineCanonical.compileInlProgHOLExactWithSupport, List.all_map]
  exact compileToCrepExactHOLW_params_nodup prog


end Flapjack
