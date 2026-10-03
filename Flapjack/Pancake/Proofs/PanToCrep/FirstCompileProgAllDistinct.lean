import Flapjack.HolRef
import Flapjack.Pancake.PanToCrep.CompileExact

/-!
The original pan_to_crep `first_compile_prog_all_distinct`
(`pan_to_crepProofScript.sml:4556-4568`) over the reviewed exact
`compile_prog` (`compileProgDeclsHOLW`).
-/

namespace Flapjack

open Flapjack.Pancake.PanLang

/-- `pan_to_crep$compile_prog` keeps the source function names in order: the
`compile_to_crep` and `compile_inl_top` stages only rewrite parameters and
bodies. Flapjack infrastructure; no HOL original. -/
theorem compileProgDeclsHOLW_names {width : Nat} [NeZero width] (prog : List (DeclHOL width)) :
    (compileProgDeclsHOLW prog).map Prod.fst = (functionsHOL prog).map Prod.fst := by
  simp [compileProgDeclsHOLW, compileToCrepExactHOLW,
    CrepInlineCanonical.compileInlTopHOLExact,
    CrepInlineCanonical.compileInlProgHOLExactWithSupport, List.map_map, Function.comp_def]

/-- Exact HOL `first_compile_prog_all_distinct` (`pan_to_crepProofScript.sml:4556-4568`)
over the reviewed exact `compile_prog`; the free `prog` is bound explicitly. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "first_compile_prog_all_distinct"
  (words_as_type_indexed_bitvec)]
theorem panToCrepFirstCompileProgAllDistinctExact {width : Nat} [NeZero width]
    (prog : List (DeclHOL width)) :
    ((functionsHOL prog).map Prod.fst).Nodup →
      ((compileProgDeclsHOLW prog).map Prod.fst).Nodup := by
  intro h
  rw [compileProgDeclsHOLW_names]
  exact h

end Flapjack
