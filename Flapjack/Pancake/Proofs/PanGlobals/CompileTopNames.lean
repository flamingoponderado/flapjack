import Flapjack.Pancake.Proofs.PanGlobals
import Flapjack.Pancake.Proofs.PanGlobals.CompileDecsStructural
import Flapjack.Pancake.Proofs.PanGlobals.DeclListLemmas
import Flapjack.Pancake.Semantics.PanProps

/-!
The original pan_globals `ALL_DISTINCT_compile_top`
(`pan_globalsProofScript.sml:3278-3295`) over the reviewed exact `compile_top`.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang

/-- Exact HOL `ALL_DISTINCT_compile_top` (`pan_globalsProofScript.sml:3278-3295`). -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "ALL_DISTINCT_compile_top"
  (words_as_type_indexed_bitvec)]
theorem allDistinctCompileTopHOL {width : Nat} [NeZero width] :
    ∀ (start : MlS) (code : List (DeclHOL width)),
      ((functionsHOL code).map Prod.fst).Nodup →
      ((functionsHOL (compileTopExactHOL code start)).map Prod.fst).Nodup := by
  intro start code hnd
  unfold compileTopExactHOL
  rw [compileTopFunctionLookup_eq_lookup]
  cases hl : (functionsHOL code).lookup start with
  | none => simp [functionsHOL]
  | some x =>
    obtain ⟨args, body, rshape⟩ := x
    simp only
    rw [functionsHOL_append,
      PanGlobalsCompileDecsStructural.compile_decs_exns_are_exnsHOL _ _ _ _ _ _ rfl,
      PanGlobalsDeclListExact.functions_FILTER_exn_declHOL]
    simp only [functionsHOL, List.nil_append, List.map_cons, List.nodup_cons]
    rw [PanGlobalsCompileDecsStructural.compile_decs_preserve_functionsHOL _ _ _ _ _ _ rfl]
    refine ⟨?_, ?_⟩
    · rw [functionsFpermDecsHOL, List.map_map,
        PanGlobalsDeclListExact.resort_decls_preserve_functionsHOL]
      intro hm
      obtain ⟨e, he, hfn⟩ := List.mem_map.mp hm
      have hn : e.1 ∈ (functionsHOL code).map Prod.fst := List.mem_map.mpr ⟨e, he, rfl⟩
      simp only [Function.comp_def] at hfn
      generalize e.1 = n at hn hfn
      have hfresh := PanGlobalsDeclListExact.new_main_name_correctHOL code
      unfold fpermName at hfn
      by_cases h1 : start = n
      · rw [if_pos h1] at hfn
        exact hfresh (hfn ▸ (h1 ▸ hn))
      · rw [if_neg h1] at hfn
        by_cases h2 : newMainNameHOL code = n
        · exact hfresh (h2 ▸ hn)
        · rw [if_neg h2] at hfn
          exact h1 hfn.symm
    · exact PanGlobalsDeclListExact.ALL_DISTINCT_fperm_decsHOL _ _ _
        (by rw [PanGlobalsDeclListExact.resort_decls_preserve_functionsHOL]; exact hnd)

end Flapjack
