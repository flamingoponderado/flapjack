import Flapjack.HolRef
import Flapjack.Pancake.PanToCrep.CompileProg

/-!
Exact HOL `compile_prog_distinct_params` and the production-carrier analogue.
-/

namespace Flapjack

/-- FLAPJACK-SPECIFIC analogue of HOL `compile_prog_distinct_params`
    (`pan_to_crepProofScript.sml:4684-4691`): every function compiled from a
    source declaration has distinct flattened parameter slots. HOL quantifies
    over its positive-width word-indexed `prog` and concludes about exact
    `compile_prog` triples whose names are `mlstring` and bodies are
    `CrepProgHOL width`. This theorem instead quantifies over production
    `Decl (BitVec width)` (String names, production Shape/Prog) and concludes
    about `compileProgTopHOL` (production String/CrepProg); it also admits
    `BitVec 0`. No existing qualifier authorizes those carrier and width
    differences. Keep this useful analogue untagged; the faithful positive-width theorem
    `compileProgDeclsHOLW_params_nodup` below uses the reviewed exact compiler. -/
theorem compileProgTopHOL_params_nodup
    (declarations : List (Decl (BitVec width))) :
    ∀ function ∈ compileProgTopHOL declarations,
      function.2.1.Nodup := by
  intro function hfunction
  simp [compileProgTopHOL, compileInlTopHOL,
    compileToCrepHOL, panToCrepVars] at hfunction
  rcases hfunction with ⟨name, params, body, _hsource, heq⟩
  cases heq
  exact List.nodup_range

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
