import Flapjack.Pancake.Proofs.PanToWord.PanToCrepCompileValidity
import Flapjack.Pancake.Proofs.PanToWord.EveryInstOkLess.PanStructs

namespace Flapjack.PanToCrepTableValidity
open Pancake.PanLang

/-- Internal function-projection membership factoring; no separate HOL declaration.
Non-function declarations are discarded without changing the function order. -/
private theorem functions_valid {width : Nat} [NeZero width]
    (declarations : List (DeclHOL width))
    (guard : ∀ d ∈ declarations, goodPanopsHOL d = true) :
    ∀ entry ∈ functionsHOL declarations,
      ∀ e ∈ expsOfHOL entry.2.2.1, everyExpHOL panopArityTwoHOL e = true := by
  induction declarations with
  | nil => simp [functionsHOL]
  | cons d ds ih =>
    have rest := ih (fun d hd => guard d (List.mem_cons_of_mem _ hd))
    cases d with
    | function fi =>
      intro entry member
      simp only [functionsHOL, List.mem_cons] at member
      rcases member with rfl | member
      · exact (PanToWordEveryInstOkLessPanStructs.everyExpListHOL_iff _ _).mp
          (guard (.function fi) List.mem_cons_self)
      · exact rest entry member
    | decl sh name exp => simpa only [functionsHOL] using rest
    | exnDecl name shape => simpa only [functionsHOL] using rest
    | name name shape => simpa only [functionsHOL] using rest

/-- Full original declaration-list guard and actual compile_to_crep table result.
The source proof (1116–1134) projects each function, then applies the complete
body-compiler theorem at its actual generated context. Function names, parameter
lists and native bodies remain unrestricted; no byte-range, distinctness, output
validity or target-run premise is added. The canonical maps are internal to the
reviewed compiler and do not occur in this theorem signature. -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml"
  "every_inst_ok_less_pan_to_crep_compile_to_crep" (words_as_type_indexed_bitvec)]
theorem everyInstOkLess_panToCrepCompileToCrep {width : Nat} [NeZero width]
    (pan_code : List (DeclHOL width))
    (guard : ∀ d ∈ pan_code, goodPanopsHOL d = true) :
    ∀ (entry : CrepInlineMapHOLName × List Nat × CrepProgHOL width),
      entry ∈ compileToCrepExactHOLW pan_code → crepBinaryProgNative entry.2.2 := by
  intro entry member
  simp only [compileToCrepExactHOLW, List.mem_map] at member
  obtain ⟨source, source_member, rfl⟩ := member
  unfold compFuncExactHOLW
  exact PanToCrepCompileValidity.everyInstOkLess_panToCrepCompile _ _
    (functions_valid pan_code guard source source_member)

end Flapjack.PanToCrepTableValidity
