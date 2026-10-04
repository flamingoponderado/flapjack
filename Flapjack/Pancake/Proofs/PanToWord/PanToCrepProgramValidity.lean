import Flapjack.Pancake.Proofs.PanToWord.PanToCrepTableValidity
import Flapjack.Pancake.Proofs.PanToWord.PanToCrepInlineTableValidity

namespace Flapjack.PanToCrepProgramValidity
open Pancake.PanLang

/-- Full original `pan_to_wordProofScript.sml:1153–1159` result.
The original declaration-list good_panops guard supplies table validity, and
the accepted full inlining theorem supplies validity of the actual compile_prog
result. Names, parameters and all source declarations retain their native
carriers without additional restrictions. No successful target run, desired
output validity or extra compiler premise is assumed. This arity invariant is
a prerequisite of source-pass composition, not full compiler correctness. -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml"
  "every_inst_ok_less_pan_to_crep_compile_prog" (words_as_type_indexed_bitvec)]
theorem everyInstOkLess_panToCrepCompileProg {width : Nat} [NeZero width]
    (pan_code : List (DeclHOL width))
    (guard : ∀ d ∈ pan_code, goodPanopsHOL d = true) :
    ∀ (entry : CrepInlineMapHOLName × List Nat × CrepProgHOL width),
      entry ∈ compileProgDeclsHOLW pan_code → crepBinaryProgNative entry.2.2 :=
  PanToCrepInlineTableValidity.everyInstWInline pan_code
    (PanToCrepTableValidity.everyInstOkLess_panToCrepCompileToCrep pan_code guard)

end Flapjack.PanToCrepProgramValidity
