import Flapjack.Pancake.PanStructs.CompileDeclsExact
import Flapjack.Pancake.Semantics.PanSem.DeclContextExact
namespace Flapjack.Pancake.PanStructs.CompileShapeExact
open Flapjack.Pancake.PanLang
/-- Compiled declarations contain no struct-name declarations, so the exact
struct-name scan preserves every initial context. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "decs_stcnames_compile_decs"
  (words_as_type_indexed_bitvec)]
theorem decsStcnamesCompileDecls {width : Nat} [NeZero width]
    (context : ContextExact) (declarations : List (DeclHOL width))
    (acc : StructContextExact) :
    Flapjack.decsStcnamesHOLExact acc (compileDeclsExact context declarations).1 = some acc := by
  induction declarations generalizing context with
  | nil => rfl
  | cons declaration declarations ih =>
    cases declaration <;> simp only [compileDeclsExact, Flapjack.decsStcnamesHOLExact] <;> apply ih
end Flapjack.Pancake.PanStructs.CompileShapeExact
