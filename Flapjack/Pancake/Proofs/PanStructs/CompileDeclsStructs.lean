import Flapjack.Pancake.PanStructs.CompileDeclsExact

namespace Flapjack.Pancake.PanStructs.CompileShapeExact
open Flapjack.Pancake.PanLang

/-- Compiling declarations preserves the source struct context. This is the
whole HOL prerequisite used by the declaration-correctness induction. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "compile_decs_structs"
  (words_as_type_indexed_bitvec)]
theorem compileDeclsStructs {width : Nat} [NeZero width]
    (context : ContextExact) (declarations compiled : List (DeclHOL width))
    (finalContext : ContextExact)
    (h : compileDeclsExact context declarations = (compiled, finalContext)) :
    finalContext.structs = context.structs := by
  have preserve : ∀ (declarations : List (DeclHOL width)) (context : ContextExact),
      (compileDeclsExact context declarations).2.structs = context.structs := by
    intro declarations
    induction declarations with
    | nil => intro context; rfl
    | cons declaration declarations ih =>
      intro context
      cases declaration <;> simp only [compileDeclsExact] <;> apply ih
  simpa only [h] using preserve declarations context

end Flapjack.Pancake.PanStructs.CompileShapeExact
