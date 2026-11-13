module

public import Flapjack.Compiler.Backend.Semantics.FlatSem.GeneratedSize

@[expose] public section

namespace Flapjack.Compiler.Backend.FlatElim

open Flapjack.Compiler.Backend.FlatSem

/-- The original sum decomposition for generated environment-entry sizes. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "SUM_MAP_v3_size"]
theorem sumMapV3Size (xs : List (AstHOL.VarN × Value)) :
    (xs.map valuePairSizeHOL).sum = xs.length +
      (xs.map (mlstringSizeHOL ∘ Prod.fst)).sum +
      (xs.map (valueSizeHOL ∘ Prod.snd)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      rcases x with ⟨name, value⟩
      simp only [List.map_cons, List.sum_cons, List.length_cons, Function.comp_apply,
        valuePairSizeHOL]
      omega

end Flapjack.Compiler.Backend.FlatElim
