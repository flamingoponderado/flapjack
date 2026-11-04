import Flapjack.Compiler.Backend.WordAlloc.ProductionFullSSA
import Flapjack.Compiler.Backend.WordAlloc.ProductionSSAStateRoute
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSARenameLookup
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASetup.ListNextVarRenameArithmetic
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASetup.EvenListDistinct

namespace Flapjack.Compiler.Backend.WordAlloc

/-- The allocator formals are exactly the original native prologue fresh-name
sequence, for every parameter count and initial counter. No map validity or
successful program evaluation is assumed. Flapjack metadata infrastructure. -/
theorem setupSSA_parameterNames {width : Nat} [NeZero width]
    (count limit : Nat) (program : WordLangProgHOL (BitVec width)) :
    (evenList count).map (optionLookup (setupSSA (outputWidth := width) count limit program).2.1) =
      (List.range count).map (fun index => 4 * index + limit) := by
  unfold setupSSA
  dsimp only
  generalize h : listNextVarRename (evenList count) .ln limit = result
  rcases result with ⟨outputs, map, next⟩
  have arithmetic := listNextVarRenameLemma1 (evenList count) .ln limit outputs map next h
  have lookup := listNextVarRenameLemma2Prime (evenList count) .ln limit outputs map next h (evenListNodup count)
  have mapped : (evenList count).map (optionLookup map) = outputs := by
    rw [lookup.1]
    apply List.map_congr_left
    intro key member
    unfold optionLookup
    cases sptLookup key map <;> rfl
  rw [mapped, arithmetic.2.1]
  simp [evenList]

end Flapjack.Compiler.Backend.WordAlloc

namespace Flapjack
open Compiler.Backend.WordAlloc

end Flapjack
