module

public import Flapjack.Compiler.Backend.Semantics.DataSem.Apply
public import Flapjack.Compiler.Backend.Semantics.DataProps.NonFfiResources

@[expose] public section

/-!
# Space-safety `do_app` lemmas of `data_to_word_assignProofScript.sml`
-/

namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataSem

/-- A successful auxiliary application never turns space safety on. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "do_app_aux_safe_for_space_mono"]
theorem doAppAux_safeForSpace_mono {C F : Type} (op : ClosLang.Op) (xs : List Value)
    (s s1 : State C F) (r : Value)
    (h : doAppAux op xs s = .val (r, s1) ∧ s1.safeForSpace = true) : s.safeForSpace = true := by
  obtain ⟨run, safe⟩ := h
  unfold doAppAux at run
  split at run
  · split at run
    · split at run
      · simp only [SemanticPrimitivesHOL.Result.val.injEq, Prod.mk.injEq] at run
        obtain ⟨-, rfl⟩ := run
        simpa using safe
      · simp at run
    · simp at run
  · simp at run
  · split at run
    · rename_i pair app
      simp only [SemanticPrimitivesHOL.Result.val.injEq] at run
      subst run
      exact (applyNonFfi_successFields op xs s s1 r s.safeForSpace app).2.2 safe
    · simp at run

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
