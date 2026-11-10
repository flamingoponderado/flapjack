module

public import Flapjack.Compiler.Backend.Semantics.ClosProps.SubmapRel
public import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateExact
import Flapjack.Compiler.Backend.Semantics.ClosSem.CodeExtensionEvaluate
@[expose] public section

/-! Evaluation under finite-map code extension. -/
namespace Flapjack.Compiler.Backend.ClosProps
open Flapjack Flapjack.Compiler.Backend.ClosSem

namespace EvaluateCodeSubmapPort
/-- The closure state uses the canonical finite-map representation. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ state : StateBroad C F, (State.ofBroad state).toBroad = state) ∧
      (∀ state : State C F, State.ofBroad state.toBroad = state) :=
  ClosSem.holFmapAsFiniteSupportWitness
end EvaluateCodeSubmapPort

/-- Evaluation and application preserve non-type-error results under a safe code extension. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "evaluate_code_SUBMAP"
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_codeSubmap {C F A B : Type} [Nonempty A] [Nonempty B] :
    (∀ (p : List ClosLang.Exp × List Value × State C F) x y z1 r s1 (_s2 : A) z2,
      p = (x, y, z1) ∧ evaluate x y z1 = (r, s1) ∧
      r ≠ .err (.abort .typeError) ∧ CodeExtension z1 z2 →
      ∃ s2, evaluate x y z2 = (r, s2) ∧ CodeExtension s1 s2) ∧
    (∀ w x y (z1 : State C F) r s1 (_s2 : B) z2,
      evaluateApp w x y z1 = (r, s1) ∧
      r ≠ .err (.abort .typeError) ∧ CodeExtension z1 z2 →
      ∃ s2, evaluateApp w x y z2 = (r, s2) ∧ CodeExtension s1 s2) := by
  constructor
  · intro p x y z1 r s1 unused z2 h
    exact (evaluate_codeExtension (C := C) (F := F)).1 x z1 y z2 r s1 h.2.1 h.2.2.1 h.2.2.2
  · intro w x y z1 r s1 unused z2 h
    exact (evaluate_codeExtension (C := C) (F := F)).2 (z1.clock + 1)
      w x y z1 z2 r s1 (by omega) h.1 h.2.1 h.2.2
end Flapjack.Compiler.Backend.ClosProps
