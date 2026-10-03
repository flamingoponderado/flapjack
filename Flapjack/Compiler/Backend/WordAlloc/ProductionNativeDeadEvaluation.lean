import Flapjack.Compiler.Backend.WordAlloc.ProductionRemoveDeadDecoderImage
import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateRemoveDead

namespace Flapjack.WordAlloc
open WordSemStateFiniteExact

/-- Actual native dead-code cleanup produces a decoded executable program and
satisfies the complete original native evaluation conclusion. Source encoding
supplies decoder acceptance; output decoding and the actual router result are
derived rather than assumed. The only semantic premises are precisely the
original source flat convention, source evaluation and non-error condition.

This API composition is Flapjack infrastructure, with no separately named HOL
original. It uses the reviewed original evaluate_remove_dead_prog result and
its semantic dependencies, including their documented IEEE real-rendering
assumption. It does not establish the still-separate production/native
state/evaluator correspondence or whole allocator semantics. -/
theorem nativeDead_evaluation {width : Nat} [NeZero width] {C F : Type}
    (source : WordProg (BitVec width)) (native : WordLangProgHOL (BitVec width))
    (encoded : wordLangProgToHOL source = some native)
    (state finalState : WordSemStateFiniteExact width C F)
    (result : Option (WordSemResult width))
    (sourceConditions : flatExpConventions native = true ∧
      evaluate native state = (result, finalState) ∧ result ≠ some .error) :
    ∃ output : WordProg (BitVec width),
      wordLangProgFromHOL (removeDeadProg native) = some output ∧
      RiscV.wordRemoveDeadProgramViaHOL source = output ∧
      ∃ targetLocals : Spt (WordLocW width),
        evaluate (removeDeadProg native) state =
          (result, {finalState with locals := targetLocals}) ∧
        match result with
        | none => True
        | some (.break _) => True
        | some (.continue _) => True
        | some _ => finalState.locals = targetLocals := by
  rcases wordRemoveDeadProgramViaHOL_sourceNative source native encoded with
    ⟨output, decoded, routed⟩
  rcases evaluateRemoveDeadProg native state finalState result sourceConditions with
    ⟨targetLocals, evaluated, locals⟩
  refine ⟨output, decoded, routed, targetLocals, evaluated, ?_⟩
  cases result with
  | none => trivial
  | some value => cases value <;> simp_all

end Flapjack.WordAlloc
