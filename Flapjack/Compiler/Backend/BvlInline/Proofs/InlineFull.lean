import Flapjack.Compiler.Backend.BvlInline.Proofs.InlineExpandedCall

/-! Assembly of the BVL inlining evaluator simulation. -/
namespace Flapjack.Compiler.Backend.BvlInline.Proofs
open Flapjack.Compiler.Backend.BvlSem Flapjack.Compiler.Backend.BvlProps Flapjack.SemanticPrimitivesHOL

namespace InlineFullCarrier
/-- Canonical BVL reference-map state representation roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : Flapjack.Compiler.Backend.BvlSem.State C F, State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness
end InlineFullCarrier

/-- BVL evaluation is simulated by tick inlining, with the original
type-error exclusion. -/
@[hol "cakeml/compiler/backend/proofs/bvl_inlineProofScript.sml" "evaluate_inline"
  (fmap_as_finite_support := [refs])]
theorem evaluateInline {C F : Type} (expressions : List Bvl.Exp) (env : List BvlSem.Value)
    (source : Flapjack.Compiler.Backend.BvlSem.State (Spt (Nat × Bvl.Exp) × C) F)
    (result : Result (List BvlSem.Value) BvlSem.Value)
    (target : Flapjack.Compiler.Backend.BvlSem.State C F)
    (final : Flapjack.Compiler.Backend.BvlSem.State (Spt (Nat × Bvl.Exp) × C) F)
    (output : List Bvl.Exp) (limit : Nat)
    (h : inStateRel limit source target ∧ ExpRel source.code expressions output ∧
      evaluateTuple (expressions, env, source) = (result, final) ∧
      result ≠ .err (.abort .typeError)) :
    ∃ targetFinal, evaluateTuple (output, env, target) = (result, targetFinal) ∧
      inStateRel limit final targetFinal := by
  have allRanks : ∀ clock weight : Nat, ∀ (es out : List Bvl.Exp) (a : List BvlSem.Value)
      (s last : State (Spt (Nat × Bvl.Exp) × C) F) (t : State C F)
      (res : Result (List BvlSem.Value) BvlSem.Value),
      s.clock = clock → expsWeight es = weight → inStateRel limit s t → ExpRel s.code es out →
      evaluateTuple (es, a, s) = (res, last) → res ≠ .err (.abort .typeError) →
      ∃ targetLast, evaluateTuple (out, a, t) = (res, targetLast) ∧ inStateRel limit last targetLast := by
    intro clock
    induction clock using Nat.strongRecOn with
    | ind clock clockIH =>
      intro weight
      induction weight using Nat.strongRecOn with
      | ind weight weightIH =>
        have exprIH : ∀ (es out : List Bvl.Exp) (a : List BvlSem.Value)
            (s last : State (Spt (Nat × Bvl.Exp) × C) F) (t : State C F)
            (res : Result (List BvlSem.Value) BvlSem.Value),
            s.clock ≤ clock → expsWeight es < weight → inStateRel limit s t → ExpRel s.code es out →
            evaluateTuple (es, a, s) = (res, last) → res ≠ .err (.abort .typeError) →
            ∃ targetLast, evaluateTuple (out, a, t) = (res, targetLast) ∧ inStateRel limit last targetLast := by
          intro es out a s last t res clockLe weightLt rel expRel run valid
          rcases Nat.lt_or_eq_of_le clockLe with clockLt | clockEq
          · exact clockIH s.clock clockLt (expsWeight es) es out a s last t res rfl rfl rel expRel run valid
          · exact weightIH (expsWeight es) weightLt es out a s last t res clockEq rfl rel expRel run valid
        intro es out a s last t res stateClock measure rel expRel run valid
        cases expRel with
        | nil => exact evaluateInline_nil limit a s last t res rel .nil run valid
        | var index => exact evaluateInline_var limit index a s last t res rel (.var index) run valid
        | cons headRel tailRel =>
          rename_i x x1 y y1 xs ys
          refine evaluateInline_cons limit x x1 y y1 xs ys a s last t ?_ ?_ res rel (.cons headRel tailRel) run valid
          · intro ss ll tt rr bound r er ev ok
            apply exprIH [x] [y] a ss ll tt rr (by omega) ?_ r er ev ok
            simp only [expsWeight] at measure ⊢
            have := expWeight_pos x1
            omega
          · intro ss ll tt rr bound r er ev ok
            apply exprIH (x1 :: xs) (y1 :: ys) a ss ll tt rr (by omega) ?_ r er ev ok
            simp only [expsWeight] at measure ⊢
            omega
        | ifThenElse conditionRel yesRel noRel =>
          rename_i condition yes no condition' yes' no'
          refine evaluateInline_if limit condition yes no condition' yes' no' a s last t ?_ ?_ res rel
            (.ifThenElse conditionRel yesRel noRel) run valid
          · intro ss ll tt rr bound r er ev ok
            apply exprIH [condition] [condition'] a ss ll tt rr (by omega) ?_ r er ev ok
            simp only [expsWeight, expWeight] at measure ⊢; omega
          · intro choice ss ll tt rr bound r er ev ok
            apply exprIH [if choice then yes else no] [if choice then yes' else no'] a ss ll tt rr
              (by omega) ?_ r er ev ok
            cases choice <;> simp only [Bool.false_eq_true, ↓reduceIte, expsWeight, expWeight] at measure ⊢ <;> omega
        | letExp bindingsRel bodyRel =>
          rename_i bindings bindings' body body'
          refine evaluateInline_let limit bindings bindings' body body' a s last t ?_ ?_ res rel
            (.letExp bindingsRel bodyRel) run valid
          · intro ss ll tt rr bound r er ev ok
            apply exprIH bindings bindings' a ss ll tt rr (by omega) ?_ r er ev ok
            simp only [expsWeight, expWeight] at measure ⊢; omega
          · intro bodyEnv ss ll tt rr bound r er ev ok
            apply exprIH [body] [body'] bodyEnv ss ll tt rr (by omega) ?_ r er ev ok
            simp only [expsWeight, expWeight] at measure ⊢; omega
        | handle bodyRel handlerRel =>
          rename_i body handler body' handler'
          refine evaluateInline_handle limit body handler body' handler' a s last t ?_ ?_ res rel
            (.handle bodyRel handlerRel) run valid
          · intro ss ll tt rr bound r er ev ok
            apply exprIH [body] [body'] a ss ll tt rr (by omega) ?_ r er ev ok
            simp only [expsWeight, expWeight] at measure ⊢; omega
          · intro handlerEnv ss ll tt rr bound r er ev ok
            apply exprIH [handler] [handler'] handlerEnv ss ll tt rr (by omega) ?_ r er ev ok
            simp only [expsWeight, expWeight] at measure ⊢; omega
        | raise bodyRel =>
          rename_i body body'
          refine evaluateInline_raise limit body body' a s last t ?_ res rel (.raise bodyRel) run valid
          intro ss ll tt rr bound r er ev ok
          apply exprIH [body] [body'] a ss ll tt rr (by omega) ?_ r er ev ok
          simp only [expsWeight, expWeight] at measure ⊢; omega
        | tick bodyRel =>
          rename_i body body'
          refine evaluateInline_tick limit body body' a s last t ?_ res rel (.tick bodyRel) run valid
          intro ss ll tt rr bound r er ev ok
          exact clockIH ss.clock (by omega) (expsWeight [body]) [body] [body'] a ss ll tt rr rfl rfl r er ev ok
        | op argsRel =>
          rename_i op args args'
          refine evaluateInline_op limit op args args' a s last t ?_ res rel (.op argsRel) run valid
          intro ss ll tt rr bound r er ev ok
          apply exprIH args args' a ss ll tt rr (by omega) ?_ r er ev ok
          simp only [expsWeight, expWeight] at measure ⊢; omega
        | force location index =>
          refine evaluateInline_force limit location index a s last t ?_ res rel (.force location index) run valid
          intro body body' values thunk value ll rr _ _ _ nonzero er ev ok
          have smaller : (decClock 1 s).clock < clock := by simp [decClock]; omega
          exact clockIH (decClock 1 s).clock smaller (expsWeight [body]) [body] [body'] values
            (decClock 1 s) ll (decClock 1 t) rr rfl rfl
            (inStateRel_decClock limit 1 s t rel) (by simpa [decClock] using er) ev ok
        | call argsRel =>
          rename_i ticks dest args args'
          refine evaluateInline_call limit ticks dest args args' a s last t ?_ ?_ res rel (.call argsRel) run valid
          · intro ll rr er ev ok
            apply exprIH args args' a s ll t rr (by omega) ?_ rel er ev ok
            simp only [expsWeight, expWeight] at measure ⊢; omega
          · intro middle ll targetMiddle values body body' rr bound enough r er ev ok
            have smaller : (decClock (ticks + 1) middle).clock < clock := by simp [decClock]; omega
            exact clockIH (decClock (ticks + 1) middle).clock smaller (expsWeight [body]) [body] [body']
              values (decClock (ticks + 1) middle) ll (decClock (ticks + 1) targetMiddle) rr rfl rfl
              (inStateRel_decClock limit (ticks + 1) middle targetMiddle r) (by simpa [decClock] using er) ev ok
        | inlineCall argsRel codeFound bodyRel =>
          rename_i ticks name arity args args' body body'
          refine evaluateInline_inlineCall limit ticks name args args' (Bvl.mkTick (ticks + 1) body') a
            s last t ?_ ?_ res rel (.inlineCall argsRel codeFound bodyRel) run valid
          · intro ll rr er ev ok
            apply exprIH args args' a s ll t rr (by omega) ?_ rel er ev ok
            simp only [expsWeight, expWeight] at measure ⊢; omega
          · intro middle ll targetMiddle values callee callee' rr bound enough r er ev ok
            have smaller : (decClock (ticks + 1) middle).clock < clock := by simp [decClock]; omega
            exact clockIH (decClock (ticks + 1) middle).clock smaller (expsWeight [callee]) [callee] [callee']
              values (decClock (ticks + 1) middle) ll (decClock (ticks + 1) targetMiddle) rr rfl rfl
              (inStateRel_decClock limit (ticks + 1) middle targetMiddle r) (by simpa [decClock] using er) ev ok
  exact allRanks source.clock (expsWeight expressions) expressions output env source final target result
    rfl rfl h.1 h.2.1 h.2.2.1 h.2.2.2

end Flapjack.Compiler.Backend.BvlInline.Proofs
