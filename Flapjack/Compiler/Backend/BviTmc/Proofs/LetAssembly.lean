import Flapjack.Compiler.Backend.BviTmc.Proofs.LetWorker

/-! Assembly of the TMC let simulation. -/
namespace Flapjack.Compiler.Backend.BviTmc.LetAssembly
open BviTmc BviSem BvlSem ListSimulation LetSimulation LetWorker IfWorker

/-- Flapjack infrastructure: the ordinary, wrapper, and worker let cases
assembled from binding-list and body induction hypotheses. The original
measure and safety premises are omitted. -/
theorem evaluate_let {C F : Type} (bindings : List Bvi.Exp) (body : Bvi.Exp)
    (source : BviState (Nat × C) F) (env1 : List Value) (result : BviResult)
    (final : BviState (Nat × C) F) (opt : Bool) (f : HolFiniteMapExact Nat Nat)
    (target : BviState C F) (env2 : List Value) (loc : Nat)
    (run : evaluate [.let bindings body] env1 source = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError))
    (environments : envRel opt f env1 env2)
    (bindingsIH : ∀ r mid, evaluate bindings env1 source = (r, mid) →
      r ≠ .err (.abort .typeError) → Core bindings env2 f target r mid)
    (bodyIH : ∀ values values' mid (g : HolFiniteMapExact Nat Nat) (t : BviState C F),
      evaluate [body] (values ++ env1) mid = (result, final) →
      envRel opt g (values ++ env1) (values' ++ env2) → stateRel g mid t →
      Core [body] (values' ++ env2) g t result final ∧
      ∀ locOpt, optimisedCode loc locOpt mid.code t.code →
        (∀ wrapper, rewriteWrapperSource loc locOpt (values ++ env1).length body = some wrapper →
          Core [wrapper] (values' ++ env2) g t result final) ∧
        (opt = true → ∀ holePtr c, holeHasVal g (values ++ env1) (values' ++ env2) t.refs c →
          holeNotFinalised t.refs holePtr → holEl (values ++ env1).length (values' ++ env2) = .refPtr false holePtr →
          WorkerCore (rewriteWorkerSource loc locOpt (values ++ env1).length ((values ++ env1).length + 1)
            (values ++ env1).length body) (values ++ env1) (values' ++ env2) g t holePtr result final)) :
    Core [.let bindings body] env2 f target result final ∧
    ∀ locOpt, optimisedCode loc locOpt source.code target.code →
      (∀ wrapper, rewriteWrapperSource loc locOpt env1.length (.let bindings body) = some wrapper →
        Core [wrapper] env2 f target result final) ∧
      (opt = true → ∀ holePtr c, holeHasVal f env1 env2 target.refs c →
        holeNotFinalised target.refs holePtr → holEl env1.length env2 = .refPtr false holePtr →
        WorkerCore (rewriteWorkerSource loc locOpt env1.length (env1.length + 1) env1.length
          (.let bindings body)) env1 env2 f target holePtr result final) := by
  constructor
  · apply evaluate_let_core bindings body source env1 result final opt f target env2
      run notTypeError environments bindingsIH
    intro values values' mid g t bodyRun env states
    exact (bodyIH values values' mid g t bodyRun env states).1
  · intro locOpt code
    constructor
    · intro wrapper wrapperRun
      apply evaluate_let_wrapper bindings body wrapper source env1 result final opt f target env2
        loc locOpt run notTypeError environments code wrapperRun bindingsIH
      intro values values' mid g t body' bodyRun env states nextCode rewrite
      exact (bodyIH values values' mid g t bodyRun env states).2 locOpt nextCode |>.1 body' rewrite
    · intro optTrue holePtr c hole notFinal pointer
      have optEnv : envRel true f env1 env2 := by simpa [optTrue] using environments
      apply evaluate_let_worker bindings body source env1 result final f target env2 loc locOpt holePtr
        run notTypeError optEnv c hole notFinal pointer code bindingsIH
      intro values values' mid g t bodyRun env states nextHole nextNotFinal nextPointer nextCode
      have bodyEnv : envRel opt g (values ++ env1) (values' ++ env2) := by simpa [optTrue] using env
      exact (bodyIH values values' mid g t bodyRun bodyEnv states).2 locOpt nextCode |>.2
        optTrue holePtr c nextHole nextNotFinal nextPointer

end Flapjack.Compiler.Backend.BviTmc.LetAssembly
