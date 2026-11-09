import Flapjack.Compiler.Backend.BviTmc.Proofs.CallBlockSimulation
import Flapjack.Compiler.Backend.BviTmc.Proofs.LetSimulation
import Flapjack.Compiler.Backend.BviTmc.Proofs.ExtractionWellFormed
import Flapjack.Compiler.Backend.BviTmc.Proofs.LetWorkerBlock

/-! Simulation of expressions with extracted call blocks. -/
namespace Flapjack.Compiler.Backend.BviTmc.ExtractedSimulation
open BviTmc BviSem BvlSem ListSimulation CallBlockAuxSimulation

/-- Flapjack infrastructure: successful extraction selects the call-block
worker in the source-shaped worker traversal. -/
theorem rewrite_worker_extracted (loc dest n : Nat) (e : Bvi.Exp) (bindings : List Bvi.Exp) (cb : CallBlock)
    (extracted : toBlockSource n loc e = some (bindings, cb)) :
    rewriteWorkerSource loc dest n (n + 1) n e =
      .let bindings (workerBlockSource cb dest (bindings.length + n) (bindings.length + n + 1)) := by
  rcases toBlock_cases n loc e bindings cb extracted with ⟨tag, args, left, child, right, rfl, rfl⟩ |
    ⟨ticks, args, vars, rfl, rfl⟩
  · simp [rewriteWorkerSource, extracted, Nat.add_assoc]
  · simp [rewriteWorkerSource, extracted, Nat.add_assoc]

/-- Flapjack infrastructure: an extracted constructor selects its wrapper in
the source-shaped wrapper traversal. -/
theorem rewrite_wrapper_extracted (loc dest n tag : Nat) (e : Bvi.Exp) (bindings : List Bvi.Exp)
    (left right : List Nat) (child : CallBlock)
    (extracted : toBlockSource n loc e = some (bindings, .callBlock tag left child right)) :
    rewriteWrapperSource loc dest n e = some (.let bindings (wrapperBlockSource tag left child right dest)) := by
  rcases toBlock_cases n loc e bindings (.callBlock tag left child right) extracted with
    ⟨tag', args, left', child', right', shape, same⟩ | ⟨ticks, args, vars, shape, same⟩
  · cases same
    subst e
    simp [rewriteWrapperSource, extracted]
  · cases same

/-- Flapjack infrastructure: an extracted expression's ordinary simulation
follows from its binding-list and recursive-call body hypotheses. -/
theorem evaluate_extracted_ordinary {C F : Type} (loc : Nat) (cb : CallBlock) (e : Bvi.Exp)
    (bindings : List Bvi.Exp) (source : BviState (Nat × C) F) (target : BviState C F)
    (env1 env2 : List Value) (opt : Bool) (f : HolFiniteMapExact Nat Nat)
    (result : BviResult) (final : BviState (Nat × C) F)
    (run : evaluate [e] env1 source = (result, final))
    (extracted : toBlockSource env1.length loc e = some (bindings, cb))
    (notTypeError : result ≠ .err (.abort .typeError)) (environments : envRel opt f env1 env2)
    (bindingsIH : ∀ r mid, evaluate bindings env1 source = (r, mid) →
      r ≠ .err (.abort .typeError) → Core bindings env2 f target r mid)
    (bodyIH : ∀ values values' mid (g : HolFiniteMapExact Nat Nat) (t : BviState C F),
      evaluate bindings env1 source = (.val values, mid) →
      evaluate bindings env2 target = (.val values', t) →
      envRel opt g (values ++ env1) (values' ++ env2) → stateRel g mid t →
      CallBlockSimulation.OrdinaryBodyIH loc mid t (values ++ env1) (values' ++ env2) g) :
    Core [e] env2 f target result final := by
  have sourceRun := ListExtraction.evaluate_bvi_to_cb cb env1.length loc e env1 source final result bindings
    run extracted (Nat.le_refl _)
  have letCore : Core [.let bindings (callBlockToBvi loc cb)] env2 f target result final := by
    apply LetSimulation.evaluate_let_to_core bindings (callBlockToBvi loc cb) (callBlockToBvi loc cb)
      source env1 result final opt f target env2 sourceRun notTypeError environments bindingsIH
    intro values values' mid g t blockRun valuesRelated env states sourceBindings targetBindings
    have nextEnv := envRel_append opt g env1 env2 values values' env valuesRelated
    have valueLength := evaluate_length bindings env1 source mid values sourceBindings
    have blockWf : wfBlock (values ++ env1).length cb := by
      apply wfBlock_expand bindings.length (values ++ env1).length cb (toBlock_wf env1.length loc e bindings cb extracted)
      simp [List.length_append, valueLength]
    exact CallBlockLeaf.evaluate_cb_ordinary loc cb mid (values ++ env1) opt g t (values' ++ env2)
      nextEnv states (bodyIH values values' mid g t sourceBindings targetBindings nextEnv states)
      result final blockWf blockRun notTypeError
  obtain ⟨next, g, targetResult, targetLetRun, related, nextStates, extension, fresh, unchanged, still⟩ := letCore
  cases targetRun : evaluate [e] env2 target with
  | mk actual targetFinal =>
    have targetLet := ListExtraction.evaluate_bvi_to_cb cb env1.length loc e env2 target targetFinal actual bindings
      targetRun extracted (envRel_length opt f env1 env2 environments)
    rw [targetLetRun] at targetLet
    cases targetLet
    exact ⟨next, g, targetResult, targetRun, related, nextStates, extension, fresh, unchanged, still⟩

/-- Flapjack infrastructure: an extracted constructor expression is
simulated by its binding list and optimized wrapper. The binding-list and
smaller-clock function-body induction hypotheses are still explicit. -/
theorem evaluate_extracted_wrapper {C F : Type} (loc dest tag : Nat) (left right : List Nat)
    (child : CallBlock) (e : Bvi.Exp) (bindings : List Bvi.Exp)
    (source : BviState (Nat × C) F) (target : BviState C F) (env1 env2 : List Value)
    (opt : Bool) (f : HolFiniteMapExact Nat Nat) (result : BviResult) (final : BviState (Nat × C) F)
    (run : evaluate [e] env1 source = (result, final))
    (extracted : toBlockSource env1.length loc e = some (bindings, .callBlock tag left child right))
    (notTypeError : result ≠ .err (.abort .typeError)) (environments : envRel opt f env1 env2)
    (code : optimisedCode loc dest source.code target.code)
    (bindingsIH : ∀ r mid, evaluate bindings env1 source = (r, mid) →
      r ≠ .err (.abort .typeError) → Core bindings env2 f target r mid)
    (bodyIH : ∀ values values' mid (g : HolFiniteMapExact Nat Nat) (t : BviState C F),
      evaluate bindings env1 source = (.val values, mid) →
      evaluate bindings env2 target = (.val values', t) →
      envRel opt g (values ++ env1) (values' ++ env2) → stateRel g mid t →
      optimisedCode loc dest mid.code t.code →
      WorkerBodyIH loc dest mid (values ++ env1) (values' ++ env2) g) :
    Core [.let bindings (wrapperBlockSource tag left child right dest)] env2 f target result final := by
  have sourceRun := ListExtraction.evaluate_bvi_to_cb (.callBlock tag left child right)
    env1.length loc e env1 source final result bindings run extracted (Nat.le_refl _)
  apply LetSimulation.evaluate_let_to_core bindings (callBlockToBvi loc (.callBlock tag left child right))
    (wrapperBlockSource tag left child right dest) source env1 result final opt f target env2
    sourceRun notTypeError environments bindingsIH
  intro values values' mid g t blockRun valuesRelated env states sourceBindings targetBindings
  have nextEnv := envRel_append opt g env1 env2 values values' env valuesRelated
  have nextCode := WrapperCases.evaluate_pres_opt_code loc dest source mid target t bindings env1 env2
    (.val values) (.val values') code sourceBindings targetBindings
  have valueLength := evaluate_length bindings env1 source mid values sourceBindings
  have blockWf : wfBlock (values ++ env1).length (.callBlock tag left child right) := by
    apply wfBlock_expand bindings.length (values ++ env1).length _ (toBlock_wf env1.length loc e bindings _ extracted)
    simp [List.length_append, valueLength]
  exact evaluate_wrapper_cb loc dest tag left right child mid t (values ++ env1) (values' ++ env2)
    opt g result final nextEnv states blockWf blockRun notTypeError nextCode
    (bodyIH values values' mid g t sourceBindings targetBindings nextEnv states nextCode)

/-- Flapjack infrastructure: an extracted expression's optimized worker is
simulated by its bindings and the extracted call-block worker. -/
theorem evaluate_extracted_worker {C F : Type} (loc dest ptr : Nat) (cb : CallBlock)
    (e : Bvi.Exp) (bindings : List Bvi.Exp) (source : BviState (Nat × C) F) (target : BviState C F)
    (env1 env2 : List Value) (f : HolFiniteMapExact Nat Nat) (initial : Value)
    (result : BviResult) (final : BviState (Nat × C) F)
    (run : evaluate [e] env1 source = (result, final))
    (extracted : toBlockSource env1.length loc e = some (bindings, cb))
    (notTypeError : result ≠ .err (.abort .typeError)) (environments : envRel true f env1 env2)
    (hole : holeHasVal f env1 env2 target.refs initial) (notFinal : holeNotFinalised target.refs ptr)
    (pointer : holEl env1.length env2 = .refPtr false ptr)
    (code : optimisedCode loc dest source.code target.code)
    (bindingsIH : ∀ r mid, evaluate bindings env1 source = (r, mid) →
      r ≠ .err (.abort .typeError) → Core bindings env2 f target r mid)
    (bodyIH : ∀ values values' mid (g : HolFiniteMapExact Nat Nat) (t : BviState C F),
      evaluate bindings env1 source = (.val values, mid) →
      evaluate [callBlockToBvi loc cb] (values ++ env1) mid = (result, final) →
      envRel true g (values ++ env1) (values' ++ env2) → stateRel g mid t →
      optimisedCode loc dest mid.code t.code →
      WorkerBodyIH loc dest mid (values ++ env1) (values' ++ env2) g) :
    IfWorker.WorkerCore (.let bindings (workerBlockSource cb dest (bindings.length + env1.length)
      (bindings.length + env1.length + 1))) env1 env2 f target ptr result final := by
  have sourceRun := ListExtraction.evaluate_bvi_to_cb cb env1.length loc e env1 source final result bindings
    run extracted (Nat.le_refl _)
  apply LetWorkerBlock.evaluate_let_worker_block bindings (callBlockToBvi loc cb) cb source env1 result final
    f target env2 loc dest ptr sourceRun notTypeError environments initial hole notFinal pointer code bindingsIH
  intro values values' mid g t valueLength sourceBindings blockRun nextEnv nextStates nextHole nextNotFinal nextPointer nextCode
  have blockWf : wfBlock (values ++ env1).length cb := by
    apply wfBlock_expand bindings.length (values ++ env1).length cb (toBlock_wf env1.length loc e bindings cb extracted)
    simp [List.length_append, valueLength]
  exact CallBlockWorkerSimulation.evaluate_worker_cb loc dest ptr cb mid t (values ++ env1) (values' ++ env2) g
    initial result final blockRun notTypeError nextEnv blockWf nextStates nextHole nextNotFinal nextPointer nextCode
    (bodyIH values values' mid g t sourceBindings blockRun nextEnv nextStates nextCode)

end Flapjack.Compiler.Backend.BviTmc.ExtractedSimulation
