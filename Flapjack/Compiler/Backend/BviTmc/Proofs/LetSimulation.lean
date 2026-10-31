import Flapjack.Compiler.Backend.BviTmc.Proofs.ListSimulation
import Flapjack.Compiler.Backend.BviTmc.Proofs.WrapperCases

/-! Simulation of let bindings for the TMC proof. -/
namespace Flapjack.Compiler.Backend.BviTmc.LetSimulation
open BviTmc BviSem BvlSem SemanticPrimitivesProps ResultRelation ListSimulation

/-- Flapjack infrastructure: ordinary let simulation with a possibly rewritten
body. The hypotheses are specialized binding-list and body simulations;
the original measure, safety premises, and worker conclusion are omitted. -/
theorem evaluate_let_to_core {C F : Type} (bindings : List Bvi.Exp) (body targetBody : Bvi.Exp)
    (source : BviState (Nat × C) F) (env1 : List Value) (result : BviResult)
    (final : BviState (Nat × C) F) (opt : Bool) (f : HolFiniteMapExact Nat Nat)
    (target : BviState C F) (env2 : List Value)
    (run : evaluate [.let bindings body] env1 source = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError))
    (environments : envRel opt f env1 env2)
    (bindingsIH : ∀ r mid, evaluate bindings env1 source = (r, mid) →
      r ≠ .err (.abort .typeError) → Core bindings env2 f target r mid)
    (bodyIH : ∀ values values' mid (g : HolFiniteMapExact Nat Nat) (t : BviState C F),
      evaluate [body] (values ++ env1) mid = (result, final) →
      List.Forall₂ (valueRel g) values values' → envRel opt g env1 env2 → stateRel g mid t →
      evaluate bindings env1 source = (.val values, mid) →
      evaluate bindings env2 target = (.val values', t) →
      Core [targetBody] (values' ++ env2) g t result final) :
    Core [.let bindings targetBody] env2 f target result final := by
  cases bindingsRun : evaluate bindings env1 source with
  | mk bindingsResult middle =>
    have bindingsSafe : bindingsResult ≠ .err (.abort .typeError) := by
      intro bad
      subst bindingsResult
      rw [BviSem.evaluate, BviSem.fixClock_evaluate, bindingsRun] at run
      exact notTypeError (congrArg Prod.fst run.symm)
    obtain ⟨middleTarget, g, targetResult, targetRun, related, middleStates, extension,
      fresh, unchanged, still⟩ := bindingsIH bindingsResult middle bindingsRun bindingsSafe
    cases bindingsResult with
    | err error =>
      cases targetResult with
      | val values => simp [resultRel] at related
      | err error' =>
        rw [BviSem.evaluate, BviSem.fixClock_evaluate, bindingsRun] at run
        obtain ⟨rfl, rfl⟩ := run.symm
        refine ⟨middleTarget, g, .err error', ?_, related, middleStates, extension, fresh, unchanged, still⟩
        rw [BviSem.evaluate, BviSem.fixClock_evaluate, targetRun]
    | val values =>
      cases targetResult with
      | err error => simp [resultRel] at related
      | val values' =>
        have valuesRelated : List.Forall₂ (valueRel g) values values' := related
        rw [BviSem.evaluate, BviSem.fixClock_evaluate, bindingsRun] at run
        obtain ⟨last, h, bodyResult, bodyRun, bodyRel, states, bodyExtension,
          bodyFresh, bodyUnchanged, bodyStill⟩ :=
          bodyIH values values' middle g middleTarget run valuesRelated
            (envRel_submap opt f g env1 env2 environments extension) middleStates
            bindingsRun targetRun
        have submap : finiteSubmap f h := by
          intro k v found; exact bodyExtension k v (extension k v found)
        have domain := BviProps.evaluate_refs_subset bindings env2 target middleTarget (.val values') targetRun
        have allFresh := onlyFresh_trans f g h target.refs middleTarget.refs fresh bodyFresh domain
        have allUnchanged := holesUnchanged_trans f g target.refs middleTarget.refs last.refs ∅
          unchanged bodyUnchanged fresh extension
        have allStill := holesStill_trans f g target.refs middleTarget.refs last.refs ()
          still bodyStill fresh extension
        refine ⟨last, h, bodyResult, ?_, bodyRel, states, submap, allFresh, allUnchanged, allStill⟩
        rw [BviSem.evaluate, BviSem.fixClock_evaluate, targetRun]
        exact bodyRun

/-- Flapjack infrastructure: the ordinary let induction step with the same
body on both sides. -/
theorem evaluate_let_core {C F : Type} (bindings : List Bvi.Exp) (body : Bvi.Exp)
    (source : BviState (Nat × C) F) (env1 : List Value) (result : BviResult)
    (final : BviState (Nat × C) F) (opt : Bool) (f : HolFiniteMapExact Nat Nat)
    (target : BviState C F) (env2 : List Value)
    (run : evaluate [.let bindings body] env1 source = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError))
    (environments : envRel opt f env1 env2)
    (bindingsIH : ∀ r mid, evaluate bindings env1 source = (r, mid) →
      r ≠ .err (.abort .typeError) → Core bindings env2 f target r mid)
    (bodyIH : ∀ values values' mid (g : HolFiniteMapExact Nat Nat) (t : BviState C F),
      evaluate [body] (values ++ env1) mid = (result, final) →
      envRel opt g (values ++ env1) (values' ++ env2) → stateRel g mid t →
      Core [body] (values' ++ env2) g t result final) :
    Core [.let bindings body] env2 f target result final := by
  apply evaluate_let_to_core bindings body body source env1 result final opt f target env2
    run notTypeError environments bindingsIH
  intro values values' mid g t bodyRun valuesRelated env states _sourceRun _targetRun
  exact bodyIH values values' mid g t bodyRun (envRel_append opt g env1 env2 values values' env valuesRelated) states

/-- Flapjack infrastructure: the let-wrapper simulation from the binding and
body induction hypotheses, with optimized code preserved through bindings. -/
theorem evaluate_let_wrapper {C F : Type} (bindings : List Bvi.Exp) (body wrapper : Bvi.Exp)
    (source : BviState (Nat × C) F) (env1 : List Value) (result : BviResult)
    (final : BviState (Nat × C) F) (opt : Bool) (f : HolFiniteMapExact Nat Nat)
    (target : BviState C F) (env2 : List Value) (loc locOpt : Nat)
    (run : evaluate [.let bindings body] env1 source = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError))
    (environments : envRel opt f env1 env2)
    (code : optimisedCode loc locOpt source.code target.code)
    (wrapperRun : rewriteWrapperSource loc locOpt env1.length (.let bindings body) = some wrapper)
    (bindingsIH : ∀ r mid, evaluate bindings env1 source = (r, mid) →
      r ≠ .err (.abort .typeError) → Core bindings env2 f target r mid)
    (bodyIH : ∀ values values' mid (g : HolFiniteMapExact Nat Nat) (t : BviState C F) body',
      evaluate [body] (values ++ env1) mid = (result, final) →
      envRel opt g (values ++ env1) (values' ++ env2) → stateRel g mid t →
      optimisedCode loc locOpt mid.code t.code →
      rewriteWrapperSource loc locOpt (values ++ env1).length body = some body' →
      Core [body'] (values' ++ env2) g t result final) :
    Core [wrapper] env2 f target result final := by
  obtain ⟨body', rfl, rewrite⟩ := WrapperCases.wrapper_strip_let env1.length loc locOpt bindings body wrapper wrapperRun
  apply evaluate_let_to_core bindings body body' source env1 result final opt f target env2
    run notTypeError environments bindingsIH
  intro values values' mid g t bodyRun valuesRelated env states sourceBindings targetBindings
  have nextCode := WrapperCases.evaluate_pres_opt_code loc locOpt source mid target t
    bindings env1 env2 (.val values) (.val values') code sourceBindings targetBindings
  have valueLength := evaluate_length bindings env1 source mid values sourceBindings
  exact bodyIH values values' mid g t body' bodyRun
    (envRel_append opt g env1 env2 values values' env valuesRelated) states nextCode (by
      simpa [List.length_append, valueLength, Nat.add_comm] using rewrite)

end Flapjack.Compiler.Backend.BviTmc.LetSimulation
