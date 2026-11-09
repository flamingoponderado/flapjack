module

public import Flapjack.Compiler.Backend.Semantics.ClosProps.AdjustOracle
public import Flapjack.Compiler.Backend.Semantics.ClosSem.SemanticsRelated

@[expose] public section

-- Public declarations below use private helpers.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-! Assemble oracle-adjustment evaluator cases by clock and expression size. -/
namespace Flapjack.Compiler.Backend.ClosProps.AdjustOracle
open ClosSem

/-- Mutual simulation of closure evaluation and closure application under
an oracle adjustment. This helper assembles the source theorem's cases. -/
theorem evaluateSimulation {C D F : Type} (cc : Compiler D) (f : C → D) :
    (∀ expressions env (source : State C F), EvalAt cc f expressions env source) ∧
      (∀ location function args (source : State C F), AppAt cc f location function args source) := by
  have all : ∀ clock : Nat,
      (∀ (source : State C F), source.clock = clock → ∀ location function args,
        AppAt cc f location function args source) ∧
      (∀ weight expressions env (source : State C F),
        source.clock = clock → expsWeight expressions = weight → EvalAt cc f expressions env source) := by
    intro clock
    induction clock using Nat.strongRecOn with
    | ind clock clockIH =>
      have appAll : ∀ (source : State C F), source.clock = clock → ∀ location function args,
          AppAt cc f location function args source := by
        intro source clockEq location function args
        cases args with
        | nil => exact evaluateAppAdjOracNil () cc f location function source
        | cons arg rest =>
          apply evaluateAppAdjOracCons () cc f location function arg rest source
          · intro body env remaining closureRun enough
            have positive : 0 < (arg :: rest).length - remaining.length :=
              Nat.sub_pos_of_lt (destClosure_full_remaining_lt _ _ _ _ _ _ _ closureRun)
            have smaller : (decClock ((arg :: rest).length - remaining.length) source).clock < clock := by
              simp only [decClock, clockEq, List.length_cons] at positive enough ⊢
              omega
            exact (clockIH _ smaller).2 (expsWeight [body]) [body] env _ rfl rfl
          · intro body env remaining value middle closureRun enough bodyRun
            have positive : 0 < (arg :: rest).length - remaining.length :=
              Nat.sub_pos_of_lt (destClosure_full_remaining_lt _ _ _ _ _ _ _ closureRun)
            have bound := evaluate_clock_le [body] env (decClock ((arg :: rest).length - remaining.length) source)
            have smaller : middle.clock < clock := by
              rw [bodyRun] at bound
              have before : middle.clock ≤ (decClock ((arg :: rest).length - remaining.length) source).clock := bound
              simp only [decClock, clockEq, List.length_cons] at before positive enough
              omega
            exact (clockIH _ smaller).1 middle rfl location value remaining
      constructor
      · exact appAll
      · intro weight
        induction weight using Nat.strongRecOn with
        | ind weight weightIH =>
          have exprIH : ∀ expressions env (state : State C F),
              state.clock ≤ clock → expsWeight expressions < weight → EvalAt cc f expressions env state := by
            intro expressions env state clockLe weightLt
            rcases Nat.lt_or_eq_of_le clockLe with clockLt | clockEqual
            · exact (clockIH state.clock clockLt).2 (expsWeight expressions) expressions env state rfl rfl
            · exact weightIH (expsWeight expressions) weightLt expressions env state clockEqual rfl
          intro expressions env source clockEq measure
          cases expressions with
          | nil => exact evaluateAdjOracNil () cc f env source
          | cons first rest =>
            cases rest with
            | cons second tail =>
              apply evaluateAdjOracCons () cc f first second tail env source
              · apply exprIH [first] env source (by omega)
                simp only [expsWeight] at measure ⊢; omega
              · intro values middle firstRun
                apply exprIH (second :: tail) env middle
                · have bound := evaluate_clock_le [first] env source
                  simpa [firstRun, clockEq] using bound
                · simp only [expsWeight] at measure ⊢; omega
            | nil =>
              cases first with
              | var trace index => exact evaluateAdjOracVar () cc f trace index env source
              | fn name location selected arity body =>
                exact evaluateAdjOracFn () cc f name location selected arity body env source
              | raise trace body =>
                apply evaluateAdjOracRaise () cc f trace body env source
                apply exprIH [body] env source (by omega)
                simp only [expsWeight, expWeight] at measure ⊢; omega
              | tick trace body =>
                apply evaluateAdjOracTick () cc f trace body env source
                intro nonzero
                apply exprIH [body] env (decClock 1 source) (by simp [decClock]; omega)
                simp only [expsWeight, expWeight] at measure ⊢; omega
              | «let» trace bindings body =>
                apply evaluateAdjOracLet () cc f trace bindings body env source
                · apply exprIH bindings env source (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢; omega
                · intro values middle bindingsRun
                  apply exprIH [body] (values ++ env) middle
                  · have bound := evaluate_clock_le bindings env source
                    simpa [bindingsRun, clockEq] using bound
                  · simp only [expsWeight, expWeight] at measure ⊢; omega
              | letrec names location selected functions body =>
                apply evaluateAdjOracLetrec () cc f names location selected functions body env source
                intro captured valid capture
                apply exprIH [body] _ source (by omega)
                simp only [expsWeight, expWeight] at measure ⊢; omega
              | handle trace body handler =>
                apply evaluateAdjOracHandle () cc f trace body handler env source
                · apply exprIH [body] env source (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢; omega
                · intro value middle bodyRun
                  apply exprIH [handler] (value :: env) middle
                  · have bound := evaluate_clock_le [body] env source
                    simpa [bodyRun, clockEq] using bound
                  · simp only [expsWeight, expWeight] at measure ⊢; omega
              | ifThenElse trace condition yes no =>
                apply evaluateAdjOracIf () cc f trace condition yes no env source
                · apply exprIH [condition] env source (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢; omega
                · intro value middle conditionRun decision
                  apply exprIH [yes] env middle
                  · have bound := evaluate_clock_le [condition] env source
                    simpa [conditionRun, clockEq] using bound
                  · simp only [expsWeight, expWeight] at measure ⊢; omega
                · intro value middle conditionRun decision
                  apply exprIH [no] env middle
                  · have bound := evaluate_clock_le [condition] env source
                    simpa [conditionRun, clockEq] using bound
                  · simp only [expsWeight, expWeight] at measure ⊢; omega
              | call trace ticks location args =>
                apply evaluateAdjOracCall () cc f trace ticks location args env source
                · apply exprIH args env source (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢; omega
                · intro values middle callEnv body argsRun codeRun enough
                  have bound := evaluate_clock_le args env source
                  have middleLe : middle.clock ≤ source.clock := by simpa [argsRun] using bound
                  have smaller : (decClock (ticks + 1) middle).clock < clock := by
                    simp only [decClock]
                    omega
                  exact (clockIH _ smaller).2 (expsWeight [body]) [body] callEnv _ rfl rfl
              | app trace location function args =>
                apply evaluateAdjOracApp () cc f trace location function args env source
                · intro nonempty
                  apply exprIH args env source (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢; omega
                · intro values middle nonempty argsRun
                  apply exprIH [function] env middle
                  · have bound := evaluate_clock_le args env source
                    simpa [argsRun, clockEq] using bound
                  · simp only [expsWeight, expWeight] at measure ⊢; omega
                · intro values middle functions last nonempty argsRun functionRun
                  have firstBound := evaluate_clock_le args env source
                  have secondBound := evaluate_clock_le [function] env middle
                  have bound : last.clock ≤ clock := by
                    have one : middle.clock ≤ source.clock := by simpa [argsRun] using firstBound
                    have two : last.clock ≤ middle.clock := by simpa [functionRun] using secondBound
                    omega
                  rcases Nat.lt_or_eq_of_le bound with smaller | equal
                  · exact (clockIH last.clock smaller).1 last rfl location _ values
                  · exact appAll last equal location _ values
              | op trace op args =>
                by_cases install : op = .install
                · subst op
                  apply evaluateAdjOracInstall () cc f trace args env source
                  · apply exprIH args env source (by omega)
                    have smaller := opWeight_gt trace .install args
                    simp only [expsWeight] at measure
                    omega
                  · intro values middle program installed argsRun installRun
                    have argsClock := evaluate_clock_le args env source
                    have installClock := doInstall_success_clock values.reverse middle installed program installRun
                    have smaller : installed.clock < clock := by
                      have middleLe : middle.clock ≤ source.clock := by simpa [argsRun] using argsClock
                      omega
                    exact (clockIH installed.clock smaller).2 (expsWeight program) program [] installed rfl rfl
                · by_cases force : op = .thunkOp .forceThunk
                  · subst op
                    apply evaluateAdjOracForce () cc f trace args env source
                    · apply exprIH args env source (by omega)
                      have smaller := opWeight_gt trace (.thunkOp .forceThunk) args
                      simp only [expsWeight] at measure
                      omega
                    · intro values middle value argsRun thunkRun
                      apply exprIH [appUnit (.var .none 0)] [value] middle
                      · have bound := evaluate_clock_le args env source
                        simpa [argsRun, clockEq] using bound
                      · have h := appUnit_var_weight
                        simp only [expsWeight, expWeight] at measure
                        simp only [appUnit, expsWeight, expWeight] at h ⊢
                        omega
                  · apply evaluateAdjOracOrdinaryOp () cc f trace op args env source install force
                    apply exprIH args env source (by omega)
                    have smaller := opWeight_gt trace op args
                    simp only [expsWeight] at measure
                    omega
  constructor
  · intro expressions env source
    exact (all source.clock).2 (expsWeight expressions) expressions env source rfl rfl
  · intro location function args source
    exact (all source.clock).1 source rfl location function args

namespace SimulationPort

/-- The canonical closure finite-map state roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) := ClosSem.holFmapAsFiniteSupportWitness

/-- Closure evaluation and application preserve their exact non-type-error
result when the compiler oracle is adjusted compatibly. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "evaluate_adj_orac"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateAdjOrac {C D F U V : Type} (cc : Compiler D) (f : C → D) :
    (∀ (p : List ClosLang.Exp × List Value × State C F) (z1 : State C F)
      (r : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value) (s1 : State C F)
      (_unused : U) (z2 : State D F),
      evaluate p.1 p.2.1 p.2.2 = (r, s1) ∧ p.2.2 = z1 ∧
        r ≠ .err (.abort .typeError) ∧ adjOracRel cc f z1 z2 →
      ∃ s2, evaluate p.1 p.2.1 z2 = (r, s2) ∧ adjOracRel cc f s1 s2) ∧
    (∀ (w : Option Nat) (x : Value) (y : List Value) (z1 : State C F)
      (r : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value) (s1 : State C F)
      (_unused : V) (z2 : State D F),
      evaluateApp w x y z1 = (r, s1) ∧ r ≠ .err (.abort .typeError) ∧ adjOracRel cc f z1 z2 →
      ∃ s2, evaluateApp w x y z2 = (r, s2) ∧ adjOracRel cc f s1 s2) := by
  constructor
  · intro p z1 r s1 _ z2 ⟨run, same, safe, rel⟩
    subst z1
    exact (evaluateSimulation cc f).1 p.1 p.2.1 p.2.2 r s1 z2 ⟨run, safe, rel⟩
  · intro w x y z1 r s1 _ z2 h
    exact (evaluateSimulation cc f).2 w x y z1 r s1 z2 h

end SimulationPort

private def maptoBroadlookup (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) :
    Nat → Option (Nat × ClosLang.Exp) := code.lookup

private def mapofBroad (lookup : Nat → Option (Nat × ClosLang.Exp))
    (support : ∃ keys : List Nat, ∀ key, lookup key ≠ none → key ∈ keys) :
    HolFiniteMapExact Nat (Nat × ClosLang.Exp) := ⟨lookup, support⟩

/-- The supplied code map retains its canonical lookup and finite support. -/
theorem holFmapAsFiniteSupportParamWitness_semanticsAdjOrac_code
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) :
    mapofBroad (maptoBroadlookup code) code.finiteSupport = code := by
  cases code
  rfl

/-- Compatible oracle adjustment preserves whole-program observations. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "semantics_adj_orac"
  (fmap_as_finite_support_parameters := [code])]
theorem semanticsAdjOrac {C D F : Type} (ffi : HolFfiState F) (maxApp : Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (co : CompileOracle C)
    (ccX : Compiler C) (es : List ClosLang.Exp) (coX : CompileOracle D) (cc : Compiler D) (f : C → D)
    (h : semantics ffi maxApp code co ccX es ≠ .fail ∧
      coX = (fun n => (f (co n).1, (co n).2)) ∧
      ∀ n x y, co n = (x, y) → cc (f x) y =
        (ccX x y).map (fun (bytes, words, cfg) => (bytes, words, f cfg))) :
    semantics ffi maxApp code coX cc es = semantics ffi maxApp code co ccX es := by
  obtain ⟨nonFail, rfl, compatible⟩ := h
  have safe := (semantics_ne_fail_iff ffi maxApp code co ccX es).mp nonFail
  have same : ∀ clock,
      resultOutcome (evaluate es [] (initialState ffi maxApp code co ccX clock)).1 =
        resultOutcome (evaluate es [] (initialState ffi maxApp code
          (fun n => (f (co n).1, (co n).2)) cc clock)).1 ∧
      ((evaluate es [] (initialState ffi maxApp code co ccX clock)).1 = .err (.abort .typeError) ↔
        (evaluate es [] (initialState ffi maxApp code (fun n => (f (co n).1, (co n).2)) cc clock)).1 =
          .err (.abort .typeError)) ∧
      (evaluate es [] (initialState ffi maxApp code co ccX clock)).2.ffi =
        (evaluate es [] (initialState ffi maxApp code (fun n => (f (co n).1, (co n).2)) cc clock)).2.ffi := by
    intro clock
    let source := initialState ffi maxApp code co ccX clock
    let target := initialState ffi maxApp code (fun n => (f (co n).1, (co n).2)) cc clock
    have related : adjOracRel cc f source target := by
      refine ⟨?_, rfl⟩
      intro n x y eq
      exact (compatible n x y eq).symm
    cases sourceRun : evaluate es [] source with
    | mk result final =>
      have noType : result ≠ .err (.abort .typeError) := by
        intro bad
        apply safe clock
        simpa [source, sourceRun] using bad
      obtain ⟨last, targetRun, finalRel⟩ :=
        (evaluateSimulation cc f).1 es [] source result final target ⟨sourceRun, noType, related⟩
      have ffiEq : final.ffi = last.ffi := by rcases finalRel with ⟨_, rfl⟩; rfl
      simp [target, targetRun, ffiEq]
  exact (semantics_eq_of_related_evaluations ffi maxApp code code co _ ccX cc es es same).symm

/-- The supplied code map retains its canonical lookup and finite support. -/
theorem holFmapAsFiniteSupportParamWitness_semanticsCurryI_code
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) :
    mapofBroad (maptoBroadlookup code) code.finiteSupport = code := by
  cases code
  rfl

/-- Adding an unused compiler state does not alter closure observations. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "semantics_CURRY_I"
  (fmap_as_finite_support_parameters := [code])]
theorem semanticsCurryI {S C F : Type} (ffi : HolFfiState F) (maxApp : Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (co : CompileOracle (S × C))
    (cc : Compiler C) (es : List ClosLang.Exp)
    (nonFail : semantics ffi maxApp code co (BackendProps.stateCc (fun s p => (s, p)) cc) es ≠ .fail) :
    semantics ffi maxApp code (BackendProps.stateCo (fun s p => (s, p)) co) cc es =
      semantics ffi maxApp code co (BackendProps.stateCc (fun s p => (s, p)) cc) es := by
  apply semanticsAdjOrac ffi maxApp code co (BackendProps.stateCc (fun s p => (s, p)) cc) es
    (BackendProps.stateCo (fun s p => (s, p)) co) cc Prod.snd
  refine ⟨nonFail, ?_, ?_⟩
  · funext n
    rfl
  · intro n x y entry
    cases x with
    | mk state cfg =>
      cases result : cc cfg y with
      | none => simp [BackendProps.stateCc, result]
      | some value =>
        rcases value with ⟨bytes, words, next⟩
        simp [BackendProps.stateCc, result]

end Flapjack.Compiler.Backend.ClosProps.AdjustOracle
